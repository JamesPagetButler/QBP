/-
QBP #827 axiom audit — the Lean enumerator (PR #829, Gemini r1 finding 1).

A standalone program, run as `lean --run scripts/LeanAxiomAudit.lean ARGS` with `LEAN_PATH`
UNSET, so this file is elaborated against the Lean toolchain ONLY. The audited modules are
never imported into this file: `main` loads them at RUN time with `Lean.importModules`, as plain
data (`loadExts := false`, initializers never enabled). Consequences:

  * no syntax extension of an audited module (macro, notation, elaborator, instance, `open`,
    identifier) can reach this file's elaboration — they do not exist when it is elaborated;
  * no code of an audited module runs: `loadExts := false` builds no environment extension
    state (the interpreter is never invoked on imported data) and `initialize` blocks need
    `enableInitializersExecution`, which this program never calls;
  * this program's own `import Lean` resolves only against the toolchain (`LEAN_PATH` unset),
    so a project module cannot shadow `Lean`/`Init`/`Std` for the auditor itself.

The decision data is computed from the constants alone: for every constant whose defining
module is a target, its axiom closure (type + value, constructors of inductives), recomputed
here from the terms — the precomputed per-module axiom cache that oleans carry is NOT used.

usage: env -u LEAN_PATH QBP_AUDIT_LEAN_PATH=<sp> lean --run LeanAxiomAudit.lean NONCE LABEL ITEM...
  <sp>   the project's search path (`lake env printenv LEAN_PATH`), ':'-separated; the
         library of the toolchain running this program is appended after it
  ITEM   `i:Mod` = import Mod;  `t:Mod` = audit the constants defined in Mod
Output: exactly one JSON line on stdout (the checker reads nothing else):
  {"mark":"AXIOM-AUDIT-827","nonce":…,"root":…,"targets":[…],"missing":[…],
   "declarations":N,"nonstd":[{"decl":…,"module":…,"axioms":[…]}]}
-/
import Lean

open Lean

/-- Axiom closure of every constant reachable from `roots`, memoised (iterative DFS, so no deep
recursion). An axiom contributes itself; definitions, theorems and opaques contribute type +
value; inductives add their constructors; everything else contributes its type. -/
def qbpAuditAxiomsOf (env : Environment) (roots : Array Name) : Std.HashMap Name NameSet := Id.run do
  let mut memo : Std.HashMap Name NameSet := {}
  let mut onStack : NameSet := {}
  for r in roots do
    if memo.contains r then continue
    let mut stack : Array (Name × Bool) := #[(r, false)]
    while 0 < stack.size do
      let (n, expanded) := stack.back!
      stack := stack.pop
      if memo.contains n then continue
      let some ci := env.find? n | memo := memo.insert n {}; continue
      let mut deps : Array Name := ci.type.getUsedConstants
      match ci with
      | .defnInfo v => deps := deps ++ v.value.getUsedConstants
      | .thmInfo v => deps := deps ++ v.value.getUsedConstants
      | .opaqueInfo v => deps := deps ++ v.value.getUsedConstants
      | .inductInfo v => deps := deps ++ v.ctors.toArray
      | _ => pure ()
      if expanded then
        let mut acc : NameSet := {}
        if ci matches .axiomInfo _ then acc := acc.insert n
        for d in deps do
          if let some s := memo.get? d then
            for a in s do acc := acc.insert a
        memo := memo.insert n acc
        onStack := onStack.erase n
      else
        onStack := onStack.insert n
        stack := stack.push (n, true)
        for d in deps do
          if memo.contains d || onStack.contains d then continue
          stack := stack.push (d, false)
  return memo

def qbpStd : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

def main (args : List String) : IO UInt32 := do
  let nonce :: label :: items := args
    | IO.eprintln "usage: LeanAxiomAudit NONCE LABEL ITEM..."; return 2
  let some sp ← IO.getEnv "QBP_AUDIT_LEAN_PATH"
    | IO.eprintln "QBP_AUDIT_LEAN_PATH is not set"; return 2
  -- Project paths first (as `lake env` orders them), then THIS binary's own toolchain library.
  let userPaths : SearchPath := System.SearchPath.parse sp
  searchPathRef.set (userPaths ++ [← getLibDir (← getBuildDir)])
  let mut imports : Array Import := #[]
  let mut targets : Array Name := #[]
  for it in items do
    if it.startsWith "i:" then imports := imports.push { module := (it.drop 2).toString.toName }
    else if it.startsWith "t:" then targets := targets.push (it.drop 2).toString.toName
    else IO.eprintln s!"bad item {it}"; return 2
  if imports.isEmpty || targets.isEmpty then
    IO.eprintln "no imports or no targets"; return 2
  let env ← importModules imports {} (loadExts := false)
  let mut idxs : Std.HashSet Nat := {}
  let mut missing : Array Name := #[]
  for t in targets do
    match env.getModuleIdx? t with
    | some i => idxs := idxs.insert i.toNat
    | none => missing := missing.push t
  let mut inScope : Array Name := #[]
  for (n, _) in env.constants.map₁ do
    if let some i := env.getModuleIdxFor? n then
      if idxs.contains i.toNat then inScope := inScope.push n
  let memo := qbpAuditAxiomsOf env inScope
  let modNames := env.header.moduleNames
  let mut bad : Array Json := #[]
  for n in inScope do
    let axs := (memo.get? n).getD {}
    let extra := axs.toList.filter (fun a => qbpStd.contains a == false)
    if extra.isEmpty then continue
    let modName := match env.getModuleIdxFor? n with
      | some i => toString (modNames[i.toNat]?.getD .anonymous)
      | none => ""
    bad := bad.push (Json.mkObj [("decl", toString n), ("module", modName),
      ("axioms", Json.arr (extra.map (fun a => Json.str (toString a))).toArray)])
  let out := Json.mkObj [
    ("mark", "AXIOM-AUDIT-827"), ("nonce", nonce), ("root", label),
    ("targets", Json.arr (targets.map (fun t => Json.str (toString t)))),
    ("missing", Json.arr (missing.map (fun t => Json.str (toString t)))),
    ("declarations", inScope.size), ("nonstd", Json.arr bad)]
  IO.println out.compress
  return 0
