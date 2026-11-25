/-
QBP #827 axiom audit — the trusted Lean enumerator (PR #829: Gemini r1 finding 1, Red Team
findings 1–4 and 9).

A standalone program, run as `lean --run scripts/LeanAxiomAudit.lean ARGS` with `LEAN_PATH`
UNSET, so this file is elaborated against the Lean toolchain ONLY. The audited modules are never
imported into this file: `main` loads them at RUN time with `Lean.importModules`, as plain data
(`loadExts := false`; initializers are never enabled). Consequences:

  * no syntax extension of an audited module (macro, `macro_rules` on `run_cmd`, notation,
    elaborator, instance, identifier) can reach this file's elaboration — none of them exists
    when it is elaborated (Gemini r1 1, Red Team 1);
  * no code of an audited module runs: `loadExts := false` builds no environment-extension state
    (the interpreter is never invoked on imported data), and `initialize` blocks need
    `enableInitializersExecution`, which this program never calls — so an imported module cannot
    print a forged result or `IO.Process.exit 0` (Red Team 2). Nothing printed after the import is
    parsed by anyone: the ONE result line is written by this program at the end;
  * this program's own `import Lean` resolves only against the toolchain (`LEAN_PATH` unset),
    and at run time the toolchain library comes FIRST on the search path, so no project module can
    stand in for `Init`/`Std`/`Lean`/`Lake` (`shadowed` reports any that resolved elsewhere);
  * the result reports what the names `propext`, `Classical.choice`, `Quot.sound` denote in the
    loaded environment (kind, module, fingerprint), so the checker can verify they are the
    toolchain's own axioms, not same-named project ones (Red Team r2 finding 3).

SCOPE COMES FROM LEAN (Red Team 4). The audited modules are every module in the loaded
environment (`env.header.moduleNames`, i.e. everything the root really imports, however its
header is written) whose .olean resolves under one of the project build directories given as
`p:DIR`. The Python closure (`t:` items) is only a cross-check: each must be present.

AXIOM CLOSURE (Red Team 9): exact, per strongly connected component (iterative Tarjan), so an
inductive and its constructors (a dependency cycle) get the same, complete axiom set — what
`Lean.collectAxioms` / `#print axioms` report. Recomputed from the terms; the per-module axiom
cache that oleans carry is NOT used.

FINGERPRINTS (Red Team 3; allowlist IDENTITY only, never a verdict): for each declaration named
by an `a:NAME` item that reports a non-standard axiom, and for each of its non-standard axioms,
the result carries `fp`: a canonical serialisation of the constant and of every PROJECT constant
reachable from it (theorems: statement only; definitions, opaques, axioms, inductives: statement
and body/constructors), plus the names of the non-project constants it reaches. The checker
SHA-256s it and compares it with the allowlist entry's pin.

usage: env -u LEAN_PATH QBP_AUDIT_LEAN_PATH=<sp> lean --run LeanAxiomAudit.lean NONCE LABEL ITEM...
  <sp>   the project's search path, ':'-separated (in CI: the project build output and the
         pinned Mathlib cache, written from the artifact layout). The library of the toolchain
         running this program is put FIRST, before it (Red Team r2 finding 2)
  ITEM   `i:Mod` import Mod · `t:Mod` Mod must be in scope (cross-check) ·
         `p:DIR` a project build directory (scope) · `a:Name` allowlisted name (fingerprint it)
Output: exactly one JSON line on stdout:
  {"mark":"AXIOM-AUDIT-827","nonce":…,"root":…,"scope":[…],"missing":[…],"unresolved":[…],
   "declarations":N,"nonstd":[{"decl":…,"module":…,"axioms":[{"name":…,"module":…,"fp"?:…}],"fp"?:…}]}
-/
import Lean

open Lean

/-- Used constants of a constant's statement and (for non-theorems) body; inductives add their
constructors. `full` also adds a theorem's proof (axiom closure needs it; fingerprints do not). -/
def qbpDeps (ci : ConstantInfo) (full : Bool) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .thmInfo v => if full then t ++ v.value.getUsedConstants else t
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | _ => t

structure QbpFrame where
  n : Name
  deps : Array Name
  i : Nat
  deriving Inhabited

/-- Axiom closure of every constant reachable from `roots`: iterative Tarjan SCC, so every
member of a dependency cycle gets the full axiom set of the cycle (exact, like `collectAxioms`). -/
def qbpAuditAxiomsOf (env : Environment) (roots : Array Name) : Std.HashMap Name NameSet := Id.run do
  let mut memo : Std.HashMap Name NameSet := {}
  let mut index : Std.HashMap Name Nat := {}
  let mut low : Std.HashMap Name Nat := {}
  let mut onS : NameSet := {}
  let mut sstack : Array Name := #[]
  let mut counter := 0
  for r in roots do
    if index.contains r || memo.contains r then continue
    let some rci := env.find? r | memo := memo.insert r {}; continue
    index := index.insert r counter; low := low.insert r counter; counter := counter + 1
    sstack := sstack.push r; onS := onS.insert r
    let mut frames : Array QbpFrame := #[{ n := r, deps := qbpDeps rci true, i := 0 }]
    while 0 < frames.size do
      let f := frames.back!
      if f.i < f.deps.size then
        let d := f.deps[f.i]!
        frames := frames.pop.push { f with i := f.i + 1 }
        if memo.contains d then continue
        if let some di := index.get? d then
          if onS.contains d then
            low := low.insert f.n (Nat.min (low.getD f.n 0) di)
          continue
        let some dci := env.find? d | memo := memo.insert d {}; continue
        index := index.insert d counter; low := low.insert d counter; counter := counter + 1
        sstack := sstack.push d; onS := onS.insert d
        frames := frames.push { n := d, deps := qbpDeps dci true, i := 0 }
      else
        frames := frames.pop
        let ln := low.getD f.n 0
        if ln == index.getD f.n 0 then
          -- f.n is the root of an SCC: pop its members, give them all the same axiom set.
          let mut members : Array Name := #[]
          let mut going := true
          while going do
            let m := sstack.back!
            sstack := sstack.pop
            onS := onS.erase m
            members := members.push m
            if m == f.n then going := false
          let mut acc : NameSet := {}
          for m in members do
            let some mci := env.find? m | continue
            if mci matches .axiomInfo _ then acc := acc.insert m
            for d in qbpDeps mci true do
              if let some s := memo.get? d then
                for a in s do acc := acc.insert a
          for m in members do memo := memo.insert m acc
        if 0 < frames.size then
          let p := frames.back!
          low := low.insert p.n (Nat.min (low.getD p.n 0) ln)
  return memo

def qbpStdList : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def qbpStd : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound

/-- Module-name roots owned by the toolchain. -/
def qbpReservedRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- Canonical serialisation of an expression (binder names dropped; everything else kept). -/
partial def qbpSer (e : Expr) : String :=
  match e with
  | .bvar i => s!"#{i}"
  | .fvar _ => "!fvar"
  | .mvar _ => "!mvar"
  | .sort l => s!"(S {l})"
  | .const n ls => s!"(C {n.toString (escape := true)} {ls.map toString})"
  | .app f a => s!"(A {qbpSer f} {qbpSer a})"
  | .lam _ t b bi => s!"(L{repr bi} {qbpSer t} {qbpSer b})"
  | .forallE _ t b bi => s!"(P{repr bi} {qbpSer t} {qbpSer b})"
  | .letE _ t v b nd => s!"(Z{nd} {qbpSer t} {qbpSer v} {qbpSer b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal s) => s!"(T {s.quote})"
  | .mdata _ b => qbpSer b
  | .proj t i b => s!"(J {t.toString (escape := true)} {i} {qbpSer b})"

/-- Fingerprint text of `c`: itself and every project constant reachable from it (sorted). -/
def qbpFingerprint (env : Environment) (inProject : Name → Bool) (c : Name) : String := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[c]
  let mut parts : Array String := #[]
  while 0 < todo.size do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | parts := parts.push s!"{n.toString (escape := true)} ?"; continue
    if !(n == c || inProject n) then
      parts := parts.push s!"{n.toString (escape := true)} ext"
      continue
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let body := match ci with
      | .defnInfo v => qbpSer v.value
      | .opaqueInfo v => qbpSer v.value
      | .inductInfo v => toString (v.ctors.map (fun (c : Name) => c.toString (escape := true)))
      | _ => ""
    parts := parts.push s!"{n.toString (escape := true)} {kind} {ci.levelParams} {qbpSer ci.type} {body}"
    for d in qbpDeps ci false do
      if !seen.contains d then todo := todo.push d
  return "\n".intercalate (parts.qsort (· < ·)).toList

def main (args : List String) : IO UInt32 := do
  let nonce :: label :: items := args
    | IO.eprintln "usage: LeanAxiomAudit NONCE LABEL ITEM..."; return 2
  let some sp ← IO.getEnv "QBP_AUDIT_LEAN_PATH"
    | IO.eprintln "QBP_AUDIT_LEAN_PATH is not set"; return 2
  -- TOOLCHAIN LIBRARY FIRST (PR #829 Red Team r2 finding 2): a project directory earlier on the
  -- path could otherwise supply its own `Init` (an empty `prelude` module) and make `sorryAx`
  -- vanish. With the toolchain first, every `Init`/`Std`/`Lean`/`Lake` module resolves to the
  -- toolchain of the binary running this program; the `shadowed` check below verifies that.
  let tcLib ← getLibDir (← getBuildDir)
  let tcDir := (← IO.FS.realPath tcLib).toString ++ "/"
  searchPathRef.set ([tcLib] ++ System.SearchPath.parse sp)
  let mut imports : Array Import := #[]
  let mut targets : Array Name := #[]
  let mut projDirs : Array String := #[]
  let mut allowNames : NameSet := {}
  for it in items do
    let v := (it.drop 2).toString
    if it.startsWith "i:" then imports := imports.push { module := v.toName }
    else if it.startsWith "t:" then targets := targets.push v.toName
    else if it.startsWith "p:" then
      projDirs := projDirs.push ((← IO.FS.realPath v).toString ++ "/")
    else if it.startsWith "a:" then allowNames := allowNames.insert v.toName
    else IO.eprintln s!"bad item {it}"; return 2
  if imports.isEmpty || projDirs.isEmpty then
    IO.eprintln "no imports or no project directory"; return 2
  let env ← importModules imports {} (loadExts := false)
  let modNames := env.header.moduleNames
  -- Scope from Lean: every loaded module whose .olean lies in a project build directory.
  let mut scopeIdx : Std.HashSet Nat := {}
  let mut scope : Array Name := #[]
  let mut unresolved : Array Name := #[]
  let mut shadowed : Array Name := #[]
  for h : k in [0:modNames.size] do
    let m := modNames[k]
    let path : Option String ←
      try pure (some (← IO.FS.realPath (← findOLean m)).toString) catch _ => pure none
    let some path := path | unresolved := unresolved.push m; continue
    -- A toolchain-rooted module must come from the toolchain library, never from elsewhere.
    if qbpReservedRoots.contains m.getRoot && !path.startsWith tcDir then
      shadowed := shadowed.push m
    if projDirs.any (fun d => path.startsWith d) then
      scopeIdx := scopeIdx.insert k
      scope := scope.push m
  let missing := targets.filter (fun t => !scope.contains t)
  let mut inScope : Array Name := #[]
  for (n, _) in env.constants.map₁ do
    if let some i := env.getModuleIdxFor? n then
      if scopeIdx.contains i.toNat then inScope := inScope.push n
  let inProject : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some i => scopeIdx.contains i.toNat
    | none => false
  let modOf : Name → String := fun n =>
    match env.getModuleIdxFor? n with
    | some i => toString (modNames[i.toNat]?.getD .anonymous)
    | none => ""
  let memo := qbpAuditAxiomsOf env inScope
  let mut bad : Array Json := #[]
  for n in inScope do
    let axs := (memo.get? n).getD {}
    let extra := axs.toList.filter (fun a => qbpStd.contains a == false)
    if extra.isEmpty then continue
    let pinned := allowNames.contains n
    let axJ := extra.toArray.map fun a =>
      let base := [("name", Json.str (toString a)), ("module", Json.str (modOf a))]
      Json.mkObj (if pinned then base ++ [("fp", Json.str (qbpFingerprint env inProject a))] else base)
    let base := [("decl", Json.str (toString n)), ("module", Json.str (modOf n)),
      ("axioms", Json.arr axJ)]
    bad := bad.push (Json.mkObj
      (if pinned then base ++ [("fp", Json.str (qbpFingerprint env inProject n))] else base))
  -- STANDARD AXIOM IDENTITY (Red Team r2 finding 3): the three standard axioms are matched by
  -- name in the filter above, so report what those names ARE in this environment — kind,
  -- module and fingerprint — for the checker to compare with the toolchain's pins. A `prelude`
  -- module declaring its own `axiom propext : False` is caught here.
  let stdJ := qbpStdList.toArray.map fun a =>
    match env.find? a with
    | some ci => Json.mkObj [("name", Json.str (toString a)), ("module", Json.str (modOf a)),
        ("axiom", Json.bool (ci matches .axiomInfo _)),
        ("fp", Json.str (qbpFingerprint env inProject a))]
    | none => Json.mkObj [("name", Json.str (toString a)), ("module", Json.str ""),
        ("axiom", Json.bool false), ("fp", Json.str "")]
  let out := Json.mkObj [
    ("mark", "AXIOM-AUDIT-827"), ("nonce", nonce), ("root", label),
    ("scope", Json.arr (scope.map (fun t => Json.str (toString t)))),
    ("missing", Json.arr (missing.map (fun t => Json.str (toString t)))),
    ("unresolved", Json.arr (unresolved.map (fun t => Json.str (toString t)))),
    ("shadowed", Json.arr (shadowed.map (fun t => Json.str (toString t)))),
    ("std", Json.arr stdJ),
    ("declarations", inScope.size), ("nonstd", Json.arr bad)]
  IO.println out.compress
  return 0
