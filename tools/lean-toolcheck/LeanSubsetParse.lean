/-
LeanSubsetParse — the pass-file subset check, done by LEAN'S OWN PARSER (PR #824, Red Team r5,
director decision). Trusted toolchain code; run with `lean --run`, never imported.

usage: env -u LEAN_PATH QBP_SUBSET_LEAN_PATH=<sp> lean --run LeanSubsetParse.lean NONCE FILE

What it does, and what it never does:
1. Parses FILE's header with `Lean.Parser.parseHeader` and imports exactly those modules
   (`importModules (loadExts := true)` after `enableInitializersExecution`, so the imported
   modules' parser extensions — Mathlib's pinned syntax — are live). This runs the IMPORTED
   modules' initializers (toolchain + pinned Mathlib: trusted), never code from FILE: FILE is not a
   module on the search path (run.sh passes only the pinned `.lake/packages/*` directories), and
   the grader requires every import root to be a pinned package (`ALLOWED_IMPORT_ROOTS`).
2. Parses each command with `Lean.Parser.parseCommand`, WITHOUT ELABORATING IT. FILE's own code
   (`#eval`, simprocs, macros, elaborators, initializers) therefore never runs here.
3. The one exception, needed for a faithful parse: a TOP-LEVEL `namespace`, `section`, `end`,
   `open` or `set_option` is handed to Lean's own builtin elaborator, because `open`/`namespace`
   activate scoped syntax and `end` drops it. These elaborators run only toolchain code. Any
   error they log is reported (`scope_errors`), and the grader FAILS the file on it.
4. Prints one JSON line per command (`kind`, position, nested command-category kinds, every
   syntax-node kind, attribute names, `set_option` keys, parse errors), then one `done` line.
   Every line carries NONCE.

Soundness argument (README §"Lean-parser subset"): FILE can change the parser only with a
command (syntax/notation/macro/declare_syntax_cat/elab/initialize/attribute [..._parser] …) or
an attribute; none of them is on the grader's kind/attribute allowlist. So up to the first
command outside the allowlist, the header environment plus the scope commands is EXACTLY the
environment real Lean parses that prefix in; from that command on, the grade already FAILS.
A parse error FAILS too.
-/
import Lean

open Lean Elab Parser

namespace QBPToolcheck.SubsetParse

/-- Every syntax-node kind in `stx` (atoms and identifiers are not nodes). -/
partial def kinds (stx : Syntax) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match stx with
  | .node _ k args => args.foldl (fun a s => kinds s a) (acc.insert k)
  | _ => acc

/-- Nested nodes whose kind is in `cat` (the command category), excluding the root. -/
partial def nestedIn (cat : SyntaxNodeKindSet) (stx : Syntax) (root := true)
    (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .node _ k args =>
    let acc := if !root && cat.contains k then acc.push k else acc
    args.foldl (fun a s => nestedIn cat s false a) acc
  | _ => acc

/-- Attribute names: the kind of each `attrInstance`'s attribute node, and for the generic
`Attr.simple` form its identifier too (`@[ext]`, `@[reducible]`, …). -/
partial def attrs (stx : Syntax) (acc : Array String := #[]) : Array String :=
  match stx with
  | .node _ k args =>
    let acc :=
      if k == ``Lean.Parser.Term.attrInstance then
        let a := args[1]!
        match a with
        | .node _ ak aargs =>
          if ak == ``Lean.Parser.Attr.simple then acc.push s!"simple:{aargs[0]!.getId}"
          else acc.push ak.toString
        | _ => acc.push "?"
      else acc
    args.foldl (fun a s => attrs s a) acc
  | _ => acc

/-- `set_option` keys anywhere (command, `… in`, tactic and term forms). -/
partial def optKeys (stx : Syntax) (acc : Array String := #[]) : Array String :=
  match stx with
  | .node _ k args =>
    let acc :=
      if k == ``Lean.Parser.Command.set_option || k == ``Lean.Parser.Tactic.set_option ||
          k == ``Lean.Parser.Term.set_option then
        acc.push (args[1]!.getId.toString)
      else acc
    args.foldl (fun a s => optKeys s a) acc
  | _ => acc

/-- Position of the command's first token OUTSIDE a doc comment (the Python layer blanks doc
comments, so this is where it must see the command start). -/
partial def headPos : Syntax → Option String.Pos.Raw
  | .node _ k args =>
    if k == ``Lean.Parser.Command.docComment then none
    else args.foldl (fun r s => r <|> headPos s) none
  | stx@(.atom ..) | stx@(.ident ..) => stx.getPos?
  | _ => none

/-- Option names in tactic configurations (`decide +kernel`, `simp (config := …)` items). -/
partial def configs (stx : Syntax) (acc : Array String := #[]) : Array String :=
  match stx with
  | .node _ k args =>
    let acc :=
      if k == ``Lean.Parser.Tactic.posConfigItem || k == ``Lean.Parser.Tactic.negConfigItem ||
          k == ``Lean.Parser.Tactic.valConfigItem then
        match args.find? (·.isIdent) with
        | some i => acc.push i.getId.toString
        | none => acc.push "?"
      else acc
    args.foldl (fun a s => configs s a) acc
  | _ => acc

/-- Head positions (first token outside a doc comment) of nested command-category nodes, e.g.
the `theorem` after `set_option … in` on the next line. -/
partial def nestedHeads (cat : SyntaxNodeKindSet) (stx : Syntax) (root := true)
    (acc : Array String.Pos.Raw := #[]) : Array String.Pos.Raw :=
  match stx with
  | .node _ k args =>
    let acc := if !root && cat.contains k then
        match headPos stx with | some p => acc.push p | none => acc
      else acc
    args.foldl (fun a s => nestedHeads cat s false a) acc
  | _ => acc

def scopeKinds : List Name :=
  [``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
   ``Lean.Parser.Command.open, ``Lean.Parser.Command.set_option]

def strs (xs : Array String) : Json := toJson xs
def names (xs : Array Name) : Json := toJson (xs.map (·.toString))

end QBPToolcheck.SubsetParse

open QBPToolcheck.SubsetParse in
unsafe def main (args : List String) : IO UInt32 := do
  let [nonce, file] := args
    | IO.eprintln "usage: LeanSubsetParse NONCE FILE"; return 2
  let some sp ← IO.getEnv "QBP_SUBSET_LEAN_PATH"
    | IO.eprintln "QBP_SUBSET_LEAN_PATH is not set"; return 2
  -- Toolchain library FIRST (as PR #829's auditor): no project dir can supply its own `Init`.
  let tcLib ← getLibDir (← getBuildDir)
  searchPathRef.set ([tcLib] ++ System.SearchPath.parse sp)
  let input ← IO.FS.readFile file
  let ictx := mkInputContext input file
  let emit (fields : List (String × Json)) : IO Unit :=
    IO.println (Json.compress (Json.mkObj (("nonce", toJson nonce) :: fields)))
  let (header, mps, msgs) ← parseHeader ictx
  let imports := headerToImports header
  let hdrErr := msgs.hasErrors
  emit [("header", toJson true),
        ("imports", toJson ((imports.filter (·.module != `Init)).map (·.module.toString))),
        ("parse_error", toJson hdrErr)]
  if hdrErr then
    emit [("done", toJson false), ("reason", toJson "header parse error")]
    return 1
  enableInitializersExecution
  let env ← importModules imports {} (loadExts := true)
  let some cmdCat := (parserExtension.getState env).categories.find? `command
    | emit [("done", toJson false), ("reason", toJson "no command category")]; return 1
  let opts : Options := {}
  let mut cs : Command.State := Command.mkState env {} opts
  let mut mps := mps
  let mut n := 0
  let mut parseErrors := 0
  let mut scopeErrors := 0
  repeat
    let scope := cs.scopes.head!
    let pmctx : ParserModuleContext :=
      { env := cs.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let before := cs.messages.toList.length
    let (cmd, mps', msgs') := parseCommand ictx pmctx mps cs.messages
    mps := mps'
    let perr := msgs'.toList.drop before |>.any (·.severity == .error)
    cs := { cs with messages := msgs' }
    if isTerminalCommand cmd then break
    n := n + 1
    if perr then parseErrors := parseErrors + 1
    let k := cmd.getKind
    let pos := ictx.fileMap.toPosition (cmd.getPos?.getD 0)
    let hpos := ictx.fileMap.toPosition ((headPos cmd).getD (cmd.getPos?.getD 0))
    -- Scope commands only: Lean's builtin elaborator, so later commands parse in the right scope.
    let mut serr := false
    if !perr && scopeKinds.contains k then
      let ctx : Command.Context :=
        { cmdPos := cmd.getPos?.getD 0, fileName := ictx.fileName, fileMap := ictx.fileMap,
          snap? := none, cancelTk? := none }
      let before2 := cs.messages.toList.length
      match (← EIO.toIO' ((Command.elabCommandTopLevel cmd ctx).run cs)) with
      | .error _ => serr := true
      | .ok ((), s') =>
        cs := s'
        serr := cs.messages.toList.drop before2 |>.any (·.severity == .error)
    if serr then scopeErrors := scopeErrors + 1
    emit [("i", toJson n), ("line", toJson pos.line), ("col", toJson pos.column),
          ("head_line", toJson hpos.line), ("head_col", toJson hpos.column),
          ("kind", toJson k.toString),
          ("nested", names (nestedIn cmdCat.kinds cmd)),
          ("nested_heads", toJson ((nestedHeads cmdCat.kinds cmd).map fun q =>
            let r := ictx.fileMap.toPosition q; #[r.line, r.column])),
          ("kinds", names ((kinds cmd).toArray.qsort (·.toString < ·.toString))),
          ("attrs", strs (attrs cmd)), ("set_option", strs (optKeys cmd)),
          ("config", strs (configs cmd)),
          ("parse_error", toJson perr), ("scope_error", toJson serr)]
  emit [("done", toJson true), ("commands", toJson n), ("parse_errors", toJson parseErrors),
        ("scope_errors", toJson scopeErrors)]
  return 0
