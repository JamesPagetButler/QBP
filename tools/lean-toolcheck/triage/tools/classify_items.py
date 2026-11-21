"""Rule-based first-pass triage of Lean release-note items against QBP usage.
Inputs: items.json (parsed notes), QBP proofs dir. Output: triage.json + counts.
Every item gets exactly one disposition + a one-line reason. Manual overrides in OVERRIDES.
"""

import json, re, sys, pathlib, collections

items = json.load(open(sys.argv[1]))
qbp = pathlib.Path(sys.argv[2])
outp = sys.argv[3]


def strip(s):
    s = re.sub(r"/-.*?-/", "", s, flags=re.S)
    return re.sub(r"--.*", "", s)


code = ""
for p in qbp.rglob("*.lean"):
    if p.relative_to(qbp).parts[0] in (".lake", "lean-toolcheck"):
        continue
    code += strip(p.read_text(errors="replace")) + "\n"
words = set(re.findall(r"[A-Za-z_][\w'.!?]*", code))

STOP = {
    "module",
    "def",
    "error",
    ".all",
    "all",
    "fun",
    "match",
    "return",
    "try",
    "theorem",
    "instance",
    "where",
    "with",
    "then",
    "else",
    "let",
    "have",
    "show",
    "from",
    "open",
    "end",
    "namespace",
    "section",
    "variable",
    "structure",
    "class",
    "inductive",
    "abbrev",
    "example",
    "true",
    "false",
    "True",
    "False",
    "Type",
    "Prop",
    "Sort",
    "by",
    "at",
    "in",
    "do",
    "for",
    "if",
    "set_option",
    "simp",
    "dsimp",
    "rfl",
    "omega",
    "decide",
    "Nat",
    "Int",
    "List",
    "Array",
    "String",
    "Bool",
    "Option",
    "Unit",
    "IO",
    "Float",
    "Fin",
    "default",
    "id",
    "map",
    "get",
    "set",
    "none",
    "some",
    "pure",
    "bind",
    "trivial",
    "and",
    "or",
    "not",
    "eq",
    "ne",
}


def used(ident):
    ident = ident.strip("`")
    if (
        not ident
        or len(ident) < 3
        or ident in STOP
        or not re.match(r"^[A-Za-z_][\w'.]*$", ident)
    ):
        return False
    return ident in words or (
        ("." in ident) and ident.split(".")[-1] in words and ident in code
    )


QBP_TACTICS = [
    "decide",
    "simp",
    "dsimp",
    "simpa",
    "simp_rw",
    "omega",
    "rfl",
    "ext",
    "funext",
    "rcases",
    "obtain",
    "rintro",
    "induction",
    "cases",
    "calc",
    "unfold",
    "show",
    "change",
    "split",
    "split_ifs",
    "constructor",
    "exact",
    "apply",
    "rw",
    "rewrite",
    "refine",
    "intro",
    "by_contra",
    "trivial",
    "push_cast",
    "norm_cast",
    "exact_mod_cast",
    "subst",
    "congr",
    "native_decide",
    "first",
    "all_goals",
    "any_goals",
    "repeat",
    "have",
    "let",
    "exfalso",
    "absurd",
    "contradiction",
    "assumption",
    "symm",
    "trans",
    "use",
    "exists",
    "left",
    "right",
    "specialize",
    "generalize",
    "set",
    "clear",
    "revert",
    "fin_cases",
    "infer_instance",
    "rename_i",
    "next",
    "case",
    "<;>",
    "with_reducible",
    "refl",
    "norm_num",
    "ring",
    "linarith",
    "positivity",
    "abel",
]
NOT_USED_TACTICS = [
    "grind",
    "bv_decide",
    "mvcgen",
    "mvcgen'",
    "sym",
    "cbv",
    "lia",
    "bv_omega",
    "ac_rfl",
    "ac_nf",
    "fun_induction",
    "fun_cases",
    "simp_arith",
    "massumption",
    "mintro",
    "mspec",
    "mframe",
    "spec",
    "try?",
    "exact?",
    "apply?",
    "rw?",
    "hint",
    "observe",
    "suggest",
    "grind?",
    "simp?",
    "decreasing",
    "termination_by",
    "partial_fixpoint",
    "coinductive",
    "Sym",
    "SymM",
    "order",
    "linear_combination'",
    "cutsat",
    "bitvec",
    "BitVec",
    "Std.Do",
    "Hoare",
    "monadic",
    "do-notation",
    "native",
]

KEY_LANG = [
    "structure",
    "instance",
    "deriving",
    "DecidableEq",
    "Decidable",
    "inductive",
    "match",
    "notation",
    "namespace",
    "section",
    "variable",
    "open ",
    "scoped",
    "attribute",
    "@[simp]",
    "noncomputable",
    "set_option",
    "maxRecDepth",
    "maxHeartbeats",
    "kernel",
    "defeq",
    "definitional",
    "transparency",
    "reducible",
    "coercion",
    "deprecat",
    "#print",
    "axiom",
    "sorry",
    "instances",
    "typeclass",
    "type class",
    "unification",
    "projection",
    "`Fin`",
    "OfNat",
    "numeral",
]
NOT_LANG = [
    "module system",
    "`module`",
    "public import",
    "`public`",
    "`meta`",
    "meta import",
    "`expose`",
    "@[expose]",
    "private import",
    "import all",
    "`#where`",
    "Verso",
    "verso",
    "IR ",
    "LCNF",
    "toLCNF",
    "codegen",
    "language server",
    "LSP",
    "hover",
    "infoview",
    "widget",
    "do`",
    "`do`",
    "`do ",
    "do block",
    "do notation",
    "`for`",
    "`while`",
    "`repeat`",
    "async",
    "Async",
    "HTTP",
    "Http",
    "Task",
    "thread",
    "Std.Time",
    "Timestamp",
    "WallTime",
    "ByteArray",
    "UInt",
    "Int8",
    "Int16",
    "Int32",
    "Int64",
    "ISize",
    "USize",
    "Char",
    "String.",
    "Substring",
    "Slice",
    "Iterator",
    "Iter",
    "HashMap",
    "HashSet",
    "TreeMap",
    "TreeSet",
    "DHashMap",
    "ExtHashMap",
    "Vector",
    "Array.",
    "BitVec",
    "Sym",
    "mvcgen",
    "grind",
    "cbv",
    "bv_decide",
    "Lake",
    "lake",
    "server",
    "Server",
    "FFI",
    "Elab.",
    "MetaM",
    "TermElabM",
    "CoreM",
    "Lean.Meta",
    "Lean.Elab",
    "metaprogram",
    "MessageData",
    "SnapshotTree",
    "Environment",
    "env extension",
    "EnvExtension",
    "olean",
    "compacted region",
    "mimalloc",
    "LLVM",
    "C code",
    "emitC",
    "IO.",
    "System.",
    "FilePath",
    "Process",
    "Signal",
    "socket",
    "Socket",
    "Std.Net",
    "uv",
    "libuv",
    "TCP",
    "UDP",
    "DNS",
    "Option.",
    "Except",
    "ExceptT",
    "StateT",
    "ReaderT",
    "EStateM",
    "Functor",
    "Monad",
    "monad",
]

B = "breaking"
R = "relevant"
OVERRIDES = {
    14577: (
        R,
        "kernel SOUNDNESS fix (nested inductives w/ phantom params; v4.32.2 point release) — pinned v4.30.0 kernel is affected; target must contain it",
    ),
    14498: (
        R,
        "kernel SOUNDNESS fix (opaque values with fvars; v4.32.1 point release) — pinned v4.30.0 kernel is affected; target must contain it",
    ),
    13636: (
        B,
        "TOP BITE: `simpa using h` now closes at REDUCIBLE transparency — QBP has 70 `simpa` uses in 17 files (CDLifting 18, RuleFlow 10); migration = `simpa using!`; T09 `simpa_using` covers the shape",
    ),
    13492: (
        B,
        "stricter `@[defeq]` inference — changes which `rfl`-proved `@[simp]` lemmas `dsimp` may use; QBP declares 75 `@[simp]` lemmas, many `:= rfl` (CDAlg/CrystalHosting); T09/T11 cover the shape",
    ),
    13363: (
        R,
        "matcher unfolding transparency allowlist — affects `simp`/`decide` through `match`-defined tables (T01 `qtab`, QBP basis tables)",
    ),
    13512: (
        R,
        "equation-lemma generation at reducible transparency — affects `simp only [f]`/`unfold f` on QBP defs (T09 dsimp_def, T16 unfold)",
    ),
    13317: (
        R,
        "opt-in rfl-simp transparency linter — useful diagnostic for #723 migration; not on by default",
    ),
    13807: (
        B,
        "app elaborator beta-reduces arguments — may make existing `dsimp only`/`show` steps unnecessary or change goal shape; QBP uses `show`/`change` 182× in 20 files",
    ),
    8309: (
        B,
        "TOP BITE: `Decidable p` becomes a structure (Bool + proof) — the object every kernel `decide` reduces; QBP has 707 `decide` uses in 30 files, custom `Decidable` instances (Octonion32Count, SedenionOctonionCount, Breakdown) and memory-bound sweeps (Octonion32Count 4.6 GiB, #633) — re-measure RSS; T01/T02/T11/T12 + MF04 cover it",
    ),
    15430: (
        R,
        "`Decidable` And/Or instances `macro_inline` again — compiled short-circuiting; kernel `decide` on ∧/∨ (T01, T02) re-checked",
    ),
    14583: (
        B,
        "defeq/unification heuristic change — can alter elaboration of any proof; caught only by the full project rebuild (G1) — no isolated test possible",
    ),
    13895: (
        B,
        "`backward.isDefEq.respectTransparency.types` ON by default — instance/metavariable assignment stricter; affects hand-built instance stacks (T11 NonUnitalNonAssocRing/IsScalarTower, QBP CDAlg/ArtinSpan)",
    ),
    14624: (
        B,
        "instance-search metavariables assigned only up to instance transparency (affected Mathlib decls) — QBP's hand-written instances (CDAlg, ArtinSpan) must re-elaborate; T11 covers the shape",
    ),
    13637: (
        R,
        "transparency levels split (`implicit_reducible` vs `instance_reducible`) — QBP sets no reducibility attributes, but instance unfolding in `decide` may change (T02/T11)",
    ),
    14854: (
        R,
        "`constructor` warns when several constructors match (`constructor!` keeps old behaviour) — QBP uses `constructor` 65× in 20 files; warnings, not errors; T16 `and_build`",
    ),
    7577: (
        R,
        "`simp`/`conv` use `pi_congr` — can change simp results under binders (T09 `simp_rw_binder`)",
    ),
    14267: (
        R,
        "`Fin.foldl` now reduces in the kernel — may let more `decide` goals close; T18 (`decide +kernel` / `Fin.foldl_succ`) + KL02 probe (elaborator `decide` stuck at v4.30.0, expected to flip)",
    ),
    14554: (
        R,
        "`Fin.foldl` type-theoretic vs runtime split — QBP never names `Fin.foldl`, but kernel `decide` over Fin-indexed sweeps reduces through core folds; T18 + KL02 + the G1 rebuild and the heavy-`decide` RSS re-measure (with lean4#8309). Reclassified from not-relevant (Red Team on PR #824)",
    ),
    14316: (
        R,
        "type-class resolution cache persists across commands — performance; correctness covered by rebuild",
    ),
    15399: (
        R,
        "TC cache invalidation on reducibility/scoped attribute change — `attribute [local simp]`/scoped use (T09)",
    ),
    14091: (
        R,
        "`Float` redefined as a wrapper of `Float.Model` — the Float oracle (QBP/Oracle/FloatCompute.lean, QBP/Units/Oracle.lean) must still compile; T17 covers the API shape",
    ),
    14079: (R, "`Float.Model` logical model added — groundwork for #14091; T17"),
    14953: (
        B,
        "TOP BITE (tooling, not proofs): `Lean.ofReduceBool`/`trustCompiler` REMOVED — `native_decide` now asserts per-call axioms; any check keyed on the name `ofReduceBool` goes blind. QBP: scripts/check_anchor_manifest.py is subset-based (OK); docstrings in Sprint12-Inherited/SedenionHessianTraceSq.lean + docs name `ofReduceBool` (stale after bump); MF02 is name-agnostic",
    ),
    14582: (
        R,
        "kernel rejects non-uniform inductive occurrences (soundness hardening) — QBP's inductives are plain enumerations (T02 `Op`); rebuild confirms",
    ),
    14849: (
        R,
        "kernel caps Nat literal size at 128 MB (`LEAN_NAT_MAX_SIZE`) — QBP's kernel `decide` sweeps use small numerals; rebuild confirms",
    ),
    14833: (
        R,
        "official releases now link GMP 6.3.0 (older GMP had unsound corner cases) — kernel bignum trust base; MF04/T12 exercise kernel arithmetic",
    ),
    14807: (R, "kernel `is_prop` SOUNDNESS fix — trust base; target must contain it"),
    14806: (
        R,
        "kernel `is_def_eq` cache SOUNDNESS fix — trust base; target must contain it",
    ),
    13002: (
        R,
        "`deprecated_module` — Mathlib now ships 164 deprecated-module shims; QBP imports 3 of them at v4.35.0 (Mathlib.Data.Real.Basic, .Complex.Basic, .Real.Sign → Mathlib.Basic.*); warnings, T00 import surface surfaces them",
    ),
    14564: (
        R,
        "deprecated-module warning position — cosmetic; relevant only because QBP will hit 3 deprecated modules",
    ),
    13195: (
        R,
        "deprecated options warn on `set_option` — QBP sets maxRecDepth/maxHeartbeats/linter options only; re-check warnings on bump",
    ),
    14478: (R, "option deprecation via `@[deprecated]` — as #13195"),
    13803: (
        "not-relevant",
        "renames the `defLemma` linter — QBP sets no option for it",
    ),
    13595: (
        "not-relevant",
        "silences deprecation warnings inside deprecated defs — QBP declares none",
    ),
    13486: (
        "not-relevant",
        "`do`-notation control-flow analysis — QBP's only `do` blocks are 2 trivial `IO` mains",
    ),
    13367: (
        R,
        "removes `simp` timeout overruns — performance of `simp`; rebuild timing (R6 baseline) will show it",
    ),
    13243: (
        "not-relevant",
        "structure-instance notation *in patterns* — QBP has no structure-instance patterns (grep)",
    ),
    13245: (
        "not-relevant",
        "dotted-function `@.f`/universe syntax extension — additive; QBP does not use",
    ),
    13108: (
        "not-relevant",
        "`deprecated_syntax` command — QBP uses none of the deprecated syntaxes (peel/whatsnew/countHeartbeats; grep 0)",
    ),
    13938: (
        "not-relevant",
        "`@[csimp]` runtime replacements for `Nat` bounded-quantifier instances — affects compiled evaluation only, not kernel `decide`",
    ),
    14333: (
        "not-relevant",
        "`@[deprecated]` self-reference error — QBP declares no deprecations",
    ),
    14303: (
        "not-relevant",
        "removes internal simproc helper defs — QBP references none by name",
    ),
    14255: (
        "not-relevant",
        "renames `Int.Linear` (omega/grind internals) — QBP never references it by name; `omega` itself unchanged (T16)",
    ),
    14212: ("not-relevant", "adds `List.Nodup.length_le_of_subset` — additive"),
    14195: ("not-relevant", "`vcgen` frame inference — QBP does not use vcgen/mvcgen"),
    14603: (
        "not-relevant",
        "`requires`/`invariant` contract clauses (intrinsic verification) — QBP does not use",
    ),
    14533: (
        "not-relevant",
        "deprecated-syntax warning display — QBP uses no deprecated syntax",
    ),
    14523: ("not-relevant", "deprecates `letFun` — QBP never names it (grep 0)"),
    12166: (
        "not-relevant",
        "List lemma dependency refactor — QBP does not use `pairwise_iff_getElem`",
    ),
    14462: (
        "not-relevant",
        "renames `Nat.div_eq`/`Nat.mod_eq` → `*_ite` — QBP never names them (grep 0)",
    ),
    15020: (
        "not-relevant",
        "Syntax `SepArray` coercions (metaprogramming) — QBP has no macros",
    ),
    14940: (
        "not-relevant",
        "deprecated-syntax warning focus in macros — QBP has no macros",
    ),
    14925: (
        R,
        "`casesOn`/`recOn` of a proposition reduce via projections — can change definitional unfolding in `decide`/`rfl` over `And` structures; rebuild confirms",
    ),
    14858: (
        "not-relevant",
        "`ensures` clause syntax (intrinsic verification) — QBP does not use",
    ),
    14816: (
        "not-relevant",
        "`@[deprecated]` replacement-chain warning — QBP declares no deprecations",
    ),
    14600: ("not-relevant", "deprecation-defeq warning — QBP declares no deprecations"),
    15239: (
        "not-relevant",
        "removes a redundant pass for structurally recursive defs — performance only",
    ),
    15594: (
        "not-relevant",
        "renames internal error-helper functions — QBP references none",
    ),
    15217: ("not-relevant", "`EPred`→`EPosts` in Std.Do — QBP does not use Std.Do"),
    15171: ("not-relevant", "`Std.WP` renames — QBP does not use Std.WP"),
    13683: (
        R,
        "compiled Lake config moves to the workspace `.lake/config` — matters for the borrowed-`.lake/packages` symlink used by run.sh; re-check on the bump branch",
    ),
    15141: (
        "not-relevant",
        "`lake build --package` / `lake cache put` — QBP never uploads caches",
    ),
}


def classify(it):
    if it["pr"] in OVERRIDES:
        return OVERRIDES[it["pr"]]
    t, sec = it["text"], it["sec"]
    if re.search(
        r"`sym =>`|\bSymM\b|\bSym\.|`Sym`|sym mode|\bvcgen\b|\bmvcgen|\bcontract\b|intrinsic verification|`requires`|`ensures`|Std\.Do|Std\.WP|\bWP\b|PredTrans",
        t,
    ):
        return (
            "not-relevant",
            "Sym/vcgen/mvcgen/contract (intrinsic-verification) machinery — QBP does not use it (0 uses)",
        )
    if re.search(
        r"do-block|`do`|do block|do notation|doLet|doHave|ControlInfo|`mut`|`for`|`while`|`repeat`|loop",
        t,
    ):
        return (
            "not-relevant",
            "`do`-notation / loops — QBP's only `do` blocks are 2 trivial `IO Unit` mains (T17 type-checks the shape)",
        )
    if re.search(r"\blinter\b|lint", t) and not re.search(
        r"unusedSimpArgs|unnecessarySeqFocus|unusedVariables", t
    ):
        return (
            "not-relevant",
            "linter framework / new linter — warnings only; QBP's CI fails on errors, not warnings",
        )
    if re.search(
        r"(?i)error message|improves the message|hint|diagnos|hover|infoview|InfoTree|autocompletion|go to definition|docstring",
        t,
    ) and not re.search(r"axiom|sorry", t):
        return (
            "not-relevant",
            "diagnostic / editor text only — does not change what elaborates",
        )
    tl = t.lower()
    idents = re.findall(r"`([^`]{2,60})`", t)
    used_ids = sorted({i for i in idents if used(i)})
    breaking = bool(
        re.search(
            r"breaking change|\bbreaking\b|\brenames?\b|\bremoves?\b|\bdeprecat|no longer|now (?:requires|rejects|errors|fails)",
            tl,
        )
    )
    soundness = bool(
        re.search(
            r"soundness|proof of `?false|unsound|use-after-free|kernel (?:now )?rejects|kernel bug",
            tl,
        )
    )
    if soundness:
        return (
            "relevant",
            "kernel/runtime SOUNDNESS fix — trust base of every QBP proof; #723 must land on a version containing it (covered by MF04 + full project rebuild)",
        )
    if sec in ("Lake",):
        if re.search(
            r"cache|manifest|`require`|lakefile|default_target|lean_lib|lean_exe|srcdir|`roots`|lake env|lake update|lake exe|lake build|toolchain",
            tl,
        ):
            if breaking:
                return (
                    "breaking",
                    "Lake behaviour QBP uses (build/env/cache/manifest/targets) — exercised by run.sh preflight + CI `lake build` on the bump branch"
                    + (f"; touches {used_ids}" if used_ids else ""),
                )
            return (
                "relevant",
                "Lake build/env/cache path QBP uses — exercised by run.sh (`lake env lean`) + CI `lake build`",
            )
        return (
            "not-relevant",
            "Lake feature QBP does not use (QBP uses only `lake build`, `lake env`, `lake exe cache get`, `lake exe <oracle>`)",
        )
    if sec in ("Server",):
        return (
            "not-relevant",
            "editor/LSP server behaviour — no effect on batch `lake build` results",
        )
    if sec == "Documentation":
        return "not-relevant", "documentation-only change"
    if sec == "FFI":
        return (
            "not-relevant",
            "C FFI — QBP's only FFI file (QBP/Oracle/FFI.lean) is build-invisible/quarantined (#644)",
        )
    if sec == "Pretty Printing":
        if re.search(r"axiom|#print|sorry", tl):
            return (
                "relevant",
                "pretty-printing of `#print axioms`/sorry output — run.sh's axiom-audit parser depends on it (every test file)",
            )
        return (
            "not-relevant",
            "pretty-printing/delaboration only — proofs unaffected; run.sh parses only `#print axioms` lines",
        )
    if sec == "Compiler":
        if re.search(
            r"float|`io`|io\.|string|native_decide|ofreducebool|reducebool|implemented_by",
            tl,
        ):
            return (
                "relevant",
                "compiled-code path the Float oracle exe or native_decide relies on — T17 (Float/IO compile) + MF02 (native_decide detection)",
            )
        return (
            "not-relevant",
            "code generation / runtime internals — QBP proofs are kernel-checked; compiled code only backs the Float oracle exes",
        )
    if sec == "Other":
        if re.search(r"gmp|kernel|nat literal|bignum", tl):
            return (
                "relevant",
                "kernel arithmetic / trust base — MF04 + T01/T12 kernel `decide` cover it",
            )
        return "not-relevant", "release process / CI / test-suite / packaging change"
    # Tactics / Language / Library
    for k in NOT_USED_TACTICS:
        if re.search(r"(?<![\w])`?" + re.escape(k) + r"`?(?![\w'])", t) and not any(
            re.search(r"`" + re.escape(q) + r"`", t)
            for q in [
                "decide",
                "simp",
                "omega",
                "rfl",
                "dsimp",
                "simpa",
                "native_decide",
                "exact",
                "rw",
                "cases",
                "induction",
            ]
        ):
            return (
                "not-relevant",
                f"concerns `{k}` — not used by QBP (0 uses, 2026-11-20 grep)",
            )
    for k in NOT_LANG:
        if (
            k in t
            and not used_ids
            and not re.search(
                r"`(decide|simp|dsimp|simpa|omega|rfl|native_decide|instance|deriving|structure)`",
                t,
            )
        ):
            return (
                "not-relevant",
                f"concerns {k.strip('`').strip()} — a Lean surface QBP does not use",
            )
    hit_tac = [
        q for q in QBP_TACTICS if re.search(r"`" + re.escape(q) + r"(?:[ `!?]|$)", t)
    ]
    hit_lang = [k for k in KEY_LANG if k in t]
    if breaking and (hit_tac or used_ids or hit_lang):
        why = []
        if hit_tac:
            why.append("tactics " + ", ".join(hit_tac[:4]))
        if used_ids:
            why.append("identifiers QBP uses: " + ", ".join(used_ids[:4]))
        if hit_lang and not why:
            why.append("constructs " + ", ".join(hit_lang[:3]))
        return (
            "breaking",
            "touches QBP usage ("
            + "; ".join(why)
            + ") — must be re-checked on the bump branch",
        )
    if breaking:
        return (
            "breaking-no-touch",
            "breaking for its feature, but none of the named identifiers/tactics occur in QBP"
            + (f" (checked: {', '.join(idents[:4])})" if idents else ""),
        )
    if hit_tac or used_ids:
        why = []
        if hit_tac:
            why.append("tactics " + ", ".join(hit_tac[:4]))
        if used_ids:
            why.append("identifiers " + ", ".join(used_ids[:4]))
        return (
            "relevant",
            "QBP uses "
            + "; ".join(why)
            + " — covered by the tool tests / project rebuild",
        )
    if sec == "Library":
        return (
            "not-relevant",
            "core-library addition/change in an API QBP does not reference"
            + (f" ({', '.join(idents[:3])})" if idents else ""),
        )
    if hit_lang:
        return (
            "relevant",
            "language/elaboration change on constructs QBP uses ("
            + ", ".join(hit_lang[:3])
            + ") — covered by tests + project rebuild",
        )
    return (
        "not-relevant",
        "internal / metaprogramming / error-message change with no QBP-visible surface",
    )


items = items + [
    {
        "ver": "v4.32.1",
        "sec": "Point release (prose)",
        "pr": 14498,
        "text": "point release: fixes a kernel soundness bug (issue #14484); a malicious meta program in-process could make the kernel accept False",
    },
    {
        "ver": "v4.32.2",
        "sec": "Point release (prose)",
        "pr": 14577,
        "text": "point release: fixes a kernel soundness bug in nested inductives with phantom type parameters (issue #14576); exploitable even under comparator",
    },
]
res = []
for it in items:
    d, r = classify(it)
    res.append({**it, "disp": d, "reason": r})
json.dump(res, open(outp, "w"), indent=1, ensure_ascii=False)
c = collections.Counter(x["disp"] for x in res)
print(c)
print(collections.Counter((x["ver"], x["disp"]) for x in res))
