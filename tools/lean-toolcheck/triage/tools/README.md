# Triage generators (R5 template for the next upgrade)

These produced [`../lean-v4.30.0-to-v4.36.0.md`](../lean-v4.30.0-to-v4.36.0.md) on 2026-11-20. Everything they
download is **untrusted data**: put it in its own empty directory, read it as text, never execute or build it,
and run the scripts with `python3 -I`.

| Step | Script | Input → output |
|---|---|---|
| 1 | `fetch_release_notes.py OUTDIR` | `gh api repos/leanprover/reference-manual/contents/Manual/Releases/v4_N_M.lean` (raw) → `OUTDIR/v4_N_M.txt`. Edit the version list for the new range. |
| 2 | `parse_release_notes.py OUTDIR items.json` | the `- [#PR](…)` bullets of each `# Section` → one item per bullet |
| 3 | `classify_items.py items.json <QBP>/proofs triage.json` | rule pass against a usage index of QBP's comment-stripped `.lean` + the hand `OVERRIDES` (one reason per item). **Re-review `OVERRIDES` for each new range** — they are range-specific judgements. The two point-release prose items (4.32.1/4.32.2) are appended by hand at the bottom. |
| 4 | `scan_mathlib_usage.py <QBP>/proofs OLD_MATHLIB NEW_MATHLIB mathlib.json` | text index of declarations / `@[deprecated]` / `deprecated_module` in two Mathlib source trees (old = the pinned `.lake/packages/mathlib`; new = `gh api repos/leanprover-community/mathlib4/tarball/<tag>`, extracted) ∩ QBP's imports and identifiers |
| 5 | `write_triage_md.py triage.json mathlib.json OUT.md` | the per-item table (URLs in item text are replaced by `‹url›` so the markdown link checker does not fetch ~1000 links) |

Limits are stated in `../../FEATURES.md` §2 (method): rule-assigned "not relevant" reasons; the Mathlib scan
cannot see `@[to_additive]`/`irreducible_def` names, simp-set contents or instance changes — the rebuild is the
test for those.
