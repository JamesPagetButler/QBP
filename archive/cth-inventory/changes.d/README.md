# CTH ledger change fragments

QBP#817 variant A (beekeeper-ruled 2026-11-16). A content PR that edits the CTH
ledger adds exactly one fragment file here — `<issue>-<slug>.json` — instead of
hand-writing the ledger's `version`/`changelog[]`/`last_updated` (that's now
impossible by construction: `scripts/cth_ledger_edit.py`'s `LedgerEdit.touch()`
refuses those three keys outright).

Write a fragment with `scripts/ledger_fragment.write_fragment(...)`, never by
hand — see that script's docstring for the exact shape. Read the full design
and rationale in `docs/cth/qbp-local-extensions.md`, under "Frozen ledger
bookkeeping".

This directory is **append-only**: once a fragment lands on master, nothing
ever edits or removes it (`scripts/ledger_bookkeeping_lint.py` enforces this in
CI). `scripts/ledger_version.py` derives the ledger's current reporting version
from the merge order of the fragments here; `scripts/generate_ledger_changelog_
view.py` renders the human-readable table at `analysis/cth-ledger-changelog.md`.
