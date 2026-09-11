# Applied one-shot encoders (history — do not re-run)

These scripts each encoded one reviewed batch into the CTH ledger and have already been
applied (the ledger changelog names the PR for each). They rewrote the whole ledger with
`json.dump` — the pattern retired by issue #654 D7: every new encoder writes through
`scripts/cth_ledger_edit.py`, which proves the write is confined to the declared records,
that no declared edit silently failed to land, and that no formatting noise is introduced.
`tests/test_cth_ledger_edit.py` guards that no top-level `scripts/*.py` writes the ledger
directly. They are kept here, unmodified, as the provenance of what was encoded and how.

| script | batch | PR |
|---|---|---|
| encode_473_anchors.py | #473 δ-landscape | #631 |
| encode_473_ac1_anchors.py | #473 AC1 | #640 |
| encode_473_ac2_disposition.py | #473 AC2 disposition | #640 |
| encode_619_anchors.py | #619 orphan anchoring | #628 |
| encode_639_hosting_anchors.py | #639 hosting | #641 |
| encode_holographic_anchors.py | #642 holographic subalgebra | #642 |
| encode_p2_lean_anchors.py | #649 P2 Lean anchors | #653 |
| apply_option_b_deriv_sedenion.py | #647 option B (DERIV-sedenion clause) | #651 |
