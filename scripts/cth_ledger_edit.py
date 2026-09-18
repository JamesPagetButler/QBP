#!/usr/bin/env python3
"""Confined, surgical edits to the CTH ledger — issue #654 D7.

Rule (qbp-implementor, live-test seq 1293; devops agent boundary 4): never rewrite the
whole ledger blind. An encoder declares every record it touches; on exit this context
manager proves that ONLY those records changed, that every declared record actually
changed (a silent no-op is a finding, not a success — the 2026-09 silent-abort fault),
and that the file's formatting is canonical (a json.dump round-trip of the untouched
file is byte-identical) so the write introduces no formatting noise. Only then is the
file written, with the canonical settings. Anything else raises and writes nothing.

Usage (see scripts/encode_ruling_bundle.py):

    from cth_ledger_edit import ledger_edit

    with ledger_edit(LEDGER, dry_run=args.dry_run) as e:
        L = e.ledger                                   # the parsed ledger, mutate in place
        a = e.record("anchors", "PRED-x")              # fetch + declare a record edit
        a["status"] = "coherent"
        e.append("anchors", {"id": "PRED-new", ...})   # declare an appended record
        e.remove("axioms", "AXIOM-2")                  # declare a removed record (returns it)
        e.touch("changelog")                           # declare a non-id top-level key edit
    # on exit: confinement proven, file written (unless dry_run); e.summary is printed

Record lists are top-level lists whose items carry an `id`. `meta_axiom` (a single
object) is treated as a one-record list under its own key.
"""

import contextlib
import json
from collections import OrderedDict

CANON = dict(ensure_ascii=False, indent=2)


class ConfinementError(AssertionError):
    pass


def canonical_dump(obj):
    return json.dumps(obj, **CANON) + "\n"


def _records(ledger):
    """{key: {id: record}} for every top-level list of id-carrying records (and the
    single-object meta_axiom); {key: value} for everything else."""
    recs, scalars = OrderedDict(), OrderedDict()
    for k, v in ledger.items():
        if (
            isinstance(v, list)
            and v
            and all(isinstance(x, dict) and "id" in x for x in v)
        ):
            ids = [x["id"] for x in v]
            if len(ids) != len(set(ids)):
                dup = sorted({i for i in ids if ids.count(i) > 1})
                raise ConfinementError(f"{k}: duplicate ids {dup}")
            recs[k] = OrderedDict((x["id"], x) for x in v)
        elif isinstance(v, dict) and "id" in v:
            recs[k] = OrderedDict([(v["id"], v)])
        elif isinstance(v, list) and not v:
            recs[k] = OrderedDict()
        else:
            scalars[k] = v
    return recs, scalars


class LedgerEdit:
    def __init__(self, path, dry_run=False):
        self.path, self.dry_run = path, dry_run
        with open(path, encoding="utf-8") as f:
            self._raw = f.read()
        self.ledger = json.loads(self._raw, object_pairs_hook=OrderedDict)
        if canonical_dump(self.ledger) != self._raw:
            raise ConfinementError(
                f"{path} is not in canonical form (indent=2, ensure_ascii=False, trailing "
                f"newline): a whole-file write would introduce formatting noise. Canonicalise "
                f"it in its own commit first."
            )
        self._before = json.loads(self._raw)  # independent deep copy
        self.declared = set()  # (key, id) or (key, None) for non-record keys
        self.summary = ""

    # --- declarations -------------------------------------------------------------
    def record(self, key, rid):
        recs, _ = _records(self.ledger)
        if key not in recs or rid not in recs[key]:
            raise KeyError(f"{key}[{rid}] not in ledger")
        self.declared.add((key, rid))
        return recs[key][rid]

    def append(self, key, rec):
        if not isinstance(rec, dict) or "id" not in rec:
            raise ConfinementError(f"append to {key}: record has no id")
        self.ledger.setdefault(key, [])
        if any(x.get("id") == rec["id"] for x in self.ledger[key]):
            raise ConfinementError(f"{key}[{rec['id']}] already exists (use record())")
        self.ledger[key].append(rec)
        self.declared.add((key, rec["id"]))
        return rec

    def remove(self, key, rid):
        lst = self.ledger.get(key, [])
        for i, x in enumerate(lst):
            if x.get("id") == rid:
                self.declared.add((key, rid))
                return lst.pop(i)
        raise KeyError(f"{key}[{rid}] not in ledger")

    SENTINELS = ("<record order>", "<top-level key order>")

    def touch(self, key, rid=None):
        """Declare an edit to a non-record top-level key (changelog, last_updated, …) or,
        with rid, to a record you mutate through another reference. Order sentinels cannot
        be declared: reordering is never a confined edit (PR #658 round-2 NF-5)."""
        if key in self.SENTINELS or rid in self.SENTINELS:
            raise ConfinementError(f"order changes cannot be declared: {(key, rid)}")
        self.declared.add((key, rid))

    # --- verification -------------------------------------------------------------
    def actual_changes(self):
        b_recs, b_sc = _records(self._before)
        a_recs, a_sc = _records(json.loads(json.dumps(self.ledger)))
        changed = set()
        for k in set(b_recs) | set(a_recs):
            bi, ai = b_recs.get(k, {}), a_recs.get(k, {})
            for rid in set(bi) | set(ai):
                # serialised: key ORDER inside a record is content (PR #658 round-2 NF-4)
                if json.dumps(bi.get(rid)) != json.dumps(ai.get(rid)):
                    changed.add((k, rid))
            if k in b_recs and k not in a_recs and not b_recs[k]:
                pass
        for k in set(b_sc) | set(a_sc):
            if json.dumps(b_sc.get(k, "<absent>")) != json.dumps(
                a_sc.get(k, "<absent>")
            ):
                changed.add((k, None))
        # a list key that changed shape (record list <-> scalar) shows up on both sides
        for k in (set(b_recs) ^ set(a_recs)) & (set(b_sc) | set(a_sc)):
            changed.add((k, None))
        # ORDER is content: the top-level key sequence and each record list's id sequence must
        # be identical up to declared appends/removals; any reordering is an undeclared change
        # of the whole key (PR #658 Red Team: a reversed anchors[] wrote a 17k-line diff that
        # the per-record comparison reported as confined).
        # only the KEPT keys' relative order is content; a declared new key (appended) is an
        # addition, not a reorder — same rule as the per-list id sequence below
        b_keys, a_keys = list(self._before.keys()), list(self.ledger.keys())
        if [k for k in b_keys if k in a_keys] != [k for k in a_keys if k in b_keys]:
            changed.add(("<top-level key order>", None))
        # a top-level key added or removed is itself a change and must be declared with
        # touch(key) — even an empty new list (PR #662 Red Team A7)
        for k in set(a_keys) ^ set(b_keys):
            changed.add((k, None))
        for k in set(b_recs) & set(a_recs):
            b_ids, a_ids = list(b_recs[k]), list(a_recs[k])
            kept_b = [i for i in b_ids if i in a_recs[k]]
            kept_a = [i for i in a_ids if i in b_recs[k]]
            if kept_b != kept_a:
                changed.add((k, "<record order>"))
        return changed

    def verify(self):
        changed = self.actual_changes()
        undeclared = sorted(changed - self.declared, key=str)
        silent = sorted(self.declared - changed, key=str)
        if undeclared or silent:
            msg = []
            if undeclared:
                msg.append(
                    f"UNDECLARED changes (the write is not confined): {undeclared}"
                )
            if silent:
                msg.append(
                    f"DECLARED but unchanged (silent no-op — an edit did not land): {silent}"
                )
            raise ConfinementError("; ".join(msg))
        by_key = OrderedDict()
        for k, rid in sorted(changed, key=str):
            by_key.setdefault(k, []).append(rid)
        self.summary = "confined edit: " + "; ".join(
            f"{k}: {len([r for r in v if r is not None]) or 'key'}"
            + (
                f" [{', '.join(str(r) for r in v if r is not None)}]"
                if any(r is not None for r in v)
                else ""
            )
            for k, v in by_key.items()
        )
        return changed

    def write(self):
        out = canonical_dump(self.ledger)
        if not self.dry_run:
            with open(self.path, "w", encoding="utf-8") as f:
                f.write(out)
        return out


@contextlib.contextmanager
def ledger_edit(path, dry_run=False):
    e = LedgerEdit(path, dry_run=dry_run)
    yield e
    e.verify()
    e.write()
    print(("DRY-RUN " if dry_run else "") + e.summary)
