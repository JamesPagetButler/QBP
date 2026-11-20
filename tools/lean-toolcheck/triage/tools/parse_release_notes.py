from __future__ import annotations

"""Parse Lean release-note .lean (Verso) files (read as TEXT only) into items."""

import re, sys, json, pathlib, collections
from typing import Any

d = pathlib.Path(sys.argv[1])
items: list[dict[str, Any]] = []
for f in sorted(d.glob("v4_*.txt")):
    ver = "v" + f.stem[1:].replace("_", ".")
    lines = f.read_text().splitlines()
    sec = "?"

    cur: dict[str, Any] | None = None
    for l in lines:
        m = re.match(r"^# (.+)$", l)
        if m:
            sec = m.group(1).strip()
            if cur:
                items.append(cur)
                cur = None
            continue
        m = re.match(
            r"^- \[#(\d+)\]\(https://github.com/leanprover/lean4/pull/\d+\)\s*(.*)$", l
        )
        if m and sec not in ("Highlights",) and not sec.startswith("Lean 4"):
            if cur:
                items.append(cur)
            cur = {"ver": ver, "sec": sec, "pr": int(m.group(1)), "text": m.group(2)}
            continue
        if cur is not None:
            if l.startswith("  ") or l == "":
                cur["text"] = str(cur["text"]) + " " + l.strip()
            else:
                items.append(cur)
                cur = None
    if cur:
        items.append(cur)
for it in items:
    it["text"] = re.sub(r"\s+", " ", str(it["text"])).strip()
json.dump(items, open(sys.argv[2], "w"), indent=1)
c = collections.Counter((i["ver"], i["sec"]) for i in items)
for k, v in sorted(c.items()):
    print(k, v)
print("TOTAL", len(items))
print("versions", collections.Counter(i["ver"] for i in items))
