#!/usr/bin/env bash
# test_check_vendor_upstream.sh — mutation tests for check_vendor_upstream.sh (QBP#694 R1/R5).
# Runs the check on a scratch COPY of tools/cth-pa; the real tree is never modified.
# usage: test_check_vendor_upstream.sh <confluent-trust-checkout> <pin>
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: $0 <confluent-trust-checkout> <pin>" >&2; exit 64; }
UP="$1"; PIN="$2"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
cp -r "$HERE" "$T/cth-pa"
V="$T/cth-pa"; META="$V/VENDOR.meta.json"; CHECK="$V/scripts/check_vendor_upstream.sh"
cp "$META" "$T/meta.bak"

run() { bash "$CHECK" "$UP" "$PIN" >"$T/out" 2>&1; echo $?; }
reset() { cp "$T/meta.bak" "$META"; rm -rf "$V/vendor-src" "$V/testdata"; cp -r "$HERE/vendor-src" "$HERE/testdata" "$V/"; }
expect() { local want="$1" name="$2" got; got="$(run)"; if [ "$got" = "$want" ]; then echo "PASS  $name (exit $got)"; else echo "FAIL  $name: exit $got, wanted $want"; sed -n '1,12p' "$T/out"; exit 1; fi; reset; }

pymeta() { python3 - "$META" "$@" <<'PY'
import json, sys, hashlib
p, op = sys.argv[1], sys.argv[2]
m = json.load(open(p))
if op == "sed_payload":
    m["import_rewrites"][-1]["to"] = "x#; s#backdoor##; s#x"
elif op == "extra_pair":
    m["import_rewrites"].append({"from": "github.com/JamesPagetButler/confluent-trust/internal/leanlink",
                                 "to": "github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/leanlink"})
elif op == "drop_pair":
    m["import_rewrites"] = m["import_rewrites"][:-1]
elif op == "fix_sha":
    path = sys.argv[3]
    for f in m["files"]:
        if f["vendored_path"] == path:
            f["vendored_sha256"] = hashlib.sha256(open(sys.argv[4], "rb").read()).hexdigest()
elif op == "drop_row":
    m["files"] = [f for f in m["files"] if f["vendored_path"] != sys.argv[3]]
json.dump(m, open(p, "w"), indent=2)
PY
}

expect 0 "clean tree is OK"
pymeta sed_payload;                                   expect 1 "R5 (iii): sed-injection payload in meta rewrite refused"
pymeta extra_pair;                                    expect 1 "R5 (ii): extra meta rewrite pair refused"
pymeta drop_pair;                                     expect 1 "R5: missing meta rewrite pair refused"
printf '\n' >> "$V/vendor-src/pa/pa.go"; pymeta fix_sha vendor-src/pa/pa.go "$V/vendor-src/pa/pa.go"
                                                      expect 1 "tamper: one byte in pa.go with colluding meta sha fails the byte diff"
rm "$V/vendor-src/attestation/attestation_test.go"; pymeta drop_row vendor-src/attestation/attestation_test.go
                                                      expect 1 "R1: dropped vendored file (and its meta row) refused"
echo 'package pa' > "$V/vendor-src/pa/extra.go";     expect 1 "R1: extra vendored file refused"
python3 - "$META" <<'PY'
import json,sys; p=sys.argv[1]; m=json.load(open(p)); m["source_sha"]="0"*40; json.dump(m,open(p,"w"),indent=2)
PY
                                                      expect 1 "pin: meta source_sha != argument pin refused"
echo "ALL MUTANTS CAUGHT"
