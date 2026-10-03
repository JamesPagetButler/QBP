#!/usr/bin/env bash
# check_vendor_upstream.sh — the check of record for tools/cth-pa (QBP#692 / QBP#694 R1+R5).
#
# Diffs the vendored engine against the bytes of the same paths in an upstream
# confluent-trust checkout at the pinned commit, after reversing the ONLY
# permitted substitution: the Go import-path rewrite, whose pairs are FIXED
# BELOW (ruling: qbp-architecture, live-test seq 2329, R5). VENDOR.meta.json is
# treated as UNTRUSTED INPUT: it lives in the same PR as the files it describes,
# so nothing here is derived from it except cross-checks that must agree.
#
#   R1  tree set-equality: the vendored file set under vendor-src/{pa,attestation}
#       and testdata/pa must equal the upstream file set of internal/pa,
#       attestation and testdata/pa at the pin (no extras, no omissions), and the
#       meta must list exactly that set.
#   R5  rewrites are hard-coded; the meta's import_rewrites must equal them
#       exactly; replacement is a literal byte replace (never sed/regex).
#   pin the argument must resolve to the meta's source_sha.
#   sha every file's upstream and vendored sha256 must equal the meta's.
#
# usage: check_vendor_upstream.sh <confluent-trust-checkout> <pin>
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <confluent-trust-checkout> <pin>" >&2
  exit 64
fi
UP="$1"
PIN="$2"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
META="$HERE/VENDOR.meta.json"

for bin in git python3; do
  command -v "$bin" >/dev/null || { echo "missing tool: $bin" >&2; exit 69; }
done
[ -f "$META" ] || { echo "missing $META" >&2; exit 66; }

FULL_PIN="$(git -C "$UP" rev-parse --verify "${PIN}^{commit}")" || { echo "pin $PIN does not resolve in $UP" >&2; exit 65; }

# Everything below runs in one Python process so no meta content ever reaches a
# shell, sed, or regex. Fixed constants are the ruling; the meta must agree.
exec python3 - "$UP" "$FULL_PIN" "$HERE" "$META" <<'PY'
import hashlib, json, os, re, subprocess, sys

UP, PIN, HERE, META = sys.argv[1:5]

# ---- R5: the ONLY permitted substitution, fixed here (longest first). --------
UPSTREAM_MOD = "github.com/JamesPagetButler/confluent-trust"
VENDOR_MOD = "github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src"
REWRITES = [  # (upstream import, vendored import) — exact quoted strings only
    (UPSTREAM_MOD + "/attestation/attestationtest", VENDOR_MOD + "/attestation/attestationtest"),
    (UPSTREAM_MOD + "/attestation", VENDOR_MOD + "/attestation"),
    (UPSTREAM_MOD + "/internal/pa", VENDOR_MOD + "/pa"),
]
# ---- R1: the vendored trees and their upstream sources, fixed here. ----------
TREES = [  # (upstream dir at the pin, vendored dir under tools/cth-pa)
    ("internal/pa", "vendor-src/pa"),
    ("attestation", "vendor-src/attestation"),
    ("testdata/pa", "testdata/pa"),
]
SAFE = re.compile(r"^[A-Za-z0-9._/@-]+$")  # no '#', ';', quotes, whitespace, newline

def die(msg, code=1):
    print("RESULT: FAIL — " + msg, file=sys.stderr)
    sys.exit(code)

def safe_path(p, what):
    if not SAFE.match(p) or p.startswith("/") or ".." in p.split("/"):
        die(f"{what} is not a plain relative path: {p!r}")
    return p

def sha256(b):
    return hashlib.sha256(b).hexdigest()

def git_show(path):
    r = subprocess.run(["git", "-C", UP, "show", f"{PIN}:{path}"], capture_output=True)
    return r.stdout if r.returncode == 0 else None

meta = json.load(open(META))

# pin cross-check
if meta.get("source_sha") != PIN:
    die(f"pin mismatch: argument resolves to {PIN} but VENDOR.meta.json records {meta.get('source_sha')}")

# R5: meta rewrites must equal the fixed pairs exactly (order-insensitive, no extras)
meta_rw = {(r.get("from"), r.get("to")) for r in meta.get("import_rewrites", [])}
for a, b in meta_rw:
    for s in (a, b):
        if not isinstance(s, str) or not SAFE.match(s):
            die(f"meta import_rewrites entry is not a plain import path: {s!r}")
if meta_rw != set(REWRITES):
    die("meta import_rewrites differ from the fixed permitted set: "
        f"meta={sorted(meta_rw)} fixed={sorted(REWRITES)}")

# R1: upstream file set at the pin, mapped to vendored paths
expected = {}  # vendored_path -> upstream_path
for up_dir, vd_dir in TREES:
    r = subprocess.run(["git", "-C", UP, "ls-tree", "-r", "--name-only", PIN, "--", up_dir],
                       capture_output=True, text=True)
    if r.returncode != 0:
        die(f"git ls-tree failed for {up_dir} at {PIN}")
    for up_path in r.stdout.split():
        safe_path(up_path, "upstream path")
        expected[vd_dir + up_path[len(up_dir):]] = up_path
if not expected:
    die("upstream tree set is empty — wrong checkout or pin")

# vendored files actually present under the fixed trees
present = set()
for _, vd_dir in TREES:
    root = os.path.join(HERE, vd_dir)
    for dp, _, fns in os.walk(root):
        for fn in fns:
            present.add(os.path.relpath(os.path.join(dp, fn), HERE))

extra = present - set(expected)
missing = set(expected) - present
if extra or missing:
    for p in sorted(extra): print(f"EXTRA    {p} (vendored, not in upstream tree at pin)")
    for p in sorted(missing): print(f"MISSING  {p} (upstream has {expected[p]}, not vendored)")
    die("vendored tree set != upstream tree set (R1)")

# meta must list exactly that set
meta_files = {}
for f in meta.get("files", []):
    vp = safe_path(f["vendored_path"], "meta vendored_path")
    up = safe_path(f["upstream_path"], "meta upstream_path")
    meta_files[vp] = f
    if expected.get(vp) != up:
        die(f"meta maps {vp} to {up}, upstream tree says {expected.get(vp)}")
if set(meta_files) != set(expected):
    die(f"meta file list != tree set: only_meta={sorted(set(meta_files)-set(expected))} "
        f"only_tree={sorted(set(expected)-set(meta_files))}")

fail = False
for vp in sorted(expected):
    up_path = expected[vp]
    up_bytes = git_show(up_path)
    if up_bytes is None:
        print(f"MISSING  {up_path} (not in upstream at {PIN})"); fail = True; continue
    vd_bytes = open(os.path.join(HERE, vp), "rb").read()
    f = meta_files[vp]
    if sha256(up_bytes) != f.get("upstream_sha256"):
        print(f"DRIFT    {up_path} upstream sha256 {sha256(up_bytes)} != meta {f.get('upstream_sha256')}"); fail = True
    if sha256(vd_bytes) != f.get("vendored_sha256"):
        print(f"DRIFT    {vp} vendored sha256 {sha256(vd_bytes)} != meta {f.get('vendored_sha256')}"); fail = True
    # reverse the permitted rewrite: literal byte replace of the exact quoted import
    rev = vd_bytes
    if vp.endswith(".go"):
        for up_imp, vd_imp in REWRITES:
            rev = rev.replace(('"' + vd_imp + '"').encode(), ('"' + up_imp + '"').encode())
    if rev == up_bytes:
        print(f"OK       {up_path} -> {vp}")
    else:
        print(f"DIFF     {up_path} -> {vp}"); fail = True
        import difflib
        for line in list(difflib.unified_diff(
                up_bytes.decode("utf-8", "replace").splitlines(),
                rev.decode("utf-8", "replace").splitlines(),
                "upstream", "vendored(reversed)", lineterm=""))[:40]:
            print("    " + line)

print(f"checked {len(expected)} files against {UP} @ {PIN}")
if fail:
    die("vendored tree is not byte-identical to upstream (modulo the fixed import rewrite)")
print("RESULT: OK")
PY
