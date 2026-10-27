#!/usr/bin/env bash
# Negative control for the fanoTableF4 drift guard (#605 AC2).
#
# Proves the guard catches a DELIBERATELY FALSIFIED snapshot even when the PR also
# modifies its producer script in the same PR (the #604-Gemini self-defeat attack):
# the hardened guard pins the producer to the trusted base commit BEFORE regenerating,
# so the PR's tampered producer can't reproduce its own falsified snapshot.
#
# It uses a STUB producer (no Lean / no lake) in a throwaway git sandbox, so it tests
# the trusted-pin POLICY — the security property #605 adds — not the kernel regen
# (which the workflow exercises for real against QBP.Foundations.FanoOrientationF3).
set -euo pipefail

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"
git init -q
git config user.email t@example.com
git config user.name test
git config commit.gpgsign false

mkdir -p scripts proofs/QBP/Foundations
SNAP=proofs/QBP/Foundations/fanoTableF4.snapshot
PRODUCER=scripts/regen_fano_snapshot.sh

# --- trusted producer on "base" (stands in for origin/master): emits the TRUE table ---
cat > "$PRODUCER" <<'EOF'
#!/usr/bin/env bash
set -e
printf 'TRUE-TABLE\n' > proofs/QBP/Foundations/fanoTableF4.snapshot
EOF
chmod +x "$PRODUCER"
bash "$PRODUCER"
git add -A
git commit -qm base
base=$(git rev-parse HEAD)

# --- "PR": falsify the snapshot AND rewrite the producer to reproduce the lie ---
printf 'FALSE-TABLE\n' > "$SNAP"
cat > "$PRODUCER" <<'EOF'
#!/usr/bin/env bash
set -e
printf 'FALSE-TABLE\n' > proofs/QBP/Foundations/fanoTableF4.snapshot
EOF
git add -A
git commit -qm tamper-snapshot-and-producer

# --- NAIVE guard (runs the PR's own producer): the attack PASSES (demonstrates the hole) ---
bash "$PRODUCER"
if git diff --quiet -- "$SNAP"; then naive=PASS; else naive=FAIL; fi

# --- HARDENED guard (#605 AC1): pin the producer to the trusted base, THEN regen + diff ---
git checkout "$base" -- "$PRODUCER"
bash "$PRODUCER"
if git diff --quiet -- "$SNAP"; then hardened=PASS; else hardened=FAIL; fi

echo "naive-guard=$naive  hardened-guard=$hardened"
[ "$naive" = PASS ] || { echo "CONTROL BROKEN: the naive guard should pass the self-defeat attack"; exit 1; }
[ "$hardened" = FAIL ] || { echo "REGRESSION: hardened guard did NOT catch the falsified snapshot"; exit 1; }
echo "OK (#605 AC2): the trusted-producer pin makes a falsified snapshot fail the guard even when the producer is also tampered"
