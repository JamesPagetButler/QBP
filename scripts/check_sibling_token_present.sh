#!/usr/bin/env bash
# QBP#761: fail loud (non-zero exit) if SIBLING_READ_TOKEN is unset or empty.
#
# Used by .github/workflows/tenancy-xref-lint.yml in two places:
#   1. The real `tenancy-xref-lint` job, where SIBLING_READ_TOKEN is the
#      actual GitHub Actions secret — this should PASS whenever the secret
#      is configured and visible to the run.
#   2. The `tenancy-xref-lint-missing-secret-negative-control` job, which
#      deliberately sets SIBLING_READ_TOKEN="" and asserts this script FAILS
#      — proving the fail-loud guard actually fails loud, not just that a
#      comment claims it does (Red Team note on PR #808, issuecomment-6866713929;
#      qbp-oppenheimer ruling on #761, 2026-11-13).
#
# Rationale: once `tenancy-xref-lint` becomes a required status check (#738
# AC3), a missing or unreadable SIBLING_READ_TOKEN must never let the job
# silently fall back to the linter's local-dev "not verifiable here -> exit 0"
# path -- that would quietly turn sibling-ref verification off on every PR.
# There is no Dependabot config on this repo and no fork PRs today, so no
# actor-scoped exemption is needed now. If Dependabot or fork PRs are ever
# enabled, add a visible, actor-scoped exemption at the CALL SITE in the
# workflow (e.g. `if: github.actor != 'dependabot[bot]'`) that logs
# "skipped: no secret for <actor>" -- never silence this script itself.
set -euo pipefail

if [ -z "${SIBLING_READ_TOKEN:-}" ]; then
  echo "::error::SIBLING_READ_TOKEN is not set (or is empty) -- cannot verify" \
    "sibling cross-references on CI. Failing loudly rather than silently" \
    "falling back to 'not verifiable here' (QBP#761)."
  exit 1
fi

echo "SIBLING_READ_TOKEN is present."
