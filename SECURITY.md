# Security Policy

This document outlines security practices for the Quaternion-Based Physics (QBP) project.

## Reporting Vulnerabilities

If you discover a security vulnerability, please report it privately by emailing the maintainer. Do not create a public issue.

## Secrets Management

### What Counts as a Secret

- API keys and tokens (GitHub, Gemini, OpenAI, etc.)
- Database credentials
- Private keys and certificates
- OAuth client secrets
- Any authentication credentials

### Best Practices

1. **Never commit secrets to git.** Even if you delete them later, they remain in git history.

2. **Use environment variables.** Store secrets in environment variables, not in code:
   ```bash
   export GEMINI_API_KEY="your-key-here"
   ```

3. **Use `.env` files locally.** For local development, use a `.env` file (already in `.gitignore`):
   ```bash
   # .env (never commit this file)
   GEMINI_API_KEY=your-key-here
   ```

4. **Use a secrets manager in production.** For deployed applications, use a proper secrets manager (AWS Secrets Manager, HashiCorp Vault, etc.).

5. **Rotate compromised secrets immediately.** If a secret is accidentally committed:
   - Rotate/regenerate the secret immediately
   - Remove it from git history using `git filter-branch` or BFG Repo Cleaner
   - Document the incident (see below)

### Pre-commit Hook

This repository uses [gitleaks](https://github.com/gitleaks/gitleaks) as a pre-commit hook to prevent accidental secret commits. The hook runs automatically before each commit.

To install the pre-commit hooks:
```bash
pip install pre-commit
pre-commit install
```

To run manually:
```bash
pre-commit run gitleaks --all-files
```

### Files That Should Never Be Committed

The following patterns are in `.gitignore` and should never be committed:

- `.env`, `.env.*` - Environment files with secrets
- `*.key`, `*.pem`, `*.p12`, `*.pfx` - Private keys and certificates
- `credentials.*`, `secrets.*` - Credential files
- `.netrc`, `.npmrc`, `.pypirc` - Package manager auth files

## Security Audit Log

### 2026-02-06: Initial Security Audit

**Audit performed by:** Claude (AI assistant) under human supervision
**Tools used:** gitleaks v8.18.4
**Scope:** Full git history (141 commits)

**Findings:**
- No secrets detected in git history
- No API keys, tokens, or passwords found in tracked files
- Third-party packages in `venv/` contain example/test credentials (expected, not a risk)

**Actions taken:**
1. Added secret file patterns to `.gitignore`
2. Added gitleaks pre-commit hook to `.pre-commit-config.yaml`
3. Created this `SECURITY.md` document

**Status:** PASS - No remediation required

---

## Dependency Security

Regularly audit dependencies for known vulnerabilities:

```bash
# Python
pip-audit

# General
npm audit  # if using Node.js tools
```

## Code Security

- Avoid command injection: never pass user input directly to shell commands
- Avoid SQL injection: use parameterized queries
- Validate all external input
- Keep dependencies updated

## Contact

For security concerns, contact the project maintainer.
