# QBP Agent Framework

This directory contains documentation for the AI agent personas used in the QBP development workflow.

## Overview

The QBP project uses a multi-agent review and development system to ensure code quality, mathematical rigor, and physical correctness.

---

## Agent Roles

### Red Team (Claude) — Review & Critique

| Persona | Focus | Key Questions |
|---------|-------|---------------|
| **Sabine** | Experimentalist | Is it testable? Is it falsifiable? |
| **Grothendieck** | Mathematician | Is it rigorous? Is it complete? |
| **Knuth** | Engineer | Is it correct? Is it efficient? |

Red Team reviews are triggered via `claude_review_prompt.md` and produce structured reviews with explicit APPROVE/REJECT verdicts.

### Gemini Team — Theory & Intuition

| Persona | Focus | Key Questions |
|---------|-------|---------------|
| **Furey** | Algebraist | Does it align with division algebra principles? |
| **Feynman** | Physicist | Is it physically intuitive? Can you explain it simply? |

Gemini reviews are triggered via `gemini_review_prompt.md` and generate PRDs for feature implementations.

### Writing & Communication

| Persona | Focus | Key Questions |
|---------|-------|---------------|
| **Der Depperte** | Communicator | Is it clear? Is it accessible? Does it inspire wonder? |

Der Depperte handles Phase 5 publication writing — clarity, accessibility, and sense of wonder.

### Execution (Steve) — *Deprecated*

| Persona | Focus | Key Questions |
|---------|-------|---------------|
| **Steve** | Contractor | Is the PRD clear? Does it match existing patterns? |

> **Note:** Steve is deprecated. No persona definition exists and there is no evidence of active use in the current workflow. Retained here for historical reference only.

---

## Workflow

```
┌─────────────────────────────────────────────────────────────┐
│                                                              │
│   Developer creates PR                                       │
│           ↓                                                  │
│   ┌─────────────────────────────────┐                       │
│   │  RED TEAM REVIEW (Claude)       │                       │
│   │  Sabine + Grothendieck + Knuth  │                       │
│   └─────────────────────────────────┘                       │
│           ↓                                                  │
│   ┌─────────────────────────────────┐                       │
│   │  GEMINI REVIEW                  │                       │
│   │  Furey + Feynman                │                       │
│   └─────────────────────────────────┘                       │
│           ↓                                                  │
│   Issues synthesized & presented to James                    │
│           ↓                                                  │
│   Human merge authorization                                  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Agent Documentation

- [Steve (Contractor)](./steve.md) — Software implementation agent (deprecated)
- **[Central Persona Registry](../personas/README.md)** — Single source of truth for all 14 QBP personas
- [Expert Panel](../personas/expert_panel.md) — 7 personas for Theory Refinement review

---

## Review Prompts

- `claude_review_prompt.md` — Red Team review trigger
- `gemini_review_prompt.md` — Gemini review trigger

---

## Verdict Standards

All agents use a three-tier verdict system:

| Verdict | Meaning |
|---------|---------|
| **APPROVE** | Ready to merge as-is |
| **APPROVE WITH CONDITIONS** | Merge after specific issues addressed |
| **REJECT** | Fundamental problems that block merge |

Each persona has explicit rejection criteria that must be enforced — see the individual review prompts for details.
