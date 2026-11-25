# Tutte's 3-Flow Conjecture (ProofAtlas #355)

## Problem Statement (Tutte, 1972)
Every finite 4-edge-connected multigraph admits a nowhere-zero 3-flow.

Equivalently (via Tutte's flow theorem / modulo-3 orientations):
- Every finite 4-edge-connected multigraph admits a nowhere-zero integer 3-flow $f : E \to \{-2, -1, 1, 2\}$ satisfying flow conservation at every vertex.
- Equivalently, it admits a nowhere-zero $\mathbb{Z}/3\mathbb{Z}$-flow, or equivalently a modulo-3 orientation ($\deg^+(v) \equiv \deg^-(v) \pmod 3$ for every vertex $v$).

## Workflow
1. `Tutte3Flow/Challenge.lean`: Frozen, audited formal statement of the full, unweakened Tutte 3-Flow Conjecture (finite multigraphs, integer nowhere-zero 3-flow + equivalence to mod-3 orientation). Once audited, this file is READ-ONLY.
2. `RESEARCH_PLAN.md` & `Tutte3Flow/Blueprint.lean`: Mathematical proof/disproof architecture and Lean 4 lemma skeleton discovered by GPT-6.2 Astra (`xhigh`/`max`).
3. `Tutte3Flow/*.lean`: Full Lean 4 kernel-verified proof filled by Claude Code (`opus 5.5`, `high`), escalating genuine mathematical gaps back to Astra.
