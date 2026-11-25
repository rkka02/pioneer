# Fourier Entropy–Influence (FEI) Conjecture (ProofAtlas #412)

## Problem Statement (Friedgut & Kalai, 1996)
There exists a universal constant $C > 0$ such that for every $n \in \mathbb{N}$ and every Boolean function $f : \{-1, 1\}^n \to \{-1, 1\}$,
$$H(\hat{f}^2) \le C \cdot \mathrm{Inf}(f)$$
where $H(\hat{f}^2) = -\sum_{S \subseteq [n]} \hat{f}(S)^2 \log_2(\hat{f}(S)^2)$ is the Shannon entropy of the squared Fourier spectrum and $\mathrm{Inf}(f) = \sum_{i=1}^n \mathrm{Inf}_i(f) = \sum_{S \subseteq [n]} |S|\hat{f}(S)^2$ is the total influence.

## Workflow
1. `FEI/Challenge.lean`: Frozen, audited formal statement of the full, unweakened FEI Conjecture (`Fin n → Bool`, Parseval & spectral=combinatorial influence sanity checks, explicit `AND₂` witness). READ-ONLY once audited.
2. `RESEARCH_ANALYSIS.md` & `FEI/Blueprint.lean`: Mathematical proof/disproof architecture and Lean 4 lemma skeleton discovered by GPT-6.2 Astra (`xhigh`/`max`).
3. `FEI/*.lean`: Full Lean 4 kernel-verified proof filled by Claude Code (`opus 5.5`, `high`), escalating mathematical gaps back to Astra.
