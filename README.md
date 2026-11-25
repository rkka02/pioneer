# Fourier Entropy–Influence (FEI) Conjecture

- **Field:** Analysis — Analysis of Boolean Functions & Discrete Harmonic Analysis
- **Catalog References:** ProofAtlas Top 500 `#412`, [`teorth/optimizationproblems` `#71a`](https://teorth.github.io/optimizationproblems/constants/71a.html)
- **Status:** Open (Full conjecture unresolved — **Case C**); **new certified finite world-record lower bound on the universal constant $C$**, two new exact FEI equivalences (dyadic midpoint crossings & fixed-error matrix rank), major positive structural theorems, and **87 kernel-verified Lean 4 theorems** completed across 1 `xhigh` recon + 5 `max` research rounds.
- **Frozen Challenge Statement:** [`FEI/Challenge.lean`](FEI/Challenge.lean)
  - **SHA-256:** `6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b`
  - Full unweakened statement (Friedgut & Kalai, 1996): $\exists C > 0$ such that for all $n \in \mathbb{N}$ and all Boolean functions $f : \{0, 1\}^n \to \{\pm 1\}$, $H(\hat{f}^2) \le C \cdot \mathrm{Inf}(f)$ (in bits, $\log_2$).

---

## Headline Results

Full proofs, exact rational/integer certificates, frontier comparisons, and verification ledgers are documented in [`RESEARCH_ANALYSIS.md`](RESEARCH_ANALYSIS.md).

1. **New Rigorously Certified Finite World-Record Lower Bound (`#71a` — Round 5, §4):**
   An explicit balanced monotone Boolean function (constructed via asymmetric shared-variable spinal composition and finite depth-140 disjoint composition) satisfies
   $$6.521851167347822949109657013506222645 < \frac{H(f)}{I(f)} < 6.521851167347822949109657013506222646.$$
   - Strictly improves the published `#71a` constant (`6.521845710923046575`, Numaro 2026) by $+5.456 \times 10^{-6}$ (and beats our own Round 1 certificate by $+5.52 \times 10^{-16}$).
   - Verified with **Python standard library only** using exact integer Walsh transforms and outward-rounded $2^{-192}$ rational interval arithmetic in [`scripts/max5_record.py`](scripts/max5_record.py). Ready for upstream submission to `teorth/optimizationproblems` `#71a`.
2. **End-to-End Lean 4 Kernel Proof: Dyadic Grid Energy & Midpoint-Crossing FEI Equivalence ([`FEI/GridEquivalence.lean`](FEI/GridEquivalence.lean)):**
   Define the dyadic grid energy $G(f) = \sum_{m \ge 0}\sum_S \operatorname{dist}(\hat{f}(S), 2^{-m}\mathbb{Z})^2$ and the fixed-order coarse midpoint-crossing cost $R_{\mathrm{fixed}}(f)$ along the coordinate-restriction tree. Proved directly in Lean 4 for **every** Boolean function in `FEI/Challenge.lean`:
   $$0 \le \frac{H(f)}{2} - G(f) \le 2 I(f), \qquad R_{\mathrm{fixed}}(f) \le \frac{H(f)}{2} \le R_{\mathrm{fixed}}(f) + \frac{38}{3} I(f),$$
   yielding the kernel-verified equivalence `fei_iff_crossing_bound`:
   $$\mathrm{FEI} \iff \exists C > 0\ \forall n, f:\ R_{\mathrm{fixed}}(f) \le C \cdot I(f).$$
3. **Fixed-Error Real Matrix Rank Equivalence & Non-XOR Half-Bit Separation (Rounds 4–5):**
   For normalized Boolean sign matrices $M_{xy} = f(x, y)/\sqrt{|X||Y|}$ with singular-value entropy $S(M)$ and minimum $3/4$-Frobenius-mass real rank $r_{1/4}(M)$:
   $$\mathrm{FEI} \iff \exists K\ \forall f, X, Y:\ \log_2 r_{1/4}(M) \le K(I_X + I_Y) \iff \exists K:\ S(M) \le K(I_X + I_Y).$$
   - **Non-XOR CHSH Selector Lift (§5.1):** Substituting a two-party signed-dictator selector yields $S(M_{F_h}) = H(h) + I(h)$ at physical influence $2I(h)$, attaining
     $$\frac{S(M)}{I_X + I_Y} > 3.76092558367391147455$$
     — beating every scalar XOR matrix $h(x \oplus y)$ by an exact $+1/2$ bit per unit influence, and locating the optimal constant $(C_*+1)/2 \le K_S \le C_*/2 + 1/\ln 2$.
   - **Small-Rank Threshold (§5.3):** Sharp constant $2$ holds for all rank-2 sign matrices (and all signs whose minority event indicator has rank $\le 2$, via sharp $S_E - J_E \le \log_2(5/4)$); an explicit **rank-5** guarded sign matrix attains $S(M)/I \in (2.0024983293, 2.0024983294)$, pinning the first violating rank to $\{3, 4, 5\}$.
4. **Broad Positive Classes & Sharp Structural Obstructions (Rounds 1–5):**
   - Uniform $P_2 / I$ (hence $X / I$ and $H / I$) bounds for: fixed-degree shells, symmetric functions ($X < 78I$), Gaussian ensembles ($\mathbb{E}H \le 24\mathbb{E}I$), arbitrary $\mathbb{F}_2$-linearly recoded block-symmetric functions, linearly recoded disjoint gate towers, bounded-width reversible shared-data routing, mixed address+data recoded quadratic lookups ($P_2 < 60I$), simultaneous block-permutation-invariant signs, exponential-tail affine partitions, and overlapping bounded-rank local dictionaries.
   - Exact obstructions: adaptive 1-coordinate induction barrier ($> 7.11149$), dyadic two-shell parity & non-plateaued row obstructions, stopped-walk single-frequency local-time divergence ($\log_2(V/Q)$ with sharp constant $1$ even at $Q=1$), high-order future-marginal invariance barrier, and trace-norm / decision-tree clustering barriers on Tribes XOR matrices.

---

## Lean 4 Verification (87 Kernel-Verified Theorems)

Built with **Lean 4.36.0** + **Mathlib `v4.36.0`**. Zero `sorry`, zero `admit`, zero added axioms; every single named theorem (public and private) uses only `propext`, `Classical.choice`, and `Quot.sound`.

| Module | Theorems (Pub / Priv) | Scope |
|---|---:|---|
| [`Challenge.lean`](FEI/Challenge.lean) | Frozen statement | Unweakened Friedgut–Kalai FEI Conjecture on `Fin n → Bool` |
| [`ChallengeSanity.lean`](FEI/ChallengeSanity.lean) | 8 / 7 | Parseval, combinatorial = spectral influence, `AND₂` ($C \ge 2$), constant witness |
| [`ResearchLemmas.lean`](FEI/ResearchLemmas.lean) | 34 / 13 | Dyadic grid sandwich $0 \le H/2 - G \le 2I$, `fei_iff_grid_bound`, pooled second moment, rank-2 scalar bound, CHSH selector identities |
| [`GridEquivalence.lean`](FEI/GridEquivalence.lean) | 9 / 16 | Walsh restriction butterfly, exact midpoint-crossing formula, `fourierEntropy_crossing_bounds`, `fei_iff_crossing_bound` |
| **Total** | **51 / 36 (87)** | **100% standard axioms, 0 `sorry`** |

---

## Reproduction

```bash
# 1. Verify frozen statement integrity
shasum -a 256 FEI/Challenge.lean
# Expected: 6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b

# 2. Replay the standalone world-record #71a certificate (Python stdlib only!)
python3 scripts/max5_record.py

# 3. Build all 87 Lean 4 theorems and run the full axiom audit
lake build
python3 scripts/max5_audit.py

# 4. Replay Round 5 matrix, small-rank, and crossing verifiers (requires NumPy)
python3 scripts/max5_matrix.py
python3 scripts/max5_small_rank.py
python3 scripts/max5_crossings.py
```
