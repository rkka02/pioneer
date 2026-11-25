# Fonollosa's Minimum Modulus Conjecture

- **Field:** Number Theory — Additive & Modular Combinatorics
- **Catalog References:** [`arXiv:2607.08366`](https://arxiv.org/abs/2607.08366) (Conjecture 1, José A. R. Fonollosa, July 2026), `google-deepmind/formal-conjectures` (`FormalConjectures/Arxiv/2607.08366/MinModulus.lean`)
- **Status:** Open (Full conjecture unresolved — **Case C**); **new world-record unconditional cyclic lower bound $N \ge \frac{11}{16} \cdot 2^n$ kernel-proved in Lean 4**, exact binary-core rigidity theorem, complete exclusion of $n = 10$ boundary moduli $1013, 1014, 1015$ and continuous floor $N \ge 724$, and **41 kernel-verified Lean 4 declarations** across 3 `max` rounds.
- **Frozen Challenge Statement:** [`FonollosaMinModulus/Challenge.lean`](FonollosaMinModulus/Challenge.lean)
  - **SHA-256:** `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`
  - Statement: for every $n \ge 2$ and $0 < N < 2^n - 2^{\lfloor \log_2 n \rfloor}$, no subset $A \subseteq \mathbb{Z}/N\mathbb{Z}$ of size $n$ is valid mod $N$ (i.e., admits the all-ones multiset as the unique size-$n$ multiset from $A$ summing to $\sum_{a \in A} a \pmod N$).

---

## Headline Results

Full proofs, exact C++/Python certificates, and verification ledgers are documented in [`RESEARCH_ANALYSIS.md`](RESEARCH_ANALYSIS.md).

1. **New World-Record Unconditional Cyclic Lower Bound — Kernel-Proved in Lean 4 ([`ResearchLemmas.lean`](FonollosaMinModulus/ResearchLemmas.lean), `RankPacking.cyclic_eleven_sixteenths`):**
   For **every** $n \ge 3$ and **every** valid $n$-set $A \subseteq \mathbb{Z}/N\mathbb{Z}$,
   $$N \ge \frac{11}{16} \cdot 2^n \qquad (= 0.6875 \cdot 2^n).$$
   - Strictly improves Sitjar's Nov 2026 published general lower bound $N \ge (1/2 + o(1)) 2^n$ ([Zenodo `24228247`](https://doi.org/10.5281/zenodo.24228247)) for **every $n \ge 6$**, jumping the exponential constant straight past $2/3$ via an 8-label packing + directed-crossing unequal-size Bollobás set-pair inequality ([`SetPairCounting.lean`](FonollosaMinModulus/SetPairCounting.lean)).
   - Proves that **$11/16$ is the exact ceiling** of the entire multi-layer signature-square relaxation (`RankSlots.four_signature_relaxation_ceiling`).
2. **Three-Quarters Theorem for Affine $\{0, 1, 3\}$ Copies (`three_quarters_of_triple` — Lean 4 Kernel-Proved):**
   Any valid $n$-set ($n \ge 3$) containing a nondegenerate affine copy of $\{0, 1, 3\}$ (even with a nonunit step!) satisfies $N \ge \frac{3}{4} \cdot 2^n$ (sharp at $n = 3, N = 6$).
3. **Binary-Core Rigidity Theorem for All $n \ge 6$ (`minModulus_le_of_affine_binary_core` — Lean 4 Kernel-Proved):**
   Any valid $n$-set ($n \ge 6$) containing a unit-affine binary core $\{t + u 2^i : 0 \le i \le n - 2\}$ satisfies the **exact** conjectured bound $N \ge 2^n - 2^{\lfloor \log_2 n \rfloor}$, and for $2^{n-1} \le N < 2^n$ the last residue is uniquely forced to $t + u 2^{n-1}$. Also exhaustively ruled out all $n - 2$ binary-core extensions for $8 \le n \le 25$ (including nonunit steps $g = 2, 3, 4$).
4. **Sharp $n = 10$ Reduction ($724 \le N \le 1012$):**
   - Lean's $11/16$ bound gives $N \ge 704$ directly; exact finite exchange-profile classification + dual C++17 searches raise the continuous unrestricted floor to **$N \ge 724$** (up from Sitjar's $569$).
   - Eliminated all antipodal and all nonunit-difference 10-sets across all 447 subthreshold moduli ($569 \le N \le 1015$).
   - **Exhaustively excluded the top three boundary moduli $N = 1015$, $1014$, and $1013$** via independent four-clique and direct-completion C++17 verifiers (at $1015$ alone: 23,884 fourth-coordinate branches, 562,690,729 six-point prefixes, 680,066,873 target graphs, zero valid 10-sets; both solvers recover the canonical valid 10-set at $1016$).
   - Proved Conway–Guy, Lunnon, Bohman, and Fibonacci families have $N^* = \infty$ (3-AP midpoint replacement) and refuted 2,969 distinct non-binary construction candidates across $10 \le n \le 20$.

---

## Lean 4 Verification (41 Kernel-Verified Declarations)

Built with **Lean 4.36.0** + **Mathlib `v4.36.0`**. Zero `sorry`, zero `admit`, zero `native_decide`; all **41 public declarations** pass `leanchecker --fresh` using only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Module | Scope |
|---|---|
| [`FonollosaMinModulus/Challenge.lean`](FonollosaMinModulus/Challenge.lean) | Frozen, read-only conjecture statement (1:1 with `formal-conjectures`) |
| [`FonollosaMinModulus/SetPairCounting.lean`](FonollosaMinModulus/SetPairCounting.lean) | Finite permutation proof of weighted unequal-size Bollobás set-pair inequality & binomial bounds |
| [`FonollosaMinModulus/ResearchLemmas.lean`](FonollosaMinModulus/ResearchLemmas.lean) | `cyclic_eleven_sixteenths`, `three_quarters_of_triple`, `cyclic_nine_sixteenths`, `minModulus_le_of_affine_binary_core`, `four_signature_relaxation_ceiling`, two-pivot interval & exact-converse theorems |

---

## Reproduction

```bash
# 1. Verify frozen statement integrity
shasum -a 256 FonollosaMinModulus/Challenge.lean
# Expected: 3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91

# 2. Build all 41 Lean 4 declarations, audit axioms, and replay with leanchecker --fresh
lake build
lake env lean scripts/check_axioms.lean
lake env leanchecker --fresh --verbose FonollosaMinModulus.Challenge
lake env leanchecker --fresh --verbose FonollosaMinModulus.SetPairCounting
lake env leanchecker --fresh --verbose FonollosaMinModulus.ResearchLemmas

# 3. Replay Round 3 exact LP/slot & exchange-profile verifiers
python3 -B scripts/round3_slots.py
python3 -B scripts/round3_profiles.py
```
