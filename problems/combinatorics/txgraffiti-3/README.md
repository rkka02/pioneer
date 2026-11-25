# TxGraffiti Conjecture 3 — Disproved (42-Vertex Cubic Counterexample, Lean 4 Kernel-Verified)

- **Field:** Combinatorics — Graph Theory (Independent Domination & Matching Saturation)
- **Catalog References:** [`arXiv:2507.17780`](https://arxiv.org/abs/2507.17780) (Conjecture 3, Davila–Brimkov–Pepper), `google-deepmind/formal-conjectures` (`FormalConjectures/Arxiv/2507.17780/3.lean`)
- **Status:** **Disproved (Case B — Complete Lean 4 Kernel Disproof!)**
  - Prior public counterexamples existed on 50 vertices ([`cubic-domination-counterexamples`](https://github.com/andrewbutz22-cosmic/cubic-domination-counterexamples)) and 48 vertices ([`txgraffiti-order48-successor`](https://github.com/ipitchford/txgraffiti-order48-successor), [Zenodo `22083656`](https://doi.org/10.5281/zenodo.22083656)), though the statement remained marked `research open` in `formal-conjectures`.
  - This project **reduces the counterexample size to 42 vertices** (finding 4 non-isomorphic connected cubic counterexamples on 42 vertices), provides **the complete zero-`sorry` Lean 4 kernel disproof** directly against the frozen `formal-conjectures` statement, constructs connected counterexamples in every degree divisible by 3, and certifies **50,724,108** regular graphs through order 14 (plus **12,967,515** connected cubic/4-regular/5-regular graphs).
- **Frozen Challenge Statement:** [`TxGraffiti3/Challenge.lean`](TxGraffiti3/Challenge.lean)
  - **SHA-256:** `d54daf16a077ec5cf824d8fc0f336888a413396799bc203c1b14d4cd85430d41`
  - Statement: for every finite $r$-regular simple graph $G$ ($r \ge 1$), $i(G) \le \mu^*(G)$.

---

## Main Result (`TxGraffiti3.not_TxGraffitiConjecture3`)

There exists a connected cubic (3-regular) simple graph $G$ on **42 vertices and 63 edges** ([`scripts/counterexample.g6`](scripts/counterexample.g6), SHA-256 `6ab95c87...`) satisfying:
$$i(G) = 14 > 13 = \mu^*(G).$$

- **Matching saturation $\mu^*(G) = 13$:** An explicit 13-edge matching $M = \{\{2j, 2j+1\} : 0 \le j < 13\}$ covers all 63 edges (vertices $26\ldots 41$ form an independent set), while in any cubic graph each matching edge covers at most $5$ edges, giving $\mu^*(G) \ge \lceil 63/5 \rceil = 13$.
- **Independent domination $i(G) = 14$:** Attained by $D = \{1,2,4,6,8,10,12,14,16,18,20,22,24,29\}$, while a **277-row recurrence certificate** verified by Lean 4's kernel (`decide +kernel`, zero `native_decide`) rules out every independent dominating set of size $\le 13$.
- **Degree generalization:** Blowing up each vertex into an independent set of size $t \ge 1$ yields connected $3t$-regular counterexamples with $i(G_t) = 14t > 13t \ge \mu^*(G_t)$.
- **Minimum counterexample order bounds:** Exhaustive censuses with zero violations across **50,724,108** positive-regular graphs (orders $2\ldots 14$) and **12,967,515** connected graphs (cubic $n \le 20$, 4-regular $n \le 16$, 5-regular $n \le 14$) pin the global minimum counterexample order to **$15 \le n_{\min} \le 42$** (and cubic minimum to **$22 \le n_{\min}^{(3)} \le 42$**).

Full mathematical proof and verification ledger: [`PROOF.md`](PROOF.md).

---

## Lean 4 Kernel Verification

Built with **Lean 4.36.0** + **Mathlib `v4.36.0`**. Zero `sorry`, zero `admit`, zero `native_decide`.

| File | Role |
|---|---|
| [`TxGraffiti3/Challenge.lean`](TxGraffiti3/Challenge.lean) | Frozen, read-only conjecture statement (1:1 with `formal-conjectures`) |
| [`TxGraffiti3/Bounds.lean`](TxGraffiti3/Bounds.lean) | Soundness proof for component-splitting / neighborhood-pivoting lower-bound certificates |
| [`TxGraffiti3/Matching.lean`](TxGraffiti3/Matching.lean) | General $r$-regular bound $|E(G)| \le (2r - 1)|M|$ and maximal-matching characterization |
| [`TxGraffiti3/Certificate.lean`](TxGraffiti3/Certificate.lean) | Explicit 42-vertex cubic graph, connectivity proof, and 277-row kernel-checked `i(G) ≥ 14` certificate |
| [`TxGraffiti3/Solution.lean`](TxGraffiti3/Solution.lean) | `not_TxGraffitiConjecture3 : ¬ TxGraffitiConjecture3`, `independent_domination_eq`, `saturation_eq` |

Axiom audit ([`scripts/audit.lean`](scripts/audit.lean)):
- `TxGraffiti3.not_TxGraffitiConjecture3`: `[propext, Classical.choice, Quot.sound]`
- `TxGraffiti3.Counterexample.independent_domination_eq`: `[propext, Classical.choice, Quot.sound]`
- `TxGraffiti3.Counterexample.saturation_eq`: `[propext, Classical.choice, Quot.sound]`
- `TxGraffiti3.Counterexample.cubic`: `[propext, Classical.choice, Quot.sound]`
- `TxGraffiti3.Counterexample.connected`: `[propext, Quot.sound]`

---

## Reproduction

```bash
# 1. Verify frozen statement integrity
shasum -a 256 TxGraffiti3/Challenge.lean
# Expected: d54daf16a077ec5cf824d8fc0f336888a413396799bc203c1b14d4cd85430d41

# 2. Build the Lean 4 disproof, check axioms, and replay with leanchecker
lake build
lake env lean scripts/audit.lean
lake env leanchecker -v TxGraffiti3

# 3. Independently verify the 42-vertex counterexample via Python DP & SciPy/HiGHS MILP
python3 scripts/check_exact.py scripts/counterexample.g6
python3 scripts/check_milp.py scripts/counterexample.g6
python3 scripts/reconstruct.py
```
