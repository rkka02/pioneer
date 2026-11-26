# Pioneer — Open Mathematics, Theoretical Physics & Lean 4 Verification

Pioneer studies open problems in mathematics and theoretical physics. Its mathematics projects use **frozen Lean 4 challenge statements**, **multi-round frontier AI mathematical discovery**, **exact symbolic/computational certificates**, and **kernel-verified Lean 4 proofs**.

Mathematical problems are organized by **field**, while external references (ProofAtlas Top 500, `google-deepmind/formal-conjectures`, `teorth/optimizationproblems`, arXiv, Erdős Problems, independent conjectures) are tracked in [`catalog.json`](catalog.json). See [`METHODOLOGY.md`](METHODOLOGY.md) for the frozen-statement integrity rules and verification standards. The [theoretical physics section](#theoretical-physics) collects research manuscripts with analytical derivations and reproducible calculations.

---

## Active Problem Catalog

| Field | Problem | External References | Status | Lean 4 Theorems (`sorry` = 0) | Key Results |
|---|---|---|---|---:|---|
| **Combinatorics** (`graph-theory`) | [**TxGraffiti Conjecture 3**](problems/combinatorics/txgraffiti-3/) | [`arXiv:2507.17780`](https://arxiv.org/abs/2507.17780) (`#3`), `formal-conjectures` | **Disproved (Lean 4 Kernel Proof)** | **28** (`18` pub / `10` priv) | Complete kernel disproof `not_TxGraffitiConjecture3`; smallest known **42-vertex** cubic counterexample ($i = 14 > 13 = \mu^*$, beating prior 48/50-vertex repos); $3t$-regular blowups; **50.72M** regular graph census ($15 \le n_{\min} \le 42$) |
| **Combinatorics** (`graph-theory`) | [**Tutte's 3-Flow Conjecture**](problems/combinatorics/tutte-3-flow/) | ProofAtlas `#355` | Partial Theorems & Lean Package | **72** (`56` pub / `16` priv) | $\le 16$ odd-vertex & unrestricted $b \le 12$ pinned theorems (105.6B classes certified); kernel-verified arbitrary-$r$ matching-tree $2^{r-1}$ hole & one-edge repair theorem; 88-vertex coupled electrical obstruction |
| **Analysis** (`boolean-fourier`) | [**Fourier Entropy–Influence (FEI) Conjecture**](problems/analysis/fourier-entropy-influence/) | ProofAtlas `#412`, [`#71a`](https://teorth.github.io/optimizationproblems/constants/71a.html) | **New World Record** & Lean Package | **87** (`51` pub / `36` priv) | Certified finite lower bound **$H/I > 6.521851167347822949109657013506222645$** (beats `#71a`); kernel-verified midpoint-crossing FEI equivalence; fixed-error matrix-rank equivalence + non-XOR CHSH lift ($> 3.76092558$) |
| **Number Theory** (`additive-combinatorics`) | [**Fonollosa's Minimum Modulus Conjecture**](problems/number-theory/fonollosa-min-modulus/) | [`arXiv:2607.08366`](https://arxiv.org/abs/2607.08366) (`#1`), `formal-conjectures` | **New World Record** & Lean Package | **76** (`41` pub / `35` priv) | Kernel-proved unconditional bound **$N \ge \frac{11}{16} \cdot 2^n$** ($\forall n \ge 3$, beats Sitjar 2026 via unequal-size Bollobás set-pair inequality) + relaxation ceiling; $3/4$ bound on $\{0,1,3\}$; exact binary-core rigidity; $n = 10$ narrowed to **$724 \le N \le 1012$** ($1013\text{--}1015$ exhausted) |
| **TCS** (`combinatorial-games`) | [**Catch-Up Game Even-Sum Draw Conjecture**](problems/tcs/catch-up-game/) | [MPRA `108784`](https://mpra.ub.uni-muenchen.de/108784/), `formal-conjectures` | **New World Record** & Lean Package | **137** (`77` pub / `60` priv) | Exact prefix draws extended to **$N = 48$** (beats $N \le 34$; all openings draw $12 \le N \le 44$); **68.20M** density boards verified ($\max \le 32$); 6-token min-loss theorem & $4K$ cap obstruction; infinite-family Lean draws (high intervals, 10-token adjacent holes, bank embeddings, upper ray) |

**Mathematics totals** `5` active campaigns across `4` mathematical fields · **`400` Lean 4 kernel-verified theorems** (`243` public + `157` private, **0 `sorry`**, **0 `admit`**, **0 `native_decide`**, standard axioms `propext`, `Classical.choice`, `Quot.sound` only) · **`1` complete kernel disproof** (`TxGraffiti-3`) · **`3` world-record improvements** (`FEI #71a`, `Fonollosa 11/16`, `Catch-Up N = 48`).

---

## Theoretical Physics

**Information encoded in relative boosts at a gravitational corner** studies a pair of boundaries whose individual measurement statistics are identical for every message. Under the clock-bounded Schwarzschild area law, the paper derives the sharp threshold in relative boost for joint discrimination and the optimal probability of preparing one bit near that threshold. The one-loop exponent $257/90$ controls that probability. An explicit four-message construction succeeds with limiting probability 39.45%.

[Read the manuscript (PDF)](physics/corner-boost-information/main.pdf) · [Assumptions, source and reproduction](physics/corner-boost-information/)

---

## Directory Layout

```text
pioneer/
├── README.md                                        # Master catalog & scoreboard
├── METHODOLOGY.md                                   # Frozen-Challenge protocol & verification rules
├── catalog.json                                     # Machine-readable registry (fields, external IDs, stats)
├── physics/
│   └── corner-boost-information/                    # Gravitational corner boosts, paper and numerical verifier
└── problems/
    ├── combinatorics/
    │   ├── txgraffiti-3/                            # Case B disproof (42-vertex cubic + Lean kernel proof)
    │   └── tutte-3-flow/                            # Standalone Lean 4.36 project + exact C++/Python censuses
    ├── analysis/
    │   └── fourier-entropy-influence/               # Standalone Lean 4.36 project + stdlib #71a certificate
    ├── number-theory/
    │   └── fonollosa-min-modulus/                   # Standalone Lean 4.36 project + Bollobás 11/16 + n=10 C++ search
    └── tcs/
        └── catch-up-game/                           # Standalone Lean 4.36 project + N=48 & 68.2M-board C++ solvers
```

Future campaigns across `algebra/`, `geometry/`, `probability/`, and additional subfields slot directly under `problems/<field>/<slug>/` as self-contained Lean 4 projects and register in [`catalog.json`](catalog.json).

---

## Quick Verification

Every problem directory is independently verifiable:

```bash
# 1. Verify TxGraffiti Conjecture 3 Lean 4 disproof (28 theorems, 42-vertex cubic counterexample)
cd problems/combinatorics/txgraffiti-3
shasum -a 256 TxGraffiti3/Challenge.lean
lake build && lake env lean scripts/audit.lean
python3 scripts/check_exact.py scripts/counterexample.g6

# 2. Verify Tutte's 3-Flow Conjecture Lean 4 package (72 theorems, standard axioms only)
cd ../tutte-3-flow
shasum -a 256 Tutte3Flow/Challenge.lean
lake build && python3 -B scripts/round2_audit.py

# 3. Verify FEI world-record #71a certificate (stdlib only) & Lean 4 package (87 theorems)
cd ../../analysis/fourier-entropy-influence
shasum -a 256 FEI/Challenge.lean
python3 scripts/max5_record.py
lake build && python3 scripts/max5_audit.py

# 4. Verify Fonollosa Minimum Modulus Lean 4 package (76 theorems, N >= (11/16)*2^n)
cd ../../number-theory/fonollosa-min-modulus
shasum -a 256 FonollosaMinModulus/Challenge.lean
lake build && lake env lean scripts/check_axioms.lean

# 5. Verify Catch-Up Game Lean 4 package (137 theorems / 88 public declarations, 28,259 constants)
cd ../../tcs/catch-up-game
shasum -a 256 CatchUpGame/Challenge.lean
lake build && python3 -B scripts/audit.py
```

---

## Integrity Guarantee

Every target problem begins with an audited, unweakened Lean 4 statement (`Challenge.lean`) locked read-only (`0444`) and pinned by SHA-256 across all research rounds:

| Problem | Frozen Statement | SHA-256 |
|---|---|---|
| TxGraffiti Conjecture 3 | [`TxGraffiti3/Challenge.lean`](problems/combinatorics/txgraffiti-3/TxGraffiti3/Challenge.lean) | `d54daf16a077ec5cf824d8fc0f336888a413396799bc203c1b14d4cd85430d41` |
| Tutte's 3-Flow Conjecture | [`Tutte3Flow/Challenge.lean`](problems/combinatorics/tutte-3-flow/Tutte3Flow/Challenge.lean) | `cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6` |
| Fourier Entropy–Influence | [`FEI/Challenge.lean`](problems/analysis/fourier-entropy-influence/FEI/Challenge.lean) | `6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b` |
| Fonollosa's Minimum Modulus | [`FonollosaMinModulus/Challenge.lean`](problems/number-theory/fonollosa-min-modulus/FonollosaMinModulus/Challenge.lean) | `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91` |
| Catch-Up Game Even-Sum Draw | [`CatchUpGame/Challenge.lean`](problems/tcs/catch-up-game/CatchUpGame/Challenge.lean) | `0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3` |
