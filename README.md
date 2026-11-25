# Pioneer — Open Mathematics Research & Lean 4 Verification

An expanding, multi-domain research repository tackling open problems in mathematics through **frozen Lean 4 challenge statements**, **multi-round frontier AI mathematical discovery**, **exact symbolic/computational certificates**, and **kernel-verified Lean 4 proofs**.

Problems are organized strictly by **mathematical field** (not tied to any single benchmark list), while external references (ProofAtlas Top 500, Erdős Problems, `teorth/optimizationproblems`, arXiv, independent conjectures) are tracked in [`catalog.json`](catalog.json). See [`METHODOLOGY.md`](METHODOLOGY.md) for the frozen-statement integrity rules and verification standards.

---

## Active Problem Catalog

| Field | Problem | External References | Status | Lean 4 Theorems (`sorry` = 0) | Key Results |
|---|---|---|---|---:|---|
| **Combinatorics** (`graph-theory`) | [**Tutte's 3-Flow Conjecture**](problems/combinatorics/tutte-3-flow/) | ProofAtlas `#355` | Partial Theorems & Lean Package | **72** (`56` pub / `16` priv) | $\le 16$ odd-vertex & unrestricted $b \le 12$ pinned theorems (105.6B classes certified); kernel-verified arbitrary-$r$ matching-tree $2^{r-1}$ hole & one-edge repair theorem; 88-vertex coupled electrical obstruction |
| **Analysis** (`boolean-fourier`) | [**Fourier Entropy–Influence (FEI) Conjecture**](problems/analysis/fourier-entropy-influence/) | ProofAtlas `#412`, [`#71a`](https://teorth.github.io/optimizationproblems/constants/71a.html) | **New World Record** & Lean Package | **87** (`51` pub / `36` priv) | Certified finite lower bound **$H/I > 6.521851167347822949109657013506222645$** (beats `#71a`); kernel-verified midpoint-crossing FEI equivalence; fixed-error matrix-rank equivalence + non-XOR CHSH lift ($> 3.76092558$) |

**Repository Totals:** `2` active campaigns · **`159` Lean 4 kernel-verified theorems** (`107` public + `52` private, **0 `sorry`**, **0 `admit`**, standard axioms `propext`, `Classical.choice`, `Quot.sound` only) · **`1` certified world-record constant** (`#71a`).

---

## Directory Layout

```text
pioneer/
├── README.md                                        # Master catalog & scoreboard
├── METHODOLOGY.md                                   # Frozen-Challenge protocol & verification rules
├── catalog.json                                     # Machine-readable registry (fields, external IDs, stats)
└── problems/
    ├── combinatorics/
    │   └── tutte-3-flow/                            # Standalone Lean 4.36 project + exact C++/Python censuses
    └── analysis/
        └── fourier-entropy-influence/               # Standalone Lean 4.36 project + stdlib #71a certificate
```

Future campaigns across `number-theory/`, `algebra/`, `geometry/`, `probability/`, and `tcs/` slot directly under `problems/<field>/<slug>/` as self-contained Lean 4 projects and register in [`catalog.json`](catalog.json).

---

## Quick Verification

Every problem directory is independently verifiable:

```bash
# 1. Verify Tutte's 3-Flow Conjecture Lean 4 package (72 theorems, standard axioms only)
cd problems/combinatorics/tutte-3-flow
shasum -a 256 Tutte3Flow/Challenge.lean
lake build
python3 -B scripts/round2_audit.py

# 2. Verify FEI world-record #71a certificate (stdlib only) & Lean 4 package (87 theorems)
cd ../../analysis/fourier-entropy-influence
shasum -a 256 FEI/Challenge.lean
python3 scripts/max5_record.py
lake build
python3 scripts/max5_audit.py
```

---

## Integrity Guarantee

Every target problem begins with an audited, unweakened Lean 4 statement (`Challenge.lean`) locked read-only (`0444`) and pinned by SHA-256 across all research rounds:

| Problem | Frozen Statement | SHA-256 |
|---|---|---|
| Tutte's 3-Flow Conjecture | [`Tutte3Flow/Challenge.lean`](problems/combinatorics/tutte-3-flow/Tutte3Flow/Challenge.lean) | `cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6` |
| Fourier Entropy–Influence | [`FEI/Challenge.lean`](problems/analysis/fourier-entropy-influence/FEI/Challenge.lean) | `6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b` |
