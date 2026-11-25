# Tutte's 3-Flow Conjecture

- **Field:** Combinatorics — Graph Theory (Nowhere-Zero Flows & Modular Orientations)
- **Catalog References:** ProofAtlas Top 500 `#355`
- **Status:** Open (Full conjecture unresolved — **Case C**); major unconditional partial theorems, exact computer-assisted censuses, sharp structural obstructions, and **72 kernel-verified Lean 4 theorems** completed across 1 `xhigh` recon + 5 `max` research rounds.
- **Frozen Challenge Statement:** [`Tutte3Flow/Challenge.lean`](Tutte3Flow/Challenge.lean)
  - **SHA-256:** `cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6`
  - Full unweakened statement: every finite 4-edge-connected multigraph admits a nowhere-zero integer 3-flow.

---

## Headline Results

Full proofs, methodology, literature comparisons, and verification ledgers are documented in [`RESEARCH_ANALYSIS.md`](RESEARCH_ANALYSIS.md).

1. **Sixteen Odd-Vertex Theorem (Unpinned, Arbitrary Graph Order — §12.1–12.2):**
   Every finite 4-edge-connected multigraph (and more generally every connected odd-5-edge-connected multigraph) with **at most 16 odd-degree vertices** admits a nowhere-zero integer 3-flow. Consequently, **every counterexample to Tutte's 3-Flow Conjecture must have at least 18 odd-degree vertices**.
2. **Unrestricted Twelve Nonroot Degree-Five Pinned Theorem ($b \le 12$, Arbitrary Graph Order — §11.2, §12.1–12.2):**
   In any finite 5-edge-connected multigraph with no nontrivial 5-cut and at most 12 nonroot degree-5 vertices, every compatible zero-boundary star at a degree-5 root extends to a modulo-3 orientation (arbitrary graph order).
   - Backed by a **100% self-contained proof** of the reduced-density inequality $m \le 3h - 7$ via vertex-lattice electrical rounding (§11.2), and two **independent exact C++17 enumerators** ([`round5_census.cpp`](scripts/round5_census.cpp) using `nauty` and [`round5_replay.cpp`](scripts/round5_replay.cpp) without `nauty`) certifying all **139,242,686** isomorphism classes at free order 13 and **105,577,935,570** isomorphism classes at free order 15 (**zero reduced survivors**), cross-checked against exact Burnside enumeration ([`round5_burnside.py`](scripts/round5_burnside.py)).
3. **End-to-End Lean 4 Kernel Proof: Exact $2^{r-1}$ Missing-Boundary Formula & One-Edge Repair ([`Tutte3Flow/MatchingTree.lean`](Tutte3Flow/MatchingTree.lean)):**
   Joining $r \ge 1$ disjoint one-hole finite multigraphs (such as $K_4$) along any tree via 3-edge matchings yields **exactly $2^{r-1}$ missing balanced $\mathbb{Z}_3$-boundaries** (distinguishable even after erasing any one block's coordinates), and **adding any single edge between distinct blocks makes the entire graph $\mathbb{Z}_3$-connected**. Proved completely in Lean 4 for arbitrary $r \ge 1$.
4. **Sharp Structural Obstructions:**
   - **Unbounded neutral-exchange & support/branching tradeoff (§8–9):** Explicit $18 + 12k$ seven-cut family requiring $(k-1)/2$ neutral exchanges and exhibiting exact tradeoff $(7k+9)/2$ ($k+1$ branches) vs $(7k+11)/2$ ($k$ branches).
   - **Six-Vertex Cover Theorem (§10.4):** Every zero-sum boundary extends on any reduced core with vertex cover number $\le 6$ (allowing separating 5-cuts).
   - **Pinned 5-Cube Obstruction to Unsigned Thin-Tree Cut Bounds (§11.3):** $Q_5$ meets all connectivity conditions and extends all 10 compatible root stars, yet its 5 coordinate bonds impose fractional-tree thresholds summing to 85 against universal fractional-tree budget 90.
   - **88-Vertex Unweighted Obstruction to Coupled Electrical Rounding (§12.3):** Every global unweighted Laplacian energy minimizer demands divergence $8$ at a degree-4 free vertex (minimum energy $17551/524$; degree-5 obstruction at 109 vertices) despite the pinned star extending.
   - **Larger-Order Certification (§12.4):** All 409,600 root/minority stars extend across 4,096 targeted double covers, and every connected 5-shift cyclic bipartite graph of orders 18–36 (all 262 affine orbits) stays $\mathbb{Z}_3$-connected after deleting any vertex.

---

## Lean 4 Verification (72 Kernel-Verified Theorems)

Built with **Lean 4.36.0** + **Mathlib `v4.36.0`**. Zero `sorry`, zero `admit`, zero `native_decide`; every theorem uses only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Module | Theorems (Pub / Priv) | Scope |
|---|---:|---|
| [`Challenge.lean`](Tutte3Flow/Challenge.lean) | Frozen statement | Unweakened Tutte 3-Flow Conjecture on finite multigraphs |
| [`ChallengeSanity.lean`](Tutte3Flow/ChallengeSanity.lean) | 2 / 0 | $K_4$ sharpness and 4-parallel-edge witness |
| [`Equivalence.lean`](Tutte3Flow/Equivalence.lean) | 2 / 1 | Nowhere-zero $\mathbb{Z}/3\mathbb{Z}$-flow $\iff$ mod-3 orientation |
| [`IntegralLift.lean`](Tutte3Flow/IntegralLift.lean) | 2 / 1 | Full equivalence `hasMod3Orientation_iff_hasNowhereZeroIntFlow` |
| [`PrescribedDegrees.lean`](Tutte3Flow/PrescribedDegrees.lean) | 2 / 0 | Necessary and sufficient outdegree quota orientation criterion |
| [`ModularBase.lean`](Tutte3Flow/ModularBase.lean) | 1 / 1 | Modular outdegree reformulation of integer 3-flows |
| [`EdgeInsertion.lean`](Tutte3Flow/EdgeInsertion.lean) | 3 / 2 | Rooted edge-insertion transfer characterization |
| [`TransferReorientation.lean`](Tutte3Flow/TransferReorientation.lean) | 2 / 2 | Reorientation algebra on transfer sets |
| [`TransferExample.lean`](Tutte3Flow/TransferExample.lean) | 6 / 0 | Explicit shortest-transfer and full integer-flow witnesses |
| [`TransferTemplates.lean`](Tutte3Flow/TransferTemplates.lean) | 2 / 0 | Fork table and tight-chain exclusion |
| [`BoundaryDeck.lean`](Tutte3Flow/BoundaryDeck.lean) | 5 / 0 | Boundary count deck, triangle/square cycle identities |
| [`CutRounding.lean`](Tutte3Flow/CutRounding.lean) | 4 / 0 | Integer cut-demand orientation criterion & degree-5 saturation |
| [`PairedInterfaces.lean`](Tutte3Flow/PairedInterfaces.lean) | 8 / 0 | 3-port/4-port common-state theorems, $K_4$ signature, edge repair |
| [`MatchingJoin.lean`](Tutte3Flow/MatchingJoin.lean) | 7 / 1 | Two-block triple-matching exact hole theorem & edge repair |
| [`MatchingTree.lean`](Tutte3Flow/MatchingTree.lean) | 8 / 8 | Arbitrary-$r$ matching-tree $2^{r-1}$ hole count & one-edge repair |
| [`VoltageLift.lean`](Tutte3Flow/VoltageLift.lean) | 2 / 0 | Signed voltage double-cover complementary channel decomposition |
| **Total** | **56 / 16 (72)** | **100% standard axioms, 0 `sorry`** |

---

## Reproduction

```bash
# 1. Verify frozen statement integrity
shasum -a 256 Tutte3Flow/Challenge.lean
# Expected: cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6

# 2. Build all 72 Lean 4 theorems and audit axioms
lake build
python3 -B scripts/round2_audit.py

# 3. Replay Round 5 exact censuses & certificates (requires Python 3 + NumPy/SciPy/NetworkX, clang++, nauty)
python3 -B scripts/round5_certify.py
python3 -B scripts/round5_splitting.py
python3 -B scripts/round5_energy.py
python3 -B scripts/round5_covers.py
python3 -B scripts/round4_interfaces.py
```
