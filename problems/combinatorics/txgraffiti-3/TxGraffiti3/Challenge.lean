import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

/-!
# TxGraffiti Conjecture 3 (Frozen Challenge Statement)

Reference:
- Randy Davila, Boris Brimkov, Ryan Pepper,
  *In Reverie Together: Ten Years of Mathematical Discovery with a Machine Collaborator*,
  arXiv:2507.17780 (Conjecture 3, open since 2020).
- Upstream formalization: `google-deepmind/formal-conjectures`
  (`FormalConjectures/Arxiv/2507.17780/3.lean`).

Statement: For every finite `r`-regular simple graph `G` with `r ≥ 1`,
`i(G) ≤ μ*(G)`, where `i(G)` is the independent domination number (minimum cardinality
of a maximal independent set) and `μ*(G)` is the saturation number (minimum cardinality
of a maximal matching).

THIS FILE IS FROZEN AND READ-ONLY. DO NOT MODIFY.
-/

namespace TxGraffiti3

open SimpleGraph

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set `D` is a dominating set for `G` if every vertex of `G` is either in `D`
or adjacent to a vertex of `D`. -/
def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- An `n`-independent dominating set is an independent dominating set of cardinality `n`. -/
@[mk_iff]
structure IsNIndepDominatingSet (G : SimpleGraph α) (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet (D : Set α)
  isDominating : IsDominating G (D : Set α)
  card_eq : D.card = n

/-- The independent domination number `i(G)`: minimum size of a maximal independent set. -/
noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, IsNIndepDominatingSet G n D}

/-- A finite set of edges `M` is a matching of `G` if every element of `M` is an edge of `G`
and distinct edges in `M` share no vertex. -/
def IsEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ = e₂ ∨ ∀ v : α, ¬ (v ∈ e₁ ∧ v ∈ e₂)

instance instDecidableIsEdgeMatching (G : SimpleGraph α) [DecidableRel G.Adj]
    (M : Finset (Sym2 α)) : Decidable (IsEdgeMatching G M) := by
  unfold IsEdgeMatching; infer_instance

/-- A matching `M` of `G` is maximal if no further edge of `G` can be added while preserving
the matching property. -/
def IsMaximalEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  IsEdgeMatching G M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ¬ IsEdgeMatching G (insert e M)

instance instDecidableIsMaximalEdgeMatching (G : SimpleGraph α) [DecidableRel G.Adj]
    (M : Finset (Sym2 α)) : Decidable (IsMaximalEdgeMatching G M) := by
  unfold IsMaximalEdgeMatching; infer_instance

/-- The saturation number `μ*(G)` (minimum size of a maximal matching). -/
noncomputable def saturationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), IsMaximalEdgeMatching G M ∧ M.card = n}

end Definitions

/-- **TxGraffiti Conjecture 3 (Davila–Brimkov–Pepper, arXiv:2507.17780):**
For every finite `r`-regular simple graph `G` (`r ≥ 1`), `i(G) ≤ μ*(G)`. -/
def TxGraffitiConjecture3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), (∀ v, G.degree v = r) → 1 ≤ r →
      indepDominationNumber G ≤ saturationNumber G

end TxGraffiti3
