module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs

/-! # Tutte's 3-flow conjecture -/

@[expose] public section

/-- The two endpoints of each edge, in a fixed reference orientation.
Distinct edges may share endpoints, and an edge may be a loop. -/
structure FinMultigraph (V E : Type*) where
  src : E → V
  dst : E → V

namespace FinMultigraph

variable {V E : Type*} (G : FinMultigraph V E) [Fintype E] [DecidableEq V]

/-- Edges with exactly one endpoint in `S`. Each parallel edge counts separately. -/
def cutEdges (S : Finset V) : Finset E :=
  Finset.univ.filter fun e =>
    (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S)

/-- Every nonempty proper vertex set has at least `k` edges crossing its cut. -/
def IsKEdgeConnected [Fintype V] (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ (G.cutEdges S).card

/-- Signed integer edge values of magnitude strictly between zero and `k`,
with equal outgoing and incoming sums at every vertex. A loop occurs in both sums. -/
def IsNowhereZeroIntFlow (k : ℕ) (f : E → ℤ) : Prop :=
  (∀ e, f e ≠ 0 ∧ |f e| < (k : ℤ)) ∧
  ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => G.src e = v), f e) =
           (∑ e ∈ Finset.univ.filter (fun e => G.dst e = v), f e)

/-- Existence of a nowhere-zero integer `k`-flow in the reference orientation. -/
def HasNowhereZeroIntFlow (k : ℕ) : Prop :=
  ∃ f, G.IsNowhereZeroIntFlow k f

/-- Nonzero residues on the edges whose outgoing and incoming sums agree modulo three. -/
def HasNowhereZeroZMod3Flow : Prop :=
  ∃ f : E → ZMod 3, (∀ e, f e ≠ 0) ∧
    ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => G.src e = v), f e) =
             (∑ e ∈ Finset.univ.filter (fun e => G.dst e = v), f e)

/-- Reverse precisely the edges marked `true`. -/
def reorient (reverse : E → Bool) : FinMultigraph V E where
  src e := if reverse e then G.dst e else G.src e
  dst e := if reverse e then G.src e else G.dst e

/-- Some orientation has outdegree congruent to indegree modulo three at every vertex. -/
def HasMod3Orientation : Prop :=
  ∃ reverse : E → Bool, ∀ v : V,
    ((Finset.univ.filter (fun e => (G.reorient reverse).src e = v)).card : ZMod 3) =
    ((Finset.univ.filter (fun e => (G.reorient reverse).dst e = v)).card : ZMod 3)

end FinMultigraph

/-- Tutte's 3-flow conjecture (1972). -/
def Tutte3FlowConjecture : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : FinMultigraph V E),
    G.IsKEdgeConnected 4 → G.HasNowhereZeroIntFlow 3
