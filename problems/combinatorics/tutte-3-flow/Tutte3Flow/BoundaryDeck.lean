module

public import Tutte3Flow.EdgeInsertion
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

/-! # Boundary counts across edge deletions and affine cycle lines -/

namespace FinMultigraph

open Finset

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : FinMultigraph V E)

/-- Column of the incidence matrix for a unit edge directed from `x` to `y`. -/
@[expose] public def unitColumn (x y : V) (v : V) : ZMod 3 :=
  (if x = v then 1 else 0) - (if y = v then 1 else 0)

/-- Number of orientations with a prescribed modular boundary. Parallel edges are labelled. -/
@[expose] public def orientationBoundaryCount [Fintype V] [DecidableEq E] (γ : V → ZMod 3) : ℕ :=
  ∑ b : E → Bool, if G.mod3Divergence (fun e => if b e then 1 else -1) = γ then 1 else 0

/-- Partition the orientations by the sign assigned to the newly adjoined edge. -/
public theorem boundaryCount_adjoin [Fintype V] [DecidableEq E] (x y : V) (γ : V → ZMod 3) :
    (G.adjoinReferenceEdge x y).orientationBoundaryCount γ =
      G.orientationBoundaryCount (γ - unitColumn x y) +
      G.orientationBoundaryCount (γ + unitColumn x y) := by
  let hit (s : Bool) (b : E → Bool) : ℕ :=
    if G.mod3Divergence (fun e => if b e then 1 else -1) =
      (if s then γ - unitColumn x y else γ + unitColumn x y) then 1 else 0
  calc
    _ = ∑ p : Bool × (E → Bool), hit p.1 p.2 := by
      unfold orientationBoundaryCount
      apply Fintype.sum_equiv Equiv.piOptionEquivProd _ _
      intro b
      unfold hit
      change (if _ then 1 else 0) = (if _ = (if b none then _ else _) then 1 else 0)
      congr 1
      apply propext
      rw [funext_iff, funext_iff]
      apply forall_congr'
      intro v
      rw [divergence_adjoin]
      cases hs : b none <;> by_cases hx : x = v <;> by_cases hy : y = v <;>
        simp [hs, hx, hy, unitColumn, eq_add_neg_iff_add_eq, sub_eq_add_neg, add_comm] <;>
        exact (show ∀ a b : ZMod 3, -1 + a = b ↔ a = b + 1 by decide) _ _
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      rfl

/-- A missing boundary forces equal counts at both neighbours along this edge column. -/
public theorem boundaryCount_neighbors_of_gap [Fintype V] [DecidableEq E] (x y : V) (γ : V → ZMod 3)
    (gap : (G.adjoinReferenceEdge x y).orientationBoundaryCount γ = 0) :
    (G.adjoinReferenceEdge x y).orientationBoundaryCount (γ + unitColumn x y) =
        G.orientationBoundaryCount γ ∧
      (G.adjoinReferenceEdge x y).orientationBoundaryCount (γ - unitColumn x y) =
        G.orientationBoundaryCount γ := by
  rw [boundaryCount_adjoin] at gap
  obtain ⟨noMinus, noPlus⟩ := Nat.add_eq_zero_iff.mp gap
  have plus2 : γ + unitColumn x y + unitColumn x y = γ - unitColumn x y := by
    funext v
    exact (show ∀ a b : ZMod 3, a + b + b = a - b by decide) _ _
  have minus2 : γ - unitColumn x y - unitColumn x y = γ + unitColumn x y := by
    funext v
    exact (show ∀ a b : ZMod 3, a - b - b = a + b by decide) _ _
  simp [boundaryCount_adjoin, plus2, minus2, noPlus, noMinus]

/-- Translation along a circulation stays in the same boundary fibre. -/
public theorem divergence_add_circulation (f c : E → ZMod 3)
    (hc : ∀ v, G.mod3Divergence c v = 0) (t : ZMod 3) :
    G.mod3Divergence (fun e => f e + t * c e) = G.mod3Divergence f := by
  funext v
  simp only [mod3Divergence, sum_add_distrib, ← mul_sum] at hc ⊢
  rw [sub_eq_zero.mp (hc v)]
  abel

/-- Positions at which a normalized cycle coordinate vanishes at the given shift. -/
@[expose] public def cycleZeroClass {k : ℕ} (w : Fin k → Fin 3) (t : Fin 3) : Finset (Fin k) :=
  univ.filter (fun i => w i = t)

/-- If all three shifts have a zero on a triangle, each shift has exactly one. -/
public theorem triangle_cycle_singletons :
    ∀ w : Fin 3 → Fin 3, (∀ t, (cycleZeroClass w t).Nonempty) →
      ∀ t, (cycleZeroClass w t).card = 1 := by decide

/-- On a four-cycle, a specified edge is alone in its class precisely when the unique
doubleton class avoids that edge. This is the per-line square deletion identity. -/
public theorem square_cycle_singleton_iff :
    ∀ w : Fin 4 → Fin 3, (∀ t, (cycleZeroClass w t).Nonempty) → ∀ i,
      (cycleZeroClass w (w i)).card = 1 ↔
        (univ.filter (fun t => (cycleZeroClass w t).card = 2 ∧ i ∉ cycleZeroClass w t)).card = 1 := by
  decide

end FinMultigraph
