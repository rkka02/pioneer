module

public import Tutte3Flow.EdgeInsertion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-! # How reversing a set of free edges acts on attainable transfer boundaries -/

namespace FinMultigraph

open Finset

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : FinMultigraph V E)

private theorem divergence_columns (g : E → ZMod 3) (v : V) :
    G.mod3Divergence g v = ∑ e, ((if G.src e = v then g e else 0) -
      (if G.dst e = v then g e else 0)) := by
  simp only [mod3Divergence, sum_filter, sum_sub_distrib]

/-- Symmetric difference transports subsets between two reference orientations.
The shift is the divergence of the reversed set. -/
public theorem subset_divergence_reorient (t b : E → Bool) (v : V) :
    (G.reorient t).mod3Divergence (fun e => if b e then 1 else 0) v =
      G.mod3Divergence (fun e => if (t e ^^ b e) then 1 else 0) v -
      G.mod3Divergence (fun e => if t e then 1 else 0) v := by
  rw [divergence_columns, divergence_columns, divergence_columns, ← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  cases ht : t e <;> cases hb : b e <;> by_cases a : G.src e = v <;> by_cases c : G.dst e = v <;>
    simp [reorient, ht, a, c]

private theorem unit_divergence_reorient (t : E → Bool) (v : V) :
    (G.reorient t).mod3Divergence (fun _ => 1) v =
      G.mod3Divergence (fun _ => 1) v + G.mod3Divergence (fun e => if t e then 1 else 0) v := by
  rw [divergence_columns, divergence_columns, divergence_columns, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  cases ht : t e <;> by_cases a : G.src e = v <;> by_cases c : G.dst e = v <;>
    simp [reorient, ht, a, c] <;> decide

/-- Divergences of subsets using only unpinned edges. -/
@[expose] public def transferSet (pinned : E → Prop) : Set (V → ZMod 3) :=
  {γ | ∃ b : E → Bool, (∀ e, pinned e → b e = false) ∧
    ∀ v, G.mod3Divergence (fun e => if b e then 1 else 0) v = γ v}

/-- Any two orientations agreeing on the pins and having the same modular boundary
have exactly the same attainable transfer boundaries. -/
public theorem transferSet_reorient_eq (pinned : E → Prop) (t : E → Bool)
    (fixed : ∀ e, pinned e → t e = false)
    (same : ∀ v, (G.reorient t).mod3Divergence (fun _ => 1) v =
      G.mod3Divergence (fun _ => 1) v) :
    (G.reorient t).transferSet pinned = G.transferSet pinned := by
  have zero (v : V) : G.mod3Divergence (fun e => if t e then 1 else 0) v = 0 := by
    have h := same v
    rw [G.unit_divergence_reorient] at h
    exact add_left_cancel (h.trans (add_zero _).symm)
  have transport (b : E → Bool) (v : V) := G.subset_divergence_reorient t b v
  simp only [zero, sub_zero] at transport
  ext γ
  constructor
  · rintro ⟨b, pins, h⟩
    exact ⟨fun e => t e ^^ b e, fun e he => by simp [fixed e he, pins e he],
      fun v => (transport b v).symm.trans (h v)⟩
  · rintro ⟨b, pins, h⟩
    refine ⟨fun e => t e ^^ b e, fun e he => by simp [fixed e he, pins e he], fun v => ?_⟩
    rw [transport]
    simpa using h v

end FinMultigraph
