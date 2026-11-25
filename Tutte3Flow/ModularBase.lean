module

public import Tutte3Flow.IntegralLift
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

/-! # The modular outdegree criterion for an integer 3-flow -/

namespace FinMultigraph

open Finset

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : FinMultigraph V E)

/-- Counts both incidences of a loop. -/
@[expose] public def incidenceDegree (v : V) : ℕ :=
  (univ.filter (fun e => G.src e = v)).card + (univ.filter (fun e => G.dst e = v)).card

private theorem balance_iff_twice_outdegree (r : E → Bool) (v : V) :
    (((univ.filter (fun e => (G.reorient r).src e = v)).card : ZMod 3) =
     ((univ.filter (fun e => (G.reorient r).dst e = v)).card : ZMod 3)) ↔
    2 * ((univ.filter (fun e => (G.reorient r).src e = v)).card : ZMod 3) =
      (G.incidenceDegree v : ZMod 3) := by
  have total :
      ((univ.filter (fun e => (G.reorient r).src e = v)).card : ZMod 3) +
      ((univ.filter (fun e => (G.reorient r).dst e = v)).card : ZMod 3) =
      (G.incidenceDegree v : ZMod 3) := by
    simp only [incidenceDegree, Nat.cast_add, Finset.natCast_card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    cases h : r e <;> simp [reorient, h, add_comm]
  rw [← total, two_mul, add_right_inj]

/-- The integral orientation base contains a quota vector in the required residue class
exactly when the frozen graph has a nowhere-zero integer 3-flow. -/
public theorem hasNowhereZeroIntFlow_iff_exists_modular_outdegrees [Fintype V] :
    G.HasNowhereZeroIntFlow 3 ↔ ∃ q : V → ℕ,
      Fintype.card E = ∑ v, q v ∧
      (∀ s : Finset V, (G.internalEdges s).card ≤ ∑ v ∈ s, q v) ∧
      ∀ v, 2 * (q v : ZMod 3) = (G.incidenceDegree v : ZMod 3) := by
  rw [← G.hasMod3Orientation_iff_hasNowhereZeroIntFlow]
  constructor
  · rintro ⟨r, balanced⟩
    let q (v : V) := (univ.filter (fun e => (G.reorient r).src e = v)).card
    obtain ⟨mass, cuts⟩ := (G.exists_orientation_with_outdegrees_iff q).mp ⟨r, fun _ => rfl⟩
    exact ⟨q, mass, cuts, fun v => (G.balance_iff_twice_outdegree r v).mp (balanced v)⟩
  · rintro ⟨q, mass, cuts, residues⟩
    obtain ⟨r, h⟩ := (G.exists_orientation_with_outdegrees_iff q).mpr ⟨mass, cuts⟩
    refine ⟨r, fun v => (G.balance_iff_twice_outdegree r v).mpr ?_⟩
    rw [h v]
    exact residues v

end FinMultigraph
