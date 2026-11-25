module

public import Tutte3Flow.Challenge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

/-! # Modulo-three orientations and flows -/

namespace FinMultigraph

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : FinMultigraph V E)

private def edgeValue (reverse : Bool) : ZMod 3 := if reverse then -1 else 1

-- Reversing an edge negates its contribution to outdegree minus indegree.
private theorem degreeDifference (reverse : E → Bool) (v : V) :
    ((Finset.univ.filter (fun e => (G.reorient reverse).src e = v)).card : ZMod 3) -
    ((Finset.univ.filter (fun e => (G.reorient reverse).dst e = v)).card : ZMod 3) =
    (∑ e ∈ Finset.univ.filter (fun e => G.src e = v), edgeValue (reverse e)) -
    (∑ e ∈ Finset.univ.filter (fun e => G.dst e = v), edgeValue (reverse e)) := by
  simp only [Finset.natCast_card_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases h : reverse e <;> by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
    simp [reorient, edgeValue, h, hs, ht]

/-- An edge directed with the reference orientation carries `1`, and a reversed edge carries `-1`. -/
public theorem hasMod3Orientation_iff_hasNowhereZeroZMod3Flow :
    G.HasMod3Orientation ↔ G.HasNowhereZeroZMod3Flow := by
  constructor
  · rintro ⟨reverse, h⟩
    refine ⟨fun e => edgeValue (reverse e), fun e => ?_, fun v => ?_⟩
    · change edgeValue (reverse e) ≠ 0
      cases reverse e <;> decide
    · exact sub_eq_zero.mp ((G.degreeDifference reverse v).symm.trans (sub_eq_zero.mpr (h v)))
  · rintro ⟨f, hn, h⟩
    let reverse (e : E) := decide (f e = -1)
    have classify : ∀ a : ZMod 3, a ≠ 0 → edgeValue (decide (a = -1)) = a := by decide
    have value (e : E) : edgeValue (reverse e) = f e := classify _ (hn e)
    refine ⟨reverse, fun v => sub_eq_zero.mp ?_⟩
    rw [G.degreeDifference]
    simp only [value, h v, sub_self]

/-- Reducing a nowhere-zero integer 3-flow modulo three preserves nonvanishing and balance. -/
public theorem hasNowhereZeroZMod3Flow_of_hasNowhereZeroIntFlow
    (h : G.HasNowhereZeroIntFlow 3) : G.HasNowhereZeroZMod3Flow := by
  obtain ⟨f, bounds, balance⟩ := h
  refine ⟨fun e => (f e : ZMod 3), ?_, fun v => ?_⟩
  · intro e hz
    obtain ⟨hn, hb⟩ := bounds e
    obtain ⟨lo, hi⟩ := abs_lt.mp hb
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    omega
  · simpa only [Int.cast_sum] using congrArg (fun n : ℤ => (n : ZMod 3)) (balance v)

end FinMultigraph
