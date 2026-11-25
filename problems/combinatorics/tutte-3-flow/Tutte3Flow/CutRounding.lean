module

public import Tutte3Flow.ModularBase
import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-! # Rounding an integral demand using cut bounds -/

namespace FinMultigraph

open Finset

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : FinMultigraph V E)

/-- The degree sum on a shore counts internal loops twice, like any internal edge. -/
public theorem incidenceDegree_sum_shore (s : Finset V) :
    ∑ v ∈ s, G.incidenceDegree v =
      2 * (G.internalEdges s).card + (G.cutEdges s).card := by
  classical
  simp only [incidenceDegree, Finset.sum_add_distrib, Finset.sum_card_fiberwise_eq_card_filter]
  simp only [internalEdges, cutEdges, Finset.card_filter, two_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : G.src e ∈ s <;> by_cases ht : G.dst e ∈ s <;> simp [hs, ht]

/-- An integer lift with the correct parities and cut bounds gives the prescribed
integer imbalance at every vertex. The conclusion counts the two incidences of a loop. -/
public theorem orientation_of_integral_cut_demands [Fintype V] (η : V → ℤ)
    (mass : ∑ v, η v = 0)
    (parity : ∀ v, 2 ∣ (G.incidenceDegree v : ℤ) + η v)
    (cuts : ∀ s : Finset V, |∑ v ∈ s, η v| ≤ ((G.cutEdges s).card : ℤ)) :
    ∃ r : E → Bool, ∀ v, 2 * ((univ.filter (fun e => (G.reorient r).src e = v)).card : ℤ)
      - (G.incidenceDegree v : ℤ) = η v := by
  classical
  choose k hk using parity
  have shore (s : Finset V) :
      2 * (∑ v ∈ s, k v) = 2 * ((G.internalEdges s).card : ℤ) +
        ((G.cutEdges s).card : ℤ) + ∑ v ∈ s, η v := by
    have incidence := G.incidenceDegree_sum_shore s
    have ie : (∑ v ∈ s, (G.incidenceDegree v : ℤ)) =
        2 * ((G.internalEdges s).card : ℤ) + ((G.cutEdges s).card : ℤ) := by exact_mod_cast incidence
    rw [Finset.mul_sum]
    simp_rw [← hk]
    rw [Finset.sum_add_distrib, ie]
  have bound (s : Finset V) : ((G.internalEdges s).card : ℤ) ≤ ∑ v ∈ s, k v := by
    have hm := (abs_le.mp (cuts s)).1
    linarith [shore s]
  have nonneg (v : V) : 0 ≤ k v := by
    simpa using le_trans (Int.natCast_nonneg _) (bound {v})
  let q (v : V) := (k v).toNat
  have qk (v : V) : (q v : ℤ) = k v := Int.toNat_of_nonneg (nonneg v)
  have total : Fintype.card E = ∑ v, q v := by
    have eq := shore univ
    simp [internalEdges, cutEdges, mass] at eq
    have totalInt : (Fintype.card E : ℤ) = ∑ v, (q v : ℤ) := by
      simp_rw [qk]
      linarith
    exact_mod_cast totalInt
  have quotas (s : Finset V) : (G.internalEdges s).card ≤ ∑ v ∈ s, q v := by
    have h : ((G.internalEdges s).card : ℤ) ≤ ∑ v ∈ s, (q v : ℤ) := by
      simp_rw [qk]
      exact bound s
    exact_mod_cast h
  obtain ⟨r, hr⟩ := (G.exists_orientation_with_outdegrees_iff q).mpr ⟨total, quotas⟩
  refine ⟨r, fun v => ?_⟩
  rw [hr v, qk]
  linarith [hk v]

/-- Comparing a closest lift with the two translates by six bounds its directional
derivative by three times the resistance in that direction. -/
public theorem quadratic_six_shift_bound {drop resistance : ℝ}
    (plus : 0 ≤ 12 * drop + 36 * resistance)
    (minus : 0 ≤ -12 * drop + 36 * resistance) : |drop| ≤ 3 * resistance := by
  apply abs_le.mpr
  constructor <;> linarith

/-- At a zero-residue vertex of odd degree an integral demand cannot have magnitude
strictly between three and nine. These are the bounds forced by four saturated edges. -/
public theorem degree_five_saturation_impossible {η : ℤ} {a : ℝ} (one : 1 < a)
    (nine : 5 * a < 9) (odd : Odd η) (zeroResidue : 3 ∣ η)
    (lower : 3 * a ≤ ((|η| : ℤ) : ℝ)) (upper : ((|η| : ℤ) : ℝ) ≤ 5 * a) : False := by
  have lo : (3 : ℝ) < ((|η| : ℤ) : ℝ) := by linarith
  have hi : ((|η| : ℤ) : ℝ) < 9 := by linarith
  have ilo : (3 : ℤ) < |η| := by exact_mod_cast lo
  have ihi : |η| < (9 : ℤ) := by exact_mod_cast hi
  obtain ⟨k, hk⟩ := odd
  obtain ⟨j, hj⟩ := zeroResidue
  rcases le_total 0 η with h | h
  · rw [abs_of_nonneg h] at ilo ihi
    omega
  · rw [abs_of_nonpos h] at ilo ihi
    omega

end FinMultigraph
