module

public import FEI.ChallengeSanity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Auxiliary bounds for the FEI experiments. -/

public section

namespace FEI

open Filter Topology

/-- Entropy contribution of a product of spectral masses. -/
theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp, entropyTerm]
  by_cases hq : q = 0
  · simp [hq, entropyTerm]
  simp only [entropyTerm, ite_eq_right hp, ite_eq_right hq, ite_eq_right (mul_ne_zero hp hq),
    Real.logb_mul hp hq]
  ring

/-- Fixing k address bits replicates a private spectral mass on 2^k characters,
each with its amplitude divided by 2^k. -/
theorem dyadic_copy_entropy (k : ℕ) (p : ℝ) :
    (2 : ℝ)^k * entropyTerm (p / ((2 : ℝ)^k)^2) =
      (entropyTerm p + 2 * k * p) / (2 : ℝ)^k := by
  by_cases hp : p = 0
  · simp [hp, entropyTerm]
  have hd : ((2 : ℝ)^k)^2 ≠ 0 := by positivity
  simp only [entropyTerm, ite_eq_right hp, ite_eq_right (div_ne_zero hp hd), Real.logb_div hp hd,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
  push_cast
  field_simp
  ring

/-- First-moment Fourier tail estimate in the normalization of the challenge. -/
theorem levelTail_mul_le_totalInfluence {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) :
    (d : ℝ) * (∑ S : Finset (Fin n), if d ≤ S.card then (fourierCoeff f S) ^ 2 else 0) ≤
      totalInfluence f := by
  rw [totalInfluence_eq_spectralInfluence, spectralInfluence, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with h
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
  · simp only [mul_zero]
    positivity

/-- Ratio recurrence of iterated balanced composition, after dividing by influence. -/
theorem amplification_ratio_formula {h a : ℝ} (ha : 1 < a) (r : ℕ → ℝ)
    (hz : r 0 = 0) (hs : ∀ k, r (k + 1) = r k + h / a ^ (k + 1)) (k : ℕ) :
    r k = h / (a - 1) * (1 - a⁻¹ ^ k) := by
  have hn : a ≠ 0 := by linarith
  have hm : a - 1 ≠ 0 := by linarith
  induction k with
  | zero => simp [hz]
  | succ k ih =>
    rw [hs, ih, inv_pow, inv_pow, pow_succ]
    field_simp
    ring

/-- Once the ratio recurrence has been obtained on realizable cubes, any uniform
FEI bound dominates the amplified score. The hypotheses expose the combinatorial
composition step needed by callers. -/
theorem amplified_score_le_uniform_bound {C h a : ℝ} (ha : 1 < a)
    (bound : ∀ n (f : (Fin n → Bool) → Bool), fourierEntropy f ≤ C * totalInfluence f)
    (dims : ℕ → ℕ) (family : (k : ℕ) → (Fin (dims k) → Bool) → Bool)
    (r : ℕ → ℝ) (hz : r 0 = 0) (hs : ∀ k, r (k + 1) = r k + h / a ^ (k + 1))
    (hi : ∀ k, 0 < totalInfluence (family k))
    (hr : ∀ k, r k = fourierEntropy (family k) / totalInfluence (family k)) :
    h / (a - 1) ≤ C := by
  have ha' : 0 < a := by linarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr ha'.le)
    (inv_lt_one_of_one_lt₀ ha)
  have conv : Tendsto r atTop (𝓝 (h / (a - 1))) := by
    simp_rw [funext (amplification_ratio_formula ha r hz hs)]
    have one : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using (one.sub ht).const_mul (h / (a - 1))
  apply le_of_tendsto conv
  exact Eventually.of_forall fun k ↦ (hr k) ▸ ((div_le_iff₀ (hi k)).mpr (bound _ _))

end FEI
