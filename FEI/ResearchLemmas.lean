module

public import FEI.ChallengeSanity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt

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

/-- The conditional mean and derivative of a sign have disjoint support and
their squared magnitudes partition the two restrictions. -/
theorem boolean_restriction_pair (u v : Bool) :
    let e := (pm u + pm v) / 2
    let d := (pm u - pm v) / 2
    e * d = 0 ∧ e ^ 2 + d ^ 2 = 1 := by
  cases u <;> cases v <;> norm_num [pm]

/-- The constant and the three nonconstant coefficients of a two-dimensional
face satisfy the Fourier equations for the square of a sign function. -/
theorem boolean_face_equations (p q r s : Bool) :
    let a := (pm p + pm q + pm r + pm s) / 4
    let b := (pm p - pm q + pm r - pm s) / 4
    let c := (pm p + pm q - pm r - pm s) / 4
    let d := (pm p - pm q - pm r + pm s) / 4
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧
      a * d + b * c = 0 ∧ a * b + c * d = 0 ∧ a * c + b * d = 0 := by
  cases p <;> cases q <;> cases r <;> cases s <;> norm_num [pm]

/-- Cauchy–Schwarz for pooled loss on the actual spectrum of the frozen
statement. The empty set has zero loss, including for a biased function. -/
theorem spectral_pooled_cauchy {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A : Finset (Fin n) → ℝ) (hA : A ∅ = 0) :
    (∑ S, (fourierCoeff f S) ^ 2 * A S) ^ 2 ≤ totalInfluence f *
      ∑ S, (fourierCoeff f S) ^ 2 * (A S) ^ 2 / (S.card : ℝ) := by
  rw [totalInfluence_eq_spectralInfluence, spectralInfluence]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro S _
    positivity
  · intro S _
    positivity
  · intro S _
    by_cases hs : S = ∅
    · simp [hs, hA]
    · have hcard : 0 < (S.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      apply le_of_eq
      field_simp [ne_of_gt hcard]

/-- A mixed-loss bound closes the quadratic inequality for the square root
of normalized pooled loss. The analytic diagonal estimate is a hypothesis. -/
theorem pooled_sqrt_bound {y c : ℝ} (hc : 0 ≤ c) (h : y ^ 2 ≤ 3 * y + c) :
    y ≤ 3 + Real.sqrt c := by
  by_contra! hy
  have hs := Real.sq_sqrt hc
  have hn := Real.sqrt_nonneg c
  have hp : 0 < (y - 3 - Real.sqrt c) * (y + Real.sqrt c) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- In a perfect matching, the contributions from the core and the fresh gate
inherit their bounds. The remaining entropy and excess influence have ratio 4.
The hypotheses give the two exact Walsh identities. -/
theorem perfect_matching_score {h i hg ig hb ib t d R : ℝ}
    (ht : t ^ 2 ≤ 1) (hd : 0 ≤ d) (hR : 4 ≤ R)
    (hg' : hg ≤ R * (ig - 1)) (hb' : hb ≤ R * (ib - 1))
    (he : h = hg + t ^ 2 * hb + 2 * d * (1 - t ^ 2))
    (hi : i - 1 = (ig - 1) + t ^ 2 * (ib - 1) + d / 2 * (1 - t ^ 2)) :
    h ≤ R * (i - 1) := by
  rw [he, hi]
  have hcore := mul_le_mul_of_nonneg_left hb' (sq_nonneg t)
  have hcopy := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg hd (sub_nonneg.mpr ht))
  linarith

end FEI
