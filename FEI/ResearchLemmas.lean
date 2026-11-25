module

public import FEI.ChallengeSanity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Round

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

/-- Removing the singleton level from total influence retains exactly the
incidences at which branching loss is measured. -/
theorem branching_mass_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    totalInfluence f - (∑ S, if S.card = 1 then (fourierCoeff f S) ^ 2 else 0) =
      ∑ S, if 2 ≤ S.card then (S.card : ℝ) * (fourierCoeff f S) ^ 2 else 0 := by
  rw [totalInfluence_eq_spectralInfluence, spectralInfluence, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h₀ : S.card = 0
  · simp [h₀]
  by_cases h₁ : S.card = 1
  · simp [h₁]
  have h₂ : 2 ≤ S.card := by omega
  simp [h₁, h₂]

/-- For a ternary derivative with positive, negative and zero masses p, m, z,
the expected absolute independent-copy difference is at most twice its variance. -/
theorem ternary_copy_gap_le_two_variance {p m z : ℝ} (hp : 0 ≤ p) (hm : 0 ≤ m)
    (h : p + m + z = 1) :
    2 * (p + m) * z + 4 * p * m ≤ 2 * (p + m - (p - m) ^ 2) := by
  have hz : z = 1 - (p + m) := by linarith
  rw [hz]
  nlinarith [mul_nonneg hp hm]

/-- The primitive positive row ratio of a nondegenerate independent Walsh bit
must be 1:1 once integer Parseval supplies this dyadic divisor. -/
theorem dyadic_sum_of_two_squares {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : a.Coprime b) (hd : a ^ 2 + b ^ 2 ∣ 2 ^ k) : a = 1 ∧ b = 1 := by
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hsmall : a ^ 2 + b ^ 2 ≤ 2 := by
    cases j with
    | zero => omega
    | succ j =>
      cases j with
      | zero => omega
      | succ j =>
        have hfour : 4 ∣ a ^ 2 + b ^ 2 := ⟨2 ^ j, by rw [hj, pow_succ, pow_succ]; ring⟩
        have hs (x : ℕ) : x ^ 2 % 4 = x % 2 := by
          exact_mod_cast Int.sq_emod_four (x : ℤ)
        have hmod := Nat.mod_eq_zero_of_dvd hfour
        rw [Nat.add_mod, hs, hs] at hmod
        have hdiv : 2 ∣ a.gcd b := Nat.dvd_gcd (by omega) (by omega)
        rw [hc.gcd_eq_one] at hdiv
        omega
  have h₁ : a ≤ a ^ 2 := by simpa [sq] using Nat.mul_le_mul_left a ha
  have h₂ : b ≤ b ^ 2 := by simpa [sq] using Nat.mul_le_mul_left b hb
  omega

/-- Completing the square in the routing calculation absorbs the inherited
loss into the influence added by the address. -/
theorem routed_excess_le {b v u e : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u) (hcharge : u * v ≤ e) :
    u * v * (14 * b - b ^ 2) + 25 * e ≤ 74 * e := by
  have h := mul_nonneg (mul_nonneg hu hv) (sq_nonneg (b - 7))
  nlinarith

/-- A quantized real slice pays its step size times every signed mean in
second moment. Normalized counting measure and Walsh signs give the affine
flat estimate once the partial Walsh coefficients lie on the indicated grid. -/
theorem signed_slice_mass {ι : Type*} (s : Finset ι) (w h σ : ι → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hw : ∀ i ∈ s, 0 ≤ w i) (hσ : ∀ i ∈ s, |σ i| ≤ 1)
    (hgrid : ∀ i ∈ s, δ * |h i| ≤ (h i) ^ 2) :
    δ * |∑ i ∈ s, w i * h i * σ i| ≤ ∑ i ∈ s, w i * (h i) ^ 2 := by
  calc
    _ ≤ δ * ∑ i ∈ s, |w i * h i * σ i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
    _ = ∑ i ∈ s, δ * |w i * h i * σ i| := Finset.mul_sum ..
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (hw i hi)]
      calc
        δ * (w i * |h i| * |σ i|) ≤ δ * (w i * |h i| * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hσ i hi) (mul_nonneg (hw i hi) (abs_nonneg _))) hδ
        _ = w i * (δ * |h i|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hgrid i hi) (hw i hi)

/-- If the inverse Walsh values are odd integers, Parseval with unit mean
square forces each physical value to be a Boolean sign. -/
theorem sign_of_odd_unit_energy {ι : Type*} [Fintype ι] (v : ι → ℤ)
    (ho : ∀ i, Odd (v i)) (he : ∑ i, (v i) ^ 2 = (Fintype.card ι : ℤ)) :
    ∀ i, v i = 1 ∨ v i = -1 := by
  have hmin (i : ι) : 1 ≤ (v i) ^ 2 := by
    obtain ⟨k, hk⟩ := ho i
    have hn : v i ≠ 0 := by omega
    have hp := sq_pos_of_ne_zero hn
    omega
  have hz : (∑ i, ((v i) ^ 2 - 1)) = 0 := by
    rw [Finset.sum_sub_distrib, he]
    simp
  intro i
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ ↦ sub_nonneg.mpr (hmin j))).1 hz i (Finset.mem_univ i)
  have hprod : (v i - 1) * (v i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h | h <;> omega

/-- Copying both ends of a deletion edge with a common amplitude multiplier
scales its loss contribution by the square of that multiplier. -/
theorem scaled_deletion_loss (c a b : ℝ) :
    (c * a) ^ 2 * Real.logb 2 (1 + (c * b) ^ 2 / (c * a) ^ 2) =
      c ^ 2 * (a ^ 2 * Real.logb 2 (1 + b ^ 2 / a ^ 2)) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases ha : a = 0
  · simp [ha]
  have hr : (c * b) ^ 2 / (c * a) ^ 2 = b ^ 2 / a ^ 2 := by
    field_simp
  rw [hr, mul_pow]
  ring

/-- Squared distance to the grid of integer multiples of a positive step. -/
noncomputable def gridError (h x : ℝ) : ℝ := (x - h * (round (x / h) : ℤ)) ^ 2

theorem gridError_le_candidate {h : ℝ} (hh : 0 < h) (x : ℝ) (z : ℤ) :
    gridError h x ≤ (x - h * z) ^ 2 := by
  have h₁ := round_le (x / h) z
  have h₂ := mul_le_mul_of_nonneg_left h₁ hh.le
  rw [← abs_of_pos hh, ← abs_mul, ← abs_mul, abs_of_pos hh] at h₂
  have hx : h * (x / h) = x := by field_simp
  simp only [mul_sub, hx] at h₂
  exact sq_le_sq.mpr h₂

/-- The two nearest grid points for the parent coefficient pair give
admissible comparison points for both signed restriction coefficients. -/
theorem gridError_restriction {h : ℝ} (hh : 0 < h) (u v : ℝ) :
    (gridError h (u + v) + gridError h (u - v)) / 2 ≤
      gridError h u + gridError h v := by
  let a := round (u / h)
  let b := round (v / h)
  have hp := gridError_le_candidate hh (u + v) (a + b)
  have hm := gridError_le_candidate hh (u - v) (a - b)
  push_cast at hp hm
  change _ ≤ (u - h * (a : ℝ)) ^ 2 + (v - h * (b : ℝ)) ^ 2
  nlinarith

/-- Each coefficient lies within half a grid step of a nearest multiple. -/
theorem gridError_le_quarter_sq {h : ℝ} (hh : 0 < h) (x : ℝ) :
    gridError h x ≤ h ^ 2 / 4 := by
  have he := mul_le_mul_of_nonneg_left (abs_sub_round (x / h)) hh.le
  rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh, mul_sub] at he
  have hx : h * (x / h) = x := by field_simp
  rw [hx] at he
  have hs := mul_self_le_mul_self (abs_nonneg _) he
  rw [← sq, sq_abs] at hs
  unfold gridError
  nlinarith

/-- This geometric envelope is summed over all steps at most four times
the magnitude of the coefficient on the queried bit. -/
theorem gridError_restriction_loss_le {h : ℝ} (hh : 0 < h) (u v : ℝ) :
    gridError h u + gridError h v -
      (gridError h (u + v) + gridError h (u - v)) / 2 ≤ h ^ 2 / 2 := by
  have hp : 0 ≤ gridError h (u + v) := sq_nonneg _
  have hm : 0 ≤ gridError h (u - v) := sq_nonneg _
  linarith [gridError_le_quarter_sq hh u, gridError_le_quarter_sq hh v]

/-- A random variable on an integer grid has variance at least the
product of the distances from its mean to the adjacent grid points. -/
theorem grid_slice_variance {ι : Type*} (s : Finset ι) (w : ι → ℝ) (x : ι → ℤ)
    (h a : ℝ) (k : ℤ) (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∑ i ∈ s, w i = 1)
    (ha : ∑ i ∈ s, w i * (h * (x i : ℝ)) = a) :
    (a - h * k) * (h * ((k : ℝ) + 1) - a) ≤
      ∑ i ∈ s, w i * (h * (x i : ℝ) - a) ^ 2 := by
  let c := (a - h * k) * (h * ((k : ℝ) + 1) - a)
  let b := h * (2 * (k : ℝ) + 1) - 2 * a
  have hz : ∑ i ∈ s, w i * (h * (x i : ℝ) - a) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hn, ha, one_mul, sub_self]
  calc
    _ = (∑ i ∈ s, w i) * c + (∑ i ∈ s, w i * (h * (x i : ℝ) - a)) * b := by
      rw [hn, hz]; ring
    _ = ∑ i ∈ s, (w i * c + w i * (h * (x i : ℝ) - a) * b) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hprod : (0 : ℤ) ≤ (x i - k) * (x i - k - 1) := by
        rcases le_or_gt (x i) k with hle | hgt
        · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
        · apply mul_nonneg <;> omega
      have hr : (0 : ℝ) ≤ ((x i : ℝ) - k) * ((x i : ℝ) - k - 1) := by exact_mod_cast hprod
      have hw' := mul_nonneg (hw i hi) (mul_nonneg (sq_nonneg h) hr)
      dsimp [b, c]
      nlinarith

/-- Absorbing the maximum overlap of a subcube boundary with the defect
boundary, after isoperimetry at defect density at most the cube density cubed. -/
theorem cube_defect_absorption {d ρ boundary excess : ℝ}
    (hiso : 6 * d * ρ ≤ boundary)
    (hoverlap : boundary ≤ excess + 2 * (d + 1) * ρ) (hd : 0 ≤ d) :
    (2 * d - 1) * boundary ≤ 3 * d * excess := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ d + 1) (sub_nonneg.mpr hiso),
    mul_nonneg hd (sub_nonneg.mpr hoverlap)]

end FEI
