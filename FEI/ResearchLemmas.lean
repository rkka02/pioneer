module

public import FEI.ChallengeSanity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

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

/-- Squared error in rounding one Walsh coefficient to the grid of step 2⁻ᵐ. -/
noncomputable def gridLayer (m : ℕ) (x : ℝ) : ℝ :=
  gridError 1 ((2 : ℝ)^m * x) / ((2 : ℝ)^m)^2

theorem gridLayer_eq (m : ℕ) (x : ℝ) :
    gridLayer m x = gridError ((2 : ℝ)^m)⁻¹ x := by
  simp only [gridLayer, gridError, div_one, one_mul, div_inv_eq_mul]
  rw [mul_comm x ((2 : ℝ)^m)]
  field_simp

/-- At dimension n all further grid errors vanish for Boolean Walsh coefficients. -/
noncomputable def gridSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, gridLayer m x

private theorem unit_grid_reflect (z : ℤ) (x : ℝ) :
    gridError 1 ((z : ℝ) - x) = gridError 1 x := by
  have step (y : ℝ) : gridError 1 ((z : ℝ) - y) ≤ gridError 1 y := by
    have h := gridError_le_candidate (h := 1) (by norm_num) ((z : ℝ) - y) (z - round y)
    push_cast at h
    simpa only [gridError, div_one, one_mul, sub_sub_sub_cancel_left, sub_sq_comm] using h
  exact le_antisymm (step x) (by simpa using step ((z : ℝ) - x))

private theorem gridSum_reflect (n : ℕ) (x : ℝ) : gridSum n (1-x) = gridSum n x := by
  apply Finset.sum_congr rfl
  intro m _
  unfold gridLayer
  rw [mul_sub, mul_one]
  have h := unit_grid_reflect ((2 : ℤ)^m) ((2 : ℝ)^m*x)
  push_cast at h
  rw [h]

private theorem gridSum_nonneg (n : ℕ) (x : ℝ) : 0 ≤ gridSum n x := by
  unfold gridSum gridLayer gridError
  positivity

private theorem gridSum_succ (n : ℕ) (x : ℝ) :
    gridSum (n+1) x = gridError 1 x + gridSum n (2*x)/4 := by
  rw [gridSum, Finset.sum_range_succ', gridSum, div_eq_mul_inv, Finset.sum_mul, add_comm]
  simp only [gridLayer, pow_zero, one_mul, one_pow, div_one]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [pow_succ, mul_assoc, mul_pow]
  ring

private theorem gridSum_small (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hh : x ≤ 1/2) :
    gridSum (n+1) x = x^2 + gridSum n (2*x)/4 := by
  rw [gridSum_succ]
  congr 1
  rcases lt_or_eq_of_le hh with h | rfl
  · have hr : round x = 0 := round_eq_zero_iff.mpr ⟨by linarith, h⟩
    simp [gridError, hr]
  · norm_num [gridError, round_eq_iff, round_two_inv]

private theorem gridSum_le_variance (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    gridSum n x ≤ x*(1-x) := by
  induction n generalizing x with
  | zero => simpa [gridSum] using mul_nonneg hx (sub_nonneg.mpr hx')
  | succ n ih =>
    have small (y : ℝ) (hy : 0 ≤ y) (h : y ≤ 1/2) : gridSum (n+1) y ≤ y*(1-y) := by
      rw [gridSum_small n hy h]
      have v := ih (x := 2*y) (by linarith) (by linarith)
      nlinarith
    by_cases h : x ≤ 1/2
    · exact small _ hx h
    · have h' := small (1-x) (by linarith) (by linarith)
      rw [gridSum_reflect] at h'
      nlinarith

private noncomputable def amplitudeEntropy (x : ℝ) : ℝ := -x^2 * Real.logb 2 x

private theorem amplitudeEntropy_double {x : ℝ} (hx : x ≠ 0) :
    amplitudeEntropy x = x^2 + amplitudeEntropy (2*x)/4 := by
  simp only [amplitudeEntropy, Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) hx,
    Real.logb_self_eq_one (by norm_num : 1 < (2:ℝ))]
  ring

private theorem amplitudeEntropy_eq (x : ℝ) :
    entropyTerm (x^2)/2 = amplitudeEntropy |x| := by
  by_cases hx : x = 0
  · simp [hx, amplitudeEntropy, entropyTerm]
  · rw [entropyTerm, ite_eq_right (pow_ne_zero _ hx), Real.logb_pow, amplitudeEntropy,
      Real.logb_abs, sq_abs]
    push_cast
    ring

private theorem variance_le_amplitudeEntropy {x : ℝ} (h : 1/2 ≤ x) (h' : x ≤ 1) :
    x*(1-x) ≤ amplitudeEntropy x := by
  have hx : 0 < x := by linarith
  have ha : 0 ≤ 2 - x⁻¹ := sub_nonneg.mpr ((inv_le_iff_one_le_mul₀ hx).mpr (by linarith))
  have hb : 0 ≤ x⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hx).mpr h')
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) (show (2:ℝ) ∈ Set.Ioi 0 by norm_num)
    ha hb (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  rw [show (2-x⁻¹)*1+(x⁻¹-1)*2 = x⁻¹ by ring, Real.log_inv] at hc
  have hl : x⁻¹ - 1 ≤ - Real.logb 2 x := by
    rw [Real.logb, ← neg_div, le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
    exact hc
  have hmul := mul_le_mul_of_nonneg_left hl (sq_nonneg x)
  have hi : x*x⁻¹=1 := mul_inv_cancel₀ hx.ne'
  unfold amplitudeEntropy
  nlinarith [show x^2*x⁻¹=x by linear_combination x*hi]

private theorem gridSum_le_amplitudeEntropy (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (h' : x ≤ 1) :
    gridSum n x ≤ amplitudeEntropy x := by
  have zero_case (k : ℕ) : gridSum k 0 = 0 := by simp [gridSum, gridLayer, gridError]
  induction n generalizing x with
  | zero =>
    simp only [gridSum, Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (sq_nonneg x))
      (Real.logb_nonpos (by norm_num) hx h')
  | succ n ih =>
    rcases eq_or_lt_of_le hx with rfl | hp
    · simp [zero_case, amplitudeEntropy]
    by_cases h : x ≤ 1/2
    · rw [gridSum_small n hx h, amplitudeEntropy_double hp.ne']
      linarith [ih (x := 2*x) (by linarith) (by linarith)]
    · exact (gridSum_le_variance _ hx h').trans (variance_le_amplitudeEntropy (by linarith) h')

private theorem amplitudeEntropy_sub_mass_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (h' : x ≤ 1)
    (hgrid : x = 0 ∨ 1 ≤ (2:ℝ)^n*x) : amplitudeEntropy x - x^2 ≤ gridSum n x := by
  rcases hgrid with rfl | hg
  · simp [amplitudeEntropy, gridSum, gridLayer, gridError]
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, one_mul] at hg
    have h : x = 1 := le_antisymm h' hg
    simp [h, amplitudeEntropy, gridSum]
  | succ n ih =>
    have hp : 0 < x := lt_of_le_of_ne hx (by intro e; rw [← e, mul_zero] at hg; linarith)
    by_cases h : x ≤ 1/2
    · rw [gridSum_small n hx h, amplitudeEntropy_double hp.ne']
      rw [pow_succ, mul_assoc] at hg
      have v := ih (x := 2*x) (by linarith) (by linarith) hg
      nlinarith
    · have hm := Real.logb_le_logb_of_le (b := 2) (by norm_num)
          (x := (2:ℝ)⁻¹) (by norm_num) (y := x) (by linarith)
      rw [Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at hm
      have t := mul_le_mul_of_nonneg_left hm (sq_nonneg x)
      unfold amplitudeEntropy
      linarith [gridSum_nonneg n.succ x]


/-- The integer numerator of every normalized Boolean Walsh coefficient. -/
theorem fourierCoeff_dyadic {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
    ∃ z : ℤ, (2:ℝ)^n * fourierCoeff f S = z := by
  let signInt (b : Bool) : ℤ := if b then -1 else 1
  have castSign (b : Bool) : ((signInt b : ℤ) : ℝ) = pm b := by
    cases b <;> norm_num [signInt, pm]
  refine ⟨∑ x : Fin n → Bool, signInt (f x) * ∏ i ∈ S, signInt (x i), ?_⟩
  simp only [fourierCoeff, chi, Int.cast_sum, Int.cast_mul, Int.cast_prod, castSign]
  field_simp

/-- All terms beyond the finite grid sum are zero on a Boolean spectrum. -/
theorem gridLayer_tail_zero {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (k : ℕ) : gridLayer (k+n) |fourierCoeff f S| = 0 := by
  obtain ⟨z, hz⟩ := fourierCoeff_dyadic f S
  have h : (2:ℝ)^n * |fourierCoeff f S| = ((|z| : ℤ) : ℝ) := by
    simpa [abs_mul, abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) n)] using congrArg abs hz
  have hc : (2:ℝ)^k * ((|z| : ℤ) : ℝ) = (((2:ℤ)^k * |z| : ℤ) : ℝ) := by push_cast; rfl
  unfold gridLayer
  rw [pow_add, mul_assoc, h, hc]
  simp only [gridError, div_one, one_mul, round_intCast, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]

private theorem fourierCoeff_abs_le_one {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) : |fourierCoeff f S| ≤ 1 := by
  have hs := Finset.single_le_sum (f := fun T ↦ (fourierCoeff f T)^2)
    (fun T (_ : T ∈ Finset.univ) ↦ sq_nonneg _) (Finset.mem_univ S)
  rw [parseval] at hs
  nlinarith [sq_abs (fourierCoeff f S)]

private theorem amplitudeEntropy_le_missing_mass {x : ℝ} (h : 0 ≤ x) (h' : x ≤ 1) :
    amplitudeEntropy x ≤ 1 - x^2 := by
  rcases eq_or_lt_of_le h with rfl | hp
  · norm_num [amplitudeEntropy]
  have p : 0 < x^2 := sq_pos_of_pos hp
  have hm := Real.log_le_sub_one_of_pos (inv_pos.mpr p)
  rw [Real.log_inv, Real.log_pow] at hm
  have hh := mul_le_mul_of_nonneg_left hm p.le
  have eq : x^2*(x^2)⁻¹=1 := mul_inv_cancel₀ p.ne'
  have ln2 : (1:ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  have v : 0 ≤ 1-x^2 := by nlinarith [mul_nonneg h (sub_nonneg.mpr h')]
  have big := mul_le_mul_of_nonneg_right ln2 v
  unfold amplitudeEntropy Real.logb
  rw [← mul_div_assoc, div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  nlinarith

/-- Sum over the squared rounding errors on all dyadic grids of step at most one. -/
noncomputable def fourierGridEnergy {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S, gridSum n |fourierCoeff f S|

/-- The dyadic grid energy approximates half the frozen entropy from below. -/
theorem fourierGridEnergy_bounds {n : ℕ} (f : (Fin n → Bool) → Bool) :
    fourierEntropy f / 2 - 2 * totalInfluence f ≤ fourierGridEnergy f ∧
    fourierGridEnergy f ≤ fourierEntropy f / 2 := by
  classical
  let a (S : Finset (Fin n)) := fourierCoeff f S
  have sumH : fourierEntropy f / 2 = ∑ S, amplitudeEntropy |a S| := by
    rw [fourierEntropy, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    exact amplitudeEntropy_eq _
  rw [sumH]
  constructor
  · let rest := (Finset.univ : Finset (Finset (Fin n))).erase ∅
    have mass : ∑ S ∈ rest, (a S)^2 + (a ∅)^2 = 1 :=
      (Finset.univ.sum_erase_add (fun S ↦ (a S)^2) (Finset.mem_univ ∅)).trans (parseval f)
    have splitI : ∑ S ∈ rest, (S.card : ℝ) * (a S)^2 = totalInfluence f := by
      rw [totalInfluence_eq_spectralInfluence]
      simp [rest, a, spectralInfluence]
    have inf : ∑ S ∈ rest, (a S)^2 ≤ totalInfluence f := by
      rw [← splitI]
      apply Finset.sum_le_sum
      intro S hS
      have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)
      exact le_mul_of_one_le_left (sq_nonneg _) (by exact_mod_cast pos)
    have others : ∑ S ∈ rest, (amplitudeEntropy |a S| - gridSum n |a S|) ≤ ∑ S ∈ rest, (a S)^2 := by
      apply Finset.sum_le_sum
      intro S _
      obtain ⟨z, hz⟩ := fourierCoeff_dyadic f S
      have hgrid : |a S| = 0 ∨ 1 ≤ (2:ℝ)^n * |a S| := by
        have h : (2:ℝ)^n * |a S| = ((|z| : ℤ) : ℝ) := by
          simpa [a, abs_mul, abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) n)] using congrArg abs hz
        by_cases zz : z = 0
        · left; simp [zz] at h; simpa using h
        · right; rw [h]; exact_mod_cast (show (1:ℤ) ≤ |z| by have := abs_pos.mpr zz; omega)
      have hs := amplitudeEntropy_sub_mass_le n (abs_nonneg (a S)) (fourierCoeff_abs_le_one f S) hgrid
      rw [sq_abs] at hs
      linarith
    have empty := amplitudeEntropy_le_missing_mass (abs_nonneg (a ∅)) (fourierCoeff_abs_le_one f ∅)
    rw [sq_abs] at empty
    have hs := Finset.univ.sum_erase_add (fun S ↦ amplitudeEntropy |a S| - gridSum n |a S|)
      (Finset.mem_univ ∅)
    change (∑ S ∈ rest, _) + _ = _ at hs
    rw [Finset.sum_sub_distrib] at others
    simp only [Finset.sum_sub_distrib] at hs
    change _ ≤ ∑ S, gridSum n |a S|
    linarith [gridSum_nonneg n |a ∅|]
  · exact Finset.sum_le_sum fun S _ ↦ gridSum_le_amplitudeEntropy n (abs_nonneg _) (fourierCoeff_abs_le_one f S)

/-- A dimension-independent upper bound on the signed-grid energy is equivalent to FEI. -/
theorem fei_iff_grid_bound : FourierEntropyInfluenceConjecture ↔
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      fourierGridEnergy f ≤ C * totalInfluence f := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C/2, by positivity, fun n f ↦ (fourierGridEnergy_bounds f).2.trans (by linarith [h n f])⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨2*C+4, by positivity, fun n f ↦ by linarith [(fourierGridEnergy_bounds f).1, h n f]⟩


/-- Entropy of a two-outcome measurement whose rare outcome has probability
at most four times the density of a phase feature. Both sides are in nats. -/
theorem binary_entropy_four_mass {u x : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/2)
    (hx : 0 ≤ x) (hxu : x ≤ 4*u) : Real.binEntropy x ≤ -(4*u) * Real.log u := by
  rcases eq_or_lt_of_le hu with rfl | hp
  · have := le_antisymm (by linarith : x ≤ 0) hx
    simp [this]
  have ln4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num)]
    ring
  by_cases hsmall : u ≤ 1/8
  · have mono := Real.binEntropy_strictMonoOn.monotoneOn
      (show x ∈ Set.Icc (0:ℝ) 2⁻¹ from ⟨hx, by norm_num; linarith⟩)
      (show 4*u ∈ Set.Icc (0:ℝ) 2⁻¹ from ⟨by positivity, by norm_num; linarith⟩) hxu
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub (4*u)] at mono
    have htail := Real.negMulLog_le_one_sub_self (x := 1-4*u) (by linarith)
    rw [Real.negMulLog, Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hp.ne', ln4] at mono
    nlinarith [mul_nonneg hp.le (show 0 ≤ 2*Real.log 2 - 1 by linarith [Real.log_two_gt_d9])]
  · have hlog (c : ℝ) (hc : u ≤ c⁻¹) : Real.log c ≤ -Real.log u := by
      have h := Real.log_le_log hp hc
      rw [Real.log_inv] at h
      linarith
    by_cases h : u ≤ 1/4
    · have h4 := hlog 4 (by simpa using h)
      rw [ln4] at h4
      nlinarith [mul_nonneg (by linarith : 0 ≤ 4*u) (sub_nonneg.mpr h4),
        mul_nonneg (by linarith : 0 ≤ 8*u-1) (Real.log_nonneg (by norm_num : (1:ℝ)≤2)),
        Real.binEntropy_le_log_two (p := x)]
    · have h2 := hlog 2 (by simpa using hu')
      nlinarith [mul_nonneg (by linarith : 0 ≤ 4*u) (sub_nonneg.mpr h2),
        mul_nonneg (by linarith : 0 ≤ 4*u-1) (Real.log_nonneg (by norm_num : (1:ℝ)≤2)),
        Real.binEntropy_le_log_two (p := x)]

/-- The smaller eigenvalue of a trace-one two-state mixture is bounded by
its smaller measurement probability in a basis containing the common state. -/
theorem binary_mixture_small_root {d θ w : ℝ} (hd : 0 ≤ d)
    (ht : 0 ≤ θ) (ht' : θ ≤ 1) (hw : w ≤ 1/2)
    (hdet : w*(1-w) = d*(1-d)*θ) : w ≤ d*θ := by
  have hq : d*θ ≤ d := mul_le_of_le_one_right hd ht'
  by_contra! h
  have order := mul_pos (sub_pos.mpr h) (show 0 < 1-w-d*θ by linarith)
  nlinarith [mul_nonneg (mul_nonneg hd ht) (sub_nonneg.mpr hq)]

/-- Entropy estimate for the two nonzero squared singular values of a
rank-two sign kernel with projective row and column densities μ and δ. -/
theorem rank_two_entropy_scalar {μ δ w : ℝ} (hm : 0 ≤ μ) (hm' : μ ≤ 1/2)
    (hd : 0 ≤ δ) (hd' : δ ≤ 1/2) (hw : 0 ≤ w) (hw' : w ≤ 1/2)
    (hdet : w*(1-w) = 4*μ*(1-μ)*δ*(1-δ)) :
    Real.binEntropy w ≤ -(4*(μ*δ))*Real.log (μ*δ) := by
  have ht : 0 ≤ 4*μ*(1-μ) := mul_nonneg (by positivity) (by linarith)
  have ht' : 4*μ*(1-μ) ≤ 1 := by nlinarith [sq_nonneg (1-2*μ)]
  have h := binary_mixture_small_root hd ht ht' hw' (by rw [hdet]; ring)
  apply binary_entropy_four_mass (mul_nonneg hm hd) (by nlinarith [mul_nonneg hm (sub_nonneg.mpr hd')]) hw
  nlinarith [mul_nonneg (sq_nonneg μ) hd]

end FEI
