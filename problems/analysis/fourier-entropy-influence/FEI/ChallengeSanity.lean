module

public import FEI.Challenge
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Normalization and non-vacuity checks for the FEI statement -/

public section

namespace FEI

noncomputable section

variable {n : ℕ}

private theorem pm_sq (b : Bool) : pm b ^ 2 = 1 := by
  cases b <;> norm_num [pm]

/-- Summing the Walsh kernel over all subsets gives a product over coordinates. -/
private theorem walsh_kernel (x y : Fin n → Bool) :
    ∑ S : Finset (Fin n), chi S x * chi S y = if x = y then (2 : ℝ) ^ n else 0 := by
  classical
  calc
    _ = ∏ i, (1 + pm (x i) * pm (y i)) := by
      simp only [Finset.prod_one_add, Finset.powerset_univ, chi, Finset.prod_mul_distrib]
    _ = _ := by
      split_ifs with h
      · subst y
        norm_num [← sq, pm_sq]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hx : x i <;> cases hy : y i <;> simp_all [pm]

private theorem fourier_inversion (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    ∑ S, fourierCoeff f S * chi S x = pm (f x) := by
  classical
  calc
    _ = (1 / (2 : ℝ) ^ n) * ∑ y, pm (f y) * ∑ S, chi S y * chi S x := by
      simp only [fourierCoeff, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [walsh_kernel, mul_ite, mul_zero]
      simp [mul_comm (pm (f x))]

/-- Pairing any Walsh expansion with `pm ∘ f` picks out its Fourier coefficients. -/
private theorem fourier_pairing (f : (Fin n → Bool) → Bool) (a : Finset (Fin n) → ℝ) :
    ∑ S, a S * fourierCoeff f S =
      (1 / (2 : ℝ) ^ n) * ∑ x, pm (f x) * ∑ S, a S * chi S x := by
  simp only [fourierCoeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun S _ ↦ by ring

/-- Parseval's identity for the sign encoding of a Boolean function. -/
theorem parseval (f : (Fin n → Bool) → Bool) : ∑ S, (fourierCoeff f S) ^ 2 = 1 := by
  simp only [sq, fourier_pairing, fourier_inversion]
  simp [← sq, pm_sq]

private theorem chi_flipAt (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :
    chi S (flipAt x i) = if i ∈ S then -chi S x else chi S x := by
  have h (j : Fin n) : pm (flipAt x i j) = (if j = i then (-1 : ℝ) else 1) * pm (x j) := by
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp [flipAt, hx, pm]
    · simp [flipAt, hj]
  simp only [chi, h, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  split_ifs <;> simp

/-- The half-difference across an edge retains exactly the characters containing `i`. -/
private theorem fourier_derivative (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (i : Fin n) :
    ∑ S, (if i ∈ S then fourierCoeff f S else 0) * chi S x =
      (pm (f x) - pm (f (flipAt x i))) / 2 := by
  rw [← fourier_inversion f x, ← fourier_inversion f (flipAt x i),
    ← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  rw [chi_flipAt]
  split_ifs <;> ring

/-- Coordinate influence is the Fourier mass on subsets containing that coordinate. -/
theorem coordInfluence_eq_sum (f : (Fin n → Bool) → Bool) (i : Fin n) :
    coordInfluence f i = ∑ S, if i ∈ S then (fourierCoeff f S) ^ 2 else 0 := by
  have edge (b c : Bool) : pm b * ((pm b - pm c) / 2) = if b ≠ c then 1 else 0 := by
    cases b <;> cases c <;> norm_num [pm]
  symm
  calc
    _ = ∑ S, (if i ∈ S then fourierCoeff f S else 0) * fourierCoeff f S := by
      simp_rw [ite_mul, zero_mul, sq]
    _ = _ := by
      rw [fourier_pairing]
      simp_rw [fourier_derivative, edge]
      rw [Finset.sum_boole, coordInfluence]

theorem totalInfluence_eq_spectralInfluence (f : (Fin n → Bool) → Bool) :
    totalInfluence f = spectralInfluence f := by
  simp only [totalInfluence, coordInfluence_eq_sum, spectralInfluence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp

/-- Boolean AND on the two-dimensional cube. -/
@[expose] def and2 (x : Fin 2 → Bool) : Bool := x 0 && x 1

private theorem fourierCoeff_and2_sq (S : Finset (Fin 2)) :
    (fourierCoeff and2 S) ^ 2 = 1 / 4 := by
  rw [fourierCoeff, ← (finTwoArrowEquiv Bool).symm.sum_comp,
    Fintype.sum_prod_type]
  have subsets : ∀ T : Finset (Fin 2), T = ∅ ∨ T = {0} ∨ T = {1} ∨ T = {0, 1} := by decide
  rcases subsets S with rfl | rfl | rfl | rfl <;>
    norm_num [Fintype.sum_bool, finTwoArrowEquiv, and2, chi, pm]

theorem fourierEntropy_and2 : fourierEntropy and2 = 2 := by
  have log_quarter : Real.logb 2 (1 / 4) = -2 := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.logb_inv, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  simp only [fourierEntropy, fourierCoeff_and2_sq]
  norm_num [entropyTerm, log_quarter, Fintype.card_finset]

theorem totalInfluence_and2 : totalInfluence and2 = 1 := by
  have edges : ∀ i : Fin 2,
      (Finset.univ.filter fun x ↦ and2 x ≠ and2 (flipAt x i)).card = 2 := by decide
  norm_num [totalInfluence, coordInfluence, edges]

/-- Every uniform FEI bound has constant at least two. -/
theorem two_le_of_fei_bound {C : ℝ}
    (h : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), fourierEntropy f ≤ C * totalInfluence f) :
    2 ≤ C := by
  simpa [fourierEntropy_and2, totalInfluence_and2] using h 2 and2

@[expose] def constFalse : (Fin n → Bool) → Bool := fun _ ↦ false

theorem totalInfluence_constFalse : totalInfluence (constFalse (n := n)) = 0 := by
  simp [totalInfluence, coordInfluence, constFalse]

theorem fourierEntropy_constFalse : fourierEntropy (constFalse (n := n)) = 0 := by
  have dc : fourierCoeff (constFalse (n := n)) ∅ = 1 := by
    simp [fourierCoeff, constFalse, pm, chi]
  have rest : ∑ S ∈ (Finset.univ.erase ∅), (fourierCoeff (constFalse (n := n)) S) ^ 2 = 0 := by
    have h := (Finset.univ.sum_erase_add (fun S ↦ (fourierCoeff (constFalse (n := n)) S) ^ 2)
      (Finset.mem_univ ∅)).trans (parseval constFalse)
    simpa only [dc, one_pow, add_eq_right] using h
  apply Finset.sum_eq_zero
  intro S _
  by_cases h : S = ∅
  · simp [h, dc, entropyTerm]
  · have mass := (Finset.sum_eq_zero_iff_of_nonneg (fun T _ ↦ sq_nonneg _)).mp rest S
      (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    simp [mass, entropyTerm]

end

end FEI
