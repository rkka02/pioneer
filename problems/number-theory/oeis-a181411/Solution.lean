import OMAStatements.S_oeis_a181411
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic


/-!
# Asymptotic growth of OEIS A181411

Václav Kotesovec's conjecture is that the binomial sum of `σ₁(n + k)` is
asymptotic to `(π² / 4) * n * 2^n`. Source: https://oeis.org/A181411.

The proof approximates the summatory divisor function by a quadratic with a finite
reciprocal-square coefficient. Discrete summation by parts bounds the binomial
average of the approximation error by its uniform bound times the total variation
of the weights. The binomial mean and the Basel sum give the limiting constant.
-/

namespace OEISA181411

open Finset Filter Asymptotics
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta Topology

section DivisorSums

/-- Summatory sum of divisors. -/
noncomputable def divisorPrefix (m : ℕ) : ℝ := ∑ j ∈ Ioc 0 m, (σ 1 j : ℝ)

/-- Finite reciprocal-square sum used for the leading coefficient. -/
noncomputable def reciprocalSquares (M : ℕ) : ℝ := ∑ d ∈ Ioc 0 M, 1 / (d : ℝ) ^ 2

lemma sum_Ioc_nat_real (q : ℕ) :
    (∑ k ∈ Ioc 0 q, (k : ℝ)) = (q : ℝ) * (q + 1 : ℝ) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le q), ih]
    push_cast
    ring

lemma divisorPrefix_triangle (m : ℕ) :
    divisorPrefix m = ∑ d ∈ Ioc 0 m, ((m / d : ℕ) : ℝ) * ((m / d : ℕ) + 1 : ℝ) / 2 := by
  rw [divisorPrefix, ← Nat.cast_sum, ← ArithmeticFunction.zeta_mul_pow_eq_sigma,
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum, Nat.cast_sum]
  refine sum_congr rfl fun d hd => ?_
  have hd0 := (mem_Ioc.mp hd).1
  simp only [ArithmeticFunction.zeta_apply, if_neg hd0.ne', one_mul, Nat.cast_sum,
    ArithmeticFunction.pow_one_eq_id, ArithmeticFunction.id_apply]
  exact sum_Ioc_nat_real _

lemma divisorPrefix_triangle_to {m M : ℕ} (hm : m ≤ M) :
    divisorPrefix m = ∑ d ∈ Ioc 0 M, ((m / d : ℕ) : ℝ) * ((m / d : ℕ) + 1 : ℝ) / 2 := by
  rw [divisorPrefix_triangle]
  refine Finset.sum_subset (fun d hd => mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1, (mem_Ioc.mp hd).2.trans hm⟩) ?_
  intro d hd hdm
  have hd0 := (mem_Ioc.mp hd).1
  have hlt : m < d := lt_of_not_ge (fun h => hdm (mem_Ioc.mpr ⟨hd0, h⟩))
  simp [Nat.div_eq_of_lt hlt]

lemma abs_triangle_div_error {m d : ℕ} (hd : 0 < d) :
    |((m / d : ℕ) : ℝ) * ((m / d : ℕ) + 1 : ℝ) / 2 -
      ((m : ℝ) / d) ^ 2 / 2| ≤ 2 * ((m : ℝ) / d) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / d := Nat.cast_div_le
  have hhi : (m : ℝ) / d < ((m / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdp).mpr
    exact_mod_cast (show m < (m / d + 1) * d by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ m hd)
  generalize hq : ((m / d : ℕ) : ℝ) = q at hlo hhi ⊢
  generalize ht : (m : ℝ) / d = t at hlo hhi ⊢
  have hq0 : 0 ≤ q := hq ▸ Nat.cast_nonneg _
  have ht0 : 0 ≤ t := hq0.trans hlo
  have h₁ := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ t + q from add_nonneg ht0 hq0)
  have h₂ := mul_nonneg (show 0 ≤ 1 - (t - q) by linarith) (show 0 ≤ t + q from add_nonneg ht0 hq0)
  rw [abs_le]
  constructor <;> nlinarith

/-- The same finite zeta approximation can be used uniformly up to index `M`. -/
theorem divisorPrefix_error {m M : ℕ} (hm : m ≤ M) :
    |divisorPrefix m - (m : ℝ) ^ 2 / 2 * reciprocalSquares M| ≤
      2 * (m : ℝ) * (1 + Real.log M) := by
  rw [divisorPrefix_triangle_to hm, reciprocalSquares, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Ioc 0 M, |((m / d : ℕ) : ℝ) * ((m / d : ℕ) + 1 : ℝ) / 2 -
        ((m : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 M, 2 * ((m : ℝ) / d) := by
      refine sum_le_sum fun d hd => ?_
      have hd0 := (mem_Ioc.mp hd).1
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      have heq : (m : ℝ) ^ 2 / 2 * (1 / (d : ℝ) ^ 2) = ((m : ℝ) / d) ^ 2 / 2 := by
        field_simp
      rw [heq]
      exact abs_triangle_div_error hd0
    _ = 2 * (m : ℝ) * (harmonic M : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum, mul_sum]
      have hset : Ioc 0 M = Icc 1 M := by ext d; simp; omega
      rw [hset]
      refine sum_congr rfl fun d hd => ?_
      simp only [Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (by positivity)

lemma divisorPrefix_succ (m : ℕ) :
    divisorPrefix (m + 1) = divisorPrefix m + (σ 1 (m + 1) : ℝ) := by
  unfold divisorPrefix
  rw [sum_Ioc_succ_top (Nat.zero_le m)]

end DivisorSums

section BinomialWeights

/-- Weights of the symmetric binomial distribution on `0, …, n`. -/
noncomputable def binWeight (n k : ℕ) : ℝ := (n.choose k : ℝ) / (2 : ℝ) ^ n

lemma binWeight_nonneg (n k : ℕ) : 0 ≤ binWeight n k := by unfold binWeight; positivity

lemma binWeight_symm {n k : ℕ} (hk : k ≤ n) : binWeight n (n - k) = binWeight n k := by
  simp only [binWeight, Nat.choose_symm hk]

lemma binWeight_le_succ_of_lt_half (n : ℕ) {k : ℕ} (hk : k < n / 2) :
    binWeight n k ≤ binWeight n (k + 1) :=
  div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_succ_of_lt_half_left hk) (by positivity)

lemma binWeight_succ_le_of_half_le (n : ℕ) {k : ℕ} (hk : n / 2 ≤ k) (hkn : k < n) :
    binWeight n (k + 1) ≤ binWeight n k := by
  rcases eq_or_lt_of_le hk with hkeq | hk'
  · subst k
    have h := Nat.choose_le_middle (n / 2 + 1) n
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
  · have hlo : n - (k + 1) < n / 2 := by omega
    have h := binWeight_le_succ_of_lt_half n hlo
    rw [show n - (k + 1) + 1 = n - k by omega,
      binWeight_symm (by omega : k + 1 ≤ n), binWeight_symm hkn.le] at h
    exact h

/-- The sum of the absolute first differences, including two endpoints of the support. -/
theorem binWeight_totalVariation (n : ℕ) :
    binWeight n 0 + (∑ k ∈ range n, |binWeight n (k + 1) - binWeight n k|) + binWeight n n =
      2 * binWeight n (n / 2) := by
  have hhalf : n / 2 ≤ n := Nat.div_le_self _ _
  rw [← sum_range_add_sum_Ico (fun k => |binWeight n (k + 1) - binWeight n k|) hhalf]
  have h₁ : (∑ k ∈ range (n / 2), |binWeight n (k + 1) - binWeight n k|) =
      binWeight n (n / 2) - binWeight n 0 := by
    rw [← Finset.sum_range_sub (binWeight n) (n / 2)]
    exact sum_congr rfl fun k hk => abs_of_nonneg (sub_nonneg.mpr (binWeight_le_succ_of_lt_half n (mem_range.mp hk)))
  have h₂ : (∑ k ∈ Ico (n / 2) n, |binWeight n (k + 1) - binWeight n k|) =
      binWeight n (n / 2) - binWeight n n := by
    calc
      _ = ∑ k ∈ Ico (n / 2) n, (binWeight n k - binWeight n (k + 1)) := by
        refine sum_congr rfl fun k hk => ?_
        obtain ⟨hl, hu⟩ := mem_Ico.mp hk
        rw [abs_of_nonpos (sub_nonpos.mpr (binWeight_succ_le_of_half_le n hl hu)), neg_sub]
      _ = _ := by
        rw [sum_Ico_eq_sub _ hhalf]
        have htel (j : ℕ) : (∑ k ∈ range j, (binWeight n k - binWeight n (k + 1))) =
            -(binWeight n j - binWeight n 0) := by
          simp_rw [← neg_sub (binWeight n (_ + 1)) (binWeight n _), sum_neg_distrib, Finset.sum_range_sub]
        rw [htel, htel]
        ring
  rw [h₁, h₂]
  ring

lemma central_binWeight_square (m : ℕ) : ((m : ℝ) + 1) * (binWeight (2 * m) m) ^ 2 ≤ 1 := by
  induction m with
  | zero => norm_num [binWeight]
  | succ m ih =>
    have hc : ((m : ℝ) + 1) * ((m + 1).centralBinom : ℝ) =
        2 * (2 * (m : ℝ) + 1) * (m.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hp : 0 < (2 : ℝ) ^ (2 * m) := by positivity
    have hr : binWeight (2 * (m + 1)) (m + 1) =
        ((2 * (m : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * binWeight (2 * m) m := by
      simp only [binWeight, ← Nat.centralBinom_eq_two_mul_choose]
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
      have hmp : 0 < (m : ℝ) + 1 := by positivity
      field_simp
      linear_combination hc
    have hrle : ((m : ℝ) + 2) * ((2 * (m : ℝ) + 1) / (2 * ((m : ℝ) + 1))) ^ 2 ≤
        (m : ℝ) + 1 := by
      have hden : 0 < (2 * ((m : ℝ) + 1)) ^ 2 := by positivity
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    push_cast
    rw [hr, mul_pow, show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hrle (sq_nonneg _)).trans ih

lemma binWeight_bound (n k : ℕ) :
    binWeight n k ≤ 4 / Real.sqrt ((n : ℝ) + 1) := by
  let m := (n + 1) / 2
  have hnm : n ≤ 2 * m := by dsimp [m]; omega
  have hmn : 2 * m ≤ n + 1 := by dsimp [m]; omega
  have hchoose : (n.choose k : ℝ) ≤ ((2 * m).choose m : ℝ) := by
    exact_mod_cast (Nat.choose_le_choose k hnm).trans (Nat.choose_le_centralBinom k m)
  have hden : (2 : ℝ) ^ (2 * m) ≤ 2 * (2 : ℝ) ^ n := by
    simpa [pow_succ, mul_comm] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmn
  have hb : binWeight n k ≤ 2 * binWeight (2 * m) m := by
    unfold binWeight
    calc
      _ ≤ ((2 * m).choose m : ℝ) / (2 : ℝ) ^ n := by gcongr
      _ ≤ _ := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ ((2 * m).choose m : ℝ) by positivity)
  have hmle : (n : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1) := by exact_mod_cast (show n + 1 ≤ 2 * (m + 1) by omega)
  have hs : ((n : ℝ) + 1) * (binWeight (2 * m) m) ^ 2 ≤ 2 := by
    have := mul_le_mul_of_nonneg_right hmle (sq_nonneg (binWeight (2 * m) m))
    nlinarith [central_binWeight_square m]
  have hsqrt : 0 < Real.sqrt ((n : ℝ) + 1) := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hsmall : binWeight (2 * m) m ≤ 2 / Real.sqrt ((n : ℝ) + 1) := by
    rw [le_div_iff₀ hsqrt]
    have hprod : (binWeight (2 * m) m * Real.sqrt ((n : ℝ) + 1)) ^ 2 ≤ 2 := by
      rw [mul_pow, hsq, mul_comm]
      exact hs
    nlinarith
  -- Avoid a parity split: the fixed factor `2` from the first comparison is harmless.
  apply le_trans hb
  convert mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2) using 1
  ring

lemma binWeight_mass (n : ℕ) : ∑ k ∈ range (n + 1), binWeight n k = 1 := by
  simp only [binWeight, ← sum_div, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (by positivity)

lemma binWeight_mean (n : ℕ) : ∑ k ∈ range (n + 1), binWeight n k * (k : ℝ) = (n : ℝ) / 2 := by
  have hsymm := Finset.sum_range_reflect (fun k => binWeight n k * (k : ℝ)) (n + 1)
  simp only [Nat.add_sub_cancel] at hsymm
  have hsymm' : (∑ k ∈ range (n + 1), binWeight n k * ((n : ℝ) - k)) =
      ∑ k ∈ range (n + 1), binWeight n k * (k : ℝ) := by
    rw [← hsymm]
    refine sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.le_of_lt_succ <| mem_range.mp hk
    rw [binWeight_symm hkn, Nat.cast_sub hkn]
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, binWeight_mass, one_mul] at hsymm'
  linarith

end BinomialWeights

/-- Summation by parts with both endpoints retained. -/
lemma sum_weighted_firstDifference (w F : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ range (n + 1), w k * (F (k + 1) - F k)) =
      w n * F (n + 1) - w 0 * F 0 -
        ∑ k ∈ range n, (w (k + 1) - w k) * F (k + 1) := by
  induction n with
  | zero =>
    simp
    ring
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- Bounding every prefix error bounds its binomial average by total variation. -/
theorem binWeight_sum_error (F : ℕ → ℝ) (n : ℕ) (C : ℝ)
    (hC : ∀ k ≤ n + 1, |F k| ≤ C) :
    |∑ k ∈ range (n + 1), binWeight n k * (F (k + 1) - F k)| ≤
      C * (2 * binWeight n (n / 2)) := by
  rw [sum_weighted_firstDifference, ← binWeight_totalVariation]
  have hsum : |∑ k ∈ range n, (binWeight n (k + 1) - binWeight n k) * F (k + 1)| ≤
      C * (∑ k ∈ range n, |binWeight n (k + 1) - binWeight n k|) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC (k + 1) (by have := mem_range.mp hk; omega)) (abs_nonneg _)
  have hend (k j : ℕ) (hj : j ≤ n + 1) : |binWeight n k * F j| ≤ C * binWeight n k := by
    rw [abs_mul, abs_of_nonneg (binWeight_nonneg n k), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC j hj) (binWeight_nonneg n k)
  have absSub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  have h₁ := absSub (binWeight n n * F (n + 1) - binWeight n 0 * F 0)
    (∑ k ∈ range n, (binWeight n (k + 1) - binWeight n k) * F (k + 1))
  have h₂ := absSub (binWeight n n * F (n + 1)) (binWeight n 0 * F 0)
  linarith [hend n (n + 1) le_rfl, hend 0 0 (Nat.zero_le (n + 1))]

/-- The OEIS finite sum on positive indices, with its natural extension at zero. -/
def a (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k * σ 1 (n + k)

private lemma weighted_sigma (n : ℕ) :
    (∑ k ∈ range (n + 1), binWeight n k * (σ 1 (n + k) : ℝ)) = (a n : ℝ) / (2 : ℝ) ^ n := by
  rw [a, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, binWeight]
  ring

private lemma weighted_linear (n : ℕ) (z : ℝ) :
    (∑ k ∈ range (n + 1), binWeight n k * (((n : ℝ) + k - 1 / 2) * z)) =
      (((3 / 2 : ℝ) * n - 1 / 2) * z) := by
  simp only [← mul_assoc, ← sum_mul]
  congr 1
  simp_rw [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
  rw [← sum_mul, ← sum_mul, binWeight_mass, binWeight_mean]
  ring

private noncomputable def normalized (n : ℕ) : ℝ := (a n : ℝ) / ((2 : ℝ) ^ n * n)

private noncomputable def model (n : ℕ) : ℝ :=
  ((3 / 2 : ℝ) - (1 / 2 : ℝ) / n) * reciprocalSquares (2 * n)

/-- Uniform normalized error bound for the finite Basel approximation. -/
private lemma normalized_error {n : ℕ} (hn : 0 < n) :
    |normalized n - model n| ≤ 32 * (1 + Real.log (2 * n)) / Real.sqrt ((n : ℝ) + 1) := by
  let z := reciprocalSquares (2 * n)
  let F := fun k : ℕ => divisorPrefix (n - 1 + k) - ((n - 1 + k : ℕ) : ℝ) ^ 2 / 2 * z
  let C := 4 * (n : ℝ) * (1 + Real.log (2 * n))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn])
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : ∀ k ≤ n + 1, |F k| ≤ C := by
    intro k hk
    have h := divisorPrefix_error (show n - 1 + k ≤ 2 * n by omega)
    refine h.trans ?_
    dsimp [C]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    have hu : ((n - 1 + k : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n - 1 + k ≤ 2 * n by omega)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hdiff (k : ℕ) : F (k + 1) - F k =
      (σ 1 (n + k) : ℝ) - (((n : ℝ) + k - 1 / 2) * z) := by
    dsimp [F]
    rw [show n - 1 + (k + 1) = (n - 1 + k) + 1 by omega, divisorPrefix_succ,
      show n - 1 + k + 1 = n + k by omega, show n - 1 + k = n + k - 1 by omega,
      Nat.cast_sub (by omega : 1 ≤ n + k)]
    push_cast
    ring
  have hsum := binWeight_sum_error F n C hF
  simp_rw [hdiff, mul_sub, sum_sub_distrib, weighted_sigma, weighted_linear] at hsum
  have hmax : |(a n : ℝ) / (2 : ℝ) ^ n - (((3 / 2 : ℝ) * n - 1 / 2) * z)| ≤
      C * (2 * (4 / Real.sqrt ((n : ℝ) + 1))) :=
    hsum.trans <| mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (binWeight_bound n (n / 2)) (by norm_num)) hC
  have heq : normalized n - model n =
      ((a n : ℝ) / (2 : ℝ) ^ n - (((3 / 2 : ℝ) * n - 1 / 2) * z)) / n := by
    dsimp [normalized, model, z]
    field_simp
  rw [heq, abs_div, abs_of_pos hn']
  refine (div_le_div_of_nonneg_right hmax hn'.le).trans ?_
  dsimp [C]
  field_simp
  ring_nf
  exact le_rfl

private lemma tendsto_reciprocalSquares :
    Tendsto (fun n : ℕ => reciprocalSquares (2 * n)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hmul : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n + 1) tendsto_id
  refine (hasSum_zeta_two.tendsto_sum_nat.comp hmul).congr fun n => ?_
  change (∑ d ∈ range (2 * n + 1), 1 / (d : ℝ) ^ 2) = reciprocalSquares (2 * n)
  rw [← sum_range_add_sum_Ico (fun d : ℕ => 1 / (d : ℝ) ^ 2) (by omega : 1 ≤ 2 * n + 1)]
  have hset : Ico 1 (2 * n + 1) = Ioc 0 (2 * n) := by ext d; simp; omega
  rw [hset]
  simp [reciprocalSquares]

private lemma tendsto_model : Tendsto model atTop (𝓝 (Real.pi ^ 2 / 4)) := by
  have hinv : Tendsto (fun n : ℕ => (1 / 2 : ℝ) / n) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  have ht := ((tendsto_const_nhds (x := (3 / 2 : ℝ))).sub hinv).mul tendsto_reciprocalSquares
  rw [show ((3 / 2 : ℝ) - 0) * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 4 by ring] at ht
  exact ht

private lemma tendsto_log_sqrt_error :
    Tendsto (fun n : ℕ => 32 * (1 + Real.log (2 * n)) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hseq : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 1) tendsto_natCast_atTop_atTop
  have hlog := (isLittleO_log_rpow_atTop (show 0 < (1 / 2 : ℝ) by norm_num)).tendsto_div_nhds_zero.comp hseq
  have hpow := (tendsto_rpow_neg_atTop (show 0 < (1 / 2 : ℝ) by norm_num)).comp hseq
  have hsum : Tendsto (fun n : ℕ => 32 * ((1 + Real.log 2 + Real.log ((n : ℝ) + 1)) /
      Real.sqrt ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have ht := ((hpow.const_mul (1 + Real.log 2)).add hlog).const_mul 32
    simp only [mul_zero, zero_add] at ht
    refine ht.congr fun n => ?_
    simp only [Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) + 1),
      div_eq_mul_inv, add_mul]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn'.ne', mul_div_assoc, ← add_assoc]
    have hlog : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn' (by linarith)
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)) (by norm_num)

private lemma tendsto_normalized : Tendsto normalized atTop (𝓝 (Real.pi ^ 2 / 4)) := by
  have he : Tendsto (fun n : ℕ => normalized n - model n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_log_sqrt_error
      (Eventually.of_forall fun n => norm_nonneg _) ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simpa only [Real.norm_eq_abs] using normalized_error hn
  simpa only [sub_add_cancel, zero_add] using he.add tendsto_model

/-- Václav Kotesovec's conjecture for OEIS A181411. -/
theorem oeis_a181411 :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (Real.pi ^ 2 / 4) * (n : ℝ) * (2 : ℝ) ^ n) := by
  have hc : (Real.pi ^ 2 / 4 : ℝ) ≠ 0 := by positivity
  have hden : ∀ᶠ n : ℕ in atTop, (Real.pi ^ 2 / 4) * (n : ℝ) * (2 : ℝ) ^ n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  apply (isEquivalent_iff_tendsto_one hden).mpr
  have h := tendsto_normalized.div_const (Real.pi ^ 2 / 4)
  rw [div_self hc] at h
  refine h.congr fun n => ?_
  change normalized n / (Real.pi ^ 2 / 4) = (a n : ℝ) /
    ((Real.pi ^ 2 / 4) * (n : ℝ) * (2 : ℝ) ^ n)
  unfold normalized
  ring

end OEISA181411

-- Credit: @rkka02
theorem OMA.solution : type_of% @OMA.S_oeis_a181411.main :=
  OEISA181411.oeis_a181411
