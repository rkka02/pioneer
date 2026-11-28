import OMAStatements.S_oeis_a074360
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! R. J. Mathar's cubic-coefficient generating function in OEIS A074360. -/
namespace OMA.P_oeis_a074360

open OMA.S_oeis_a074360 PowerSeries Finset

private noncomputable def c (j n : ℕ) : ℤ := (nu n).coeff j

@[local simp] private theorem c_zero (j : ℕ) : c j 0 = if j = 0 then 1 else 0 := by
  simp [c, nu, Polynomial.coeff_one]

@[local simp] private theorem c_one (j : ℕ) : c j 1 = if j = 0 then 2 else 0 := by
  rw [c, nu, show (2 : Polynomial ℤ) = Polynomial.C 2 by simp, Polynomial.coeff_C]

@[local simp] private theorem c_two (j : ℕ) : c j 2 = if j = 0 then 6 else 0 := by
  rw [c, show nu 2 = Polynomial.C 6 by norm_num [nu], Polynomial.coeff_C]

private theorem coefficient_recurrence (j n : ℕ) :
    c j (n+2) = 2*c j (n+1) +
      2*∑ i ∈ range (j+1), if i ≤ n then c (j-i) n else 0 := by
  let g : Polynomial ℤ := ∑ i ∈ range (n+1), Polynomial.X ^ i
  have hg (i : ℕ) : g.coeff i = if i ≤ n then 1 else 0 := by
    simp [g, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  have h (p : Polynomial ℤ) : (g*p).coeff j =
      ∑ i ∈ range (j+1), if i ≤ n then p.coeff (j-i) else 0 := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    funext i
    rw [hg]
    split_ifs <;> simp
  change (2*nu (n+1) + 2*g*nu n : Polynomial ℤ).coeff j = _
  rw [Polynomial.coeff_add, mul_assoc, show (2:Polynomial ℤ) = Polynomial.C 2 by simp,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, h]
  rfl

private noncomputable def F (j : ℕ) : PowerSeries ℤ := mk (c j)
private noncomputable def D : PowerSeries ℤ := 1 - C 2 * X^1 - C 2 * X^2
private noncomputable def U : PowerSeries ℤ := C 2 * X^2

private theorem coeffD (j n : ℕ) : coeff n (D * F j) =
    c j n - 2*(if 1 ≤ n then c j (n-1) else 0) -
      2*(if 2 ≤ n then c j (n-2) else 0) := by
  simp only [D, F, sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk]

private theorem coeffU (f : PowerSeries ℤ) (n : ℕ) : coeff n (U * f) =
    2*(if 2 ≤ n then coeff (n-2) f else 0) := by
  simp only [U, mul_assoc, coeff_C_mul, coeff_X_pow_mul']

private noncomputable def forcing : ℕ → PowerSeries ℤ
  | 0 => 0
  | 1 => F 0 - 1
  | 2 => F 1 + F 0 - 1 - C 2 * X^1
  | 3 => F 2 + F 1 + F 0 - 1 - C 2 * X^1 - C 6 * X^2
  | _ => 0

private theorem forced_series (j : ℕ) (hj : j ≤ 3) :
    D * F j = (if j = 0 then 1 else 0) + U * forcing j := by
  ext n
  rw [coeffD, map_add, coeffU]
  rcases n with _ | (_ | m)
  · interval_cases j <;> norm_num [coeff_one]
  · interval_cases j <;> norm_num [coeff_one]
  · have hr := coefficient_recurrence j m
    rw [if_pos (by omega : 1 ≤ m+2), if_pos (by omega : 2 ≤ m+2),
      show m+2-1 = m+1 by omega, show m+2-2 = m by omega]
    by_cases hm : 3 ≤ m
    · have hm1 : 1 ≤ m := by omega
      have hm2 : 2 ≤ m := by omega
      have he0 : m ≠ 0 := by omega
      have he1 : m ≠ 1 := by omega
      have he2 : m ≠ 2 := by omega
      have hs0 : m+2 ≠ 0 := by omega
      interval_cases j <;>
        simp only [forcing, map_add, map_sub, coeff_C_mul, coeff_X_pow] <;>
        norm_num [coeff_one, F, sum_range_succ, hm, hm1, hm2, he0, he1, he2, hs0] at hr ⊢ <;>
        linear_combination hr
    · interval_cases m <;> interval_cases j <;>
        simp only [forcing, map_add, map_sub, coeff_C_mul, coeff_X_pow] <;>
        norm_num [coeff_one, F, sum_range_succ] at hr ⊢ <;>
        linear_combination hr

theorem formula :
    let x := (X : PowerSeries ℤ)
    (2*x^2 + 2*x - 1)^4 * mk a =
      8*x^5*(1+x)*(12*x^4 + 24*x^3 - 2*x^2 - 16*x + 5) := by
  dsimp only
  have h0 : D * F 0 = 1 := by simpa [forcing] using forced_series 0 (by decide)
  have h1 : D * F 1 = U * (F 0 - 1) := by simpa [forcing] using forced_series 1 (by decide)
  have h2 : D * F 2 = U * (F 1 + F 0 - 1 - C 2 * X^1) := by
    simpa [forcing] using forced_series 2 (by decide)
  have h3 : D * F 3 = U * (F 2 + F 1 + F 0 - 1 - C 2 * X^1 - C 6 * X^2) := by
    simpa [forcing] using forced_series 3 (by decide)
  change (2*X^2 + 2*X - 1)^4 * F 3 = _
  linear_combination (norm := (simp [D, U]; ring)) D^3*h3 + U*D^2*h2 +
    (U*D^2 + U^2*D)*h1 + (U*D^2 + 2*U^2*D + U^3)*h0

end OMA.P_oeis_a074360

theorem OMA.solution : type_of% @OMA.S_oeis_a074360.main :=
  OMA.P_oeis_a074360.formula
