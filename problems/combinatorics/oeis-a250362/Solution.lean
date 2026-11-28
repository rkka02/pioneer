import OMAStatements.S_oeis_a250362
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Closed form, generating function, and recurrence for Barker's conjectures in A250362. -/

namespace OMA.P_oeis_a250362

open OMA.S_oeis_a250362 PowerSeries

private def constantEquiv (n : ℕ) : {w : ArrayChoice n // constantArray w} ≃ Fin (n - 2) where
  toFun w :=
    ⟨(w.val 0).val - 3, by
      have h := w.property (3 : Fin 4)
      change (w.val 3).val + 3 = (w.val 0).val at h
      have hn := (w.val 0).isLt
      omega⟩
  invFun j :=
    ⟨fun i => ⟨j.val + 3 - i.val, by
      have hi := i.isLt
      have hj := j.isLt
      omega⟩, by
      intro i
      change j.val + 3 - i.val + i.val = j.val + 3 - 0
      have hi := i.isLt
      omega⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have h3 := w.property (3 : Fin 4)
    have hi := w.property i
    change (w.val 3).val + 3 = (w.val 0).val at h3
    change (w.val i).val + i.val = (w.val 0).val at hi
    change (w.val 0).val - 3 + 3 - i.val = (w.val i).val
    omega
  right_inv j := by
    apply Fin.ext
    change j.val + 3 - 0 - 3 = j.val
    omega

private theorem count_formula (n : ℕ) (hn : n ≠ 0) :
    a n = (n + 1)^4 - (n - 2) := by
  classical
  rw [a, if_neg hn, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_congr (constantEquiv n)]
  simp [ArrayChoice]

private theorem a_polynomial (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) = ((n : ℤ) + 1)^4 - ((n : ℤ) - 2) := by
  rw [count_formula n (by omega), Int.natCast_sub, Int.natCast_sub hn]
  · push_cast
    ring
  · calc
      n - 2 ≤ n + 1 := by omega
      _ ≤ (n + 1)^4 := Nat.le_self_pow (by decide) _

private theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  have shifted (k : ℕ) (hk : k ≤ 5) :
      (a (n - k) : ℤ) = ((n : ℤ) - k + 1)^4 - ((n : ℤ) - k - 2) := by
    rw [a_polynomial _ (by omega), Int.natCast_sub (by omega)]
  rw [a_polynomial n (by omega), shifted 1 (by decide), shifted 2 (by decide),
    shifted 3 (by decide), shifted 4 (by decide), shifted 5 (by decide)]
  push_cast
  ring

private theorem coeff_shift (n k : ℕ) (f : ℕ → ℤ) :
    coeff n (X ^ k * mk f) = if k ≤ n then f (n - k) else 0 := by
  simp [coeff_X_pow_mul']

private theorem generating_function :
    ((1 - X) ^ 5 * mk (fun n => (a n : ℤ)) : PowerSeries ℤ) =
      X * (16 + X + 10 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + X ^ 5) := by
  have denominator :
      (1 - X)^5 = (1 : PowerSeries ℤ) - C 5 * X^1 + C 10 * X^2 -
        C 10 * X^3 + C 5 * X^4 - X^5 := by
    simp only [map_ofNat, pow_one]
    ring
  have numerator :
      (X : PowerSeries ℤ) * (16 + X + 10 * X^2 - 2 * X^3 - 2 * X^4 + X^5) =
        C 16 * X^1 + X^2 + C 10 * X^3 - C 2 * X^4 - C 2 * X^5 + X^6 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [denominator, numerator]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow, coeff_shift, coeff_mk]
  by_cases h : 6 < n
  · rw [if_pos (by omega : 1 ≤ n), if_pos (by omega : 2 ≤ n),
      if_pos (by omega : 3 ≤ n), if_pos (by omega : 4 ≤ n), if_pos (by omega : 5 ≤ n),
      if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3),
      if_neg (by omega : n ≠ 4), if_neg (by omega : n ≠ 5), if_neg (by omega : n ≠ 6)]
    linear_combination recurrence n h
  · have a_zero : a 0 = 0 := by simp [a]
    interval_cases n <;> norm_num [a_zero, count_formula]

theorem main :
    ((1 - X) ^ 5 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (16 + X + 10 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + X ^ 5)) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
        5 * a (n - 4) + a (n - 5)) :=
  ⟨generating_function, recurrence⟩

end OMA.P_oeis_a250362

theorem OMA.solution : type_of% @OMA.S_oeis_a250362.main :=
  OMA.P_oeis_a250362.main
