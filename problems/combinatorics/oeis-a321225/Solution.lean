import OMAStatements.S_oeis_a321225
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Chai Wah Wu's recurrence and generating function for the decimal chunks of 12321. -/

namespace OMA.P_oeis_a321225

open OMA.S_oeis_a321225 PowerSeries

private theorem digit_period (i q : ℕ) : digit (i + 5 * q) = digit i := by
  have h : (i + 5 * q) % 5 = i % 5 := by omega
  simp only [digit, h]

private theorem digit_cycle (i : ℕ) :
    digit i + digit (i+1) + digit (i+2) + digit (i+3) + digit (i+4) = 9 := by
  have h (j : ℕ) : digit (i+j) = digit (i%5+j) := by
    have hmod : (i+j)%5 = (i%5+j)%5 := by omega
    simp only [digit, hmod]
  rw [show digit i = digit (i%5) by simpa using h 0, h 1, h 2, h 3, h 4]
  have hm : i%5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases i%5 <;> decide

private theorem prefix_five (i : ℕ) :
    prefixSum (i+5) = prefixSum i + 9 := by
  have h := digit_cycle i
  simp only [prefixSum]
  omega

private theorem prefix_period (i q : ℕ) :
    prefixSum (i + 5*q) = prefixSum i + 9*q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show i + 5 * (q+1) = (i + 5*q) + 5 by omega, prefix_five, ih]
    omega

private theorem prefix_strict : StrictMono prefixSum := by
  apply strictMono_nat_of_lt_succ
  intro i
  have h : 0 < digit i := by unfold digit; split_ifs <;> decide
  simp only [prefixSum]
  omega

private theorem triangle_twice (n : ℕ) :
    2 * triangle n = n * (n+1) := by
  unfold triangle
  have he : (n * (n+1)) % 2 = 0 := by
    have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h with h | h
    · simp [Nat.mul_mod, h]
    · have hs : (n+1) % 2 = 0 := by omega
      simp [Nat.mul_mod, hs]
  omega

private theorem triangle_period (n : ℕ) :
    triangle (n+9) = triangle n + 9*(n+5) := by
  have h : 2 * triangle (n+9) = 2 * (triangle n + 9*(n+5)) := by
    rw [Nat.mul_add, triangle_twice, triangle_twice]
    ring
  omega

private theorem triangle_mod (n : ℕ) : triangle n % 9 = triangle (n%9) % 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 9
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 9 ≤ n by omega)
      rw [Nat.add_comm 9 m, triangle_period]
      have hr : (m+9)%9 = m%9 := by omega
      have ht : (triangle m + 9*(m+5))%9 = triangle m%9 := by omega
      rw [hr, ht, ih m (by omega)]

private def offset (n : ℕ) : ℕ :=
  match n % 9 with
  | 1 | 4 | 7 => 1
  | 2 | 6 => 2
  | 3 | 5 => 3
  | _ => 0

private theorem offset_spec (n : ℕ) : prefixSum (offset n) = triangle n % 9 := by
  rw [triangle_mod, offset]
  have hn : n % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases n%9 <;> decide

private theorem cut_eq (n : ℕ) : cut n = offset n + 5*(triangle n / 9) := by
  let k := offset n + 5*(triangle n / 9)
  have hk : prefixSum k = triangle n := by
    dsimp only [k]
    rw [prefix_period, offset_spec]
    omega
  have hs : {m : ℕ | prefixSum m = triangle n} = {k} := by
    ext m
    constructor
    · intro hm
      exact prefix_strict.injective (hm.trans hk.symm)
    · intro hm
      change m = k at hm
      change prefixSum m = triangle n
      rw [hm]
      exact hk
  rw [cut, hs, csInf_singleton]

private theorem cut_spec (n : ℕ) : prefixSum (cut n) = triangle n := by
  rw [cut_eq, prefix_period, offset_spec]
  omega

private theorem cut_period (n : ℕ) : cut (n+9) = cut n + 5*(n+5) := by
  apply prefix_strict.injective
  rw [cut_spec, prefix_period, cut_spec, triangle_period]

private theorem cut_le (n : ℕ) : cut n ≤ cut (n+1) := by
  apply prefix_strict.le_iff_le.mp
  rw [cut_spec, cut_spec]
  have h : 2 * triangle (n+1) = 2 * (triangle n + (n+1)) := by
    rw [Nat.mul_add, triangle_twice, triangle_twice]
    ring
  omega

private theorem decimal_period (i q k : ℕ) :
    decimal (i+5*q) k = decimal i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [decimal, ih, show i+5*q+k = i+k+5*q by omega, digit_period]

private theorem decimal_append (i u v : ℕ) :
    decimal i (u+v) = 10^v*decimal i u + decimal (i+u) v := by
  induction v with
  | zero => simp [decimal]
  | succ v ih =>
    rw [Nat.add_succ, decimal, ih, decimal, pow_succ,
      show i + (u + v) = i + u + v by omega]
    ring

private theorem extend_chunk (n : ℕ) :
    a (n+1+9) = 100000*a (n+1) + decimal (cut (n+1)) 5 := by
  have hc := cut_le n
  have hlen :
      (cut (n+1) + 5*(n+1+5)) - (cut n + 5*(n+5)) =
        (cut (n+1) - cut n) + 5 := by omega
  rw [show n+1+9 = (n+9)+1 by omega, a, show n+9+1 = n+1+9 by omega,
    cut_period (n+1), cut_period n, hlen, decimal_period, decimal_append,
    show cut n + (cut (n+1) - cut n) = cut (n+1) by omega]
  norm_num [a]

private theorem recurrence (n : ℕ) (hn : 18 < n) :
    a n = 100001*a (n-9) - 100000*a (n-18) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 19 ≤ n by omega)
  have h1 := extend_chunk k
  have h2 := extend_chunk (k+9)
  rw [show k+9+1 = k+1+9 by omega, cut_period, decimal_period] at h2
  rw [show 19+k-9 = k+1+9 by omega, show 19+k-18 = k+1 by omega,
    show 19+k = k+1+9+9 by omega]
  linear_combination h2 - h1

private theorem coeff_shift (n k : ℕ) (f : ℕ → ℤ) :
    coeff n (X^k * mk f) = if k ≤ n then f (n-k) else 0 := by
  simp [coeff_X_pow_mul']

private theorem generating_function :
    let x := (X : PowerSeries ℤ)
    (100000*x^18 - 100001*x^9 + 1) * mk a =
      x*(10000*x^16 + 20000*x^15 + 30000*x^14 + 21100*x^13 + 23000*x^12
        + 21120*x^11 + 32110*x^10 + 23210*x^9 + 12321*x^8 + 2321*x^7
        + 3211*x^6 + 2112*x^5 + 23*x^4 + 211*x^3 + 3*x^2 + 2*x + 1) := by
  dsimp only
  have denominator :
      (100000*X^18 - 100001*X^9 + 1 : PowerSeries ℤ) =
        C 100000 * X^18 - C 100001 * X^9 + 1 := by simp
  have numerator :
      (X*(10000*X^16 + 20000*X^15 + 30000*X^14 + 21100*X^13 + 23000*X^12
        + 21120*X^11 + 32110*X^10 + 23210*X^9 + 12321*X^8 + 2321*X^7
        + 3211*X^6 + 2112*X^5 + 23*X^4 + 211*X^3 + 3*X^2 + 2*X + 1) : PowerSeries ℤ) =
      C 10000*X^17 + C 20000*X^16 + C 30000*X^15 + C 21100*X^14 + C 23000*X^13 +
        C 21120*X^12 + C 32110*X^11 + C 23210*X^10 + C 12321*X^9 + C 2321*X^8 +
        C 3211*X^7 + C 2112*X^6 + C 23*X^5 + C 211*X^4 + C 3*X^3 + C 2*X^2 + X^1 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [denominator, numerator]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow, coeff_shift, coeff_mk]
  by_cases hn : 18 < n
  · have he (k : ℕ) (hk : k ≤ 17) : n ≠ k := by omega
    simp only [if_pos (by omega : 18 ≤ n), if_pos (by omega : 9 ≤ n),
      if_neg (he 17 (by decide)), if_neg (he 16 (by decide)), if_neg (he 15 (by decide)),
      if_neg (he 14 (by decide)), if_neg (he 13 (by decide)), if_neg (he 12 (by decide)),
      if_neg (he 11 (by decide)), if_neg (he 10 (by decide)), if_neg (he 9 (by decide)),
      if_neg (he 8 (by decide)), if_neg (he 7 (by decide)), if_neg (he 6 (by decide)),
      if_neg (he 5 (by decide)), if_neg (he 4 (by decide)), if_neg (he 3 (by decide)),
      if_neg (he 2 (by decide)), if_neg (he 1 (by decide))]
    linear_combination recurrence n hn
  · interval_cases n <;> norm_num [a, cut_eq, offset, triangle, decimal, digit]

end OMA.P_oeis_a321225

theorem OMA.solution : type_of% @OMA.S_oeis_a321225.main :=
  ⟨OMA.P_oeis_a321225.recurrence, OMA.P_oeis_a321225.generating_function⟩
