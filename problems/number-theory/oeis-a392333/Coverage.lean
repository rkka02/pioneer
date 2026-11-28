import Mathlib

namespace FactorialEndpoint

private theorem factorization_large_prime {n p : ℕ} (hp : p.Prime)
    (hpn : p ≤ n) (hnp : n < 2 * p) : n.factorial.factorization p = 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hsq : n < p ^ 2 := by nlinarith
  have hlog : p.log n < 2 := Nat.log_lt_of_lt_pow (by omega : n ≠ 0) hsq
  rw [Nat.factorization_factorial hp hlog]
  have hrange : Finset.Ico 1 2 = {1} := by decide
  rw [hrange, Finset.sum_singleton, pow_one]
  exact Nat.div_eq_of_lt_le (by simpa using hpn) hnp

private theorem product_factorization (a b c d e p : ℕ) :
    (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial).factorization p =
      a.factorial.factorization p + b.factorial.factorization p + c.factorial.factorization p +
        d.factorial.factorization p + e.factorial.factorization p := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity)]
  simp

private theorem even_five_factorization {a b c d e p : ℕ}
    (hs : IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial)) :
    Even (a.factorial.factorization p + b.factorial.factorization p + c.factorial.factorization p +
          d.factorial.factorization p + e.factorial.factorization p) := by
  obtain ⟨s, h⟩ := hs
  have hs0 : s ≠ 0 := by
    by_contra! hz
    subst s
    exact (by positivity : 0 < a.factorial * b.factorial * c.factorial * d.factorial * e.factorial).ne'
      (by simpa using h)
  rw [← product_factorization, h, Nat.factorization_mul hs0 hs0]
  simp

/-- An endpoint-square witness has fourth index at least any prime in `(e/2, e]`. -/
theorem fourth_index_ge_prime {a b c d e p : ℕ} (hp : p.Prime)
    (hpe : p ≤ e) (hep : e < 2 * p) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hs : IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial)) : p ≤ d := by
  by_contra! hdp
  have hev := even_five_factorization (p := p) hs
  rw [Nat.factorization_factorial_eq_zero_of_lt (by omega : a < p),
      Nat.factorization_factorial_eq_zero_of_lt (by omega : b < p),
      Nat.factorization_factorial_eq_zero_of_lt (by omega : c < p),
      Nat.factorization_factorial_eq_zero_of_lt hdp,
      factorization_large_prime hp hpe hep] at hev
  exact (by decide : ¬ Even (0 + 0 + 0 + 0 + 1 : ℕ)) hev

/-- An odd parity from the last two factorials must be canceled by one of the first three. -/
theorem third_index_ge_odd_suffix_prime {a b c d e p : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hodd : Odd (d.factorial.factorization p + e.factorial.factorization p))
    (hs : IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial)) : p ≤ c := by
  by_contra! hcp
  have hev := even_five_factorization (p := p) hs
  rw [Nat.factorization_factorial_eq_zero_of_lt (by omega : a < p),
      Nat.factorization_factorial_eq_zero_of_lt (by omega : b < p),
      Nat.factorization_factorial_eq_zero_of_lt hcp] at hev
  exact (Nat.not_even_iff_odd.mpr hodd) (by simpa using hev)

/-- An odd parity from the last three factorials must be canceled by one of the first two. -/
theorem second_index_ge_odd_suffix_prime {a b c d e p : ℕ} (hab : a ≤ b)
    (hodd : Odd (c.factorial.factorization p + d.factorial.factorization p +
                e.factorial.factorization p))
    (hs : IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial)) : p ≤ b := by
  by_contra! hbp
  have hev := even_five_factorization (p := p) hs
  rw [Nat.factorization_factorial_eq_zero_of_lt (by omega : a < p),
      Nat.factorization_factorial_eq_zero_of_lt hbp] at hev
  exact (Nat.not_even_iff_odd.mpr hodd) (by simpa using hev)

private theorem adjacent_factorial_pair {n : ℕ} (hn : 0 < n) :
    (n - 1).factorial * n.factorial = n * (n - 1).factorial ^ 2 := by
  have hs : n = (n - 1) + 1 := by omega
  conv_lhs => enter [2]; rw [hs, Nat.factorial_succ]
  rw [← hs]
  ring

/-- The three adjacent factorial pairs ending at `a`, `b`, and `a * b`
give a square product. For the application, the six indices are distinct. -/
theorem six_factorials_of_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsSquare (((a - 1).factorial * a.factorial) * ((b - 1).factorial * b.factorial) *
      (((a * b) - 1).factorial * (a * b).factorial)) := by
  rw [adjacent_factorial_pair ha, adjacent_factorial_pair hb,
    adjacent_factorial_pair (Nat.mul_pos ha hb)]
  refine ⟨a * b * (a - 1).factorial * (b - 1).factorial * (a * b - 1).factorial, ?_⟩
  ring

private theorem factorial_numeric_succ {a b : ℕ} (h : a = b + 1) :
    a.factorial = a * b.factorial := by
  subst a
  exact Nat.factorial_succ b

private theorem last_factorials_one : (435643 : ℕ).factorial =
    435643 * (435642 : ℕ).factorial :=
  factorial_numeric_succ (a := 435643) (b := 435642) (by decide)

/-- Six distinct factorials ending at the excluded endpoint give a square. -/
theorem six_factorials_square : IsSquare ((12 : ℕ).factorial * (13 : ℕ).factorial *
    (33510 : ℕ).factorial * (33511 : ℕ).factorial * (435642 : ℕ).factorial * (435643 : ℕ).factorial) := by
  have pair {a b c A B C : ℕ} (hab : a * b = c) :
      IsSquare (A * (a * A) * B * (b * B) * C * (c * C)) := by
    refine ⟨A * B * C * c, ?_⟩
    rw [← hab]
    ring
  rw [last_factorials_one,
      factorial_numeric_succ (a := 13) (b := 12) (by decide),
      factorial_numeric_succ (a := 33511) (b := 33510) (by decide)]
  exact pair (a := 13) (b := 33511) (c := 435643)
      (A := (12 : ℕ).factorial) (B := (33510 : ℕ).factorial) (C := (435642 : ℕ).factorial) (by decide)

end FactorialEndpoint

#print axioms FactorialEndpoint.six_factorials_square
#print axioms FactorialEndpoint.fourth_index_ge_prime
#print axioms FactorialEndpoint.third_index_ge_odd_suffix_prime
#print axioms FactorialEndpoint.second_index_ge_odd_suffix_prime
#print axioms FactorialEndpoint.six_factorials_of_product
