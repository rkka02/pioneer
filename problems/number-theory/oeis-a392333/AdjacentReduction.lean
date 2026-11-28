import Mathlib

namespace FactorialEndpoint

private theorem cancel_square_factor {x s : ℕ} (hs : 0 < s) :
    IsSquare (s ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨z, hz⟩
    have hdiv : s ^ 2 ∣ z ^ 2 := ⟨x, by simpa only [pow_two] using hz.symm⟩
    obtain ⟨u, hu⟩ := (Nat.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hdiv
    refine ⟨u, Nat.eq_of_mul_eq_mul_left (pow_pos hs 2) ?_⟩
    calc
      s ^ 2 * x = z * z := hz
      _ = s ^ 2 * (u * u) := by rw [hu]; ring
  · rintro ⟨z, rfl⟩
    exact ⟨s * z, by ring⟩

private theorem adjacent_pair {n : ℕ} (hn : 0 < n) :
    (n - 1).factorial * n.factorial = n * (n - 1).factorial ^ 2 := by
  have hs : n = (n - 1) + 1 := by omega
  conv_lhs => enter [2]; rw [hs, Nat.factorial_succ]
  rw [← hs]
  ring

/-- The square class of a product with two adjacent factorial pairs. -/
theorem adjacent_five_square_iff {c m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsSquare (c.factorial * (m - 1).factorial * m.factorial *
        (n - 1).factorial * n.factorial) ↔ IsSquare (n * m * c.factorial) := by
  have h : c.factorial * (m - 1).factorial * m.factorial *
      (n - 1).factorial * n.factorial =
      c.factorial * ((m - 1).factorial * m.factorial) * ((n - 1).factorial * n.factorial) := by ring
  rw [h, adjacent_pair hm, adjacent_pair hn,
    show c.factorial * (m * (m - 1).factorial ^ 2) * (n * (n - 1).factorial ^ 2) =
      ((m - 1).factorial * (n - 1).factorial) ^ 2 * (n * m * c.factorial) by ring]
  exact cancel_square_factor (by positivity)

private theorem prime_in_other_factor {a m p x : ℕ} (hp : p.Prime)
    (hpa : ¬ p ∣ a) (hpx : ¬ p ∣ x) (h : IsSquare ((a * p) * m * x)) : p ∣ m := by
  obtain ⟨z, hz⟩ := h
  have hpz2 : p ∣ z * z := ⟨a * m * x, by rw [← hz]; ring⟩
  have hpz : p ∣ z := by simpa using hp.dvd_mul.mp hpz2
  obtain ⟨u, rfl⟩ := hpz
  have hcancel : a * m * x = p * (u * u) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * (a * m * x) = (a * p) * m * x := by ring
      _ = (p * u) * (p * u) := hz
      _ = p * (p * (u * u)) := by ring
  have hdiv : p ∣ a * m * x := ⟨u * u, hcancel⟩
  exact (hp.dvd_mul.mp ((hp.dvd_mul.mp hdiv).resolve_right hpx)).resolve_left hpa

/-- If `n = a * p`, `c < p`, and the prime `p` does not divide `a`, the five
factorial square condition is equivalent to divisibility of `m` by `p` and a
square after canceling the two factors of `p`. -/
theorem prime_adjacent_five_square_iff {c m a p : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hm : 0 < m) (hc : c < p) (hpa : ¬ p ∣ a) :
    IsSquare (c.factorial * (m - 1).factorial * m.factorial *
        (a * p - 1).factorial * (a * p).factorial) ↔
      p ∣ m ∧ IsSquare (a * (m / p) * c.factorial) := by
  rw [adjacent_five_square_iff hm (Nat.mul_pos ha hp.pos)]
  have hpx : ¬ p ∣ c.factorial := fun h ↦ (not_le_of_gt hc) (hp.dvd_factorial.mp h)
  have hcancel (hdiv : p ∣ m) :
      IsSquare ((a * p) * m * c.factorial) ↔ IsSquare (a * (m / p) * c.factorial) := by
    have hm' : p * (m / p) = m := Nat.mul_div_cancel' hdiv
    rw [show (a * p) * m * c.factorial = p ^ 2 * (a * (m / p) * c.factorial) by
      calc
        (a * p) * m * c.factorial = (a * p) * (p * (m / p)) * c.factorial := by rw [hm']
        _ = _ := by ring]
    exact cancel_square_factor hp.pos
  constructor
  · intro h
    have hdiv := prime_in_other_factor hp hpa hpx h
    exact ⟨hdiv, (hcancel hdiv).mp h⟩
  · rintro ⟨hdiv, h⟩
    exact (hcancel hdiv).mpr h

end FactorialEndpoint

#print axioms FactorialEndpoint.adjacent_five_square_iff
#print axioms FactorialEndpoint.prime_adjacent_five_square_iff
