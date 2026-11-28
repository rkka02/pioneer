import OMAStatements.S_oeis_a308758
import Mathlib

/-!
# The third-largest parts of four-part partitions

Colin Barker's conjectures for OEIS A308758, from June 23, 2019.
Source: https://oeis.org/A308758.
-/

namespace OEISA308758

open OMA.S_oeis_a308758 Finset PowerSeries

private noncomputable abbrev x : PowerSeries ℤ := PowerSeries.X
private abbrev M : (ℕ → ℤ) → PowerSeries ℤ := PowerSeries.mk

private noncomputable abbrev D (d : ℕ) : PowerSeries ℤ := 1 - x ^ d

private lemma shift_index (d m i : ℕ) : m + d - d * (i + 1) = m - d * i := by
  rw [Nat.mul_add, Nat.mul_one]
  omega

private lemma accumulate_step {d : ℕ} (hd : 0 < d) (f : ℕ → ℤ) (m : ℕ) :
    accumulate d f (m + d) = f (m + d) + accumulate d f m := by
  rw [accumulate, Nat.add_div_right _ hd, sum_range_succ']
  simp only [shift_index, Nat.mul_zero, Nat.sub_zero, accumulate]
  ring

private lemma weighted_step {d : ℕ} (hd : 0 < d) (f : ℕ → ℤ) (m : ℕ) :
    weighted d f (m + d) = weighted d f m + accumulate d f m := by
  rw [weighted, Nat.add_div_right _ hd, sum_range_succ']
  simp only [shift_index, Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
    sum_add_distrib, add_zero, weighted, accumulate]

private lemma accumulate_series {d : ℕ} (hd : 0 < d) (f : ℕ → ℤ) :
    D d * M (accumulate d f) = M f := by
  ext m
  simp only [D, sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk]
  by_cases hm : d ≤ m
  · have h := accumulate_step hd f (m - d)
    rw [Nat.sub_add_cancel hm] at h
    simp only [if_pos hm]
    omega
  · simp [hm, accumulate, Nat.div_eq_of_lt (lt_of_not_ge hm)]

private lemma weighted_series {d : ℕ} (hd : 0 < d) (f : ℕ → ℤ) :
    D d * M (weighted d f) = x ^ d * M (accumulate d f) := by
  ext m
  simp only [D, sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk]
  by_cases hm : d ≤ m
  · have h := weighted_step hd f (m - d)
    rw [Nat.sub_add_cancel hm] at h
    simp only [if_pos hm]
    omega
  · simp [hm, weighted, Nat.div_eq_of_lt (lt_of_not_ge hm)]

private lemma ones_series : D 1 * M ones = 1 := by
  ext m
  simp only [D, sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk, ones, coeff_one]
  cases m <;> simp

private lemma series_a : M a = x ^ 4 * (M partCount + M pWeight + M qWeight) := by
  ext m
  simp [a, coeff_X_pow_mul']

private noncomputable abbrev denominator : PowerSeries ℤ :=
  (1 - x) ^ 5 * (1 + x) ^ 3 * (1 + x ^ 2) ^ 2 * (1 + x + x ^ 2) ^ 2

private noncomputable abbrev numerator : PowerSeries ℤ := x ^ 4 * (1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6)

private lemma series_identity : denominator * M a = numerator := by
  have hpairs : D 2 * M pairs = M ones := accumulate_series (d := 2) (by decide) ones
  have htriples : D 3 * M triples = M pairs := accumulate_series (d := 3) (by decide) pairs
  have hpart : D 4 * M partCount = M triples := accumulate_series (d := 4) (by decide) triples
  have hpw : D 4 * M pWeight = x ^ 4 * M partCount := weighted_series (d := 4) (by decide) triples
  have hqw : D 4 * M qWeight = M (weighted 3 pairs) :=
    accumulate_series (d := 4) (by decide) (weighted 3 pairs)
  have hwq : D 3 * M (weighted 3 pairs) = x ^ 3 * M triples := weighted_series (d := 3) (by decide) pairs
  let rawD := D 1 * D 2 * D 3 ^ 2 * D 4 ^ 2
  have h₀ : rawD * M partCount = D 3 * D 4 := by
    calc
      _ = (D 3 * D 4) * (D 1 * (D 2 * (D 3 * (D 4 * M partCount)))) := by dsimp [rawD]; ring
      _ = _ := by rw [hpart, htriples, hpairs, ones_series, mul_one]
  have h₁ : rawD * M pWeight = x ^ 4 * D 3 := by
    calc
      _ = D 3 * (D 1 * (D 2 * (D 3 * (D 4 * (D 4 * M pWeight))))) := by dsimp [rawD]; ring
      _ = (x ^ 4 * D 3) * (D 1 * (D 2 * (D 3 * (D 4 * M partCount)))) := by
        rw [hpw]
        ring
      _ = _ := by rw [hpart, htriples, hpairs, ones_series, mul_one]
  have h₂ : rawD * M qWeight = x ^ 3 * D 4 := by
    calc
      _ = D 4 * (D 1 * (D 2 * (D 3 * (D 3 * (D 4 * M qWeight))))) := by dsimp [rawD]; ring
      _ = (x ^ 3 * D 4) * (D 1 * (D 2 * (D 3 * M triples))) := by
        rw [hqw, hwq]
        ring
      _ = _ := by rw [htriples, hpairs, ones_series, mul_one]
  have hraw : rawD * M a = x ^ 4 * (1 - x ^ 7) := by
    rw [series_a]
    calc
      _ = x ^ 4 * (rawD * M partCount + rawD * M pWeight + rawD * M qWeight) := by ring
      _ = _ := by rw [h₀, h₁, h₂]; simp only [D]; ring
  have hD : D 1 ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    simp [D, coeff_X] at h0
  apply mul_left_cancel₀ hD
  calc
    _ = rawD * M a := by dsimp [rawD, denominator, D]; ring
    _ = x ^ 4 * (1 - x ^ 7) := hraw
    _ = _ := by simp only [D, numerator]; ring

private lemma recurrence (n : ℕ) (hn : 15 < n) :
    a n = a (n - 2) + 2 * a (n - 3) + 2 * a (n - 4) - 2 * a (n - 5) - 3 * a (n - 6) - 4 * a (n - 7)
      + 4 * a (n - 9) + 3 * a (n - 10) + 2 * a (n - 11) - 2 * a (n - 12) - 2 * a (n - 13)
      - a (n - 14) + a (n - 16) := by
  have hD : denominator = 1 - x ^ 2 - C (2 : ℤ) * x ^ 3 - C (2 : ℤ) * x ^ 4 +
      C (2 : ℤ) * x ^ 5 + C (3 : ℤ) * x ^ 6 + C (4 : ℤ) * x ^ 7 - C (4 : ℤ) * x ^ 9 -
      C (3 : ℤ) * x ^ 10 - C (2 : ℤ) * x ^ 11 + C (2 : ℤ) * x ^ 12 +
      C (2 : ℤ) * x ^ 13 + x ^ 14 - x ^ 16 := by
    simp only [denominator, map_ofNat]
    ring
  have hN : coeff n numerator = 0 := by
    unfold numerator
    rw [coeff_X_pow_mul', if_pos (by omega : 4 ≤ n)]
    simp only [map_add, coeff_one, coeff_X, coeff_X_pow]
    split_ifs <;> omega
  have h := congrArg (coeff n) series_identity
  rw [hD, hN] at h
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk] at h
  have hn' (k : ℕ) (hk : k ≤ 16) : k ≤ n := by omega
  simp only [hn' _ (by decide : 2 ≤ 16), hn' _ (by decide : 3 ≤ 16), hn' _ (by decide : 4 ≤ 16),
    hn' _ (by decide : 5 ≤ 16), hn' _ (by decide : 6 ≤ 16), hn' _ (by decide : 7 ≤ 16),
    hn' _ (by decide : 9 ≤ 16), hn' _ (by decide : 10 ≤ 16), hn' _ (by decide : 11 ≤ 16),
    hn' _ (by decide : 12 ≤ 16), hn' _ (by decide : 13 ≤ 16), hn' _ (by decide : 14 ≤ 16),
    hn' _ (by decide : 16 ≤ 16), if_true] at h
  linarith

end OEISA308758

-- Credit: @rkka02
theorem OMA.solution : type_of% @OMA.S_oeis_a308758.main :=
  ⟨OEISA308758.series_identity, OEISA308758.recurrence⟩
