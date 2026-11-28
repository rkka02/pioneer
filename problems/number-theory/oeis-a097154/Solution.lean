import OMAStatements.S_oeis_a097154
import Mathlib.Data.Nat.Digits.Lemmas


namespace OeisA097154

def reverseDecimal (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

def largestDigit (n : ℕ) : ℕ := (Nat.digits 10 n).foldr max 0

private theorem value_eq_zero_iff_sum_eq_zero (digits : List ℕ) :
    Nat.ofDigits 10 digits = 0 ↔ digits.sum = 0 := by
  induction digits with
  | nil => simp
  | cons d tail ih =>
    rw [Nat.ofDigits_cons, List.sum_cons]
    omega

private theorem max_lt_ten (digits : List ℕ) (h : ∀ d ∈ digits, d < 10) :
    digits.foldr max 0 < 10 := by
  induction digits with
  | nil => decide
  | cons d tail ih =>
    exact max_lt (h d (by simp)) (ih fun e he => h e (by simp [he]))

private theorem max_zero_implies_value_zero (digits : List ℕ)
    (h : digits.foldr max 0 = 0) : Nat.ofDigits 10 digits = 0 := by
  induction digits with
  | nil => rfl
  | cons d tail ih =>
    change max d (tail.foldr max 0) = 0 at h
    have hd : d = 0 := by have := le_max_left d (tail.foldr max 0); omega
    have ht : tail.foldr max 0 = 0 := by have := le_max_right d (tail.foldr max 0); omega
    simp [Nat.ofDigits_cons, hd, ih ht]

private theorem reverse_mod_nine (digits : List ℕ) :
    Nat.ofDigits 10 digits.reverse % 9 = Nat.ofDigits 10 digits % 9 := by
  rw [Nat.ofDigits_mod 10 9 digits.reverse, Nat.ofDigits_mod 10 9 digits]
  change Nat.ofDigits 1 digits.reverse % 9 = Nat.ofDigits 1 digits % 9
  rw [Nat.ofDigits_one, Nat.ofDigits_one, List.sum_reverse]

private theorem pair_of_gap_nine (digits : List ℕ) (hbound : ∀ d ∈ digits, d < 10)
    (hgap : Nat.ofDigits 10 digits.reverse = Nat.ofDigits 10 digits + 9) :
    ∃ first last : ℕ, digits = [first, last] ∧ first = last + 1 := by
  cases digits with
  | nil => simp at hgap
  | cons first tail =>
    induction tail using List.reverseRecOn with
    | nil => simp at hgap
    | append_singleton mid last =>
      have hfirst : first < 10 := hbound first (by simp)
      have hlast : last < 10 := hbound last (by simp)
      have hmid : ∀ d ∈ mid, d < 10 := fun d hd => hbound d (by simp [hd])
      have hmidReverse : ∀ d ∈ mid.reverse, d < 10 := fun d hd => hmid d (by simpa using hd)
      let p := (10 : ℕ) ^ mid.length
      have hp : 0 < p := Nat.pow_pos (by decide)
      have hval : Nat.ofDigits 10 mid < p :=
        Nat.ofDigits_lt_base_pow_length (by decide) hmid
      have hrev : Nat.ofDigits 10 mid.reverse < p := by
        simpa [p] using Nat.ofDigits_lt_base_pow_length (b := 10) (by decide) hmidReverse
      have hend : last = (first + 9) % 10 := by
        have hm := congrArg (· % 10) hgap
        rw [Nat.add_mod, Nat.ofDigits_mod_eq_head!, Nat.ofDigits_mod_eq_head!] at hm
        simpa [List.reverse_cons, Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hlast, Nat.add_mod]
          using hm
      change Nat.ofDigits 10 (first :: (mid ++ [last])).reverse =
        Nat.ofDigits 10 (first :: (mid ++ [last])) + 9 at hgap
      have hlist : (first :: (mid ++ [last])).reverse = last :: (mid.reverse ++ [first]) := by
        simp [List.reverse_cons, List.reverse_append]
      rw [hlist] at hgap
      have hformula :
          last + 10 * Nat.ofDigits 10 mid.reverse + 10 * p * first =
            first + 10 * Nat.ofDigits 10 mid + 10 * p * last + 9 := by
        simp only [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_nil, mul_zero,
          add_zero, List.length_reverse, p] at hgap ⊢
        simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hgap
      have hstep : first = last + 1 := by
        by_contra hne
        have ha : first = 0 := by omega
        have hz : last = 9 := by omega
        rw [ha, hz] at hformula
        omega
      rw [hstep, mul_add, mul_one] at hformula
      have hzero : Nat.ofDigits 10 mid.reverse = 0 := by omega
      have hvalzero : Nat.ofDigits 10 mid = 0 := by
        apply (value_eq_zero_iff_sum_eq_zero _).mpr
        simpa using (value_eq_zero_iff_sum_eq_zero _).mp hzero
      have hpone : p = 1 := by omega
      have hnil : mid = [] := by
        cases mid with
        | nil => rfl
        | cons d ds =>
          have hpow : 0 < (10 : ℕ) ^ ds.length := Nat.pow_pos (by decide)
          simp only [p, List.length_cons, pow_succ] at hpone
          omega
      simp [hnil, hstep]

/-- The fixed-point conjecture from the original OEIS entry. The sum form avoids
truncated subtraction at inputs where reversal is smaller than the largest digit. -/
theorem fixed_points (n : ℕ) :
    reverseDecimal n = n + largestDigit n ↔ n = 0 ∨ n = 89 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    let digits := Nat.digits 10 n
    have hrepr : Nat.ofDigits 10 digits = n := Nat.ofDigits_digits 10 n
    have hbound : ∀ d ∈ digits, d < 10 := fun _ hd => Nat.digits_lt_base (by decide) hd
    have hbelow : largestDigit n < 10 := max_lt_ten digits hbound
    have hpos : 0 < largestDigit n := by
      by_contra! hh
      change digits.foldr max 0 ≤ 0 at hh
      exact hn (hrepr.symm.trans (max_zero_implies_value_zero digits (by omega)))
    have hmod := reverse_mod_nine digits
    change reverseDecimal n % 9 = _ at hmod
    rw [h, hrepr] at hmod
    have hnine : largestDigit n = 9 := by omega
    have hgap : Nat.ofDigits 10 digits.reverse = Nat.ofDigits 10 digits + 9 := by
      change reverseDecimal n = _
      simpa [hrepr, hnine] using h
    obtain ⟨first, last, hpair, hstep⟩ := pair_of_gap_nine digits hbound hgap
    have hs : digits.foldr max 0 = 9 := hnine
    rw [hpair] at hs hrepr
    simp only [List.foldr_cons, List.foldr_nil, max_zero, Nat.ofDigits_cons,
      Nat.ofDigits_nil, mul_zero, add_zero] at hs hrepr
    rw [max_eq_left (by omega)] at hs
    omega
  · rintro (rfl | rfl) <;> decide

private theorem max_le_sum (digits : List ℕ) : digits.foldr max 0 ≤ digits.sum := by
  induction digits with
  | nil => decide
  | cons d tail ih =>
    change max d (tail.foldr max 0) ≤ d + tail.sum
    exact max_le (by omega) (by omega)

private theorem largestDigit_le_reverse (n : ℕ) : largestDigit n ≤ reverseDecimal n := by
  calc
    largestDigit n ≤ (Nat.digits 10 n).sum := max_le_sum _
    _ = (Nat.digits 10 n).reverse.sum := (List.sum_reverse _).symm
    _ ≤ reverseDecimal n := Nat.sum_le_ofDigits _ (by decide)

/-- The fixed-point set in the exact form of the proposed Left to Solve statement. -/
theorem fixedPointSet : {x : ℕ | reverseDecimal x - largestDigit x = x} = {0, 89} := by
  ext x
  change (reverseDecimal x - largestDigit x = x) ↔ x = 0 ∨ x = 89
  rw [Nat.sub_eq_iff_eq_add (largestDigit_le_reverse x)]
  exact fixed_points x

end OeisA097154

theorem OMA.solution : type_of% @OMA.S_oeis_a097154.main := OeisA097154.fixedPointSet
