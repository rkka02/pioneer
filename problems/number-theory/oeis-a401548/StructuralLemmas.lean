import Mathlib

/-!
# Structural lemmas for A401548

The analytic proof of the conjecture is in the accompanying manuscript.
This file checks the greedy-root bijection and the modular tail bound.
-/

namespace OeisA401548

/-- The ordered list of square roots chosen by greedy subtraction. -/
def greedyRoots : (n : ℕ) → List ℕ
  | 0 => []
  | n + 1 => (n + 1).sqrt :: greedyRoots (n + 1 - (n + 1).sqrt ^ 2)
termination_by n => n
decreasing_by
  have hs : 0 < (n + 1).sqrt := Nat.sqrt_pos.mpr (by omega)
  have hsq : 0 < ((n + 1).sqrt) ^ 2 := pow_pos hs 2
  omega

def totalSquares : List ℕ → ℕ
  | [] => 0
  | a :: tail => a ^ 2 + totalSquares tail

/-- Each root is positive and the sum of the later squares is at most twice
that root. -/
def Admissible : List ℕ → Prop
  | [] => True
  | a :: tail => 0 < a ∧ totalSquares tail ≤ 2 * a ∧ Admissible tail

private theorem sqrt_add_tail {a t : ℕ} (ht : t ≤ 2 * a) :
    Nat.sqrt (a ^ 2 + t) = a := by
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt'.mpr
    nlinarith
  · apply Nat.le_sqrt'.mpr
    omega

private theorem greedyRoots_pos {n : ℕ} (hn : 0 < n) :
    greedyRoots n = n.sqrt :: greedyRoots (n - n.sqrt ^ 2) := by
  cases n with
  | zero => simp at hn
  | succ n => rw [greedyRoots]

/-- Each admissible list is recovered by greedy subtraction of its total. -/
theorem greedyRoots_totalSquares {roots : List ℕ} (h : Admissible roots) :
    greedyRoots (totalSquares roots) = roots := by
  induction roots with
  | nil => rw [totalSquares, greedyRoots]
  | cons a tail ih =>
    obtain ⟨ha, ht, htail⟩ := h
    have hp : 0 < a ^ 2 + totalSquares tail := by positivity
    have hrem : a ^ 2 + totalSquares tail - a ^ 2 = totalSquares tail := by omega
    rw [totalSquares, greedyRoots_pos hp, sqrt_add_tail ht, hrem, ih htail]

/-- The greedy root list is admissible and its total recovers the input. -/
theorem admissible_greedyRoots (n : ℕ) :
    Admissible (greedyRoots n) ∧ totalSquares (greedyRoots n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [greedyRoots, totalSquares]
      exact ⟨trivial, rfl⟩
    · have hs : 0 < n.sqrt := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
      have hpos : 0 < n.sqrt ^ 2 := pow_pos hs 2
      have hnlt : n - n.sqrt ^ 2 < n := by omega
      have hlo := Nat.sqrt_le' n
      have hup : n < (n.sqrt + 1) ^ 2 := Nat.sqrt_lt'.mp (by omega)
      have hub : n < n.sqrt ^ 2 + 2 * n.sqrt + 1 := by nlinarith only [hup]
      have htail : n - n.sqrt ^ 2 ≤ 2 * n.sqrt := by omega
      obtain ⟨hvalid, hsum⟩ := ih (n - n.sqrt ^ 2) hnlt
      rw [greedyRoots_pos (Nat.pos_of_ne_zero hn), totalSquares, hsum]
      refine ⟨⟨hs, ?_, hvalid⟩, by omega⟩
      rwa [hsum]

def sqsum (a b c d : ℕ) : ℕ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

private theorem sqResidue (a : ℕ) :
    (a % 2 = 1 ∧ a ^ 2 % 8 = 1) ∨
      (a % 2 = 0 ∧ (a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 4)) := by
  have hmod : a % 8 % 2 = a % 2 := Nat.mod_mod_of_dvd a (by decide : 2 ∣ 8)
  have hpow : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := Nat.pow_mod a 2 8
  have hlt : a % 8 < 8 := Nat.mod_lt a (by decide)
  revert hmod hpow hlt
  generalize a % 8 = r
  intro hmod hpow hlt
  interval_cases r <;> norm_num at * <;> tauto

private theorem residueSum (a b c d : ℕ) :
    sqsum a b c d % 8 =
      (a ^ 2 % 8 + b ^ 2 % 8 + c ^ 2 % 8 + d ^ 2 % 8) % 8 := by
  unfold sqsum
  conv_lhs =>
    rw [Nat.add_mod, Nat.add_mod (a ^ 2 + b ^ 2), Nat.add_mod (a ^ 2) (b ^ 2)]
  simp only [Nat.add_assoc, Nat.mod_add_mod]

/-- A sum of four squares divisible by 8 has four even roots. -/
theorem rootsEven {a b c d : ℕ} (h : 8 ∣ sqsum a b c d) :
    2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ d := by
  have hr := (Nat.dvd_iff_mod_eq_zero.mp h)
  rw [residueSum] at hr
  rcases sqResidue a with ⟨ha, ha'⟩ | ⟨ha, ha' | ha'⟩ <;>
    rcases sqResidue b with ⟨hb, hb'⟩ | ⟨hb, hb' | hb'⟩ <;>
    rcases sqResidue c with ⟨hc, hc'⟩ | ⟨hc, hc' | hc'⟩ <;>
    rcases sqResidue d with ⟨hd, hd'⟩ | ⟨hd, hd' | hd'⟩ <;>
    simp_all only [Nat.dvd_iff_mod_eq_zero, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, and_self]

/-- If the sum has a factor `4^(m+1)`, each root has a factor `2^m`. -/
theorem rootsDvdTwoPow (m : ℕ) {a b c d : ℕ} (h : 4 ^ (m + 1) ∣ sqsum a b c d) :
    2 ^ m ∣ a ∧ 2 ^ m ∣ b ∧ 2 ^ m ∣ c ∧ 2 ^ m ∣ d := by
  induction m generalizing a b c d with
  | zero => simp
  | succ m ih =>
    have h8 : 8 ∣ sqsum a b c d :=
      dvd_trans (dvd_trans (by decide : 8 ∣ 4 ^ 2)
        (pow_dvd_pow 4 (show 2 ≤ m + 1 + 1 by omega))) h
    rcases rootsEven h8 with ⟨⟨A, rfl⟩, ⟨B, rfl⟩, ⟨C, rfl⟩, ⟨D, rfl⟩⟩
    have hscale :
        sqsum (2 * A) (2 * B) (2 * C) (2 * D) = 4 * sqsum A B C D := by
      unfold sqsum
      ring
    rw [hscale, pow_succ'] at h
    have hr := Nat.dvd_of_mul_dvd_mul_left (show 0 < 4 by decide) h
    rcases ih hr with ⟨ha, hb, hc, hd⟩
    rw [pow_succ']
    exact ⟨Nat.mul_dvd_mul_left 2 ha, Nat.mul_dvd_mul_left 2 hb,
      Nat.mul_dvd_mul_left 2 hc, Nat.mul_dvd_mul_left 2 hd⟩

end OeisA401548
