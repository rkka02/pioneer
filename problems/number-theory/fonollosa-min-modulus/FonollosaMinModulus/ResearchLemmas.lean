import FonollosaMinModulus.Challenge
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Max

/-! Signed relations and subset-sum packings for the frozen definition. -/

namespace FonollosaMinModulus

open Finset

variable {N : ℕ} {A S T : Finset (ZMod N)}

/-- Every balanced integral relation with entries at least `-1` vanishes on a valid set. -/
theorem valid_iff_signed :
    IsValidMod A ↔ ∀ c : ZMod N → ℤ, (∀ x ∈ A, -1 ≤ c x) →
      ∑ x ∈ A, c x = 0 → ∑ x ∈ A, (c x : ZMod N) * x = 0 →
      ∀ x ∈ A, c x = 0 := by
  classical
  constructor
  · intro h c hlow hcount hsum
    let m (x : ZMod N) := (c x + 1).toNat
    have hm (x) (hx : x ∈ A) : (m x : ℤ) = c x + 1 :=
      Int.toNat_of_nonneg (by have := hlow x hx; omega)
    have hmc : ∑ x ∈ A, m x = A.card := by
      exact_mod_cast (show (∑ x ∈ A, (m x : ℤ)) = (A.card : ℤ) by
        rw [sum_congr rfl hm, sum_add_distrib, hcount]
        simp)
    have hmw : ∑ x ∈ A, (m x : ZMod N) * x = ∑ x ∈ A, x := by
      calc
        _ = ∑ x ∈ A, ((c x : ZMod N) * x + x) := by
          apply sum_congr rfl
          intro x hx
          have hcast := congrArg (Int.cast : ℤ → ZMod N) (hm x hx)
          push_cast at hcast
          rw [hcast, add_mul, one_mul]
        _ = _ := by rw [sum_add_distrib, hsum, zero_add]
    intro x hx
    have := hm x hx
    have := h m hmc hmw x hx
    omega
  · intro h m hcount hsum
    let c (x : ZMod N) : ℤ := m x - 1
    have hc : ∑ x ∈ A, c x = 0 := by
      simp [c, sum_sub_distrib, ← Nat.cast_sum, hcount]
    have hw : ∑ x ∈ A, (c x : ZMod N) * x = 0 := by
      simpa [c, sub_mul, sum_sub_distrib] using sub_eq_zero.mpr hsum
    intro x hx
    have := h c (fun z _ => by dsimp [c]; omega) hc hw x hx
    dsimp [c] at this
    omega

private def mark (S : Finset (ZMod N)) (x : ZMod N) : ℤ := if x ∈ S then 1 else 0

private theorem sum_mark (hS : S ⊆ A) : ∑ x ∈ A, mark S x = (S.card : ℤ) := by
  classical
  simp [mark, sum_ite_mem, inter_eq_right.mpr hS]

private theorem weight_mark (hS : S ⊆ A) :
    ∑ x ∈ A, (mark S x : ZMod N) * x = ∑ x ∈ S, x := by
  classical
  simp [mark, apply_ite, ite_mul, sum_ite_mem, inter_eq_right.mpr hS]

/-- A bad multiset is the replacement of a nonempty subset by the same number
of copies of elements outside that subset. Multiplicities outside `A` are ignored. -/
theorem valid_iff_no_replacement :
    IsValidMod A ↔ ∀ S ⊆ A, S.Nonempty → ∀ d : ZMod N → ℕ,
      (∀ x ∈ S, d x = 0) → (∑ x ∈ A, d x) = S.card →
      (∑ x ∈ A, (d x : ZMod N) * x) ≠ ∑ x ∈ S, x := by
  classical
  constructor
  · intro hA S hS hs d hd hc hw
    let c (x : ZMod N) : ℤ := d x - mark S x
    have hh := (valid_iff_signed.mp hA) c (by
      intro x _
      by_cases hx : x ∈ S <;> simp [c, mark, hx]) (by
      simp [c, sum_sub_distrib, sum_mark hS, ← Nat.cast_sum, hc]) (by
      simp [c, sub_mul, sum_sub_distrib, weight_mark hS, hw])
    obtain ⟨x, hx⟩ := hs
    have := hh x (hS hx)
    simp [c, mark, hx, hd x hx] at this
  · intro h
    apply valid_iff_signed.mpr
    intro c hl hc hw
    let S := A.filter fun x => c x = -1
    let d (x : ZMod N) := (c x).toNat
    have hS : S ⊆ A := filter_subset _ _
    have he (x) (hx : x ∈ A) : (d x : ℤ) = c x + mark S x := by
      have hcx := hl x hx
      by_cases hneg : c x = -1
      · simp [d, mark, S, hx, hneg]
      · simp [d, mark, S, hx, hneg, Int.toNat_of_nonneg (show 0 ≤ c x by omega)]
    have hcount : ∑ x ∈ A, d x = S.card := by
      exact_mod_cast (show (∑ x ∈ A, (d x : ℤ)) = (S.card : ℤ) by
        rw [sum_congr rfl he, sum_add_distrib, hc, zero_add, sum_mark hS])
    have hd (x) (hx : x ∈ S) : d x = 0 := by
      have hneg := (mem_filter.mp hx).2
      simp [d, hneg]
    by_cases hne : S.Nonempty
    · apply False.elim
      apply h S hS hne d hd hcount
      calc
        (∑ x ∈ A, (d x : ZMod N) * x) =
            ∑ x ∈ A, ((c x : ZMod N) * x + (mark S x : ZMod N) * x) := by
          apply sum_congr rfl
          intro x hx
          have hcast := congrArg (Int.cast : ℤ → ZMod N) (he x hx)
          push_cast at hcast
          rw [hcast, add_mul]
        _ = _ := by rw [sum_add_distrib, hw, zero_add, weight_mark hS]
    · have hnil := not_nonempty_iff_eq_empty.mp hne
      rw [hnil, card_empty] at hcount
      intro x hx
      have hzero := sum_eq_zero_iff.mp hcount x hx
      simpa [hzero, mark, hnil] using (he x hx).symm

/-- Extending a signed relation by zero proves heredity. -/
theorem valid_subset (hA : IsValidMod A) {B : Finset (ZMod N)} (hB : B ⊆ A) :
    IsValidMod B := by
  classical
  apply valid_iff_signed.mpr
  intro c hl hc hw x hx
  let d (z : ZMod N) : ℤ := if z ∈ B then c z else 0
  have hz := valid_iff_signed.mp hA d (by
    intro z _
    by_cases h : z ∈ B
    · simpa [d, h] using hl z h
    · simp [d, h]) (by
    simpa [d, sum_ite_mem, inter_eq_right.mpr hB] using hc) (by
    simpa [d, apply_ite, ite_mul, sum_ite_mem, inter_eq_right.mpr hB] using hw) x (hB hx)
  simpa [d, hx] using hz

/-- Every invertible affine change of residue coordinates preserves validity. -/
theorem valid_affine_iff (u : (ZMod N)ˣ) (t : ZMod N) :
    IsValidMod (A.image (fun x => (u : ZMod N) * x + t)) ↔ IsValidMod A := by
  classical
  have forward (B : Finset (ZMod N)) (w : (ZMod N)ˣ) (s : ZMod N) (hB : IsValidMod B) :
      IsValidMod (B.image (fun x => (w : ZMod N) * x + s)) := by
    let f (x : ZMod N) := (w : ZMod N) * x + s
    have hf : Function.Injective f := by
      intro x y h
      exact w.mul_right_inj.mp (add_right_cancel h)
    apply valid_iff_signed.mpr
    intro c hl hc hw y hy
    change y ∈ B.image f at hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    rw [sum_image hf.injOn] at hc hw
    have hz : (∑ z ∈ B, (c (f z) : ZMod N)) = 0 := by
      rw [← Int.cast_sum, (hc : ∑ z ∈ B, c (f z) = 0), Int.cast_zero]
    have hw' : (w : ZMod N) * (∑ z ∈ B, (c (f z) : ZMod N) * z) = 0 := by
      calc
        _ = (∑ z ∈ B, (c (f z) : ZMod N) * f z) - (∑ z ∈ B, (c (f z) : ZMod N)) * s := by
          rw [mul_sum, sum_mul, ← sum_sub_distrib]
          apply sum_congr rfl
          intro z _
          dsimp [f]
          ring
        _ = 0 := by rw [hw, hz]; simp
    exact (valid_iff_signed.mp hB) (fun z => c (f z))
      (fun z h => hl _ (mem_image_of_mem f h)) hc
      (w.mul_right_inj.mp (hw'.trans (mul_zero _).symm)) x hx
  constructor
  · intro h
    have hback := forward _ u⁻¹ (-((↑u⁻¹ : ZMod N) * t)) h
    simpa [image_image, Function.comp_def, mul_add, ← mul_assoc] using hback
  · exact forward A u t

/-- Integer adjustments outside the two subsets may be used to balance their sizes and sums. -/
theorem subsets_eq_of_balance (hA : IsValidMod A) (hS : S ⊆ A) (hT : T ⊆ A)
    (d : ZMod N → ℤ) (hlow : ∀ x ∈ A, -1 ≤ d x)
    (hoff : ∀ x ∈ S ∪ T, d x = 0)
    (hc : (S.card : ℤ) - T.card + ∑ x ∈ A, d x = 0)
    (hw : (∑ x ∈ S, x) - (∑ x ∈ T, x) + ∑ x ∈ A, (d x : ZMod N) * x = 0) :
    S = T := by
  classical
  let c (x : ZMod N) := mark S x - mark T x + d x
  have hzero := (valid_iff_signed.mp hA) c (by
    intro x hx
    by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;>
      simp_all [c, mark]) (by
    simpa [c, sum_add_distrib, sum_sub_distrib, sum_mark hS, sum_mark hT] using hc) (by
    simpa [c, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib,
      weight_mark hS, weight_mark hT] using hw)
  ext x
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T
  · simp [hs, ht]
  · have := hzero x (hS hs)
    simp [c, mark, hs, ht, hoff x (mem_union_left _ hs)] at this
  · have := hzero x (hT ht)
    simp [c, mark, hs, ht, hoff x (mem_union_right _ ht)] at this
  · simp [hs, ht]

private def spike (a : ZMod N) (v : ℤ) (x : ZMod N) : ℤ := if a = x then v else 0

private theorem sum_spike {a : ZMod N} (ha : a ∈ A) (v : ℤ) :
    ∑ x ∈ A, spike a v x = v := by classical simp [spike, ha]

private theorem weight_spike {a : ZMod N} (ha : a ∈ A) (v : ℤ) :
    ∑ x ∈ A, (spike a v x : ZMod N) * x = (v : ZMod N) * a := by
  classical
  simp [spike, apply_ite, ite_mul, ha]

/-- Inal's translated Boolean cube, for any pivot in the original frozen finset. -/
theorem anchored_injOn (hA : IsValidMod A) {a : ZMod N} (ha : a ∈ A) :
    Set.InjOn (fun S : Finset (ZMod N) => ∑ x ∈ S, (x - a)) ↑(A.erase a).powerset := by
  classical
  intro S hS T hT heq
  change S ∈ (A.erase a).powerset at hS
  change T ∈ (A.erase a).powerset at hT
  rw [mem_powerset] at hS hT
  wlog hcard : S.card ≤ T.card generalizing S T
  · symm
    apply this <;> first | assumption | exact heq.symm | omega
  let v : ℤ := T.card - S.card
  apply subsets_eq_of_balance hA (hS.trans (erase_subset ..)) (hT.trans (erase_subset ..))
    (spike a v)
  · intro x _
    simp [spike, v]
    split <;> omega
  · intro x hx
    have hx' : x ∈ A.erase a := (union_subset hS hT) hx
    simp [spike, (mem_erase.mp hx').1.symm]
  · rw [sum_spike ha]
    dsimp [v]
    omega
  · rw [weight_spike ha]
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at heq
    dsimp [v]
    push_cast
    linear_combination heq

/-- Universal modulus bound, in the frozen `IsValidMod` API. -/
theorem card_bound_of_valid [NeZero N] (hA : IsValidMod A) {a : ZMod N} (ha : a ∈ A) :
    2 ^ (A.card - 1) ≤ N := by
  classical
  have h := card_le_card_of_injOn (t := (univ : Finset (ZMod N))) _
    (fun _ _ => mem_univ _) (anchored_injOn hA ha)
  simpa [card_erase_of_mem ha, ZMod.card] using h

/-- A three-term arithmetic progression with distinct endpoints precludes validity. -/
theorem not_valid_of_midpoint {x y z : ZMod N}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (heq : x + z = y + y) :
    ¬ IsValidMod A := by
  classical
  intro hA
  have hp : ({x, z} : Finset _) ⊆ A := insert_subset hx (singleton_subset_iff.mpr hz)
  have hf := subsets_eq_of_balance (S := ∅) hA (empty_subset _) hp (spike y 2)
    (by intro t _; simp [spike]; split <;> decide)
    (by
      intro t ht
      simp only [empty_union, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp [spike, hxy.symm, hyz])
    (by simp [sum_spike hy, hxz])
    (by simp [weight_spike hy, hxz, heq, two_mul])
  have := congrArg Finset.card hf
  simp [hxz] at this

/-- Two exceptional coordinates can compensate an arbitrary difference of subset sizes. -/
theorem subsets_eq_of_two_pivots (hA : IsValidMod A) {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hS : S ⊆ (A.erase a).erase b) (hT : T ⊆ (A.erase a).erase b)
    (u v : ℤ) (hu : -1 ≤ u) (hv : -1 ≤ v)
    (hc : (S.card : ℤ) - T.card + u + v = 0)
    (hw : (∑ x ∈ S, x) - (∑ x ∈ T, x) + (u : ZMod N) * a + (v : ZMod N) * b = 0) :
    S = T := by
  classical
  have hsub : (A.erase a).erase b ⊆ A := (erase_subset ..).trans (erase_subset ..)
  apply subsets_eq_of_balance hA (hS.trans hsub) (hT.trans hsub)
    (fun x => spike a u x + spike b v x)
  · intro x _
    by_cases hax : a = x <;> by_cases hbx : b = x <;> simp_all [spike]
  · intro x hx
    obtain ⟨hxb, hx'⟩ := mem_erase.mp ((union_subset hS hT) hx)
    simp [spike, hxb.symm, (mem_erase.mp hx').1.symm]
  · simpa [sum_add_distrib, sum_spike ha, sum_spike hb, ← add_assoc] using hc
  · simpa [add_mul, sum_add_distrib, weight_spike ha, weight_spike hb, ← add_assoc] using hw

/-- Full forbidden interval for the signed displacement between two subset sums.
Both cardinalities are measured before removing their common elements. -/
theorem subsets_eq_of_pivot_interval (hA : IsValidMod A) {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hS : S ⊆ (A.erase a).erase b) (hT : T ⊆ (A.erase a).erase b)
    (j : ℤ) (hl : min 0 ((S.card : ℤ) - T.card) - 1 ≤ j)
    (hr : j ≤ max 0 ((S.card : ℤ) - T.card) + 1)
    (heq : (∑ x ∈ S, (x - a)) = (∑ x ∈ T, (x - a)) + (j : ZMod N) * (b - a)) :
    S = T := by
  classical
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at heq
  by_cases h : S.card ≤ T.card
  · apply subsets_eq_of_two_pivots hA ha hb hab hS hT ((T.card : ℤ) - S.card + j) (-j)
        (by omega) (by omega) (by omega)
    push_cast
    linear_combination heq
  · symm
    apply subsets_eq_of_two_pivots hA ha hb hab hT hS ((S.card : ℤ) - T.card - j) j
        (by omega) (by omega) (by omega)
    push_cast
    linear_combination -heq

/-- Across one step in the direction of the two pivots, distinct subsets cannot meet. -/
theorem subsets_eq_of_pivot_step (hA : IsValidMod A) {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hS : S ⊆ (A.erase a).erase b) (hT : T ⊆ (A.erase a).erase b)
    (j : ℤ) (hl : -1 ≤ j) (hr : j ≤ 1)
    (heq : (∑ x ∈ S, (x - a)) = (∑ x ∈ T, (x - a)) + (j : ZMod N) * (b - a)) :
    S = T := by
  exact subsets_eq_of_pivot_interval hA ha hb hab hS hT j (by omega) (by omega) heq

/-- If one difference has order three, three translates of a cube of dimension `|A|-2` fit. -/
theorem order_three_bound [NeZero N] (hA : IsValidMod A) {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hthree : 3 * (b - a) = 0) :
    3 * 2 ^ (A.card - 2) ≤ N := by
  classical
  let d := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  have h3 : 3 * d = 0 := hthree
  have hpm : d ≠ -d := by
    intro h
    apply hd
    linear_combination h3 - h
  let D : Finset (ZMod N) := {0, d, -d}
  have hD : D.card = 3 := by simp [D, hd, hpm, Ne.symm hd]
  have hdif (z w : ZMod N) (hz : z ∈ D) (hw : w ∈ D) :
      ∃ j : ℤ, -1 ≤ j ∧ j ≤ 1 ∧ w - z = (j : ZMod N) * d := by
    simp only [D, mem_insert, mem_singleton] at hz hw
    rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact ⟨0, by decide, by decide, by simp⟩
    · exact ⟨1, by decide, by decide, by simp⟩
    · exact ⟨-1, by decide, by decide, by simp⟩
    · exact ⟨-1, by decide, by decide, by simp⟩
    · exact ⟨0, by decide, by decide, by simp⟩
    · exact ⟨1, by decide, by decide, by push_cast; linear_combination -h3⟩
    · exact ⟨1, by decide, by decide, by simp⟩
    · exact ⟨-1, by decide, by decide, by push_cast; linear_combination h3⟩
    · exact ⟨0, by decide, by decide, by simp⟩
  let B := (A.erase a).erase b
  let f (p : ZMod N × Finset (ZMod N)) := p.1 + ∑ x ∈ p.2, (x - a)
  have hinj : Set.InjOn f ↑(D ×ˢ B.powerset) := by
    rintro ⟨z, S⟩ hp ⟨w, T⟩ hq he
    obtain ⟨hz, hS⟩ := mem_product.mp hp
    obtain ⟨hw, hT⟩ := mem_product.mp hq
    obtain ⟨j, hl, hr, hj⟩ := hdif z w hz hw
    change z + (∑ x ∈ S, (x - a)) = w + ∑ x ∈ T, (x - a) at he
    have hST := subsets_eq_of_pivot_step hA ha hb hab (mem_powerset.mp hS)
      (mem_powerset.mp hT) j hl hr (by
        change _ = _ + (j : ZMod N) * d
        rw [← hj]
        linear_combination he)
    change S = T at hST
    subst T
    exact Prod.ext (add_right_cancel he) rfl
  have h := card_le_card_of_injOn (t := (univ : Finset (ZMod N))) f (fun _ _ => mem_univ _) hinj
  have hb' : b ∈ A.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  simpa [B, hD, card_erase_of_mem hb', card_erase_of_mem ha, Nat.sub_sub, ZMod.card] using h

/-- A sum of exactly `k` binary coins with highest denomination `2^d`. -/
inductive BinaryCoins (d : ℕ) : ℕ → ℕ → Prop where
  | zero : BinaryCoins d 0 0
  | add {k v i : ℕ} : i ≤ d → BinaryCoins d k v → BinaryCoins d (k + 1) (v + 2 ^ i)

namespace BinaryCoins

private theorem raise {d k v : ℕ} (h : BinaryCoins d k v) : BinaryCoins (d + 1) k v := by
  induction h with
  | zero => exact .zero
  | add hi _ ih => exact .add (Nat.le_succ_of_le hi) ih

private theorem copies {d k v i : ℕ} (h : BinaryCoins d k v) (hi : i ≤ d) (q : ℕ) :
    BinaryCoins d (k + q) (v + q * 2 ^ i) := by
  induction q with
  | zero => simpa using h
  | succ q ih => simpa [Nat.succ_mul, Nat.add_assoc] using BinaryCoins.add hi ih

private theorem split_one {d k v : ℕ} (h : BinaryCoins d k v) (hlt : k < v) :
    BinaryCoins d (k + 1) v := by
  induction h with
  | zero => omega
  | @add k v i hi h ih =>
    cases i with
    | zero =>
      have hv : k < v := by simpa using hlt
      exact .add hi (ih hv)
    | succ i =>
      have hi' : i ≤ d := by omega
      simpa [pow_succ, Nat.mul_two, Nat.add_assoc] using
        BinaryCoins.add hi' (BinaryCoins.add hi' h)

private theorem pad {d k v : ℕ} (h : BinaryCoins d k v) {l : ℕ}
    (hkl : k ≤ l) (hlv : l ≤ v) : BinaryCoins d l v := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ l _ ih => exact (ih (by omega)).split_one (by omega)

private theorem digits (d v : ℕ) (hv : v < 2 ^ d) :
    ∃ k ≤ d, (v + 1 < 2 ^ d → k < d) ∧ BinaryCoins d k v := by
  induction d generalizing v with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at hv
    subst v
    exact ⟨0, le_rfl, by simp, .zero⟩
  | succ d ih =>
    rw [pow_succ] at hv ⊢
    by_cases hsmall : v < 2 ^ d
    · obtain ⟨k, hk, _, hrep⟩ := ih v hsmall
      exact ⟨k, by omega, by omega, hrep.raise⟩
    · obtain ⟨k, hk, hstrict, hrep⟩ := ih (v - 2 ^ d) (by omega)
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · intro h
        have := hstrict (by omega)
        omega
      · have hsum : (v - 2 ^ d) + 2 ^ d = v := by omega
        simpa only [hsum] using BinaryCoins.add (Nat.le_succ d) hrep.raise

/-- Every value from `d+2` through `4*2^d-2` can be paid with exactly `d+2` coins. -/
theorem cover_below (d v : ℕ) (hlo : d + 2 ≤ v) (hhi : v + 1 < 4 * 2 ^ d) :
    BinaryCoins d (d + 2) v := by
  let H := 2 ^ d
  have hH : 0 < H := Nat.two_pow_pos d
  let q := v / H
  let r := v % H
  have hr : r < H := Nat.mod_lt _ hH
  have hval : r + q * H = v := Nat.mod_add_div' _ _
  obtain ⟨k, hk, hstrict, hrep⟩ := digits d r hr
  have hq : q < 4 := (Nat.div_lt_iff_lt_mul hH).mpr (by dsimp [H]; omega)
  have hkq : k + q ≤ d + 2 := by
    by_cases h : q = 3
    · rw [h] at hval
      change v + 1 < 4 * H at hhi
      have := hstrict (by change r + 1 < H; omega)
      omega
    · omega
  have h := hrep.copies (le_refl d) q
  change BinaryCoins d (k + q) (r + q * H) at h
  rw [hval] at h
  exact h.pad hkq hlo

/-- The short interval immediately above `4*2^d` is covered too. -/
theorem cover_above (d j : ℕ) (hd : 4 ≤ d) (hj : j ≤ d) :
    BinaryCoins d (d + 2) (4 * 2 ^ d + j) := by
  have h0 := (BinaryCoins.zero (d := d)).copies (i := 0) (Nat.zero_le d) (j % 2)
  have h1 := h0.copies (i := 1) (by omega) (j / 2)
  have h := h1.copies (le_refl d) 4
  simp only [pow_zero, mul_one, zero_add, pow_one] at h
  have hj' : j % 2 + j / 2 * 2 + 4 * 2 ^ d = 4 * 2 ^ d + j := by omega
  rw [hj'] at h
  have hpow := Nat.lt_two_pow_self (n := d)
  exact h.pad (by omega) (by omega)

/-- A gap strictly between successive powers removes at least two ones from
the all-ones binary expansion. The resulting sum uses at most `d-1` coins. -/
theorem complement_gap {s g d : ℕ} (hs : s ≤ d) (hl : 2 ^ s < g) (hr : g < 2 ^ (s+1)) :
    ∃ k, k + 2 ≤ d + 1 ∧ BinaryCoins d k (2 ^ (d+1) - 1 - g) := by
  induction d, hs using Nat.le_induction with
  | base =>
    rw [pow_succ] at hr ⊢
    have hlt : 2 ^ s * 2 - 1 - g + 1 < 2 ^ s := by omega
    obtain ⟨k, _, hstrict, hrep⟩ := digits s (2 ^ s * 2 - 1 - g) (by omega)
    have := hstrict hlt
    exact ⟨k, by omega, hrep⟩
  | succ d hd ih =>
    obtain ⟨k, hk, hrep⟩ := ih
    have hbound := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ hd)
    have he : (2 ^ (d+1) - 1 - g) + 2 ^ (d+1) = 2 ^ (d+1+1) - 1 - g := by
      rw [pow_succ 2 (d+1)]
      omega
    exact ⟨k+1, by omega, he ▸ BinaryCoins.add (le_refl (d+1)) hrep.raise⟩

private theorem multiplicities {d k v : ℕ} (h : BinaryCoins d k v)
    (hcore : ∀ i ≤ d, ((2 ^ i : ℕ) : ZMod N) ∈ A) {x : ZMod N}
    (hout : ∀ i ≤ d, x ≠ ((2 ^ i : ℕ) : ZMod N)) :
    ∃ m : ZMod N → ℕ, m x = 0 ∧ (∑ a ∈ A, m a) = k ∧
      (∑ a ∈ A, (m a : ZMod N) * a) = (v : ZMod N) := by
  classical
  induction h with
  | zero => exact ⟨fun _ => 0, rfl, by simp, by simp⟩
  | @add k v i hi _ ih =>
    obtain ⟨m, hx, hc, hw⟩ := ih
    let b : ZMod N := ((2 ^ i : ℕ) : ZMod N)
    have hb : b ∈ A := hcore i hi
    refine ⟨fun a => m a + if b = a then 1 else 0, ?_, ?_, ?_⟩
    · have hbx : b ≠ x := (hout i hi).symm
      simp [hx, hbx]
    · simp [sum_add_distrib, hb, hc]
    · simp only [Nat.cast_add, apply_ite Nat.cast, Nat.cast_one, Nat.cast_zero, add_mul,
        ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq, ite_eq_left hb, hw]
      rfl


end BinaryCoins

/-- The all-ones residue and its first positive wrap for an arbitrary extra coin. -/
theorem binary_core_wrap {d : ℕ} (hd : 4 ≤ d) [NeZero N]
    (hlo : 2 * 2 ^ d ≤ N) (hhi : N < 4 * 2 ^ d)
    {x : ZMod N} (hx : x ∈ A) (hc : A.card = d + 2)
    (hcore : ∀ i ≤ d, ((2 ^ i : ℕ) : ZMod N) ∈ A)
    (hout : ∀ i ≤ d, x ≠ ((2 ^ i : ℕ) : ZMod N)) (hA : IsValidMod A) :
    (∑ a ∈ A, a).val < d + 2 ∧ (∑ a ∈ A, a).val + N + 1 = 4 * 2 ^ d := by
  classical
  let p : ZMod N := ∑ a ∈ A, a
  have noPay (v : ℕ) (hv : (v : ZMod N) = p) (h : BinaryCoins d (d + 2) v) : False := by
    obtain ⟨m, hm, hcnt, hsum⟩ := h.multiplicities hcore hout
    have := hA m (hcnt.trans hc.symm) (hsum.trans hv) x hx
    omega
  have hpN := p.val_lt
  have hp : p.val < d + 2 := by
    by_contra! h
    exact noPay _ (ZMod.natCast_zmod_val p) (BinaryCoins.cover_below _ _ h (by omega))
  have hwrap : ((p.val + N : ℕ) : ZMod N) = p := by simp
  have hpow := Nat.lt_two_pow_self (n := d)
  have he : p.val + N + 1 = 4 * 2 ^ d := by
    by_contra hn
    by_cases h : p.val + N + 1 < 4 * 2 ^ d
    · exact noPay _ hwrap (BinaryCoins.cover_below _ _ (by omega) h)
    · let j := p.val + N - 4 * 2 ^ d
      have hj : j ≤ d := by dsimp [j]; omega
      have hj' : 4 * 2 ^ d + j = p.val + N := by dsimp [j]; omega
      exact noPay _ hwrap (hj' ▸ BinaryCoins.cover_above d j hd hj)
  exact ⟨hp, he⟩

/-- A binary core gives the unconditional lower bound `2^n - n ≤ N`, for `n = d+2`. -/
theorem binary_core_lower_bound {d : ℕ} (hd : 4 ≤ d) [NeZero N]
    {x : ZMod N} (hx : x ∈ A) (hc : A.card = d + 2)
    (hcore : ∀ i ≤ d, ((2 ^ i : ℕ) : ZMod N) ∈ A)
    (hout : ∀ i ≤ d, x ≠ ((2 ^ i : ℕ) : ZMod N)) (hA : IsValidMod A) :
    4 * 2 ^ d ≤ N + (d + 2) := by
  by_cases hhi : N < 4 * 2 ^ d
  · have hlo := card_bound_of_valid hA hx
    rw [hc, show d + 2 - 1 = d + 1 by omega, pow_succ, Nat.mul_comm] at hlo
    obtain ⟨hp, he⟩ := binary_core_wrap hd hlo hhi hx hc hcore hout hA
    omega
  · omega

/-- Below `2^n`, a valid extension of `n-1` consecutive binary coins is forced.
Here `n = d+2` and the extra residue is `x`. -/
theorem binary_extension_rigidity {d : ℕ} (hd : 4 ≤ d) [NeZero N]
    (hlo : 2 * 2 ^ d ≤ N) (hhi : N < 4 * 2 ^ d)
    {x : ZMod N} (hx : x ∈ A) (hc : A.card = d + 2)
    (hcore : ∀ i ≤ d, ((2 ^ i : ℕ) : ZMod N) ∈ A)
    (hout : ∀ i ≤ d, x ≠ ((2 ^ i : ℕ) : ZMod N)) (hA : IsValidMod A) :
    x = ((2 ^ (d + 1) : ℕ) : ZMod N) := by
  classical
  let p : ZMod N := ∑ a ∈ A, a
  have he : p.val + N + 1 = 4 * 2 ^ d := (binary_core_wrap hd hlo hhi hx hc hcore hout hA).2
  let coins : ℕ → ZMod N := fun i => ((2 ^ i : ℕ) : ZMod N)
  let I := range (d + 1)
  have hinj : Set.InjOn coins ↑I := by
    intro i hi j hj hij
    have hi' : i ≤ d := by simpa [I, Nat.lt_succ_iff] using hi
    have hj' : j ≤ d := by simpa [I, Nat.lt_succ_iff] using hj
    have hiN : 2 ^ i < N := by have := Nat.pow_le_pow_right (by decide : 0 < 2) hi'; omega
    have hjN : 2 ^ j < N := by have := Nat.pow_le_pow_right (by decide : 0 < 2) hj'; omega
    have h := congrArg ZMod.val hij
    change ((2 ^ i : ℕ) : ZMod N).val = ((2 ^ j : ℕ) : ZMod N).val at h
    rw [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] at h
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) h
  have hout' : x ∉ I.image coins := by
    intro hin
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hin
    exact hout i (by simpa [I, Nat.lt_succ_iff] using hi) rfl
  have hEq : insert x (I.image coins) = A := by
    apply eq_of_subset_of_card_le
    · apply insert_subset hx
      intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
      exact hcore i (by simpa [I, Nat.lt_succ_iff] using hi)
    · rw [card_insert_of_notMem hout', card_image_of_injOn hinj, hc]
      simp [I]
  have hgeom (t : ℕ) : (∑ i ∈ range t, (2 : ZMod N) ^ i) + 1 = 2 ^ t := by
    induction t with
    | zero => simp
    | succ t ih => rw [sum_range_succ, pow_succ]; linear_combination ih
  have hpsum : p + 1 = x + (2 : ZMod N) ^ (d + 1) := by
    change (∑ a ∈ A, a) + 1 = _
    rw [← hEq, sum_insert hout', sum_image hinj, add_assoc]
    simpa [I, coins] using congrArg (x + ·) (hgeom (d + 1))
  have he' := congrArg (Nat.cast : ℕ → ZMod N) he
  push_cast at he' ⊢
  simp only [ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero] at he'
  rw [hpsum, pow_succ] at he'
  rw [pow_succ]
  linear_combination he'

/-- The conjectured lower bound for *any* extra residue adjoining the binary
core, proved directly for the frozen validity predicate. -/
theorem minModulus_le_of_binary_core {d : ℕ} (hd : 4 ≤ d) [NeZero N]
    {x : ZMod N} (hx : x ∈ A) (hc : A.card = d + 2)
    (hcore : ∀ i ≤ d, ((2 ^ i : ℕ) : ZMod N) ∈ A)
    (hout : ∀ i ≤ d, x ≠ ((2 ^ i : ℕ) : ZMod N)) (hA : IsValidMod A) :
    minModulus (d + 2) ≤ N := by
  classical
  by_contra! bad
  let s := Nat.log 2 (d+2)
  have hpow4 : 2 ^ (d + 2) = 4 * 2 ^ d := by rw [pow_add]; omega
  change N < 2 ^ (d+2) - 2 ^ s at bad
  rw [hpow4] at bad
  have hlo := card_bound_of_valid hA hx
  rw [hc, show d + 2 - 1 = d + 1 by omega, pow_succ, Nat.mul_comm] at hlo
  have hhi : N < 4 * 2 ^ d := bad.trans_le (Nat.sub_le ..)
  let p : ZMod N := ∑ a ∈ A, a
  obtain ⟨hp, hwrap⟩ := binary_core_wrap hd hlo hhi hx hc hcore hout hA
  change p.val < d + 2 at hp
  change p.val + N + 1 = 4 * 2 ^ d at hwrap
  let g := 4 * 2 ^ d - N
  have hg : g ≤ d+2 := by dsimp [g]; omega
  have hpow := Nat.lt_two_pow_self (n := d)
  have hs : s ≤ d := by
    have hlt : d+2 < 2 ^ (d+1) := by rw [pow_succ]; omega
    have := Nat.log_lt_of_lt_pow (by omega : d+2 ≠ 0) hlt
    dsimp [s]
    omega
  have hlow : 2 ^ s < g := by dsimp [g]; omega
  have hhigh : g < 2 ^ (s+1) :=
    lt_of_le_of_lt hg (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _)
  let v := 2 ^ (d+1) - 1 - g
  obtain ⟨k, hk, hrep⟩ := BinaryCoins.complement_gap hs hlow hhigh
  have hv : d-1 ≤ v := by dsimp [v]; rw [pow_succ]; omega
  have hpaid : BinaryCoins d (d-1) v := hrep.pad (by omega) hv
  obtain ⟨m, hmx, hmc, hmw⟩ := hpaid.multiplicities hcore hout
  have hextra := binary_extension_rigidity hd hlo hhi hx hc hcore hout hA
  have hvalue : v + 3 * 2 ^ (d+1) = p.val + 2*N := by
    dsimp [v, g]
    rw [pow_succ]
    omega
  have hmod := congrArg (Nat.cast : ℕ → ZMod N) hvalue
  push_cast at hmod hextra
  simp only [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val] at hmod
  let m' (a : ZMod N) := m a + if x = a then 3 else 0
  have hcount : ∑ a ∈ A, m' a = A.card := by
    simp [m', sum_add_distrib, hx, hmc, hc]
    omega
  have hweight : ∑ a ∈ A, (m' a : ZMod N) * a = p := by
    simp only [m', Nat.cast_add, apply_ite Nat.cast, Nat.cast_ofNat, Nat.cast_zero,
      add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq, ite_eq_left hx, hmw]
    rw [hextra]
    exact hmod
  have := hA m' hcount hweight x hx
  simp [m', hmx] at this

/-- Sharp lower bound as a containment test on the original set, allowing
translation and any unit multiplier. -/
theorem minModulus_le_of_affine_binary_core {d : ℕ} (hd : 4 ≤ d) [NeZero N]
    (u : (ZMod N)ˣ) (t : ZMod N) (hc : A.card = d + 2) (hA : IsValidMod A)
    (hcore : ∀ i ≤ d, (u : ZMod N) * ((2 ^ i : ℕ) : ZMod N) + t ∈ A) :
    minModulus (d + 2) ≤ N := by
  classical
  let undo (z : ZMod N) := (↑u⁻¹ : ZMod N) * z + -((↑u⁻¹ : ZMod N) * t)
  let B := A.image undo
  have hB : IsValidMod B := (valid_affine_iff _ _).mpr hA
  have hinj : Function.Injective undo :=
    fun _ _ h => (u⁻¹).mul_right_inj.mp (add_right_cancel h)
  have hcard : B.card = d+2 := (card_image_of_injective _ hinj).trans hc
  let coin (i : ℕ) := ((2 ^ i : ℕ) : ZMod N)
  have hcoins (i : ℕ) (hi : i ≤ d) : coin i ∈ B := by
    refine mem_image.mpr ⟨_, hcore i hi, ?_⟩
    simp [undo, coin, mul_add, ← mul_assoc]
  have hlt : ((range (d+1)).image coin).card < B.card := by
    apply lt_of_le_of_lt card_image_le
    simp [hcard]
  obtain ⟨x, hx, hout⟩ := exists_mem_notMem_of_card_lt_card hlt
  apply minModulus_le_of_binary_core hd hx hcard hcoins _ hB
  intro i hi he
  exact hout (he ▸ mem_image_of_mem coin (mem_range.mpr (by omega)))

end FonollosaMinModulus

namespace FonollosaMinModulus
open Finset
namespace RankPacking

variable {α : Type*} [LinearOrder α]

private def precedes (W : Finset α) (rev : Bool) (x y : α) : Prop :=
  (x ∈ W ∧ y ∉ W) ∨ ((x ∈ W ↔ y ∈ W) ∧ (if rev then y < x else x < y))

private lemma precedes_asymm {W : Finset α} {rev : Bool} {x y : α}
    (h : precedes W rev x y) : ¬ precedes W rev y x := by
  cases rev <;> simp only [precedes, Bool.false_eq_true, reduceIte, ↓reduceIte] at * <;> grind

private def toggle (W : Finset α) (x : α) := if x ∈ W then W.erase x else insert x W

private lemma mem_toggle {W : Finset α} {x y : α} :
    y ∈ toggle W x ↔ if y = x then y ∉ W else y ∈ W := by
  by_cases e : y = x <;> by_cases h : x ∈ W <;> simp_all [toggle]

private lemma toggle_ne (W : Finset α) (x : α) : toggle W x ≠ W := by
  intro h
  have h' : x ∈ toggle W x ↔ x ∈ W := by rw [h]
  rw [mem_toggle] at h'
  simp at h'

private lemma toggle_inj (W : Finset α) {x y : α} (h : toggle W x = toggle W y) : x = y := by
  by_contra hn
  have h' : x ∈ toggle W x ↔ x ∈ toggle W y := by rw [h]
  simp [mem_toggle, hn] at h'

/-- A disjoint nonempty pair of sets of coordinates in a Boolean cube. -/
private structure Window (α : Type*) [LinearOrder α] where
  left : Finset α
  right : Finset α
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disj : Disjoint left right

private def Window.both (w : Window α) := w.left ∪ w.right
private def Window.lo (w : Window α) := w.both.min' (w.left_nonempty.mono subset_union_left)
private def Window.hi (w : Window α) := w.both.max' (w.left_nonempty.mono subset_union_left)

private lemma Window.lo_mem (w : Window α) : w.lo ∈ w.both := min'_mem _ _
private lemma Window.hi_mem (w : Window α) : w.hi ∈ w.both := max'_mem _ _
private lemma Window.lo_le (w : Window α) {x : α} (h : x ∈ w.both) : w.lo ≤ x := min'_le _ _ h
private lemma Window.le_hi (w : Window α) {x : α} (h : x ∈ w.both) : x ≤ w.hi := le_max' _ _ h

private lemma Window.ends_ne (w : Window α) : w.lo ≠ w.hi := by
  intro h
  obtain ⟨x,hx⟩ := w.left_nonempty
  obtain ⟨y,hy⟩ := w.right_nonempty
  have ex : x = w.lo := le_antisymm ((w.le_hi (mem_union_left _ hx)).trans h.ge) (w.lo_le (mem_union_left _ hx))
  have ey : y = w.lo := le_antisymm ((w.le_hi (mem_union_right _ hy)).trans h.ge) (w.lo_le (mem_union_right _ hy))
  exact disjoint_left.mp w.disj hx ((ex.trans ey.symm).symm ▸ hy)

private def Window.encode (w : Window α) (S : Finset α) (i : Fin 4) : Finset α × Bool :=
  if i = 0 then (S,false) else if i = 1 then (S,true) else
  if i = 2 then (toggle S w.lo, decide (w.lo ∈ w.right))
  else (toggle S w.hi, decide (w.hi ∈ w.left))

private lemma Window.encode_inj (w : Window α) (S : Finset α) :
    Function.Injective (w.encode S) := by
  intro i j h
  have he := w.ends_ne
  have hl := toggle_ne S w.lo
  have hh := toggle_ne S w.hi
  have ht : toggle S w.lo ≠ toggle S w.hi := fun h => he (toggle_inj S h)
  fin_cases i <;> fin_cases j <;> simp_all [Window.encode, eq_comm]

private lemma Window.encode_inside (w : Window α) {S R : Finset α} (hS : S ⊆ R)
    (hw : w.both ⊆ R) (i : Fin 4) : (w.encode S i).1 ⊆ R := by
  have aux (x : α) (hx : x ∈ R) : toggle S x ⊆ R := by
    intro y hy
    by_cases h : y = x
    · simpa [h] using hx
    · exact hS (by simpa [mem_toggle,h] using hy)
  fin_cases i <;> simp [Window.encode, hS, aux _ (hw w.lo_mem), aux _ (hw w.hi_mem)]

private lemma Window.decode (w : Window α) {S : Finset α} (hL : w.left ⊆ S)
    (hR : Disjoint S w.right) (i : Fin 4) :
    (w.encode S i).1 \ w.right ∪ w.left = S := by
  have none := disjoint_left.mp hR
  have aux {x : α} (hx : x ∈ w.both) : toggle S x \ w.right ∪ w.left = S := by
    ext y
    by_cases e : y=x
    · subst y
      rcases mem_union.mp hx with h|h
      · simp [h,hL h]
      · have hs : x ∉ S := fun m => none m h
        have hl : x ∉ w.left := fun m => hs (hL m)
        simp [h,hs,hl]
    · simp only [mem_union,mem_sdiff,mem_toggle,ite_eq_right e]
      grind
  have base : S \ w.right ∪ w.left = S := by ext x; simp only [mem_union,mem_sdiff]; grind
  fin_cases i <;> simp [Window.encode, base, aux w.lo_mem, aux w.hi_mem]

private lemma sep_toggle {S D C : Finset α} {x : α} (rev : Bool) (hD : D ⊆ S)
    (hC : Disjoint S C)
    (hleft : x ∈ D → ∀ c ∈ C, if rev then c < x else x < c)
    (hright : x ∈ C → ∀ d ∈ D, if rev then x < d else d < x) :
    ∀ d ∈ D, ∀ c ∈ C, precedes (toggle S x) rev d c := by
  intro d hd c hc
  have hs := hD hd
  have hn : c ∉ S := fun h => disjoint_left.mp hC h hc
  have ne : d ≠ c := fun h => hn (h ▸ hs)
  by_cases e : d=x
  · subst d
    exact Or.inr ⟨by simp [mem_toggle,ne.symm,hs,hn], hleft hd c hc⟩
  by_cases f : c=x
  · subst c
    exact Or.inr ⟨by simp [mem_toggle,e,hs,hn], hright hc d hd⟩
  exact Or.inl ⟨by simpa [mem_toggle,e] using hs, by simpa [mem_toggle,f] using hn⟩

private lemma Window.separates (w : Window α) {S : Finset α} (hL : w.left ⊆ S)
    (hR : Disjoint S w.right) (i : Fin 4) :
    ∀ d ∈ w.left, ∀ c ∈ w.right, precedes (w.encode S i).1 (w.encode S i).2 d c := by
  have base (rev : Bool) : ∀ d ∈ w.left, ∀ c ∈ w.right, precedes S rev d c :=
    fun _ hd _ hc => Or.inl ⟨hL hd, fun h => disjoint_left.mp hR h hc⟩
  have dl := disjoint_left.mp w.disj
  fin_cases i
  · exact base false
  · exact base true
  · apply sep_toggle _ hL hR
    · intro h c hc
      have hn := dl h
      have ne : w.lo ≠ c := fun e => hn (e ▸ hc)
      simpa [Window.encode,hn] using lt_of_le_of_ne (w.lo_le (mem_union_right _ hc)) ne
    · intro h d hd
      have ne : w.lo ≠ d := fun e => dl hd (e ▸ h)
      simpa [Window.encode,h] using lt_of_le_of_ne (w.lo_le (mem_union_left _ hd)) ne
  · apply sep_toggle _ hL hR
    · intro h c hc
      have ne : c ≠ w.hi := fun e => dl h (e ▸ hc)
      simpa [Window.encode,h] using lt_of_le_of_ne (w.le_hi (mem_union_right _ hc)) ne
    · intro h d hd
      have hn : w.hi ∉ w.left := fun hl => dl hl h
      have ne : d ≠ w.hi := fun e => hn (e ▸ hd)
      simpa [Window.encode,hn] using lt_of_le_of_ne (w.le_hi (mem_union_left _ hd)) ne

/-- Comparable windows are separated by a Boolean cut and either tie order.
Two opposite endpoint toggles give the other two encodings. -/
private theorem window_bound (R : Finset α) (E : Finset (Finset α)) (W : Finset α → Window α)
    (hsub : E ⊆ R.powerset)
    (hW : ∀ S ∈ E, (W S).left ⊆ S ∧ Disjoint S (W S).right ∧ (W S).both ⊆ R)
    (cross : ∀ S ∈ E, ∀ T ∈ E, W S ≠ W T →
      ∃ x ∈ (W S).left, x ∈ (W T).right) :
    2 * E.card ≤ R.powerset.card := by
  classical
  let f (p : Fin 4 × Finset α) := (W p.2).encode p.2 p.1
  have hj : Set.InjOn f ↑((univ : Finset (Fin 4)) ×ˢ E) := by
    rintro ⟨i,S⟩ hS ⟨j,T⟩ hT he
    have hs := (mem_product.mp hS).2
    have ht := (mem_product.mp hT).2
    change (W S).encode S i = (W T).encode T j at he
    obtain ⟨sl,sr,_⟩ := hW S hs
    obtain ⟨tl,tr,_⟩ := hW T ht
    have ww : W S = W T := by
      by_contra hn
      obtain ⟨d,hd,h'd⟩ := cross S hs T ht hn
      obtain ⟨c,hc,h'c⟩ := cross T ht S hs (Ne.symm hn)
      have h1 := (W S).separates sl sr i d hd c h'c
      rw [he] at h1
      exact precedes_asymm h1 ((W T).separates tl tr j c hc d h'd)
    have de := (W S).decode sl sr i
    rw [he,ww] at de
    have st := de.symm.trans ((W T).decode tl tr j)
    subst T
    exact Prod.ext ((W S).encode_inj S he) rfl
  have h := card_le_card_of_injOn (t := R.powerset ×ˢ (univ : Finset Bool)) f (by
    rintro ⟨i,S⟩ hp
    have hs := (mem_product.mp hp).2
    exact mem_product.mpr ⟨mem_powerset.mpr ((W S).encode_inside (mem_powerset.mp (hsub hs))
      (hW S hs).2.2 i),mem_univ _⟩) hj
  simp only [card_product,card_univ,Fintype.card_fin,Fintype.card_bool] at h
  omega


private lemma Window.eq_of_parts {v w : Window α} (h : v.left=w.left) (h' : v.right=w.right) :
    v=w := by cases v; cases w; congr

variable {N : ℕ} {A R : Finset (ZMod N)}

/-- Different equal-length exchanges for one fixed displacement must cross in both directions. -/
theorem equal_exchanges_cross (hA : IsValidMod A) {S T U V : Finset (ZMod N)}
    (hs : S ⊆ A) (ht : T ⊆ A) (hu : U ⊆ A) (hv : V ⊆ A)
    (hst : S.card=T.card) (huv : U.card=V.card)
    (he : (∑ x ∈ T, x) - (∑ x ∈ S, x) = (∑ x ∈ V, x) - (∑ x ∈ U, x))
    (hd : Disjoint (S \ T) (V \ U)) : S \ T = U \ V ∧ T \ S = V \ U := by
  classical
  let c (x : ZMod N) := mark T x - mark S x + mark U x - mark V x
  have hc := valid_iff_signed.mp hA c (by
    intro x _
    have hbad : x ∈ S \ T → x ∉ V \ U := fun h => disjoint_left.mp hd h
    simp only [mem_sdiff] at hbad
    dsimp [c,mark]
    split_ifs <;> simp_all) (by simp [c,sum_sub_distrib,sum_add_distrib,sum_mark hs,
      sum_mark ht,sum_mark hu,sum_mark hv,hst,huv]) (by
    simp [c,sub_mul,add_mul,sum_sub_distrib,sum_add_distrib,
      weight_mark hs,weight_mark ht,weight_mark hu,weight_mark hv]
    linear_combination he)
  have eqbits (x : ZMod N) : mark T x - mark S x + mark U x - mark V x = 0 := by
    by_cases h : x ∈ A
    · exact hc x h
    · have h1 : x ∉ S := fun m => h (hs m)
      have h2 : x ∉ T := fun m => h (ht m)
      have h3 : x ∉ U := fun m => h (hu m)
      have h4 : x ∉ V := fun m => h (hv m)
      simp [mark,h1,h2,h3,h4]
  constructor <;> ext x <;> have H := eqbits x <;> simp only [mem_sdiff] <;>
    dsimp [mark] at H <;> split_ifs at H <;> simp_all

/-- At most half the subsets can move by a fixed nonzero displacement while retaining
their cardinality. Both the source and the destination lie in the same subcube. -/
theorem equal_rank_half [NeZero N] (hA : IsValidMod A) (hR : R ⊆ A) (g : ZMod N) (hg : g ≠ 0) :
    2 * (R.powerset.filter (fun S => ∃ T ∈ R.powerset, T.card = S.card ∧
      (∑ x ∈ T, x) = (∑ x ∈ S, x) + g)).card ≤ R.powerset.card := by
  classical
  let ord := LinearOrder.lift' ZMod.val (ZMod.val_injective N)
  let : LinearOrder (ZMod N) := { ord with
    toDecidableEq := ZMod.decidableEq N
    compare := fun x y => @compareOfLessAndEq _ x y ord.toLT (ord.toDecidableLT x y) (ZMod.decidableEq N)
    compare_eq_compareOfLessAndEq := fun _ _ => rfl }
  let E := R.powerset.filter (fun S => ∃ T ∈ R.powerset, T.card = S.card ∧
      (∑ x ∈ T, x) = (∑ x ∈ S, x) + g)
  change 2 * E.card ≤ _
  by_cases hempty : E.Nonempty
  · obtain ⟨s₀,hs₀⟩ := hempty
    have partner (S) (hS : S ∈ E) := (mem_filter.mp hS).2
    let mate (S) (hS : S ∈ E) := Classical.choose (partner S hS)
    have prop (S) (hS : S ∈ E) := Classical.choose_spec (partner S hS)
    have parts (S) (hS : S ∈ E) : (S \ mate S hS).Nonempty ∧ (mate S hS \ S).Nonempty := by
      obtain ⟨_,hcard,hw⟩ := prop S hS
      change (mate S hS).card = S.card at hcard
      change (∑ x ∈ mate S hS,x) = _ at hw
      have neq : mate S hS ≠ S := by intro h; rw [h] at hw; exact hg (by linear_combination -hw)
      constructor
      · apply sdiff_nonempty.mpr
        exact fun h => neq (eq_of_subset_of_card_le h hcard.le).symm
      · apply sdiff_nonempty.mpr
        exact fun h => neq (eq_of_subset_of_card_le h hcard.ge)
    let mk (S) (hS : S ∈ E) : Window (ZMod N) :=
      ⟨S \ mate S hS, mate S hS \ S, (parts S hS).1,(parts S hS).2, by
        apply disjoint_left.mpr; simp only [mem_sdiff]; grind⟩
    let W (S) := if h : S ∈ E then mk S h else mk s₀ hs₀
    apply window_bound R E W (filter_subset ..)
    · intro S hs
      have hr := mem_powerset.mp (mem_filter.mp hs).1
      have hm := mem_powerset.mp (prop S hs).1
      change mate S hs ⊆ R at hm
      simp only [W,dite_eq_left hs,mk,Window.both]
      exact ⟨sdiff_subset, disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hy).2 hx),
        union_subset (sdiff_subset.trans hr) (sdiff_subset.trans hm)⟩
    · intro S hs U hu hn
      by_contra no
      have hd : Disjoint (S \ mate S hs) (mate U hu \ U) := by
        apply disjoint_left.mpr
        intro x hx hy
        exact no ⟨x,by simpa [W,hs,mk] using hx,by simpa [W,hu,mk] using hy⟩
      obtain ⟨tR,tc,tw⟩ := prop S hs
      obtain ⟨vR,vc,vw⟩ := prop U hu
      have ee := equal_exchanges_cross hA ((mem_powerset.mp (mem_filter.mp hs).1).trans hR)
        ((mem_powerset.mp tR).trans hR) ((mem_powerset.mp (mem_filter.mp hu).1).trans hR)
        ((mem_powerset.mp vR).trans hR) tc.symm vc.symm (by rw [tw,vw]; ring) hd
      apply hn
      apply Window.eq_of_parts <;> simp only [W,dite_eq_left hs,dite_eq_left hu,mk]
      · exact ee.1
      · exact ee.2
  · simp [not_nonempty_iff_eq_empty.mp hempty]

end RankPacking
end FonollosaMinModulus

namespace FonollosaMinModulus
open Finset
namespace RankPacking
variable {N : ℕ} {A : Finset (ZMod N)}

/-- Five slots around each rank-centred subset sum, using two copies of the group.
Only an equal-rank shift by twice the pivot difference can identify two slots. -/
theorem five_slots [NeZero N] (hA : IsValidMod A) {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    let R := (A.erase a).erase b
    let E := R.powerset.filter (fun S => ∃ T ∈ R.powerset, T.card = S.card ∧
      (∑ x ∈ T, x) = (∑ x ∈ S, x) + 2*(b-a))
    5 * R.powerset.card ≤ 2 * N + E.card := by
  classical
  let R := (A.erase a).erase b
  let K := R.powerset
  let d := b-a
  let F (S : Finset (ZMod N)) := ∑ x ∈ S, (x-a)
  let E := K.filter (fun S => ∃ T ∈ K, T.card = S.card ∧
      (∑ x ∈ T, x) = (∑ x ∈ S, x) + 2*d)
  let allSlots := range 5 ×ˢ K
  let cut := ({4} : Finset ℕ) ×ˢ E
  let D := allSlots \ cut
  let height (i : ℕ) (S : Finset (ZMod N)) : ℤ := (i : ℤ) - S.card
  let f (p : ℕ × Finset (ZMod N)) :=
    (F p.2 + ((height p.1 p.2 / 2 : ℤ) : ZMod N)*d, height p.1 p.2 % 2)
  have hcut : cut ⊆ allSlots := product_subset_product (by decide) (filter_subset ..)
  have props (i : ℕ) (S) (hp : (i,S) ∈ D) : i < 5 ∧ S ∈ K ∧ (i=4 → S ∉ E) := by
    obtain ⟨hh,nh⟩ := mem_sdiff.mp hp
    obtain ⟨hi,hs⟩ := mem_product.mp hh
    exact ⟨mem_range.mp hi,hs,fun he h => nh (mem_product.mpr ⟨mem_singleton.mpr he,h⟩)⟩
  have collision {i j : ℕ} {S T : Finset (ZMod N)}
      (hi : (i,S) ∈ D) (hj : (j,T) ∈ D) (he : f (i,S) = f (j,T)) :
      ¬ (i=4 ∧ j=0 ∧ S.card=T.card) := by
    rintro ⟨rfl,rfl,eq⟩
    obtain ⟨_,hs,del⟩ := props _ _ hi
    obtain ⟨_,ht,_⟩ := props _ _ hj
    apply del rfl
    refine mem_filter.mpr ⟨hs,T,ht,eq.symm,?_⟩
    have hw := congrArg Prod.fst he
    change F S + ((height 4 S/2 : ℤ) : ZMod N)*d =
      F T + ((height 0 T/2 : ℤ) : ZMod N)*d at hw
    have sz : height 4 S/2 = height 0 T/2 + 2 := by dsimp [height]; omega
    rw [sz, Int.cast_add] at hw
    simp only [F,sum_sub_distrib,sum_const,nsmul_eq_mul,eq,Int.cast_ofNat] at hw
    linear_combination -hw
  have inj : Set.InjOn f ↑D := by
    rintro ⟨i,S⟩ hi ⟨j,T⟩ hj he
    obtain ⟨hib,hs,_⟩ := props _ _ hi
    obtain ⟨hjb,ht,_⟩ := props _ _ hj
    have bad := collision hi hj he
    have bad' := collision hj hi he.symm
    have hp := congrArg Prod.snd he
    change height i S % 2 = height j T % 2 at hp
    have hw := congrArg Prod.fst he
    change F S + ((height i S/2 : ℤ) : ZMod N)*d =
      F T + ((height j T/2 : ℤ) : ZMod N)*d at hw
    let v := height j T / 2 - height i S / 2
    have hm : 2*v = ((j : ℤ)-i) + ((S.card : ℤ)-T.card) := by
      dsimp [v,height] at *; omega
    have hl : min 0 ((S.card : ℤ)-T.card)-1 ≤ v := by omega
    have hr : v ≤ max 0 ((S.card : ℤ)-T.card)+1 := by omega
    have hsT := subsets_eq_of_pivot_interval hA ha hb hab (mem_powerset.mp hs) (mem_powerset.mp ht)
      v hl hr (by change F S = F T + (v : ZMod N)*d; dsimp [v]; push_cast; linear_combination hw)
    subst T
    have hv : (v : ZMod N)*d=0 := by dsimp [v]; push_cast; linear_combination -hw
    have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
    have zero : v=0 := by
      have rangeV : v = -1 ∨ v = 0 ∨ v = 1 := by omega
      rcases rangeV with h|h|h
      · simp [h,hd] at hv
      · exact h
      · simp [h,hd] at hv
    exact Prod.ext (by omega) rfl
  have h := card_le_card_of_injOn (t := (univ : Finset (ZMod N)) ×ˢ ({0,1} : Finset ℤ)) f
    (by
      rintro ⟨i,S⟩ _
      apply mem_product.mpr
      refine ⟨mem_univ _,?_⟩
      change height i S % 2 ∈ ({0,1} : Finset ℤ)
      simp only [mem_insert,mem_singleton]; omega) inj
  have cv := card_sdiff_add_card_eq_card hcut
  change D.card + cut.card = allSlots.card at cv
  simp [allSlots,cut] at cv
  simp [ZMod.card] at h
  change 5*K.card ≤ 2*N+E.card
  omega

/-- The 9/16 lower bound for any pair with non-involutory difference. -/
theorem nine_sixteenths_of_pivots [NeZero N] (hA : IsValidMod A) {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hd : 2*(b-a) ≠ 0) :
    9 * 2^(A.card-2) ≤ 4*N := by
  have h := five_slots hA ha hb hab
  dsimp only at h
  have e := equal_rank_half (R := (A.erase a).erase b) hA
    ((erase_subset ..).trans (erase_subset ..)) _ hd
  have hb' := mem_erase.mpr ⟨hab.symm,hb⟩
  simp only [card_powerset,card_erase_of_mem hb',card_erase_of_mem ha,Nat.sub_sub,Nat.reduceAdd] at h e
  omega

/-- Every cyclic group accommodating a valid set of at least three points has
order at least (9/16) times 2 to the power of the cardinality. -/
theorem cyclic_nine_sixteenths [NeZero N] (hA : IsValidMod A) (hn : 3 ≤ A.card) :
    9 * 2^(A.card-2) ≤ 4*N := by
  classical
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < A.card by omega)
  have ce := card_erase_of_mem ha
  obtain ⟨b,hb,c,hc,hbc⟩ := one_lt_card.mp (show 1 < (A.erase a).card by omega)
  obtain ⟨hba,hbA⟩ := mem_erase.mp hb
  obtain ⟨hca,hcA⟩ := mem_erase.mp hc
  by_cases h : 2*(b-a) = 0
  · apply nine_sixteenths_of_pivots hA ha hcA hca.symm
    intro h'
    have ordTwo (x : ZMod N) (hx : x ≠ a) (he : 2*(x-a)=0) : 2*(x-a).val = N := by
      have neg : -(x-a) = x-a := by linear_combination -he
      exact ((ZMod.neg_eq_self_iff _).mp neg).resolve_left (sub_ne_zero.mpr hx)
    have left := ordTwo b hba h
    have right := ordTwo c hca h'
    have eq := ZMod.val_injective N (show (b-a).val=(c-a).val by omega)
    exact hbc (sub_left_inj.mp eq)
  · exact nine_sixteenths_of_pivots hA ha hbA hba.symm h

end RankPacking
end FonollosaMinModulus

namespace FonollosaMinModulus
open Finset

/-- If two chosen pivots satisfy the interval exclusion, every balanced signed
relation bounded above by one off those pivots vanishes. -/
theorem signed_zero_of_pivot_interval {N : ℕ} {A : Finset (ZMod N)} {a b : ZMod N}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hI : ∀ S ⊆ (A.erase a).erase b, ∀ T ⊆ (A.erase a).erase b, ∀ j : ℤ,
      min 0 ((S.card : ℤ) - T.card) - 1 ≤ j → j ≤ max 0 ((S.card : ℤ) - T.card) + 1 →
      (∑ x ∈ S, (x-a)) = (∑ x ∈ T, (x-a)) + (j : ZMod N)*(b-a) → S = T)
    (c : ZMod N → ℤ) (hl : ∀ x ∈ A, -1 ≤ c x)
    (hu : ∀ x ∈ (A.erase a).erase b, c x ≤ 1)
    (hc : ∑ x ∈ A, c x = 0) (hw : ∑ x ∈ A, (c x : ZMod N)*x = 0) :
    ∀ x ∈ A, c x = 0 := by
  classical
  let R := (A.erase a).erase b
  let S := R.filter (fun x => c x = -1)
  let T := R.filter (fun x => c x = 1)
  have hR : R ⊆ A := (erase_subset ..).trans (erase_subset ..)
  have hs : S ⊆ R := filter_subset ..
  have ht : T ⊆ R := filter_subset ..
  let v (x : ZMod N) := mark T x - mark S x + spike a (c a) x + spike b (c b) x
  have hv (x) (hx : x ∈ A) : c x = v x := by
    by_cases ea : x = a
    · subst x; simp [v,mark,spike,S,T,R,hab.symm]
    by_cases eb : x = b
    · subst x; simp [v,mark,spike,S,T,R,hab]
    have hm : x ∈ R := mem_erase.mpr ⟨eb,mem_erase.mpr ⟨ea,hx⟩⟩
    have l := hl x hx
    have u := hu x hm
    have choices : c x = -1 ∨ c x = 0 ∨ c x = 1 := by omega
    rcases choices with h|h|h <;> simp [v,mark,spike,S,T,hm,Ne.symm ea,Ne.symm eb,h]
  have count : (T.card : ℤ) - S.card + c a + c b = 0 := by
    rw [sum_congr rfl hv] at hc
    simpa [v,sum_add_distrib,sum_sub_distrib,sum_mark (ht.trans hR),sum_mark (hs.trans hR),
      sum_spike ha,sum_spike hb] using hc
  have weight : (∑ x ∈ T,x) - (∑ x ∈ S,x) + (c a : ZMod N)*a + (c b : ZMod N)*b = 0 := by
    have hh : ∀ x ∈ A, (c x : ZMod N)*x = (v x : ZMod N)*x :=
      fun x hx => congrArg (fun z : ℤ => (z : ZMod N)*x) (hv x hx)
    rw [sum_congr rfl hh] at hw
    simpa [v,sub_mul,add_mul,sum_add_distrib,sum_sub_distrib,weight_mark (ht.trans hR),
      weight_mark (hs.trans hR),weight_spike ha,weight_spike hb] using hw
  have la := hl a ha
  have lb := hl b hb
  have balance : c a + c b = (S.card : ℤ) - T.card := by omega
  have castBalance := congrArg (Int.cast : ℤ → ZMod N) balance
  push_cast at castBalance
  have st := hI S hs T ht (c b) (by omega) (by omega) (by
    simp only [sum_sub_distrib,sum_const,nsmul_eq_mul]
    linear_combination -weight + a*castBalance)
  rw [st] at count weight
  simp only [sub_self,zero_add] at count weight
  have cb : c b = 0 := by
    have choices : c b = -1 ∨ c b = 0 ∨ c b = 1 := by omega
    rcases choices with h|h|h
    · have ca : c a = 1 := by omega
      simp [ca,h] at weight
      exact False.elim (hab (by linear_combination weight))
    · exact h
    · have ca : c a = -1 := by omega
      simp [ca,h] at weight
      exact False.elim (hab (by linear_combination -weight))
  have ca : c a = 0 := by omega
  intro x hx
  rw [hv x hx]
  simp [v,st,ca,cb,spike]


/-- A multiset of total size |A| can have multiplicity at least three at no
more than one third of its coordinates. -/
theorem triple_multiplicity_card_le {α : Type*} (A : Finset α) (m : α → ℕ)
    (hm : ∑ x ∈ A, m x = A.card) : 3 * (A.filter (fun x => 3 ≤ m x)).card ≤ A.card := by
  classical
  let H := A.filter fun x => 3 ≤ m x
  calc
    3 * H.card = ∑ _x ∈ H, 3 := by simp [mul_comm]
    _ ≤ ∑ x ∈ H, m x := sum_le_sum (fun _ hx => (mem_filter.mp hx).2)
    _ ≤ ∑ x ∈ A, m x := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)
    _ = A.card := hm

end FonollosaMinModulus
