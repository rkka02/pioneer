import FonollosaMinModulus.Challenge
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
