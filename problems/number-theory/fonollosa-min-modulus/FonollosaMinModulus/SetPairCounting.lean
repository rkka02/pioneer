module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-! Counting cross-intersecting pairs of coordinate sets by permutations. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace FonollosaMinModulus.SetPairs
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
private theorem exists_front (rank : α → ℕ) (inj : Function.Injective rank)
    (k : ℕ) (U : Finset α) (hk : k ≤ U.card) :
    ∃ B ⊆ U, B.card = k ∧ ∀ x ∈ B, ∀ y ∈ U \ B, rank x < rank y := by
  classical
  induction k generalizing U with
  | zero => exact ⟨∅,empty_subset _,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨x,hx,hmin⟩ := exists_min_image U rank (card_pos.mp (by omega))
    have hc := card_erase_of_mem hx
    obtain ⟨B,hB,hkB,sep⟩ := ih (U.erase x) (by omega)
    have hn : x ∉ B := fun h => (mem_erase.mp (hB h)).1 rfl
    refine ⟨insert x B,insert_subset hx (hB.trans (erase_subset ..)),by simp [hn,hkB],?_⟩
    intro z hz y hy
    obtain ⟨hyU,hyB⟩ := mem_sdiff.mp hy
    have hne : y ≠ x := fun e => hyB (e ▸ mem_insert_self ..)
    rcases mem_insert.mp hz with rfl|hz
    · exact lt_of_le_of_ne (hmin y hyU) (fun he => hne (inj he).symm)
    · exact sep z hz y (mem_sdiff.mpr ⟨mem_erase.mpr ⟨hne,hyU⟩,
        fun h => hyB (mem_insert_of_mem h)⟩)

/-- Simultaneously relabel two disjoint sets, preserving their separate sizes. -/
private theorem relabel {D C B K : Finset α} (hDC : Disjoint D C) (hBK : Disjoint B K)
    (hD : D.card = B.card) (hC : C.card = K.card) :
    ∃ p : Equiv.Perm α, (∀ x ∈ D, p x ∈ B) ∧ ∀ x ∈ C, p x ∈ K := by
  classical
  let e := D.equivOfCardEq hD
  let f := C.equivOfCardEq hC
  let i : D ⊕ C → α := Sum.elim (fun x => x.val) (fun x => x.val)
  let j : D ⊕ C → α := Sum.elim (fun x => (e x).val) (fun x => (f x).val)
  have hi : Function.Injective i := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change a.val = b.val at h
      exact False.elim (disjoint_left.mp hDC a.2 (h.symm ▸ b.2))
    · change a.val = b.val at h
      exact False.elim (disjoint_left.mp hDC b.2 (h ▸ a.2))
    · exact congrArg Sum.inr (Subtype.ext h)
  have hj : Function.Injective j := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (e.injective (Subtype.ext h))
    · change (e a).val = (f b).val at h
      exact False.elim (disjoint_left.mp hBK (e a).2 (h.symm ▸ (f b).2))
    · change (f a).val = (e b).val at h
      exact False.elim (disjoint_left.mp hBK (e b).2 (h ▸ (f a).2))
    · exact congrArg Sum.inr (f.injective (Subtype.ext h))
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair i j hi hj
  refine ⟨p,?_,?_⟩
  · intro x hx
    have h : p x = (e ⟨x,hx⟩).val := hp (.inl ⟨x,hx⟩)
    exact h ▸ (e ⟨x,hx⟩).2
  · intro x hx
    have h : p x = (f ⟨x,hx⟩).val := hp (.inr ⟨x,hx⟩)
    exact h ▸ (f ⟨x,hx⟩).2

noncomputable def separated (rank : α → ℕ) (D C : Finset α) :=
  (univ : Finset (Equiv.Perm α)).filter fun p => ∀ x ∈ D, ∀ y ∈ C, rank (p x) < rank (p y)

/-- A fixed ordered pair of disjoint sets is separated by at least the reciprocal
of its binomial coefficient of all permutations. No equality of sizes is needed. -/
theorem count_separated (rank : α → ℕ) (inj : Function.Injective rank)
    {D C : Finset α} (hd : Disjoint D C) :
    Fintype.card (Equiv.Perm α) ≤ (D.card+C.card).choose D.card * (separated rank D C).card := by
  classical
  let U := D ∪ C
  have hU : U.card = D.card+C.card := card_union_of_disjoint hd
  let Bs := U.powersetCard D.card
  have front (p : Equiv.Perm α) : ∃ B ∈ Bs, ∀ x ∈ B, ∀ y ∈ U \ B, rank (p x) < rank (p y) := by
    obtain ⟨B,hB,hc,ht⟩ := exists_front (rank ∘ p) (inj.comp p.injective) D.card U (by omega)
    exact ⟨B,mem_powersetCard.mpr ⟨hB,hc⟩,ht⟩
  let first (p : Equiv.Perm α) := Classical.choose (front p)
  have prop (p) := Classical.choose_spec (front p)
  have label (B : Finset α) : ∃ q : Equiv.Perm α, B ∈ Bs →
      (∀ x ∈ D, q x ∈ B) ∧ ∀ x ∈ C, q x ∈ U \ B := by
    by_cases h : B ∈ Bs
    · obtain ⟨sub,sz⟩ := mem_powersetCard.mp h
      obtain ⟨q,hq⟩ := relabel (B:=B) (K:=U \ B) hd (disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp hy).2 hx)) sz.symm
        (by rw [card_sdiff_of_subset sub,hU,sz]; omega)
      exact ⟨q,fun _ => hq⟩
    · exact ⟨Equiv.refl _,fun h' => False.elim (h h')⟩
  let q (B) := Classical.choose (label B)
  let enc (p : Equiv.Perm α) := (first p, (q (first p)).trans p)
  have h := card_le_card_of_injOn (s := (univ : Finset (Equiv.Perm α)))
    (t := Bs ×ˢ separated rank D C) enc (by
      intro p _
      obtain ⟨hb,hs⟩ := prop p
      have acts := Classical.choose_spec (label (first p)) hb
      refine mem_product.mpr ⟨hb,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      intro x hx y hy
      exact hs _ (acts.1 x hx) _ (acts.2 y hy)) (by
      intro p _ v _ he
      have eq : first p = first v := congrArg Prod.fst he
      have eq' : (q (first p)).trans p = (q (first v)).trans v := congrArg Prod.snd he
      rw [eq] at eq'
      ext x
      obtain ⟨y,rfl⟩ := (q (first v)).surjective x
      exact DFunLike.congr_fun eq' y)
  simpa [Bs,card_powersetCard,hU] using h


/-- Subsets containing the removed coordinates and avoiding the inserted coordinates. -/
def cylinder (R D C : Finset α) := R.powerset.filter fun S => D ⊆ S ∧ Disjoint S C

theorem cylinder_scaled {R D C : Finset α} (hD : D ⊆ R) (hC : C ⊆ R)
    (hd : Disjoint D C) :
    (cylinder R D C).card * 2^(D.card+C.card) ≤ 2^R.card := by
  classical
  let U := D ∪ C
  have hU : U ⊆ R := union_subset hD hC
  have sz : U.card = D.card+C.card := card_union_of_disjoint hd
  have h := card_le_card_of_injOn (s := cylinder R D C) (t := (R \ U).powerset)
    (fun S => S \ U) (by
      intro S hS
      exact mem_powerset.mpr (sdiff_subset_sdiff_left _ (mem_powerset.mp (mem_filter.mp hS).1))) (by
      intro S hS T hT eq
      obtain ⟨sd,sc⟩ := (mem_filter.mp hS).2
      obtain ⟨td,tc⟩ := (mem_filter.mp hT).2
      ext x
      by_cases dx : x ∈ D
      · exact iff_of_true (sd dx) (td dx)
      by_cases cx : x ∈ C
      · exact iff_of_false (fun hs => disjoint_left.mp sc hs cx) (fun ht => disjoint_left.mp tc ht cx)
      have hx : x ∉ U := fun hu => (mem_union.mp hu).elim dx cx
      change S \ U = T \ U at eq
      have ee : x ∈ S \ U ↔ x ∈ T \ U := by rw [eq]
      simpa [hx] using ee)
  rw [card_powerset] at h
  calc
    _ ≤ 2^(R \ U).card * 2^(D.card+C.card) := Nat.mul_le_mul_right _ h
    _ = _ := by rw [← pow_add,← sz,card_sdiff_add_card_eq_card hU]

/-- A weighted set-pair inequality. The separating sets may omit coordinates
already forced in every cylinder; this permits conditioning on a singleton rule. -/
theorem weighted {ι : Type*} (rank : α → ℕ) (inj : Function.Injective rank)
    (I : Finset ι) (R : Finset α) (D C L M : ι → Finset α) (w : ι → ℕ) (K W : ℕ)
    (inside : ∀ i ∈ I, D i ⊆ R ∧ C i ⊆ R ∧ Disjoint (D i) (C i))
    (apart : ∀ i ∈ I, Disjoint (L i) (M i))
    (cross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∃ x ∈ L i, x ∈ M j)
    (localBound : ∀ i ∈ I, K*w i*((L i).card+(M i).card).choose (L i).card ≤
         W*2^((D i).card+(C i).card)) :
    K * (∑ i ∈ I, w i * (cylinder R (D i) (C i)).card) ≤ W*2^R.card := by
  classical
  let P := Fintype.card (Equiv.Perm α)
  have pos : 0 < P := Fintype.card_pos
  let events i := separated rank (L i) (M i)
  have dis : (I : Set ι).PairwiseDisjoint events := by
    intro i hi j hj hn
    apply disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨x,hx,hx'⟩ := cross i hi j hj hn
    obtain ⟨y,hy,hy'⟩ := cross j hj i hi hn.symm
    exact lt_asymm ((mem_filter.mp hpi).2 x hx y hy') ((mem_filter.mp hpj).2 y hy x hx')
  have total : ∑ i ∈ I, (events i).card ≤ P := by
    rw [← card_biUnion dis]
    exact card_le_univ _
  have one (i) (hi : i ∈ I) :
      K*(w i*(cylinder R (D i) (C i)).card)*P ≤ W*2^R.card*(events i).card := by
    let B := (cylinder R (D i) (C i)).card
    let J := ((L i).card+(M i).card).choose (L i).card
    let E := (events i).card
    have pe : P ≤ J*E := count_separated rank inj (apart i hi)
    have bound := localBound i hi
    have area := cylinder_scaled (inside i hi).1 (inside i hi).2.1 (inside i hi).2.2
    change K*(w i*B)*P ≤ W*2^R.card*E
    calc
      _ ≤ K*(w i*B)*(J*E) := Nat.mul_le_mul_left _ pe
      _ = (K*w i*J)*B*E := by ring
      _ ≤ (W*2^((D i).card+(C i).card))*B*E :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ bound)
      _ = W*(B*2^((D i).card+(C i).card))*E := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ area)
  apply Nat.le_of_mul_le_mul_right (c := P) _ pos
  calc
    _ = ∑ i ∈ I, K*(w i*(cylinder R (D i) (C i)).card)*P := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ ∑ i ∈ I, W*2^R.card*(events i).card := sum_le_sum one
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ total

private theorem pascal_bound (a b base : ℕ)
    (init : ∀ k, a*base.choose k ≤ b*2^base) {h : ℕ} (hh : base ≤ h) (k : ℕ) :
    a*h.choose k ≤ b*2^h := by
  induction h, hh using Nat.le_induction generalizing k with
  | base => exact init k
  | succ h _ ih =>
    cases k with
    | zero =>
      have e := ih 0
      simp only [Nat.choose_zero_right,mul_one] at *
      rw [pow_succ, ← Nat.mul_assoc]; omega
    | succ k =>
      rw [Nat.choose_succ_succ,Nat.mul_add,pow_succ]
      have lo := ih k
      have hi := ih k.succ
      rw [← Nat.mul_assoc]
      omega

theorem binom_half {h k : ℕ} (hh : 1 ≤ h) : 2*h.choose k ≤ 2^h := by
  simpa using pascal_bound 2 1 1 (by
    intro j; by_cases hj : j ≤ 1
    · interval_cases j <;> decide
    · simp [Nat.choose_eq_zero_of_lt (by omega : 1 < j)]) hh k

theorem binom_three_eighths {h k : ℕ} (hh : 3 ≤ h) : 8*h.choose k ≤ 3*2^h :=
  pascal_bound 8 3 3 (by
    intro j; by_cases hj : j ≤ 3
    · interval_cases j <;> decide
    · simp [Nat.choose_eq_zero_of_lt (by omega : 3 < j)]) hh k

theorem binom_quarter_gap_two {d c : ℕ} (hg : d+2=c ∨ c+2=d) :
    4*(d+c).choose d ≤ 2^(d+c) := by
  by_cases big : 9 ≤ d+c
  · simpa using pascal_bound 4 1 9 (by
      intro j; by_cases hj : j ≤ 9
      · interval_cases j <;> decide
      · simp [Nat.choose_eq_zero_of_lt (by omega : 9 < j)]) big d
  · have hd : d ≤ 8 := by omega
    have hc : c ≤ 8 := by omega
    rcases hg with rfl|rfl
    · interval_cases d <;> decide
    · interval_cases c <;> decide

end FonollosaMinModulus.SetPairs
