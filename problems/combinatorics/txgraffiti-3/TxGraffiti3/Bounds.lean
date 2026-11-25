module

public import Mathlib.Data.Finset.Card

/-! A certificate for lower bounds on independent domination in induced subgraphs.
A mask records the remaining vertices. Each row depends only on earlier rows. -/

@[expose] public section

namespace TxGraffiti3.Bounds

variable {n : ℕ}

abbrev InMask (s : ℕ) (v : Fin n) : Prop := s.testBit v.val = true

/-- Remove the bits of `b` from `a`. -/
def cut (a b : ℕ) := a ^^^ (a &&& b)

private theorem in_cut {a b : ℕ} {v : Fin n} :
    InMask (cut a b) v ↔ InMask a v ∧ ¬InMask b v := by
  simp only [cut, InMask, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit v.val <;> cases b.testBit v.val <;> decide

private theorem in_union {a b : ℕ} {v : Fin n} :
    InMask (a ||| b) v ↔ InMask a v ∨ InMask b v := by
  simp [InMask]

private theorem no_inter {a b : ℕ} (h : a &&& b = 0) {v : Fin n} :
    InMask a v → ¬InMask b v := by
  intro ha hb
  have hbit := congrArg (fun z : ℕ ↦ z.testBit v.val) h
  simp [InMask] at ha hb
  simp [ha, hb] at hbit

/-- `N` gives closed neighborhoods. All three conditions refer to the induced graph on `s`. -/
structure Feasible (N : Fin n → ℕ) (s : ℕ) (D : Finset (Fin n)) : Prop where
  within : ∀ x ∈ D, InMask s x
  apart : ∀ x ∈ D, ∀ y ∈ D, InMask (N x) y → x = y
  dominates : ∀ v, InMask s v → ∃ w ∈ D, InMask (N v) w

def Lower (N : Fin n → ℕ) (s k : ℕ) : Prop :=
  ∀ D : Finset (Fin n), Feasible N s D → k ≤ D.card

private theorem after_choice {N : Fin n → ℕ}
    (sym : ∀ v w, InMask (N v) w → InMask (N w) v)
    {s : ℕ} {D : Finset (Fin n)} (h : Feasible N s D) {x : Fin n} (hx : x ∈ D) :
    Feasible N (cut s (N x)) (D.erase x) := by
  constructor
  · intro y hy
    obtain ⟨hne, hyD⟩ := Finset.mem_erase.mp hy
    exact in_cut.mpr ⟨h.within y hyD, fun hxy ↦ hne (h.apart x hx y hyD hxy).symm⟩
  · intro y hy z hz
    exact h.apart y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz)
  · intro v hv
    obtain ⟨hvs, hvx⟩ := in_cut.mp hv
    obtain ⟨w, hw, hvw⟩ := h.dominates v hvs
    have hne : w ≠ x := by
      rintro rfl
      exact hvx (sym v w hvw)
    exact ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩, hvw⟩

private theorem on_piece {N : Fin n → ℕ} {a b : ℕ} {D : Finset (Fin n)}
    (h : Feasible N (a ||| b) D)
    (sep : ∀ v, InMask a v → ∀ w : Fin n, InMask b w → ¬InMask (N v) w) :
    Feasible N a (D.filter (InMask a)) := by
  constructor
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy
    exact h.apart x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := h.dominates x (in_union.mpr (.inl hx))
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hxy⟩
    exact (in_union.mp (h.within y hy)).resolve_right (fun hby ↦ sep x hx y hby hxy)

private theorem add_pieces {N : Fin n → ℕ}
    (sym : ∀ v w, InMask (N v) w → InMask (N w) v)
    {a b i j : ℕ} (dis : a &&& b = 0)
    (sep : ∀ v, InMask a v → N v &&& b = 0)
    (ha : Lower N a i) (hb : Lower N b j) : Lower N (a ||| b) (i+j) := by
  intro D h
  have hab (v) (hv : InMask a v) (w : Fin n) (hw : InMask b w) : ¬InMask (N v) w :=
    fun hedge ↦ no_inter (sep v hv) hedge hw
  have h₁ := ha _ (on_piece h hab)
  have h' : Feasible N (b ||| a) D := by rwa [Nat.or_comm]
  have h₂ := hb _ (on_piece h' (fun v hv w hw hedge ↦ hab w hw v hv (sym v w hedge)))
  have heq : D.filter (InMask b) = D.filter (fun v ↦ ¬InMask a v) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hbi⟩
      exact ⟨hv, fun hai ↦ no_inter dis hai hbi⟩
    · rintro ⟨hv, hai⟩
      exact ⟨hv, (in_union.mp (h.within v hv)).resolve_left hai⟩
  rw [heq] at h₂
  exact (Nat.add_le_add h₁ h₂).trans_eq (D.card_filter_add_card_filter_not (InMask a))

inductive Rule (n : ℕ) where
  | zero
  | pivot (v : Fin n) (children : List ℕ)
  | split (left right : ℕ)

structure Row (n : ℕ) where
  mask : ℕ
  bound : ℕ
  rule : Rule n

/-- A row either records zero, branches on a dominator of a pivot, or adds two components. -/
def Valid (N : Fin n → ℕ) (table : ℕ → Row n) (i : ℕ) : Prop :=
  let r := table i
  match r.rule with
  | .zero => r.bound = 0
  | .pivot v children =>
    InMask r.mask v ∧ ∀ x : Fin n, InMask r.mask x → InMask (N v) x →
      ∃ j ∈ children, j < i ∧ (table j).mask = cut r.mask (N x) ∧
        r.bound ≤ (table j).bound + 1
  | .split j k =>
    j < i ∧ k < i ∧ r.mask = (table j).mask ||| (table k).mask ∧
    (table j).mask &&& (table k).mask = 0 ∧
    (∀ v : Fin n, InMask (table j).mask v → N v &&& (table k).mask = 0) ∧
    r.bound ≤ (table j).bound + (table k).bound

instance (N : Fin n → ℕ) (table : ℕ → Row n) (i : ℕ) : Decidable (Valid N table i) := by
  unfold Valid
  dsimp only
  split <;> infer_instance

theorem sound {N : Fin n → ℕ} (sym : ∀ v w, InMask (N v) w → InMask (N w) v)
    {table : ℕ → Row n} {length : ℕ} (ok : ∀ i < length, Valid N table i)
    (i : ℕ) (hi : i < length) : Lower N (table i).mask (table i).bound := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have hr := ok i hi
    unfold Valid at hr
    dsimp only at hr
    split at hr
    · intro D _
      simp [hr]
    · rename_i v children _
      intro D hd
      obtain ⟨x, hx, hvx⟩ := hd.dominates v hr.1
      obtain ⟨j, _, hji, hmask, hb⟩ := hr.2 x (hd.within x hx) hvx
      have hl := ih j hji (lt_trans hji hi)
      rw [hmask] at hl
      have hcard := hl (D.erase x) (after_choice sym hd hx)
      exact hb.trans (by simpa [Finset.card_erase_add_one hx] using Nat.add_le_add_right hcard 1)
    · obtain ⟨hj, hk, hmask, hdis, hsep, hb⟩ := hr
      have hsum := add_pieces sym hdis hsep (ih _ hj (lt_trans hj hi)) (ih _ hk (lt_trans hk hi))
      rw [hmask]
      exact fun D hd ↦ hb.trans (hsum D hd)

end TxGraffiti3.Bounds
