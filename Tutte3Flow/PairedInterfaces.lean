module

public import Tutte3Flow.BoundaryDeck
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Choosing a common interface and repairing a boundary hole by one edge -/

namespace FinMultigraph

open Finset

/-- Two lists of forbidden interface states leave a common permissible state if their
combined size is smaller than the available residue class. -/
public theorem exists_common_interface {I : Type*} [DecidableEq I] (states left right : Finset I)
    (capacity : left.card + right.card < states.card) :
    ∃ i ∈ states, i ∉ left ∧ i ∉ right := by
  by_contra! exhausted
  have cover : states ⊆ left ∪ right := by
    intro i hi
    by_cases hl : i ∈ left
    · exact mem_union_left _ hl
    · exact mem_union_right _ (exhausted i hi hl)
  have := card_le_card cover
  have := card_union_le left right
  omega

/-- Signs at a labelled matching interface use a common reference direction. -/
@[expose] public def portTotal {k : ℕ} (s : Fin k → Bool) : ZMod 3 :=
  ∑ i, if s i then 1 else -1

/-- A three-edge interface has two states at residue zero and three at each other residue. -/
public theorem triple_port_class_sizes :
    ∀ d : ZMod 3, (univ.filter (fun s : Fin 3 → Bool => portTotal s = d)).card =
      if d = 0 then 2 else 3 := by decide

/-- The two zero-residue states of the matching point uniformly in opposite directions. -/
public theorem triple_port_zero_states :
    ∀ s : Fin 3 → Bool, portTotal s = 0 ↔ (∀ i, s i = true) ∨ (∀ i, s i = false) := by decide

/-- A hole on each side can cover a whole three-port residue class precisely when
the two forbidden states are the opposite constant signs at residue zero. -/
public theorem triple_port_exhaustion :
    ∀ (d : ZMod 3) (left right : Fin 3 → Bool),
      (∀ s : Fin 3 → Bool, portTotal s = d → s = left ∨ s = right) ↔
      d = 0 ∧ ((left = (fun _ => true) ∧ right = (fun _ => false)) ∨
                (left = (fun _ => false) ∧ right = (fun _ => true))) := by decide

/-- With at most one forbidden state per side, a total class is obstructed exactly
when its opposite constant states are rejected on different sides. -/
public theorem triple_port_cover_iff (d : ZMod 3) (P Q : (Fin 3 → Bool) → Prop)
    (up : ∀ s t, P s → P t → s = t) (uq : ∀ s t, Q s → Q t → s = t) :
    (∀ s : Fin 3 → Bool, portTotal s = d → P s ∨ Q s) ↔
      d = 0 ∧ ((P (fun _ => true) ∧ Q (fun _ => false)) ∨
               (P (fun _ => false) ∧ Q (fun _ => true))) := by
  classical
  have zeroT : portTotal (fun _ : Fin 3 => true) = 0 := by decide
  have zeroF : portTotal (fun _ : Fin 3 => false) = 0 := by decide
  have different : (fun _ : Fin 3 => true) ≠ (fun _ => false) := by decide
  constructor
  · intro cover
    have repr {R : (Fin 3 → Bool) → Prop} (unique : ∀ s t, R s → R t → s = t) :
        ∃ r, ∀ s, R s → s = r := by
      by_cases h : ∃ s, R s
      · obtain ⟨r, hr⟩ := h
        exact ⟨r, fun s hs => unique _ _ hs hr⟩
      · exact ⟨fun _ => true, fun s hs => False.elim (h ⟨s, hs⟩)⟩
    obtain ⟨l, hl⟩ := repr up
    obtain ⟨r, hr⟩ := repr uq
    have hd := ((triple_port_exhaustion d l r).mp
      (fun s hs => (cover s hs).imp (hl s) (hr s))).1
    refine ⟨hd, ?_⟩
    rcases cover _ (zeroT.trans hd.symm) with x | x <;> rcases cover _ (zeroF.trans hd.symm) with y | y
    · exact False.elim (different (up _ _ x y))
    · exact Or.inl ⟨x, y⟩
    · exact Or.inr ⟨y, x⟩
    · exact False.elim (different (uq _ _ x y))
  · rintro ⟨hd, sides⟩ s hs
    rcases (triple_port_zero_states s).mp (hs.trans hd) with on | off
    · have eq : s = fun _ => true := funext on
      rw [eq]
      exact sides.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    · have eq : s = fun _ => false := funext off
      rw [eq]
      exact sides.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)

/-- Two adjacent four-port layers with at most one hole each have a common state
for any prescribed total, even with two distinct forbidden states. -/
public theorem four_port_common_state (d : ZMod 3) (left right : Fin 4 → Bool) :
    ∃ s : Fin 4 → Bool, portTotal s = d ∧ s ≠ left ∧ s ≠ right := by
  have size : ∀ k : ZMod 3, 5 ≤ (univ.filter (fun s : Fin 4 → Bool => portTotal s = k)).card := by decide
  obtain ⟨s, hs, hl, hr⟩ := exists_common_interface
    (univ.filter (fun s : Fin 4 → Bool => portTotal s = d)) {left} {right}
    (by simpa using (show 2 < (univ.filter (fun s : Fin 4 → Bool => portTotal s = d)).card by
          have := size d
          omega))
  exact ⟨s, (mem_filter.mp hs).2, by simpa using hl, by simpa using hr⟩

/-- The six labelled edges of the four-vertex complete fibre, directed from low to high. -/
@[expose] public def fourCliqueFibre : FinMultigraph (Fin 4) (Fin 6) where
  src := ![0, 0, 0, 1, 1, 2]
  dst := ![1, 2, 3, 2, 3, 3]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4500000 in
/-- The only missing balanced boundary of the four-clique is the zero vector. -/
public theorem fourCliqueFibre_boundary_signature :
    ∀ γ : Fin 4 → ZMod 3, ∑ v, γ v = 0 →
      (0 < fourCliqueFibre.orientationBoundaryCount γ ↔ γ ≠ 0) := by decide +kernel

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : FinMultigraph V E)

/-- If all missing balanced boundaries have the same sum on a shore, any new edge
crossing it repairs every balanced boundary of the graph, including on multigraphs. -/
public theorem boundaryCount_pos_adjoin_across_constant_hole_sum (S : Finset V) (c : ZMod 3)
    (holes : ∀ b : V → ZMod 3, ∑ v, b v = 0 → G.orientationBoundaryCount b = 0 → ∑ v ∈ S, b v = c)
    (x y : V) (hx : x ∈ S) (hy : y ∉ S) (γ : V → ZMod 3) (valid : ∑ v, γ v = 0) :
    0 < (G.adjoinReferenceEdge x y).orientationBoundaryCount γ := by
  classical
  have sumCol (T : Finset V) : ∑ v ∈ T, unitColumn x y v =
      (if x ∈ T then 1 else 0) - (if y ∈ T then 1 else 0) := by
    simp [unitColumn, sum_sub_distrib]
  have allCol : ∑ v, unitColumn x y v = 0 := by simpa using sumCol univ
  have part : ∑ v ∈ S, unitColumn x y v = 1 := by simpa [hx, hy] using sumCol S
  rw [boundaryCount_adjoin]
  by_contra! zero
  obtain ⟨minus, plus⟩ := Nat.add_eq_zero_iff.mp (Nat.le_zero.mp zero)
  have hm := holes _ (by simp [Pi.sub_apply, sum_sub_distrib, valid, allCol]) minus
  have hp := holes _ (by simp [Pi.add_apply, sum_add_distrib, valid, allCol]) plus
  simp only [Pi.sub_apply, sum_sub_distrib, Pi.add_apply, sum_add_distrib, part] at hm hp
  exact (show ∀ a b : ZMod 3, a - 1 = b → a + 1 = b → False by decide) _ _ hm hp

end FinMultigraph
