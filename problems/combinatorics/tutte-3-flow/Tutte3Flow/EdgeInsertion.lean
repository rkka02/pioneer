module

public import Tutte3Flow.IntegralLift
import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Abel

/-! # Transferring a unit modulo three to insert an edge with prescribed old edges -/

namespace FinMultigraph

open Finset

variable {V E : Type*} (G : FinMultigraph V E)

/-- The new edge is labelled `none`, and each original edge keeps its reference direction. -/
@[expose] public def adjoinReferenceEdge (x y : V) : FinMultigraph V (Option E) where
  src
    | none => x
    | some e => G.src e
  dst
    | none => y
    | some e => G.dst e

variable [Fintype E] [DecidableEq V]

/-- The outgoing sum minus the incoming sum in the reference orientation. -/
@[expose] public def mod3Divergence (f : E → ZMod 3) (v : V) : ZMod 3 :=
  (∑ e ∈ univ.filter (fun e => G.src e = v), f e) -
  (∑ e ∈ univ.filter (fun e => G.dst e = v), f e)

private theorem divergence_as_sum (f : E → ZMod 3) (v : V) :
    G.mod3Divergence f v = (∑ e, if G.src e = v then f e else 0) -
      (∑ e, if G.dst e = v then f e else 0) := by
  simp only [mod3Divergence, sum_filter]

/-- The divergence after adjoining one labelled edge separates into the two contributions. -/
public theorem divergence_adjoin (x y v : V) (f : Option E → ZMod 3) :
    (G.adjoinReferenceEdge x y).mod3Divergence f v =
      G.mod3Divergence (fun e => f (some e)) v +
        ((if x = v then f none else 0) - (if y = v then f none else 0)) := by
  rw [divergence_as_sum, divergence_as_sum, Fintype.sum_option, Fintype.sum_option]
  have rearrange (a b c d : ZMod 3) : (c + a) - (d + b) = (a - b) + (c - d) := by abel
  exact rearrange _ _ _ _

private theorem divergence_one_add (g : E → ZMod 3) (v : V) :
    G.mod3Divergence (fun e => 1 + g e) v =
      G.mod3Divergence (fun _ => 1) v + G.mod3Divergence g v := by
  simp only [mod3Divergence, sum_add_distrib]
  abel

/-- Starting from a balanced reference orientation, inserting an edge while preserving the
specified old directions is equivalent to transferring one nonzero residue on a subset of
the unpinned edges. The boolean function selects those edges. -/
public theorem pinned_insertion_iff_transfer (x y : V) (pinned : E → Prop)
    (balanced : ∀ v, G.mod3Divergence (fun _ => 1) v = 0) :
    (∃ f : Option E → ZMod 3, (∀ e, f e ≠ 0) ∧
      (∀ v, (G.adjoinReferenceEdge x y).mod3Divergence f v = 0) ∧
      ∀ e, pinned e → f (some e) = 1) ↔
    ∃ (b : E → Bool) (t : ZMod 3), t ≠ 0 ∧ (∀ e, pinned e → b e = false) ∧
      ∀ v, G.mod3Divergence (fun e => if b e then 1 else 0) v =
        (if y = v then t else 0) - (if x = v then t else 0) := by
  constructor
  · rintro ⟨f, nonzero, conservation, fixed⟩
    let b (e : E) := decide (f (some e) ≠ 1)
    have classify : ∀ a : ZMod 3, a ≠ 0 → a = 1 + (if decide (a ≠ 1) then 1 else 0) := by decide
    have repr : (fun e => f (some e)) = (fun e => 1 + (if b e then 1 else 0)) :=
      funext (fun e => classify _ (nonzero _))
    refine ⟨b, f none, nonzero none, fun e he => ?_, fun v => ?_⟩
    · simp [b, fixed e he]
    · have h := conservation v
      rw [G.divergence_adjoin, repr, G.divergence_one_add, balanced, zero_add] at h
      exact (eq_neg_of_add_eq_zero_left h).trans (neg_sub _ _)
  · rintro ⟨b, t, ht, fixed, transfer⟩
    let f : Option E → ZMod 3
      | none => t
      | some e => 1 + (if b e then 1 else 0)
    refine ⟨f, ?_, ?_, fun e he => ?_⟩
    · rintro (_ | e)
      · exact ht
      · cases h : b e <;> simp [f, h] <;> decide
    · intro v
      rw [G.divergence_adjoin]
      change G.mod3Divergence (fun e => 1 + (if b e then 1 else 0)) v + _ = 0
      rw [G.divergence_one_add, balanced, zero_add, transfer]
      change _ + ((if x = v then t else 0) - (if y = v then t else 0)) = 0
      abel
    · simp [f, fixed e he]

/-- With all old edges free, the same transfer criterion gives an integer 3-flow. -/
public theorem hasNowhereZeroIntFlow_adjoin_iff_transfer [Fintype V] (x y : V)
    (balanced : ∀ v, G.mod3Divergence (fun _ => 1) v = 0) :
    (G.adjoinReferenceEdge x y).HasNowhereZeroIntFlow 3 ↔
    ∃ (b : E → Bool) (t : ZMod 3), t ≠ 0 ∧
      ∀ v, G.mod3Divergence (fun e => if b e then 1 else 0) v =
        (if y = v then t else 0) - (if x = v then t else 0) := by
  rw [← (G.adjoinReferenceEdge x y).hasMod3Orientation_iff_hasNowhereZeroIntFlow,
    (G.adjoinReferenceEdge x y).hasMod3Orientation_iff_hasNowhereZeroZMod3Flow]
  simpa [HasNowhereZeroZMod3Flow, mod3Divergence, sub_eq_zero] using
    G.pinned_insertion_iff_transfer x y (fun _ => False) balanced

end FinMultigraph
