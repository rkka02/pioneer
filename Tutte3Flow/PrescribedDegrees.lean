module

public import Tutte3Flow.Challenge
public import Mathlib.Data.Finset.Union
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-! # Prescribing integer outdegrees on a finite multigraph -/

namespace FinMultigraph

open Finset

/-- Hall's theorem with a finite set of slots of each type. -/
public theorem assignWithQuotas {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (support : E → Finset V) (q : V → ℕ) (total : Fintype.card E = ∑ v, q v)
    (bound : ∀ s : Finset E, s.card ≤ ∑ v ∈ s.biUnion support, q v) :
    ∃ owner : E → V, (∀ e, owner e ∈ support e) ∧
      ∀ v, ∑ e, (if owner e = v then 1 else 0 : ℕ) = q v := by
  classical
  let slots (v : V) : Finset (Fin (q v)) := univ
  let choices (e : E) := (support e).sigma slots
  have card_eq : Fintype.card E = Fintype.card (Σ v, Fin (q v)) := by
    simpa [Fintype.card_sigma] using total
  have hall (s : Finset E) : s.card ≤ (s.biUnion choices).card := by
    have union_eq : s.biUnion choices = (s.biUnion support).sigma slots := by
      ext ⟨v, i⟩
      simp [choices, slots]
    simpa [union_eq, Finset.card_sigma, slots] using bound s
  obtain ⟨f, inj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp hall
  let equiv := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj, card_eq⟩)
  refine ⟨fun e => (f e).1, fun e => (Finset.mem_sigma.mp (hf e)).1, ?_⟩
  intro v
  change (∑ e, (if (equiv e).1 = v then 1 else 0 : ℕ)) = _
  rw [equiv.sum_comp (fun x => (if x.1 = v then 1 else 0 : ℕ))]
  rw [Fintype.sum_sigma]
  have single (x : V) :
      (∑ _ : Fin (q x), (if x = v then 1 else 0 : ℕ)) = if x = v then q x else 0 := by
    split <;> simp
  simp_rw [single]
  simp

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] (G : FinMultigraph V E)

/-- The induced edge set counts loops once and retains parallel edges. -/
@[expose] public def internalEdges (s : Finset V) : Finset E :=
  univ.filter (fun e => G.src e ∈ s ∧ G.dst e ∈ s)

/-- Hakimi's cut criterion. Every edge contributes exactly one tail. -/
public theorem exists_orientation_with_outdegrees_iff (q : V → ℕ) :
    (∃ r : E → Bool, ∀ v,
      (univ.filter (fun e => (G.reorient r).src e = v)).card = q v) ↔
    Fintype.card E = ∑ v, q v ∧
      ∀ s : Finset V, (G.internalEdges s).card ≤ ∑ v ∈ s, q v := by
  classical
  constructor
  · rintro ⟨r, degrees⟩
    let tail := (G.reorient r).src
    have mass (s : Finset V) :
        ∑ v ∈ s, q v = (univ.filter (fun e => tail e ∈ s)).card := by
      simp only [← degrees]
      exact Finset.sum_card_fiberwise_eq_card_filter _ _ _
    refine ⟨?_, fun s => ?_⟩
    · simp [mass]
    · rw [mass]
      apply Finset.card_le_card
      intro e he
      have both := (Finset.mem_filter.mp he).2
      apply Finset.mem_filter.mpr
      exact ⟨mem_univ _, by cases h : r e <;> simp_all [tail, reorient]⟩
  · rintro ⟨total, cuts⟩
    let ends (e : E) : Finset V := {G.src e, G.dst e}
    have bound (s : Finset E) : s.card ≤ ∑ v ∈ s.biUnion ends, q v := by
      apply le_trans _ (cuts (s.biUnion ends))
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_filter.mpr ⟨mem_univ _, Finset.mem_biUnion.mpr ⟨e, he, by simp [ends]⟩,
        Finset.mem_biUnion.mpr ⟨e, he, by simp [ends]⟩⟩
    obtain ⟨owner, supported, loads⟩ := assignWithQuotas ends q total bound
    let r (e : E) := decide (owner e ≠ G.src e)
    have tail (e : E) : (G.reorient r).src e = owner e := by
      have h : owner e = G.src e ∨ owner e = G.dst e := by simpa [ends] using supported e
      by_cases hs : owner e = G.src e <;> simp_all [reorient, r]
    refine ⟨r, fun v => ?_⟩
    simpa only [tail, Finset.sum_boole, Nat.cast_id] using loads v

end FinMultigraph
