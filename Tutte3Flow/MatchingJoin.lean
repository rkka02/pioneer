module

public import Tutte3Flow.PairedInterfaces
public import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-! # Gluing finite multigraphs along labelled ternary interfaces -/

namespace FinMultigraph

open Finset

variable {V W E F I : Type*} (G : FinMultigraph V E) (H : FinMultigraph W F)

/-- Disjoint union with one extra edge from the left to the right for each interface label. -/
@[expose] public def joinPorts (a : I → V) (b : I → W) :
    FinMultigraph (V ⊕ W) (E ⊕ (F ⊕ I)) where
  src := Sum.elim (fun e => .inl (G.src e)) (Sum.elim (fun e => .inr (H.src e)) (fun i => .inl (a i)))
  dst := Sum.elim (fun e => .inl (G.dst e)) (Sum.elim (fun e => .inr (H.dst e)) (fun i => .inr (b i)))

variable [DecidableEq V] [DecidableEq W] [Fintype E] [Fintype F] [Fintype I]

/-- Contributions of an interface assignment at its endpoints on a single side. -/
@[expose] public def portDemand (a : I → V) (s : I → Bool) (v : V) : ZMod 3 :=
  ∑ i ∈ univ.filter (fun i => a i = v), if s i then 1 else -1

/-- Attain a specified boundary by choosing one of the two nonzero signs at each edge. -/
@[expose] public def realizesBoundary (γ : V → ZMod 3) : Prop :=
  ∃ t : E → Bool, G.mod3Divergence (fun e => if t e then 1 else -1) = γ

/-- The existence and counting descriptions of a boundary agree. -/
public theorem realizesBoundary_iff_count_pos [Fintype V] [DecidableEq E] (γ : V → ZMod 3) :
    G.realizesBoundary γ ↔ 0 < G.orientationBoundaryCount γ := by
  classical
  simp [realizesBoundary, orientationBoundaryCount, ← card_filter, card_pos, Finset.Nonempty]

private theorem joinPorts_divergence (a : I → V) (b : I → W) (t : E ⊕ (F ⊕ I) → Bool) :
    (∀ v, (G.joinPorts H a b).mod3Divergence (fun e => if t e then 1 else -1) (.inl v) =
      G.mod3Divergence (fun e => if t (.inl e) then 1 else -1) v +
        portDemand a (fun i => t (.inr (.inr i))) v) ∧
    ∀ w, (G.joinPorts H a b).mod3Divergence (fun e => if t e then 1 else -1) (.inr w) =
      H.mod3Divergence (fun e => if t (.inr (.inl e)) then 1 else -1) w -
        portDemand b (fun i => t (.inr (.inr i))) w := by
  constructor <;> intro v <;>
    simp only [mod3Divergence, portDemand, sum_filter, Fintype.sum_sum_type] <;>
    simp [joinPorts] <;> abel

/-- The same signs must work on both sides. Endpoint repetitions and parallel edges
are allowed. -/
public theorem joinPorts_realizes_iff (a : I → V) (b : I → W) (γ : V → ZMod 3) (δ : W → ZMod 3) :
    (G.joinPorts H a b).realizesBoundary (Sum.elim γ δ) ↔
      ∃ s : I → Bool, G.realizesBoundary (γ - portDemand a s) ∧
        H.realizesBoundary (δ + portDemand b s) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i => t (.inr (.inr i)), ⟨fun e => t (.inl e), ?_⟩, ⟨fun e => t (.inr (.inl e)), ?_⟩⟩
    · funext v
      have h := congrFun ht (.inl v)
      rw [(G.joinPorts_divergence H a b t).1] at h
      exact eq_sub_of_add_eq h
    · funext w
      have h := congrFun ht (.inr w)
      rw [(G.joinPorts_divergence H a b t).2] at h
      exact eq_add_of_sub_eq h
  · rintro ⟨s, ⟨l, hl⟩, ⟨r, hr⟩⟩
    let t : E ⊕ (F ⊕ I) → Bool := Sum.elim l (Sum.elim r s)
    refine ⟨t, ?_⟩
    funext j
    cases j with
    | inl v =>
      rw [(G.joinPorts_divergence H a b t).1]
      change G.mod3Divergence (fun e => if l e then 1 else -1) v + portDemand a s v = γ v
      rw [hl]
      exact sub_add_cancel _ _
    | inr w =>
      rw [(G.joinPorts_divergence H a b t).2]
      change H.mod3Divergence (fun e => if r e then 1 else -1) w - portDemand b s w = δ w
      rw [hr]
      exact add_sub_cancel_right _ _

private theorem realizable_mass [Fintype V] {γ : V → ZMod 3} (h : G.realizesBoundary γ) :
    ∑ v, γ v = 0 := by
  obtain ⟨s, rfl⟩ := h
  simp [mod3Divergence, sum_sub_distrib, sum_fiberwise]

private theorem portDemand_injective {a : I → V} (inj : Function.Injective a) :
    Function.Injective (portDemand a) := by
  intro s t h
  funext i
  classical
  have he := congrFun h (a i)
  have fibre (x : I) : a x = a i ↔ x = i := inj.eq_iff
  simp only [portDemand, sum_filter, fibre, sum_ite_eq', mem_univ, ite_true] at he
  exact (show ∀ j k : Bool, (if j then 1 else -1 : ZMod 3) = (if k then 1 else -1) →
      j = k by decide) _ _ he

private theorem portDemand_total [Fintype V] {k : ℕ} (p : Fin k → V) (s : Fin k → Bool) :
    ∑ v, portDemand p s v = portTotal s := sum_fiberwise univ p _

/-- On a triple matching between graphs each missing just the zero boundary, give every
endpoint the same nonzero residual contribution. These are exactly the two holes in
the joined graph. The inputs allow any vertex set sizes on either side. -/
public theorem triple_matching_join_holes [Fintype V] [Fintype W] (a : Fin 3 → V) (b : Fin 3 → W)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (left : ∀ β : V → ZMod 3, ∑ v, β v = 0 → (G.realizesBoundary β ↔ β ≠ 0))
    (right : ∀ β : W → ZMod 3, ∑ v, β v = 0 → (H.realizesBoundary β ↔ β ≠ 0))
    (γ : V → ZMod 3) (δ : W → ZMod 3) (valid : (∑ v, γ v) + ∑ w, δ w = 0) :
    ¬ (G.joinPorts H a b).realizesBoundary (Sum.elim γ δ) ↔
      (γ = portDemand a (fun _ => true) ∧ δ = -portDemand b (fun _ => false)) ∨
      (γ = portDemand a (fun _ => false) ∧ δ = -portDemand b (fun _ => true)) := by
  classical
  let d := ∑ v, γ v
  have massLeft (s : Fin 3 → Bool) : (∑ v, (γ - portDemand a s) v) = d - portTotal s := by
    simp [d, sum_sub_distrib, portDemand_total]
  have massRight (s : Fin 3 → Bool) (hs : portTotal s = d) : ∑ w, (δ + portDemand b s) w = 0 := by
    simpa [sum_add_distrib, portDemand_total, hs, d, add_comm] using valid
  have rule : ¬ (G.joinPorts H a b).realizesBoundary (Sum.elim γ δ) ↔
      ∀ s : Fin 3 → Bool, portTotal s = d → γ = portDemand a s ∨ δ = -portDemand b s := by
    rw [joinPorts_realizes_iff]
    constructor
    · intro no s hs
      by_contra! both
      apply no
      refine ⟨s, (left _ (by rw [massLeft, hs, sub_self])).mpr ?_, (right _ (massRight s hs)).mpr ?_⟩
      · exact sub_ne_zero.mpr both.1
      · exact fun zero => both.2 (eq_neg_of_add_eq_zero_left zero)
    · rintro block ⟨s, l, r⟩
      have hs : portTotal s = d := by
        have h := G.realizable_mass l
        rw [massLeft, sub_eq_zero] at h
        exact h.symm
      rcases block s hs with lzero | rzero
      · exact ((left _ (by rw [massLeft, hs, sub_self])).mp l) (sub_eq_zero.mpr lzero)
      · exact ((right _ (massRight s hs)).mp r) (by rw [rzero, neg_add_cancel])
  have uniqueL (s t : Fin 3 → Bool) (x : γ = portDemand a s) (y : γ = portDemand a t) : s = t :=
    portDemand_injective ha (x.symm.trans y)
  have uniqueR (s t : Fin 3 → Bool) (x : δ = -portDemand b s) (y : δ = -portDemand b t) : s = t :=
    portDemand_injective hb (neg_inj.mp (x.symm.trans y))
  rw [rule, triple_port_cover_iff d _ _ uniqueL uniqueR]
  refine ⟨fun h => h.2, fun sides => ⟨?_, sides⟩⟩
  have zeroT : portTotal (fun _ : Fin 3 => true) = 0 := by decide
  have zeroF : portTotal (fun _ : Fin 3 => false) = 0 := by decide
  rcases sides with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [d, h, portDemand_total, zeroT, zeroF]

/-- One further edge between arbitrary vertices on opposite sides of the triple
matching realizes every balanced boundary of the augmented graph. -/
public theorem triple_matching_adjoin_connects [Fintype V] [Fintype W] [DecidableEq E] [DecidableEq F]
    (a : Fin 3 → V) (b : Fin 3 → W) (ha : Function.Injective a) (hb : Function.Injective b)
    (left : ∀ β : V → ZMod 3, ∑ v, β v = 0 → (G.realizesBoundary β ↔ β ≠ 0))
    (right : ∀ β : W → ZMod 3, ∑ v, β v = 0 → (H.realizesBoundary β ↔ β ≠ 0))
    (x : V) (y : W) (γ : V ⊕ W → ZMod 3) (mass : ∑ j, γ j = 0) :
    0 < ((G.joinPorts H a b).adjoinReferenceEdge (.inl x) (.inr y)).orientationBoundaryCount γ := by
  classical
  let emb : V ↪ V ⊕ W := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
  let S := univ.map emb
  apply (G.joinPorts H a b).boundaryCount_pos_adjoin_across_constant_hole_sum S 0 _ _ _
    (mem_map.mpr ⟨x, mem_univ _, rfl⟩) (by simp [S, emb]) γ mass
  intro δ valid hole
  let l (v : V) := δ (.inl v)
  let r (w : W) := δ (.inr w)
  have split : Sum.elim l r = δ := by funext j; cases j <;> rfl
  have zero : (∑ v, l v) + ∑ w, r w = 0 := by simpa only [Fintype.sum_sum_type] using valid
  have missing : ¬ (G.joinPorts H a b).realizesBoundary (Sum.elim l r) := by
    simp [split, realizesBoundary_iff_count_pos, hole]
  have holes := (G.triple_matching_join_holes H a b ha hb left right l r zero).mp missing
  have shore : ∑ j ∈ S, δ j = ∑ v, l v := by
    unfold S
    rw [sum_map]
    rfl
  have zt : portTotal (fun _ : Fin 3 => true) = 0 := by decide
  have zf : portTotal (fun _ : Fin 3 => false) = 0 := by decide
  rcases holes with ⟨lt, _⟩ | ⟨lf, _⟩
  · rw [shore, lt, portDemand_total, zt]
  · rw [shore, lf, portDemand_total, zf]

end FinMultigraph
