module

public import Tutte3Flow.MatchingJoin
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-! # All missing boundaries of a tree of one-hole blocks

The indexing tree is presented by attaching leaves in any order. Each attachment
names one existing block and chooses three distinct endpoints on each side. -/

namespace FinMultigraph

open Finset

universe u w

variable {V W : Type u} {E F : Type w} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq W]

/-- Every balanced boundary other than zero is realizable, and zero is missing. -/
@[expose] public def IsOneHole (G : FinMultigraph V E) : Prop :=
  ∀ γ : V → ZMod 3, ∑ v, γ v = 0 → (G.realizesBoundary γ ↔ γ ≠ 0)

omit [Fintype V] in
/-- Reversing every edge negates its realized boundary. -/
public theorem realizesBoundary_neg_iff (G : FinMultigraph V E) (γ : V → ZMod 3) :
    G.realizesBoundary (-γ) ↔ G.realizesBoundary γ := by
  have flip {δ : V → ZMod 3} : G.realizesBoundary δ → G.realizesBoundary (-δ) := by
    rintro ⟨t, rfl⟩
    refine ⟨fun e => !(t e), ?_⟩
    funext v
    have sign (e : E) : (if !(t e) then (1 : ZMod 3) else -1) = -(if t e then 1 else -1) := by
      cases t e <;> decide
    simp only [sign, mod3Divergence, sum_neg_distrib, Pi.neg_apply]
    abel
  exact ⟨fun h => neg_neg γ ▸ flip h, flip⟩

/-- A unique missing balanced boundary must be zero, since negation preserves failure. -/
public theorem isOneHole_iff_unique_missing (G : FinMultigraph V E) :
    G.IsOneHole ↔ ∃! γ : V → ZMod 3, (∑ v, γ v) = 0 ∧ ¬ G.realizesBoundary γ := by
  classical
  constructor
  · intro h
    exact ⟨0, ⟨by simp, fun r => (h 0 (by simp)).mp r rfl⟩,
      fun γ gap => not_not.mp (fun ne => gap.2 ((h γ gap.1).mpr ne))⟩
  · rintro ⟨γ, ⟨mass, gap⟩, unique⟩
    have opposite : -γ = γ := unique (-γ)
      ⟨by simp only [Pi.neg_apply, sum_neg_distrib, mass, neg_zero],
       fun r => gap ((G.realizesBoundary_neg_iff γ).mp r)⟩
    have zero : γ = 0 := by
      funext v
      exact (show ∀ x : ZMod 3, -x = x → x = 0 by decide) (γ v) (congrFun opposite v)
    subst γ
    intro δ total
    constructor
    · rintro r rfl
      exact gap r
    · intro ne
      by_contra absent
      exact ne (unique δ ⟨total, absent⟩)

/-- The kernel-computed four-clique signature gives an initial block for the induction. -/
public theorem fourCliqueFibre_isOneHole : fourCliqueFibre.IsOneHole := by
  intro γ mass
  rw [realizesBoundary_iff_count_pos]
  exact fourCliqueFibre_boundary_signature γ mass

/-- Block zero denotes the new leaf; existing block numbers move up by one. -/
@[expose] public def joinedBlock (block : V → ℕ) : V ⊕ W → ℕ :=
  Sum.elim (fun v => block v + 1) (fun _ => 0)

/-- A tree-edge coefficient contributes the same sign at all six of its port endpoints. -/
@[expose] public def joinedCode {k : ℕ} (code : (Fin k → Bool) → V → ZMod 3)
    (a : Fin 3 → V) (b : Fin 3 → W) (c : Fin (k + 1) → Bool) : V ⊕ W → ZMod 3 :=
  Sum.elim (code (fun i => c i.succ) + portDemand a (fun _ => c 0))
           (portDemand b (fun _ => c 0))

/-- Leaf-attachment construction. The index counts tree edges, and there is one
initial block. No restriction is placed on reuse of a port vertex by later matchings. -/
public inductive MatchingTree : {V : Type u} → {E : Type w} → [Fintype V] → [Fintype E] → [DecidableEq V] →
    (k : ℕ) → FinMultigraph V E → (V → ℕ) → ((Fin k → Bool) → V → ZMod 3) → Prop where
  | single {V : Type u} {E : Type w} [Fintype V] [Fintype E] [DecidableEq V] (G : FinMultigraph V E)
      (hole : G.IsOneHole) :
      MatchingTree 0 G (fun _ => 0) (fun _ _ => 0)
  | attach {V W : Type u} {E F : Type w} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
      [DecidableEq V] [DecidableEq W] {k : ℕ} {G : FinMultigraph V E}
      {block : V → ℕ} {code : (Fin k → Bool) → V → ZMod 3}
      (old : MatchingTree k G block code) (H : FinMultigraph W F) (leaf : H.IsOneHole)
      (parent : ℕ) (a : Fin 3 → V) (b : Fin 3 → W) (atParent : ∀ i, block (a i) = parent)
      (ha : Function.Injective a) (hb : Function.Injective b) :
      MatchingTree (k + 1) (G.joinPorts H a b) (joinedBlock block) (joinedCode code a b)

/-- The four induction invariants. Projection omitting any designated block
recovers every tree coefficient. -/
public structure MatchingTreeLaw {k : ℕ} (G : FinMultigraph V E) (block : V → ℕ)
    (code : (Fin k → Bool) → V → ZMod 3) : Prop where
  recover : ∀ j c d, (∀ v, block v ≠ j → code c v = code d v) → c = d
  mass : ∀ c, ∑ v, code c v = 0
  blockMass : ∀ c j, ∑ v ∈ univ.filter (fun v => block v = j), code c v = 0
  holes : ∀ γ : V → ZMod 3, ∑ v, γ v = 0 → (¬ G.realizesBoundary γ ↔ ∃ c, γ = code c)

private theorem constant_triple_total (t : Bool) : portTotal (fun _ : Fin 3 => t) = 0 := by
  cases t <;> decide

omit [Fintype V] in
private theorem neg_portDemand_flip (a : Fin 3 → V) (t : Bool) :
    -portDemand a (fun _ => !t) = portDemand a (fun _ => t) := by
  funext v
  cases t <;> simp [portDemand]

omit [Fintype V] in
private theorem portDemand_off_block (block : V → ℕ) (a : Fin 3 → V) (j : ℕ)
    (atJ : ∀ i, block (a i) = j) (v : V) (outside : block v ≠ j) (s : Fin 3 → Bool) :
    portDemand a s v = 0 := by
  have h (i : Fin 3) : a i ≠ v := by
    rintro rfl
    exact outside (atJ i)
  simp [portDemand, h]

private theorem portDemand_on_block_sum (block : V → ℕ) (a : Fin 3 → V) (parent j : ℕ)
    (atParent : ∀ i, block (a i) = parent) (t : Bool) :
    ∑ v ∈ univ.filter (fun v => block v = j), portDemand a (fun _ => t) v = 0 := by
  unfold portDemand
  rw [sum_fiberwise_eq_sum_filter]
  by_cases eq : parent = j
  · simpa [atParent, eq, portTotal] using constant_triple_total t
  · simp [atParent, eq]

omit [Fintype W] in
private theorem joinedCode_recover {k : ℕ} (G : FinMultigraph V E) (block : V → ℕ)
    (code : (Fin k → Bool) → V → ZMod 3) (old : MatchingTreeLaw G block code)
    (a : Fin 3 → V) (b : Fin 3 → W) (parent : ℕ) (atParent : ∀ i, block (a i) = parent)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (j : ℕ) (c d : Fin (k+1) → Bool)
    (same : ∀ v, joinedBlock block v ≠ j → joinedCode code a b c v = joinedCode code a b d v) :
    c = d := by
  let l := fun i : Fin k => c i.succ
  let r := fun i : Fin k => d i.succ
  have assemble (head : c 0 = d 0) (tail : l = r) : c = d := by
    funext i
    exact Fin.cases head (fun i => congrFun tail i) i
  cases j with
  | zero =>
    have eq (v : V) : code l v + portDemand a (fun _ => c 0) v =
        code r v + portDemand a (fun _ => d 0) v := same (.inl v) (by simp [joinedBlock])
    have tail : l = r := old.recover parent l r (fun v outside => by
      simpa only [portDemand_off_block block a parent atParent v outside, add_zero] using eq v)
    have ports : portDemand a (fun _ => c 0) = portDemand a (fun _ => d 0) := by
      funext v
      exact add_left_cancel (tail ▸ eq v)
    exact assemble (congrFun (portDemand_injective ha ports) 0) tail
  | succ j =>
    have ports : portDemand b (fun _ => c 0) = portDemand b (fun _ => d 0) :=
      funext (fun w => same (.inr w) (by simp [joinedBlock]))
    have head := congrFun (portDemand_injective hb ports) 0
    apply assemble head (old.recover j l r ?_)
    intro v hv
    have eq := same (.inl v) (by simpa [joinedBlock] using hv)
    change code l v + portDemand a (fun _ => c 0) v = code r v + portDemand a (fun _ => d 0) v at eq
    rw [show c 0 = d 0 from head] at eq
    exact add_right_cancel eq

private theorem old_forbids_one {k : ℕ} (G : FinMultigraph V E) (block : V → ℕ)
    (code : (Fin k → Bool) → V → ZMod 3) (old : MatchingTreeLaw G block code)
    (a : Fin 3 → V) (parent : ℕ) (atParent : ∀ i, block (a i) = parent)
    (ha : Function.Injective a) (γ : V → ZMod 3) (s t : Fin 3 → Bool)
    (hs : ∃ c, γ = code c + portDemand a s) (ht : ∃ c, γ = code c + portDemand a t) : s = t := by
  obtain ⟨c, hc⟩ := hs
  obtain ⟨d, hd⟩ := ht
  have coincide := hc.symm.trans hd
  have cd : c = d := old.recover parent c d (fun v hv => by
    simpa only [Pi.add_apply, portDemand_off_block block a parent atParent v hv, add_zero]
      using congrFun coincide v)
  subst d
  exact portDemand_injective ha (add_left_cancel coincide)

private theorem joinedCode_holes {k : ℕ} (G : FinMultigraph V E) (H : FinMultigraph W F)
    (block : V → ℕ) (code : (Fin k → Bool) → V → ZMod 3) (old : MatchingTreeLaw G block code)
    (leaf : H.IsOneHole) (a : Fin 3 → V) (b : Fin 3 → W) (parent : ℕ)
    (atParent : ∀ i, block (a i) = parent) (ha : Function.Injective a) (hb : Function.Injective b)
    (γ : V → ZMod 3) (δ : W → ZMod 3) (valid : (∑ v, γ v) + ∑ w, δ w = 0) :
    ¬ (G.joinPorts H a b).realizesBoundary (Sum.elim γ δ) ↔
      ∃ c, Sum.elim γ δ = joinedCode code a b c := by
  classical
  let d := ∑ v, γ v
  let P (s : Fin 3 → Bool) := ∃ c, γ = code c + portDemand a s
  let Q (s : Fin 3 → Bool) := δ = -portDemand b s
  have ml (s : Fin 3 → Bool) : ∑ v, (γ - portDemand a s) v = d - portTotal s := by
    simp [d, sum_sub_distrib, portDemand_total]
  have mr (s : Fin 3 → Bool) (hs : portTotal s = d) : ∑ w, (δ + portDemand b s) w = 0 := by
    simpa [sum_add_distrib, portDemand_total, hs, d, add_comm] using valid
  have rule : ¬ (G.joinPorts H a b).realizesBoundary (Sum.elim γ δ) ↔
      ∀ s : Fin 3 → Bool, portTotal s = d → P s ∨ Q s := by
    rw [joinPorts_realizes_iff]
    constructor
    · intro missing s hs
      by_contra! neither
      apply missing
      refine ⟨s, ?_, (leaf _ (mr s hs)).mpr (fun eq => neither.2 (eq_neg_of_add_eq_zero_left eq))⟩
      by_contra gap
      obtain ⟨c, hc⟩ := (old.holes _ (by rw [ml, hs, sub_self])).mp gap
      exact neither.1 ⟨c, sub_eq_iff_eq_add.mp hc⟩
    · rintro excluded ⟨s, l, r⟩
      have zero := G.realizable_mass l
      rw [ml, sub_eq_zero] at zero
      rcases excluded s zero.symm with ⟨c, hc⟩ | bad
      · exact (old.holes _ (by rw [ml, zero, sub_self])).mpr ⟨c, sub_eq_iff_eq_add.mpr hc⟩ l
      · exact (leaf _ (mr s zero.symm)).mp r (by rw [bad, neg_add_cancel])
  have oneR (s t : Fin 3 → Bool) (hs : Q s) (ht : Q t) := portDemand_injective hb (neg_inj.mp (hs.symm.trans ht))
  rw [rule, triple_port_cover_iff d P Q (old_forbids_one G block code old a parent atParent ha γ) oneR]
  constructor
  · rintro ⟨_, pair⟩
    have assemble (t : Bool) (leftGap : P (fun _ => t)) (rightGap : Q (fun _ => !t)) :
        ∃ c, Sum.elim γ δ = joinedCode code a b c := by
      obtain ⟨l, hl⟩ := leftGap
      refine ⟨Fin.cons t l, ?_⟩
      funext v
      cases v with
      | inl v => simpa [joinedCode, Fin.cons_succ, Fin.cons_zero] using congrFun hl v
      | inr w =>
        have eq := rightGap.trans (neg_portDemand_flip b t)
        simpa [joinedCode, Fin.cons_zero] using congrFun eq w
    exact pair.elim (fun h => assemble true h.1 h.2) (fun h => assemble false h.1 h.2)
  · rintro ⟨c, hc⟩
    have L : γ = code (fun i => c i.succ) + portDemand a (fun _ => c 0) := funext (fun v => congrFun hc (.inl v))
    have R : δ = portDemand b (fun _ => c 0) := funext (fun w => congrFun hc (.inr w))
    have rightGap : Q (fun _ => !(c 0)) := R.trans (neg_portDemand_flip b (c 0)).symm
    have leftGap : P (fun _ => c 0) := ⟨_, L⟩
    refine ⟨?_, ?_⟩
    · simp [d, L, sum_add_distrib, old.mass, portDemand_total, constant_triple_total]
    · cases head : c 0 with
      | false => exact Or.inr ⟨head ▸ leftGap, by simpa only [head, Bool.not_false, Bool.not_true] using rightGap⟩
      | true => exact Or.inl ⟨head ▸ leftGap, by simpa only [head, Bool.not_false, Bool.not_true] using rightGap⟩

private theorem joinedCode_blockMass {k : ℕ} (G : FinMultigraph V E) (block : V → ℕ)
    (code : (Fin k → Bool) → V → ZMod 3) (old : MatchingTreeLaw G block code)
    (a : Fin 3 → V) (b : Fin 3 → W) (parent : ℕ) (atParent : ∀ i, block (a i) = parent)
    (c : Fin (k+1) → Bool) (j : ℕ) :
    ∑ v ∈ univ.filter (fun v => joinedBlock block v = j), joinedCode code a b c v = 0 := by
  classical
  rw [sum_filter, Fintype.sum_sum_type]
  simp only [joinedBlock, joinedCode, Sum.elim_inl, Sum.elim_inr]
  cases j with
  | zero => simp [portDemand_total, constant_triple_total]
  | succ j =>
    simp only [Nat.add_one, Nat.succ.injEq, Nat.zero_ne_add_one, ite_false, sum_const_zero, add_zero]
    rw [← sum_filter]
    simp only [Pi.add_apply, sum_add_distrib, old.blockMass, portDemand_on_block_sum block a parent j atParent, add_zero]

/-- Complete induction on the leaf-attachment presentation of any finite tree. -/
public theorem matchingTree_law {k : ℕ} {G : FinMultigraph V E} {block : V → ℕ}
    {code : (Fin k → Bool) → V → ZMod 3} (tree : MatchingTree k G block code) :
    MatchingTreeLaw G block code := by
  classical
  induction tree with
  | single G one =>
    refine ⟨fun _ _ _ _ => Subsingleton.elim _ _, by simp, by simp, ?_⟩
    intro γ h
    simp [one γ h]
    rfl
  | attach tree H one parent a b atParent ha hb ih =>
    refine ⟨joinedCode_recover _ _ _ ih a b parent atParent ha hb, ?_,
      joinedCode_blockMass _ _ _ ih a b parent atParent, ?_⟩
    · intro c
      simp [joinedCode, Fintype.sum_sum_type, sum_add_distrib, ih.mass, portDemand_total, constant_triple_total]
    · intro γ valid
      have split : Sum.elim (fun v => γ (.inl v)) (fun w => γ (.inr w)) = γ := by
        funext j; cases j <;> rfl
      have eq := joinedCode_holes _ H _ _ ih one a b parent atParent ha hb (fun v => γ (.inl v))
        (fun w => γ (.inr w)) (by simpa only [Fintype.sum_sum_type] using valid)
      rwa [split] at eq

/-- Even after omitting all vertices in any one block, the coefficients are unique. -/
public theorem matchingTree_recover_omitting {k : ℕ} {G : FinMultigraph V E} {block : V → ℕ}
    {code : (Fin k → Bool) → V → ZMod 3} (tree : MatchingTree k G block code)
    (j : ℕ) (c d : Fin k → Bool) (same : ∀ v, block v ≠ j → code c v = code d v) : c = d :=
  (matchingTree_law tree).recover j c d same

/-- Exactly the signed sums of the six marked endpoints per tree edge are holes. -/
public theorem matchingTree_missing_iff {k : ℕ} {G : FinMultigraph V E} {block : V → ℕ}
    {code : (Fin k → Bool) → V → ZMod 3} (tree : MatchingTree k G block code)
    (γ : V → ZMod 3) (mass : ∑ v, γ v = 0) :
    ¬ G.realizesBoundary γ ↔ ∃ c, γ = code c := (matchingTree_law tree).holes γ mass

/-- Finite set of missing balanced boundaries, with labelled vertices. -/
@[expose] public noncomputable def missingBoundaries (G : FinMultigraph V E) : Finset (V → ZMod 3) := by
  classical exact univ.filter (fun γ => ∑ v, γ v = 0 ∧ ¬ G.realizesBoundary γ)

/-- A tree with k edges and k+1 blocks has exactly 2^k missing balanced boundaries. -/
public theorem matchingTree_hole_count {k : ℕ} {G : FinMultigraph V E} {block : V → ℕ}
    {code : (Fin k → Bool) → V → ZMod 3} (tree : MatchingTree k G block code) :
    G.missingBoundaries.card = 2^k := by
  classical
  have law := matchingTree_law tree
  have inj : Function.Injective code := fun c d eq => law.recover 0 c d (fun v _ => congrFun eq v)
  have image : G.missingBoundaries = univ.image code := by
    ext γ
    simp only [missingBoundaries, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨mass, gap⟩
      obtain ⟨c, hc⟩ := (law.holes γ mass).mp gap
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨law.mass c, (law.holes _ (law.mass c)).mpr ⟨c, rfl⟩⟩
  rw [image, card_image_of_injective _ inj]
  simp

/-- Any single edge between different blocks repairs every balanced boundary. -/
public theorem matchingTree_one_edge_repair [DecidableEq E] {k : ℕ} {G : FinMultigraph V E}
    {block : V → ℕ} {code : (Fin k → Bool) → V → ZMod 3} (tree : MatchingTree k G block code)
    (x y : V) (separate : block x ≠ block y) (γ : V → ZMod 3) (mass : ∑ v, γ v = 0) :
    0 < (G.adjoinReferenceEdge x y).orientationBoundaryCount γ := by
  classical
  let S := univ.filter (fun v => block v = block x)
  apply G.boundaryCount_pos_adjoin_across_constant_hole_sum S 0 _ x y
    (by simp [S]) (by simp [S, Ne.symm separate]) γ mass
  intro δ valid gap
  have absent : ¬ G.realizesBoundary δ := by simp [realizesBoundary_iff_count_pos, gap]
  obtain ⟨c, rfl⟩ := (matchingTree_missing_iff tree δ valid).mp absent
  exact (matchingTree_law tree).blockMass c (block x)

end FinMultigraph
