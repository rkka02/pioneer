import TxGraffiti3.Challenge

/-! Each edge of a maximal matching in an r-regular graph covers at most 2r−1 edges. -/

namespace TxGraffiti3

open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Meets (e f : Sym2 V) : Prop := ∃ v : V, v ∈ e ∧ v ∈ f

theorem maximal_iff_covers {M : Finset (Sym2 V)} :
    IsMaximalEdgeMatching G M ↔
      IsEdgeMatching G M ∧ ∀ e ∈ G.edgeSet, ∃ f ∈ M, Meets e f := by
  classical
  constructor
  · rintro ⟨hm, hmax⟩
    refine ⟨hm, ?_⟩
    intro e he
    by_cases hem : e ∈ M
    · exact ⟨e, hem, e.out.1, e.out_fst_mem, e.out_fst_mem⟩
    by_contra h
    apply hmax e he hem
    constructor
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact he
      · exact hm.1 f hf
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with hae | haM
      · subst a
        rcases Finset.mem_insert.mp hb with hbe | hbM
        · exact .inl hbe.symm
        · exact .inr (fun v hv ↦ h ⟨b, hbM, v, hv⟩)
      · rcases Finset.mem_insert.mp hb with hbe | hbM
        · subst b
          exact .inr (fun v hv ↦ h ⟨a, haM, v, hv.2, hv.1⟩)
        · exact hm.2 a haM b hbM
  · rintro ⟨hm, covers⟩
    refine ⟨hm, ?_⟩
    intro e he hem hins
    obtain ⟨f, hf, v, hve, hvf⟩ := covers e he
    rcases hins.2 e (Finset.mem_insert_self ..) f (Finset.mem_insert_of_mem hf) with rfl | dis
    · exact hem hf
    · exact dis v ⟨hve, hvf⟩

variable [Fintype V] [DecidableRel G.Adj]

private def coveredEdges (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) :=
  e.toFinset.biUnion (fun v ↦ G.incidenceFinset v)

private theorem covered_card_le {r : ℕ} (reg : ∀ v, G.degree v = r)
    (e : Sym2 V) (he : e ∈ G.edgeSet) : (coveredEdges G e).card ≤ 2*r - 1 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hpos : 0 < (G.incidenceFinset u ∩ G.incidenceFinset v).card := by
      apply Finset.card_pos.mpr
      exact ⟨s(u,v), Finset.mem_inter.mpr
        ⟨mem_incidenceFinset.mpr ⟨he, Sym2.mem_mk_left ..⟩,
         mem_incidenceFinset.mpr ⟨he, Sym2.mem_mk_right ..⟩⟩⟩
    have h := Finset.card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
    rw [G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree, reg, reg] at h
    simp only [coveredEdges, Sym2.toFinset_mk_eq, Finset.biUnion_insert, Finset.singleton_biUnion]
    omega

theorem maximal_matching_edge_count {r : ℕ} (reg : ∀ v, G.degree v = r)
    {M : Finset (Sym2 V)} (h : IsMaximalEdgeMatching G M) :
    G.edgeFinset.card ≤ M.card * (2*r - 1) := by
  have hm := maximal_iff_covers.mp h
  have sub : G.edgeFinset ⊆ M.biUnion (coveredEdges G) := by
    intro e he
    obtain ⟨f, hf, v, hve, hvf⟩ := hm.2 e (mem_edgeFinset.mp he)
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_biUnion.mpr
      ⟨v, Sym2.mem_toFinset.mpr hvf, mem_incidenceFinset.mpr ⟨mem_edgeFinset.mp he, hve⟩⟩⟩
  have count (S : Finset (Sym2 V)) : (∀ e ∈ S, e ∈ G.edgeSet) →
      (S.biUnion (coveredEdges G)).card ≤ S.card * (2*r - 1) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert e S he ih =>
      intro hE
      rw [Finset.biUnion_insert, Finset.card_insert_of_notMem he, Nat.succ_mul]
      have ha := covered_card_le reg e (hE e (Finset.mem_insert_self ..))
      have hb := ih (fun f hf ↦ hE f (Finset.mem_insert_of_mem hf))
      exact (Finset.card_union_le ..).trans (by omega)
  exact (Finset.card_le_card sub).trans (count M hm.1.1)

end TxGraffiti3
