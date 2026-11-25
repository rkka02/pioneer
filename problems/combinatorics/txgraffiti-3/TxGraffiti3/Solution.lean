import TxGraffiti3.Certificate
import TxGraffiti3.Matching

/-! The 42-vertex cubic graph in `scripts/counterexample.g6` refutes the frozen conjecture. -/

namespace TxGraffiti3

namespace Counterexample

open Bounds SimpleGraph

set_option maxRecDepth 12000
set_option maxHeartbeats 0

def dominatingWitness : Finset V :=
  {1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 29}

theorem dominatingWitness_valid : IsNIndepDominatingSet graph 14 dominatingWitness := by
  constructor
  · decide +kernel
  · unfold IsDominating
    decide +kernel
  · decide +kernel

private theorem minimum_eq {P : ℕ → Prop} {k : ℕ} (witness : P k)
    (bound : ∀ m, P m → k ≤ m) : sInf {m | P m} = k :=
  Nat.le_antisymm (Nat.sInf_le witness) (bound _ (Nat.sInf_mem ⟨k, witness⟩))

theorem independent_domination_eq : indepDominationNumber graph = 14 := by
  apply minimum_eq (P := fun m ↦ ∃ D : Finset V, IsNIndepDominatingSet graph m D)
    ⟨dominatingWitness, dominatingWitness_valid⟩
  rintro m ⟨D, hd⟩
  rw [← hd.card_eq]
  apply lower D
  constructor
  · exact fun v _ ↦ full_mem v
  · intro x hx y hy hxy
    by_contra hne
    exact hd.isIndep hx hy hne ⟨hne, hxy⟩
  · intro v _
    rcases hd.isDominating v with hv | ⟨w, hw, hadj⟩
    · exact ⟨v, hv, diagonal v⟩
    · exact ⟨w, hw, hadj.2⟩

def matchingWitness : Finset (Sym2 V) :=
  {s(0,1), s(2,3), s(4,5), s(6,7), s(8,9), s(10,11), s(12,13), s(14,15),
   s(16,17), s(18,19), s(20,21), s(22,23), s(24,25)}

private theorem covers : ∀ u v : V, graph.Adj u v →
    ∃ f ∈ matchingWitness, u ∈ f ∨ v ∈ f := by decide +kernel

theorem matchingWitness_maximal : IsMaximalEdgeMatching graph matchingWitness := by
  apply maximal_iff_covers.mpr
  refine ⟨by decide +kernel, ?_⟩
  intro e
  induction e using Sym2.inductionOn with
  | _ u v =>
    intro he
    obtain ⟨f, hf, huf | hvf⟩ := covers u v he
    · exact ⟨f, hf, u, Sym2.mem_mk_left .., huf⟩
    · exact ⟨f, hf, v, Sym2.mem_mk_right .., hvf⟩

theorem saturation_eq : saturationNumber graph = 13 := by
  apply minimum_eq (P := fun m ↦ ∃ M : Finset (Sym2 V),
    IsMaximalEdgeMatching graph M ∧ M.card = m)
    ⟨matchingWitness, matchingWitness_maximal, by decide +kernel⟩
  rintro m ⟨M, hm, rfl⟩
  have h := maximal_matching_edge_count cubic hm
  rw [edge_count] at h
  omega

end Counterexample

theorem not_TxGraffitiConjecture3 : ¬ TxGraffitiConjecture3 := by
  intro h
  have hin := h Counterexample.V Counterexample.graph 3 Counterexample.cubic (by decide)
  rw [Counterexample.independent_domination_eq, Counterexample.saturation_eq] at hin
  omega

end TxGraffiti3
