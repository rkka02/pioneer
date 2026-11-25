module

public import Tutte3Flow.EdgeInsertion
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

/-! # A five-edge-connected rooted graph requiring a branched transfer at one edge -/

namespace Tutte3Flow.TransferExample

open Finset FinMultigraph

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The deleted edge runs from 1 to 2. The old orientation has a fixed star at vertex 0. -/
@[expose] public def partialGraph : FinMultigraph (Fin 4) (Fin 9) where
  src := ![1, 1, 2, 2, 0, 3, 3, 3, 3]
  dst := ![0, 0, 0, 0, 3, 1, 1, 2, 2]

@[expose] public def pinned (e : Fin 9) : Prop := e.val < 5

public theorem partial_balanced : ∀ v, partialGraph.mod3Divergence (fun _ => 1) v = 0 := by
  decide

/-- The actual graph in the frozen representation satisfies both cut assumptions. -/
public theorem insertion_cuts :
    (partialGraph.adjoinReferenceEdge 1 2).IsKEdgeConnected 5 ∧
    ∀ S : Finset (Fin 4), S.card = 2 →
      6 ≤ ((partialGraph.adjoinReferenceEdge 1 2).cutEdges S).card := by
  unfold IsKEdgeConnected
  decide

/-- The pins and balance determine the entire partial orientation. -/
public theorem forced_free_directions (r : Fin 9 → Bool)
    (fixed : ∀ e, pinned e → r e = false)
    (balanced : ∀ v, (partialGraph.reorient r).mod3Divergence (fun _ => 1) v = 0) :
    ∀ e, r e = false := by
  revert r
  unfold pinned
  decide

/-- Every free arc in that orientation starts at vertex 3, so neither terminal can start a path. -/
public theorem free_arcs_from_three : ∀ e, ¬ pinned e → partialGraph.src e = 3 := by
  unfold pinned
  decide

/-- The least number of free arcs attaining either sign of the terminal demand is three. -/
public theorem shortest_transfer :
    (∃ b : Fin 9 → Bool, (∀ e, pinned e → b e = false) ∧
      (univ.filter (fun e => b e = true)).card = 3 ∧
      ∀ v, partialGraph.mod3Divergence (fun e => if b e then 1 else 0) v =
        (if 1 = v then 1 else 0) - (if 2 = v then 1 else 0)) ∧
    (∀ (b : Fin 9 → Bool) (s : ZMod 3), s ≠ 0 → (∀ e, pinned e → b e = false) →
      (∀ v, partialGraph.mod3Divergence (fun e => if b e then 1 else 0) v =
        (if 1 = v then s else 0) - (if 2 = v then s else 0)) →
      3 ≤ (univ.filter (fun e => b e = true)).card) := by
  constructor
  · refine ⟨![false, false, false, false, false, true, true, true, false], ?_⟩
    unfold pinned
    decide
  · unfold pinned
    decide

public theorem full_integer_flow :
    (partialGraph.adjoinReferenceEdge 1 2).HasNowhereZeroIntFlow 3 := by
  apply (partialGraph.hasNowhereZeroIntFlow_adjoin_iff_transfer 1 2 partial_balanced).mpr
  refine ⟨![false, false, false, false, false, true, true, true, false], -1, ?_⟩
  decide

end Tutte3Flow.TransferExample
