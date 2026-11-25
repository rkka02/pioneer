module

public import Tutte3Flow.Challenge
public import Mathlib.Data.Fin.VecNotation
import Tutte3Flow.Equivalence
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-! # Non-vacuity and sharpness of the connectivity hypothesis -/

@[expose] public section

namespace Tutte3Flow.Sanity

/-- Four distinct edges from vertex `false` to vertex `true`. -/
def fourParallel : FinMultigraph Bool (Fin 4) where
  src _ := false
  dst _ := true

theorem fourParallel_sanity :
    fourParallel.IsKEdgeConnected 4 ∧ fourParallel.HasNowhereZeroIntFlow 3 := by
  constructor
  · unfold FinMultigraph.IsKEdgeConnected
    decide
  · refine ⟨![1, 1, -1, -1], ?_⟩
    unfold FinMultigraph.IsNowhereZeroIntFlow
    decide

/-- The six edges of the complete graph on four vertices, directed from smaller to larger. -/
def K4 : FinMultigraph (Fin 4) (Fin 6) where
  src := ![0, 0, 0, 1, 1, 2]
  dst := ![1, 2, 3, 2, 3, 3]

theorem K4_sharpness : K4.IsKEdgeConnected 3 ∧ ¬ K4.HasNowhereZeroIntFlow 3 := by
  constructor
  · unfold FinMultigraph.IsKEdgeConnected
    decide
  · intro h
    -- Check all 64 orientations of the six edges.
    have noOrientation : ¬ K4.HasMod3Orientation := by
      unfold FinMultigraph.HasMod3Orientation
      decide
    exact noOrientation (K4.hasMod3Orientation_iff_hasNowhereZeroZMod3Flow.mpr
      (K4.hasNowhereZeroZMod3Flow_of_hasNowhereZeroIntFlow h))

end Tutte3Flow.Sanity
