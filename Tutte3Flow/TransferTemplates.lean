module

public import Mathlib.Data.Fintype.Basic

/-! # The equality case at the interfaces of the seven-cut family

A mask indexes a subset of the six matching wires, with the first wire in bit zero.
At the unrestricted support lower bound a middle with one branch must use an inward
two-edge fork in the receiving template. Reversing the whole middle uses the same test.
-/

@[expose] public section

namespace Tutte3Flow.SevenCut

abbrev Mask := Fin 64

def leftPorts : List Nat := [1, 0, 4, 5, 2, 3]
def rightPorts : List Nat := [11, 7, 10, 9, 8, 6]
def middleArcs : List (Nat × Nat) :=
  [(0, 1), (2, 0), (6, 0), (11, 0), (4, 1), (1, 8), (11, 1), (5, 2),
   (6, 2), (9, 2), (5, 3), (7, 3), (3, 9), (10, 3), (5, 4), (6, 4),
   (7, 4), (5, 10), (6, 8), (7, 9), (7, 10), (8, 9), (11, 8), (11, 10)]

def marked (ports : List Nat) (m : Mask) : List Nat :=
  (ports.zipIdx.filter (fun p => m.val.testBit p.2)).map Prod.fst

def fork (first : Bool) (l r : Mask) : Bool :=
  let ports := marked leftPorts l ++ marked rightPorts r
  ports.length == 3 && (!first || !ports.contains 6) &&
    ports.any (fun c => ports.all (fun v => v == c || middleArcs.contains (v, c)))

/-- One or two direct terminal arcs may be used at the left cap, at positions 0 and 4. -/
def leftDirect (l : Mask) : Bool := [1, 16, 17].contains l.val

/-- The corresponding positions at the right cap are 0 and 1. -/
def rightDirect (r : Mask) : Bool := [1, 2, 3].contains r.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem fork_table :
    (∀ l r : Mask, leftDirect l = true → fork true l r = true → r = 17) ∧
    (∀ r l : Mask, (r = 17 ∨ r = 48) → fork false l r = true → l = 1) ∧
    (∀ r : Mask, fork false 1 r = true → r = 17 ∨ r = 48) := by
  decide

/-- A first receiving middle, followed by any number of sending/receiving pairs. -/
inductive RightReachable : Mask → Prop where
  | first (l r : Mask) : leftDirect l = true → fork true l r = true → RightReachable r
  | step {r l s : Mask} : RightReachable r → fork false l r = true →
      fork false l s = true → RightReachable s

/-- No odd chain of tight one-branch middles with the pinned first root can finish directly
at the right cap. The graph argument separately shows that equality would give such a chain. -/
theorem no_tight_chain {r : Mask} (h : RightReachable r) : rightDirect r = false := by
  have inv : r = 17 ∨ r = 48 := by
    induction h with
    | first l r hl hf => exact Or.inl (fork_table.1 l r hl hf)
    | @step r l s _ hrl hls ih =>
      have hl := fork_table.2.1 r l ih hrl
      subst l
      exact fork_table.2.2 s hls
  rcases inv with rfl | rfl <;> decide

end Tutte3Flow.SevenCut
