module

public import TxGraffiti3.Bounds
meta import TxGraffiti3.Bounds
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Eval
import Lean.Data.RArray

/-! The elaborator computes candidate *data*. The kernel verifies every row against
`Bounds.Valid`. The soundness theorem applies to every table that passes the check. -/

@[expose] public section

namespace TxGraffiti3.Counterexample

open Bounds

abbrev V := Fin 42

def graph6 := (include_str "../scripts/counterexample.g6").trimAscii.toString
def codes : Array ℕ := eval% graph6.toList.toArray.map Char.toNat

/-- Graph6 lists the strict upper triangle by columns, most significant bit first. -/
def edgeBit (u v : V) : Bool :=
  let j := max u.val v.val
  let t := j * (j - 1) / 2 + min u.val v.val
  u != v && (codes[1 + t / 6]! - 63).testBit (5 - t % 6)

def makeMask (v : V) : ℕ :=
  (List.finRange 42).foldl (fun s w ↦
    if v == w || edgeBit v w then s ||| (1 <<< w.val) else s) 0

deriving instance Lean.ToExpr for Lean.RArray

def masks : Lean.RArray ℕ := eval% Lean.RArray.ofFn makeMask (by decide)

def neighborhood (v : V) : ℕ := masks.getImpl v.val

set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem encoding_size : codes.size = 145 ∧ codes[0]! = 63 + 42 := by decide +kernel

theorem neighborhood_spec : ∀ u v : V,
    InMask (neighborhood u) v ↔ u = v ∨ edgeBit u v = true := by decide +kernel

theorem symmetric : ∀ u v : V, InMask (neighborhood u) v → InMask (neighborhood v) u := by
  decide +kernel

theorem diagonal : ∀ v : V, InMask (neighborhood v) v := by decide +kernel

def full : ℕ := 2^42 - 1

theorem full_mem : ∀ v : V, InMask full v := by decide +kernel

def graph : SimpleGraph V where
  Adj u v := u ≠ v ∧ InMask (neighborhood u) v
  symm := ⟨fun u v h ↦ ⟨Ne.symm h.1, symmetric u v h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance : DecidableRel graph.Adj := fun u v ↦
  inferInstanceAs (Decidable (u ≠ v ∧ InMask (neighborhood u) v))

/-- Independent list of the neighborhoods of vertices 26 through 41 in the written proof. -/
def unmatchedRows : Array (List ℕ) :=
  #[[19, 20, 23], [0, 15, 16], [13, 20, 25], [9, 17, 23], [5, 7, 10], [1, 15, 18],
    [9, 13, 22], [2, 5, 7], [0, 14, 21], [14, 16, 18], [2, 4, 24], [3, 8, 24],
    [6, 10, 12], [1, 19, 21], [11, 12, 22], [8, 17, 25]]

def listedEdge (u v : V) : Bool :=
  let a := min u.val v.val
  let b := max u.val v.val
  if b < 26 then
    (a != b && a/2 == b/2) || (a == 3 && b == 4) || (a == 6 && b == 11)
  else
    (unmatchedRows.getD (b-26) []).contains a

theorem adjacency_table : ∀ u v : V, graph.Adj u v ↔ listedEdge u v = true := by
  decide +kernel

theorem cubic : ∀ v : V, graph.degree v = 3 := by decide +kernel

theorem edge_count : graph.edgeFinset.card = 63 := by
  have h := graph.sum_degrees_eq_twice_card_edges
  simp [cubic] at h
  omega

private def distance (v : V) : ℕ :=
  #[0, 1, 8, 7, 8, 9, 8, 9, 5, 5, 8, 8, 6, 5, 2, 2, 2, 3, 3, 3, 3, 2,
    6, 5, 6, 5, 4, 1, 4, 4, 9, 2, 6, 9, 1, 3, 7, 6, 7, 2, 7, 4][v.val]!

theorem connected : graph.Connected := by
  have step : ∀ v : V, v ≠ 0 → ∃ u : V, distance u < distance v ∧ graph.Adj u v := by
    decide +kernel
  have reach (k : ℕ) : ∀ v : V, distance v = k → graph.Reachable 0 v := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      rintro v rfl
      by_cases h : v = 0
      · subst v
        exact SimpleGraph.Reachable.refl _
      obtain ⟨u, hlt, hadj⟩ := step v h
      exact (ih _ hlt u rfl).trans hadj.reachable
  exact graph.connected_iff_exists_forall_reachable.mpr ⟨0, fun v ↦ reach _ v rfl⟩

private structure SearchState where
  rows : Array (Row 42) := #[]
  index : Std.HashMap ℕ ℕ := {}

/-- Breadth-first order from vertex 15 breaks ties between pivots. -/
private def order : List V :=
  [15, 14, 27, 31, 34, 35, 0, 16, 1, 18, 21, 17, 39, 19, 20, 29, 41, 26,
   28, 9, 23, 8, 25, 13, 32, 22, 37, 24, 12, 40, 3, 36, 38, 11, 2, 4,
   6, 10, 33, 5, 7, 30]

private def component (vertices : List V) (s : ℕ) : ℕ := Id.run do
  let mut seen := s ^^^ (s &&& (s - 1))  -- the lowest set bit
  for _ in vertices do
    let grown := vertices.foldl (fun m v ↦
      if seen.testBit v.val then m ||| neighborhood v else m) seen
    let next := grown &&& s
    if next == seen then break
    seen := next
  return seen

private def zeroRow : Row 42 := ⟨0, 0, .zero⟩

/-- Obtain the index of a previously solved mask or append a recurrence row. -/
private partial def visit (s : ℕ) : StateM SearchState ℕ := do
  if let some i := (← get).index[s]? then return i
  let vertices := order.filter (s.testBit ·.val)
  let mut row := zeroRow
  if let p :: _ := vertices then
    let a := component vertices s
    if a != s then
      let i ← visit a
      let j ← visit (s ^^^ a)
      let rs := (← get).rows
      row := ⟨s, (rs.getD i zeroRow).bound + (rs.getD j zeroRow).bound, .split i j⟩
    else
      let options := fun (v : V) ↦ vertices.filter ((neighborhood v).testBit ·.val)
      let pivot := vertices.foldl (fun best v ↦
        if (options v).length < (options best).length then v else best) p
      let children ← (options pivot).mapM (fun x ↦ visit (cut s (neighborhood x)))
      let rs := (← get).rows
      let vals := children.map (fun i ↦ (rs.getD i zeroRow).bound)
      row := ⟨s, 1 + vals.min?.getD 0, .pivot pivot children⟩
  let i := (← get).rows.size
  modify (fun st ↦ {rows := st.rows.push row, index := st.index.insert s i})
  return i

deriving instance Lean.ToExpr for Bounds.Rule
deriving instance Lean.ToExpr for Bounds.Row

private def makeTable : Lean.RArray (Row 42) :=
  let rs := ((visit full).run {}).2.rows
  if h : 0 < rs.size then Lean.RArray.ofArray rs h else .leaf zeroRow

private def certificate : Lean.RArray (Row 42) := eval% makeTable
private abbrev rowAt := certificate.get

/-- Each entry has a lower-bound proof under the generic recurrence. -/
private theorem checked : ∀ i < 277, Valid neighborhood rowAt i := by decide +kernel

theorem lower : Lower neighborhood full 14 := by
  exact sound symmetric checked 276 (by decide)

end TxGraffiti3.Counterexample
