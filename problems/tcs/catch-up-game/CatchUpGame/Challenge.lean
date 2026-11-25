import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Attach

/-!
# The Catch-Up Game Even-Sum Draw Conjecture (Frozen Challenge Statement)

Reference:
- A. Isaksen, M. Ismail, S. J. Brams, A. Nealen,
  *Catch-Up: A Game in Which the Lead Alternates*,
  Game & Puzzle Design 1(2), 38–49 (2015).
- Upstream formalization: `google-deepmind/formal-conjectures`
  (`FormalConjectures/Paper/CatchUpConjecture.lean`).

Statement: Let `T_N = N * (N + 1) / 2`. Whenever `T_N` is even (equivalently
`N ≡ 0 (mod 4)` or `N ≡ 3 (mod 4)`), optimal play in `Catch-Up({1, ..., N})`
results in a draw.

THIS FILE IS FROZEN AND READ-ONLY. DO NOT MODIFY.
-/

namespace CatchUpGame

/-- An arbitrary two-element type indexing the players in the Catch-Up game. -/
inductive Player
  | p1
  | p2
deriving DecidableEq, Repr

/-- Returns the other player. -/
def Player.other : Player → Player
  | p1 => p2
  | p2 => p1

/-- The possible outcomes of a Catch-Up game. -/
inductive Outcome
  | win
  | loss
  | draw
deriving DecidableEq, Repr

/-- Negates an outcome, swapping win and loss. -/
def Outcome.neg : Outcome → Outcome
  | win => loss
  | loss => win
  | draw => draw

/-- Computes the best outcome for the current player from a list of possible outcomes
(Win > Draw > Loss). -/
def Outcome.best (os : List Outcome) : Outcome :=
  os.foldl (fun
    | .win,  _     => .win
    | _,     .win  => .win
    | .draw, _     => .draw
    | _,     .draw => .draw
    | _,     _     => .loss) .loss

/-- Recursive game-theoretic value of Catch-Up from the current player's perspective. -/
noncomputable def valueAux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : Outcome :=
  if remaining = ∅ then
    if s_me > s_opp then
      .win
    else if s_opp > s_me then
      .loss
    else
      .draw
  else
    if s_me + remaining.sum (fun x => x) < s_opp then
      .loss
    else
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, _⟩ =>
        let s_me' := s_me + x
        let remaining' := remaining.erase x
        if isFirstMove then
          (valueAux remaining' s_opp s_me' false).neg
        else
          if s_me' ≥ s_opp then
            (valueAux remaining' s_opp s_me' false).neg
          else
            valueAux remaining' s_me' s_opp false
      )
      .best outcomes
termination_by remaining.card
decreasing_by
  all_goals
    simpa [remaining'] using Finset.card_erase_lt_of_mem ‹_›

/-- The game-theoretic value of Catch-Up on `S` from Player 1's perspective. -/
noncomputable def value (S : Finset ℕ) : Outcome :=
  valueAux S 0 0 true

/-- **Catch-Up Even-Sum Draw Conjecture (Isaksen–Ismail–Brams–Nealen, 2015):**
Whenever `N * (N + 1) / 2` is even, optimal play in `Catch-Up({1, ..., N})` ends in a draw. -/
def CatchUpConjecture : Prop :=
  ∀ (N : ℕ), Even (N * (N + 1) / 2) → value (Finset.Icc 1 N) = .draw

end CatchUpGame
