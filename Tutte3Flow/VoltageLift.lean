module

public import Tutte3Flow.EdgeInsertion
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-! # Boundary realizations in a signed double cover -/

namespace FinMultigraph

open Finset

variable {V E : Type*} (G : FinMultigraph V E)

/-- Each base edge lifts once at each tail sheet. A switched edge changes sheet. -/
@[expose] public def voltageDoubleCover (switch : E → Bool) :
    FinMultigraph (Bool × V) (Bool × E) where
  src p := (p.1, G.src p.2)
  dst p := (if switch p.2 then !p.1 else p.1, G.dst p.2)

variable [Fintype E] [DecidableEq V]

/-- A switched edge contributes its value with the same sign at both ends. -/
@[expose] public def signedMod3Divergence (switch : E → Bool) (f : E → ZMod 3) (v : V) : ZMod 3 :=
  (∑ e ∈ univ.filter (fun e => G.src e = v), f e) -
  (∑ e ∈ univ.filter (fun e => G.dst e = v), if switch e then -f e else f e)

/-- Adding sheet boundaries gives ordinary divergence. Subtracting sheet boundaries
gives signed divergence on the voltage graph. -/
public theorem voltageDoubleCover_channels (s : E → Bool) (f : Bool × E → ZMod 3) (v : V) :
    (G.voltageDoubleCover s).mod3Divergence f (false, v) +
      (G.voltageDoubleCover s).mod3Divergence f (true, v) =
      G.mod3Divergence (fun e => f (false, e) + f (true, e)) v ∧
    (G.voltageDoubleCover s).mod3Divergence f (false, v) -
      (G.voltageDoubleCover s).mod3Divergence f (true, v) =
      G.signedMod3Divergence s (fun e => f (false, e) - f (true, e)) v := by
  constructor <;>
    simp only [mod3Divergence, signedMod3Divergence, sum_filter,
      Fintype.sum_prod_type_right, Fintype.sum_bool, ← sum_sub_distrib, ← sum_add_distrib] <;>
    apply sum_congr rfl <;> intro e he <;>
    cases h : s e <;> by_cases a : G.src e = v <;> by_cases b : G.dst e = v <;>
    simp [voltageDoubleCover, h, a, b] <;> abel

/-- A nowhere-zero realization on the double cover is equivalent to a pair of base
realizations with complementary supports, for the sum and difference of the demands. -/
public theorem voltageDoubleCover_boundary_iff (s : E → Bool) (γ : Bool × V → ZMod 3) :
    (∃ f : Bool × E → ZMod 3, (∀ p, f p ≠ 0) ∧
      ∀ p, (G.voltageDoubleCover s).mod3Divergence f p = γ p) ↔
    ∃ u w : E → ZMod 3, (∀ e, (u e ≠ 0 ∧ w e = 0) ∨ (u e = 0 ∧ w e ≠ 0)) ∧
      (∀ v, G.mod3Divergence u v = γ (false, v) + γ (true, v)) ∧
      ∀ v, G.signedMod3Divergence s w v = γ (false, v) - γ (true, v) := by
  constructor
  · rintro ⟨f, nz, boundary⟩
    refine ⟨fun e => f (false, e) + f (true, e), fun e => f (false, e) - f (true, e), ?_, ?_, ?_⟩
    · have localRule : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 →
          (a + b ≠ 0 ∧ a - b = 0) ∨ (a + b = 0 ∧ a - b ≠ 0) := by decide
      exact fun e => localRule _ _ (nz (false, e)) (nz (true, e))
    · intro v
      rw [← (G.voltageDoubleCover_channels s f v).1, boundary, boundary]
    · intro v
      rw [← (G.voltageDoubleCover_channels s f v).2, boundary, boundary]
  · rintro ⟨u, w, disjoint, ordinary, signed⟩
    let f (p : Bool × E) : ZMod 3 :=
      if p.1 then -(u p.2 - w p.2) else -(u p.2 + w p.2)
    have inv : ∀ a b : ZMod 3, -(a + b) + -(a - b) = a ∧ -(a + b) - -(a - b) = b := by decide
    have addEq : (fun e => f (false, e) + f (true, e)) = u := funext (fun e => (inv (u e) (w e)).1)
    have subEq : (fun e => f (false, e) - f (true, e)) = w := funext (fun e => (inv (u e) (w e)).2)
    refine ⟨f, ?_, ?_⟩
    · have localRule : ∀ a b : ZMod 3, ((a ≠ 0 ∧ b = 0) ∨ (a = 0 ∧ b ≠ 0)) →
          -(a + b) ≠ 0 ∧ -(a - b) ≠ 0 := by decide
      rintro ⟨i, e⟩
      cases i
      · exact (localRule _ _ (disjoint e)).1
      · exact (localRule _ _ (disjoint e)).2
    · rintro ⟨i, v⟩
      have channels := G.voltageDoubleCover_channels s f v
      rw [addEq, subEq, ordinary, signed] at channels
      have injective : ∀ a b c d : ZMod 3, a + b = c + d ∧ a - b = c - d →
          a = c ∧ b = d := by decide
      cases i
      · exact (injective _ _ _ _ channels).1
      · exact (injective _ _ _ _ channels).2

end FinMultigraph
