module

public import Tutte3Flow.Equivalence
public import Tutte3Flow.PrescribedDegrees
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Choose

/-! # Lifting a nonzero residue circulation to signed integer values -/

namespace FinMultigraph

open Finset

/-- Give each row a single supported column. A row has three units of weight,
and a column of weight `3 * q v` receives exactly `q v` rows. -/
private theorem roundThirds {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (w : E → V → ℕ) (q : V → ℕ) (row : ∀ e, ∑ v, w e v = 3)
    (col : ∀ v, ∑ e, w e v = 3 * q v) :
    ∃ owner : E → V, (∀ e, 0 < w e (owner e)) ∧
      ∀ v, ∑ e, (if owner e = v then 1 else 0 : ℕ) = q v := by
  classical
  let support (e : E) := univ.filter (fun v => 0 < w e v)
  have card_eq : Fintype.card E = ∑ v, q v := by
    have h := Finset.sum_comm (f := w) (s := univ) (t := univ)
    simp only [row, col, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Finset.mul_sum] at h
    omega
  have hall (s : Finset E) : s.card ≤ ∑ v ∈ s.biUnion support, q v := by
    let t := s.biUnion support
    have h (e) (he : e ∈ s) : ∑ v ∈ t, w e v = 3 := by
      rw [← row e]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      by_contra! hp
      exact hv (Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨mem_univ _, Nat.pos_of_ne_zero hp⟩⟩)
    have bound : ∑ e ∈ s, ∑ v ∈ t, w e v ≤ ∑ v ∈ t, 3 * q v := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun v _ => col v ▸
        Finset.sum_le_univ_sum_of_nonneg (fun i => Nat.zero_le (w i v))
    simp only [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul,
      ← Finset.mul_sum] at bound
    exact (show s.card ≤ ∑ v ∈ t, q v by omega)
  obtain ⟨owner, hs, loads⟩ := assignWithQuotas support q card_eq hall
  exact ⟨owner, fun e => (Finset.mem_filter.mp (hs e)).2, loads⟩

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] (G : FinMultigraph V E)

/-- Lift the *given* nonzero residue circulation, preserving its value modulo three on every edge. -/
public theorem exists_intFlow_lifting (r : E → ZMod 3) (hn : ∀ e, r e ≠ 0)
    (balance : ∀ v, (∑ e ∈ univ.filter (fun e => G.src e = v), r e) =
                    (∑ e ∈ univ.filter (fun e => G.dst e = v), r e)) :
    ∃ f : E → ℤ, G.IsNowhereZeroIntFlow 3 f ∧ ∀ e, (f e : ZMod 3) = r e := by
  classical
  let w (e : E) (v : V) := (if G.src e = v then (r e).val else 0) +
    (if G.dst e = v then 3 - (r e).val else 0)
  have small (e : E) : (r e).val ≤ 3 := (r e).val_lt.le
  have row (e : E) : ∑ v, w e v = 3 := by
    simp [w, Finset.sum_add_distrib, Nat.add_sub_of_le (small e)]
  have mod_weight (e : E) (v : V) : (w e v : ZMod 3) =
      (if G.src e = v then r e else 0) - (if G.dst e = v then r e else 0) := by
    have three : (3 : ZMod 3) = 0 := by decide
    by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
      simp [w, hs, ht, Nat.cast_sub (small e), three, sub_eq_add_neg]
  have divisible (v : V) : 3 ∣ ∑ e, w e v := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp only [Nat.cast_sum, mod_weight, Finset.sum_sub_distrib]
    simpa only [Finset.sum_filter] using sub_eq_zero.mpr (balance v)
  choose q hq using divisible
  obtain ⟨owner, supported, loads⟩ := roundThirds w q row hq
  have endpoint (e : E) : owner e = G.src e ∨ owner e = G.dst e := by
    by_contra! h
    have pos := supported e
    simp [w, Ne.symm h.1, Ne.symm h.2] at pos
  let f (e : E) : ℤ := ((r e).val : ℤ) - if owner e = G.src e then 3 else 0
  have contribution (e : E) (v : V) :
      (if G.src e = v then f e else 0) - (if G.dst e = v then f e else 0) =
      (w e v : ℤ) - 3 * (if owner e = v then 1 else 0) := by
    rcases endpoint e with he | he <;>
      by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
      by_cases hh : owner e = G.src e <;>
      simp_all [f, w, Nat.cast_sub (small e)]
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro e
    have hlt := (r e).val_lt
    have hpos : (r e).val ≠ 0 := by simpa using hn e
    dsimp [f]
    split <;> constructor <;> (try rw [abs_lt]) <;> omega
  · intro v
    apply sub_eq_zero.mp
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib, contribution]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hl := congrArg (fun n : ℕ => (n : ℤ)) (loads v)
    push_cast at hl
    have hc := congrArg (fun n : ℕ => (n : ℤ)) (hq v)
    push_cast at hc
    omega
  · intro e
    have three : (3 : ZMod 3) = 0 := by decide
    by_cases h : owner e = G.src e <;> simp [f, h, three]

/-- Tutte's change of coefficient group, for the frozen graph representation. -/
public theorem hasMod3Orientation_iff_hasNowhereZeroIntFlow :
    G.HasMod3Orientation ↔ G.HasNowhereZeroIntFlow 3 := by
  rw [G.hasMod3Orientation_iff_hasNowhereZeroZMod3Flow]
  constructor
  · rintro ⟨r, hn, hb⟩
    obtain ⟨f, hf, _⟩ := G.exists_intFlow_lifting r hn hb
    exact ⟨f, hf⟩
  · exact G.hasNowhereZeroZMod3Flow_of_hasNowhereZeroIntFlow

end FinMultigraph
