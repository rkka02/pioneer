module

public import FEI.ResearchLemmas
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Fixed-order coordinate restrictions and coarse dyadic crossings -/

public noncomputable section
namespace FEI

variable {n : ℕ}

/-- Restrict the first remaining physical coordinate. -/
@[expose] def restrictFirst (f : (Fin (n+1) → Bool) → Bool) (b : Bool) (x : Fin n → Bool) : Bool :=
  f (Fin.cons b x)

/-- Lift a frequency without the first coordinate. -/
@[expose] def liftFrequency (T : Finset (Fin n)) : Finset (Fin (n+1)) := T.map (Fin.succEmb n)

private theorem zero_out (T : Finset (Fin n)) : 0 ∉ liftFrequency T := by
  simp [liftFrequency, Finset.mem_map, Fin.succEmb]

private theorem succ_mem (i : Fin n) (T : Finset (Fin n)) :
    i.succ ∈ liftFrequency T ↔ i ∈ T := by
  simp [liftFrequency, Fin.succEmb]

private def maskEquiv (n : ℕ) : Bool × Finset (Fin n) ≃ Finset (Fin (n+1)) where
  toFun p := if p.1 then insert 0 (liftFrequency p.2) else liftFrequency p.2
  invFun S := (decide (0 ∈ S), Finset.univ.filter fun i => i.succ ∈ S)
  left_inv := by
    rintro ⟨b,T⟩
    cases b <;> simp [zero_out] <;> ext i <;> simp [succ_mem]
  right_inv := by
    intro S
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> by_cases h : 0 ∈ S <;> simp [h, zero_out, succ_mem]

private theorem splitMasks (F : Finset (Fin (n+1)) → ℝ) :
    ∑ S, F S = ∑ T, (F (liftFrequency T) + F (insert 0 (liftFrequency T))) := by
  rw [← (maskEquiv n).sum_comp F, Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
  exact add_comm _ _

private theorem chi_cons (T : Finset (Fin n)) (b : Bool) (x : Fin n → Bool) :
    chi (liftFrequency T) (Fin.cons b x) = chi T x := by
  simp [chi, liftFrequency, Fin.succEmb, Finset.prod_map]

/-- The sum and difference of a Walsh pair are the two child coefficients. -/
theorem fourierCoeff_restrictFirst (f : (Fin (n+1) → Bool) → Bool) (T : Finset (Fin n)) :
    fourierCoeff (restrictFirst f false) T =
      fourierCoeff f (liftFrequency T) + fourierCoeff f (insert 0 (liftFrequency T)) ∧
    fourierCoeff (restrictFirst f true) T =
      fourierCoeff f (liftFrequency T) - fourierCoeff f (insert 0 (liftFrequency T)) := by
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Bool)
  have split (F : (Fin (n+1) → Bool) → ℝ) :
      ∑ x, F x = (∑ x, F (Fin.cons true x)) + ∑ x, F (Fin.cons false x) := by
    rw [← e.sum_comp F, Fintype.sum_prod_type, Fintype.sum_bool]
    rfl
  have ins (b : Bool) (x : Fin n → Bool) :
      chi (insert 0 (liftFrequency T)) (Fin.cons b x) = pm b * chi T x := by
    rw [chi, Finset.prod_insert (zero_out T), Fin.cons_zero]
    exact congrArg (pm b * ·) (chi_cons T b x)
  unfold fourierCoeff
  rw [split (fun x => pm (f x) * chi (liftFrequency T) x),
      split (fun x => pm (f x) * chi (insert 0 (liftFrequency T)) x)]
  simp only [chi_cons, ins, pm, ite_true, Bool.false_eq_true, ite_false, neg_one_mul,
    one_mul, mul_neg, Finset.sum_neg_distrib, restrictFirst, pow_succ]
  constructor <;> ring_nf <;> rfl

/-- The queried influence is exactly the sum of the squared difference coefficients. -/
theorem coordInfluence_first (f : (Fin (n+1) → Bool) → Bool) :
    coordInfluence f 0 = ∑ T, (fourierCoeff f (insert 0 (liftFrequency T)))^2 := by
  rw [coordInfluence_eq_sum, splitMasks]
  simp [zero_out]

/-- Average child influence accounts for every direction except the one revealed. -/
theorem totalInfluence_restrictFirst (f : (Fin (n+1) → Bool) → Bool) :
    totalInfluence f = coordInfluence f 0 +
      (totalInfluence (restrictFirst f false) + totalInfluence (restrictFirst f true))/2 := by
  simp only [totalInfluence_eq_spectralInfluence, spectralInfluence, coordInfluence_first]
  rw [splitMasks]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [(fourierCoeff_restrictFirst f T).1, (fourierCoeff_restrictFirst f T).2,
    Finset.card_insert_of_notMem (zero_out T)]
  simp only [liftFrequency, Finset.card_map, Nat.cast_add, Nat.cast_one]
  ring

/-- Loss on a single grid at a Walsh butterfly. -/
@[expose] def gridStep (h u v : ℝ) : ℝ :=
  gridError h u + gridError h v - (gridError h (u+v) + gridError h (u-v))/2

/-- Coarse loss, retaining exactly the scales whose step exceeds four increments. -/
@[expose] def coarseStep (h u v : ℝ) : ℝ := if 4*|v| < h then gridStep h u v else 0

/-- Distance to the nearest midpoint between consecutive multiples of the step. -/
@[expose] def midpointDistance (h u : ℝ) : ℝ := h/2 - |u-h*(round (u/h):ℤ)|

private theorem unit_fold {x : ℝ} (hx : |x| ≤ 1) :
    gridError 1 x = x^2 - 2*max 0 (|x|-1/2) := by
  obtain ⟨lo,hi⟩ := abs_le.mp hx
  unfold gridError
  simp only [div_one, one_mul]
  by_cases l : x < -(1/2:ℝ)
  · have r : round x = (-1:ℤ) := round_eq_iff.mpr (by constructor <;> push_cast <;> linarith)
    rw [r, abs_of_neg (by linarith), max_eq_right (by linarith)]
    push_cast; ring
  · by_cases u : x < 1/2
    · have r : round x = 0 := round_eq_iff.mpr (by constructor <;> push_cast <;> linarith)
      have h : |x| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [r, max_eq_left (by linarith)]; simp
    · have r : round x = 1 := round_eq_iff.mpr (by constructor <;> push_cast <;> linarith)
      rw [r, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      push_cast; ring

private theorem unit_period (x : ℝ) (a : ℤ) : gridError 1 (x + a) = gridError 1 x := by
  simp only [gridError, div_one, one_mul, round_add_intCast, Int.cast_add]
  ring

private theorem unit_scale {h : ℝ} (hh : 0 < h) (w : ℝ) :
    gridError h w = h^2 * gridError 1 (w/h) := by
  simp only [gridError, div_one, one_mul]
  field_simp

private theorem folded_pair (a b : ℝ) (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/4) :
    max 0 (|a+b|-1/2) + max 0 (|a-b|-1/2) = max 0 (|b|-(1/2-|a|)) := by
  obtain ⟨al,au⟩ := abs_le.mp ha
  obtain ⟨bl,bu⟩ := abs_le.mp hb
  have ordered (x y : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1/2)
      (hy : 0 ≤ y) (hY : y ≤ 1/4) :
      max 0 (|x+y|-1/2) + max 0 (|x-y|-1/2) = max 0 (y-(1/2-x)) := by
    rw [abs_of_nonneg (by linarith), max_eq_left (show |x-y|-1/2 ≤ 0 by
      have := abs_le.mpr (show -(1/2:ℝ) ≤ x-y ∧ x-y ≤ 1/2 by constructor <;> linarith)
      linarith), add_zero]
    congr 1; ring
  by_cases ap : 0 ≤ a <;> by_cases bp : 0 ≤ b
  · simpa only [abs_of_nonneg ap, abs_of_nonneg bp] using ordered a b ap au bp bu
  · have hn : 0 ≤ -b := by linarith
    convert ordered a (-b) ap au hn (by linarith) using 1 <;>
      simp only [abs_of_nonneg ap, abs_of_nonpos (le_of_not_ge bp), sub_neg_eq_add, ← sub_eq_add_neg]; ring
  · have hn : 0 ≤ -a := by linarith
    have eq := ordered (-a) b hn (by linarith) bp bu
    rw [show -a+b = -(a-b) by ring, show -a-b = -(a+b) by ring, abs_neg, abs_neg, add_comm] at eq
    simpa only [abs_of_nonpos (le_of_not_ge ap), abs_of_nonneg bp] using eq
  · have eq := ordered (-a) (-b) (by linarith) (by linarith) (by linarith) (by linarith)
    rw [show -a + -b = -(a+b) by ring, show -a - -b = -(a-b) by ring, abs_neg, abs_neg] at eq
    simpa only [abs_of_nonpos (le_of_not_ge ap), abs_of_nonpos (le_of_not_ge bp)] using eq

/-- At a coarse scale the restriction loss is the actual dyadic midpoint crossing. -/
theorem coarseStep_midpoint {h : ℝ} (hh : 0 < h) (u v : ℝ) (hc : 4*|v| < h) :
    coarseStep h u v = h * max 0 (|v|-midpointDistance h u) := by
  let z := round (u/h)
  let a := u/h - (z:ℝ)
  let b := v/h
  have ha : |a| ≤ 1/2 := abs_sub_round _
  have hb : |b| ≤ 1/4 := by
    change |v/h| ≤ _
    rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]; linarith
  have norm (w : ℝ) (hw : |w| ≤ 1/2) : gridError 1 w = w^2 := by
    rw [unit_fold (by linarith), max_eq_left (by linarith)]; ring
  have hsum : |a+b| ≤ 1 := (abs_add_le ..).trans (by linarith)
  have hdif : |a-b| ≤ 1 := (abs_sub ..).trans (by linarith)
  have e : u/h = a+z := by dsimp [a]; ring
  have ep : (u+v)/h = (a+b)+z := by rw [add_div, e]; dsimp [b]; ring
  have em : (u-v)/h = (a-b)+z := by rw [sub_div, e]; dsimp [b]; ring
  have hu : h*a = u-h*(z:ℝ) := by dsimp [a]; field_simp
  have hv : h*b = v := by dsimp [b]; field_simp
  have price : |v|-midpointDistance h u = h*(|b|-(1/2-|a|)) := by
    unfold midpointDistance
    rw [← hu, ← hv, abs_mul, abs_mul, abs_of_pos hh]
    ring
  have hm (w : ℝ) : max 0 (h*w) = h * max 0 w := by
    simpa only [mul_zero] using (mul_max_of_nonneg (0:ℝ) w hh.le).symm
  rw [show coarseStep h u v = gridStep h u v by simp [coarseStep, hc], gridStep, unit_scale hh u, unit_scale hh v,
    unit_scale hh (u+v), unit_scale hh (u-v), ep, em, e, unit_period, unit_period, unit_period,
    norm a ha, norm b (by linarith), unit_fold hsum, unit_fold hdif, price, hm]
  linear_combination h^2 * (folded_pair a b ha hb)

/-- The dyadic step at scale index m. -/
@[expose] def dyadicStep (m : ℕ) : ℝ := ((2:ℝ)^m)⁻¹
private theorem step_pos (m : ℕ) : 0 < dyadicStep m := by unfold dyadicStep; positivity
private theorem step_half (m : ℕ) : dyadicStep (m+1) = dyadicStep m / 2 := by
  simp [dyadicStep, pow_succ, div_eq_mul_inv, mul_comm]

private theorem fine_bounds (m L : ℕ) (u v : ℝ) :
    let F := ∑ j ∈ Finset.range L,
      (gridStep (dyadicStep (m+j)) u v - coarseStep (dyadicStep (m+j)) u v)
    0 ≤ F ∧ F ≤ (2/3)*(dyadicStep m)^2 ∧ F ≤ (32/3)*v^2 := by
  induction L generalizing m with
  | zero => simp [sq_nonneg]
  | succ L ih =>
    dsimp only
    rw [Finset.sum_range_succ']
    have shift (j : ℕ) : dyadicStep (m+(j+1)) = dyadicStep ((m+1)+j) := congrArg dyadicStep (by omega)
    have shiftSum : (∑ j ∈ Finset.range L, (gridStep (dyadicStep (m+(j+1))) u v -
        coarseStep (dyadicStep (m+(j+1))) u v)) =
        ∑ j ∈ Finset.range L, (gridStep (dyadicStep ((m+1)+j)) u v -
        coarseStep (dyadicStep ((m+1)+j)) u v) :=
      Finset.sum_congr rfl fun j _ => by rw [shift j]
    rw [shiftSum]
    simp only [Nat.add_zero]
    obtain ⟨hn,hg,hi⟩ := ih (m+1)
    rw [step_half] at hg
    have h := step_pos m
    by_cases hc : 4*|v| < dyadicStep m
    · simp only [show coarseStep (dyadicStep m) u v = gridStep (dyadicStep m) u v by simp [coarseStep, hc], sub_self, add_zero]
      exact ⟨hn, by nlinarith [sq_nonneg (dyadicStep m)], hi⟩
    · simp only [show coarseStep (dyadicStep m) u v = 0 by simp [coarseStep, hc], sub_zero]
      have l : 0 ≤ gridStep (dyadicStep m) u v :=
        sub_nonneg.mpr (gridError_restriction h u v)
      have b := gridError_restriction_loss_le h u v
      change gridStep (dyadicStep m) u v ≤ _ at b
      have hh := mul_self_le_mul_self h.le (le_of_not_gt hc)
      have hsq : (4*|v|)^2 = 16*v^2 := by rw [mul_pow, sq_abs]; ring
      rw [← sq, ← sq, hsq] at hh
      exact ⟨add_nonneg hn l, by nlinarith, by nlinarith⟩


private theorem grid_even {h : ℝ} (hh : 0 < h) (x : ℝ) : gridError h (-x) = gridError h x := by
  have one (w : ℝ) : gridError h (-w) ≤ gridError h w := by
    have hz := gridError_le_candidate hh (-w) (-round (w/h))
    unfold gridError
    unfold gridError at hz
    push_cast at hz
    linarith only [hz, show (-w-h*(-((round (w/h):ℤ):ℝ)))^2 =
      (w-h*((round (w/h):ℤ):ℝ))^2 by ring]
  exact le_antisymm (one x) (by simpa only [neg_neg] using one (-x))

private theorem layer_abs (m : ℕ) (x : ℝ) : gridLayer m |x| = gridLayer m x := by
  rw [gridLayer_eq, gridLayer_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; exact grid_even (step_pos m) x

private theorem grid_at {k : ℕ} (f : (Fin k → Bool) → Bool) (S : Finset (Fin k)) (m : ℕ) :
    gridLayer m |fourierCoeff f S| = gridError (dyadicStep m) (fourierCoeff f S) := by
  rw [layer_abs, gridLayer_eq]; rfl

private theorem child_grid (f : (Fin n → Bool) → Bool) :
    fourierGridEnergy f = ∑ T, ∑ m ∈ Finset.range (n+1),
      gridError (dyadicStep m) (fourierCoeff f T) := by
  unfold fourierGridEnergy gridSum
  apply Finset.sum_congr rfl
  intro T _
  simp_rw [← grid_at]
  rw [Finset.sum_range_succ, show gridLayer n |fourierCoeff f T| = 0 by
    simpa only [Nat.zero_add] using gridLayer_tail_zero f T 0, add_zero]

/-- Sum a one-grid butterfly cost over all masks and grids at this node. -/
@[expose] def stepTotal (cost : ℝ → ℝ → ℝ → ℝ) (f : (Fin (n+1) → Bool) → Bool) : ℝ :=
  ∑ T, ∑ m ∈ Finset.range (n+1), cost (dyadicStep m) (fourierCoeff f (liftFrequency T))
    (fourierCoeff f (insert 0 (liftFrequency T)))

/-- Exact one-step grid identity, including both signs of every child coefficient. -/
theorem fourierGridEnergy_restrictFirst (f : (Fin (n+1) → Bool) → Bool) :
    fourierGridEnergy f - (fourierGridEnergy (restrictFirst f false) +
      fourierGridEnergy (restrictFirst f true))/2 = stepTotal gridStep f := by
  rw [child_grid (restrictFirst f false), child_grid (restrictFirst f true)]
  unfold fourierGridEnergy gridSum stepTotal
  rw [splitMasks]
  simp_rw [grid_at]
  simp only [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [(fourierCoeff_restrictFirst f T).1, (fourierCoeff_restrictFirst f T).2]
  simp [gridStep, Finset.sum_sub_distrib, Finset.sum_add_distrib]

private theorem local_bounds (f : (Fin (n+1) → Bool) → Bool) :
    0 ≤ stepTotal gridStep f - stepTotal coarseStep f ∧
    stepTotal gridStep f - stepTotal coarseStep f ≤ (32/3)*coordInfluence f 0 := by
  unfold stepTotal
  rw [← Finset.sum_sub_distrib, coordInfluence_first, Finset.mul_sum]
  simp_rw [← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro T _
    simpa only [Nat.zero_add] using (fine_bounds 0 (n+1) (fourierCoeff f (liftFrequency T))
      (fourierCoeff f (insert 0 (liftFrequency T)))).1
  · apply Finset.sum_le_sum
    intro T _
    simpa only [Nat.zero_add] using (fine_bounds 0 (n+1) (fourierCoeff f (liftFrequency T))
      (fourierCoeff f (insert 0 (liftFrequency T)))).2.2

/-- Total coarse cost along the fixed order, with fair averaging over restrictions. -/
@[expose] def restrictionCrossings : (n : ℕ) → ((Fin n → Bool) → Bool) → ℝ
  | 0, _ => 0
  | k+1, f => stepTotal coarseStep f +
      (restrictionCrossings k (restrictFirst f false) +
        restrictionCrossings k (restrictFirst f true))/2

/-- The fine scales over the entire physical restriction tree cost at most 32I/3. -/
theorem fourierGridEnergy_sub_crossings (n : ℕ) (f : (Fin n → Bool) → Bool) :
    0 ≤ fourierGridEnergy f - restrictionCrossings n f ∧
    fourierGridEnergy f - restrictionCrossings n f ≤ (32/3)*totalInfluence f := by
  induction n with
  | zero => simp [fourierGridEnergy, gridSum, restrictionCrossings, totalInfluence]
  | succ k ih =>
    have hf := ih (restrictFirst f false)
    have ht := ih (restrictFirst f true)
    obtain ⟨h₁,h₂⟩ := local_bounds f
    have he := fourierGridEnergy_restrictFirst f
    rw [restrictionCrossings, totalInfluence_restrictFirst]
    constructor <;> linarith [hf.1,hf.2,ht.1,ht.2]

/-- All retained midpoint costs are nonnegative, including at dimension zero. -/
theorem restrictionCrossings_nonneg (n : ℕ) (f : (Fin n → Bool) → Bool) :
    0 ≤ restrictionCrossings n f := by
  induction n with
  | zero => exact le_refl (0:ℝ)
  | succ k ih =>
    rw [restrictionCrossings]
    apply add_nonneg _ (div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num))
    apply Finset.sum_nonneg
    intro T _
    apply Finset.sum_nonneg
    intro m _
    unfold coarseStep
    split
    · exact sub_nonneg.mpr (gridError_restriction (step_pos m) _ _)
    · exact le_rfl

/-- Direct comparison of the frozen base-two entropy and the physical restriction tree. -/
theorem fourierEntropy_crossing_bounds (n : ℕ) (f : (Fin n → Bool) → Bool) :
    restrictionCrossings n f ≤ fourierEntropy f/2 ∧
    fourierEntropy f/2 ≤ restrictionCrossings n f + (38/3)*totalInfluence f := by
  obtain ⟨lo,hi⟩ := fourierGridEnergy_bounds f
  obtain ⟨a,b⟩ := fourierGridEnergy_sub_crossings n f
  constructor <;> linarith

/-- A dimension-free bound for the fixed-order coarse crossings is equivalent to FEI. -/
theorem fei_iff_crossing_bound : FourierEntropyInfluenceConjecture ↔
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      restrictionCrossings n f ≤ C * totalInfluence f := by
  rw [fei_iff_grid_bound]
  constructor
  · rintro ⟨C,hC,h⟩
    exact ⟨C,hC,fun n f => by linarith [(fourierGridEnergy_sub_crossings n f).1, h n f]⟩
  · rintro ⟨C,hC,h⟩
    exact ⟨C+32/3,by positivity,fun n f => by
      linarith [(fourierGridEnergy_sub_crossings n f).2, h n f]⟩

end FEI
