import CatchUpGame.Challenge
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Int

namespace CatchUpGame.Research

open CatchUpGame

private def join : Outcome → Outcome → Outcome
  | .win, _ | _, .win => .win
  | .draw, _ | _, .draw => .draw
  | _, _ => .loss

private theorem fold_formula (os : List Outcome) (r : Outcome) :
    os.foldl join r = if r = .win ∨ .win ∈ os then .win
      else if r = .draw ∨ .draw ∈ os then .draw else .loss := by
  induction os generalizing r with
  | nil => cases r <;> rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases r <;> cases x <;> simp [join, List.mem_cons]

theorem best_formula (os : List Outcome) :
    Outcome.best os = if .win ∈ os then .win else if .draw ∈ os then .draw else .loss := by
  change os.foldl join .loss = _
  simp [fold_formula]

private theorem best_congr {as bs : List Outcome} (h : ∀ o, o ∈ as ↔ o ∈ bs) :
    Outcome.best as = Outcome.best bs := by
  simp only [best_formula, h]

/-- Common translations of the scores preserve every frozen position, including opening flags. -/
theorem valueAux_add (s : Finset ℕ) (a b k : ℕ) (first : Bool) :
    valueAux s (a + k) (b + k) first = valueAux s a b first := by
  induction s using Finset.strongInductionOn generalizing a b first with
  | _ s ih =>
    rw [valueAux.eq_def s (a+k) (b+k), valueAux.eq_def s a b]
    by_cases he : s = ∅
    · simp [he]
    simp only [he, ite_false]
    have hc : a + k + s.sum id < b + k ↔ a + s.sum id < b := by omega
    change (if a + k + s.sum id < b + k then _ else _) =
      (if a + s.sum id < b then _ else _)
    by_cases h : a + s.sum id < b
    · simp only [ite_eq_left h, ite_eq_left (hc.mpr h)]
    simp only [ite_eq_right h, ite_eq_right (hc.not.mpr h)]
    apply congrArg Outcome.best
    apply List.map_congr_left
    intro ⟨x, hx⟩ _
    have hi := ih (s.erase x) (Finset.erase_ssubset hx)
    dsimp only
    rw [show a+k+x = a+x+k by omega]
    cases first <;> simp [hi]

/-- The player about to pick is behind by the nonnegative deficit d. -/
noncomputable def gapValue (s : Finset ℕ) (d : ℕ) : Outcome := valueAux s 0 d false

theorem valueAux_eq_gap (s : Finset ℕ) {a b : ℕ} (h : a ≤ b) :
    valueAux s a b false = gapValue s (b-a) := by
  simpa [gapValue, Nat.sub_add_cancel h] using valueAux_add s 0 (b-a) a false

theorem value_eq_gap (s : Finset ℕ) : value s = gapValue s 0 := by
  unfold value gapValue
  rw [valueAux.eq_def s 0 0 true, valueAux.eq_def s 0 0 false]
  simp

theorem gap_empty (d : ℕ) :
    gapValue ∅ d = if d = 0 then .draw else .loss := by
  rw [gapValue, valueAux.eq_def]
  cases d <;> simp

theorem gap_insufficient (s : Finset ℕ) {d : ℕ} (h : s.sum id < d) :
    gapValue s d = .loss := by
  by_cases he : s = ∅
  · subst s
    simp only [Finset.sum_empty] at h
    simp [gap_empty, Nat.ne_of_gt h]
  rw [gapValue, valueAux.eq_def]
  simpa [he, id_def] using (show (if s.sum id < d then Outcome.loss else _) = .loss from ite_eq_left h)

/-- The value of one specified pick, measured for the player who makes it. -/
noncomputable def pick (s : Finset ℕ) (d x : ℕ) : Outcome :=
  if x < d then gapValue (s.erase x) (d-x)
  else (gapValue (s.erase x) (x-d)).neg

/-- Any list enumerating a nonempty board gives the one-pick recurrence.
It also holds beyond the frozen immediate-loss cutoff. -/
theorem gap_step {s : Finset ℕ} {xs : List ℕ} (hs : s = xs.toFinset) (hn : xs ≠ [])
    (d : ℕ) : gapValue s d = Outcome.best (xs.map (pick s d)) := by
  have he : s ≠ ∅ := by simpa [hs] using hn
  by_cases hc : s.sum id < d
  · rw [gap_insufficient s hc]
    have allLoss : ∀ x ∈ xs, pick s d x = .loss := by
      intro x hx
      have hm : x ∈ s := by simpa [hs] using hx
      have ht := s.add_sum_erase id hm
      change x + (s.erase x).sum id = s.sum id at ht
      have hxd : x < d := by omega
      simp [pick, hxd, gap_insufficient _ (show (s.erase x).sum id < d-x by omega)]
    rw [best_formula]
    have absent (o : Outcome) (ho : o ≠ .loss) : o ∉ xs.map (pick s d) := by
      rintro h
      obtain ⟨x, hx, hxo⟩ := List.mem_map.mp h
      exact ho (hxo.symm.trans (allLoss x hx))
    simp [absent .win (by decide), absent .draw (by decide)]
  · rw [gapValue, valueAux.eq_def]
    simp only [he, ite_false, Nat.zero_add, Bool.false_eq_true]
    change (if s.sum id < d then _ else _) = _
    rw [ite_eq_right hc]
    apply best_congr
    intro o
    simp only [List.mem_map]
    constructor
    · rintro ⟨⟨x, hx⟩, _, ho⟩
      refine ⟨x, by simpa [hs] using hx, ?_⟩
      by_cases h : x < d
      · simpa [pick, h, Nat.not_le_of_gt h, valueAux_eq_gap _ (Nat.le_of_lt h)] using ho
      · simpa [pick, h, Nat.le_of_not_gt h, valueAux_eq_gap _ (Nat.le_of_not_gt h)] using ho
    · rintro ⟨x, hx, ho⟩
      have hm : x ∈ s := by simpa [hs] using hx
      refine ⟨⟨x, hm⟩, by simp, ?_⟩
      by_cases h : x < d
      · simpa [pick, h, Nat.not_le_of_gt h, valueAux_eq_gap _ (Nat.le_of_lt h)] using ho
      · simpa [pick, h, Nat.le_of_not_gt h, valueAux_eq_gap _ (Nat.le_of_not_gt h)] using ho

/-- Executable list evaluator. The correctness theorem supplies fuel and excludes duplicates. -/
def eval : ℕ → List ℕ → ℕ → Outcome
  | 0, _, d => if d = 0 then .draw else .loss
  | _+1, [], d => if d = 0 then .draw else .loss
  | n+1, x::xs, d => Outcome.best ((x::xs).map fun y =>
      if y < d then eval n ((x::xs).erase y) (d-y)
      else (eval n ((x::xs).erase y) (y-d)).neg)

theorem eval_correct (xs : List ℕ) (hn : xs.Nodup) (d : ℕ) :
    eval xs.length xs d = gapValue xs.toFinset d := by
  generalize hf : xs.length = fuel
  induction fuel generalizing xs d with
  | zero =>
    have : xs = [] := List.length_eq_zero_iff.mp hf
    subst xs
    simp [eval, gap_empty]
  | succ n ih =>
    cases xs with
    | nil => simp at hf
    | cons x xs =>
      rw [gap_step rfl (List.cons_ne_nil x xs), eval]
      apply congrArg Outcome.best
      apply List.map_congr_left
      intro y hy
      have he : ((x::xs).erase y).toFinset = (x::xs).toFinset.erase y := by
        ext z
        simp [hn.mem_erase_iff]
      have hi := ih ((x::xs).erase y) (hn.erase y)
      have hl : ((x::xs).erase y).length = n := by rw [List.length_erase_of_mem hy, hf]; rfl
      simp only [pick]
      split <;> simp_all

private theorem best_win_iff (os : List Outcome) : Outcome.best os = .win ↔ .win ∈ os := by
  rw [best_formula]
  split_ifs <;> simp_all

private theorem best_loss_iff (os : List Outcome) :
    Outcome.best os = .loss ↔ ∀ o ∈ os, o = .loss := by
  rw [best_formula]
  by_cases hw : .win ∈ os
  · simp only [ite_eq_left hw]; grind
  by_cases hd : .draw ∈ os
  · simp only [ite_eq_right hw, ite_eq_left hd]; grind
  simp only [ite_eq_right hw, ite_eq_right hd, true_iff]
  intro o ho
  cases o <;> simp_all

theorem gap_win_iff (s : Finset ℕ) (hn : s.Nonempty) (d : ℕ) :
    gapValue s d = .win ↔ ∃ x ∈ s, pick s d x = .win := by
  have he : s.toList ≠ [] := by simpa using hn.ne_empty
  rw [gap_step s.toList_toFinset.symm he, best_win_iff]
  simp

theorem gap_loss_iff (s : Finset ℕ) (hn : s.Nonempty) (d : ℕ) :
    gapValue s d = .loss ↔ ∀ x ∈ s, pick s d x = .loss := by
  have he : s.toList ≠ [] := by simpa using hn.ne_empty
  rw [gap_step s.toList_toFinset.symm he, best_loss_iff]
  simp

@[simp] private theorem neg_neg (o : Outcome) : o.neg.neg = o := by cases o <;> rfl

/-- Interchanging distinct first picks reverses their conditional outcome. -/
theorem opening_reversal (s : Finset ℕ) {a b : ℕ} (h : a ≠ b) :
    pick (s.erase a) a b = (pick (s.erase b) b a).neg := by
  have he : (s.erase a).erase b = (s.erase b).erase a := by ext; simp [and_left_comm]
  rcases Nat.lt_or_gt_of_ne h with hab | hba
  · simp [pick, hab, Nat.not_lt_of_ge hab.le, he]
  · simp [pick, hba, Nat.not_lt_of_ge hba.le, he]

/-- A strict winning opening makes every other opening lose. -/
theorem other_openings_lose {s : Finset ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hw : pick s 0 a = .win) : pick s 0 b = .loss := by
  have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have ha' : a ∈ s.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hl : gapValue (s.erase a) a = .loss := by
    simp [pick] at hw
    cases h : gapValue (s.erase a) a <;> simp_all [Outcome.neg]
  have hr := (gap_loss_iff _ ⟨b, hb'⟩ a).mp hl b hb'
  rw [opening_reversal s hab] at hr
  have hwin : pick (s.erase b) b a = .win := by
    cases h : pick (s.erase b) b a <;> simp_all [Outcome.neg]
  have := (gap_win_iff _ ⟨a, ha'⟩ b).mpr ⟨a, ha', hwin⟩
  simp [pick, this, Outcome.neg]

/-- Two distinct non-losing openings certify both players' defenses. -/
theorem draw_of_two_openings {s : Finset ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (h₁ : pick s 0 a ≠ .loss) (h₂ : pick s 0 b ≠ .loss) :
    value s = .draw := by
  rw [value_eq_gap]
  cases hv : gapValue s 0 with
  | win =>
    obtain ⟨x, hx, hw⟩ := (gap_win_iff s ⟨a, ha⟩ 0).mp hv
    by_cases h : x = a
    · subst x; exact (h₂ (other_openings_lose ha hb hab hw)).elim
    · exact (h₁ (other_openings_lose hx ha h hw)).elim
  | loss => exact (h₁ ((gap_loss_iff s ⟨a, ha⟩ 0).mp hv a ha)).elim
  | draw => rfl

/-- A signed terminal margin in the frozen three-valued order. -/
def ofMargin (z : ℤ) : Outcome := if 0 < z then .win else if z < 0 then .loss else .draw

private theorem neg_ofMargin (z : ℤ) : (ofMargin z).neg = ofMargin (-z) := by
  unfold ofMargin
  split_ifs <;> first | rfl | omega

private theorem join_ofMargin (z w : ℤ) : join (ofMargin z) (ofMargin w) = ofMargin (max z w) := by
  unfold ofMargin
  simp only [lt_max_iff, max_lt_iff]
  split_ifs <;> first | rfl | omega

@[simp] private theorem best_single (x : Outcome) : Outcome.best [x] = x := by cases x <;> rfl

private theorem best_two (x y : Outcome) : Outcome.best [x,y] = join x y := by
  cases x <;> cases y <;> rfl

private theorem best_three (x y z : Outcome) : Outcome.best [x,y,z] = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem best_four (w x y z : Outcome) :
    Outcome.best [w,x,y,z] = join w (join x (join y z)) := by
  cases w <;> cases x <;> cases y <;> cases z <;> rfl

theorem gap_singleton (x d : ℕ) : gapValue {x} d = ofMargin ((x : ℤ)-d) := by
  rw [gap_step (xs := [x]) (by simp) (by simp)]
  simp only [List.map_cons, List.map_nil, best_single, pick, Finset.erase_singleton, gap_empty, ofMargin]
  split_ifs <;> first | rfl | omega

/-- Exact minimax margin for two remaining tokens, including the forced pass at equality. -/
def twoMargin (u v d : ℕ) : ℤ :=
  if d ≤ u then (v : ℤ) - u - d else (u : ℤ) + v - d

theorem gap_pair {u v : ℕ} (huv : u < v) (d : ℕ) :
    gapValue {u,v} d = ofMargin (twoMargin u v d) := by
  rw [gap_step (xs := [u,v]) (by simp) (by simp)]
  simp only [List.map_cons, List.map_nil, best_two, pick]
  have hne := huv.ne
  simp [hne, Finset.erase_insert_of_ne, gap_singleton,
    neg_ofMargin]
  by_cases h : d ≤ u
  · have hv : ¬ v < d := by omega
    simp only [Nat.not_lt_of_ge h, hv, ite_false, join_ofMargin, twoMargin, ite_eq_left h]
    congr 1; omega
  · simp only [Nat.lt_of_not_ge h, ite_true, twoMargin, ite_eq_right h]
    split <;> rw [join_ofMargin] <;> congr 1 <;> omega

private def atThree (u v d x : ℕ) : ℤ :=
  if x < d then twoMargin u v (d-x) else -twoMargin u v (x-d)

private theorem gap_three {a b c : ℕ} (hab : a < b) (hbc : b < c) (d : ℕ) :
    gapValue {a,b,c} d = ofMargin (max (atThree b c d a)
      (max (atThree a c d b) (atThree a b d c))) := by
  have hac := hab.trans hbc
  rw [gap_step (xs := [a,b,c]) (by simp) (by simp)]
  have ha : ({a,b,c} : Finset ℕ).erase a = {b,c} := by simp [hab.ne, hac.ne]
  have hb : ({a,b,c} : Finset ℕ).erase b = {a,c} := by
    simp [Finset.erase_insert_of_ne, hab.ne, hbc.ne]
  have hc : ({a,b,c} : Finset ℕ).erase c = {a,b} := by
    simp [Finset.erase_insert_of_ne, hac.ne, hbc.ne]
  simp only [List.map_cons, List.map_nil, best_three, pick, ha, hb, hc, gap_pair hab,
    gap_pair hbc, gap_pair hac, neg_ofMargin, atThree]
  split_ifs <;> simp only [join_ofMargin]

private def fourRows (ab ac ad bc bd cd : ℤ) : ℤ :=
  max (min ab (min ac ad))
    (max (min (-ab) (min bc bd))
      (max (min (-ac) (min (-bc) cd)) (min (-ad) (min (-bd) (-cd)))))

private theorem four_rows {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    value {a,b,c,d} = ofMargin (fourRows (twoMargin c d (b-a)) (twoMargin b d (c-a))
      (twoMargin b c (d-a)) (twoMargin a d (c-b)) (twoMargin a c (d-b))
      (twoMargin a b (d-c))) := by
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hbd := hbc.trans hcd
  rw [value_eq_gap, gap_step (xs := [a,b,c,d]) (by simp) (by simp)]
  have ha : ({a,b,c,d} : Finset ℕ).erase a = {b,c,d} := by simp [hab.ne, hac.ne, had.ne]
  have hb : ({a,b,c,d} : Finset ℕ).erase b = {a,c,d} := by
    simp [Finset.erase_insert_of_ne, hab.ne, hbc.ne, hbd.ne]
  have hc : ({a,b,c,d} : Finset ℕ).erase c = {a,b,d} := by
    simp [Finset.erase_insert_of_ne, hac.ne, hbc.ne, hcd.ne]
  have hd : ({a,b,c,d} : Finset ℕ).erase d = {a,b,c} := by
    simp [Finset.erase_insert_of_ne, had.ne, hbd.ne, hcd.ne]
  simp only [List.map_cons, List.map_nil, best_four, pick, Nat.not_lt_zero, ite_false,
    Nat.sub_zero, ha, hb, hc, hd, gap_three hbc hcd, gap_three hac hcd, gap_three hab hbd,
    gap_three hab hbc, neg_ofMargin, join_ofMargin, atThree, fourRows]
  simp only [hab, hac, had, hbc, hbd, hcd, Nat.not_lt_of_ge hab.le, Nat.not_lt_of_ge hac.le,
    Nat.not_lt_of_ge had.le, Nat.not_lt_of_ge hbc.le, Nat.not_lt_of_ge hbd.le,
    Nat.not_lt_of_ge hcd.le, ite_true, ite_false, ← Int.neg_min_neg, Int.neg_neg]

private theorem twoMargin_diff {x y : ℕ} (h : x ≤ y) (u v : ℕ) :
    twoMargin u v (y-x) = if y ≤ x+u then (x : ℤ)+v-u-y else (x : ℤ)+u+v-y := by
  unfold twoMargin
  split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- Four tokens draw exactly when one can partition them equally. The displayed
margin is the smaller of the two potentially minimal absolute partition differences. -/
theorem value_four {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    value {a,b,c,d} = ofMargin (min (abs ((a : ℤ)+d-b-c)) (abs ((a : ℤ)+b+c-d))) := by
  rw [four_rows hab hbc hcd]
  congr 1
  have hac := hab.trans hbc
  have hbd := hbc.trans hcd
  have had := hac.trans hcd
  simp only [twoMargin_diff hab.le, twoMargin_diff hac.le, twoMargin_diff had.le,
    twoMargin_diff hbc.le, twoMargin_diff hbd.le, twoMargin_diff hcd.le, fourRows, abs_eq_max_neg]
  split_ifs <;> omega

/-- Three distinct tokens draw exactly in the additive case. -/
theorem value_three {a b c : ℕ} (hab : a < b) (hbc : b < c) :
    value {a,b,c} = ofMargin |(a : ℤ)+b-c| := by
  rw [value_eq_gap, gap_three hab hbc]
  congr 1
  simp only [atThree, Nat.not_lt_zero, ite_false, Nat.sub_zero, twoMargin, abs_eq_max_neg]
  split_ifs <;> omega


private theorem min_abs_result (x y : ℤ) :
    ofMargin (min |x| |y|) = if x=0 ∨ y=0 then .draw else .win := by
  by_cases h : x=0 ∨ y=0
  · rw [ite_eq_left h]
    rcases h with rfl | rfl <;> simp [ofMargin]
  · have hpos := lt_min (abs_pos.mpr (show x ≠ 0 by tauto)) (abs_pos.mpr (show y ≠ 0 by tauto))
    simp only [h, ite_false, ofMargin, ite_eq_left hpos]

private theorem neg_win (o : Outcome) : o.neg = .win ↔ o = .loss := by cases o <;> decide
private theorem neg_loss (o : Outcome) : o.neg = .loss ↔ o = .win := by cases o <;> decide

theorem four_draw_iff {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    value {a,b,c,d} = .draw ↔ a+d = b+c ∨ a+b+c = d := by
  rw [value_four hab hbc hcd]
  rw [min_abs_result]
  split_ifs <;> simp_all <;> omega

theorem four_win_iff {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    value {a,b,c,d} = .win ↔ a+d ≠ b+c ∧ a+b+c ≠ d := by
  rw [value_four hab hbc hcd]
  rw [min_abs_result]
  split_ifs <;> simp_all <;> omega

theorem gap_exact_total (s : Finset ℕ) : gapValue s (s.sum id) = .draw := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with he | hn
    · simp [he, gap_empty]
    have holds (x : ℕ) (hx : x ∈ s) : pick s (s.sum id) x = .draw := by
      have ht : x + (s.erase x).sum id = s.sum id := s.add_sum_erase id hx
      have hi := ih _ (Finset.erase_ssubset hx)
      by_cases h : x < s.sum id
      · simpa only [pick, ite_eq_left h, show s.sum id - x = (s.erase x).sum id by omega] using hi
      · simp only [pick, ite_eq_right h, show x - s.sum id = (s.erase x).sum id by omega,
          hi, Outcome.neg]
    cases hv : gapValue s (s.sum id) with
    | win =>
      obtain ⟨x,hx,h⟩ := (gap_win_iff s hn _).mp hv
      rw [holds x hx] at h
      cases h
    | loss =>
      obtain ⟨x,hx⟩ := hn
      have h := (gap_loss_iff _ ⟨x,hx⟩ _).mp hv x hx
      rw [holds x hx] at h
      cases h
    | draw => rfl

theorem eval_scale (k : ℕ) (hk : 0 < k) (fuel : ℕ) (xs : List ℕ) (d : ℕ) :
    eval fuel (xs.map (k*·)) (k*d) = eval fuel xs d := by
  have hin : Function.Injective (k*· : ℕ → ℕ) := fun x y h => Nat.eq_of_mul_eq_mul_left hk h
  induction fuel generalizing xs d with
  | zero => simp [eval, Nat.ne_of_gt hk]
  | succ n ih =>
    cases xs with
    | nil => simp [eval, Nat.ne_of_gt hk]
    | cons x xs =>
      have step (ys : List ℕ) (hy : ys ≠ []) (g : ℕ) : eval (n+1) ys g =
          Outcome.best (ys.map fun y => if y < g then eval n (ys.erase y) (g-y)
          else (eval n (ys.erase y) (y-g)).neg) := by
        cases ys with
        | nil => exact (hy rfl).elim
        | cons => rfl
      rw [step _ (by simp), step _ (by simp)]
      apply congrArg Outcome.best
      rw [List.map_map]
      apply List.map_congr_left
      intro y _
      change (if k*y < k*d then eval n (((x::xs).map (k*·)).erase (k*y)) (k*d-k*y)
        else (eval n (((x::xs).map (k*·)).erase (k*y)) (k*y-k*d)).neg) = _
      simp only [← List.map_erase hin, ← Nat.mul_sub_left_distrib, Nat.mul_lt_mul_left hk, ih]

/-- Scaling all the tokens of a finite board by a positive factor preserves its value. -/
theorem value_scale (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) (hk : 0 < k) :
    value (xs.map (k*·)).toFinset = value xs.toFinset := by
  have hin : Function.Injective (k*· : ℕ → ℕ) := fun x y h => Nat.eq_of_mul_eq_mul_left hk h
  rw [value_eq_gap, value_eq_gap, ← eval_correct _ (hn.map hin), ← eval_correct _ hn]
  simpa only [List.length_map, Nat.mul_zero] using eval_scale k hk xs.length xs 0

/-- Tying immediately guarantees a non-loss if the remaining tied game cannot be won by its opener. -/
theorem hold_by_exact_pick {s : Finset ℕ} {d : ℕ} (hd : d ∈ s)
    (h : value (s.erase d) ≠ .win) : gapValue s d ≠ .loss := by
  intro hl
  have ht := (gap_loss_iff s ⟨d,hd⟩ d).mp hl d hd
  simp [pick] at ht
  rw [value_eq_gap] at h
  cases hv : gapValue (s.erase d) 0 <;> simp_all [Outcome.neg]

/-- Two deficit tests and tied games with an additive triple removed suffice for a prefix draw. -/
theorem draw_of_anchor_tests (N : ℕ) (hN : 4 ≤ N) (s : Finset ℕ) (hs : s = Finset.Icc 1 N)
    (h12 : gapValue ((s.erase 1).erase 2) 1 = .draw)
    (h24 : gapValue ((s.erase 2).erase 4) 2 ≠ .loss)
    (ht : ∀ a ∈ ({1,2} : Finset ℕ), ∀ b ∈ s, a < b → b ≠ 2*a →
      value (((s.erase a).erase b).erase (b-a)) ≠ .win) : value s = .draw := by
  have h1 : 1 ∈ s := by simp [hs]; omega
  have h2 : 2 ∈ s := by simp [hs]; omega
  apply draw_of_two_openings h1 h2 (by decide)
  all_goals
    intro lose
    simp only [pick, Nat.not_lt_zero, ite_false, Nat.sub_zero, neg_loss] at lose
  case h₁ =>
    have hw := lose
    obtain ⟨b,hb,hbwin⟩ := (gap_win_iff _ ⟨2, Finset.mem_erase.mpr ⟨by decide,h2⟩⟩ _).mp hw
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hb
    have hbr := Finset.mem_Icc.mp (hs ▸ hm)
    have hgt : 1 < b := by omega
    simp only [pick, Nat.not_lt_of_ge hgt.le, ite_false, neg_win] at hbwin
    by_cases hh : b = 2
    · subst b; simp [h12] at hbwin
    have hdiff : b-1 ∈ (s.erase 1).erase b := by
      simp only [Finset.mem_erase, hs, Finset.mem_Icc]; omega
    have hsafe := hold_by_exact_pick hdiff (ht 1 (by simp) b hm hgt (by omega))
    exact hsafe hbwin
  case h₂ =>
    have hw := lose
    obtain ⟨b,hb,hbwin⟩ := (gap_win_iff _ ⟨1, Finset.mem_erase.mpr ⟨by decide,h1⟩⟩ _).mp hw
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hb
    have hbr := Finset.mem_Icc.mp (hs ▸ hm)
    by_cases hb1 : b = 1
    · subst b
      have he : (s.erase 2).erase 1 = (s.erase 1).erase 2 := by ext; simp [and_left_comm]
      simp [pick, he, h12] at hbwin
    have hgt : 2 < b := by omega
    simp only [pick, Nat.not_lt_of_ge hgt.le, ite_false, neg_win] at hbwin
    by_cases hh : b = 4
    · subst b
      exact h24 hbwin
    have hdiff : b-2 ∈ (s.erase 2).erase b := by
      simp only [Finset.mem_erase, hs, Finset.mem_Icc]; omega
    have hsafe := hold_by_exact_pick hdiff (ht 2 (by simp) b hm hgt (by omega))
    exact hsafe hbwin

private theorem value_list (xs : List ℕ) (hn : xs.Nodup) :
    value xs.toFinset = eval xs.length xs 0 := (value_eq_gap _).trans (eval_correct xs hn 0).symm

theorem five_win : value ([4,5,6,7,8] : List ℕ).toFinset = .win := by
  rw [value_list _ (by decide)]
  decide

theorem six_loss : value ([4,5,6,7,12,14] : List ℕ).toFinset = .loss := by
  rw [value_list _ (by decide)]
  decide

theorem append_four_changes_draw :
    gapValue ([1,6] : List ℕ).toFinset 7 = .draw ∧
    gapValue ([1,6,8,9,10,11] : List ℕ).toFinset 7 = .win := by
  rw [← eval_correct _ (by decide), ← eval_correct _ (by decide)]
  decide

set_option maxRecDepth 8192 in
theorem prefix_eight : value (Finset.Icc 1 8) = .draw := by
  have h : Finset.Icc 1 8 = ([1,2,3,4,5,6,7,8] : List ℕ).toFinset := by decide
  rw [h, value_list _ (by decide)]
  decide


/-- In every drawn subgame some allocation of the live tokens repays the deficit exactly. -/
theorem draw_requires_split (s : Finset ℕ) (d : ℕ) (hv : gapValue s d = .draw) :
    ∃ t ⊆ s, 2 * t.sum id = s.sum id + d := by
  induction s using Finset.strongInductionOn generalizing d with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · refine ⟨∅, Finset.Subset.rfl, ?_⟩
      cases d <;> simp_all [gap_empty]
    have hex : ¬ ∀ x ∈ s, pick s d x = .loss := by
      intro h
      have h' := (gap_loss_iff s hn d).mpr h
      rw [hv] at h'; cases h'
    push Not at hex
    obtain ⟨x,hx,hnl⟩ := hex
    have hdraw : pick s d x = .draw := by
      cases ho : pick s d x with
      | win =>
        have h' := (gap_win_iff s hn d).mpr ⟨x,hx,ho⟩
        rw [hv] at h'; cases h'
      | loss => exact (hnl ho).elim
      | draw => rfl
    have ht : x + (s.erase x).sum id = s.sum id := s.add_sum_erase id hx
    have sub := Finset.erase_subset x s
    have ind := ih (s.erase x) (Finset.erase_ssubset hx)
    by_cases h : x < d
    · simp only [pick, ite_eq_left h] at hdraw
      obtain ⟨t,hsub,hsum⟩ := ind _ hdraw
      have hnot : x ∉ t := fun hx' => (Finset.notMem_erase x s) (hsub hx')
      refine ⟨insert x t, Finset.insert_subset hx (hsub.trans sub), ?_⟩
      have htot : (insert x t).sum id = x + t.sum id := Finset.sum_insert hnot
      omega
    · simp only [pick, ite_eq_right h] at hdraw
      have hc : gapValue (s.erase x) (x-d) = .draw := by
        cases h' : gapValue (s.erase x) (x-d) <;> simp_all [Outcome.neg]
      obtain ⟨t,hsub,hsum⟩ := ind _ hc
      have hsub' := hsub.trans sub
      have htot : (s \ t).sum id + t.sum id = s.sum id := Finset.sum_sdiff hsub'
      exact ⟨s \ t, Finset.sdiff_subset, by omega⟩

theorem additive_triples_union_win :
    value (({2,7,9} : Finset ℕ) ∪ {4,6,10}) = .win := by
  have h : ({2,7,9} : Finset ℕ) ∪ {4,6,10} = ([2,4,6,7,9,10] : List ℕ).toFinset := by decide
  rw [h, value_list _ (by decide)]
  decide


theorem draw_of_drawing_opening {s : Finset ℕ} {x : ℕ} (hx : x ∈ s)
    (hd : pick s 0 x = .draw) : value s = .draw := by
  rw [value_eq_gap]
  cases hv : gapValue s 0 with
  | win =>
    obtain ⟨y,hy,hw⟩ := (gap_win_iff _ ⟨x,hx⟩ _).mp hv
    by_cases he : y = x
    · subst y; rw [hd] at hw; cases hw
    · have hl := other_openings_lose hy hx he hw
      rw [hd] at hl; cases hl
  | loss =>
    have h := (gap_loss_iff _ ⟨x,hx⟩ _).mp hv x hx
    rw [hd] at h; cases h
  | draw => rfl

theorem win_of_dominant {s : Finset ℕ} {x : ℕ} (hx : x ∈ s)
    (h : (s.erase x).sum id < x) : value s = .win := by
  rw [value_eq_gap, gap_win_iff _ ⟨x,hx⟩]
  exact ⟨x, hx, by simp [pick, gap_insufficient _ h, Outcome.neg]⟩

theorem draw_of_half_token {s : Finset ℕ} {x : ℕ} (hx : x ∈ s)
    (h : (s.erase x).sum id = x) : value s = .draw := by
  apply draw_of_drawing_opening hx
  have ht := gap_exact_total (s.erase x)
  rw [h] at ht
  simp [pick,ht,Outcome.neg]

private theorem win_using {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) (hn : (s.erase x).Nonempty)
    (hr : ∀ y ∈ s.erase x, pick (s.erase x) x y = .loss) : value s = .win := by
  rw [value_eq_gap, gap_win_iff _ ⟨x,hx⟩]
  have h := (gap_loss_iff _ hn x).mpr hr
  exact ⟨x,hx,by simp [pick,h,Outcome.neg]⟩

set_option maxHeartbeats 800000 in
private theorem ap_small {a r : ℕ} (ha : 0 < a) (hr : 0 < r) (hreg : a < r ∨ 2*r < a) :
    value {a,a+r,a+2*r,a+3*r,a+4*r} = .win := by
  apply win_using (x := a) (by simp)
  · exact ⟨a+r, by simp [Finset.mem_erase]; omega⟩
  intro y hy
  have hcases : y = a+r ∨ y = a+2*r ∨ y = a+3*r ∨ y = a+4*r := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals rcases hreg with hreg | hreg
  all_goals
    simp (disch := first | omega | (simp; omega)) [pick, Finset.erase_insert_of_ne, gap_three, atThree, twoMargin,
      ofMargin, Outcome.neg]
    split_ifs <;> first | rfl | omega

set_option maxHeartbeats 800000 in
private theorem ap_middle {a r : ℕ} (hr : 0 < r) (hlo : r ≤ a) (hhi : a < 2*r) :
    value {a,a+r,a+2*r,a+3*r,a+4*r} = .win := by
  apply win_using (x := a+2*r) (by simp)
  · exact ⟨a, by simp [Finset.mem_erase]; omega⟩
  intro y hy
  have hcases : y = a ∨ y = a+r ∨ y = a+3*r ∨ y = a+4*r := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    simp (disch := first | omega | (simp; omega)) [pick, Finset.erase_insert_of_ne, gap_three, atThree, twoMargin,
      ofMargin, Outcome.neg]
    split_ifs <;> first | rfl | omega

/-- Among positive five-term arithmetic progressions, precisely those starting at
twice the step draw. Every other progression is a strict first-player win. -/
theorem value_five_progression {a r : ℕ} (ha : 0 < a) (hr : 0 < r) :
    value {a,a+r,a+2*r,a+3*r,a+4*r} = if a = 2*r then .draw else .win := by
  split
  · rename_i h
    subst a
    have base : value ([2,3,4,5,6] : List ℕ).toFinset = .draw := by
      rw [value_eq_gap, ← eval_correct _ (by decide)]
      decide
    have h := (value_scale [2,3,4,5,6] (by decide) r hr).trans base
    convert h using 2
    ext z
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
    omega
  · rename_i h
    by_cases hmid : r ≤ a ∧ a < 2*r
    · exact ap_middle hr hmid.1 hmid.2
    · exact ap_small ha hr (by omega)


/-- Opening 1 holds against larger replies by taking b-1. A drawing 1,2 subgame
bounds that opening from the other side. Reversal then covers every initial pick. -/
theorem draw_of_first_ray (N : ℕ) (hN : 2 ≤ N) (s : Finset ℕ) (hs : s = Finset.Icc 1 N)
    (h12 : gapValue ((s.erase 1).erase 2) 1 = .draw)
    (ht : ∀ b ∈ s, 3 ≤ b → value (((s.erase 1).erase b).erase (b-1)) ≠ .win) :
    value s = .draw := by
  have h1 : 1 ∈ s := by simp [hs]; omega
  have h2 : 2 ∈ s.erase 1 := by simp [hs]; omega
  have hreply : pick (s.erase 1) 1 2 = .draw := by simp [pick, h12, Outcome.neg]
  apply draw_of_drawing_opening h1
  cases hv : gapValue (s.erase 1) 1 with
  | draw => simp [pick, hv, Outcome.neg]
  | loss =>
    have h := (gap_loss_iff _ ⟨2,h2⟩ _).mp hv 2 h2
    rw [hreply] at h; cases h
  | win =>
    obtain ⟨b,hb,hwin⟩ := (gap_win_iff _ ⟨2,h2⟩ _).mp hv
    by_cases h : b = 2
    · subst b; rw [hreply] at hwin; cases hwin
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hb
    have hbr := Finset.mem_Icc.mp (hs ▸ hm)
    have hgt : 3 ≤ b := by omega
    have hdiff : b-1 ∈ (s.erase 1).erase b := by
      simp only [Finset.mem_erase, hs, Finset.mem_Icc]; omega
    have hsafe := hold_by_exact_pick hdiff (ht b hm hgt)
    have hbad : gapValue ((s.erase 1).erase b) (b-1) = .loss := by
      simp only [pick, show ¬b < 1 by omega, ite_false] at hwin
      cases hc : gapValue ((s.erase 1).erase b) (b-1) <;> simp_all [Outcome.neg]
    exact (hsafe hbad).elim

/-- Whether an outcome meets the strict-win or the non-loss threshold. -/
def meets : Outcome → Bool → Bool
  | .win, _ => true
  | .draw, strict => !strict
  | .loss, _ => false

private theorem meets_neg (o : Outcome) (strict : Bool) :
    meets o.neg strict = !(meets o (!strict)) := by cases o <;> cases strict <;> rfl

private theorem meets_best (os : List Outcome) (strict : Bool) :
    meets (Outcome.best os) strict = os.any (fun o => meets o strict) := by
  apply Bool.eq_iff_iff.mpr
  rw [best_formula, List.any_eq_true]
  split
  · rename_i h
    simp only [meets, true_iff]
    exact ⟨.win,h,rfl⟩
  · rename_i hw
    split
    · rename_i hd
      cases strict
      · exact ⟨fun _ => ⟨.draw,hd,rfl⟩, fun _ => rfl⟩
      · constructor
        · intro h; cases h
        · rintro ⟨o,ho,h⟩; cases o <;> simp_all [meets]
    · rename_i hd
      constructor
      · intro h; cases h
      · rintro ⟨o,ho,h⟩; cases o <;> simp_all [meets]

/-- Short-circuit minimax with two thresholds. A passed turn exchanges and complements them. -/
def canReach : ℕ → List ℕ → ℕ → Bool → Bool
  | 0, _, d, strict => (d == 0) && !strict
  | _+1, [], d, strict => (d == 0) && !strict
  | n+1, x::xs, d, strict => (x::xs).any fun y =>
      if y < d then canReach n ((x::xs).erase y) (d-y) strict
      else !(canReach n ((x::xs).erase y) (y-d) (!strict))

/-- The two Boolean thresholds agree with the list evaluator at every fuel level. -/
theorem canReach_correct (fuel : ℕ) (xs : List ℕ) (d : ℕ) (strict : Bool) :
    canReach fuel xs d strict = meets (eval fuel xs d) strict := by
  induction fuel generalizing xs d strict with
  | zero => cases d <;> cases strict <;> rfl
  | succ n ih =>
    cases xs with
    | nil => cases d <;> cases strict <;> rfl
    | cons x xs =>
      simp only [canReach,eval,meets_best,List.any_map,Function.comp_def]
      apply congrArg (List.any (x::xs))
      funext y
      split <;> simp only [ih,meets_neg]

private theorem opening_of_false (xs : List ℕ) (hn : xs.Nodup) (a : ℕ)
    (h : canReach (xs.erase a).length (xs.erase a) a true = false) :
    pick xs.toFinset 0 a ≠ .loss := by
  rw [canReach_correct, eval_correct _ (hn.erase a)] at h
  have he : (xs.erase a).toFinset = xs.toFinset.erase a := by ext z; simp [hn.mem_erase_iff]
  rw [he] at h
  simp only [pick, Nat.not_lt_zero, ite_false, Nat.sub_zero]
  cases ho : gapValue (xs.toFinset.erase a) a <;> simp_all [meets,Outcome.neg]

/-- Two failed opponent win searches certify a prefix draw in the kernel. -/
theorem draw_of_checked_prefix (N a b : ℕ) (ha : a ∈ List.range' 1 N) (hb : b ∈ List.range' 1 N)
    (hab : a ≠ b)
    (h₁ : let xs := (List.range' 1 N).erase a; canReach xs.length xs a true = false)
    (h₂ : let xs := (List.range' 1 N).erase b; canReach xs.length xs b true = false) :
    value (Finset.Icc 1 N) = .draw := by
  have hs : (List.range' 1 N).toFinset = Finset.Icc 1 N := by ext x; simp; omega
  have hn : (List.range' 1 N).Nodup := List.nodup_range' 1
  rw [← hs]
  exact draw_of_two_openings (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb) hab
    (opening_of_false _ hn a h₁) (opening_of_false _ hn b h₂)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2500000 in
/-- The frozen conjecture for every prefix of length at most twelve. -/
theorem prefix_through_twelve (N : ℕ) (hN : N ≤ 12) (h : Even (N * (N+1) / 2)) :
    value (Finset.Icc 1 N) = .draw := by
  have admissible : ∀ n : Fin 13, Even (n.val * (n.val+1) / 2) →
      n.val = 0 ∨ n.val = 3 ∨ n.val = 4 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 11 ∨ n.val = 12 := by
    decide
  rcases admissible ⟨N, by omega⟩ h with h | h | h | h | h | h | h <;> change N = _ at h <;> subst N
  · simp [value_eq_gap, gap_empty]
  · exact draw_of_checked_prefix 3 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  all_goals exact draw_of_checked_prefix _ 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A positive subset of the required sum can be taken to equality in one turn.
The opponent then opens the complementary board at equal scores. -/
theorem hold_by_exact_subset {t s : Finset ℕ} (ht : t ⊆ s) (hne : t.Nonempty)
    (hpos : ∀ x ∈ t, 0 < x) (hrest : value (s \ t) ≠ .win) :
    gapValue s (t.sum id) ≠ .loss := by
  induction t using Finset.induction_on generalizing s with
  | empty => simp at hne
  | @insert x t hx ih =>
    have hxs : x ∈ s := ht (Finset.mem_insert_self _ _)
    have hts : t ⊆ s.erase x := by
      intro z hz
      have hz' : z ≠ x := by rintro rfl; exact hx hz
      exact Finset.mem_erase.mpr ⟨hz',ht (Finset.mem_insert_of_mem hz)⟩
    have he : (s.erase x) \ t = s \ (insert x t) := by
      ext z
      simp [Finset.mem_erase]
      tauto
    have hp : ∀ z ∈ t, 0 < z := fun z hz => hpos z (Finset.mem_insert_of_mem hz)
    rcases t.eq_empty_or_nonempty with rfl | hn
    · have hsingle : value (s.erase x) ≠ .win := by
        rw [← he] at hrest
        simpa using hrest
      simpa using hold_by_exact_pick hxs hsingle
    · obtain ⟨z,hz⟩ := hn
      have hs : 0 < t.sum id := by
        rw [← Finset.sum_erase_add t id hz]
        exact Nat.add_pos_right _ (hp z hz)
      have safe := ih hts ⟨z,hz⟩ hp (by rwa [he])
      rw [Finset.sum_insert hx, id_eq]
      intro lose
      have taken := (gap_loss_iff s ⟨x,hxs⟩ _).mp lose x hxs
      have hlt : x < x + t.sum id := by omega
      exact safe (by simpa only [pick, hlt, ite_true, Nat.add_sub_cancel_left] using taken)


/-- A designated defender stays within K after every completed turn, including
the last. The Boolean identifies whose turn it is. The opponent is unrestricted. -/
inductive Capped (K : ℕ) : Finset ℕ → ℕ → Bool → Prop
  | terminal : Capped K ∅ 0 true
  | keep {s : Finset ℕ} {d x : ℕ} : x ∈ s → x < d → Capped K (s.erase x) (d-x) true → Capped K s d true
  | pass {s : Finset ℕ} {d x : ℕ} : x ∈ s → d ≤ x → x-d ≤ K →
      Capped K (s.erase x) (x-d) false → Capped K s d true
  | against {s : Finset ℕ} {d : ℕ} :
      (∀ x ∈ s, x < d → Capped K (s.erase x) (d-x) false) →
      (∀ x ∈ s, d ≤ x → Capped K (s.erase x) (x-d) true) → Capped K s d false

theorem capped_sound {K d : ℕ} {s : Finset ℕ} {side : Bool} (h : Capped K s d side) :
    if side then gapValue s d ≠ .loss else gapValue s d ≠ .win := by
  induction h with
  | terminal => simp [gap_empty]
  | @keep s d x hx hlt _ ih =>
    intro hl
    have step := (gap_loss_iff _ ⟨x,hx⟩ _).mp hl x hx
    exact ih (by simpa [pick,hlt] using step)
  | @pass s d x hx hle _ _ ih =>
    intro hl
    have step := (gap_loss_iff _ ⟨x,hx⟩ _).mp hl x hx
    simp only [pick,Nat.not_lt_of_ge hle,ite_false] at step
    cases hv : gapValue (s.erase x) (x-d) <;> simp_all [Outcome.neg]
  | @against s d _ _ ihk ihp =>
    intro hw
    rcases s.eq_empty_or_nonempty with rfl | hn
    · cases d <;> simp [gap_empty] at hw
    obtain ⟨x,hx,h⟩ := (gap_win_iff _ hn _).mp hw
    by_cases hlt : x < d
    · exact ihk x hx hlt (by simpa [pick,hlt] using h)
    · have ih := ihp x hx (Nat.le_of_not_gt hlt)
      simp only [pick,hlt,ite_false] at h
      cases hv : gapValue (s.erase x) (x-d) <;> simp_all [Outcome.neg]

private theorem cap_keep {K d x : ℕ} {s : Finset ℕ} (h : Capped K s d false)
    (hx : x ∈ s) (hlt : x < d) : Capped K (s.erase x) (d-x) false := by
  cases h with | against keep _ => exact keep x hx hlt

private theorem cap_pass {K d x : ℕ} {s : Finset ℕ} (h : Capped K s d false)
    (hx : x ∈ s) (hle : d ≤ x) : Capped K (s.erase x) (x-d) true := by
  cases h with | against _ pass => exact pass x hx hle

private theorem cap_defend {K d : ℕ} {s : Finset ℕ} (hn : s.Nonempty) (h : Capped K s d true) :
    ∃ x ∈ s, (x < d ∧ Capped K (s.erase x) (d-x) true) ∨
      (d ≤ x ∧ x-d ≤ K ∧ Capped K (s.erase x) (x-d) false) := by
  cases h with
  | terminal => simp at hn
  | keep hx hlt h => exact ⟨_,hx,Or.inl ⟨hlt,h⟩⟩
  | pass hx hle hk h => exact ⟨_,hx,Or.inr ⟨hle,hk,h⟩⟩

private theorem cap_empty_def {K d : ℕ} (h : Capped K ∅ d true) : d = 0 := by
  cases h <;> simp_all

private theorem cap_single_opp {K d x : ℕ} (h : Capped K {x} d false) : x ≤ d := by
  by_contra! hlt
  have he := cap_pass h (Finset.mem_singleton_self x) hlt.le
  rw [Finset.erase_singleton] at he
  have := cap_empty_def he
  omega

private theorem cap_single_def {K d x : ℕ} (h : Capped K {x} d true) : d ≤ x ∧ x-d ≤ K := by
  obtain ⟨a,ha,ht⟩ := cap_defend (Finset.singleton_nonempty x) h
  obtain rfl := Finset.mem_singleton.mp ha
  rcases ht with ⟨hlt,h'⟩ | ⟨hle,hk,_⟩
  · rw [Finset.erase_singleton] at h'
    have := cap_empty_def h'; omega
  · exact ⟨hle,hk⟩

private theorem cap_minimum {K d m : ℕ} {s : Finset ℕ} (hs : Capped K s d false)
    (hm : m ∈ s) (hmin : ∀ y ∈ s, m ≤ y) (hd : d ≤ m) :
    (s = {m} ∧ m = d) ∨
      ∃ y ∈ s.erase m, m < y ∧ y-(m-d) ≤ K ∧ Capped K ((s.erase m).erase y) (y-(m-d)) false := by
  have h := cap_pass hs hm hd
  rcases (s.erase m).eq_empty_or_nonempty with he | hn
  · rw [he] at h
    have hz := cap_empty_def h
    left
    refine ⟨?_,by omega⟩
    simpa [he] using (Finset.insert_erase hm).symm
  · obtain ⟨y,hy,ht⟩ := cap_defend hn h
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hy
    have hlt : m < y := lt_of_le_of_ne (hmin y hmem) hne.symm
    rcases ht with ⟨hbad,_⟩ | ⟨_,hk,hnext⟩
    · omega
    · exact Or.inr ⟨y,hy,hlt,hk,hnext⟩

private theorem cap_far_pair {a b d : ℕ} (ha0 : 0 < a) (hab : a+2 ≤ b) (hd : d ≤ 2)
    (h : Capped 2 {a,b} d false) : False := by
  have hn : a ≠ b := by omega
  have he : ({a,b} : Finset ℕ).erase b = {a} := by simp [Finset.erase_insert_of_ne,hn]
  have hb := cap_pass h (show b ∈ ({a,b} : Finset ℕ) by simp) (by omega)
  rw [he] at hb
  have hb' := cap_single_def hb
  have he' : ({a,b} : Finset ℕ).erase a = {b} := by simp [hn]
  by_cases ha : a < d
  · have u := cap_keep h (by simp : a ∈ ({a,b} : Finset ℕ)) ha
    rw [he'] at u
    have := cap_single_opp u; omega
  · have u := cap_pass h (by simp : a ∈ ({a,b} : Finset ℕ)) (by omega)
    rw [he'] at u
    have := cap_single_def u; omega

private theorem cap_bad_triple {a : ℕ} (ha : 2 ≤ a) (h : Capped 2 {1,a,a+1} 2 false) : False := by
  have u := cap_pass h (by simp : a ∈ ({1,a,a+1} : Finset ℕ)) ha
  have he : ({1,a,a+1} : Finset ℕ).erase a = {1,a+1} := by
    ext z; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; omega
  rw [he] at u
  obtain ⟨x,hx,ht⟩ := cap_defend (show ({1,a+1} : Finset ℕ).Nonempty by simp) u
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx <;> subst x
  · have he' : ({1,a+1} : Finset ℕ).erase 1 = {a+1} := by ext z; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; omega
    rcases ht with ⟨_,hnext⟩ | ⟨_,_,hnext⟩ <;> rw [he'] at hnext
    · have := cap_single_def hnext; omega
    · have := cap_single_opp hnext; omega
  · rcases ht with ⟨_,_⟩ | ⟨_,_,_⟩ <;> omega

private theorem cap_bad_quad {a b : ℕ} (ha : 0 < a) (hab : a+1 < b)
    (h : Capped 2 {a,a+1,b,b+1} 0 false) : False := by
  have u := cap_pass h (by simp : a+1 ∈ ({a,a+1,b,b+1} : Finset ℕ)) (Nat.zero_le _)
  have he : ({a,a+1,b,b+1} : Finset ℕ).erase (a+1) = {a,b,b+1} := by
    ext z; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; omega
  rw [he,Nat.sub_zero] at u
  obtain ⟨x,hx,ht⟩ := cap_defend (show ({a,b,b+1} : Finset ℕ).Nonempty by simp) u
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · rcases ht with ⟨_,hk⟩ | ⟨_,_,_⟩
    · have he' : ({a,b,b+1} : Finset ℕ).erase a = {b,b+1} := by ext z; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; omega
      rw [he',show a+1-a=1 by omega] at hk
      obtain ⟨z,hz,hs⟩ := cap_defend (show ({b,b+1} : Finset ℕ).Nonempty by simp) hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z <;> rcases hs with ⟨_,_⟩ | ⟨_,hc,hn⟩
      · omega
      · have he'' : ({b,b+1} : Finset ℕ).erase b = {b+1} := by simp
        rw [he''] at hn
        have := cap_single_opp hn; omega
      · omega
      · have he'' : ({b,b+1} : Finset ℕ).erase (b+1) = {b} := by simp [Finset.erase_insert_of_ne]
        rw [he''] at hn
        have := cap_single_opp hn; omega
    · omega
  · rcases ht with ⟨_,_⟩ | ⟨_,hc,hn⟩
    · omega
    · have he' : ({a,b,b+1} : Finset ℕ).erase b = {a,b+1} := by ext z; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; omega
      rw [he'] at hn
      exact cap_far_pair ha (by omega) hc hn
  · rcases ht with ⟨_,_⟩ | ⟨_,hc,hn⟩
    · omega
    · have he' : ({a,b,b+1} : Finset ℕ).erase (b+1) = {a,b} := by ext z; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; omega
      rw [he'] at hn
      exact cap_far_pair ha (by omega) hc hn

private theorem cap_bad_tied_pair {a b K : ℕ} (hab : a < b) (h : Capped K {a,b} 0 false) : False := by
  have u := cap_pass h (by simp : b ∈ ({a,b} : Finset ℕ)) (Nat.zero_le _)
  have he : ({a,b} : Finset ℕ).erase b = {a} := by simp [Finset.erase_insert_of_ne,hab.ne]
  rw [he,Nat.sub_zero] at u
  have := cap_single_def u; omega

/-- Complete list of opponent-to-move positions under a persistent lead cap of two. -/
def capTwoShape : ℕ → Finset ℕ → Prop
  | 0,s => s = ∅ ∨ s = {1,2,3}
  | 1,s => s = ∅ ∨ s = {1} ∨ ∃ a : ℕ, 0 < a ∧ s = {a,a+1}
  | 2,s => s = ∅ ∨ s = {1} ∨ s = {2}
  | _,_ => False

theorem capped_two_necessary (s : Finset ℕ) (d : ℕ) (hp : ∀ z ∈ s, 0 < z)
    (hd : d ≤ 2) (h : Capped 2 s d false) : capTwoShape d s := by
  induction s using Finset.strongInductionOn generalizing d with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
      all_goals exact Or.inl rfl
    let m := s.min' hs
    have hm : m ∈ s := s.min'_mem hs
    have hmpos := hp m hm
    have hmin : ∀ z ∈ s, m ≤ z := fun z hz => s.min'_le z hz
    have hrestore : insert m (s.erase m) = s := Finset.insert_erase hm
    have hsub : s.erase m ⊂ s := Finset.erase_ssubset hm
    have hpos' : ∀ z ∈ s.erase m, 0 < z := fun z hz => hp z (Finset.mem_erase.mp hz).2
    have htail (y : ℕ) (hy : y ∈ s.erase m) :
        insert m (insert y ((s.erase m).erase y)) = s := by rw [Finset.insert_erase hy,hrestore]
    have hltail (y z : ℕ) (hz : z ∈ (s.erase m).erase y) : m < z ∧ z ≠ y := by
      obtain ⟨hzy,hz'⟩ := Finset.mem_erase.mp hz
      obtain ⟨hzm,hzs⟩ := Finset.mem_erase.mp hz'
      exact ⟨lt_of_le_of_ne (hmin z hzs) hzm.symm,hzy⟩
    have hsmall (y g : ℕ) (hg : g ≤ 2) (hnext : Capped 2 ((s.erase m).erase y) g false) :
        capTwoShape g ((s.erase m).erase y) :=
      ih _ (lt_of_le_of_lt (Finset.erase_subset _ _) hsub) g
        (fun z hz => hpos' z (Finset.mem_erase.mp hz).2) hg hnext
    obtain rfl | rfl | rfl : d=0 ∨ d=1 ∨ d=2 := by omega
    · rcases cap_minimum h hm hmin (Nat.zero_le _) with ⟨_,hbad⟩ | ⟨y,hy,hmy,hg,hnext⟩
      · omega
      rw [Nat.sub_zero] at hg hnext
      have rest := htail y hy
      obtain he | he : y-m=1 ∨ y-m=2 := by omega
      · have sh := hsmall y _ hg hnext
        rw [he] at sh
        rcases sh with he0 | he1 | ⟨a,ha,he2⟩
        · rw [he0] at rest
          have ss : s = {m,y} := by simpa using rest.symm
          exact (cap_bad_tied_pair hmy (ss ▸ h)).elim
        · have hz : 1 ∈ (s.erase m).erase y := he1 ▸ Finset.mem_singleton_self 1
          have := hltail _ _ hz; omega
        · have hz : a ∈ (s.erase m).erase y := by rw [he2]; simp
          have := hltail _ _ hz
          have hy' : y=m+1 := by omega
          rw [he2,hy'] at rest
          exact (cap_bad_quad hmpos (by omega) (rest ▸ h)).elim
      · have sh := hsmall y _ hg hnext
        rw [he] at sh
        rcases sh with he0 | he1 | he2
        · rw [he0] at rest
          have ss : s = {m,y} := by simpa using rest.symm
          exact (cap_bad_tied_pair hmy (ss ▸ h)).elim
        · have hz : 1 ∈ (s.erase m).erase y := he1 ▸ Finset.mem_singleton_self 1
          have := hltail _ _ hz; omega
        · have hz : 2 ∈ (s.erase m).erase y := he2 ▸ Finset.mem_singleton_self 2
          have := hltail _ _ hz
          have hm1 : m=1 := by omega
          have hy3 : y=3 := by omega
          rw [he2,hm1,hy3] at rest
          right
          rw [← rest]
          decide
    · rcases cap_minimum h hm hmin (by omega) with ⟨hsm,hm1⟩ | ⟨y,hy,hmy,hg,hnext⟩
      · exact Or.inr (Or.inl (by rwa [hm1] at hsm))
      · have hy' : y=m+1 := by omega
        have hg' : y-(m-1)=2 := by omega
        have sh := hsmall y _ hg hnext
        rw [hg'] at sh
        rcases sh with he0 | he1 | he2
        · have rest := htail y hy
          rw [he0,hy'] at rest
          exact Or.inr (Or.inr ⟨m,hmpos,by simpa using rest.symm⟩)
        · have hz : 1 ∈ (s.erase m).erase y := he1 ▸ Finset.mem_singleton_self 1
          have := hltail _ _ hz; omega
        · have hz : 2 ∈ (s.erase m).erase y := he2 ▸ Finset.mem_singleton_self 2
          have := hltail _ _ hz; omega
    · by_cases hone : m=1
      · have u := cap_keep h hm (show m<2 by omega)
        rw [show 2-m=1 by omega] at u
        have sh := ih _ hsub 1 hpos' (by decide) u
        rcases sh with he0 | he1 | ⟨a,ha,he2⟩
        · rw [he0,hone] at hrestore
          exact Or.inr (Or.inl (by simpa using hrestore.symm))
        · have hz : m ∈ s.erase m := by rw [he1,hone]; simp
          exact (Finset.notMem_erase _ _ hz).elim
        · have hz : a ∈ s.erase m := by rw [he2]; simp
          have hne := (Finset.mem_erase.mp hz).1
          rw [he2,hone] at hrestore
          exact (cap_bad_triple (by omega) (hrestore ▸ h)).elim
      · rcases cap_minimum h hm hmin (by omega) with ⟨hsm,hm2⟩ | ⟨y,hy,hmy,hg,_⟩
        · exact Or.inr (Or.inr (by rwa [hm2] at hsm))
        · omega

private theorem cap_empty_opp (K d : ℕ) : Capped K ∅ d false := by
  apply Capped.against <;> simp

private theorem cap_one_def {K d x : ℕ} (hle : d ≤ x) (hk : x-d ≤ K) : Capped K {x} d true := by
  exact Capped.pass (Finset.mem_singleton_self _) hle hk (by simpa using cap_empty_opp K (x-d))

private theorem cap_one_opp {K d x : ℕ} (hx : x ≤ d) : Capped K {x} d false := by
  apply Capped.against
  · intro y hy _
    obtain rfl := Finset.mem_singleton.mp hy
    simpa using cap_empty_opp K (d-y)
  · intro y hy hle
    obtain rfl := Finset.mem_singleton.mp hy
    have hd : y-d=0 := by omega
    simpa [hd] using (Capped.terminal (K:=K))

private theorem cap_adjacent (a : ℕ) (ha : 0 < a) : Capped 2 {a,a+1} 1 false := by
  apply Capped.against
  · intro x hx hlt
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  · intro x hx _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx <;> subst x
    · have he : ({a,a+1} : Finset ℕ).erase a = {a+1} := by simp
      rw [he]; exact cap_one_def (by omega) (by omega)
    · have he : ({a,a+1} : Finset ℕ).erase (a+1) = {a} := by simp [Finset.erase_insert_of_ne]
      rw [he]; exact cap_one_def (by omega) (by omega)

private theorem cap123 : Capped 2 {1,2,3} 0 false := by
  apply Capped.against
  · intros; omega
  · intro x hx _
    have h : x=1 ∨ x=2 ∨ x=3 := by simpa using hx
    rcases h with rfl | rfl | rfl
    · change Capped 2 {2,3} 1 true
      apply Capped.pass (x:=3) (by decide) (by decide) (by decide)
      exact cap_one_opp (by decide : 2 ≤ 2)
    · change Capped 2 {1,3} 2 true
      apply Capped.pass (x:=3) (by decide) (by decide) (by decide)
      exact cap_one_opp (by decide : 1 ≤ 1)
    · change Capped 2 {1,2} 3 true
      apply Capped.keep (x:=1) (by decide) (by decide)
      exact cap_one_def (by decide : 2 ≤ 2) (by decide)

/-- All literal cap-two handoffs on distinct positive integers, independently of their largest weight. -/
theorem capped_two_iff (s : Finset ℕ) (d : ℕ) (hp : ∀ x ∈ s, 0 < x) (hd : d ≤ 2) :
    Capped 2 s d false ↔ capTwoShape d s := by
  refine ⟨capped_two_necessary s d hp hd,?_⟩
  obtain rfl | rfl | rfl : d=0 ∨ d=1 ∨ d=2 := by omega
  · rintro (rfl | rfl)
    · exact cap_empty_opp _ _
    · exact cap123
  · rintro (rfl | rfl | ⟨a,ha,rfl⟩)
    · exact cap_empty_opp _ _
    · exact cap_one_opp (by decide)
    · exact cap_adjacent a ha
  · rintro (rfl | rfl | rfl)
    · exact cap_empty_opp _ _
    · exact cap_one_opp (by decide)
    · exact cap_one_opp (by decide)

theorem no_pure_exact_class {s : Finset ℕ} (hs : s.Nonempty) (hp : ∀ x ∈ s, 0 < x) :
    ∃ m ∈ s, ∀ t ⊆ s.erase m, t.sum id ≠ m := by
  let m := s.min' hs
  have hm : m ∈ s := s.min'_mem hs
  refine ⟨m,hm,?_⟩
  intro t ht he
  rcases t.eq_empty_or_nonempty with rfl | ⟨y,hy⟩
  · have := hp m hm; simp at he; omega
  · obtain ⟨hne,hys⟩ := Finset.mem_erase.mp (ht hy)
    have hle : m ≤ y := s.min'_le y hys
    have hsum : (t.erase y).sum id + y = t.sum id := Finset.sum_erase_add t id hy
    omega

/-- A Brown-complete bank reaching the largest live weight can coexist with a strict win. -/
theorem complete_bank_counterexample :
    (∀ t : Fin 23, ∃ c ∈ ({1,2,3,7,9} : Finset ℕ).powerset, c.sum id = t.val) ∧
    value ([1,2,3,7,9,11,14,15,22] : List ℕ).toFinset = .win := by
  constructor
  · decide
  · rw [value_eq_gap, ← eval_correct _ (by decide)]
    have hw : canReach 9 [1,2,3,7,9,11,14,15,22] 0 true = true := by decide
    rw [canReach_correct] at hw
    change eval 9 [1,2,3,7,9,11,14,15,22] 0 = .win
    cases hv : eval 9 [1,2,3,7,9,11,14,15,22] 0 <;> simp_all [meets]

/-- Descent on an interval with a positive deficit no larger than its smallest token.
A large first pick allows an exact singleton response. Only the short band needs a separate test. -/
theorem interval_deficit_descent (a N d : ℕ) (ha : a ≤ N) (hd : 0 < d) (hda : d ≤ a)
    (hb : gapValue (Finset.Icc (a+1) N) (a-d) = .draw)
    (hsmall : ∀ x ∈ Finset.Icc a N, a < x → x < a+d →
      gapValue ((Finset.Icc a N).erase x) (x-d) ≠ .loss)
    (hlarge : ∀ x ∈ Finset.Icc a N, a+d ≤ x →
      value (((Finset.Icc a N).erase x).erase (x-d)) ≠ .win) :
    gapValue (Finset.Icc a N) d = .draw := by
  let s := Finset.Icc a N
  have hm : a ∈ s := Finset.mem_Icc.mpr ⟨le_rfl,ha⟩
  have he : s.erase a = Finset.Icc (a+1) N := by
    ext z; simp only [s,Finset.mem_erase,Finset.mem_Icc]; omega
  have hopen : pick s d a = .draw := by simp [pick,Nat.not_lt_of_ge hda,he,hb,Outcome.neg]
  change gapValue s d = .draw
  cases hv : gapValue s d with
  | draw => rfl
  | loss =>
    have u := (gap_loss_iff s ⟨a,hm⟩ d).mp hv a hm
    rw [hopen] at u; cases u
  | win =>
    obtain ⟨x,hx,hw⟩ := (gap_win_iff s ⟨a,hm⟩ d).mp hv
    have hax := (Finset.mem_Icc.mp hx).1
    have hxn := (Finset.mem_Icc.mp hx).2
    by_cases hxa : x=a
    · subst x; rw [hopen] at hw; cases hw
    have hs : gapValue (s.erase x) (x-d) ≠ .loss := by
      by_cases hband : x < a+d
      · exact hsmall x hx (by omega) hband
      · apply hold_by_exact_pick (h := hlarge x hx (by omega))
        simp only [Finset.mem_erase,Finset.mem_Icc]; omega
    simp only [pick,show ¬x<d by omega,ite_false] at hw
    cases hc : gapValue (s.erase x) (x-d) <;> simp_all [Outcome.neg]

theorem boundary_one_descent (N : ℕ) (hN : 3 ≤ N)
    (hb : gapValue (Finset.Icc 4 N) 2 = .draw)
    (ht : ∀ x ∈ Finset.Icc 3 N, 4 ≤ x →
      value (((Finset.Icc 3 N).erase x).erase (x-1)) ≠ .win) :
    gapValue (Finset.Icc 3 N) 1 = .draw :=
  interval_deficit_descent 3 N 1 hN (by decide) (by decide) hb (fun _ _ _ _ => by omega) ht


/-- A partition into disjoint ordered pairs, with the sum of their differences. -/
inductive PairedBudget : Finset ℕ → ℕ → Prop
  | nil : PairedBudget ∅ 0
  | cons {s : Finset ℕ} {E a b : ℕ} : a < b → a ∉ s → b ∉ s →
      PairedBudget s E → PairedBudget (insert a (insert b s)) (E+(b-a))

private theorem paired_partner {s : Finset ℕ} {E : ℕ} (h : PairedBudget s E) (x : ℕ) (hx : x ∈ s) :
    ∃ y ∈ s.erase x, ∃ e ≤ E, (y=x+e ∨ x=y+e) ∧ PairedBudget ((s.erase x).erase y) (E-e) := by
  induction h with
  | nil => simp at hx
  | @cons s E a b hab ha hb hs ih =>
    rcases Finset.mem_insert.mp hx with hxa | hx'
    · subst x
      have he : (insert a (insert b s)).erase a = insert b s := by simp [ha,hab.ne]
      refine ⟨b,by rw [he]; simp,b-a,by omega,Or.inl (by omega),?_⟩
      simpa [he,hb] using hs
    rcases Finset.mem_insert.mp hx' with hxb | hx
    · subst x
      have he : (insert a (insert b s)).erase b = insert a s := by
        simp [Finset.erase_insert_of_ne,hab.ne,hb]
      refine ⟨a,by rw [he]; simp,b-a,by omega,Or.inr (by omega),?_⟩
      simpa [he,ha] using hs
    obtain ⟨y,hy,e,hE,hor,hnext⟩ := ih hx
    obtain ⟨hyx,hys⟩ := Finset.mem_erase.mp hy
    have hxa : a ≠ x := fun z => ha (z ▸ hx)
    have hxb : b ≠ x := fun z => hb (z ▸ hx)
    have hya : a ≠ y := fun z => ha (z ▸ hys)
    have hyb : b ≠ y := fun z => hb (z ▸ hys)
    have he : (insert a (insert b s)).erase x = insert a (insert b (s.erase x)) := by
      simp [Finset.erase_insert_of_ne,hxa,hxb]
    refine ⟨y,by rw [he]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy),e,by omega,hor,?_⟩
    rw [he,Finset.erase_insert_of_ne hya,Finset.erase_insert_of_ne hyb,
      show E+(b-a)-e = (E-e)+(b-a) by omega]
    exact PairedBudget.cons hab
      (fun hm => ha (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2)
      (fun hm => hb (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).2) hnext

/-- If the defender's lead covers the total spread, and the spread plus the
lead fits below every live token, responding to each pick with its mate holds. -/
theorem paired_reservoir (s : Finset ℕ) (E d K : ℕ) (hp : PairedBudget s E)
    (hlo : E ≤ d) (hhi : d+E ≤ K) (hmin : ∀ x ∈ s, K ≤ x) : Capped K s d false := by
  induction s using Finset.strongInductionOn generalizing E d with
  | _ s ih =>
    apply Capped.against
    · intro x hx hlt
      have := hmin x hx; omega
    · intro x hx hdx
      obtain ⟨y,hy,e,he,hor,hrest⟩ := paired_partner hp x hx
      have hxy : x-d ≤ y := by rcases hor with h | h <;> omega
      have hcap : y-(x-d) ≤ K := by rcases hor with h | h <;> omega
      have hlow : E-e ≤ y-(x-d) := by rcases hor with h | h <;> omega
      have hhigh : y-(x-d)+(E-e) ≤ K := by rcases hor with h | h <;> omega
      exact Capped.pass hy hxy hcap (ih _ (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hx))
        _ _ hrest hlow hhigh (fun z hz => hmin z (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2))

theorem paired_reservoir_nonwin (s : Finset ℕ) (E d : ℕ) (hp : PairedBudget s E)
    (hlo : E ≤ d) (hmin : ∀ x ∈ s, d+E ≤ x) : gapValue s d ≠ .win :=
  capped_sound (paired_reservoir s E d (d+E) hp hlo le_rfl hmin)

/-- Consecutive pairs on an interval have total spread equal to their number. -/
theorem paired_interval (a n : ℕ) : PairedBudget (Finset.Ico a (a+2*n)) n := by
  induction n generalizing a with
  | zero => simp [PairedBudget.nil]
  | succ n ih =>
    have h := ih (a+2)
    have ha : a ∉ Finset.Ico (a+2) (a+2+2*n) := by simp
    have hb : a+1 ∉ Finset.Ico (a+2) (a+2+2*n) := by simp
    have hp := PairedBudget.cons (a:=a) (b:=a+1) (by omega) ha hb h
    have he : insert a (insert (a+1) (Finset.Ico (a+2) (a+2+2*n))) = Finset.Ico a (a+2*(n+1)) := by
      ext x; simp only [Finset.mem_insert,Finset.mem_Ico]; omega
    rw [he,show n+(a+1-a)=n+1 by omega] at hp
    exact hp

theorem high_interval_nonwin (a n d : ℕ) (hlo : n ≤ d) (hhi : d+n ≤ a) :
    gapValue (Finset.Ico a (a+2*n)) d ≠ .win :=
  paired_reservoir_nonwin _ n d (paired_interval a n) hlo
    (fun _ hx => le_trans hhi (Finset.mem_Ico.mp hx).1)


/-- Above the cap, each minimum opening forces the defender to spend one
larger token and increase the lead. -/
theorem capped_high_card (s : Finset ℕ) (d K : ℕ) (h : Capped K s d false)
    (hd : d ≤ K) (hmin : ∀ x ∈ s, K < x) : s.card ≤ 2*(K-d) := by
  induction s using Finset.strongInductionOn generalizing d with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    let m := s.min' hn
    have hm : m ∈ s := s.min'_mem hn
    have hlo := hmin _ hm
    rcases cap_minimum h hm (fun z hz => s.min'_le z hz) (by omega) with h0 | h1
    · omega
    obtain ⟨y,hy,hmy,hgap,hnxt⟩ := h1
    have hh := ih _ (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hm)) _ hnxt hgap
      (fun z hz => hmin z (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2)
    have := Finset.card_erase_add_one hy
    have := Finset.card_erase_add_one hm
    omega

/-- Greedy minimum replies exclude an absolute handoff bound on sufficiently
large boards. The low tokens each account for at most two further removals. -/
theorem capped_card_bound (s : Finset ℕ) (d K : ℕ) (h : Capped K s d false)
    (hd : d ≤ K) : s.card ≤ 2*K + 2*(s.filter (· ≤ K)).card := by
  induction s using Finset.strongInductionOn generalizing d with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    let m := s.min' hn
    have hm : m ∈ s := s.min'_mem hn
    by_cases hlow : m ≤ K
    · have hc := Finset.card_erase_add_one hm
      have hc' := Finset.card_erase_add_one (show m ∈ s.filter (· ≤ K) from Finset.mem_filter.mpr ⟨hm,hlow⟩)
      rw [← Finset.filter_erase] at hc'
      by_cases hlt : m<d
      · have hh := ih _ (Finset.erase_ssubset hm) _ (cap_keep h hm hlt) (by omega)
        omega
      rcases cap_minimum h hm (fun z hz => s.min'_le z hz) (by omega) with ⟨hs,_⟩ | ⟨y,hy,_,hg,hnext⟩
      · have hcard := congrArg Finset.card hs
        simp only [Finset.card_singleton] at hcard
        omega
      · have hh := ih _ (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hm)) _ hnext hg
        have hsub := Finset.card_le_card (Finset.filter_subset_filter (· ≤ K) (Finset.erase_subset y (s.erase m)))
        have := Finset.card_erase_add_one hy
        omega
    · have hh := capped_high_card s d K h hd (fun x hx => lt_of_lt_of_le (by omega : K<m) (s.min'_le x hx))
      omega

theorem capped_positive_card (s : Finset ℕ) (d K : ℕ) (hp : ∀ x ∈ s, 0 < x)
    (h : Capped K s d false) (hd : d ≤ K) : s.card ≤ 4*K := by
  have sub : s.filter (· ≤ K) ⊆ Finset.Icc 1 K := by
    intro x hx
    obtain ⟨hm,hk⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_Icc.mpr ⟨hp _ hm,hk⟩
  have hs := Finset.card_le_card sub
  rw [Nat.card_Icc] at hs
  have hc := capped_card_bound s d K h hd
  omega


/-- Fewer holes than the number of disjoint complementary pairs guarantee
a two-token exact catch. The condition says nothing about play after equality. -/
theorem exact_pair_of_few_holes (N d : ℕ) (s : Finset ℕ) (hd : d ≤ N)
    (hh : ((Finset.Icc 1 N) \ s).card < (d-1)/2) :
    ∃ u ∈ s, ∃ v ∈ s, u < v ∧ u+v=d := by
  let q := (d-1)/2
  let t := Finset.Icc 1 q
  let holes := Finset.Icc 1 N \ s
  have hq : q=(d-1)/2 := rfl
  by_contra! hn
  let f := fun u : ℕ => if u ∈ s then d-u else u
  have hm (u : ℕ) (hu : u∈t) : 1 ≤ u ∧ u ≤ q := Finset.mem_Icc.mp hu
  have hf (u : ℕ) (hu : u∈t) : f u ∈ holes := by
    have b := hm u hu
    apply Finset.mem_sdiff.mpr
    by_cases he : u∈s
    · simp only [f,he,ite_true]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
      intro hv
      have := hn u he (d-u) hv (by omega)
      omega
    · have huN : u≤N := by omega
      exact (by simpa [f,he] using And.intro (Finset.mem_Icc.mpr ⟨b.1,huN⟩) he)
  have hcard := Finset.card_le_card_of_injOn f (fun u hu => hf u hu) (by
    intro u hu v hv heq
    have h1 := hm u hu
    have h2 := hm v hv
    by_cases hs : u∈s <;> by_cases ht : v∈s <;> simp [f,hs,ht] at heq <;> omega)
  change t.card ≤ holes.card at hcard
  have ht : t.card=q := by simp [t,Nat.card_Icc]
  change holes.card < (d-1)/2 at hh
  omega


/-- A strict initial surplus over the total spread turns the paired response
into a win for the player who leads. -/
theorem paired_reservoir_loss (s : Finset ℕ) (E d : ℕ) (hp : PairedBudget s E)
    (hlo : E < d) (hmin : ∀ x ∈ s, d+E ≤ x+1) : gapValue s d = .loss := by
  induction s using Finset.strongInductionOn generalizing E d with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp [gap_empty,show d≠0 by omega]
    have hE : 0<E := by cases hp with
                         | nil => simp at hs
                         | cons hab _ _ _ => omega
    apply (gap_loss_iff _ hs _).mpr
    intro x hx
    obtain ⟨y,hy,e,he,hor,hrest⟩ := paired_partner hp x hx
    have hbig := hmin _ hx
    have hxy : x-d ≤ y := by rcases hor with h | h <;> omega
    have hlow : E-e < y-(x-d) := by rcases hor with h | h <;> omega
    have hhigh : y-(x-d)+(E-e) ≤ d+E := by rcases hor with h | h <;> omega
    have hh := ih _ (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hx)) _ _ hrest hlow
      (fun z hz => le_trans hhigh (hmin z (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2))
    have hw : gapValue (s.erase x) (x-d) = .win := by
      apply (gap_win_iff _ ⟨y,hy⟩ _).mpr
      exact ⟨y,hy,by simp [pick,Nat.not_lt_of_ge hxy,hh,Outcome.neg]⟩
    simp [pick,show ¬x<d by omega,hw,Outcome.neg]

/-- With three tokens' worth of density slack, a large opening has an exact
two-pick defense preserving the same strict density threshold. -/
theorem dense_pair_repair (N x : ℕ) (s : Finset ℕ) (hp : ∀ z ∈ s, 0 < z)
    (hx : x ∈ s) (hxN : x ≤ N) (hh : ((Finset.Icc 1 N) \ s).card < (x-1)/2)
    (hdeep : 2*N+10 < 3*s.card) :
    ∃ u ∈ s.erase x, ∃ v ∈ (s.erase x).erase u, u < v ∧ u+v=x ∧
      2*N+1 < 3*(((s.erase x).erase u).erase v).card := by
  obtain ⟨u,hu,v,hv,huv,hs⟩ := exact_pair_of_few_holes N x s hxN hh
  have hupos := hp _ hu
  have hu' : u ∈ s.erase x := Finset.mem_erase.mpr ⟨by omega,hu⟩
  have hv' : v ∈ (s.erase x).erase u := Finset.mem_erase.mpr ⟨by omega,Finset.mem_erase.mpr ⟨by omega,hv⟩⟩
  have := Finset.card_erase_add_one hx
  have := Finset.card_erase_add_one hu'
  have := Finset.card_erase_add_one hv'
  exact ⟨u,hu',v,hv',huv,hs,by omega⟩


/-- A bank and paired reservoir suffice if the second-smallest high token
covers the lead plus spread. The smallest high token is allowed below this bound. -/
theorem bank_and_pairs_second (s bank high : Finset ℕ) (E d : ℕ) (hs : s = bank ∪ high)
    (hdis : Disjoint bank high) (hp : PairedBudget high E)
    (hb : bank.sum id + E ≤ d) (hhigh : ∀ x ∈ high, ∀ y ∈ high, x<y → d+E ≤ y) :
    gapValue s d ≠ .win ∧ (bank.sum id + E < d → gapValue s d = .loss) := by
  induction s using Finset.strongInductionOn generalizing bank high E d with
  | _ s ih =>
    rcases high.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.union_empty] at hs
      subst s
      by_cases hlt : bank.sum id < d
      · simp [gap_insufficient bank hlt]
      · have hd : d=bank.sum id := by omega
        rw [hd,gap_exact_total]
        exact ⟨by decide,by omega⟩
    have hE : 0<E := by cases hp with
                         | nil => simp at hne
                         | cons hab _ _ _ => omega
    have hn : s.Nonempty := hs ▸ hne.mono Finset.subset_union_right
    have response (x : ℕ) (hx : x∈s) :
        pick s d x ≠ .win ∧ (bank.sum id + E < d → pick s d x = .loss) := by
      rcases Finset.mem_union.mp (hs ▸ hx) with hxb | hxh
      · have hsum := Finset.sum_erase_add bank id hxb
        change (bank.erase x).sum id + x = bank.sum id at hsum
        have hlt : x<d := by omega
        have he : s.erase x = bank.erase x ∪ high := by
          rw [hs,Finset.erase_union_distrib,Finset.erase_eq_of_notMem (Finset.disjoint_left.mp hdis hxb)]
        have hr := ih _ (Finset.erase_ssubset hx) _ _ _ (d-x) he
          (hdis.mono_left (Finset.erase_subset _ _)) hp (by omega)
          (fun y hy z hz h => le_trans (by omega : d-x+E ≤ d+E) (hhigh y hy z hz h))
        simp only [pick,hlt,ite_true]
        exact ⟨hr.1,fun h => hr.2 (by omega)⟩
      · obtain ⟨y,hy,e,he,hor,hp'⟩ := paired_partner hp x hxh
        have hyh := (Finset.mem_erase.mp hy).2
        have xbig : d≤x := by
          have hne := (Finset.mem_erase.mp hy).1
          by_cases low : x<y
          · have := hhigh x hxh y hyh low
            rcases hor with h | h <;> omega
          · have := hhigh y hyh x hxh (by omega)
            omega
        have hxy : x-d ≤ y := by rcases hor with h | h <;> omega
        have hl : bank.sum id+(E-e) ≤ y-(x-d) := by rcases hor with h | h <;> omega
        have hh : y-(x-d)+(E-e) ≤ d+E := by rcases hor with h | h <;> omega
        have hsx : s.erase x = bank ∪ high.erase x := by
          rw [hs,Finset.erase_union_distrib,Finset.erase_eq_of_notMem (Finset.disjoint_left.mp hdis.symm hxh)]
        have hsy : (s.erase x).erase y = bank ∪ (high.erase x).erase y := by
          rw [hsx,Finset.erase_union_distrib,Finset.erase_eq_of_notMem (Finset.disjoint_left.mp hdis.symm hyh)]
        have hys : y∈s.erase x := hsx ▸ Finset.mem_union_right _ hy
        have hr := ih _ (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hx))
          _ _ _ (y-(x-d)) hsy (hdis.mono_right (fun _ hz => (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2))
          hp' hl (fun u hu v hv huv => le_trans hh (hhigh u (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2
            v (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2 huv))
        have held : gapValue (s.erase x) (x-d) ≠ .loss := by
          intro loss
          have bad := (gap_loss_iff _ ⟨y,hys⟩ _).mp loss y hys
          simp only [pick,Nat.not_lt_of_ge hxy,ite_false] at bad
          cases hv : gapValue ((s.erase x).erase y) (y-(x-d)) <;> simp_all [Outcome.neg]
        simp only [pick,show ¬x<d by omega,ite_false]
        refine ⟨?_,?_⟩
        · cases hv : gapValue (s.erase x) (x-d) <;> simp_all [Outcome.neg]
        · intro strict
          have strong := hr.2 (by rcases hor with h | h <;> omega)
          have won := (gap_win_iff _ ⟨y,hys⟩ (x-d)).mpr ⟨y,hys,by simp [pick,Nat.not_lt_of_ge hxy,strong,Outcome.neg]⟩
          simp [won,Outcome.neg]
    constructor
    · intro win
      obtain ⟨x,hx,hw⟩ := (gap_win_iff _ hn _).mp win
      exact (response x hx).1 hw
    · intro hl
      exact (gap_loss_iff _ hn _).mpr (fun x hx => (response x hx).2 hl)

/-- A low bank can be spent entirely by the opponent. The defender reserves
their lead for that bank and the spread of disjoint high pairs. -/
theorem bank_and_pairs (s bank high : Finset ℕ) (E d : ℕ) (hs : s = bank ∪ high)
    (hdis : Disjoint bank high) (hp : PairedBudget high E)
    (hb : bank.sum id + E ≤ d) (hhigh : ∀ x ∈ high, d+E ≤ x) :
    gapValue s d ≠ .win ∧ (bank.sum id + E < d → gapValue s d = .loss) :=
  bank_and_pairs_second s bank high E d hs hdis hp hb (fun _ _ y hy _ => hhigh y hy)

/-- Take all preparatory tokens, then the pivot. The positive residual deficit
before the pivot is what makes every preparatory pick legal in the same turn. -/
theorem hold_by_overshoot_subset {s t : Finset ℕ} {pivot r : ℕ} (ht : t ⊆ s)
    (hz : pivot ∈ s \ t) (hr : 0 < r) (hc : r ≤ pivot)
    (hrest : gapValue ((s \ t).erase pivot) (pivot-r) ≠ .win) :
    gapValue s (t.sum id + r) ≠ .loss := by
  induction t using Finset.induction_on generalizing s with
  | empty =>
    simp only [Finset.sdiff_empty] at hz hrest
    simp only [Finset.sum_empty,Nat.zero_add]
    intro hl
    have h := (gap_loss_iff _ ⟨pivot,hz⟩ _).mp hl pivot hz
    simp only [pick,Nat.not_lt_of_ge hc,ite_false] at h
    cases hv : gapValue (s.erase pivot) (pivot-r) <;> simp_all [Outcome.neg]
  | @insert x t hx ih =>
    have hxs : x ∈ s := ht (Finset.mem_insert_self _ _)
    have hts : t ⊆ s.erase x := fun y hy => Finset.mem_erase.mpr
      ⟨fun e => hx (e ▸ hy),ht (Finset.mem_insert_of_mem hy)⟩
    have he : (s.erase x) \ t = s \ insert x t := by
      ext y; simp [Finset.mem_erase]; tauto
    have hnext := ih hts (he ▸ hz) (he ▸ hrest)
    rw [Finset.sum_insert hx,id_eq]
    intro hl
    have h := (gap_loss_iff _ ⟨x,hxs⟩ _).mp hl x hxs
    have hlt : x < x+t.sum id+r := by omega
    exact hnext (by simpa only [pick,hlt,ite_true,show x+t.sum id+r-x=t.sum id+r by omega] using h)

/-- A single adjacent-hole family at offsets two and three, together with one
unpunctured positive-deficit boundary, suffices for a full prefix draw. -/
theorem draw_of_two_offsets (N : ℕ) (hN : 3 ≤ N) (hb : gapValue (Finset.Icc 4 N) 2 = .draw)
    (hh : ∀ a, a=2 ∨ a=3 → ∀ x, a<x → x≤N →
      value (((Finset.Icc a N).erase x).erase (x-1)) ≠ .win) :
    value (Finset.Icc 1 N) = .draw := by
  have h1 : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
    ext z; simp only [Finset.mem_erase,Finset.mem_Icc]; omega
  have h2 : (Finset.Icc 2 N).erase 2 = Finset.Icc 3 N := by
    ext z; simp only [Finset.mem_erase,Finset.mem_Icc]; omega
  apply draw_of_first_ray N (by omega) _ rfl
  · rw [h1,h2]
    exact boundary_one_descent N hN hb (fun x hx h => hh 3 (Or.inr rfl) x h (Finset.mem_Icc.mp hx).2)
  · intro b hb' h
    rw [h1]
    exact hh 2 (Or.inl rfl) b h (Finset.mem_Icc.mp hb').2

private theorem paired_union {s t : Finset ℕ} {E F : ℕ} (h : PairedBudget s E) (k : PairedBudget t F)
    (dis : Disjoint s t) : PairedBudget (s∪t) (E+F) := by
  induction h with
  | nil => simpa using k
  | @cons s E a b hab ha hb _ ih =>
    obtain ⟨hat,db⟩ := Finset.disjoint_insert_left.mp dis
    obtain ⟨hbt,ds⟩ := Finset.disjoint_insert_left.mp db
    have q := PairedBudget.cons hab (show a∉s∪t by simp [ha,hat]) (show b∉s∪t by simp [hb,hbt]) (ih ds)
    simpa [Finset.insert_union,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using q

private theorem punish_with_pair {s : Finset ℕ} {d x y E : ℕ} (hy : y∈s.erase x)
    (hd : d≤x) (hp : x-d≤y) (hr : PairedBudget ((s.erase x).erase y) E)
    (hl : E<y-(x-d)) (hh : ∀ z∈(s.erase x).erase y, y-(x-d)+E≤z+1) :
    pick s d x = .loss := by
  have loss := paired_reservoir_loss _ E _ hr hl hh
  have win : gapValue (s.erase x) (x-d) = .win :=
    (gap_win_iff _ ⟨y,hy⟩ _).mpr ⟨y,hy,by simp [pick,Nat.not_lt_of_ge hp,loss,Outcome.neg]⟩
  simp [pick,Nat.not_lt_of_ge hd,win,Outcome.neg]

private theorem punish_lower (a i j : ℕ) (ha : 2*(i+1+j)≤a+1) :
    pick (Finset.Ico a (a+2*(i+1+j))) (i+1+j) (a+2*i) = .loss := by
  let x := a+2*i
  let s := Finset.Ico a (a+2*(i+1+j))
  let l := Finset.Ico a (a+2*i)
  let r := Finset.Ico (x+2) (x+2+2*j)
  have dis : Disjoint l r := by
    apply Finset.disjoint_left.mpr
    intro z hz h
    simp only [l,r,x,Finset.mem_Ico] at hz h; omega
  have pr : PairedBudget (l∪r) (i+j) := paired_union (paired_interval a i) (paired_interval (x+2) j) dis
  have he : (s.erase x).erase (x+1) = l∪r := by
    ext z; simp only [s,x,l,r,Finset.mem_union,Finset.mem_erase,Finset.mem_Ico]; omega
  have hy : x+1∈s.erase x := by simp only [s,x,Finset.mem_erase,Finset.mem_Ico]; omega
  apply punish_with_pair (d:=i+1+j) hy (by dsimp [x]; omega) (by omega) (he ▸ pr) (by dsimp [x]; omega)
  intro z hz
  have hz' := (Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2).1
  dsimp [x] at *; omega

private theorem punish_upper (a i j : ℕ) (ha : 2*(i+2+j)+1≤a) :
    pick (Finset.Ico a (a+2*(i+2+j))) (i+2+j) (a+2*i+1) = .loss := by
  let t := a+2*i
  let s := Finset.Ico a (a+2*(i+2+j))
  let l := Finset.Ico a (a+2*i)
  let r := Finset.Ico (t+4) (t+4+2*j)
  have dis : Disjoint l r := by
    apply Finset.disjoint_left.mpr
    intro z hz h
    simp only [l,r,t,Finset.mem_Ico] at hz h; omega
  have pr : PairedBudget (l∪r) (i+j) := paired_union (paired_interval a i) (paired_interval (t+4) j) dis
  have ht : t∉l∪r := by simp only [l,r,t,Finset.mem_union,Finset.mem_Ico]; omega
  have ht2 : t+2∉l∪r := by simp only [l,r,t,Finset.mem_union,Finset.mem_Ico]; omega
  have pb := PairedBudget.cons (b:=t+2) (by omega) ht ht2 pr
  have he : (s.erase (t+1)).erase (t+3) = insert t (insert (t+2) (l∪r)) := by
    ext z; simp only [s,t,l,r,Finset.mem_insert,Finset.mem_union,Finset.mem_erase,Finset.mem_Ico]; omega
  have hy : t+3∈s.erase (t+1) := by simp only [s,t,Finset.mem_erase,Finset.mem_Ico]; omega
  apply punish_with_pair (d:=i+2+j) hy (by dsimp [t]; omega) (by omega) (he ▸ pb) (by dsimp [t]; omega)
  intro z hz
  have hz' := (Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2).1
  dsimp [t] at *; omega

/-- At the critical deficit on a sufficiently high interval of even length,
every opening below the maximum loses. No existence of a drawing move is assumed. -/
theorem high_interval_only_max (a n x : ℕ) (ha : 2*n+1≤a) (hlo : a≤x) (hsmall : x+1<a+2*n) :
    pick (Finset.Ico a (a+2*n)) n x = .loss := by
  let i := (x-a)/2
  by_cases even : (x-a)%2=0
  · have hx : x=a+2*i := by dsimp [i]; omega
    have hn : i+1+(n-i-1)=n := by omega
    have h := punish_lower a i (n-i-1) (by omega)
    rwa [hn,← hx] at h
  · have hx : x=a+2*i+1 := by dsimp [i]; omega
    have hn : i+2+(n-i-2)=n := by omega
    have h := punish_upper a i (n-i-2) (by omega)
    rwa [hn,← hx] at h

theorem high_interval_draw_iff_max (a n : ℕ) (hn : 0<n) (ha : 2*n+1≤a) :
    gapValue (Finset.Ico a (a+2*n)) n = .draw ↔
      pick (Finset.Ico a (a+2*n)) n (a+2*n-1) ≠ .loss := by
  let s := Finset.Ico a (a+2*n)
  let m := a+2*n-1
  have hm : m∈s := by simp only [m,s,Finset.mem_Ico]; omega
  have hle := high_interval_nonwin a n n le_rfl (by omega)
  change gapValue s n = .draw ↔ pick s n m ≠ .loss
  constructor
  · intro draw bad
    have loss := (gap_loss_iff s ⟨m,hm⟩ n).mpr (fun x hx => by
      by_cases same : x=m
      · rwa [same]
      · obtain ⟨hx1,hx2⟩ := Finset.mem_Ico.mp hx
        exact high_interval_only_max a n x ha hx1 (by dsimp [m] at same; omega))
    rw [draw] at loss; cases loss
  · intro good
    cases hv : gapValue s n with
    | win => exact (hle hv).elim
    | draw => rfl
    | loss => exact (good ((gap_loss_iff s ⟨m,hm⟩ n).mp hv m hm)).elim



private theorem affine_sign (a b : ℕ) (c z : ℤ)
    (ha : -(a:ℤ) < z ∧ z < a) (hb : -(b:ℤ) < z ∧ z < b) :
    0 < c*a+z ↔ 0 < c*b+z := by
  rcases lt_trichotomy c 0 with neg | rfl | pos
  · have bound (t : ℕ) : c*t ≤ -(t:ℤ) := by
      simpa using mul_le_mul_of_nonneg_right (show c ≤ -1 by omega) (show 0 ≤ (t:ℤ) by omega)
    have := bound a
    have := bound b
    omega
  · simp
  · have bound (t : ℕ) : (t:ℤ) ≤ c*t := by
      simpa using mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ c by omega) (show 0 ≤ (t:ℤ) by omega)
    have := bound a
    have := bound b
    omega

private theorem translated_erase (s : Finset ℕ) (a i : ℕ) :
    (s.erase i).image (a+·) = (s.image (a+·)).erase (a+i) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨j,⟨hne,hj⟩,rfl⟩
    exact ⟨by omega, j,hj,rfl⟩
  · rintro ⟨hne,j,hj,rfl⟩
    exact ⟨j,⟨by omega,hj⟩,rfl⟩

/-- Translating every token preserves the value once the translation dominates
the total offsets and the constant term of the affine starting deficit. -/
theorem gap_translate_tail (s : Finset ℕ) (a b B d e : ℕ) (c z : ℤ)
    (ha : B ≤ a) (hb : B ≤ b)
    (hl : -(B:ℤ) < z - ((s.sum id : ℕ) : ℤ)) (hu : z + ((s.sum id : ℕ) : ℤ) < B)
    (hd : (d:ℤ) = c*a+z) (he : (e:ℤ) = c*b+z) :
    gapValue (s.image (a+·)) d = gapValue (s.image (b+·)) e := by
  induction s using Finset.strongInductionOn generalizing d e c z with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp only [Finset.sum_empty,Nat.cast_zero,sub_zero,add_zero] at hl hu
      have h := affine_sign a b c z (by constructor <;> omega) (by constructor <;> omega)
      have eq : d=0 ↔ e=0 := by omega
      simp only [Finset.image_empty,gap_empty,eq]
    have pick_eq (i : ℕ) (hi : i∈s) :
        pick (s.image (a+·)) d (a+i) = pick (s.image (b+·)) e (b+i) := by
      have sum : (((s.erase i).sum id : ℕ) : ℤ) + i = ((s.sum id : ℕ) : ℤ) := by
        exact_mod_cast Finset.sum_erase_add s id hi
      have pos := affine_sign a b (c-1) (z-i) (by constructor <;> omega) (by constructor <;> omega)
      have ca : (d:ℤ)-(a+i) = (c-1)*a+(z-i) := by rw [hd]; ring
      have cb : (e:ℤ)-(b+i) = (c-1)*b+(z-i) := by rw [he]; ring
      have iff_lt : a+i<d ↔ b+i<e := by omega
      by_cases h : a+i<d
      · have h' := iff_lt.mp h
        simp only [pick,h,h',ite_true,←translated_erase]
        exact ih _ (Finset.erase_ssubset hi) _ _ (c-1) (z-i) (by omega) (by omega)
          (by rw [Nat.cast_sub (by omega : a+i≤d),Nat.cast_add]; exact ca)
          (by rw [Nat.cast_sub (by omega : b+i≤e),Nat.cast_add]; exact cb)
      · have h' := mt iff_lt.mpr h
        simp only [pick,h,h',ite_false,←translated_erase]
        apply congrArg Outcome.neg
        exact ih _ (Finset.erase_ssubset hi) _ _ (1-c) (i-z) (by omega) (by omega)
          (by rw [Nat.cast_sub (by omega : d≤a+i),Nat.cast_add,hd]; ring)
          (by rw [Nat.cast_sub (by omega : e≤b+i),Nat.cast_add,he]; ring)
    have win : gapValue (s.image (a+·)) d = .win ↔ gapValue (s.image (b+·)) e = .win := by
      rw [gap_win_iff _ (hs.image _) _,gap_win_iff _ (hs.image _) _]
      simp only [Finset.mem_image,exists_exists_and_eq_and]
      constructor <;> rintro ⟨i,hi,h⟩
      · exact ⟨i,hi,(pick_eq i hi) ▸ h⟩
      · exact ⟨i,hi,(pick_eq i hi).symm ▸ h⟩
    have loss : gapValue (s.image (a+·)) d = .loss ↔ gapValue (s.image (b+·)) e = .loss := by
      rw [gap_loss_iff _ (hs.image _) _,gap_loss_iff _ (hs.image _) _]
      simp only [Finset.forall_mem_image]
      constructor <;> intro h i hi
      · rw [←pick_eq i hi]; exact h hi
      · rw [pick_eq i hi]; exact h hi
    cases h₁ : gapValue (s.image (a+·)) d <;> cases h₂ : gapValue (s.image (b+·)) e <;> simp_all


/-- A uniform strategy for all common shifts. A rising deficit has the same
shift as a token. At a flat deficit we use only comparisons that pass the turn
for every shift. Both players may select any legal token in the real game. -/
def shiftHold : ℕ → List ℕ → ℕ → Bool → Bool → Bool
  | 0, _, d, r, me | _+1, [], d, r, me => !me || (!r && d == 0)
  | fuel+1, x::xs, d, r, me =>
    let step y := (r || decide (d ≤ y)) &&
      (if y < d then shiftHold fuel ((x::xs).erase y) (d-y) (!r) me
       else shiftHold fuel ((x::xs).erase y) (y-d) (!r) (!me))
    if me then (x::xs).reverse.any step else (x::xs).all step

private def Held (me : Bool) (v : Outcome) : Prop := if me then v ≠ .loss else v ≠ .win

private theorem held_neg (me : Bool) (o : Outcome) : Held me o.neg ↔ Held (!me) o := by
  cases me <;> cases o <;> simp [Held,Outcome.neg]

/-- Every accepted strategy works simultaneously at all translations. -/
theorem shiftHold_sound (xs : List ℕ) (hn : xs.Nodup) (d t : ℕ) (r me : Bool)
    (cert : shiftHold xs.length xs d r me = true) :
    (if me then gapValue ((xs.map (t+·)).toFinset) (d + if r then t else 0) ≠ .loss
     else gapValue ((xs.map (t+·)).toFinset) (d + if r then t else 0) ≠ .win) := by
  change Held me _
  generalize hf : xs.length = fuel at cert
  induction fuel generalizing xs d r me with
  | zero =>
    have := List.length_eq_zero_iff.mp hf
    subst xs
    cases me <;> cases r <;> simp_all [shiftHold,Held,gap_empty] <;> split <;> decide
  | succ f ih =>
    cases xs with
    | nil => simp at hf
    | cons x xs =>
      let s := ((x::xs).map (t+·)).toFinset
      have hne : s.Nonempty := ⟨t+x,by simp [s]⟩
      let step := fun y => (r || decide (d≤y)) &&
        (if y<d then shiftHold f ((x::xs).erase y) (d-y) (!r) me
         else shiftHold f ((x::xs).erase y) (y-d) (!r) (!me))
      have child (y : ℕ) (hy : y∈x::xs) (good : step y = true) :
          Held me (pick s (d + if r then t else 0) (t+y)) := by
        have len : ((x::xs).erase y).length=f := by rw [List.length_erase_of_mem hy]; omega
        have erase : (((x::xs).erase y).map (t+·)).toFinset = s.erase (t+y) := by
          ext z
          simp only [s,Finset.mem_erase,List.mem_toFinset,List.mem_map,hn.mem_erase_iff]
          constructor
          · rintro ⟨j,⟨hne,hj⟩,rfl⟩
            exact ⟨by omega,j,hj,rfl⟩
          · rintro ⟨hne,j,hj,rfl⟩
            exact ⟨j,⟨by omega,hj⟩,rfl⟩
        simp only [step,Bool.and_eq_true] at good
        by_cases lt : y<d
        · have rr : r=true := by cases r with
            | true => rfl
            | false => have hle : d≤y := by simpa using good.1
                       omega
          have h := ih _ (hn.erase y) (d-y) (!r) me len (by simpa [lt] using good.2)
          subst r
          have hlt : t+y < d+t := by omega
          simp only [pick,ite_true,hlt,show d+t-(t+y)=d-y by omega]
          simpa only [erase,Bool.not_true,Bool.false_eq_true,reduceIte,add_zero] using h
        · have h := ih _ (hn.erase y) (y-d) (!r) (!me) len (by simpa [lt] using good.2)
          cases r <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,reduceIte,add_zero] at h ⊢
          · have hh : ¬ t+y < d := by omega
            simp only [pick,hh,ite_false,held_neg]
            rw [erase] at h
            simpa only [show t+y-d=y-d+t by omega] using h
          · have hh : ¬ t+y < d+t := by omega
            simp only [pick,hh,ite_false,held_neg]
            rw [erase] at h
            simpa only [show t+y-(d+t)=y-d by omega] using h
      change Held me (gapValue s _)
      cases me with
      | true =>
        change gapValue s _ ≠ .loss
        change (x::xs).reverse.any step = true at cert
        obtain ⟨y,hy,h⟩ := List.any_eq_true.mp cert
        have hy' : y∈x::xs := List.mem_reverse.mp hy
        have hc := child y hy' h
        exact fun hl => hc ((gap_loss_iff _ hne _).mp hl (t+y) (List.mem_toFinset.mpr (List.mem_map_of_mem hy')))
      | false =>
        change gapValue s _ ≠ .win
        change (x::xs).all step = true at cert
        intro hw
        obtain ⟨z,hz,h⟩ := (gap_win_iff _ hne _).mp hw
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
        exact child y hy (List.all_eq_true.mp cert _ hy) h

/-- The leading side holds at the critical deficit even when the interval starts at twice
its number of pairs minus one. -/
theorem high_interval_nonwin_second (a n : ℕ) (ha : 2*n≤a+1) :
    gapValue (Finset.Ico a (a+2*n)) n ≠ .win := by
  let s := Finset.Ico a (a+2*n)
  have bound (x : ℕ) (hx : x∈s) (y : ℕ) (_ : y∈s) (hxy : x<y) : n+n≤y := by
    have := (Finset.mem_Ico.mp hx).1
    omega
  exact (bank_and_pairs_second s ∅ s n n (by simp) (by simp) (paired_interval a n)
    (by simp) bound).1

/-- One uniform certificate for the odd child covers every height at this length. -/
theorem high_interval_of_shift_base (n b a : ℕ) (hn : 0<n) (hb : 2*n≤b+1) (ha : b≤a)
    (cert : let xs := List.range' b (2*n-1)
            shiftHold xs.length xs (b+n-1) true false = true) :
    gapValue (Finset.Ico a (a+2*n)) n = .draw := by
  let xs := List.range' b (2*n-1)
  let t := a-b
  have h := shiftHold_sound xs (List.nodup_range' 1) (b+n-1) t true false cert
  have he : (xs.map (t+·)).toFinset = (Finset.Ico a (a+2*n)).erase (a+2*n-1) := by
    ext z
    simp only [List.mem_toFinset,List.mem_map,xs,Finset.mem_erase,Finset.mem_Ico]
    constructor
    · rintro ⟨y,hy,rfl⟩
      simp at hy
      dsimp [t]; omega
    · intro hz
      refine ⟨z-t,?_,by dsimp [t]; omega⟩
      simp; dsimp [t]; omega
  have held := high_interval_nonwin_second a n (by omega)
  have hm : a+2*n-1 ∈ Finset.Ico a (a+2*n) := by simp only [Finset.mem_Ico]; omega
  suffices good : pick (Finset.Ico a (a+2*n)) n (a+2*n-1) ≠ .loss by
    cases hv : gapValue (Finset.Ico a (a+2*n)) n with
    | win => exact (held hv).elim
    | draw => rfl
    | loss => exact (good ((gap_loss_iff _ ⟨_,hm⟩ _).mp hv _ hm)).elim
  have hx : ¬ a+2*n-1<n := by omega
  simp only [Bool.false_eq_true,reduceIte,he] at h
  simp only [pick,hx,ite_false,show a+2*n-1-n=b+n-1+t by dsimp [t]; omega]
  cases hv : gapValue ((Finset.Ico a (a+2*n)).erase (a+2*n-1)) (b+n-1+t) <;> simp_all [Outcome.neg]



/-- One uniform certificate for the odd child covers every height at this length. -/
theorem high_interval_of_shift (n a : ℕ) (hn : 0<n) (ha : 2*n+1≤a)
    (cert : let xs := List.range' (2*n+1) (2*n-1)
            shiftHold xs.length xs (3*n) true false = true) :
    gapValue (Finset.Ico a (a+2*n)) n = .draw := by
  apply high_interval_of_shift_base n (2*n+1) a hn (by omega) ha
  simpa only [show 2*n+1+n-1=3*n by omega] using cert

/-- At positive residual deficit, the mover may spend every token of a
designated bank before following a holding strategy on the rest. -/
theorem spend_bank_first (bank high : Finset ℕ) (d : ℕ) (hd : 0<d)
    (dis : Disjoint bank high) (hold : gapValue high d ≠ .loss) :
    gapValue (bank∪high) (bank.sum id + d) ≠ .loss := by
  induction bank using Finset.induction_on with
  | empty => simpa using hold
  | @insert x bank hx ih =>
    obtain ⟨hxhi,dis'⟩ := Finset.disjoint_insert_left.mp dis
    have hr := ih dis'
    have he : (insert x bank ∪ high).erase x = bank ∪ high := by
      rw [Finset.insert_union,Finset.erase_insert (by simp [hx,hxhi])]
    have hm : x∈insert x bank∪high := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hx,id_eq]
    intro hl
    have bad := (gap_loss_iff _ ⟨x,hm⟩ _).mp hl x hm
    exact hr (by simpa only [pick,show x<x+bank.sum id+d by omega,ite_true,he,
                             show x+bank.sum id+d-x=bank.sum id+d by omega] using bad)

/-- A holding critical endgame can be embedded in a tied board by adding
a disjoint bank and an opening equal to the bank sum plus the deficit. -/
theorem draw_of_bank_lift (bank high : Finset ℕ) (d E : ℕ) (hd : 0<d)
    (dis : Disjoint bank high) (hp : PairedBudget high E) (he : E≤d)
    (hmin : ∀ z∈high, bank.sum id+d+E≤z)
    (fresh : bank.sum id+d ∉ bank∪high) (hold : gapValue high d ≠ .loss) :
    value (insert (bank.sum id+d) (bank∪high)) = .draw := by
  let x := bank.sum id+d
  have hlo := spend_bank_first bank high d hd dis hold
  have hhi := (bank_and_pairs (bank∪high) bank high E x rfl dis hp (by dsimp [x]; omega) hmin).1
  apply draw_of_drawing_opening (Finset.mem_insert_self x (bank∪high))
  have hr : gapValue (bank∪high) x = .draw := by
    cases h : gapValue (bank∪high) x <;> simp_all [x]
  change pick (insert x (bank∪high)) 0 x = .draw
  have hx : x∉bank∪high := fresh
  simp only [pick,Nat.not_lt_zero,ite_false,Nat.sub_zero,Finset.erase_insert hx,hr,Outcome.neg]

/-- With one high pair, the bank may have any size and any gaps. -/
theorem bank_pair_draw (bank : Finset ℕ) (u v : ℕ) (huv : u<v)
    (dis : Disjoint bank {u,v}) (hmin : bank.sum id+2*(v-u)≤u)
    (fresh : bank.sum id+(v-u) ∉ bank ∪ {u,v}) :
    value (insert (bank.sum id+(v-u)) (bank∪{u,v})) = .draw := by
  have hp : PairedBudget {u,v} (v-u) := by
    simpa using PairedBudget.cons (s:=∅) huv (by simp) (by simp) PairedBudget.nil
  apply draw_of_bank_lift bank {u,v} (v-u) (v-u) (by omega) dis hp le_rfl _ fresh
  · intro hl
    have hv : v∈({u,v} : Finset ℕ) := by simp
    have bad := (gap_loss_iff _ ⟨v,hv⟩ _).mp hl v hv
    have he : ({u,v} : Finset ℕ).erase v = {u} := by simp [Finset.erase_insert_of_ne,huv.ne]
    simp [pick,show ¬v<v-u by omega,he,show v-(v-u)=u by omega,gap_singleton,ofMargin,Outcome.neg] at bad
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    omega

private theorem translated_range (a l : ℕ) :
    (Finset.range l).image (a+·) = Finset.Ico a (a+l) := by
  ext z
  simp only [Finset.mem_image,Finset.mem_range,Finset.mem_Ico]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · intro h; exact ⟨z-a,by omega,by omega⟩

/-- For each length there is a finite, explicit translation interval to check. -/
theorem high_interval_finite_test (n : ℕ) (hn : 0<n)
    (checks : ∀ a, 2*n+1≤a → a≤(Finset.range (2*n)).sum id+n+1 →
      gapValue (Finset.Ico a (a+2*n)) n = .draw) :
    ∀ a, 2*n+1≤a → gapValue (Finset.Ico a (a+2*n)) n = .draw := by
  intro a ha
  let B := (Finset.range (2*n)).sum id+n+1
  by_cases small : a≤B
  · exact checks a ha small
  have hmem : n∈Finset.range (2*n) := Finset.mem_range.mpr (by omega)
  have hs := Finset.sum_erase_add (Finset.range (2*n)) id hmem
  change ((Finset.range (2*n)).erase n).sum id + n = (Finset.range (2*n)).sum id at hs
  have h := gap_translate_tail (Finset.range (2*n)) a B B n n 0 n (by omega) le_rfl
    (by dsimp [B]; omega) (by dsimp [B]; omega) (by simp) (by simp)
  rw [translated_range,translated_range] at h
  rw [h]
  exact checks B (by change 2*n+1 ≤ (Finset.range (2*n)).sum id + n + 1; omega) le_rfl

/-- At the next length, the two endpoint picks of the odd child leave intact
intervals. The lower endpoint uses the unconditional paired bound, and the
upper endpoint uses the smaller critical draw. Only strict interior holes remain. -/
theorem high_interval_of_interior_holes (a k : ℕ) (hk : 0<k) (ha : 2*(k+1)+1≤a)
    (previous : gapValue (Finset.Ico a (a+2*k)) k = .draw)
    (low : ∀ x, a<x → x<a+k →
      gapValue ((Finset.Ico a (a+2*k+1)).erase x) (a+k-x) ≠ .win)
    (high : ∀ x, a+k≤x → x<a+2*k →
      gapValue ((Finset.Ico a (a+2*k+1)).erase x) (x-(a+k)) ≠ .loss) :
    gapValue (Finset.Ico a (a+2*(k+1))) (k+1) = .draw := by
  let odd := Finset.Ico a (a+2*k+1)
  have nonwin : gapValue odd (a+k) ≠ .win := by
    intro win
    have hne : a∈odd := by simp only [odd,Finset.mem_Ico]; omega
    obtain ⟨x,hx,hp⟩ := (gap_win_iff odd ⟨a,hne⟩ _).mp win
    obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp hx
    by_cases l : x<a+k
    · simp only [pick,l,ite_true] at hp
      by_cases edge : x=a
      · subst x
        have he : odd.erase a = Finset.Ico (a+1) (a+1+2*k) := by
          ext z; simp [odd]; omega
        rw [he,show a+k-a=k by omega] at hp
        exact high_interval_nonwin (a+1) k k le_rfl (by omega) hp
      · exact low x (by omega) l hp
    · have hold : gapValue (odd.erase x) (x-(a+k)) ≠ .loss := by
        by_cases edge : x=a+2*k
        · subst x
          have he : odd.erase (a+2*k) = Finset.Ico a (a+2*k) := by
            ext z; simp [odd]; omega
          rw [he,show a+2*k-(a+k)=k by omega,previous]
          decide
        · exact high x (by omega) (by omega)
      simp only [pick,l,ite_false] at hp
      cases h : gapValue (odd.erase x) (x-(a+k)) <;> simp_all [Outcome.neg]
  apply (high_interval_draw_iff_max a (k+1) (by omega) ha).mpr
  have he : (Finset.Ico a (a+2*(k+1))).erase (a+2*(k+1)-1) = odd := by
    ext z; simp [odd]; omega
  simp only [pick,show ¬ a+2*(k+1)-1<k+1 by omega,ite_false,he,
    show a+2*(k+1)-1-(k+1)=a+k by omega]
  cases h : gapValue odd (a+k) <;> simp_all [Outcome.neg]

/-- Deleting a single interior token can already turn the critical value into a loss.
Two interior deletions at the same length and deficit realize all three outcomes. -/
theorem critical_hole_witnesses :
    gapValue ([5,6,8,9] : List ℕ).toFinset 2 = .loss ∧
    gapValue ([5,8,9,10] : List ℕ).toFinset 2 = .win ∧
    gapValue ([5,6,9,10] : List ℕ).toFinset 2 = .draw ∧
    gapValue ([5,7,8,10] : List ℕ).toFinset 2 = .loss := by
  refine ⟨?_,?_,?_,?_⟩ <;> rw [←eval_correct _ (by decide)] <;> decide



/-- Keep the head of a cached proof independent of Boolean reduction during replay. -/
private def ShiftClaim (s : List ℕ) (d : ℕ) (r me : Bool) : Prop :=
  shiftHold s.length s d r me = true

private def ShiftMove (s : List ℕ) (d : ℕ) (r me : Bool) (y : ℕ) : Prop :=
  (r || decide (d≤y)) = true ∧ ShiftClaim (s.erase y) (if y<d then d-y else y-d) (!r)
    (if y<d then me else !me)

private theorem move_ok (s : List ℕ) (d : ℕ) (r me : Bool) (y : ℕ)
    (g : (r || decide (d≤y)) = true)
    (h : ShiftClaim (s.erase y) (if y<d then d-y else y-d) (!r) (if y<d then me else !me)) :
    ShiftMove s d r me y := ⟨g,h⟩

private def EachShift (s : List ℕ) (d : ℕ) (r : Bool) (l : List ℕ) : Prop :=
  ∀ y∈l, ShiftMove s d r false y
private theorem each_nil (s : List ℕ) (d : ℕ) (r : Bool) : EachShift s d r [] := by
  intro y hy; simp at hy
private theorem each_cons (s : List ℕ) (d : ℕ) (r : Bool) (y : ℕ) (ys : List ℕ)
    (head : ShiftMove s d r false y) (tail : EachShift s d r ys) : EachShift s d r (y::ys) := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact head
  · exact tail z hz

private theorem bool_edge {s : List ℕ} {d : ℕ} {r me : Bool} {y : ℕ} (hy : y∈s)
    (h : ShiftMove s d r me y) :
    ((r || decide (d≤y)) && (if y<d then shiftHold (s.length-1) (s.erase y) (d-y) (!r) me
    else shiftHold (s.length-1) (s.erase y) (y-d) (!r) (!me))) = true := by
  obtain ⟨g,h⟩ := h
  simp only [ShiftClaim,List.length_erase_of_mem hy] at h
  rw [g]
  by_cases l:y<d <;> simpa [l] using h

private theorem claim_any (x : ℕ) (xs : List ℕ) (d : ℕ) (r : Bool) (y : ℕ)
    (hy : (x::xs).contains y = true) (h : ShiftMove (x::xs) d r true y) :
    ShiftClaim (x::xs) d r true := by
  have hm : y∈x::xs := by simpa using hy
  apply List.any_eq_true.mpr
  exact ⟨y,List.mem_reverse.mpr hm,by simpa using bool_edge hm h⟩
private theorem claim_all (x : ℕ) (xs : List ℕ) (d : ℕ) (r : Bool)
    (h : EachShift (x::xs) d r (x::xs)) : ShiftClaim (x::xs) d r false := by
  apply List.all_eq_true.mpr
  intro y hy
  simpa using bool_edge hy (h y hy)

-- Search only builds proof terms from the preceding lemmas. The kernel checks
-- every auxiliary theorem, and a rejected comparison supplies no evidence.
open Lean Meta Elab Tactic in
private partial def replayShift (s : List Nat) (d : Nat) (r me : Bool)
    (memo : IO.Ref (Std.HashMap (List Nat × Nat × Bool × Bool) (Option Expr))) :
    MetaM (Option Expr) := do
  let key := (s,d,r,me)
  if let some cached := (← memo.get)[key]? then return cached
  let reflTrue ← mkEqRefl (toExpr true)
  let build : MetaM (Option Expr) := do
    match s with
    | [] => return if !me || (!r && d==0) then some reflTrue else none
    | head::tail =>
      let args := #[toExpr s,toExpr d,toExpr r,toExpr me]
      let order := if me then s.reverse else s
      let mut pending : List (Nat × List Nat × Expr) := []
      let mut rest := order
      for y in order do
        rest := rest.tail
        let mut witness := none
        if r || d≤y then
          let child ← replayShift (s.erase y) (if y<d then d-y else y-d) (!r)
            (if y<d then me else !me) memo
          if let some pr := child then
            witness := some (mkAppN (mkConst ``move_ok) (args ++ #[toExpr y,reflTrue,pr]))
        if me then
          if let some pr := witness then
            return some (mkAppN (mkConst ``claim_any)
              #[toExpr head,toExpr tail,toExpr d,toExpr r,toExpr y,reflTrue,pr])
          pure ()
        else
          let some pr := witness | return none
          pending := (y,rest,pr)::pending
      if me then return none
      let mut allProof := mkAppN (mkConst ``each_nil) #[toExpr s,toExpr d,toExpr r]
      for (v,vs,pr) in pending do
        allProof := mkAppN (mkConst ``each_cons) #[toExpr s,toExpr d,toExpr r,toExpr v,toExpr vs,pr,allProof]
      return some (mkAppN (mkConst ``claim_all) #[toExpr head,toExpr tail,toExpr d,toExpr r,allProof])
  let result ← build
  let saved ← match result with
    | some pr =>
      if s.length % 4 == 1 && s.length ≥ 5 then
        let ty := mkAppN (mkConst ``ShiftClaim) #[toExpr s,toExpr d,toExpr r,toExpr me]
        let name ← mkAuxLemma [] ty pr (some `shiftNode)
        pure (some (mkConst name))
      else pure result
    | none => pure none
  memo.modify (·.insert key saved)
  return saved

open Lean Meta Elab Tactic in
local elab "replay_shift " lo:num size:num gap:num : tactic => do
  let xs := List.range' lo.getNat size.getNat
  let memo ← IO.mkRef {}
  let some pr ← replayShift xs gap.getNat true false memo | throwError "no uniform strategy"
  let goal ← getMainGoal
  goal.assign pr
  replaceMainGoal []


set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- Every critical interval with at most eight pairs draws, for unbounded height.
The starting height can be one below twice the number of pairs. -/
theorem high_interval_draw_through_eight (n a : ℕ) (hn : 0<n) (h8 : n≤8) (ha : 2*n≤a+1) :
    gapValue (Finset.Ico a (a+2*n)) n = .draw := by
  apply high_interval_of_shift_base n (2*n-1) a hn (by omega) (by omega)
  have h : n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
  rcases h with h|h|h|h|h|h|h|h <;> subst n
  · replay_shift 1 1 1
  · replay_shift 3 3 4
  · replay_shift 5 5 7
  · replay_shift 7 7 10
  · replay_shift 9 9 13
  · replay_shift 11 11 16
  · replay_shift 13 13 19
  · replay_shift 15 15 22


theorem draw_all_shifts (xs : List ℕ) (hn : xs.Nodup)
    (h1 : shiftHold xs.length xs 0 false true = true)
    (h2 : shiftHold xs.length xs 0 false false = true) (t : ℕ) :
    value (xs.map (t+·)).toFinset = .draw := by
  have a := shiftHold_sound xs hn 0 t false true h1
  have b := shiftHold_sound xs hn 0 t false false h2
  rw [value_eq_gap]
  cases h : gapValue (xs.map (t+·)).toFinset 0 <;> simp_all

private def tenOffsets (i : ℕ) := ((List.range 10).erase i).erase (i+1)
private def tenTokens (a i : ℕ) := (tenOffsets i).map (a+·)

private theorem tenNodup (a i : ℕ) : (tenTokens a i).Nodup :=
  (((List.nodup_range).erase i).erase (i+1)).map (fun _ _ h => Nat.add_left_cancel h)

private theorem tenBoard (a i : ℕ) : (tenTokens a i).toFinset =
    ((Finset.Ico a (a+10)).erase (a+i)).erase (a+i+1) := by
  ext z
  simp only [tenTokens,tenOffsets,List.mem_toFinset,List.mem_map,
    (List.nodup_range.erase i).mem_erase_iff,List.nodup_range.mem_erase_iff,
    List.mem_range,Finset.mem_erase,Finset.mem_Ico]
  constructor
  · rintro ⟨j,⟨h1,h2,h3⟩,rfl⟩
    omega
  · intro h
    exact ⟨z-a,by omega,by omega⟩

private def listDraws (xs : List ℕ) : Bool :=
  canReach xs.length xs 0 false && !(canReach xs.length xs 0 true)

private theorem listDraws_sound {xs : List ℕ} (hn : xs.Nodup) (h : listDraws xs=true) :
    value xs.toFinset=.draw := by
  simp only [listDraws,canReach_correct,eval_correct _ hn] at h
  rw [value_eq_gap]
  cases hv : gapValue xs.toFinset 0 <;> simp_all [meets]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
private theorem tenSmall (a : Fin 9) : ∀ i : Fin 9, listDraws (tenTokens (a.val+1) i.val)=true := by
  have alt : a.val=0 ∨ a.val=1 ∨ a.val=2 ∨ a.val=3 ∨ a.val=4 ∨ a.val=5 ∨ a.val=6 ∨ a.val=7 ∨ a.val=8 := by omega
  rcases alt with h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
private theorem tenUniform : ∀ i : Fin 9, let xs := tenTokens 10 i.val
    shiftHold xs.length xs 0 false true=true ∧ shiftHold xs.length xs 0 false false=true := by decide +kernel

/-- Removing any adjacent pair from any ten consecutive positive integers leaves
a tied board whose exact value is a draw. -/
theorem ten_interval_adjacent_holes (a i : ℕ) (ha : 0<a) (hi : i<9) :
    value (((Finset.Ico a (a+10)).erase (a+i)).erase (a+i+1)) = .draw := by
  rw [←tenBoard]
  let j : Fin 9 := ⟨i,hi⟩
  by_cases small : a<10
  · let k : Fin 9 := ⟨a-1,by omega⟩
    have h := tenSmall k j
    change listDraws (tenTokens (a-1+1) i)=true at h
    rw [show a-1+1=a by omega] at h
    exact listDraws_sound (tenNodup a i) h
  · obtain ⟨h1,h2⟩ := tenUniform j
    have h := draw_all_shifts (tenTokens 10 i) (tenNodup 10 i) h1 h2 (a-10)
    have he : (tenTokens 10 i).map (a-10+·) = tenTokens a i := by
      simp only [tenTokens,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro y _
      omega
    rwa [he] at h

/-- Strictly past the center of the consecutive minimum-pick path, interval
length alone determines the exact winner, for every prefix size. -/
theorem upper_minimum_ray (N a : ℕ) (ha : N/2+2≤a) (hle : a≤N) :
    gapValue (Finset.Icc a N) (a/2) =
      if (N+1-a)%2=0 then .loss else .win := by
  let m := (N+1-a)/2
  by_cases even : (N+1-a)%2=0
  · simp only [even,ite_true]
    have hi : Finset.Icc a N = Finset.Ico a (a+2*m) := by
      ext z; simp only [Finset.mem_Icc,Finset.mem_Ico]; dsimp [m]; omega
    rw [hi]
    apply paired_reservoir_loss _ m _ (paired_interval a m) (by dsimp [m]; omega)
    intro z hz
    have := (Finset.mem_Ico.mp hz).1
    dsimp [m]; omega
  · simp only [even,ite_false]
    have hm : a∈Finset.Icc a N := Finset.mem_Icc.mpr ⟨le_rfl,hle⟩
    have hi : (Finset.Icc a N).erase a = Finset.Ico (a+1) (a+1+2*m) := by
      ext z; simp only [Finset.mem_erase,Finset.mem_Icc,Finset.mem_Ico]; dsimp [m]; omega
    have loss : gapValue (Finset.Ico (a+1) (a+1+2*m)) (a-a/2) = .loss := by
      apply paired_reservoir_loss _ m _ (paired_interval (a+1) m) (by dsimp [m]; omega)
      intro z hz
      have := (Finset.mem_Ico.mp hz).1
      dsimp [m]; omega
    apply (gap_win_iff _ ⟨a,hm⟩ _).mpr
    exact ⟨a,hm,by simp [pick,show ¬a<a/2 by omega,hi,loss,Outcome.neg]⟩

end CatchUpGame.Research
