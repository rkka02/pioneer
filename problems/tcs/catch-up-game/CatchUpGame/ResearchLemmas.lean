import CatchUpGame.Challenge
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int

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

end CatchUpGame.Research
