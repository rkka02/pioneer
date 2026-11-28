import OMAStatements.S_oeis_a392819

/-!
# Natural density of OEIS A392819

A term divisible by a large prime `p` is a multiple of `p^2` or `p*(p+1)`.
A reciprocal-square tail bounds the contribution from these multiples.
The remaining integers have only small prime factors and are bounded by
separating off multiples of high powers of those primes.
-/

open Filter Finset
open scoped BigOperators Topology

open OMA.S_oeis_a392819

private def multiples (X d : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun n => d ∣ n

private theorem card_multiples_le (X d : ℕ) :
    ((multiples X d).card : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
  have hcard : (multiples X d).card ≤ (Icc 1 (X / d)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n / d)
    · intro n hn
      have ⟨hnBounds, hdvd⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hnBounds
      have heq := Nat.div_mul_cancel hdvd
      have hquot : 1 ≤ n / d := by
        by_cases hq : n / d = 0
        · rw [hq, zero_mul] at heq
          omega
        · exact Nat.one_le_iff_ne_zero.mpr hq
      exact Finset.mem_Icc.mpr ⟨hquot, Nat.div_le_div_right hn₂⟩
    · intro m hm n hn hdiv
      have hm' := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
      have hn' := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
      change m / d = n / d at hdiv
      rw [hdiv, hn'] at hm'
      exact hm'.symm
  rw [Nat.card_Icc] at hcard
  simp only [Nat.add_sub_cancel] at hcard
  exact (by exact_mod_cast hcard : ((multiples X d).card : ℝ) ≤ ↑(X / d)).trans
    Nat.cast_div_le

private theorem large_factor {n p : ℕ} (hn : isTerm n) (hp : p ∈ n.primeFactors) :
    p ^ 2 ∣ n ∨ p * (p + 1) ∣ n := by
  obtain ⟨hprime, hdiv, hnz⟩ := Nat.mem_primeFactors.mp hp
  by_cases he : 2 ≤ n.factorization p
  · exact Or.inl ((hprime.pow_dvd_iff_le_factorization hnz).mpr he)
  · right
    have hpos := hprime.factorization_pos_of_dvd hnz hdiv
    have hEq : n.factorization p = 1 := by omega
    have hc : p.Coprime (p + 1) := by simp
    apply hc.mul_dvd_of_dvd_of_dvd hdiv
    simpa only [hEq] using hn p hp

private theorem smooth_bound {n R K : ℕ} (hn : n ≠ 0)
    (hr : ∀ p ∈ n.primeFactors, p < R)
    (hk : ∀ p ∈ n.primeFactors, ¬ p ^ K ∣ n) :
    n ≤ ∏ p ∈ Ico 2 R, p ^ K := by
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Nat.prod_primeFactors_pow_factorization hn
    _ ≤ ∏ p ∈ n.primeFactors, p ^ K := by
      apply Finset.prod_le_prod'
      intro p hp
      have hprime := (Nat.mem_primeFactors.mp hp).1
      apply Nat.pow_le_pow_right hprime.pos
      have hlt := not_le.mp fun h => hk p hp ((hprime.pow_dvd_iff_le_factorization hn).mpr h)
      exact hlt.le
    _ ≤ ∏ p ∈ Ico 2 R, p ^ K := by
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · intro p hp
        exact Finset.mem_Ico.mpr ⟨(Nat.mem_primeFactors.mp hp).1.two_le, hr p hp⟩
      · intro p hp _
        have hpos : 0 < p := by
          have := (Finset.mem_Ico.mp hp).1
          omega
        exact Nat.one_le_pow _ _ hpos

private theorem tail_square_bound (R X : ℕ) (hR : 2 ≤ R) (hX : R ≤ X) :
    (∑ p ∈ Ico R (X + 1), (1 : ℝ) / (p : ℝ)^2) ≤ 1 / ((R : ℝ) - 1) := by
  let f (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)
  calc
    (∑ p ∈ Ico R (X + 1), (1 : ℝ) / (p : ℝ)^2) ≤
        ∑ p ∈ Ico R (X + 1), (f p - f (p+1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR : 2 ≤ p := hR.trans (Finset.mem_Ico.mp hp).1
      have hp' : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
      have hp0 : 0 < (p : ℝ) := by linarith
      have hm : 0 < (p : ℝ) - 1 := by linarith
      have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos hp0 hm
      have heq : f p - f (p+1) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        simp only [f, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        field_simp
        ring
      rw [heq]
      apply div_le_div_of_nonneg_left (by norm_num) hden
      nlinarith
    _ = f R - f (X + 1) := by
      calc
        _ = -∑ p ∈ Ico R (X + 1), (f (p + 1) - f p) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro p _
          rw [neg_sub]
        _ = _ := by
          rw [Finset.sum_Ico_sub f (show R ≤ X + 1 by omega), neg_sub]
    _ ≤ 1 / ((R : ℝ) - 1) := by
      change f R - f (X + 1) ≤ f R
      have hx' : 0 ≤ (↑(X + 1) : ℝ) - 1 := by simp
      have hf : 0 ≤ f (X + 1) := one_div_nonneg.mpr hx'
      linarith

private theorem big_multiples_bound (R X : ℕ) (hR : 2 ≤ R) (hX : R ≤ X) :
    (((Ico R (X + 1)).biUnion
      (fun p => multiples X (p ^ 2) ∪ multiples X (p * (p + 1)))).card : ℝ)
      ≤ (X : ℝ) * (2 / ((R : ℝ) - 1)) := by
  calc
    _ ≤ ∑ p ∈ Ico R (X + 1),
        ((multiples X (p ^ 2) ∪ multiples X (p * (p + 1))).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Ico R (X + 1), (2 * (X : ℝ)) * ((1 : ℝ) / (p : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp_pos : 0 < (p : ℝ) := by
        exact_mod_cast (show 0 < p from lt_of_lt_of_le (by decide : 0 < 2)
          (hR.trans (Finset.mem_Ico.mp hp).1))
      have hcu : (((multiples X (p ^ 2)) ∪
          (multiples X (p * (p + 1)))).card : ℝ) ≤
          ((multiples X (p ^ 2)).card : ℝ) + ((multiples X (p * (p + 1))).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      have hb₁ := card_multiples_le X (p ^ 2)
      have hb₂ := card_multiples_le X (p * (p + 1))
      push_cast at hb₁ hb₂
      have hmono : (X : ℝ) / ((p : ℝ) * ((p : ℝ) + 1)) ≤ (X : ℝ) / (p : ℝ)^2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      calc
        _ ≤ (X : ℝ) / (p : ℝ)^2 + (X : ℝ) / (p : ℝ)^2 :=
          hcu.trans (add_le_add hb₁ (hb₂.trans hmono))
        _ = (2 * (X : ℝ)) * (1 / (p : ℝ)^2) := by ring
    _ = (2 * (X : ℝ)) * ∑ p ∈ Ico R (X + 1), (1 : ℝ) / (p : ℝ)^2 := by
      rw [Finset.mul_sum]
    _ ≤ (2 * (X : ℝ)) * (1 / ((R : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (tail_square_bound R X hR hX) (by positivity)
    _ = (X : ℝ) * (2 / ((R : ℝ) - 1)) := by ring

private theorem small_multiples_bound (R K X : ℕ) :
    (((Ico 2 R).biUnion fun p => multiples X (p ^ K)).card : ℝ)
      ≤ (R : ℝ) * ((X : ℝ) / (2 : ℝ)^K) := by
  calc
    _ ≤ ∑ p ∈ Ico 2 R, ((multiples X (p ^ K)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ((Ico 2 R).card : ℝ) * ((X : ℝ) / (2 : ℝ)^K) := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro p hp
      have hb := card_multiples_le X (p ^ K)
      push_cast at hb
      refine hb.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (Finset.mem_Ico.mp hp).1) K
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast le_trans (Finset.card_le_card (show Ico 2 R ⊆ range R from
        fun p hp => Finset.mem_range.mpr (Finset.mem_Ico.mp hp).2)) (by simp)

private theorem count_bound (R K X : ℕ) (hR : 2 ≤ R) (hX : R ≤ X) :
    (count X : ℝ) ≤
      (↑(∏ p ∈ Ico 2 R, p ^ K) : ℝ) +
      (R : ℝ) * ((X : ℝ) / (2 : ℝ)^K) + (X : ℝ) * (2 / ((R : ℝ) - 1)) := by
  classical
  let B := ∏ p ∈ Ico 2 R, p ^ K
  let S := (Ico 2 R).biUnion fun p => multiples X (p ^ K)
  let T := (Ico R (X + 1)).biUnion
    fun p => multiples X (p ^ 2) ∪ multiples X (p * (p + 1))
  have hcover : (Icc 1 X).filter isTerm ⊆ Icc 1 B ∪ S ∪ T := by
    intro n h
    obtain ⟨hb, hn⟩ := Finset.mem_filter.mp h
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hb
    by_cases hP : ∃ p ∈ n.primeFactors, R ≤ p
    · obtain ⟨p, hp, hRp⟩ := hP
      have hpX := (Nat.le_of_dvd (show 0 < n by omega) (Nat.mem_primeFactors.mp hp).2.1).trans hn₂
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_Ico.mpr ⟨hRp, by omega⟩, ?_⟩
      rcases large_factor hn hp with h₂ | h₂
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, h₂⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, h₂⟩)
    · push Not at hP
      apply Finset.mem_union_left
      by_cases hK : ∃ p ∈ n.primeFactors, p ^ K ∣ n
      · obtain ⟨p, hp, hd⟩ := hK
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨p,
          Finset.mem_Ico.mpr ⟨(Nat.mem_primeFactors.mp hp).1.two_le, hP p hp⟩,
          Finset.mem_filter.mpr ⟨hb, hd⟩⟩
      · push Not at hK
        exact Finset.mem_union_left _ (Finset.mem_Icc.mpr
          ⟨hn₁, smooth_bound (by omega) hP hK⟩)
  have hcards : count X ≤ (Icc 1 B).card + S.card + T.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le (Icc 1 B ∪ S) T).trans
      (Nat.add_le_add_right (Finset.card_union_le (Icc 1 B) S) _))
  rw [Nat.card_Icc] at hcards
  simp only [Nat.add_sub_cancel] at hcards
  have h := (by exact_mod_cast hcards : (count X : ℝ) ≤ ↑B + ↑S.card + ↑T.card)
  exact h.trans (add_le_add (add_le_add_right (small_multiples_bound R K X) _)
    (big_multiples_bound R X hR hX))

/-- The natural density of the terms of A392819 is zero. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a392819.main := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := exists_nat_gt (8 / ε + 2)
  have hR₂ : 2 ≤ R := by
    have h₀ : 0 < 8 / ε := by positivity
    exact_mod_cast (show (2 : ℝ) ≤ (R : ℝ) by linarith)
  have hRpos : 0 < (R : ℝ) - 1 := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR₂
    linarith
  have hRerr : (2 : ℝ) / ((R : ℝ) - 1) < ε / 4 := by
    apply (div_lt_iff₀ hRpos).mpr
    have hp : 8 < ((R : ℝ) - 2) * ε := (div_lt_iff₀ hε).mp (by linarith)
    nlinarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (4 * (R : ℝ) / ε) (show (1 : ℝ) < 2 by norm_num)
  have hKerr : (R : ℝ) / (2 : ℝ)^K < ε / 4 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hp := (div_lt_iff₀ hε).mp hK
    nlinarith
  let B := ∏ p ∈ Ico 2 R, p ^ K
  obtain ⟨U, hU⟩ := exists_nat_gt (4 * (B : ℝ) / ε)
  refine ⟨max R U, ?_⟩
  intro X hX
  have hXR : R ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXB : (B : ℝ) / (X : ℝ) < ε / 4 := by
    have hl : (U : ℝ) ≤ (X : ℝ) := by exact_mod_cast (le_max_right R U).trans hX
    apply (div_lt_iff₀ hX0).mpr
    have hp := (div_lt_iff₀ hε).mp (hU.trans_le hl)
    nlinarith
  have hc := div_le_div_of_nonneg_right (count_bound R K X hR₂ hXR) hX0.le
  change (count X : ℝ) / (X : ℝ) ≤
    ((B : ℝ) + (R : ℝ) * ((X : ℝ) / (2 : ℝ)^K) +
      (X : ℝ) * (2 / ((R : ℝ) - 1))) / (X : ℝ) at hc
  have heq : ((B : ℝ) + (R : ℝ) * ((X : ℝ) / (2 : ℝ)^K) +
      (X : ℝ) * (2 / ((R : ℝ) - 1))) / (X : ℝ) =
      (B : ℝ) / (X : ℝ) + (R : ℝ) / (2 : ℝ)^K + 2 / ((R : ℝ) - 1) := by
    have htwo : (2 : ℝ)^K ≠ 0 := by positivity
    field_simp [hX0.ne', hRpos.ne', htwo]
  rw [heq] at hc
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  linarith

/-- The entry's odd-prime-power assertion fails at 5625. -/
theorem A392819.odd_composite_base :
    Odd (5625 : ℕ) ∧ isTerm 5625 ∧ ¬ IsPrimePow (5625 : ℕ) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    have hdiv := (Nat.mem_primeFactors.mp hp).2.1
    have hp' := (Nat.mem_primeFactors.mp hp).1
    have hf : p ∣ 3 ^ 2 * 5 ^ 4 := by simpa using hdiv
    rcases hp'.dvd_mul.mp hf with h₃ | h₅
    · have heq := (Nat.prime_dvd_prime_iff_eq hp' (by decide : Nat.Prime 3)).mp
        (hp'.dvd_of_dvd_pow h₃)
      subst p
      rw [show (5625 : ℕ) = 3 ^ 2 * 5 ^ 4 by decide,
        Nat.factorization_mul (by decide) (by decide),
        (by decide : Nat.Prime 3).factorization_pow,
        (by decide : Nat.Prime 5).factorization_pow]
      norm_num [Finsupp.single_apply]
    · have heq := (Nat.prime_dvd_prime_iff_eq hp' (by decide : Nat.Prime 5)).mp
        (hp'.dvd_of_dvd_pow h₅)
      subst p
      rw [show (5625 : ℕ) = 3 ^ 2 * 5 ^ 4 by decide,
        Nat.factorization_mul (by decide) (by decide),
        (by decide : Nat.Prime 3).factorization_pow,
        (by decide : Nat.Prime 5).factorization_pow]
      norm_num [Finsupp.single_apply]
  · intro h
    obtain ⟨p, k, hp, _, hk⟩ := (isPrimePow_nat_iff _).mp h
    have h₃ : 3 ∣ p ^ k := hk ▸ (by decide : 3 ∣ (5625 : ℕ))
    have h₅ : 5 ∣ p ^ k := hk ▸ (by decide : 5 ∣ (5625 : ℕ))
    have h₃p := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp
      ((by decide : Nat.Prime 3).dvd_of_dvd_pow h₃)
    have h₅p := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp
      ((by decide : Nat.Prime 5).dvd_of_dvd_pow h₅)
    omega
