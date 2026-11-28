import OMAStatements.S_oeis_a111097
import Mathlib

/-!
# Maximum likelihood for the urn-size sequence A111097

Adjacent likelihoods are compared through a finite geometric sum. Cubic and quartic
binomial truncations locate its sign change at the conjectured integer urn size.
-/

namespace OEISA111097

open OMA.S_oeis_a111097 Finset

private def choose2 (m : ℚ) : ℚ := m * (m - 1) / 2
private def choose3 (m : ℚ) : ℚ := choose2 m * (m - 2) / 3
private def choose4 (m : ℚ) : ℚ := choose3 m * (m - 3) / 4

private def cubic (m x : ℚ) : ℚ := 1 - m * x + choose2 m * x ^ 2 - choose3 m * x ^ 3
private def quartic (m x : ℚ) : ℚ := cubic m x + choose4 m * x ^ 4

private lemma choose3_nonneg (m : ℕ) : 0 ≤ choose3 m := by
  by_cases hm : 2 ≤ m
  · have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
    unfold choose3 choose2
    have : 0 ≤ (m : ℚ) - 2 := by linarith
    have : 0 ≤ (m : ℚ) - 1 := by linarith
    positivity
  · interval_cases m <;> norm_num [choose3, choose2]

private lemma choose4_nonneg (m : ℕ) : 0 ≤ choose4 m := by
  by_cases hm : 3 ≤ m
  · have hm' : (3 : ℚ) ≤ m := by exact_mod_cast hm
    unfold choose4
    have := choose3_nonneg m
    have : 0 ≤ (m : ℚ) - 3 := by linarith
    positivity
  · interval_cases m <;> norm_num [choose4, choose3, choose2]

private lemma binomial_bounds {x : ℚ} (hx : 0 ≤ x) (hx' : x ≤ 1) (m : ℕ) :
    cubic m x ≤ (1 - x) ^ m ∧ (1 - x) ^ m ≤ quartic m x := by
  induction m with
  | zero => norm_num [cubic, quartic, choose4, choose3, choose2]
  | succ m ih =>
    have hc : (1 - x) * cubic m x = cubic ((m : ℚ) + 1) x + choose3 m * x ^ 4 := by
      unfold cubic choose3 choose2
      ring
    have hq : (1 - x) * quartic m x = quartic ((m : ℚ) + 1) x - choose4 m * x ^ 5 := by
      unfold quartic cubic choose4 choose3 choose2
      ring
    rw [pow_succ', Nat.cast_succ]
    have hp := sub_nonneg.mpr hx'
    constructor
    · calc
        _ ≤ (1 - x) * cubic m x := by
          rw [hc]
          exact le_add_of_nonneg_right (mul_nonneg (choose3_nonneg m) (pow_nonneg hx _))
        _ ≤ _ := mul_le_mul_of_nonneg_left ih.1 hp
    · calc
        _ ≤ (1 - x) * quartic m x := mul_le_mul_of_nonneg_left ih.2 hp
        _ ≤ _ := by
          rw [hq]
          exact sub_le_self _ (mul_nonneg (choose4_nonneg m) (pow_nonneg hx _))

private def contrast (n N : ℕ) : ℚ :=
  (n : ℚ) - ∑ i ∈ range (n + 1), ((N : ℚ) / ((N : ℚ) + 1)) ^ i

private lemma contrast_antitone (n : ℕ) : Antitone (contrast n) := by
  intro N K h
  have h' : (N : ℚ) ≤ K := by exact_mod_cast h
  have hf : (N : ℚ) / (N + 1) ≤ (K : ℚ) / (K + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold contrast
  refine sub_le_sub_left (sum_le_sum fun i _ => ?_) _
  exact pow_le_pow_left₀ (by positivity) hf _

private lemma contrast_scaled (n N : ℕ) :
    contrast n N / ((N : ℚ) + 1) =
      ((N : ℚ) / (N + 1)) ^ (n + 1) - (1 - (n : ℚ) / (N + 1)) := by
  have hp : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have h := geom_sum_mul_neg ((N : ℚ) / (N + 1)) (n + 1)
  have hs : 1 - (N : ℚ) / (N + 1) = 1 / (N + 1) := by
    field_simp
    ring
  rw [hs] at h
  unfold contrast
  rw [sub_div]
  linear_combination -h

private lemma likelihood_zero {n N : ℕ} (h : N < n) : likelihood n N = 0 := by
  simp [likelihood, Nat.descFactorial_of_lt h]

private lemma likelihood_pos {n N : ℕ} (hn : 0 < n) (h : n ≤ N) : 0 < likelihood n N := by
  unfold likelihood
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hN : (0 : ℚ) < N := by exact_mod_cast hn.trans_le h
  have hF : (0 : ℚ) < N.descFactorial n := by exact_mod_cast Nat.descFactorial_pos.mpr h
  positivity

private lemma likelihood_difference {n N : ℕ} (hn : 0 < n) (h : n ≤ N) :
    likelihood n (N + 1) - likelihood n N =
      (likelihood n N / ((N : ℚ) + 1 - (n : ℚ))) * contrast n N := by
  have hN : (0 : ℚ) < N := by exact_mod_cast hn.trans_le h
  have hN1 : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have h' : (n : ℚ) ≤ N := by exact_mod_cast h
  have hd : (0 : ℚ) < (N : ℚ) + 1 - (n : ℚ) := by linarith
  have hDesc : ((N : ℚ) + 1 - (n : ℚ)) * ((N + 1).descFactorial n : ℚ) =
      ((N : ℚ) + 1) * (N.descFactorial n : ℚ) := by
    have hc := congrArg (fun z : ℕ => (z : ℚ)) (Nat.succ_descFactorial N n)
    push_cast [Nat.cast_sub (by omega : n ≤ N + 1)] at hc
    exact hc
  have hNext : ((N + 1).descFactorial n : ℚ) =
      ((N : ℚ) + 1) * (N.descFactorial n : ℚ) / ((N : ℚ) + 1 - (n : ℚ)) :=
    (eq_div_iff hd.ne').2 ((mul_comm _ _).trans hDesc)
  have hc := (div_eq_iff hN1.ne').1 (contrast_scaled n N)
  rw [hc]
  unfold likelihood
  rw [Nat.cast_add, Nat.cast_one, hNext, div_pow]
  field_simp

private lemma adjacent_up {n N : ℕ} (hn : 0 < n) (h : n ≤ N) (hc : 0 < contrast n N) :
    likelihood n N < likelihood n (N + 1) := by
  have hnN : (n : ℚ) ≤ N := by exact_mod_cast h
  have hd : (0 : ℚ) < (N : ℚ) + 1 - (n : ℚ) := by linarith
  have hp := mul_pos (div_pos (likelihood_pos hn h) hd) hc
  rw [← likelihood_difference hn h] at hp
  exact sub_pos.mp hp

private lemma adjacent_down {n N : ℕ} (hn : 0 < n) (h : n ≤ N) (hc : contrast n N ≤ 0) :
    likelihood n (N + 1) ≤ likelihood n N := by
  have hnN : (n : ℚ) ≤ N := by exact_mod_cast h
  have hd : (0 : ℚ) < (N : ℚ) + 1 - (n : ℚ) := by linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (div_pos (likelihood_pos hn h) hd).le hc
  rw [← likelihood_difference hn h] at hp
  exact sub_nonpos.mp hp

end OEISA111097
namespace OEISA111097

open OMA.S_oeis_a111097 Finset

private def triangular (n : ℕ) : ℕ := n * (n + 1) / 2
private def third (n : ℕ) : ℕ := (n - 1) / 3
private def peak (n : ℕ) : ℕ := triangular n - 1 - third n

private lemma triangular_cast (n : ℕ) : (triangular n : ℚ) = choose2 ((n : ℚ) + 1) := by
  unfold triangular choose2
  rw [Nat.cast_div_charZero n.two_dvd_mul_add_one]
  push_cast
  ring

private lemma third_bounds {n : ℕ} (hn : 1 ≤ n) :
    let s := ((n : ℚ) - 1) / 3
    let t := (third n : ℚ)
    0 ≤ t ∧ t ≤ s ∧ s ≤ t + 2 / 3 ∧ (s = t ∨ t + 1 / 3 ≤ s) := by
  dsimp only
  have hlo : 3 * third n ≤ n - 1 := by unfold third; omega
  have hhi : n - 1 ≤ 3 * third n + 2 := by unfold third; omega
  have hlo' : (↑(3 * third n) : ℚ) ≤ ↑(n - 1) := by exact_mod_cast hlo
  have hhi' : (↑(n - 1) : ℚ) ≤ ↑(3 * third n + 2) := by exact_mod_cast hhi
  push_cast [Nat.cast_sub hn] at hlo' hhi'
  refine ⟨by positivity, by linarith, by linarith, ?_⟩
  rcases eq_or_lt_of_le hlo with he | he
  · have he' : (↑(3 * third n) : ℚ) = ↑(n - 1) := by exact_mod_cast he
    push_cast [Nat.cast_sub hn] at he'
    left
    linarith
  · have he : 3 * third n + 1 ≤ n - 1 := he
    have he' : (↑(3 * third n + 1) : ℚ) ≤ ↑(n - 1) := by exact_mod_cast he
    push_cast [Nat.cast_sub hn] at he'
    right
    linarith

private lemma contrast_at_large_peak {n : ℕ} (hn : 7 ≤ n) :
    n < peak n ∧ 0 < contrast n (peak n - 1) ∧ contrast n (peak n) < 0 := by
  let u := (n : ℚ)
  let A := choose2 (u + 1)
  let s := (u - 1) / 3
  let t := (third n : ℚ)
  have hu : 7 ≤ u := by dsimp [u]; exact_mod_cast hn
  have hA : A = u * (u + 1) / 2 := by unfold A choose2; ring
  have hA0 : 0 < A := by rw [hA]; positivity
  have hs : 0 < s := by dsimp [s]; linarith
  obtain ⟨ht0, hts, hst, hsplit⟩ := third_bounds (show 1 ≤ n by omega)
  change 0 ≤ t at ht0
  change t ≤ s at hts
  change s ≤ t + 2 / 3 at hst
  change s = t ∨ t + 1 / 3 ≤ s at hsplit
  have hsep : u + 2 + t ≤ A := by
    rw [hA]
    dsimp [s] at hts
    nlinarith [sq_nonneg (u - 7)]
  have hNat : n + 2 + third n ≤ triangular n := by
    have h : ((n : ℚ) + 2 + (third n : ℚ)) ≤ (triangular n : ℚ) := by
      rw [triangular_cast]
      exact hsep
    exact_mod_cast h
  have hpeak : n < peak n := by unfold peak; omega
  have hcast : (peak n : ℚ) = A - 1 - t := by
    unfold peak
    rw [Nat.cast_sub (by omega : third n ≤ triangular n - 1),
      Nat.cast_sub (by omega : 1 ≤ triangular n), triangular_cast, Nat.cast_one]
  let M₁ := (peak n : ℚ)
  let M₂ := M₁ + 1
  have hM₁ : M₁ = A - t - 1 := by dsimp [M₁]; linarith
  have hM₂ : M₂ = A - t := by dsimp [M₂]; linarith
  have hM₁ge : 1 ≤ M₁ := by dsimp [M₁]; exact_mod_cast (show 1 ≤ peak n by omega)
  have hM₁pos : 0 < M₁ := by linarith
  have hM₂ge : 1 ≤ M₂ := by dsimp [M₂]; linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hA3 : choose3 (u + 1) = A * s := by unfold choose3 A s; ring
  have hA4 : choose4 (u + 1) = A * s * (u - 2) / 4 := by rw [choose4, hA3]; ring
  have hsize : ((u + 2) / 3) ^ 2 < A / 3 := by
    rw [hA]
    nlinarith [sq_nonneg (u - 7)]
  have hleft : 0 < -M₁ ^ 2 + A * M₁ - A * s := by
    have hv : 0 ≤ t + 1 := by linarith
    have hv' : t + 1 ≤ (u + 2) / 3 := by dsimp [s] at hts; linarith
    have hv2 := pow_le_pow_left₀ hv hv' 2
    have hg : A / 3 ≤ A * (t + 1 - s) := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℚ) / 3 ≤ t + 1 - s by linarith) hA0.le
      linarith
    calc
      0 < A * (t + 1 - s) - (t + 1) ^ 2 := by linarith
      _ = _ := by rw [hM₁]; ring
  have hright : -M₂ ^ 3 + A * M₂ ^ 2 - A * s * M₂ + A * s * (u - 2) / 4 < 0 := by
    have hf : -M₂ ^ 3 + A * M₂ ^ 2 - A * s * M₂ + A * s * (u - 2) / 4 =
        -(s - t) * A * M₂ - t ^ 2 * M₂ + A * s * (u - 2) / 4 := by
      rw [hM₂]
      ring
    rw [hf]
    rcases hsplit with hsEq | hgap
    · have hs2 : s ^ 2 < A * ((u + 2) / 12) := by
        have hsle : s ≤ (u + 2) / 3 := by dsimp [s]; linarith
        have hx := pow_le_pow_left₀ hs.le hsle 2
        have hy := mul_le_mul_of_nonneg_left (show (1 : ℚ) / 3 ≤ (u + 2) / 12 by linarith) hA0.le
        linarith
      have hz : 0 < s * M₂ - A * (u - 2) / 4 := by
        rw [hM₂, ← hsEq]
        dsimp [s] at hs2 ⊢
        linarith
      have hz' := mul_pos hs hz
      rw [← hsEq]
      nlinarith
    · have hsmall : s * (u - 2) / 4 < M₂ / 3 := by
        have hMs : A - s ≤ M₂ := by rw [hM₂]; linarith
        rw [hA] at hMs
        dsimp [s] at hMs ⊢
        nlinarith [sq_nonneg u]
      have hAM : 0 < A * M₂ := mul_pos hA0 hM₂pos
      have hy := mul_le_mul_of_nonneg_right (show (1 : ℚ) / 3 ≤ s - t by linarith) hAM.le
      have hz := mul_lt_mul_of_pos_left hsmall hA0
      have hw := mul_nonneg (sq_nonneg t) hM₂pos.le
      linarith
  have bound₁ (M : ℚ) (hM : 0 < M) :
      (cubic (u + 1) (1 / M) - (1 - u / M)) * M ^ 3 = -M ^ 2 + A * M - A * s := by
    unfold cubic
    rw [hA3]
    change (_ + A * (1 / M) ^ 2 - A * s * (1 / M) ^ 3 - (1 - u / M)) * M ^ 3 = _
    field_simp
    ring
  have bound₂ (M : ℚ) (hM : 0 < M) :
      (quartic (u + 1) (1 / M) - (1 - u / M)) * M ^ 4 =
        -M ^ 3 + A * M ^ 2 - A * s * M + A * s * (u - 2) / 4 := by
    unfold quartic cubic
    rw [hA3, hA4]
    change (_ + A * (1 / M) ^ 2 - A * s * (1 / M) ^ 3 +
      A * s * (u - 2) / 4 * (1 / M) ^ 4 - (1 - u / M)) * M ^ 4 = _
    field_simp
    ring
  have hpow₁ : 1 - u / M₁ < (1 - 1 / M₁) ^ (n + 1) := by
    have hp := (binomial_bounds (x := 1 / M₁) (by positivity)
      ((div_le_iff₀ hM₁pos).mpr (by simpa using hM₁ge)) (n + 1)).1
    push_cast at hp
    refine lt_of_lt_of_le ?_ hp
    refine lt_of_mul_lt_mul_right (a := M₁ ^ 3) ?_ (by positivity)
    have h := bound₁ M₁ hM₁pos
    rw [sub_mul] at h
    linarith
  have hpow₂ : (1 - 1 / M₂) ^ (n + 1) < 1 - u / M₂ := by
    have hp := (binomial_bounds (x := 1 / M₂) (by positivity)
      ((div_le_iff₀ hM₂pos).mpr (by simpa using hM₂ge)) (n + 1)).2
    push_cast at hp
    refine lt_of_le_of_lt hp ?_
    refine lt_of_mul_lt_mul_right (a := M₂ ^ 4) ?_ (by positivity)
    have h := bound₂ M₂ hM₂pos
    rw [sub_mul] at h
    linarith
  have hcon (N : ℕ) : contrast n N / ((N : ℚ) + 1) =
      (1 - 1 / ((N : ℚ) + 1)) ^ (n + 1) - (1 - u / ((N : ℚ) + 1)) := by
    rw [contrast_scaled]
    have heq : (N : ℚ) / (N + 1) = 1 - 1 / (N + 1) := by
      field_simp
      ring
    rw [heq]
  refine ⟨hpeak, ?_, ?_⟩
  · have h := hcon (peak n - 1)
    have heq : ((peak n - 1 : ℕ) : ℚ) + 1 = M₁ := by
      rw [Nat.cast_sub (by omega : 1 ≤ peak n), Nat.cast_one]
      dsimp [M₁]
      ring
    rw [heq] at h
    exact (div_pos_iff_of_pos_right hM₁pos).mp (h ▸ by linarith)
  · have h := hcon (peak n)
    change contrast n (peak n) / M₂ = (1 - 1 / M₂) ^ (n + 1) - (1 - u / M₂) at h
    have hneg : contrast n (peak n) / M₂ < 0 := by rw [h]; linarith
    simpa using (div_lt_iff₀ hM₂pos).mp hneg

private lemma peak_contrasts {n : ℕ} (hn : 2 ≤ n) :
    n ≤ peak n ∧ (n < peak n → 0 < contrast n (peak n - 1)) ∧ contrast n (peak n) < 0 := by
  by_cases h : 7 ≤ n
  · obtain ⟨h1, h2, h3⟩ := contrast_at_large_peak h
    exact ⟨h1.le, fun _ => h2, h3⟩
  · interval_cases n <;> norm_num [peak, triangular, third, contrast, Finset.sum_range_succ]

end OEISA111097
namespace OEISA111097

open OMA.S_oeis_a111097 Finset

private lemma a_zero : a 0 = 0 := by simp [a]

private lemma a_one : a 1 = 1 := by
  rw [a, if_neg (by decide : (1 : ℕ) ≠ 0)]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by decide, ?_⟩
    intro K hK
    have hK' : (1 : ℚ) ≤ K := by exact_mod_cast hK
    have hp : (0 : ℚ) < K := by positivity
    have hL : likelihood 1 K = 1 / (K : ℚ) := by
      simp only [likelihood, Nat.cast_one, Nat.descFactorial_one, one_mul]
      field_simp
    have hLone : likelihood 1 1 = 1 := by norm_num [likelihood, Nat.descFactorial_one]
    rw [hL, hLone]
    exact (div_le_iff₀ hp).mpr (by simpa using hK')
  · intro K hK
    exact hK.1

private lemma a_eq_peak {n : ℕ} (hn : 2 ≤ n) : a n = peak n := by
  obtain ⟨hpeak, hleft, hright⟩ := peak_contrasts hn
  have hn0 : 0 < n := by omega
  have hA : StrictMonoOn (likelihood n) (Set.Icc n (peak n)) := by
    apply strictMonoOn_of_lt_succ Set.ordConnected_Icc
    intro K _ hK hK'
    have hnK : n ≤ K := hK.1
    have hKp : K + 1 ≤ peak n := hK'.2
    have hc : 0 < contrast n K := (hleft (by omega)).trans_le
      (contrast_antitone n (by omega : K ≤ peak n - 1))
    exact adjacent_up hn0 hnK hc
  have hB := antitoneOn_nat_Ici_of_succ_le (f := likelihood n) (k := peak n) (fun K hK =>
    adjacent_down hn0 (hpeak.trans hK) ((contrast_antitone n hK).trans hright.le))
  have below {K : ℕ} (hK : K < peak n) : likelihood n K < likelihood n (peak n) := by
    by_cases hKn : n ≤ K
    · exact hA ⟨hKn, hK.le⟩ ⟨hpeak, le_rfl⟩ hK
    · rw [likelihood_zero (lt_of_not_ge hKn)]
      exact likelihood_pos hn0 hpeak
  rw [a, if_neg hn0.ne']
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hn0.trans_le hpeak, ?_⟩
    intro K _
    rcases lt_or_ge K (peak n) with ht | ht
    · exact (below ht).le
    · exact hB (show peak n ≤ peak n by rfl) ht ht
  · intro K hK
    by_contra! hlt
    exact (not_le_of_gt (below hlt)) (hK.2 _ (hn0.trans_le hpeak))

private lemma triangular_succ (n : ℕ) : triangular (n + 1) = triangular n + (n + 1) := by
  have h := Nat.triangle_succ (n + 1)
  simpa only [triangular, Nat.add_sub_cancel, Nat.mul_comm] using h

private lemma peak_int {n : ℕ} (hn : 2 ≤ n) :
    (peak n : ℤ) = (triangular n : ℤ) - 1 - (third n : ℤ) := by
  have h := (peak_contrasts hn).1
  unfold peak at h ⊢
  rw [Nat.cast_sub (by omega : third n ≤ triangular n - 1),
    Nat.cast_sub (by omega : 1 ≤ triangular n), Nat.cast_one]

private lemma a_difference (n : ℕ) (hn : 0 < n) :
    (a (n + 2) : ℤ) - 2 * (a (n + 1) : ℤ) + (a n : ℤ) = secondDifferenceValue n := by
  by_cases h : n = 1
  · subst n
    norm_num [a_one, a_eq_peak (n := 2) (by decide), a_eq_peak (n := 3) (by decide), peak,
      triangular, third, secondDifferenceValue]
  · have hn2 : 2 ≤ n := by omega
    rw [a_eq_peak hn2, a_eq_peak (n := n + 1) (by omega), a_eq_peak (n := n + 2) (by omega),
      peak_int hn2, peak_int (n := n + 1) (by omega), peak_int (n := n + 2) (by omega),
      triangular_succ (n + 1), triangular_succ n]
    push_cast
    unfold secondDifferenceValue third
    split_ifs <;> omega

private lemma series_identity :
    let x := (PowerSeries.X : PowerSeries ℤ)
    (1 - x) ^ 3 * (1 + x + x ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      x * (1 + 2 * x ^ 2 - x ^ 3 + 2 * x ^ 4 - x ^ 5) := by
  let x := (PowerSeries.X : PowerSeries ℤ)
  let F := PowerSeries.mk (fun n => (a n : ℤ))
  change (1 - x) ^ 3 * (1 + x + x ^ 2) * F = _
  have hD : (1 - x) ^ 3 * (1 + x + x ^ 2) =
      1 - PowerSeries.C (2 : ℤ) * x ^ 1 + x ^ 2 - x ^ 3 + PowerSeries.C (2 : ℤ) * x ^ 4 - x ^ 5 := by
    simp only [map_ofNat]
    ring
  have hG : x * (1 + 2 * x ^ 2 - x ^ 3 + 2 * x ^ 4 - x ^ 5) =
      PowerSeries.C (1 : ℤ) * x ^ 1 + PowerSeries.C (2 : ℤ) * x ^ 3 - PowerSeries.C (1 : ℤ) * x ^ 4 +
        PowerSeries.C (2 : ℤ) * x ^ 5 - PowerSeries.C (1 : ℤ) * x ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  have hC (n d : ℕ) : PowerSeries.coeff n (x ^ d * F) = if d ≤ n then (a (n - d) : ℤ) else 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    simp only [F, PowerSeries.coeff_mk]
  have hX (n d : ℕ) : PowerSeries.coeff n (x ^ d) = if n = d then (1 : ℤ) else 0 :=
    PowerSeries.coeff_X_pow n d
  ext n
  rw [hD, hG]
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, PowerSeries.coeff_C_mul,
    hC, hX, F, PowerSeries.coeff_mk]
  by_cases hn : 7 ≤ n
  · have h₁ : 1 ≤ n := by omega
    have h₂ : 2 ≤ n := by omega
    have h₃ : 3 ≤ n := by omega
    have h₄ : 4 ≤ n := by omega
    have h₅ : 5 ≤ n := by omega
    simp only [if_pos h₁, if_pos h₂, if_pos h₃, if_pos h₄, if_pos h₅,
      if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 3), if_neg (by omega : n ≠ 4),
      if_neg (by omega : n ≠ 5), if_neg (by omega : n ≠ 6), zero_add, sub_zero]
    have h2 := a_difference (n - 2) (by omega)
    have h5 := a_difference (n - 5) (by omega)
    rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at h2
    rw [show n - 5 + 2 = n - 3 by omega, show n - 5 + 1 = n - 4 by omega] at h5
    have hs : secondDifferenceValue (n - 2) = secondDifferenceValue (n - 5) := by
      unfold secondDifferenceValue
      rw [if_neg (by omega : n - 2 ≠ 1), if_neg (by omega : n - 5 ≠ 1),
        show (n - 2) % 3 = (n - 5) % 3 by omega]
    linarith
  · interval_cases n <;>
      norm_num [a_zero, a_one, a_eq_peak (n := 2) (by decide), a_eq_peak (n := 3) (by decide),
        a_eq_peak (n := 4) (by decide), a_eq_peak (n := 5) (by decide), a_eq_peak (n := 6) (by decide),
        peak, triangular, third]

end OEISA111097

-- Credit: @rkka02
theorem OMA.solution : type_of% @OMA.S_oeis_a111097.main :=
  ⟨OEISA111097.a_one, fun _ h => OEISA111097.a_eq_peak h, OEISA111097.a_difference,
    OEISA111097.series_identity⟩
