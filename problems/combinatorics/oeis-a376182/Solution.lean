import OMAStatements.S_oeis_a376182
import Mathlib

namespace SchulteTriangle
open OMA.S_oeis_a376182

/-- Counts through row n, separately for even and odd columns. -/
def cut (odd : Bool) (n : ℕ) : ℕ :=
  if odd then ((n+1)/2)*((n+2)/2) else (n/2)*((n+1)/2)

private theorem zero_cut (b : Bool) : cut b 0 = 0 := by cases b <;> decide

private theorem cut_step (b : Bool) (r : ℕ) :
    cut b (r+1) = cut b r + (if b then (r+2)/2 else (r+1)/2) := by
  obtain ⟨t, h | h⟩ : ∃ t, r=2*t ∨ r=2*t+1 := ⟨r/2, by omega⟩
  all_goals
    subst r
    cases b <;> simp only [cut, Bool.false_eq_true, if_false, if_true, Nat.add_assoc, one_add_one_eq_two] <;>
      simp only [show 2*t/2=t by omega, show (2*t+1)/2=t by omega,
        show (2*t+2)/2=t+1 by omega, show (2*t+3)/2=t+1 by omega,
        show (2*t+4)/2=t+2 by omega] <;> ring

private theorem monotone_cut (b : Bool) : Monotone (cut b) :=
  monotone_nat_of_le_succ (fun r => by rw [cut_step]; omega)

private theorem locate (b : Bool) (q : ℕ) (hq : 0 < q) :
    ∃! r, cut b r < q ∧ q ≤ cut b (r+1) := by
  have exists_end : ∃ r, q ≤ cut b (r+1) := by
    refine ⟨2*q+1, ?_⟩
    cases b <;> simp only [cut, Bool.false_eq_true, if_false, if_true, Nat.add_assoc, one_add_one_eq_two] <;>
      simp only [show (2*q+2)/2=q+1 by omega, show (2*q+3)/2=q+1 by omega,
        show (2*q+4)/2=q+2 by omega] <;> nlinarith
  let r := Nat.find exists_end
  have he : q ≤ cut b (r+1) := Nat.find_spec exists_end
  have hs : cut b r < q := by
    cases h : r with
    | zero => simpa [zero_cut] using hq
    | succ k =>
      have hl : k < Nat.find exists_end := by change k < r; omega
      exact Nat.lt_of_not_ge (Nat.find_min exists_end hl)
  refine ⟨r, ⟨hs,he⟩, ?_⟩
  intro j hj
  rcases lt_trichotomy j r with h | h | h
  · have := monotone_cut b (show j+1 ≤ r by omega)
    omega
  · exact h
  · have := monotone_cut b (show r+1 ≤ j by omega)
    omega

private theorem row_formula (r k : ℕ) (hk : 1 ≤ k ∧ k ≤ r+1) :
    entry ⟨(r+1,k),hk⟩ =
       if k%2 = 0 then 2*(cut false r : ℤ) + k else 2*(cut true (r+1) : ℤ) - k := by
  obtain ⟨t, ht | ht⟩ : ∃ t, r=2*t ∨ r=2*t+1 := ⟨r/2, by omega⟩
  · subst r
    have hs : (2*t+1)%2 ≠ 0 := by omega
    have A : (2*((2*(t:ℤ)+1)^2) + 4*(2*t+1) + 1 - (-1))/4 = 2*(t+1)^2 := by
      rw [show 2*((2*(t:ℤ)+1)^2) + 4*(2*t+1) + 1 - (-1) = (2*(t+1)^2)*4 by ring]
      omega
    by_cases h : k%2=0 <;>
      simp only [entry, paritySign, hs, h, if_true, if_false, cut, Bool.false_eq_true,
        Nat.add_assoc, one_add_one_eq_two, show 2*t/2=t by omega,
        show (2*t+1)/2=t by omega, show (2*t+2)/2=t+1 by omega, show (2*t+3)/2=t+1 by omega] <;>
      push_cast <;> rw [A] <;> ring
  · subst r
    have hs : (2*t+1+1)%2 = 0 := by omega
    have A : (2*((2*(t:ℤ)+1+1)^2) + 4*(2*t+1+1) + 1 - 1)/4 = 2*(t+1)*(t+2) := by
      rw [show 2*((2*(t:ℤ)+1+1)^2) + 4*(2*t+1+1) + 1 - 1 = (2*(t+1)*(t+2))*4 by ring]
      omega
    by_cases h : k%2=0 <;>
      simp only [entry, paritySign, hs, h, if_true, if_false, cut, Bool.false_eq_true,
        show (2*t+1)/2=t by omega, show (2*t+1+1)/2=t+1 by omega,
        show (2*t+1+1+1)/2=t+1 by omega, show (2*t+1+1+2)/2=t+2 by omega] <;>
      push_cast <;> rw [A] <;> ring

private theorem position_rank (r k : ℕ) (hk : 1 ≤ k ∧ k ≤ r+1) :
    (k%2=0 →
      cut false r < cut false r + k/2 ∧
      cut false r + k/2 ≤ cut false (r+1) ∧
      entry ⟨(r+1,k),hk⟩ = 2*((cut false r + k/2 : ℕ) : ℤ)) ∧
    (k%2≠0 →
      cut true r < cut true (r+1) - k/2 ∧
      cut true (r+1) - k/2 ≤ cut true (r+1) ∧
      entry ⟨(r+1,k),hk⟩ = 2*((cut true (r+1) - k/2 : ℕ) : ℤ)-1) := by
  have he := cut_step false r
  have ho := cut_step true r
  simp only [Bool.false_eq_true, if_false, if_true] at he ho
  constructor <;> intro h <;> rw [row_formula] <;> simp [h] <;> omega

private theorem positive_entry (p : Cell) : 0 < entry p := by
  obtain ⟨⟨n,k⟩,hk⟩ := p
  cases n with
  | zero => simp at hk; omega
  | succ r =>
    have hr := position_rank r k hk
    by_cases h : k%2=0
    · have := hr.1 h; omega
    · have := hr.2 h; omega

private theorem unique_row (b : Bool) {r s q : ℕ} (hq : 0<q)
    (hr : cut b r < q ∧ q ≤ cut b (r+1))
    (hs : cut b s < q ∧ q ≤ cut b (s+1)) : r=s := by
  obtain ⟨j, _, unique⟩ := locate b q hq
  exact (unique r hr).trans (unique s hs).symm

private theorem injective_entry : Function.Injective entry := by
  rintro ⟨⟨n,k⟩,hk⟩ ⟨⟨m,l⟩,hl⟩ hv
  cases n with
  | zero => simp at hk; omega
  | succ r =>
    cases m with
    | zero => simp at hl; omega
    | succ s =>
      have hr := position_rank r k hk
      have hs := position_rank s l hl
      by_cases bk : k%2=0 <;> by_cases bl : l%2=0
      · obtain ⟨hr₁,hr₂,hr₃⟩ := hr.1 bk
        obtain ⟨hs₁,hs₂,hs₃⟩ := hs.1 bl
        have eq : cut false r+k/2 = cut false s+l/2 := by omega
        have hrs : r = s := unique_row false (r:=r) (s:=s) (by omega : 0<cut false r+k/2) ⟨hr₁,hr₂⟩ (by omega)
        subst s
        have : k=l := by omega
        subst l; rfl
      · have := hr.1 bk; have := hs.2 bl; omega
      · have := hr.2 bk; have := hs.1 bl; omega
      · obtain ⟨hr₁,hr₂,hr₃⟩ := hr.2 bk
        obtain ⟨hs₁,hs₂,hs₃⟩ := hs.2 bl
        have eq : cut true (r+1)-k/2 = cut true (s+1)-l/2 := by omega
        have hrs : r = s := unique_row true (r:=r) (s:=s) (by omega : 0<cut true (r+1)-k/2) ⟨hr₁,hr₂⟩ (by omega)
        subst s
        have : k=l := by omega
        subst l; rfl

private theorem onto_positive (u : ℤ) (hu : 0 < u) : ∃ p, entry p = u := by
  lift u to ℕ using (by omega : 0 ≤ u)
  by_cases ht : u%2=0
  · let q := u/2
    have hq : 0 < q := by dsimp [q]; omega
    obtain ⟨r, ⟨h1,h2⟩, _⟩ := locate false q hq
    have hs := cut_step false r
    simp only [Bool.false_eq_true, if_false] at hs
    let k := 2*(q - cut false r)
    have hk : 1 ≤ k ∧ k ≤ r+1 := by dsimp [k]; omega
    refine ⟨⟨(r+1,k),hk⟩, ?_⟩
    have H := (position_rank r k hk).1 (show k%2=0 by dsimp [k]; omega)
    dsimp [k,q] at *
    omega
  · let q := u/2+1
    have hq : 0 < q := by dsimp [q]; omega
    obtain ⟨r, ⟨h1,h2⟩, _⟩ := locate true q hq
    have hs := cut_step true r
    simp only [if_true] at hs
    let k := 2*(cut true (r+1)-q)+1
    have hk : 1 ≤ k ∧ k ≤ r+1 := by dsimp [k]; omega
    refine ⟨⟨(r+1,k),hk⟩, ?_⟩
    have H := (position_rank r k hk).2 (show k%2≠0 by dsimp [k]; omega)
    dsimp [k,q] at *
    omega

end SchulteTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a376182.main := by
  refine ⟨SchulteTriangle.positive_entry, ?_⟩
  intro u hu
  obtain ⟨p, hp⟩ := SchulteTriangle.onto_positive u hu
  exact ⟨p, hp, fun t ht => SchulteTriangle.injective_entry (ht.trans hp.symm)⟩
