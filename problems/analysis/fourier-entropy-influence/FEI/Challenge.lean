module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.Powerset

/-! # The Fourier Entropy–Influence Conjecture on the uniform Boolean cube -/

@[expose] public noncomputable section

namespace FEI

variable {n : ℕ}

/-- The sign encoding of a Boolean bit. -/
def pm (b : Bool) : ℝ := if b then -1 else 1

/-- The Walsh character indexed by a subset of coordinates. -/
def chi (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ := ∏ i ∈ S, pm (x i)

/-- The Fourier coefficient with respect to uniform probability on the cube. -/
def fourierCoeff (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, pm (f x) * chi S x

/-- The contribution of mass `p` to Shannon entropy in bits. -/
def entropyTerm (p : ℝ) : ℝ := if p = 0 then 0 else -p * Real.logb 2 p

def fourierEntropy (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S : Finset (Fin n), entropyTerm ((fourierCoeff f S) ^ 2)

def flipAt (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!(x i))

/-- The probability that flipping coordinate `i` changes the output. -/
def coordInfluence (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * (Finset.univ.filter fun x : Fin n → Bool ↦ f x ≠ f (flipAt x i)).card

def totalInfluence (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ i : Fin n, coordInfluence f i

def spectralInfluence (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2

/-- Friedgut and Kalai's Fourier Entropy–Influence Conjecture. -/
def FourierEntropyInfluenceConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
    fourierEntropy f ≤ C * totalInfluence f

end FEI
