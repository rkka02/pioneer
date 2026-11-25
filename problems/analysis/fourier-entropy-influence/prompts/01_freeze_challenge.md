# Task: Formalize and Freeze `FEI/Challenge.lean` (Fourier Entropy–Influence Conjecture)

You are formalizing the canonical, unweakened statement of the **Fourier Entropy–Influence (FEI) Conjecture** (Friedgut & Kalai, 1996) in Lean 4 (`v4.36.0` + Mathlib) inside `/Users/mw/Desktop/math/pioneer/fei`.

## Requirements for `FEI/Challenge.lean`

1. **Full, Unweakened Statement (Boolean Functions on `{-1, 1}^n`)**
   - Work cleanly over `n : ℕ` and Boolean inputs `x : Fin n → Bool`, with Boolean-valued functions represented cleanly either as `f : (Fin n → Bool) → Bool` mapped to `{-1, 1} ⊂ ℝ` via `pm (b : Bool) : ℝ := if b then -1 else 1` (or `1` / `-1`, consistently!). Using `f : (Fin n → Bool) → Bool` makes the domain & codomain manifestly finite, exact, and impossible to cheat with non-Boolean functions!
   - Define the Walsh–Fourier character:
     `chi (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ := ∏ i ∈ S, pm (x i)`
   - Define the Fourier coefficient:
     `fourierCoeff (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ := (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, pm (f x) * chi S x`
   - Define the Shannon entropy term `entropyTerm (p : ℝ) : ℝ := if p = 0 then 0 else -p * Real.logb 2 p` (note: using `Real.logb 2` gives entropy in bits; `Real.log` differs only by `Real.log 2 > 0`, so universal constant existence is identical).
   - Define **Fourier Entropy**:
     `fourierEntropy (f : (Fin n → Bool) → Bool) : ℝ := ∑ S : Finset (Fin n), entropyTerm ((fourierCoeff f S) ^ 2)`
   - Define **Coordinate Influence** (combinatorial definition!) and **Total Influence**:
     - `flipAt (x : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update x i (!x i)`
     - `coordInfluence (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ := (1 / (2 : ℝ) ^ n) * (Finset.univ.filter (fun x : Fin n → Bool => f x ≠ f (flipAt x i))).card`
     - `totalInfluence (f : (Fin n → Bool) → Bool) : ℝ := ∑ i : Fin n, coordInfluence f i`
     - Also define the spectral form `spectralInfluence (f : (Fin n → Bool) → Bool) : ℝ := ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff f S) ^ 2`.
   - State the canonical **Fourier Entropy–Influence Conjecture**:
     ```lean
     def FourierEntropyInfluenceConjecture : Prop :=
       ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
         fourierEntropy f ≤ C * totalInfluence f
     ```
   - Zero `sorry`, zero custom axioms, clean compilation via `lake build FEI.Challenge`.

2. **Mandatory Non-Vacuity & Exact Normalization Sanity Checks (`FEI/ChallengeSanity.lean`)**
   - Create `FEI/ChallengeSanity.lean` importing `FEI.Challenge`, and prove (with **ZERO `sorry`**):
     1. **Parseval's Identity** (`∑ S, (fourierCoeff f S)^2 = 1`) — proves the $2^{-n}$ normalization and character orthogonality are 100% exact!
     2. **Spectral Influence = Combinatorial Total Influence** (`totalInfluence f = spectralInfluence f`) — proves both standard definitions agree identically!
     3. **Concrete Witness (`AND₂` on `n = 2`)**: for `and2 : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1`, prove `fourierEntropy and2 = 2` and `totalInfluence and2 = 1` (hence any witness `C` in `FourierEntropyInfluenceConjecture` must satisfy `2 ≤ C`!). This guarantees `fourierEntropy` is non-zero, `logb 2` sign is positive (not negated!), and the statement is completely non-vacuous.
     4. **Constant function check**: for `constFalse : (Fin n → Bool) → Bool := fun _ => false`, prove `fourierEntropy constFalse = 0` and `totalInfluence constFalse = 0`.

3. **Verification**
   - Run `lake build` and confirm **zero errors, zero `sorry`, zero extra axioms**.
   - Keep `FEI/Challenge.lean` minimal, crystal clear, and ready to be frozen read-only.
