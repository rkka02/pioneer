import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fonollosa's Minimum Modulus Conjecture (Frozen Challenge Statement)

Reference:
- José A. R. Fonollosa,
  *Minimum modulus for the unique multiset-sum problem*,
  arXiv:2607.08366 (July 2026), Conjecture 1.
- Upstream formalization: `google-deepmind/formal-conjectures`
  (`FormalConjectures/Arxiv/2607.08366/MinModulus.lean`).

Statement: Call `A : Finset (ZMod N)` valid mod `N` when the all-ones multiset is the
only multiset of size `A.card` drawn from `A` whose sum matches `∑ a ∈ A, a`.
Conjecture 1 asserts that for every `n ≥ 2` and every `0 < N < 2^n - 2^(⌊log₂ n⌋)`,
no set of `n` residues mod `N` is valid.

THIS FILE IS FROZEN AND READ-ONLY. DO NOT MODIFY.
-/

namespace FonollosaMinModulus

open Finset

variable {N : ℕ}

/-- `A` is *valid mod* `N` when the all-ones multiset is the only multiset of size `A.card`
drawn from `A` whose sum matches `∑ a ∈ A, a`. -/
def IsValidMod (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = A.card →
    ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a →
    ∀ a ∈ A, m a = 1

/-- The candidate least modulus admitting a valid set of `n` residues:
`2^n - 2^(⌊log₂ n⌋)`. -/
def minModulus (n : ℕ) : ℕ := 2 ^ n - 2 ^ (Nat.log 2 n)

/-- **Fonollosa's Minimum Modulus Conjecture (arXiv:2607.08366, Conjecture 1):**
For every `n ≥ 2` and every `0 < N < 2^n - 2^(⌊log₂ n⌋)`, no set of `n` residues
mod `N` is valid. -/
def FonollosaMinModulusConjecture : Prop :=
  ∀ n N : ℕ, 2 ≤ n → 0 < N → N < minModulus n →
    ∀ A : Finset (ZMod N), A.card = n → ¬ IsValidMod A

end FonollosaMinModulus
