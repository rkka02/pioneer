# OEIS A401548

The manuscript proves the counting asymptotic for integers whose greedy sum of positive squares uses the fewest squares. The leading constant is (16/525) times 2^(17/8). Among inputs with four greedy steps, the limiting proportion requiring four squares is 3/20.

The Python verifier computes the congruence proportions exactly. It also compares a tuple enumeration with the direct greedy algorithm and with the published OEIS counts through one million.

`StructuralLemmas.lean` proves the bijection between inputs and admissible greedy root lists and the uniform 2-adic divisibility bound on four-square tuples. The full asymptotic proof is in the manuscript. To check the two lemmas, run `lake env lean` on the file from a Lean 4.33.1 project with Mathlib.

    python3 verify.py
    tectonic main.tex

[Original OEIS entry](https://oeis.org/A401548)

## Public record

[Read the paper](main.pdf) · [Statement review with complete manuscript](https://github.com/lefttosolve2/open-math-agents/pull/25333)
