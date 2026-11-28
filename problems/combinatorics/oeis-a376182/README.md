# OEIS A376182

The manuscript proves Schulte's permutation conjecture. A parity decomposition gives consecutive blocks of the odd and even integers, an inverse using one integer square root, and the exact displacement from each element's row-major index.

The Python verifier compares the inverse and displacement directly with the OEIS formula.

    python3 verify.py
    tectonic main.tex

[Original OEIS entry](https://oeis.org/A376182)

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof attached to statement review](https://github.com/lefttosolve2/open-math-agents/pull/25014)

The proof was checked against the [frozen statement](https://github.com/rkka02/open-math-agents/blob/d7284aa2e8500309448f18b226204f2e24c6b020/statements/oeis-a376182.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `2079c58134b823a06870109031e95c5e1f87fbfeb073667b93da65e019403ed5`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a376182 /path/to/open-math-agents
```
