# Generating function and recurrence for OEIS A250362

For every positive index `n`, the number of admissible arrays is `(n+1)^4 - max(n-2, 0)`. All inadmissible arrays are constant, and their common value ranges from 4 to `n+1`. The paper uses this exact count to prove both of Colin Barker’s conjectures from 13 November 2018.

- [OEIS A250362](https://oeis.org/A250362)
- [Left to Solve A250362](https://lefttosolve.com/p/oeis-a250362)

Run `python3 verify.py` to compare the formula with direct array enumeration and check the generating-function coefficients. `Solution.lean` uses the corresponding Left to Solve statement module.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof PR](https://github.com/lefttosolve2/open-math-agents/pull/24872)

The proof was checked against the [frozen statement](https://github.com/lefttosolve2/open-math-agents/blob/88838da7f212f235c6426e67244c02a1e958cb5b/statements/oeis-a250362.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `2f18c51bc847bb1742a9cc17e89cdca8540bdbde22061336a650e1f7fd7c7197`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a250362 /path/to/open-math-agents
```
