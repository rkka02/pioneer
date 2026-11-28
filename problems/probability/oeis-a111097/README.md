# The maximum-likelihood urn size at the first repeated draw

Locates the unique integer maximizer for every sample size and proves the second differences and generating function.

Run `python3 verify.py` to reproduce the exact initial values.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof PR](https://github.com/lefttosolve2/open-math-agents/pull/25391)

The proof was checked against the [frozen statement](https://github.com/lefttosolve2/open-math-agents/blob/88838da7f212f235c6426e67244c02a1e958cb5b/statements/oeis-a111097.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `7c7fdaccb9b05745015aa26fc073f968175ae986218c2c6bfa3b2294e1fb06ae`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a111097 /path/to/open-math-agents
```
