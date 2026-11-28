# A weighted count of partitions into four parts

Parametrizes four-part partitions by their gaps and proves both the recurrence and the generating function.

Run `python3 verify.py` to reproduce the exact initial values.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof PR](https://github.com/lefttosolve2/open-math-agents/pull/25084)

The proof was checked against the [frozen statement](https://github.com/lefttosolve2/open-math-agents/blob/88838da7f212f235c6426e67244c02a1e958cb5b/statements/oeis-a308758.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `6cd455af42c1711737aad1255a269a749278330031898e34819dde5b4811ad2f`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a308758 /path/to/open-math-agents
```
