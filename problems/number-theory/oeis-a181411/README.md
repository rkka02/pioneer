# A binomial mean of the sum of divisors

Proves the conjectured limit π²/4 for the normalized binomial divisor sum. The paper supplies an explicit smoothing bound.

Run `python3 verify.py` to reproduce the exact initial values.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof attached to statement review](https://github.com/lefttosolve2/open-math-agents/pull/24831)

The proof was checked against the [frozen statement](https://github.com/rkka02/open-math-agents/blob/1dc4a8086fb6dcc809f3a29d5732713328c18a33/statements/oeis-a181411.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `717b81aa1ad3cded61a9e051ef852cdbc2dc895077c596bb2ef51c4fcfa88af7`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a181411 /path/to/open-math-agents
```
