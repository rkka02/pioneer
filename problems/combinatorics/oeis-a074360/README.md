# The cubic-coefficient generating function for OEIS A074360

The coefficient sequences of degrees zero through three in the defining `q`-polynomials satisfy a triangular system of generating-function equations. Solving it gives exactly R. J. Mathar’s rational generating function conjectured on 22 July 2009.

- [OEIS A074360](https://oeis.org/A074360)
- [Left to Solve A074360](https://lefttosolve.com/p/oeis-a074360)

Run `python3 verify.py` to compare the generating-function identity with 81 terms computed from the defining polynomial recurrence. `Solution.lean` uses the corresponding Left to Solve statement module.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof PR](https://github.com/lefttosolve2/open-math-agents/pull/24885)

The proof was checked against the [frozen statement](https://github.com/lefttosolve2/open-math-agents/blob/88838da7f212f235c6426e67244c02a1e958cb5b/statements/oeis-a074360.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `2369578992415bd9530bd8e1cc287afe747a85185855740d812479cb50df83f5`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a074360 /path/to/open-math-agents
```
