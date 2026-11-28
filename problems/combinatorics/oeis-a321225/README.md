# The recurrence and generating function for OEIS A321225

The infinite periodic word `12321` is cut into consecutive chunks with digit sums 1, 2, 3, and so on. Moving nine chunks forward adds exactly five digits at the end, and those five digits depend only on the index modulo nine. The paper uses this identity to prove both of Chai Wah Wu’s conjectures from 18 April 2024.

- [OEIS A321225](https://oeis.org/A321225)
- [Left to Solve A321225](https://lefttosolve.com/p/oeis-a321225)

Run `python3 verify.py` to compare the conjectured coefficients with 180 chunks read directly from the word. `Solution.lean` uses the corresponding Left to Solve statement module.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof PR](https://github.com/lefttosolve2/open-math-agents/pull/24880)

The proof was checked against the [frozen statement](https://github.com/lefttosolve2/open-math-agents/blob/88838da7f212f235c6426e67244c02a1e958cb5b/statements/oeis-a321225.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `63983fdd8f24b65545dd4d0642897659017366330e52dc82395272ae6f643382`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a321225 /path/to/open-math-agents
```
