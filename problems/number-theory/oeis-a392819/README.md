# Natural density of OEIS A392819

The set of positive integers in A392819 has natural density zero. The proof bounds the contribution from integers with a large prime factor by counting multiples of two explicit moduli. A separate estimate bounds integers whose prime factors are all small.

The paper also gives the odd term `5625 = 3² · 5⁴` and proves that every odd term is a square.

- [OEIS A392819](https://oeis.org/A392819)
- [OEIS A393351](https://oeis.org/A393351)
- [Left to Solve A392819](https://lefttosolve.com/p/oeis-a392819)


Run `python3 verify.py` to reproduce the four sample counts and check the odd term.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof attached to statement review](https://github.com/lefttosolve2/open-math-agents/pull/25657)

The proof was checked against the [frozen statement](https://github.com/rkka02/open-math-agents/blob/50b28b6b2a301cd69ae9fe8d72ae0e335fcdc363/statements/oeis-a392819.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `4eac9ef877d9a6c3a75406d193e4c58aec84efbe36e0911cfbf3695af545bc6f`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a392819 /path/to/open-math-agents
```
