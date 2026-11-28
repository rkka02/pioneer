# OEIS A097154

The manuscript proves the fixed-point conjecture from the OEIS entry. For any base at least three, the unique positive fixed point has digits b−2 and b−1. The sharp reversal gap at each digit length gives a uniform proof. The decimal fixed points are 0 and 89.

The Python verifier exhaustively checks the gap formula, its equality cases, and the fixed points for bases 2 through 12 and digit lengths up to 5.

    python3 verify.py
    tectonic main.tex

[Original OEIS entry](https://oeis.org/A097154)

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof attached to statement review](https://github.com/lefttosolve2/open-math-agents/pull/5188#issuecomment-7237354412)

The proof was checked against the [frozen statement](https://github.com/rkka02/open-math-agents/blob/a524e3feb8a20564312c2cef4e6eb38951f16d17/statements/oeis-a097154.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `fd36544af9bdf206740fd9f21fca7d0aa04b2330167ad425f415554a2cd36d1a`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a097154 /path/to/open-math-agents
```
