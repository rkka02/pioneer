# Cubic counterexamples for perfect powers and their divisor sums

The paper answers the higher-power questions in [OEIS A128607](https://oeis.org/A128607) and [A128608](https://oeis.org/A128608). It gives multiplicative certificates for both witnesses and an exact search establishing the least new input-side witness.

Build the verifier with a C compiler and GMP development headers.

```sh
cc -O2 verify.c $(pkg-config --cflags --libs gmp) -o verify
./verify
```

The verifier should report only the three rows shown in the paper.

## Manuscript and certificate

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Complete Lean proof](Solution.lean) · [Proof attached to statement review](https://github.com/lefttosolve2/open-math-agents/pull/24897)

The proof was checked against the [frozen statement](https://github.com/rkka02/open-math-agents/blob/31ba2a67e255b019b52a57dd3a58c01953453c69/statements/oeis-a128607.lean) on Lean 4.33.1 using the Left to Solve checker. SHA-256 of the statement is `ee0682fc3d971725140e40541c6053c833a0b84f996c0c0de0caac3b5e64ac88`.

From the Pioneer root, with the upstream checker set up, run

```sh
python3 scripts/check_left_to_solve.py oeis-a128607 /path/to/open-math-agents
```
