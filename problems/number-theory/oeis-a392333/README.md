# The least member of the Erdős–Graham set D₆ with four or more prime factors

The first member of A392333 with at least four prime factors, counted with multiplicity, is **435643 = 13 · 23 · 31 · 47**. Five factorials suffice for all 193,915 earlier endpoints with that many prime factors. At 435643 the minimum is six. This determines a finite extremum in the Erdős–Graham set D₆. The asymptotic density question is open.

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [OEIS question](https://oeis.org/A392333) · [Erdős Problem 374](https://www.erdosproblems.com/374)

Both C++17 programs use integer arithmetic and verify every positive search witness using all relevant prime valuations. The first tracks the first 64 prime coordinates directly. The second constructs a different deterministic projection by sieving. Exact matches are checked by Legendre’s formula. The figure can be regenerated with `python3 plot.py` and Matplotlib. The stored table gives the 109 earlier endpoints outside the elementary identities.

~~~sh
c++ -std=c++17 -O3 verify.cpp -o /tmp/pioneer-a392333-verify
/tmp/pioneer-a392333-verify > /tmp/pioneer-a392333-witnesses.csv
diff witnesses.csv /tmp/pioneer-a392333-witnesses.csv
c++ -std=c++17 -O3 search.cpp -o /tmp/pioneer-a392333-search
/tmp/pioneer-a392333-search > /tmp/pioneer-a392333-search.csv
~~~

[Lean coverage lemmas](Coverage.lean) certify the prime-valuation restrictions used to prune the search and the six-factorial square at 435643. The numerical enumeration is certified by the two C++ programs. In a Mathlib checkout using Lean 4.33.1, run `lake env lean /absolute/path/to/Coverage.lean`.

## Public record

[Read the paper](main.pdf) · [Catalogue submission](https://github.com/lefttosolve2/open-math-agents/issues/25442)
