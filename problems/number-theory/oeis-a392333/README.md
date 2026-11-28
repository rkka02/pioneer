# Almost primes in square products of factorials

For each fixed k ≥ 2, almost every integer n with k prime factors has the following property. The shortest product of distinct factorials ending in n! that is a perfect square has exactly six factors. Prime factors are counted with multiplicity. “Almost every” means the proportion tends to one as the upper cutoff increases. In particular this proves the 1976 Erdős–Graham conjecture on semiprimes recorded in A389148. The manuscript combines Yudin’s Corollary 6.2 with a uniform estimate for small prime divisors of n−1 averaged over almost primes. [Erdős–Graham, p. 353](https://combinatorica.hu/~p_erdos/1976-25.pdf) · [OEIS A389148](https://oeis.org/A389148) · [Yudin](https://arxiv.org/html/2610.01899v1)

The first member of A392333 with at least four prime factors, counted with multiplicity, is **435643 = 13 · 23 · 31 · 47**. Five factorials suffice for all 193,915 earlier endpoints with that many prime factors. At 435643 the minimum is six. This determines a finite extremum in the Erdős–Graham set D₆. Fedir Yudin determined the order of growth of the counting function of D₆ and proved positive lower density. Whether D₆ has a limiting natural density remains open. [Yudin, Theorem 1.2 and Section 8](https://arxiv.org/html/2610.01899v1)

[Paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [OEIS question](https://oeis.org/A392333) · [Erdős Problem 374](https://www.erdosproblems.com/374)

Both C++17 programs use integer arithmetic and verify every positive search witness using all relevant prime valuations. The first tracks the first 64 prime coordinates directly. The second constructs a different deterministic projection by sieving. Exact matches are checked by Legendre’s formula. The figure can be regenerated with `python3 plot.py` and Matplotlib. The stored table gives the 109 earlier endpoints outside the elementary identities.

~~~sh
c++ -std=c++17 -O3 verify.cpp -o /tmp/pioneer-a392333-verify
/tmp/pioneer-a392333-verify > /tmp/pioneer-a392333-witnesses.csv
diff witnesses.csv /tmp/pioneer-a392333-witnesses.csv
c++ -std=c++17 -O3 search.cpp -o /tmp/pioneer-a392333-search
/tmp/pioneer-a392333-search > /tmp/pioneer-a392333-search.csv
~~~

[Lean coverage lemmas](Coverage.lean) certify the prime-valuation restrictions used to prune the search and the six-factorial square at 435643. The numerical enumeration is certified by the two C++ programs. [Adjacent-factorial reduction](AdjacentReduction.lean) verifies both directions of the local square and divisibility equivalences used in the density proof. The analytic estimates are proved in the manuscript. In a Mathlib checkout using Lean 4.33.1, run `lake env lean /absolute/path/to/Coverage.lean`.

## Public record

[Semiprime conjecture and complete manuscript](https://github.com/lefttosolve2/open-math-agents/pull/25919) · [Finite endpoint submission and independent checker](https://github.com/lefttosolve2/open-math-agents/issues/25442)
