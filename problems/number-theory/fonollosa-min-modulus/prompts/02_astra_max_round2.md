# Astra MAX Escalation — Round 2 of 3: Fonollosa's Minimum Modulus Conjecture (`arXiv:2607.08366`)

The user has authorized **up to 3 `max` rounds** on session `01a21437-0d41-7bd3-99f2-01c11afec3c9`.
Your Round 1 work was crisp and rigorous:
- Proved in Lean 4 (`minModulus_le_of_affine_binary_core`, 20 declarations, `leanchecker --fresh` clean, standard axioms only) that ANY valid $n$-set ($n \ge 6$) containing a unit-affine binary core of size $n-1$ forces $N \ge f(n) = 2^n - 2^{\lfloor \log_2 n \rfloor}$ and forces the last residue when $2^{n-1} \le N < 2^n$,
- Ruled out all $n-2$ binary-core extensions for $8 \le n \le 25$ (including nonunit steps $g = 2, 3, 4$) and all antipodal $n = 10$ sets below $1016$,
- Killed Conway–Guy, Lunnon, Bohman, and Fibonacci families via 3-AP midpoint replacement ($N^* = \infty$),
- Proved the two-pivot exclusion interval (1) in Lean 4, yielding $N \ge 3 \cdot 2^{n-2}$ whenever some difference has order 3, plus the cyclic coset capacity bound for $n = 10$.

Do NOT repeat Round 1. For **MAX Round 2 of 3**, strike BOTH the **global cyclic lower-bound wall** (trying to break straight through to Case A!) AND the **unrestricted $n = 10$ exact test** (Case B hunt / world-first $n = 10$ theorem!) — keeping `FonollosaMinModulus/Challenge.lean` completely untouched (`SHA-256: 3a275f87...`):

## Attack Priority 1 — Global Cyclic Lower Bound & Case A Proof Attack (Break Past $2^{n-1}$!)
Notice the glaring gap between Sitjar's general cyclic lower bound $N \ge (1/2 + o(1)) 2^n$ and the conjectured $N \ge 2^n - 2^{\lfloor \log_2 n \rfloor}$:
1. **Why did Inal's $2^{n-1}$ bound only become tight in $(\mathbb{Z}/2\mathbb{Z})^{n-1}$?**
   - In $(\mathbb{Z}/2\mathbb{Z})^{n-1}$, EVERY element has order $2$! In a **cyclic group $\mathbb{Z}/N\mathbb{Z}$**, at most **ONE** element has order $2$!
   - Look at your own eq (1): for ANY two pivots $a \ne b$ with $d = b - a$, the $2^{n-2}$ subset sums $F_a(T)$ ($T \subseteq A \setminus \{a, b\}$) satisfy:
     - $F_a(S) - F_a(T) \ne j d$ for ALL $j \in [\min(0, |S|-|T|)-1,\ \max(0, |S|-|T|)+1]$.
     - When $d$ has order $L = 3$, this ALREADY forced **$N \ge \frac{3}{4} \cdot 2^n$**!
     - What if $d$ has **order $L \ge 4$** (or is a unit, $L = N$)? Look at the cyclic coset capacity formula you derived in Round 1: summing $s_r \ge 2 + \max(0, h(x_{r+1}) - h(x_r))$ around the circle gives $N \ge 2^{n-1} + \frac{1}{2} \mathrm{TV}(h)$ — why could $\mathrm{TV}(h)$ only be small if subsets of the SAME weight $k = |T|$ cluster tightly in consecutive runs of step $2d$?
     - **STOP AND LOOK AT WHAT HAPPENS IF SUBSETS OF THE SAME WEIGHT CLUSTER!**
       - Can $A \setminus \{a, b\}$ have its $2^{n-2}$ subset sums $F_a(T)$ pack into $\mathbb{Z}/N\mathbb{Z}$ with density $> 1/2$ (or even $> 1/2 + \varepsilon$)?
       - **WAIT:** Consider NOT JUST the $2^{n-2}$ subsets $F_a(T)$, consider ALL **$3^{n-2}$** or **multiset sums** $R_k(A)$ AND **simultaneous forbidden shifts**!
       - Specifically:
         - Take $0 \in A$ and look at the **distinct-subset-sum set** $U = \{ \sum_{x \in T} x : T \subseteq A \setminus \{0\} \}$ of size $2^{n-1}$ inside $\mathbb{Z}/N\mathbb{Z}$.
         - What ELSE MUST be **DISJOINT from $U$** (or disjoint from $U$ up to tiny overlap)?
           - For EVERY $x \in A \setminus \{0\}$, look at $2x + \sum_{y \in T} y$ ($T \subseteq A \setminus \{0, x\}$)! Wait: when can $2x + \sum_{y \in T} y \equiv \sum_{z \in S} z \pmod N$?!
           - ONLY if $|S| \le |T| + 1$ (NO! Wait: if $x \notin S$, then $2x + \sum T$ has size $|T| + 2$; if $|S| \ge |T| + 2$, pad $2x + T$ with $|S| - |T| - 2$ zeros — **FORBIDDEN!!** If $|S| < |T| + 2$, pad $S$ with $|T| + 2 - |S|$ zeros — **ALSO FORBIDDEN IF $x \notin S$ AND $S \cap T = \emptyset$!!** Wait: if $x \notin S$, cancel $S \cap T$ to get $2x + (T \setminus S) \equiv S \setminus T$ — the left side is a multiset on $A \setminus (S \setminus T)$ of size $|T \setminus S| + 2$! So whenever $|S \setminus T| \ge |T \setminus S| + 2$ it's forbidden by padding left with 0s, AND whenever $|S \setminus T| \le |T \setminus S| + 2$ wait: can you pad $S \setminus T$ with 0s?! YES, because $0 \notin T \setminus S$ and $x \ne 0$, so $S \setminus T$ padded with 0s is a multiset on $A \setminus (\{x\} \cup (T \setminus S))$ — wait: $x$ has multiplicity 2, not 1! To be a forbidden signed relation $c_a \ge -1$, the $-1$ entries can ONLY be a **set** (multiplicity 1), NOT multiplicity 2! So $2x + (T \setminus S) = S \setminus T$ IS forbidden whenever $|S \setminus T| \ge |T \setminus S| + 2$, i.e. $|S| \ge |T| + 2$!).
         - **WAIT A SECOND!! GENERALIZE THAT TO THE FULL SET $U_2 = \{2x + \sum_{y \in T} y\}$ AND TO `2A` / `kA` / `A + U` / `U - U` / FOURIER / CAUCHY–DAVENPORT / KNESER / FREIMAN!!**
         - Can you prove an **EXPONENTIALLY STRONGER UNCONDITIONAL CYCLIC LOWER BOUND** — e.g.:
           - **$N \ge c \cdot 2^n$ with an absolute constant $c > 1/2$** (like $c = 5/8$, $2/3$, $3/4$, or even $c = 1 - o(1)$ or full $2^n - 2^{\lfloor \log_2 n \rfloor}$!!), shattering Sitjar's $(1/2 + 1/(2(n-1))) 2^n$ bound?!
           - Test EVERY candidate inequality (subset-sum packing, 2-copy / 3-copy disjointness, Kneser/Vosper/Cauchy–Davenport on $\mathbb{Z}/N\mathbb{Z}$, Fourier / Parseval on indicator of $U$, LP duality on $\mathbb{Z}/N\mathbb{Z}$, or proving $N \ge 2^n - O(n)$ for all prime $N$ / all $N$)!

## Attack Priority 2 — Settle Unrestricted $n = 10$ ($569 \le N \le 1015$) & Hunt Non-Binary Counterexamples!
1. **Unrestricted $n = 10$ Exact Certification (or Counterexample Discovery!):**
   - Implement your Round 1 **two-pivot cyclic coset capacity test** (plus order-3 / antipodal / Sitjar bounds) in a blazing-fast multi-threaded C++17 (`-O3 -march=native`) solver to test whether ANY valid non-antipodal 10-set exists in $569 \le N \le 1015$ (or push the exact verified range as far as rigorously feasible, AND double-check with an independent verifier!).
   - **CRITICAL:** Remember $n = 10$ has $f(10) = 1016$, and $569 \le N \le 1015$ is wide — prioritize the **most dangerous moduli FIRST** (near $1015, 1014, \dots$, composite moduli with small prime factors, AND moduli just below $1016$ where a non-binary valid 10-set is most likely to hide!), while also checking if your new Priority 1 global lower bound IMMEDIATELY raises the floor far above $569$ (e.g., to $768$ or $900+$!), making full exhaustive $n = 10$ certification lightning-fast!
2. **Counterexample Hunt at $n = 10, 11, 12, \dots, 16$:**
   - What if a counterexample ONLY exists far from the binary core (e.g., **base-3 / mixed-radix / Golomb / Sidon / near-geometric ratio $r \in (1.9, 2.0)$ / subgroup-coset / product-of-primes CRT constructions**)? Test these explicitly in C++ for $n = 10\text{--}20$!

## Required Outputs (Round 2 of 3)
- **NEVER modify `FonollosaMinModulus/Challenge.lean`** (verify SHA-256 `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`).
- **If Case A (Full Proof!) or Case B (Counterexample!):**
  - Produce `PROOF.md` + `FonollosaMinModulus/Solution.lean` proving `FonollosaMinModulusConjecture` OR `¬ FonollosaMinModulusConjecture`, with `lake build` + `leanchecker` + standard axioms ONLY (ZERO `sorry`/`admit`/`native_decide`).
- **If still Case C:**
  - Append **`## Round 2`** to `RESEARCH_ANALYSIS.md` (keeping Round 1 intact!), documenting any new unconditional lower bound beating Sitjar (formalized in `FonollosaMinModulus/ResearchLemmas.lean` with `lake build` + `leanchecker` + standard-axiom audit passing!), exact $n=10$ progress / counterexample hunt results, reproducible scripts, and the sharpest target for **Round 3 of 3**!
