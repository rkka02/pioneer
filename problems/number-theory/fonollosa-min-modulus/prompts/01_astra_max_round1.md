# Astra MAX Attack — Round 1: Fonollosa's Minimum Modulus Conjecture (`arXiv:2607.08366`)

## Frozen Target (`FonollosaMinModulus/Challenge.lean` — READ-ONLY, NEVER MODIFY!)
**Fonollosa's Minimum Modulus Conjecture (José A. R. Fonollosa, July 2026, arXiv:2607.08366, Conjecture 1):**
Call a subset $A \subseteq \mathbb{Z}/N\mathbb{Z}$ of size $n$ **valid mod $N$** if the all-ones multiset is the ONLY multiset of size $n$ drawn from $A$ whose sum equals $\sum_{a \in A} a \pmod N$, i.e.:
$$\forall m : A \to \mathbb{N},\quad \sum_{a \in A} m(a) = n \ \wedge\ \sum_{a \in A} m(a)\,a \equiv \sum_{a \in A} a \pmod N \implies \forall a \in A,\ m(a) = 1.$$
Fonollosa proved (and formalized in Lean 4) that the super-increasing set $\{2^k - 1 : 0 \le k \le n - 1\}$ IS valid modulo
$$N_{\min}(n) = 2^n - 2^{\lfloor \log_2 n \rfloor}.$$
**Conjecture 1 (OPEN):** For every $n \ge 2$ and every $0 < N < 2^n - 2^{\lfloor \log_2 n \rfloor}$, **NO** set $A \subseteq \mathbb{Z}/N\mathbb{Z}$ of size $n$ is valid mod $N$!

*Background check:* This conjecture is only 4 months old (July 2026). Recent follow-up computational work (Sitjar, late 2026) reportedly checked $n = 8, 9$ and proved a partial lower bound — use `web_search` to inspect `arXiv:2607.08366` and Sitjar's paper so you immediately absorb all known techniques and avoid repeating them!

## Mission: Go Straight for the Kill (Case A Full Proof OR Case B Counterexample!)
You have full access to `/Users/mw/miniconda3/bin/python3` (NumPy, SciPy MILP, Numba), `clang++ -O3 -march=native`, Lean 4.36.0 (`lake build`), and `web_search`.

### Attack Strategy (Hit BOTH Sides Hard!)
1. **Immediate Structural Analysis & Equivalent Reformulations:**
   - Rewrite the condition in terms of **signed zero-sum relations** $c_a = m(a) - 1 \in \{-1, 0, 1, 2, \dots\}$ with $\sum_{a \in A} c_a = 0$ and $\sum_{a \in A} c_a a \equiv 0 \pmod N$!
   - **WHOA — LOOK AT THAT EQUIVALENCE:**
     - Split $c_a$ into $S = \{a \in A : c_a = -1\}$ (nonempty!) and $d_a = c_a \ge 0$ on $A \setminus S$ with $\sum_{a \notin S} d_a = |S|$!
     - So $A$ is valid mod $N$ **IF AND ONLY IF** for every nonempty $S \subsetneq A$ and every multiset $M$ of size $|S|$ supported on $A \setminus S$,
       $$\sum_{a \in S} a \not\equiv \sum_{b \in M} b \pmod N!!$$
     - In particular, ALL $2^n$ subset sums $\sum_{a \in T} a \pmod N$ MUST be **PAIRWISE DISTINCT**? Wait: NO! Two disjoint sets $T_1, T_2$ of **EQUAL SIZE** $|T_1| = |T_2|$ cannot have the same sum mod $N$ (otherwise take $S = T_1$, $M = T_2$!). Even stronger: NO subset $S$ can equal ANY multiset sum of size $|S|$ from $A \setminus S$!
     - **HOLD ON — CHECK SUBSET SUMS OF ARBITRARY SIZE TOO!** What if $T_1, T_2 \subseteq A$ have DIFFERENT sizes $|T_1| < |T_2|$ and same sum mod $N$? You can't immediately pad $T_1$ unless $0 \in A$ — wait: **translation invariance**! Replacing $A$ by $A - a_0$ preserves validity mod $N$ (because $\sum m(a) = n$ cancels any constant shift!!)!
     - So **WLOG $0 \in A$**!!
     - NOW LOOK WHAT HAPPENS WHEN $0 \in A$: for ANY two subsets $X, Y \subseteq A \setminus \{0\}$ with $X \ne Y$:
       - Put $S = X \setminus Y$ and $T = Y \setminus X$ (disjoint!).
       - If $|S| \ge |T|$ and $\sum_{a \in S} a \equiv \sum_{b \in T} b \pmod N$, then **PAD $T$ WITH $|S| - |T|$ COPIES OF $0 \in A \setminus S$**!! That gives a multiset $M$ of size $|S|$ supported on $A \setminus S$ with $\sum M \equiv \sum S \pmod N$ — **CONTRADICTION!!**
       - **WAIT A SECOND!! STOP AND DOUBLE-CHECK THAT!!**
         - Because $0 \in A \setminus (X \setminus Y)$ whenever $0 \notin X \setminus Y$ (which holds since $X, Y \subseteq A \setminus \{0\}$!), **EVERY pair of distinct subsets of $A \setminus \{0\}$ has DISTINCT sums mod $N$** — which ALREADY gives the instant bound $N \ge 2^{n-1}$!!
       - **WAIT EVEN BETTER!!** We didn't even use the **EXACT** freedom of choosing WHICH element $a_0 \in A$ to translate to $0$!!
         - For **EVERY** $a_0 \in A$, ALL $2^{n-1}$ subset sums of $(A \setminus \{a_0\}) - a_0$ are distinct mod $N$, AND even more: for every $k$-element subset $S \subseteq A$ and EVERY multiset $M$ of size $k$ from $A \setminus S$, $\sum S \not\equiv \sum M \pmod N$!!
         - In fact, consider ALL $2^n$ subsets $T \subseteq A$ — when can two distinct subsets $T_1, T_2 \subseteq A$ have the same sum mod $N$ (after translating $0 \in A$)? ONLY if $0 \in T_1 \triangle T_2$ AND the larger one contains $0$!! Wait: if $0 \in T_1 \setminus T_2$ and $|T_1| \le |T_2|$, pad $T_1 \setminus T_2$ with $|T_2| - |T_1|$ copies of something? Wait — you can only pad with $0$ if $0$ is on the side being padded, i.e. $0 \notin S$! So collisions ONLY happen when $0 \in S$ and $|S| > |T|$ — wait, translating $a_0$ to ANY element of $T_1 \triangle T_2$ kills almost ALL pairs except when...
         - **WHOA!! THAT LOOKS SO CLOSE TO A FULL PROOF OF $N \ge 2^n - 2^{\lfloor \log_2 n \rfloor}$ — OR TO FINDING THE EXACT EXCEPTION WHERE A COUNTEREXAMPLE HIDES!!**
2. **Simultaneous Counterexample Search (Case B Test!):**
   - Look closely at the formula $2^n - 2^{\lfloor \log_2 n \rfloor}$:
     - Notice the **JUMP** at powers of two $n = 2^k$!
       - $n = 7$: $128 - 4 = 124$.
       - $n = 8$: $256 - 8 = 248$.
       - $n = 9$: $512 - 8 = 504$.
       - $n = 15$: $32768 - 8 = 32760$.
       - $n = 16$: $65536 - 16 = 65520$!
     - Why does $2^{\lfloor \log_2 n \rfloor}$ appear for $\{2^k - 1\}$? Because $2^n - 2^r$ lets a single wrap-around collision happen ONLY if you need at least $2^r$ copies of $0$ (Wait: $n$ copies vs $2^{\lfloor \log_2 n \rfloor}$)!
     - **CRITICAL QUESTION:** Is $2^n - 2^{\lfloor \log_2 n \rfloor}$ REALLY the true global minimum over ALL residue sets $A \subseteq \mathbb{Z}/N\mathbb{Z}$ (including **non-super-increasing**, **Conway–Guy distinct-subset-sum sets**!!)?
     - **STOP EVERYTHING!! CONWAY–GUY / BOHMAN / LUNNON DISTINCT-SUBSET-SUM SETS!!**
       - Remember: for ordinary **distinct-subset-sum sets** (Erdős's famous problem!), Conway–Guy sequences beat $2^{n-1}$ starting at $n \ge 21$ (having max element $\approx 0.22002 \cdot 2^n < 2^{n-2}$!!)!
       - WAIT A SECOND!! Check whether a **Conway–Guy / Bohman / Lunnon / shifted-Fibonacci / optimized integer set** $A = \{0 = a_0 < a_1 < \dots < a_{n-1}\}$ has $\mathrm{IsValidMod}(A)$ modulo some $N < 2^n - 2^{\lfloor \log_2 n \rfloor}$!!
       - Think! For an integer set $0 = a_0 < a_1 < \dots < a_{n-1}$:
         - Wait: does `IsValidMod` require NO **multiset** of size $|S|$ from $A \setminus S$ to equal $\sum S \pmod N$ (not just subsets, **multisets** with repetitions!)? YES!
         - What is the **EXACT** smallest valid modulus $N^*(A)$ for Conway–Guy sets, Lunnon sets, greedy sets, and simulated-annealing / C++ optimized sets at $n = 8, 9, 10, 11, 12, \dots, 25$?!
         - **TEST THAT IN C++ IMMEDIATELY!!** If ANY set at $n = 10\text{--}25$ beats $2^n - 2^{\lfloor \log_2 n \rfloor}$, that is an **INSTANT CASE B DISPROOF OF FONOLLOSA'S CONJECTURE** (and verifiable in Lean 4 via finite certificate / `decide` or clean algebraic witness)!!
         - Conversely, if EVERY set fails to beat $2^n - 2^{\lfloor \log_2 n \rfloor}$ even when Conway–Guy beats distinct-subset-sum, figure out **WHY multisets kill Conway–Guy** and turn THAT exact mechanism into a **CASE A FULL PROOF**!!

## Required Outputs
- **NEVER modify `FonollosaMinModulus/Challenge.lean`** (verify SHA-256 before and after!).
- **Zero bluffing.** Every claim backed by rigorous proof, exact Python/C++ verification, or Lean 4 kernel proof.
- **If Case A (Full Proof!) or Case B (Counterexample!):**
  - Produce `PROOF.md` + `FonollosaMinModulus/Solution.lean` (imported by `FonollosaMinModulus.lean`) proving `FonollosaMinModulusConjecture` OR `¬ FonollosaMinModulusConjecture`, compiling cleanly under `lake build` with **ZERO `sorry`**, **ZERO `admit`**, **ZERO `native_decide`**, standard axioms ONLY!
- **If Case C (Unresolved in Round 1):**
  - Write `RESEARCH_ANALYSIS.md` with exact literature review (`arXiv:2607.08366` & Sitjar), exact C++/Python findings (including Conway–Guy / non-super-increasing tests!), strongest proved lower bounds & structural theorems, Lean 4 kernel-verified lemmas in `FonollosaMinModulus/ResearchLemmas.lean` (`lake build` + axiom audit clean), and the single sharpest attack angle for Round 2!
