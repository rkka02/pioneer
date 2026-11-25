# Astra MAX Attack — Round 1: TxGraffiti Conjecture 3 (`arXiv:2507.17780`)

## Frozen Target (`TxGraffiti3/Challenge.lean` — READ-ONLY, NEVER MODIFY!)
**TxGraffiti Conjecture 3 (Davila–Brimkov–Pepper, open since 2020; arXiv:2507.17780):**
For every finite $r$-regular simple graph $G$ with $r \ge 1$,
$$i(G) \le \mu^*(G),$$
where:
- $i(G)$ is the **independent domination number** (minimum size of a maximal independent set),
- $\mu^*(G)$ is the **saturation number** (minimum size of a maximal matching, equivalently $i(L(G))$).

Note: The statement does **not** assume connectedness (though both $i$ and $\mu^*$ are additive over connected components, so connected graphs suffice!). Its twin $\alpha(G) \le \mu(G)$ for $r$-regular graphs was proved by Caro–Davila–Pepper (2022). Conjecture 1 of the same paper was proved in June 2026 (`arXiv:2606.29553`), and Conjecture 4 ($\mu^*(G) \le H(G)$) was disproved by the 9-vertex friendship graph $F_4$. **Conjecture 3 is completely open!**

## Mission: Go Straight for the Kill (Case A Full Proof OR Case B Counterexample!)
You have full access to `/Users/mw/miniconda3/bin/python3` (NumPy, SciPy MILP, NetworkX, Numba), `clang++ -O3 -march=native`, `nauty` (`geng` is on `PATH`), Lean 4.36.0 (`lake build`), and `web_search`.

### Attack Strategy (Hit BOTH Sides Hard!)
1. **Immediate Computational Counterexample Hunt (Case B Test!):**
   - For $r = 1, 2$ the conjecture is trivial ($K_2$: $1 \le 1$; cycles $C_n$: $i(C_n) = \lceil n/3 \rceil = \mu^*(C_n)$!).
   - Notice: on $C_n$ (and $K_{r,r}$ where $i = r = \mu^*$? Wait: on $K_{r,r}$, $i(K_{r,r}) = r$ and $\mu^*(K_{r,r}) = r$! On $K_{r+1}$, $i = 1 \le \lfloor (r+1)/2 \rfloor$!).
   - **CRITICAL CHECK:** Search exhaustively with `geng` + fast C++ / Python MILP for ALL connected $r$-regular graphs:
     - Cubic ($r=3$) up to $n = 20$ (or as far as fast!),
     - $4$-regular up to $n = 16$,
     - $5$-regular up to $n = 14$,
     - **AND** targeted adversarial constructions for $r \ge 3$ (e.g., graphs with a tiny maximal matching $M$ where $V \setminus V(M)$ is a HUGE independent set — wait: if $G$ is $r$-regular and $M$ is a maximal matching, $I_0 = V \setminus V(M)$ is an independent set, so every edge out of $I_0$ goes into $V(M)$! Double counting gives $r|I_0| \le (r-1)|V(M)| = 2(r-1)|M|$, so $|I_0| \le \frac{2(r-1)}{r}|M|$, and $n = 2|M| + |I_0| \le \frac{4r - 2}{r}|M|$! Wait: when $r \ge 3$, $i(G)$ can be **up to** $\frac{r}{2r-1} n$ or $\frac{n}{2}$ on $K_{r,r}$! Wait: what about **bipartite $r$-regular** vs **non-bipartite $r$-regular** graphs with large $i(G)/n$ — e.g., Goddard–Henning extremal cubic/4-regular graphs for $i(G)$, or **blow-ups / joins / Cayley / circulant / Cartesian / lexicographic / Mycielski-like / clique-star gadgets** where EVERY maximal independent set has size $> \mu^*(G)$?!).
   - **IF YOU FIND A COUNTEREXAMPLE $G$ ($i(G) > \mu^*(G)$) — CASE B!**
     - Minimize its order $n$, verify $r$-regularity, exact $i(G)$, and exact $\mu^*(G)$ by two independent solvers, AND **write a COMPLETE, ZERO-`sorry` Lean 4 disproof (`TxGraffiti3/Solution.lean` proving `¬ TxGraffitiConjecture3`)**, verify `lake build` + `#print axioms` (standard axioms `propext`, `Classical.choice`, `Quot.sound` ONLY — no `native_decide`!), and write `PROOF.md`!
2. **Direct Structural Proof Attack (Case A Test!):**
   - Look at the geometry around a **minimum maximal matching** $M$ of size $k = \mu^*(G)$:
     - $U = V(M)$ has size $2k$; $W = V \setminus U$ is an independent set of size $w = n - 2k$.
     - Can you ALWAYS construct an independent dominating set $D$ of size $\le k$ (picking at most 1 vertex per edge of $M$, OR swapping some edges of $M$ with vertices in $W$)?
     - Wait: if you try to pick $\le 1$ vertex from each $e \in M$ plus maybe some vertices of $W$? Notice: if $W = \emptyset$ ($M$ is a perfect matching!), wait — can an $r$-regular graph with a perfect matching EVER have $i(G) > n/2$?! NO! Because $i(G) \le \alpha(G)$? No, $i(G) \le n/2$ holds for EVERY isolate-free graph since the smaller side of ANY maximal independent set... wait: $i(G)$ CAN exceed $n/2$ only for non-regular graphs (like stars $K_{1,t}$)! For **ANY** $r$-regular graph ($r \ge 1$), by Caro–Wei / Hall / Brooks / Goddard–Henning: wait, $i(G) \le \frac{n}{2}$ ALWAYS holds for $r$-regular graphs ($r \ge 1$)! Wait: IS $i(G) \le n/2$ ALWAYS true for $r$-regular graphs? (Check! On $K_{r,r}$, $i = r = n/2$; on $C_5$, $i = 2 \le 5/2$!)
     - So any counterexample MUST have $\mu^*(G) < n/2$, i.e. $W = V \setminus V(M) \ne \emptyset$!
     - **THAT MEANS** studying the bipartite/induced structure between $U = V(M)$ and $W = V \setminus V(M)$ — e.g., **greedy / probabilistic / König–Hall / maximum matching augmentation / Goddard–Henning bounds $i(G) \le c_r n$ vs $\mu^*(G) \ge \frac{r}{4r-2} n$**!!
     - WAIT A SECOND!! CHECK THAT RATIO RIGHT NOW!!
       - Double counting gave $n \le \frac{4r-2}{r} \mu^*(G) \implies \mu^*(G) \ge \frac{r}{4r-2} n$ (for $r=3$: $\mu^*(G) \ge \frac{3}{10}n$; for $r=4$: $\mu^*(G) \ge \frac{4}{14}n = \frac{2}{7}n$; for large $r$: $\mu^*(G) \ge \frac{1}{4}n$!).
       - Meanwhile, what is the MAXIMUM possible ratio $i(G)/n$ for $r$-regular graphs?!
         - For $r=3$ (Lam–Shiu–Sun 1999 / Goddard–Henning): for connected cubic graphs other than $K_{3,3}$, $i(G) \le \frac{2}{5}n$ (and $K_{3,3}$ has $i = 3 = \mu^*$)! Notice $\frac{2}{5} > \frac{3}{10}$!
         - For $r=4$: $i(G)$ can be as large as $\frac{3}{7}n$ (wait: on $K_{4,4}$, $i = 4 = n/2$, and for non-$K_{4,4}$, $i(G) \le \frac{3}{7}n$ or $\frac{4}{9}n$!), while $\mu^*(G)$ can be as small as $\frac{2}{7}n$!
         - **HOLD EVERYTHING!!** On a graph achieving BOTH large $i(G)/n$ (near $1/2$ or $3/7$ or $2/5$) AND small $\mu^*(G)/n$ (near $r/(4r-2) \approx 1/4$), **CAN THEY COEXIST?!**
         - Test this IMMEDIATELY! For large $r$, $K_{r,r}$ has $i/n = 1/2$, while $\mu^*/n$ can drop toward $1/4$ on graphs with a large independent set $W$! Wait: if $W$ is an independent set of size $w$, then $W$ ITSELF can be extended to a maximal independent set? Wait: NO, $W$ is already BIG, we want a **SMALL** maximal independent set $D$ — if $W$ is big, we want to dominate $W$ from $U$ using $\le k$ vertices of $U$! What if EVERY independent subset $S \subseteq U$ that dominates $W$ fails to dominate $U$ without adding tons of vertices of $W$?!
   - **IF YOU FIND A FULL PROOF — CASE A!**
     - Write `PROOF.md` AND **write a COMPLETE, ZERO-`sorry` Lean 4 proof (`TxGraffiti3/Solution.lean` proving `TxGraffitiConjecture3`)**, verify `lake build` + `#print axioms` (standard axioms ONLY)!

## Required Outputs
- **NEVER modify `TxGraffiti3/Challenge.lean`** (verify its SHA-256 before and after!).
- **Zero bluffing.** Every claim backed by rigorous proof, exact Python/C++ verification, or Lean 4 kernel proof.
- **If Case A (Full Proof!) or Case B (Counterexample!):**
  - Produce `PROOF.md` + `TxGraffiti3/Solution.lean` (imported by `TxGraffiti3.lean`) compiling cleanly under `lake build` with **ZERO `sorry`**, **ZERO `admit`**, **ZERO `native_decide`**, standard axioms ONLY!
- **If Case C (Unresolved in Round 1):**
  - Write `RESEARCH_ANALYSIS.md` with exact census results, tightest extremal graphs, all proved partial theorems (e.g., specific $r$, structural reductions, sharp bounds), all verification scripts in `scripts/`, kernel-verified Lean 4 lemmas in `TxGraffiti3/ResearchLemmas.lean` (`lake build` + axiom audit clean), and the single sharpest attack angle for Round 2!
