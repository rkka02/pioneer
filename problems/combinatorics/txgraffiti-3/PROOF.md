# A 42-vertex cubic counterexample to TxGraffiti Conjecture 3

There is a connected cubic simple graph $G$ on 42 vertices with

$$
i(G)=14>13=\mu^*(G).
$$

The theorem `TxGraffiti3.not_TxGraffitiConjecture3` proves the negation of the frozen statement. The construction below reduces a public 48-vertex example by six vertices. [Lean disproof](TxGraffiti3/Solution.lean) · [Original conjecture, §2.3](https://arxiv.org/html/2507.17780v1#S2.SS3) · [Order-48 source and data](https://github.com/ipitchford/txgraffiti-order48-successor)

## The graph

Use vertex labels 0 through 41. Among vertices 0 through 25, put in the 13 edges

$$
M=\big\{\{2j,2j+1\}:0\le j<13\big\}
$$

and the two further edges $\{3,4\}$ and $\{6,11\}$. Vertices 26 through 41 form an independent set. Their complete neighborhoods are given below.

| Vertex | Neighbors | Vertex | Neighbors |
|---:|:---|---:|:---|
| 26 | 19, 20, 23 | 34 | 0, 14, 21 |
| 27 | 0, 15, 16 | 35 | 14, 16, 18 |
| 28 | 13, 20, 25 | 36 | 2, 4, 24 |
| 29 | 9, 17, 23 | 37 | 3, 8, 24 |
| 30 | 5, 7, 10 | 38 | 6, 10, 12 |
| 31 | 1, 15, 18 | 39 | 1, 19, 21 |
| 32 | 9, 13, 22 | 40 | 11, 12, 22 |
| 33 | 2, 5, 7 | 41 | 8, 17, 25 |

Lean checks the displayed adjacency table against the graph for all 1,764 ordered vertex pairs. Each vertex has degree three. There are $13+2+16\cdot3=63$ edges. Lean also checks connectivity by assigning each nonzero vertex a neighbor of smaller distance to vertex 0. The graph6 record used by Lean and the independent solvers has SHA-256 `6ab95c870fc51afa068c6e25ed16f1bf48abe787be29a48a287cd7d89cbee692`, including its final newline. [Graph6 data](scripts/counterexample.g6) · [Lean graph and connectivity proof](TxGraffiti3/Certificate.lean)

To reproduce the reduction, start with the labels in the order-48 source. Delete vertices $2,3,18,19,32,39$. Add the seven edges

$$
\{1,36\},\ \{1,45\},\ \{8,44\},\ \{12,44\},\ \{13,46\},\ \{20,41\},\ \{25,40\}.
$$

Relabel the survivors in increasing order starting at zero. This gives the displayed graph byte for byte. [Reconstruction and table check](scripts/reconstruct.py) · [Archived seed](https://doi.org/10.5281/zenodo.22083656)

## The saturation number is 13

The edges of $M$ are disjoint. Every edge outside $M$ has an endpoint in $\{0,\ldots,25\}$, so none can be added. Thus $\mu^*(G)\le13$.

Conversely, every edge of a graph meets some member of any maximal matching, including a matching edge meeting itself. In a cubic simple graph each matching edge covers at most five edges, counting itself and the two other edges at each endpoint. Therefore a maximal matching has at least $\lceil 63/5\rceil=13$ edges. The Lean argument proves the general bound $|E(G)|\le(2r-1)|M|$ for an $r$-regular graph and a maximal matching. [Matching proof](TxGraffiti3/Matching.lean)

## The independent domination number is 14

Take the even endpoints of the pairs in $M$, replacing 0 by 1. These 13 vertices are independent. They dominate every vertex except 29, whose neighbors are 9, 17, and 23. Adjoining 29 gives the independent dominating set

$$
D=\{1,2,4,6,8,10,12,14,16,18,20,22,24,29\}.
$$

For the lower bound let $f(S)=i(G[S])$, with $f(\varnothing)=0$. If $S=A\sqcup B$ with no edges across the partition, then $f(S)=f(A)+f(B)$. For every $p\in S$, using closed neighborhoods in the original graph,

$$
f(S)=1+\min_{x\in S\cap N[p]} f(S\setminus N[x]).
$$

Indeed, every independent dominating set in $S$ contains an $x\in N[p]$. After removing $x$, the other selected vertices lie in $S\setminus N[x]$ by independence. They dominate this entire residual set since $x$ has no neighbor there. Conversely, adjoining $x$ to any independent dominating set of the residual set gives one for $S$.

The following four values evaluate the last step with $S=V(G)$ and $p=15$.

| Selected vertex $x$ in $N[15]$ | 15 | 14 | 27 | 31 |
|---|---:|---:|---:|---:|
| $f(V(G)\setminus N[x])$ | 13 | 13 | 13 | 13 |

The full computation has **277 distinct vertex subsets**. One is empty, 40 split into components, and 236 branch on a closed neighborhood. To reproduce these numbers, split off the component of the least label whenever the current graph is disconnected. Otherwise pick a vertex minimizing $|S\cap N[p]|$, breaking ties by breadth-first order from vertex 15 with neighbors visited in increasing label order. Cache each answer by its vertex subset. Both the Python implementation and the Lean certificate reproduce the root bound of 14. [Integer recurrence and root table](scripts/reconstruct.py) · [Certificate](TxGraffiti3/Certificate.lean)

Lean checks every row of the lower-bound certificate. A split must give the stated disjoint union, have no crossing edge, and cite two earlier rows. A pivot must belong to the current set and have an earlier row for **every** eligible choice of $x$, with the correct residual mask and sufficient lower bound. Induction on the row index then bounds the cardinality of every feasible independent dominating set. The explicit set $D$ attains the bound. [Soundness proof](TxGraffiti3/Bounds.lean) · [Exact values under the frozen definitions](TxGraffiti3/Solution.lean)

Of the $2^{13}$ endpoint selections, 4,608 are independent. Exactly 1,271 of these leave one unmatched vertex undominated, 2,483 leave two, 821 leave three, and 33 leave four. The recurrence above also covers sets that omit whole pairs and select unmatched vertices. [Endpoint enumeration](scripts/reconstruct.py)

## Connected counterexamples in every degree divisible by three

For any integer $t\ge1$, replace each vertex of $G$ by $t$ pairwise nonadjacent copies and each edge by the complete bipartite graph between its two classes. The resulting graph $G_t$ is connected and $3t$-regular. A maximal independent set that meets a class contains that whole class, since its copies have identical neighborhoods. The occupied classes form a maximal independent set of $G$, and conversely every maximal independent set of $G$ lifts this way. Hence $i(G_t)=14t$.

For each of the 13 edges of $M$, match the $t$ copies of one endpoint bijectively to the $t$ copies of the other. The unmatched classes lie over the original independent set $\{26,\ldots,41\}$, so the lifted matching is maximal. Consequently $\mu^*(G_t)\le13t$ and the additive gap is at least $t$. The same lifting argument applies to earlier order-50 examples. [Earlier cubic constructions](https://github.com/andrewbutz22-cosmic/cubic-domination-counterexamples)

## What regularity still implies

For an independent set of size $a$ in an $r$-regular graph on $n$ vertices with $r>0$, all $ra$ incident edges go to the complement, whose vertices can receive at most $r(n-a)$ such edges. Thus every independent set, including a minimum independent dominating set, has size at most $n/2$. Also, in a nonempty graph, a vertex of a maximum independent set has all $r$ neighbors outside that set, so $\alpha(G)\le n-r$. The unmatched vertices of every maximal matching are independent, giving $2\mu^*(G)\ge n-\alpha(G)\ge r$. Consequently the conjectured inequality holds whenever $3r\ge2n$, since then $i(G)\le n-r\le r/2\le\mu^*(G)$.

## Independent verification

| Method | $i(G)$ | $\mu^*(G)$ |
|---|---:|---:|
| C++ integer branching on undominated vertices and uncovered edges | 14 | 13 |
| Python integer dynamic programming on $G$ and its line graph | 14 | 13 |
| SciPy/HiGHS binary optimization, reported optimality gap zero | 14 | 13 |
| Lean kernel | 14 | 13 |

The second solver processes vertices in a fixed order. It retains which vertices have already been dominated, refuses to select a vertex adjacent to an earlier selection, and enforces domination when the last possible member of each closed neighborhood is processed. Equal states have the same continuations, so it keeps the least cost. On the line graph this directly minimizes the size of a maximal matching. HiGHS independently returned a different 14-vertex independent dominating set. [C++ solver](scripts/check_graphs.cpp) · [Python integer solver](scripts/check_exact.py) · [MILP](scripts/check_milp.py)

Direct enumeration found 94,180 maximal independent sets, including 32,803 of minimum size 14. It found 27,191,161 maximal matchings, including exactly two of minimum size 13. To reproduce these counts with NetworkX, evaluate `Counter(map(len, nx.find_cliques(nx.complement(H))))` with `H = G` and with `H = nx.line_graph(G)`, using `Counter` from Python’s `collections` module.

From the project root, run

```sh
lake build
lake env lean scripts/audit.lean
lake env leanchecker -v TxGraffiti3
clang++ -std=c++20 -O3 -march=native scripts/check_graphs.cpp -o /tmp/txg3-check
/tmp/txg3-check --exact < scripts/counterexample.g6
python3 scripts/check_exact.py scripts/counterexample.g6
python3 scripts/check_milp.py scripts/counterexample.g6
python3 scripts/reconstruct.py
shasum -a 256 TxGraffiti3/Challenge.lean
```

Use a Python environment containing NetworkX, NumPy, and SciPy. The theorem, both equalities, and cubicity audit to `[propext, Classical.choice, Quot.sound]`. Connectivity audits to `[propext, Quot.sound]`. The compile-time search supplies numerical data. Kernel reduction checks the finite claims. The build emits the frozen file’s existing module-import warnings. The frozen challenge had SHA-256 `d54daf16a077ec5cf824d8fc0f336888a413396799bc203c1b14d4cd85430d41` before and after the work. [Axiom audit](scripts/audit.lean)

## Exhaustive census and order minimization

The three requested connected censuses tested **12,967,515** isomorphism classes and found **zero** violations. Each nonempty entry below is a completed order. All order-by-degree counts agree with the independent GENREG enumeration. [Meringer’s tables of connected regular graphs](https://www.mathe2.uni-bayreuth.de/markus/reggraphs.html#CRG)

The checker can accept a graph immediately when it finds an independent dominating set of size at most $\lceil |E|/(2r-1)\rceil$. Otherwise it computes the independent domination number and checks whether a smaller maximal matching exists. For an uncovered edge $uv$, it branches on every available edge incident to $u$ or $v$, deleting both endpoints of the chosen edge. This exhausts the possibilities for a maximal matching. [Census driver](scripts/census.py) · [Decision recurrences](scripts/regular_graph.hpp)

| Order | Cubic | 4-regular | 5-regular |
|---:|---:|---:|---:|
| 4 | 1 | | |
| 5 | | 1 | |
| 6 | 2 | 1 | 1 |
| 7 | | 2 | |
| 8 | 5 | 6 | 3 |
| 9 | | 16 | |
| 10 | 19 | 59 | 60 |
| 11 | | 265 | |
| 12 | 85 | 1,544 | 7,848 |
| 13 | | 10,778 | |
| 14 | 509 | 88,168 | 3,459,383 |
| 15 | | 805,491 | |
| 16 | 4,060 | 8,037,418 | |
| 18 | 41,301 | | |
| 20 | 510,489 | | |
| **Total** | **556,471** | **8,943,749** | **3,467,295** |

Deleting two vertices from the 48-vertex seed and reconnecting all exposed ends in every simple connected cubic way gave 10,297 nonisomorphic order-46 graphs, all satisfying the inequality. Deleting two whole matching edges and two unmatched vertices allowed a larger reduction. Among 24,754,581 reconnection trials retaining the other 13 matching edges and keeping the other unmatched vertices independent, eight trials produced connected graphs with independent domination number greater than 13. They represent four isomorphism classes on 42 vertices. The witness above is the first output. Applying all two-vertex deletions and cubic reconnections to this witness gave 7,128 nonisomorphic connected graphs on 40 vertices, all satisfying the inequality. [Exhaustive two-vertex reduction](scripts/reduce_cubic.py) · [Matching-preserving search](scripts/reconnect.cpp)

For the four order-42 representatives, the same matching-preserving search tested 1,318,525 further reconnections at order 38 and 33,212,685 at order 36. None produced a connected graph whose independent domination number exceeded the retained matching size. A separate search allowed arbitrary positive integer sizes for independent twin classes in blow-ups of connected templates on two through eight vertices, with total order at most 47. Its MILP found no counterexample. [Blow-up model](scripts/search_blowups.py)

An all-degree census checked **50,724,108** isomorphism classes of regular graphs of positive degree on 2 through 14 vertices, including disconnected graphs. Of these, 50,314,869 have order 14. Every graph passed. For this run, nauty generated each degree up to $(n-1)/2$, and the checker also tested the complementary degree. At order zero both invariants are zero, and the one-vertex graph has degree zero. Thus the global minimum counterexample order lies between **15 and 42** inclusive. For cubic graphs the requested census gives the narrower interval **22 through 42**. Global minimality remains undetermined.

To replay both censuses and obtain the four order-42 representatives, run

```sh
python3 scripts/census.py requested /tmp/txg3-check
python3 scripts/census.py small /tmp/txg3-check
clang++ -std=c++20 -O3 -march=native scripts/reconnect.cpp -o /tmp/txg3-reconnect
/tmp/txg3-reconnect 15 2 < scripts/order48.g6 | shortg -qk > /tmp/txg3-order42.g6
python3 scripts/reduce_cubic.py scripts/counterexample.g6 | shortg -qk | /tmp/txg3-check
```
