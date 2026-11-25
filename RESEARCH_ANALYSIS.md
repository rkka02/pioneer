# Tutte's 3-flow conjecture — research report

**MAX Round 1 result.** Case C. A positive deficit of one can require arbitrarily many neutral exchanges, even in simple 5-regular graphs with every nontrivial cut of size at least seven. The constructions have explicit flows. An eight-vertex fractional vertex obstructs direct polyhedral rounding. All five minority positions extended at the 781 roots tested in the new search. The proofs, certificates and single Round 2 target are in [the Round 1 findings](#8-max-round-1).

**Case C, 25 November 2026.** I found neither a proof of `Tutte3FlowConjecture` nor a counterexample. The main positive result below gives a checkable sufficient condition for a *specified* bisection of a 5-regular graph to realize a 3-flow. Its special case for singleton and two-vertex components has sharp integer thresholds. The main obstruction is an 18-vertex simple 5-edge-connected graph whose unique maximum bisection fails, even though each side induces a forest and every nontrivial cut has size at least seven. A different bisection of the same graph gives an integer 3-flow.

Two supporting theorems now have Lean proofs for the frozen multigraph representation. One realizes prescribed outdegrees from cut inequalities. The other lifts **each given** nonzero residue circulation to an integer 3-flow, preserving every edge residue. The missing step is the unconditional existence of a feasible modular prescription.

## 1. The precise five-edge obstruction in LTWZ

Work first with loopless graphs. Parallel edges are distinct. Loops can be deleted for the existence question and restored with value 1. Write $d(S)=|\delta(S)|$, $e(S)=|E(G[S])|$ and $\beta(S)=\sum_{v\in S}\beta(v)$. The sign convention is outgoing minus incoming. A boundary sums to zero in $\mathbb F_3$.

Kochol's reduction makes the universal 5-edge-connected zero-boundary question equivalent to Tutte's conjecture. Prescribing **every** boundary gives the stronger Jaeger–Linial–Payan–Tarsi conjecture. Li's extension equivalences distinguish them even with a single preoriented vertex of degree five. This is a reason to retain the zero-boundary specialization during a contraction. [Kochol (2001)](https://www.sciencedirect.com/science/article/pii/S0095895601920544) · [Jaeger, Linial, Payan and Tarsi (1992)](https://doi.org/10.1016/0095-8956(92)90016-Q) · [Li (2020), Theorems 1 and 2](https://lijiaao-dm-nk.com/pdf/pub/Jiaao19_flow-extension_EJC20.pdf)

Thomassen obtained connectivity eight at modulus three. LTWZ Theorem 1.12 gives $3k-3$ for arbitrary boundaries at odd modulus $k\ge3$. In particular **every 6-edge-connected graph is $\mathbb Z_3$-connected**. Their odd-7-edge-connectivity result gives a zero-boundary orientation. [Thomassen (2012)](https://orbit.dtu.dk/en/publications/the-weak-3-flow-conjecture-and-the-weak-circular-flow/) · [LTWZ (2013), Corollaries 4.11 and 4.15](https://math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2013-3-flow-LTWZ.pdf)

For $k=3$, choose $\tau(S)\in[-3,3]$ of parity $d(S)$ and residue $\beta(S)$. Its absolute value is unique. Theorem 3.1 assumes at least three vertices, a compatible root preorientation with $d(z)\le4+|\tau(z)|$, and $d(S)\ge4+|\tau(S)|$ for nonempty $S$ avoiding $z$ with at least two vertices in the complement. There is a singleton exception for a minimum-degree nonroot vertex with $\tau=0$, if one exists. Here is the arithmetic of the lower bound. [LTWZ, Theorem 3.1](https://math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2013-3-flow-LTWZ.pdf)

| Cut size | $\beta(S)$ | $\lvert\tau\rvert$ | Actual size minus required size |
|---:|:---:|---:|---:|
| 5 | 0 | 3 | −2 |
| 5 | ±1 | 1 | 0 |
| 6 | 0 | 0 | +2 |
| 6 | ±1 | 2 | 0 |
| 7 | 0 | 3 | 0 |
| 7 | ±1 | 1 | +2 |

Thus the only deficient type among cuts of size at least five is $(5,0)$. This includes the singleton of **every** vertex in the 5-regular zero-boundary case. At such a cut the outgoing count is 1 or 4. The identity of the minority edge remains free arithmetic data.

In LTWZ Claim 1, a nontrivial shore at the lower threshold can be contracted, and its complement can then be contracted to a new preoriented root. The old lower and new upper bounds meet. Parity gives the surviving nontrivial shores two units of slack. This pays for losing two cut edges under a lift, or for losing an edge while the required $|\tau|$ rises by one under a boundary-changing deletion. At $(5,0)$ the **new root meets its upper bound** $5\le7$. The failure is the lower bound on an *uncontracted* shore, including singleton shores, and the lack of an extension theorem for the resulting instances. Simply invoking existence on each quotient supplies no agreement of the five directions. In Claim 2 the lifting vertex is the exceptional $v_0$ with $\tau(v_0)=0$. [LTWZ, proof of Theorem 3.1, Claims 1–4](https://math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2013-3-flow-LTWZ.pdf)

Three exact tests delimit possible repairs.

- **A uniform two-unit discount fails.** In $K_{3,3}$ with $\beta\equiv1$, every allowed outdegree is 2. Their sum would be 12 for nine edges. Direct enumeration gives $\min_S(d(S)-|\tau(S)|)=2$ over nonempty proper shores. This refutes a blanket lower bound of two. Its connectivity is three.
- **An arbitrary lift can destroy a nontrivial five-cut.** Splice a rooted $K_6$ to a rooted Petersen graph whose two pentagon edge sets have been doubled. In the labels of `bad_split` the shore $\{0,1,2,3,4\}$ has cut edges $05,15,28,38,49$. The full graph has minimum cut five. Lift $05,15$ at vertex 5. The displayed shore now has cut size three. Independently, lifting two disjoint opposite pairs at one zero-boundary 5-vertex is impossible in any valid orientation. Both pairs would need the unique minority incidence.
- **Two compatible roots can conflict at zero boundary.** In $K_6$ take roots $a,b$, orient $a\to b$, and at every other vertex $v$ prescribe $b\to v\to a$. Both roots already satisfy the boundary and either prescription alone extends. Taken together they leave zero demands on the internal $K_4$. Every balanced cubic vertex must be a source or a sink, which would 2-color $K_4$. The obstruction survives even though the two prescriptions agree on their common edge. More sophisticated rooted extension results impose additional degree and separating-cut assumptions. [Árnadóttir et al., *Flow-critical graphs*](https://arxiv.org/abs/2502.01451)

**Recent scope.** Li and Li allow five-cuts and exclude cut sizes 6 through 40 in the stated introductory theorem. Appendix A.2 of their posted manuscript improves the forbidden interval to 6 through 20. Appendix A.1 separately gives essential 23-edge-connectivity. Ahanjideh and Kovács characterize simple 5-valent graphs using pseudoforests and a transversal matching and prove a Cayley graph class. Jafari's November preprint treats uniformly random simple 5-regular graphs asymptotically and gives a fractional matching criterion for induced forests. These results leave the adversarial 5-regular case here open. [Li and Li, Appendix A](https://arxiv.org/html/2609.08377v1#A1) · [Ahanjideh and Kovács, Lemma 3.2](https://arxiv.org/html/2603.24175v2#S3) · [Jafari, §§6.1–6.2](https://arxiv.org/html/2611.03763v2#S6)

## 2. Exact information carried by a five-cut

For a rooted half with five labelled ports and zero boundary, let $p_i$ count extensions when the root directs only port $i$ outward. Reversing all edges gives the count for the complementary signs. If the other half has profile $q$ and the ports are joined by permutation $\pi$, the number of orientations of the splice is

$$2\sum_{i=1}^5 p_i q_{\pi(i)}.$$

Indeed, orienting across the cut fixes the internal boundaries on both halves, after which their choices are independent. There are five possible minority positions and two signs. In particular, support intersection after relabelling is necessary and sufficient. Having at least three positions available on both halves suffices for arbitrary pairing. Proving this support bound on every relevant half is open in this investigation. Even such a bound would require a separate argument for graphs having only trivial five-cuts.

The first order-eight graph in the `geng` census, with root 3, gives $(24,24,24,29,29)$. The 120 self-gluings have respectively 6,720, 6,770 and 6,820 orientations, for 36, 72 and 12 permutations. The aggregate boundary and the unrooted counts of the halves are the same in all three cases. For nonzero boundaries one sums over each signed cut pattern compatible with the prescribed shore sum. Negating it also negates the boundary, so the factor of two needs its zero-boundary justification. The script checks two whole-graph zero-boundary counts independently and 24 arbitrary-boundary counts against signed gluing. [Computation](scripts/search.py)

## 3. Cut deficit and a sufficient condition for a 3-flow

Let $G$ be loopless and 5-regular. A zero-boundary orientation has outdegree 1 or 4 at each vertex. Its set $H$ of outdegree-4 vertices has size $|V|/2$ by the total outdegree. Write $L=V\setminus H$ and $q(v)=1+3\mathbf1_H(v)$. For a proposed bisection put

$$f_H(S)=e(S)-|S|-3|S\cap H|,\qquad D(H)=\max_{S\subseteq V} f_H(S).$$

The empty shore gives $D\ge0$. The prescription is realizable precisely when $D=0$. Necessity follows by counting tails of internal edges. For sufficiency give each vertex $q(v)$ slots and match each edge to a slot at either endpoint. For any set of edges the incident vertices contain all its edges internally, so their total capacity satisfies Hall's inequality. The total slot count is $|E|$. This also proves the usual absolute cut criterion $3\big||S\cap H|-|S\cap L|\big|\le d(S)$, by writing $2e(S)=5|S|-d(S)$ and taking complements. The general prescribed-degree proof is formalized. [Lean theorem](Tutte3Flow/PrescribedDegrees.lean) · [Hakimi's criterion used in Li et al., Theorem 2.13](https://lijiaao-dm-nk.com/pdf/pub/Jiaao08_Nowhere-zero3flow-ind_DM2018.pdf)

### Matching deficiency equals the exact worst cut deficit

Suppose both induced color classes are pseudoforests. Form a bipartite graph on their **tree components**. Join two components if any original cross edge joins them. The number $t$ of tree components is equal on the two sides. Indeed their internal edge counts agree by regularity and balance, and each side has $|H|-t$ internal edges. If the maximum component matching has size $\nu$, then

$$D(H)=t-\nu.$$

For the upper bound orient each high tree away from its root and each low tree toward its root. Choose the roots of matched trees at the endpoints of a representative matching edge. Orient that edge low to high and other crossing edges high to low. In a high unicyclic component orient the cycle cyclically and the attached trees away from it. Reverse the tree directions in low unicyclic components. Every vertex has its target outdegree except one root of each unmatched high tree with excess 1 and one root of each unmatched low tree with deficit 1. Thus $e(S)\le\sum_{v\in S}d^+(v)\le q(S)+t-\nu$ for all $S$.

For the reverse bound choose a set $X$ of high trees with $|X|-|N(X)|=t-\nu$, by the deficiency form of Hall's theorem. Take $S$ to be these trees and **all** adjacent low components, including adjacent unicyclic ones. Let $h,l$ count its high and low vertices. The high trees have $h-|X|$ internal edges and send $3h+2|X|$ crossing edges into the chosen low components. The low components have $l-|N(X)|$ internal edges. Subtracting $4h+l$ gives $f_H(S)=|X|-|N(X)|$.

The zero-deficiency case is the transversal criterion of Ahanjideh and Kovács. Jafari also gives a weighted Hall equivalence on two forests. The additive deficit identity and the following bound are deductions made here. The literature check located these closely related criteria. Priority for the deductions or the examples is unverified. [Ahanjideh and Kovács](https://arxiv.org/html/2603.24175v2#S3) · [Jafari, Proposition 6.3](https://arxiv.org/html/2611.03763v2#S6.SS2)

### A sufficient component-size bound with a sharp special case

**Proposition.** Suppose both classes induce forests and $G$ has edge connectivity at least $\lambda$. For an integer $s\ge1$ write

$$R_s=\sum_{T\text{ low}} (|T|-s)_+ +\sum_{T\text{ high}}(s-|T|)_+.$$

If $3R_s<\lambda+3s+2$, the prescribed bisection realizes a nowhere-zero 3-flow.

**Proof.** If Hall fails, choose nonempty $X$ on the high side with $|N(X)|<|X|$. The union of $X$ and $N(X)$ is a nonempty proper shore since at least one low tree is omitted. All edges crossing this shore go from $N(X)$ to high trees outside $X$. A tree of order $u$ has $3u+2$ crossing incidences. Subtracting the total degrees of $X$ from those of $N(X)$ yields

$$\lambda\le d(X\cup N(X))\le -(3s+2)+3R_s.$$

Here the notation for the cut means the union of the original vertex sets. The assumed strict inequality rules out Hall failure. Apply the matching construction and integer lifting. ∎

**Consequence at connectivity five.** If all tree sizes are $s$ or $s+1$, the number of each size is equal on the two sides. Using reference size $s$ and then $s+1$ proves sufficiency if there are at most $s+2$ large trees per side **or** at most $s+3$ small trees per side. For components of order 1 or 2, three doubletons or four singletons per side suffice.

**Sharpness at $s=1$.** On one shore take eight vertices $0,\ldots,7$ inducing edges $01,23,45,67$ and five independent vertices $8,\ldots,12$. Join $8+j$ to $(5j+i)\bmod 8$ for $0\le i,j<5$. Take a second copy with labels shifted by 13 and add $i(i+13)$ for $1\le i\le7$. Color the doubletons low on the first shore, high on the second, with the opposite colors on the singleton vertices. This simple 5-regular graph has minimum cut five by exact integer min-cut. Each side has four doubletons and five singletons. The five high singletons in the first shore see only four low doubletons. Equivalently, that shore demands imbalance nine across seven edges. Both integer bounds fail at the very next value. The script also constructs an integer flow using a different signing. [Construction and tests](scripts/forest_bound.py)

A two-forest bisection is an additional hypothesis. For example, every bisection of $K_6$ induces two triangles. This identifies a structural limit to using the proposition alone. The weaker existence of a pseudoforest bisection in all 4-edge-connected 5-regular graphs has itself appeared as a research problem. [Problem 15, DeVos–Ghanbari–Šámal](https://kam.mff.cuni.cz/~kamak/static/problems/2025.pdf)

## 4. An 18-vertex obstruction to maximum bisection and strict descent

Construct a shore on $0,\ldots,8$. Put in the two paths $0$–$1$–$2$ and $3$–$4$–$5$. Give the remaining vertices the following neighbors within the shore.

| Vertex | Neighbors |
|---:|---|
| 6 | 0, 1, 3, 4, 5 |
| 7 | 0, 2, 3, 4, 5 |
| 8 | 0, 1, 2, 3, 5 |

Take another copy shifted by nine. Between copies add $(3,11),(4,9),(0,13),(5,11),(2,10),(1,14),(2,12)$. All degrees are five. Enumeration of all $2^{18}$ shores gives minimum cut five and minimum cut seven when both sides have at least two vertices. [Graph and cut certificate](scripts/obstructions.py)

**Its unique maximum cut up to complement is a bisection of size 37.** Color $0,\ldots,5$ and $15,16,17$ high. The eight path edges are monochromatic. In each copy give the four path edges, in the order $01,12,34,45$, the two-edge crossing paths through $6,8,6,7$ respectively. These paths are edge-disjoint. Removing their edges and the monochromatic edges leaves a connected spanning graph of crossing edges, as verified by traversal. Flipping any nonempty proper set of colors loses at least one residual crossing edge. Each monochromatic edge gained requires the loss of at least one edge on its assigned path. Hence the cut strictly decreases. This argument proves uniqueness even among unbalanced colorings.

On the first shore the prescribed excess is $3(6-3)=9$, beyond the seven-edge capacity. Thus **even a unique maximum bisection into forests can fail the flow criterion**. The high set $\{1,6,7,8,9,10,11,12,13\}$ realizes a bisection of size 35. Tail assignment and integer lifting supply a flow. Size 35 is optimal among realizable bisections because every bisection size has the parity of $5\cdot9$. The unrestricted question of a 3-flow therefore has a positive answer on this obstruction graph. [Witness generator with integer checks](scripts/obstructions.py)

**A single exchange need not decrease $D$.** On the same graph take $H=\{1,3,5,6,8,9,10,13,15\}$. Its deficit is 1. The shore $\{11,12,14,16,17\}$ contains six edges and has only five prescribed tails. A direct sweep over all shores for each of the 81 opposite-color swaps gives minimum neighboring deficit 1. Swapping high 1 with low 2 leaves deficit 1, then swapping high 9 with low 16 gives deficit 0. There are 16 stalled ordered bisections on this graph. Each escapes with one equal-deficit swap followed by a decrease. [Independent 81-swap check and complete exchange search](scripts/exchanges.py)

The flower graph $J_5$ with a complementary 2-factor doubled has 54 stalled ordered bisections. One is $H=\{0,1,2,3,4,6,7,10,13,15\}$, with deficit 1, best adjacent deficit 1 and violating shore $\{16,17,18\}$. The code specifies the matching used to construct the doubled factor. For a nonzero-boundary example use the 12-vertex ring of three cliques in §6 with its six interblock edges doubled. For $\beta=(1,2,2,0,1,1,1,0,2,2,2,1)$, high mask 826 has deficit 1, best adjacent deficit 1 and violating shore mask 3073. A mask encodes a set by $\sum_{v\in S}2^v$. Here high means selecting the larger of the two outdegrees permitted by the vertex boundary.

**Directed path repair can also stall.** Prescribe defects $\beta(0)=2$, $\beta(9)=1$ and zero elsewhere in the 18-vertex graph, with all seven cut edges pointing into the first shore. The solver returns signs and the script checks every divergence. Reversing a directed path adds 1 modulo three at its start and subtracts 1 at its end. A strict reduction from these two defects must annihilate both, so it needs a directed path from 0 to 9. The cut forbids it. Directed-cycle reversals alone preserve every defect. [Pinned instance and reachability check](scripts/obstructions.py)

## 5. Algebraic counting and its cancellation barriers

Fix an incidence matrix $B$ with $+1$ at a tail. Write $N(\beta)=\#\{x\in\{-1,1\}^E:Bx=\beta\pmod3\}$. The boundary dynamic program starts with unit mass at zero. Each edge adds the two translates by plus and minus its column. Dropping one vertex coordinate is exact because the total boundary is zero. A loop doubles every count. For the full arrays in this run $m<63$, so signed 64-bit arithmetic can store even their total $2^m$.

For zero boundary there is an independent expression over vertex colorings. Fix one vertex color to zero and let $h(c)$ be the number of bichromatic edges. Character orthogonality gives

$$N(0)=3^{1-n}\sum_{c}(-1)^{h(c)}2^{m-h(c)}.$$

Each monochromatic edge sums its two characters to 2, and each bichromatic edge sums them to $-1$. Fixing a color removes the common factor of three from translations. This is the flow-polynomial evaluation at three. The cut bound gives a lower bound on the support size of a nonconstant character on a connected graph, but it does not control their cumulative absolute contribution. On a path of 12 links with five parallel edges per link, the ratio of the sum of **all** absolute character terms to the constant term is $(1+2/32)^{12}>2$. Successive color differences are independent. The triangle-inequality lower bound on $N(0)$ is negative although $N(0)=10^{12}$ exactly. Each bundle permits ten balanced assignments. [Exact coefficient and character checks](scripts/search.py)

A second attempted certificate was the constant coefficient of the multilinear reduction of $P(x)=\prod_{v\ne z}(1-(Bx)_v^2)$ in $\mathbb F_3[x]/(x_e^2-1)$. Averaging over the sign cube annihilates each nonconstant squarefree monomial. The coefficient equals $2^{-m}N(0)$ in $\mathbb F_3$. It vanishes for 13 of the 60 order-ten simple 5-regular 5-edge-connected graphs. One example has 864 orientations, by both the integer dynamic program and the character sum. Its edges are specified by the forward neighbor lists below. Vertices without forward neighbors have empty lists.

| Vertex | Larger neighbors |
|---:|---|
| 0 | 4, 5, 6, 7, 8 |
| 1 | 4, 6, 7, 8, 9 |
| 2 | 5, 6, 7, 8, 9 |
| 3 | 5, 6, 7, 8, 9 |
| 4 | 5, 8, 9 |
| 5 | 9 |
| 6 | 7 |

This rules out the specific nonvanishing criterion. A different coefficient or a cancellation-sensitive bound could still certify positivity. Likewise, fractional outdegrees give little by themselves. On this entire 5-regular class the all-halves fractional orientation realizes $5/2$ everywhere, and the equally weighted mixture of the two legal target values 1 and 4 also has mean $5/2$. Rounding a *fixed integer* target is settled by Hall. Choosing which vertices receive 4 is the outstanding integrality constraint.

## 6. Extent of the search

The first table exhausts connected simple 5-regular isomorphism classes at these orders with minimum cut at least five. For every graph and **every root**, deleting the root and counting all residual boundaries also tests arbitrary compatible preorientations of that root. Once root edges are fixed, subtract their contributions at the remaining vertices. The residual vector ranges over all zero-sum boundaries as the original compatible boundary varies. The last column gives the minimum entry over all those deletion arrays.

| Vertices | Graphs | Minimum count over every graph and boundary | Range of $N(0)$ | Minimum after deleting any root |
|---:|---:|---:|---:|---:|
| 6 | 1 | 80 | 80 | 8 |
| 8 | 3 | 256 | 256–260 | 22 |
| 10 | 60 | 640 | 640–1,090 | 60 |

This covers 1,187,784 whole-graph boundary entries and 3,954,582 residual entries. All are positive. Separately the simple graph atlas contained 1, 4 and 29 graphs of minimum cut at least four at orders 5, 6 and 7 respectively. All their boundary arrays had full support. These finite tests leave the five-edge group-connectivity conjecture unresolved. [Boundary census](scripts/search.py)

The zero-boundary exchange census goes farther. For $n=12$, `geng` generated 7,848 connected simple 5-regular graphs and exact min-cut retained 7,841. The table counts both orders of a bisection. An entry is stalled if $D>0$ and **all** single exchanges have deficit at least $D$.

| Vertices | Eligible graphs | Realizable bisections | Deficient bisections | Stalled |
|---:|---:|---:|---:|---:|
| 6 | 1 | 20 | 0 | 0 |
| 8 | 3 | 134 | 76 | 0 |
| 10 | 60 | 6,724 | 8,396 | 0 |
| 12 | 7,841 | 2,311,048 | 4,934,036 | 0 |

To compute all $D(H)$ exactly in $O(n2^n)$ arithmetic operations per graph, initialize the array indexed by $S$ with $e(S)-|S|$. For each coordinate replace its pair $(a,b)$ simultaneously by $(\max(a,b),\max(a,b-3))$. After $j$ coordinates the processed bits prescribe membership in $H$ and have been maximized over as bits of $S$. The other bits still index $S$. This invariant gives the formula for $D$ after $n$ steps. For arbitrary boundaries in a 5-regular graph replace 1 by the least allowed outdegree $a_v\in\{0,1,2\}$, given by $2a_v-5\equiv\beta(v)$. Start with $e(S)-\sum_{v\in S}a_v$ and take $|H|=(m-\sum_v a_v)/3$. All 243 boundaries of $K_6$ were tested in this version. An independent subset sweep and component matching also agreed on 4,745 pseudoforest bisections in the small-graph panel. Constructed tests separately realize matching deficiencies 1 and 2. The order-12 flow-existence conclusion is covered by earlier small-order theory. [Exchange census](scripts/exchanges.py) · [Direct comparison](scripts/bisections.py) · [Li et al., Lemma 2.14](https://lijiaao-dm-nk.com/pdf/pub/Jiaao08_Nowhere-zero3flow-ind_DM2018.pdf)

| Adversarial family | Exact outcome |
|---|---|
| Petersen, flower $J_5,J_7$ | Cubic, minimum cut 3, no zero-boundary orientation. A nonbipartite cubic graph cannot orient every vertex as a source or sink. |
| Petersen with tripled spokes | 5-regular, minimum cut **4**. A matched pair has cut size 4. There are 1,568 zero-boundary orientations. |
| Petersen with both pentagons doubled | Minimum cut 5, 1,000 zero-boundary orientations. Every boundary is realized. Its tested two-sheet lift also has minimum cut 5. |
| Split $K_5$ | Splitting one vertex and adding three edges between the split vertices still leaves their four-edge cut. The augmented 6-vertex version raises minimum cut to 5 and has 540 zero-boundary orientations. |
| $K_6$ spliced to $K_6$ | Nontrivial five-cut, minimum cut 5, exactly 640 zero-boundary orientations. |
| Three $K_4$ blocks in a ring | Minimum cut 4, 640 zero-boundary orientations. Exactly two of $3^{11}$ valid boundaries fail, the constants 1 and 2. Doubling the six interblock links gives minimum cut 5 and full boundary support. |
| Flower derivatives, repeated splices, random simple graphs | The two flower derivatives obtained by doubling a complementary 2-factor, a 54-vertex six-splice graph, and three seeded graphs at each of orders 16, 24 and 36 had minimum cut 5. Each produced an integer flow and witnesses for 12 sampled valid boundaries. |

For the three-block example label block $i$ by $(i,0),\ldots,(i,3)$ and add $(i,2+j)(i+1,j)$ for $j=0,1$, cyclically. At constant boundary 1 a degree-four vertex needs outdegree 1 or 4. The edge total 24 forces four vertices of outdegree 4. Such vertices form an independent set, and the three cliques allow at most three. Reversal handles boundary 2. This recovers the classical four-edge obstruction to the stronger conjecture. [JLPT (1992)](https://doi.org/10.1016/0095-8956(92)90016-Q) · [Exact construction](scripts/flow_lab.py)

For larger named graphs, SciPy/HiGHS found edge signs using $2By-3t=\beta+B\mathbf1$, with $y$ binary and $t$ integral. Each positive answer is independently checked using integer divergence. An integral max-flow assignment then lifts each zero-boundary witness and the verifier checks its original residues, absolute values and conservation. Reported infeasibilities have separate combinatorial explanations or exact counts. Uniform random graphs are only controls. The known almost-sure result makes them a poor stand-alone test of a universal claim. [Prałat and Wormald](https://math.ryerson.ca/~pralat/papers/2020_Tutte_5reg.pdf)

## 7. What to test at higher reasoning effort

1. **Equal-deficit exchanges.** For zero boundary, test whether every component of the single-swap graph on a positive level $D=d$ contains a state adjacent to a lower level, for simple 5-regular 5-edge-connected graphs. A proof would give termination by descent between finite levels. For an exchange $h\in H$, $l\in L$, the change of $f_H(S)$ is $3(\mathbf1_S(h)-\mathbf1_S(l))$. A strict decrease requires every maximizing shore to contain $l$ and omit $h$, and every shore containing $h$ but omitting $l$ to have old value at most $d-4$. These two conditions are also sufficient. Maximizing shores are closed under intersection and union since $f_H$ is supermodular. Try to shrink their intersection or enlarge their union on a neutral move with a proved termination measure. In the 18-vertex and flower examples every stalled state escaped with one neutral move. There is no general escape proof or bound on the number of neutral moves.
2. **Deficient components of a forest bisection.** The proof in §3 produces a concrete Hall witness and its lifted shore. When the component-size bound fails, attempt an exchange moving vertices across that shore while preserving the forest or pseudoforest conditions and increasing the maximum matching. The 26-vertex witness is a required test for any argument using only the two component counts. Reducing to two forests everywhere already fails on $K_6$. A structural proof must allow unicyclic components or handle a different reducible configuration.
3. **Minority support at an exposed five-cut.** Test the weaker target $|\operatorname{supp}p|\ge3$ first on rooted pieces with only trivial five-cuts. To compose successive cuts, track joint support when two ports or two roots are exposed. The $K_6$ example in §1 rules out replacing joint support by independent marginals. Establishing strict overlap would settle gluing at a separating five-cut. It leaves the existence problem on irreducible pieces. For arbitrary boundary the signed table, including all compatible patterns, is necessary for the counting experiment in §2.

## Reproduction and formal status

Run from the repository root using Python with NumPy, SciPy (including `milp`), NetworkX, and the nauty `geng` executable on `PATH`. This run used Python 3.13.11, NumPy 2.3.5, SciPy 1.16.3, NetworkX 3.6.1 and nauty 2.9.3. The Conda interpreter was used because the system Python lacks the solver dependencies. A solver may return a different valid witness. The counts and cut certificates are independent of that choice.

```sh
/Users/mw/miniconda3/bin/python3 -B scripts/search.py
/Users/mw/miniconda3/bin/python3 -B scripts/bisections.py
/Users/mw/miniconda3/bin/python3 -B scripts/obstructions.py
/Users/mw/miniconda3/bin/python3 -B scripts/exchanges.py
/Users/mw/miniconda3/bin/python3 -B scripts/forest_bound.py
lake build
```

`FinMultigraph.exists_orientation_with_outdegrees_iff` proves the general Hall cut criterion, including loops and parallel edges. `FinMultigraph.exists_intFlow_lifting` starts with the representatives $r_e\in\{1,2\}$, places $r_e$ units at the reference tail and $3-r_e$ at the head, and uses the divisible-by-three column totals as the basis for vertex quotas. Matching each edge to a single endpoint with one third of those vertex totals selects the edges on which to subtract 3. The resulting values conserve exactly and retain their original residues. `FinMultigraph.hasMod3Orientation_iff_hasNowhereZeroIntFlow` combines this with the repository's existing modular equivalence. Both new Lean modules are in the default build. The three public results named here passed an axiom audit with only `propext`, `Classical.choice` and `Quot.sound`. [PrescribedDegrees.lean](Tutte3Flow/PrescribedDegrees.lean) · [IntegralLift.lean](Tutte3Flow/IntegralLift.lean)

The forest-bound test examined 573 candidate partitions inducing two forests, with 571 certified by the inequality, including 84 with mixed sizes. The component-size proposition and deficit identity have mathematical proofs above. The finite census and obstruction certificates are Python results. The frozen file's SHA-256 is `cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6`, matching its starting value.

## 8. MAX Round 1

**Verdict.** The universal intersection of the orientation base with the modular lattice remains open here. The one-neutral-exchange hypothesis from §7 is false. In both families below the *exact* minimum number of neutral exchanges tends to infinity, and each starting quota has deficit one. The second family survives decomposition along every nontrivial five-cut. The search also tested for positive components with no escape, a different and still open question.

### 8.1 Which graphs suffice

Kochol's equivalence applies to loopless **multigraphs**. Its three universal statements concern 4-edge-connected zero-boundary existence, 5-edge-connected zero-boundary existence, and extension of every compatible preorientation of a degree-five vertex in a 5-edge-connected graph. Li also explains the 5-regular reduction using Mader's connectivity-preserving splitting lemma. The arbitrary-boundary extension statement belongs to a separate conjecture. [Li, Theorem 1, the discussion after Theorem 2, and Lemma 3](https://arxiv.org/pdf/2005.00297) · [Kochol, original paper](https://www.sciencedirect.com/science/article/pii/S0095895601920544)

Here is an independent way to justify using **simple 5-regular, genuinely 5-edge-connected** graphs for the universal existence question. Replace each vertex of degree $d\ge5$ by the square $C_d^2$ of a cycle, with one distinct original incidence attached to each new vertex. Every new vertex has degree five. The result is simple even if two old vertices shared parallel edges. A flow orientation on the result projects to a flow orientation on the old graph by summing conservation over each expanded vertex set. Graphs of order at most one are immediate, and deleted loops can be restored with value one.

To check connectivity, a nontrivial cut of $C_d^2$ has size at least four, with equality only when one shore is a singleton. For a shore with $r$ cyclic runs, the cycle contributes $2r$. One run with both shores of size at least two cuts four more distance-two edges. With two runs, zero distance-two crossings would make the indicator constant on each parity class, hence alternating on an even cycle of length at least six, with at least three runs. The distance-two crossing count is even. Now a cut of size at most four in the expanded graph must split exactly one fiber, isolate one port *within that fiber*, and cross no original edge, or come entirely from an old cut. In the split case, move the port to the majority side. Its external neighbor belongs to a different fiber on the old singleton side. Both sides still contain an old vertex, and the old cut has size at most one. Both cases contradict old 5-edge-connectivity. This proves the equivalence for **existence**. We analyze quotas on the original multigraph separately because expansion changes the coordinates. Five tests expanded irregular graphs, parallel bundles and chains to orders 14, 30, 60, 80 and 58, checked their minimum cuts, and projected actual flows. [Expansion and projection checks](scripts/round1_base.py)

### 8.2 The rounded base, its dual witnesses and the maximizing shores

Let $c(S)=|\delta(S)|$, $d_v=\deg(v)$ and $m=|E|$. Throughout, $\sum q_v=m$. A change of coordinates $q=r+3x$, with $r_v$ the least residue of $2d_v$ modulo three, gives lower bounds
\[
 x(S)\ge h(S)=\left\lceil\frac{e(S)-r(S)}3\right\rceil,\qquad
 x(V)=(m-r(V))/3 .
\]
This total is integral by the degree sum. The new Lean theorem proves the exact equivalence with a nowhere-zero integer 3-flow in the frozen representation, including loops and parallel edges. Its natural-number quotas cover every feasible integer quota by the singleton inequalities. [ModularBase.lean](Tutte3Flow/ModularBase.lean)

**Five and seven have the same rounded slack.** The identity $2r(S)\equiv2e(S)+c(S)\pmod3$ gives $e(S)-r(S)\equiv c(S)\pmod3$. If $[a]_3\in\{0,1,2\}$ is the least residue, the center $x^*=(d/2-r)/3$ satisfies
\[
 x^*(S)-h(S)=\frac{c(S)-2[-c(S)]_3}{6}.
\]
At cut sizes $5,6,7,8,9,10$ the respective margins in $x$-coordinates are $1/2,1,1/2,1,3/2,1$. Thus every proper rounded inequality has positive slack for a 5-edge-connected graph. Equivalently, with $a_v=(d_v-2q_v)/3$, feasibility requires $|a(S)|$ at most the largest integer of the parity of $c(S)$ which is at most $c(S)/3$. Both a five-cut and a seven-cut require $|a(S)|\le1$.

All minimum five-cuts can be rounded simultaneously. Choose their shores avoiding a fixed root. If two cross, their four sectors are nonempty. Cut submodularity and its difference-set counterpart force both opposite-sector edge counts to vanish and all four sector cuts to equal five. Write $P=A\cap B,Q=A\setminus B,R=B\setminus A,T=V\setminus(A\cup B)$. Then $|E(P,R)|=|E(Q,T)|$ by subtracting the cut equations for $P,Q$, while their sum is $c(A)=5$, impossible. Thus the shores are laminar. Order all vertices so each laminar shore is an interval, then give the odd-degree vertices alternating $a_v=+1,-1$ in that order and set $a_v=0$ on even degrees. The total vanishes and all five-cuts have $|a(S)|=1$. The corresponding $q=(d-3a)/2$ has the correct total and congruences. The earlier 18-vertex example has a quota meeting every five-cut bound and giving $|a(S)|=3$ on a seven-cut. The test also checks laminarity on three new chains. [Exact shore checks](scripts/round1_base.py)

**A fractional vertex with an integer objective gap.** Use the eight-vertex block in §8.3 in the computational order $h_0,h_1,h_2,l_0,l_1,l_2,s,t$. Here $r=\mathbf1$. A shore is encoded by the sum of $2^v$ over its vertices. The rounded bounds have $h(71)=h(39)=h(103)=1$ and $h(7)=0$, where 103 and 7 encode their union and intersection. Thus $h$ fails supermodularity. More decisively, the vector
\[
 x=(0,0,\tfrac12,1,1,\tfrac12,\tfrac12,\tfrac12)
\]
satisfies the total and all 256 bounds. The tight masks $1,2,39,71,99,135,239,247$ have incidence determinant $-2$. Their sum gives the objective $(7,7,5,1,1,4,4,3)$ with linear minimum 10 at this vertex. The integer minimum is 12, checked over every four-element subset. All feasibility, determinant and objective checks here use integer arithmetic. The graph itself admits a flow. [Fractional vertex certificate](scripts/round1_base.py)

**Exact deficit and dual information.** Put $f_q(S)=e(S)-q(S)$ and $D=\max_S f_q(S)$. For any orientation with tails $p$, put capacities one on its directed edges, join the source to vertices with capacity $(p_v-q_v)_+$ and join vertices to the sink with capacity $(q_v-p_v)_+$. If $\Delta=\sum(p_v-q_v)_+$, the cut with source shore $S$ has capacity $\Delta-f_q(S)$ because $p(S)=e(S)+d^+(S)$, counting arcs leaving $S$ in the last term. Routing an integral maximum flow and reversing each used graph edge gives an orientation with total positive excess exactly $\Delta-\mathrm{maxflow}$. Every orientation has excess at least $D$ by counting tails on a maximizing shore. Hence
\[
 D(q)=\min_{\text{actual outdegree vectors }p'}\tfrac12\|p'-q\|_1 .
\]
This holds even for signed $q$. An alternative min-cut oracle uses an arc of capacity one in each direction on every undirected edge and terminal capacities $w_v^+,w_v^-$ for $w=d-2q$. It gives $2D=\sum w_v^+-\mathrm{mincut}$ from $2f_q(S)=w(S)-c(S)$. The code compares both constructions. [Integer cut oracles](scripts/round1_exchange.py) · [Independent distance check](scripts/round1_base.py)

A finite infeasibility certificate for the *whole* problem is a cover of the bounded, fixed-total modular quota vectors by violated shores. For each $v$ retain $0\le r_v+3x_v\le d_v$. A listed shore excludes precisely the vectors with $x(S)\le h(S)-1$. A certificate consists of the shores and an exact verification that their union covers every candidate. Conversely, infeasibility supplies a shore for every candidate. This gives an exact finite dual with potentially exponential size. The center satisfies even all individually rounded inequalities. The real relaxation with those rows alone therefore cannot produce a Farkas infeasibility certificate.

There is also an algebraic infeasibility certificate using only $m-|V|+1$ variables on a connected graph. Choose a spanning tree and give its chords signs $t_i\in\{\pm1\}\subset\mathbb F_3$. Across each fundamental tree cut, conservation determines its tree-edge residue as a signed linear form $\ell_a(t)$ from the crossing chords. These assignments satisfy every vertex equation by successive elimination of tree leaves. In $\mathbb F_3[t_i]/(t_i^2-1)$ reduce $Q=\prod_{a\text{ in tree}}\ell_a^2$ to squarefree coefficients. The graph fails to admit a flow exactly when **every coefficient is zero**. On the sign cube $Q$ is the indicator of a full nowhere-zero flow, and the evaluation matrix of the squarefree monomials is invertible because it is a tensor power of the two-point sign matrix with determinant $-2$. A verifier can multiply and reduce the factors, retaining all coefficients. This certificate can also be exponential. The computed coefficient vectors vanish identically for cubic Petersen and flower $J_5$, and have respectively 2,141 and 345 nonzero entries on the triangle and digon blocks. An independent sign-cube transform checks every evaluation. [Cycle-space certificate computation](scripts/round1_base.py)

**Which exchanges decrease $D$.** Supermodularity is exact up to $|E(A\setminus B,B\setminus A)|$. Thus the maximizing sets have an intersection $P$ and a union $M$, both maximizing. They are the least and greatest source shores of a minimum cut in the symmetric network. For a nonempty $T\subseteq P$ and a nonempty $U\subseteq V\setminus M$, strict extremality gives
\[
 e(T)+|E(T,P\setminus T)|-q(T)\ge1,\qquad
 q(U)-e(U)-|E(U,M)|\ge1 .
\]
In particular $\deg_P(u)\ge q_u+1$ for $u\in P$, and $q_w\ge\deg_M(w)+1$ outside $M$. For $D>0$ both $P$ and $R=V\setminus M$ are nonempty. The stronger aggregate equalities are $3a(P)=2D+c(P)$ and $3a(R)=-2D-c(R)$, so both magnitudes are at least $(2D+5)/3$. At $D=1$ a maximizing shore has cut size $1\bmod3$, at least seven.

For $u\ne w$, let $b=D-\max_{w\in S,\ u\notin S}f_q(S)$. The move $q+3\mathbf e_u-3\mathbf e_w$ is nonincreasing exactly if $b\ge3$. It strictly improves exactly if $u\in P$, $w\notin M$ and $b\ge4$. Indeed only shores receiving $w$ without $u$ gain three, and every old maximizer must lose three for strict descent. A shore at **$D-3$** can therefore block strict descent too. The script checks every ordered exchange against every shore on small new instances, including signed quotas. On a fixed sublevel $D\le t$ the singleton and complementary bounds give $-t\le q_v\le d_v+t$, so every component is finite. Connectivity to a lower level remains unproved. [Tests of extremal shores and exchanges](scripts/round1_exchange.py)

### 8.3 Five-cut chains with an exact exchange distance

**Theorem.** For every $k\ge1$ there is a simple 5-regular 5-edge-connected graph on $6k+2$ vertices with a modular quota $q$ of deficit one whose nearest feasible quota takes exactly $\lceil k/2\rceil$ exchanges. A path attaining that distance has deficit one until its last step. The same distances occur in nonregular 5-edge-connected multigraphs.

Here is the simple block and a finite orientation certificate for constructing the shortest paths. Its vertices are $s,t,h_0,h_1,h_2,l_0,l_1,l_2$. Take high and low triangles, the four edges $h_0l_2,h_1l_2,h_2l_0,h_2l_1$, and two stars. The $s$-star meets $h_0,h_1,h_2,l_0,l_1$ in that order. The $t$-star meets $h_0,h_1,l_0,l_1,l_2$. Give the high vertices quota four and the low vertices quota one, with $q_s=1,q_t=4$. Orient each triangle cyclically in index order and the other edges from high to low, high to terminal, or terminal to low. This realizes $q+\mathbf e_s-\mathbf e_t$. Since the graph is simple 5-regular on eight vertices, a smaller shore of size $j=1,2,3,4$ has cut at least $5j-j(j-1)\ge5$.

In $k$ copies delete each $t_i,s_{i+1}$ and pair the five stubs in the permutation $0,1,2,3,4\mapsto3,4,0,1,2$. Opposite senses at the two deleted tips give a consistent orientation of every new edge. Outer terminals keep their original quotas. The result is simple, and each splice preserves 5-edge-connectivity. To see this for *any* matching of five ports, a cut splitting the interiors of both halves has at least three internal edges across it on each side. Indeed if a split has $b$ internal crossing edges and $r$ of the five ports on one side, the completed graph gives $b+r,b+5-r\ge5$. A cut splitting only one interior has the size of a cut in that completion. A cut between intact interiors has size five.

In any modular orientation of the chain the net divergence at each virtual terminal is zero modulo three, by summing conservation on a shore of its interface. If all interior quotas in one block are retained, the high triangle uses the three available high indegrees internally, and the low triangle uses the three available low outdegrees internally. Every star incidence is forced. The virtual $s,t$ would have outdegrees two and three, contrary to conservation modulo three at degree five. At least one interior coordinate in **every block** must change. This proves $D>0$, and the displayed tail discrepancy proves $D\le1$. An exchange touches at most two blocks, giving the lower bound even for unrestricted intermediate quotas or paths temporarily increasing $D$.

For the upper bound use two orientations $A,B$ of the block. Number the edges from zero, starting with the four listed high-low edges and then the three high cycle edges, the three low cycle edges, the $s$-star and the $t$-star. Relative to the displayed orientation, reverse edges $9,13,17,19$ for $A$, and $4,5,10,12,15$ for $B$. Direct counting gives these tails.

| Block orientation | $s,t$ outdegrees | Changed interior quota |
|---|---|---|
| $A$ | $1,1$ | $l_0$ gains three |
| $B$ | $4,4$ | $h_0$ loses three |

The $A$-to-$B$ and $B$-to-$A$ interfaces match under the permutation above. At a $B$-to-original interface just **one** wire disagrees, where the virtual $t$ now sends into its own block. Replace the first two original blocks by $A,B$ in one exchange, and repeat from the left. At the exposed interface use the direction required by the repaired prefix. This gives one excess tail at the first unresolved block and one missing tail at the final $t$. The deficit is at most one throughout. For odd $k$, replace the last block by $A$ and move three units from the outer $t$ to its $l_0$. All final quotas are realized. The lower bound proves the asserted length and rules out an earlier decrease.

One nonregular version identifies consecutive tips, retaining their five incidences on each side and adding their quotas. Its shared vertices have degree ten and quota five. One-vertex sums preserve 5-edge-connectivity. Conservation on the components at a shared vertex forces balance separately on each side. The same proof works, with the single excess at the shared tip of a repaired prefix. The script also supplies a six-vertex block using high and low digons, with both gluing operations and explicit repairs. For the simple 32-vertex spliced example, in script order the recipient-donor pairs $(4,7),(16,20),(21,25)$ give deficits $1,1,1,0$ including the initial state. A separate binary orientation optimization finds the same distance. Here $P=\{3,4,5,30\}$ and $V\setminus M=\{24,25,26,31\}$. All 34 neutral first moves have $|P'|\ge |P|$ and $|M'|\le |M|$. Shrinking the least maximizing shore or enlarging the greatest one at each neutral step already fails in this example. [Block definitions, edge certificates, paths and independent optimization](scripts/round1_exchange.py)

### 8.4 Unbounded delay even when every nontrivial cut has size at least seven

**Theorem.** For every positive odd $k$ there is a simple 5-regular 5-edge-connected graph on $18+12k$ vertices, with smallest nontrivial cut seven, an edge $e=xy$, and a balanced modulo-three orientation $D_0$ of $G-e$, with two properties.

1. Every repair of $D_0$ inserting $e$ reverses a set of arcs whose **integer** divergence is nonzero at some vertex of each of the $k$ intermediate blocks. Exactly $k$ such intermediate vertices suffice, even with one degree-five star held fixed.
2. A legal quota of deficit one requires exactly $(k-1)/2$ neutral exchanges before a strict decrease. Thus eliminating separating five-cuts does not restore any constant exchange bound.

**Construction and certificates.** Take two nine-vertex end blocks and $k$ twelve-vertex intermediate blocks in a path. Join neighbors by matchings of size six, and put the one additional edge $xy$ between the ends. Within $G-e$, orient the six edges at every interface uniformly. Alternately, an intermediate block receives both adjacent matchings or sends both. The ends send and the first and last intermediate blocks receive. The fixed lists of directed edges, including all internal orientations, are the three small constants in the script. Each end has six distinct matching ports, two internal degree-five vertices and the remaining vertex $x$ or $y$ of internal degree four. Each intermediate vertex has internal degree four and is incident to one matching edge. The lists give zero divergence modulo three after attachment and before inserting $e$. These local statements depend on just three templates for all $k$. [Oriented templates and attachment order](scripts/round1_repair.py)

Every nonempty proper internal cut of a template has size at least four, and every internal cut with at least two vertices on both sides has size at least six. These are finite integer certificates over $2^9,2^9,2^{12}$ subsets, respectively. The full graph has degree five throughout. A cut splitting two templates costs at least eight. A cut splitting none crosses at least two whole matchings, or crosses a matching and $xy$. Suppose it splits exactly one and costs at most six. No interface between whole blocks can cross, as the partial block already contributes four. If the partial block separates a singleton internally, any neighboring whole block opposite the majority contributes at least five matching edges in addition. All whole blocks must therefore agree with the majority, giving a singleton global shore. If both internal sides have size at least two, the internal cost is at least six, leaving no crossing external edges. The whole blocks agree, including across the two sides of a partial intermediate block because $xy$ cannot cross. Vertices of the partial block on the opposite shore have no external incidences. This leaves no intermediate vertices and at most two end-block vertices. Two such end vertices have internal degrees five and contribute at least eight. This exhausts the cuts. A prefix containing one end gives a seven-cut, so the bound is attained.

**Why changing one path or a bounded number of vertices cannot work.** Let $F$ be the arcs reversed to get any full orientation, with either choice for $e$. Reversing changes the divergence by $-2\partial_{D_0}F\equiv\partial_{D_0}F\bmod3$. On each consecutive prefix of $G-e$ the required change is nonzero because $xy$ crosses that prefix. At least one edge of *each* of the six-edge matchings belongs to $F$. In a receiving intermediate block all these selected boundary arcs enter, and in a sending block all leave. Their signed sum is a nonzero multiple of three by conservation. At least one interior vertex in that block has $\partial_{D_0}F(v)\ne0$ over the integers. At a nonterminal vertex a reversal changes its outdegree by $-\partial_{D_0}F(v)$. Thus every full orientation changes at least $k$ distinct interior outdegrees. A directed path alone has zero integer divergence at all its interior vertices.

**Explicit upper bound and exchange path.** Use exactly the selected template edges in the following table. Indices are zero-based in the directed lists in the script. The six positions along each matching are also zero-based. Each receiving block uses its six left ports and six right ports in the given order. A sending copy reverses the template and interchanges its left and right interfaces so that like port lists meet.

| Template | Selected internal edges | Selected matching positions |
|---|---|---|
| Left end | $1,13$ | $0,4$ |
| Right end | $2$ | $0$ |
| Intermediate | $0,1,6$ | $0,4$ at the left-port list, $0$ at the right-port list |

The selected set has integer divergence two at $x$, one at $y$, and exactly one vertex of divergence $-3$ in each receiving block and $+3$ in each sending block. All other divergences vanish. The designated root, vertex 24 in the first intermediate block, meets no selected edge. These assertions can be checked by adding the signed incidences in each template. Reverse the selected set and insert $x\to y$ to obtain a full flow orientation. This gives the upper bound in part 1.

Orient $e$ initially as $x\to y$, write $p$ for the resulting actual outdegrees, and start with $q=p+\mathbf e_x-\mathbf e_y$. The endpoints had outdegree two in $G-e$, so $q_x=4,q_y=1$ and all quotas are legal. The orientation witnesses $D(q)\le1$. The interior lower bound proves $D(q)>0$ and that every exchange path to a feasible quota has length at least $\lceil k/2\rceil$. For a path of that length, correct pairs of intermediate blocks from the **right**. Each step raises the quota at the designated receiving vertex by three and lowers it at the adjacent sending vertex by three. To check the deficit, apply the selected reversals throughout the right end and the corrected suffix, including the selected wire across its left boundary. There is only one selected wire across that boundary, directed out of the suffix before reversal. The old quota deficit of one tail at $x$ remains, and the opposite excess now sits just outside the corrected suffix. This argument also applies to the initial suffix consisting only of the right end. The final step raises the designated vertex of the leftmost receiving block and lowers $x$ by three. It realizes the full orientation above. This proves the exact nonincreasing distance. The script verifies minimum cuts, the complete repaired orientations and every deficit along these paths at orders 30, 54, 78 and 102. [Unbounded seven-cut construction and verification](scripts/round1_repair.py)

The bisection characterizations and results on graphs with forbidden cut sizes cited in §§1–3 concern existence of suitable orientations or partitions. The exchange distances here concern a specified *infeasible* quota and the intermediate states needed to repair it. I found no prior result asserting these distances in the sources checked. Historical priority for the constructions is unverified. [Ahanjideh–Kovács](https://arxiv.org/abs/2603.24175) · [Li–Li](https://arxiv.org/abs/2609.08377) · [Jafari](https://arxiv.org/abs/2611.03763)

### 8.5 What a missing port would prove

The five-cut composition in §2 and connectivity proof in §8.3 validate the proposed disjoint-support construction. If two completed rooted halves have support sizes summing to at most five, make the supports disjoint by a permutation. The resulting graph is 5-edge-connected and has zero orientations. Two copies suffice for a half with support size at most two.

In fact **one missing minority position**, even with four other positions available, suffices to build a counterexample. This follows from Kochol's rooted equivalence and has a direct construction using Li's minority-edge argument. Take a $K_6$ with a center $c$ and five other vertices. In any balanced orientation reverse all edges if needed so $c$ has outdegree one. If every spoke were a majority edge at its other endpoint, the four neighbors directing into $c$ would each have outdegree four. The remaining neighbor and $c$ would have outdegree one. This gives total outdegree 18 for 15 edges. Replace each of the five neighbors by a copy of the deficient rooted half, by a five-splice matching its missing position to the old spoke. These splices preserve 5-edge-connectivity. A full orientation would restrict to a valid state on each copy by cut conservation. Contracting the copies would orient the skeleton with each of its five spokes a majority edge at its neighbor, impossible. This construction keeps the center as a single vertex. The script checks the skeleton property directly. [Li, Lemma 1(i) and proof of Theorem 1](https://arxiv.org/pdf/2005.00297) · [Amplifier and support tests](scripts/round1_ports.py)

**An infinite class in which both distant star prescriptions extend.** For the simple triangle block and the parallel digon block of §8.3, enumerate the ten signed states at each of the two distinguished tips. With the internal quotas released, the $10\times10$ feasibility tables contain respectively 82 and 66 positive entries. The minimum row and column supports are respectively 8 and 6. These are exact finite certificates obtained by enumerating every orientation of the free internal edges, cross-checked by a separate vertex-constraint solver. Two subsets of ten states, each of size at least six, intersect after *any* signed port relabelling. Consequently any serial chain of **two or more** such blocks, mixing either type and using arbitrary permutations, extends *both* outer star prescriptions simultaneously. The Boolean product of the first two tables is full, and multiplying by another table with no empty column preserves fullness. The 480 ordered block-pair/permutation products and 800 direct simultaneous two-root tests also verify the two-block step. This explains why the quota obstruction of §8.3, even at great length, produces no forbidden outer state. [Exact transfer certificates](scripts/round1_ports.py)

### 8.6 Search coverage and formal checks

These experiments address new instances and new predicates. Counts refer to construction instances and labelled roots, with no isomorphism deduplication. Each positive port test returns edge signs checked by integer arithmetic. One zero-boundary witness per construction also receives an independently verified integer lift.

| Five-port search | Graph instances | Roots checked | All five positions extended |
|---|---:|---:|---:|
| Flower $J_5,J_7,J_9$ with doubled 2-factor | 12 | 88 | 440 |
| Petersen-derived covers on 2, 3 or 4 sheets | 8 | 64 | 320 |
| Random simple 5-regular graphs | 22 | 188 | 940 |
| Irregular graphs with extra edges | 22 | 135 | 675 |
| Randomly permuted five-sums | 24 | 182 | 910 |
| Chains with cut vertices | 8 | 64 | 320 |
| Augmented split $K_5$ joined to Petersen derivatives | 8 | 60 | 300 |
| **Total** | **104** | **781** | **3,905** |

Every graph passed an independent minimum-cut test. Reversal supplies the complementary signed prescriptions. Each of the 104 graphs also passed a compatible pinned-star test at a separately sampled boundary. These finite results give no universal lower bound on minority support. [Port search](scripts/round1_ports.py)

On 62 construction instances of orders 20 through 40, 620 quotas included nearest-center sign assignments and random modular exchanges allowed to leave the degree box. Of these, 107 were feasible at the start, 512 decreased by a single exchange and one needed a neutral step. For the separate new structured examples, the exchange distances are proved in §§8.3–8.4. [Quota stress tests](scripts/round1_base.py)

For a **complete test of trapping** on a smaller targeted panel, take every modular quota of correct total in $-1\le q_v\le d_v+1$. This includes every possible state at $D\le1$. Maximize over all shores with a tensor transform and compute breadth-first distance from *all* feasible states using unrestricted single exchanges inside that sublevel. The graphs here were newly constructed from the terminal blocks.

| Family | Instances | $D=0$ | $D=1$, one move to zero | $D=1$, two moves to zero | Trapped $D=1$ states |
|---|---:|---:|---:|---:|---:|
| Rings of parallel blocks | 10 | 8,016 | 16,408 | 0 | 0 |
| Rings of simple blocks | 3 | 16,826 | 36,948 | 0 | 0 |
| Open chains | 4 | 6,794 | 8,558 | 68 | 0 |
| Irregular chains | 8 | 19,034 | 59,320 | 524 | 0 |

This settles escape for those 121,826 positive states. On the larger panel the general search sampled starting states. There is no proof that every positive level component in every 5-edge-connected graph has an exit. [Complete sublevel search](scripts/round1_levels.py)

The five new scripts can be run independently from the repository root. Dependencies are Python, NumPy, SciPy, NetworkX and SymPy. The earlier isomorphism census is unnecessary.

```sh
/Users/mw/miniconda3/bin/python3 -B scripts/round1_exchange.py
/Users/mw/miniconda3/bin/python3 -B scripts/round1_base.py
/Users/mw/miniconda3/bin/python3 -B scripts/round1_levels.py
/Users/mw/miniconda3/bin/python3 -B scripts/round1_ports.py
/Users/mw/miniconda3/bin/python3 -B scripts/round1_repair.py
lake build
```

The default Lean build completes with zero errors. Three new results passed the axiom audit with only propositional extensionality, classical choice and quotient soundness. They are the modular base criterion, the pinned one-edge transfer equivalence, and its integer 3-flow specialization with all old edges free. The distance theorems have mathematical proofs with executable finite template certificates. The frozen challenge SHA-256 still matches the value recorded above. [ModularBase.lean](Tutte3Flow/ModularBase.lean) · [EdgeInsertion.lean](Tutte3Flow/EdgeInsertion.lean)

### 8.7 Single target for MAX Round 2

**Prove rooted one-edge insertion on graphs with only trivial five-cuts.** Let $G$ be a loopless 5-edge-connected multigraph with no nontrivial five-cut, $z$ a degree-five vertex with a fixed compatible zero-boundary star, and $e=xy$ an edge away from $z$. Given a balanced orientation $D_0$ of $G-e$ agreeing at $z$, prove there is a subset $F$ of the arcs of $D_0$, using no edge at $z$, such that
\[
 \partial_{D_0}F \equiv \mathbf e_x-\mathbf e_y
 \quad\text{or}\quad
 \partial_{D_0}F \equiv \mathbf e_y-\mathbf e_x \pmod3 .
\]
The entries of $F$ are zero or one. Reversal changes divergence by $-2\partial_{D_0}F$, so a suitable orientation of $e$ finishes the flow. Conversely any completion with the prescribed star determines such an $F$ by its reversals. Thus a proof may start with *any* given partial orientation and may reorganize it globally. Lean proves this equivalence for arbitrary pinned old edges, with a corollary in the frozen integer-flow language when all old edges are free. Independent enumeration compared both sides on 160 tiny pinned instances, including loops and 38 infeasible instances. [Formal equivalence](Tutte3Flow/EdgeInsertion.lean) · [Assignment counts](scripts/round1_repair.py)

**Why this one target suffices.** If Tutte fails, take a smallest rooted zero-boundary obstruction by vertex count, using Kochol's equivalence. A nontrivial five-cut gives two strictly smaller 5-edge-connected completions. On the side of $z$ extend its given star by minimality, then use the induced cut directions to prescribe the new degree-five root on the other side. The two solutions glue. Hence the obstruction has only trivial five-cuts. There must be an edge $xy$ away from $z$, since otherwise degree five at $z$ and minimum degree five permit at most two vertices, where the prescribed star works. Contract $x,y$ and discard loops. The smaller graph preserves all surviving cuts and the star at $z$, and therefore has a compatible orientation. Reopen $x,y$. Their remaining divergences are opposite modulo three. Two or more parallel $xy$ edges can realize every residue at $x$ and would finish the flow. For a single $xy$ edge, a nonzero divergence selects a direction for it and finishes the flow as well. In the only unresolved case both divergences vanish. This is precisely the partial orientation required by the target. The converse implication follows from the rooted equivalence and the reversal identity. The unrooted deletion step is already known for 3-flow-critical graphs. Root-respecting contraction also occurs in work on flow-critical canvases. [Li et al., Theorem 2.3(i)](https://arxiv.org/pdf/2003.09162) · [Árnadóttir et al., flow-critical canvases](https://arxiv.org/abs/2502.01451) · [Kochol's equivalence as stated by Li](https://arxiv.org/pdf/2005.00297)

A directed path between $x,y$ in either direction avoiding the fixed star supplies such an $F$. Among 192 sampled edge deletions and star choices on 64 graphs verified to have only trivial five-cuts, all 192 had both a partial orientation and a full extension. In 29 of the first partial witnesses neither directed path existed. Section 8.4 proves that a bounded number of vertices with nonzero integer divergence in $F$ cannot suffice either. The remaining question is whether cut connectivity guarantees a **modulo-three** unit transfer with arbitrarily many such vertices. A proof of this single statement would settle the frozen conjecture. [Deletion tests and exact adversarial family](scripts/round1_repair.py)
