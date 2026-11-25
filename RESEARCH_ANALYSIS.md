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

## 9. MAX Round 2 — Final Verdict & Publishable Takeaways

**Case C, 25–26 November 2026, Seoul.** The rooted insertion statement of §8.7 remains open. The strongest result of this round is an exact separation on the simple seven-cut family. At the *same* missing edge and with the *same* fixed star, the minimum number of arcs in a transfer is $(7k+9)/2$ from the designated partial orientation and $2k+3$ when the partial orientation can be chosen. A directed path attains the latter. In the original orientation, minimizing the number of branch vertices instead costs exactly one extra edge. A different four-vertex example proves that, even with free choice of partial orientation, a specified edge can require branching. The family has a mathematical proof and executable certificates. Lean also verifies the general reorientation identity, the four-vertex example, and exclusion of a tight one-branch port sequence at every odd chain length.

### 9.1 What a failed transfer would certify

Write $A=E(G-e)\setminus\delta(z)$, orient it by $D_0$, and write $B$ for its incidence matrix, with the positive sign at the tail. All equations in this subsection are over $\mathbb F_3$ unless integer divergence is specified.

**Changing the partial orientation.** If $T\subseteq A$ is reversed, then for every $F\subseteq A$,
\[
 \partial_{D_0^T}F=\partial_{D_0}(F\mathbin\triangle T)-\partial_{D_0}T.
\]
This follows edge by edge. Changing a unit orientation on $T$ changes its total divergence by $-2\partial T=\partial T$. Thus two partial orientations with the same pins and boundary have exactly the same attainable subset divergences, with exactly the same number of subsets attaining each one. Symmetric difference gives the bijection. The sizes of corresponding subsets can differ. A reversal preserving *integer* outdegrees also preserves ordinary vertex reachability. Indeed the outgoing count of every shore is its sum of outdegrees minus its internal edge count. The shores with zero outgoing edges determine reachability. Consequently ordinary directed cycle reversals alone cannot make an incomparable terminal pair comparable. [Lean reorientation identity and attainable-set theorem](Tutte3Flow/TransferReorientation.lean) · [Finite checks](scripts/round2_structure.py)

**A criterion after identifying the terminals.** Let $C$ be the incidence matrix obtained from $B$ by merging rows $x,y$. Retain the separate original row $\ell=B_x$. Put
\[
 U=\operatorname{span}_{\mathbb F_3}\{b\in\{0,1\}^{A}: Cb=0\}.
\]
Failure of both signs of transfer is equivalent to $\ell|_U=0$. Indeed the only possible nonzero entries of $Bb$ when $Cb=0$ are opposite entries at $x,y$. If the linear functional is nonzero on the span, it is nonzero on at least one of the binary generators. Replacing $U$ by the entire ordinary cycle space loses the binary requirement. This gives an exact obstruction, with the cost of checking the generators still present.

A transfer $F$ is inclusion-minimal among transfers **of either sign** exactly when its contracted columns sum to zero and have no nonempty proper zero-sum subset, provided $\ell(1_F)\ne0$. A proper contracted zero-sum subset with nonzero split imbalance already transfers. One with zero split imbalance can be deleted. In particular the uncontracted support is connected, contains both terminals, and has no directed cycle. To see connectivity, the sum of all vertex divergences in each component is zero, so both terminals lie together and any other component can be deleted. On the contracted support itself the only two balanced unit orientations are the given one and its global reversal, since the reversed arcs of any other such orientation would give a proper zero sum.

If $v$ vertices meet a minimal transfer, then $|F|\le 2v-3$. The contracted incidence columns lie in a space of dimension at most $v-2$. Removing one gives a zero-sum-free sequence. In the group ring of $\mathbb F_3^r$ over $\mathbb F_3$, put $u_i=X^{e_i}-1$ for the standard generators. Then $u_i^3=0$, and every $1-X^g$ belongs to the ideal generated by the $u_i$. A product of more than $2r$ such factors vanishes. For a zero-sum-free sequence its coefficient at the identity is 1. This proves the bound, an application of the classical Davenport constant. Equality is possible for general directed supports. Double the arcs of a consistently directed $r$-edge path and add a forward shortcut. Split its source into $x,y$, putting just one of the two first arcs at $x$. After identifying $x,y$ all bundle counts have one common residue. The shortcut bit forces either all counts zero or all counts two. The full set is a transfer and has $2r+1=2v-3$ edges. This sharpness example makes no connectivity assumption. [Group-algebra background](https://math.smertnig.at/paper/davenport_const.pdf) · [Exhaustive checks and sharp directed examples](scripts/round2_structure.py)

**How branching can realize a transfer.** At every vertex outside $\{x,y,z\}$ partition the incident arcs into pairs consisting of one incoming and one outgoing incidence, and triples all entering or all leaving. Such partitions exist by modular balance, by pairing opposite incidences until one sign remains. Regard the arcs as objects joined whenever their incidences belong to the same group. Leave incidences at the three distinguished vertices unpaired. A transfer exists exactly when some choice of these partitions produces a component avoiding the root edges with nonzero divergence at $x$. Each component balances at the ordinary vertices. Conversely, given a transfer, the selected and unselected incidences each balance there and can be partitioned separately. At least one selected component transfers. For a minimal transfer this recovers the whole support as one component. This explains the local operations allowed at a branch. The unresolved step is choosing the partitions so that a component carries a unit across the specified terminals without touching the star. [Checks on all 29 minimum supports](scripts/round2_structure.py)

### 9.2 The 29 incomparable witnesses and a fixed-edge obstruction

The original seed and solver reconstruct all 29 initial orientations of §8.7. The following table reports minima over **both** transfer signs. The second row also optimizes over balanced orientations of $G-e$ with exactly the same root star.

| Minimum support size | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Original orientation | 0 | 0 | 1 | 5 | 14 | 6 | 2 | 1 |
| Free partial orientation, same edge | 6 | 14 | 5 | 3 | 1 | 0 | 0 | 0 |

One chosen minimum support per original instance has one internal vertex of nonzero integer divergence in 11 cases and two in 18 cases. Each such divergence is $+3$ or $-3$. Other minimizers can tie. The certificate file gives one row per witness, including the original labelled edges, root, minority position, deleted edge, partial reversals, selected edges and integer divergences, together with the optimized one-branch support when it exists, the directed geodesic and its alternative partial orientation. The primary minimizer exhausts successively larger support budgets. At a vertex with wrong residue it branches over all consistent subsets of remaining incidences. Its lower bound sums necessary incidences and charges at most two per selected edge. An independent binary integer program with integral divergence multiples and a terminal-sign bit returned the same 29 optima. Reversing the recorded edges and inserting the signed missing edge was checked directly in each case. [All 29 certificates](scripts/round2_witnesses.json) · [Reconstruction, exact search and independent MILP](scripts/round2_transfers.py)

The one-branch restriction can also be optimized exactly. For each possible branch $v$ and each allowed pair of nonzero terminal imbalances $a,b$ with $a+b\equiv0\pmod3$, prescribe integer divergences $a,b,-a-b$ at $x,y,v$ and zero elsewhere, with $a+b\ne0$. An integral minimum-cost flow with unit arc capacity and unit edge cost gives the least support for that triple. The degree bounds make the enumeration finite. A transfer with no internal branch would contain an ordinary directed terminal path by integer flow decomposition, excluded by the choice of all 29 witnesses. Fourteen admit one branch at the unrestricted minimum. Of the other fifteen, two need one extra arc, five need two extra, three need three extra, and **five admit no one-branch transfer at any size**. Those five require exactly two since the stored certificates attain two. Full subset enumeration independently checked this minimum-cost method on all 128 orientations of a small multigraph. [Constrained optima](scripts/round2_transfers.py) · [Independent subset tests](scripts/round2_structure.py)

For a simple undirected bypass $P$ of $e$ avoiding $z$, there is an admissible partial orientation directing all of $P$ if and only if $G-E(P)$, with $e$ retained, admits the prescribed star. Substitute the directed path for $e$ or the directed edge for the path. Their integer terminal divergences agree. In the resulting partial orientation, reversing $P$ and inserting $e$ in the direction opposite to the old path produces the full extension. Every transfer has size at least the undirected terminal distance in $G-e-z$, by connectivity of its support. All 29 cases realize this lower bound by a directed geodesic, which proves the second row without an optimization assumption. [Path substitution and direct sign checks](scripts/round2_paths.py)

**An edge that genuinely needs a branch.** On vertices $z,x,y,w$, take two copies each of $zx,zy,wx,wy$, and one copy each of $zw,xy$. Fix both $x\to z$, both $y\to z$, and $z\to w$. Every singleton cut has size five and every two-against-two cut has size six or eight. Delete $xy$. At $x$ and $y$ the two pinned outgoing arcs force both remaining arcs inward, since a balanced degree-four vertex has outdegree two. The partial orientation is unique, and both terminals are sinks. Selecting both $w\to x$ arcs and one $w\to y$ arc transfers a unit. Any selected free arc leaves $w$, so a nonempty transfer uses a positive multiple of three arcs. The optimum is three. Taking one of the parallel $wx$ edges as the missing edge instead admits a one-arc repair. The example refutes the fixed-edge path assertion even after reorientation. In a vertex-minimal failed rooted instance, parallel edges away from $z$ are already reducible by §8.7. [Lean certificate including the integer 3-flow](Tutte3Flow/TransferExample.lean) · [Both edge choices in Python](scripts/round2_boundaries.py)

### 9.3 Exact cost on the seven-cut family

**Theorem.** For each positive odd $k$, use the graph on $18+12k$ vertices from §8.4, its edge $xy=(6,15)$, and the original star at $z=24$. The exact minimum transfer support for its displayed orientation of $G-e$ is $(7k+9)/2$. The minimum over all admissible partial orientations at that same edge is $2k+3$.

For the first lower bound let $r_0,\ldots,r_k$ be the numbers of selected arcs in the six-edge matchings between consecutive blocks. Each matching is uniformly oriented in the original. The prefix ending at it contains just one charged terminal. Thus $r_i$ is nonzero modulo three. At every intermediate block the two matchings are both entering or both leaving, so $r_i+r_{i+1}$ is a positive multiple of three. Pair the $k+1$ matchings consecutively. This costs at least $3(k+1)/2$ arcs. Every intermediate block has at least three distinct selected boundary vertices, each with exactly one boundary incidence. One internal edge could balance at most two of them. This costs at least $2k$ internal arcs. Each end needs an internal arc at its terminal. Moreover the two end matching counts have opposite residues since there are $k$ intermediate blocks and $k$ is odd. One end therefore has at least two selected ports. Its terminal is distinct from all its ports, so a single internal edge incident to the terminal cannot balance them both. The end blocks together cost at least three. Adding the bounds gives $(7k+9)/2$.

Here are the matching upper certificates in the zero-based local ordering of §8.4. For the original orientation use internal edges $\{1\}$ in the left cap, $\{1,14\}$ in the right cap, and $\{5,22\}$ in every middle. On each interface of the local left-port type use index 0 and on each right-port interface use indices 0 and 4. For the freely chosen orientation the directed path uses internal edge 1 in the left cap, edge 14 in the right, and edge 5 in every middle. Its interface indices are respectively 0 and 4 for the two types. The full list of new orientation signs is in the certificate. The incident signs at the root stay fixed. To verify the repetition for arbitrary $k$, each internal vertex sees just its local template and its labelled matching incidence. Every middle is the displayed middle or its global reversal, with its matching incidences reversed along with it. Each same-type interface joins identical port labels in the two adjacent copies. The end caps meet the two fixed end types. Checking these local balances, signs and the two terminal residues therefore proves both constructions for all odd $k$. [Block lists and port order](scripts/round1_repair.py) · [Repeating sign and support certificates](scripts/round2_chain.py)

Any undirected bypass uses at least $k+1$ matching edges, at least one internal edge in each middle because its left and right ports are disjoint, and one internal edge at each terminal. Thus no choice of orientation can improve on $2k+3$. Direct checks at $k=1,3,5,7,9,15$ give the pairs $(8,5),(15,9),(22,13),(29,17),(36,21),(57,33)$. The proof uses arbitrary-length cut counts. The finite checks exercise both template parities and the special case where both caps meet the same middle. [Exact transfer certificates](scripts/round2_chain.py)

**Exact tradeoff between support and branching.** Count as a branch each vertex outside $\{x,y\}$ with nonzero *integer* divergence in the selected arcs. In the original orientation the two undominated pairs (branches, support) are
\[
 \left(k+1,\frac{7k+9}{2}\right),\qquad
 \left(k,\frac{7k+11}{2}\right).
\]
In particular the shortest fixed-reference repair necessarily has at least one more branch than the least branching possible.

Each middle must have a branch since its selected external arcs all have the same direction and their count is positive. If there are exactly $k$ branches, each middle has one and both caps have none away from the terminals. The degree bound five makes the nonzero integer divergence there exactly $\pm3$. Consequently every two consecutive interface counts sum to three. They alternate between one and two. For equality in the unrestricted support bound each middle must use two internal edges and each cap must use exactly as many internal edges as it has selected ports. Equality at a cap requires the arcs directly from its terminal to each selected port. With the middle in its receiving orientation, two internal edges must lead from two of the three selected ports into the third. Indeed every selected port needs an incident internal edge, and a branch outside the three would need three incoming internal edges. Global reversal gives the identical two-edge test for a sending middle.

This leaves a finite port calculation valid for every length. A left or right state lists the *positions* of the selected ports in the two ordered lists of §8.4. A pair of states is allowed exactly when their three corresponding vertices in the middle contain the two arcs just described. The first middle also avoids vertex 6 of its template, the pinned root. Start with the direct-arc states of the left cap. From the first reachable right states, close under alternately traversing the allowed pairs right-to-left and left-to-right. The following table gives that entire right-state closure, so it bounds reachability for any positive odd $k$.

| Number selected at the left cap | Possible initial left states | First reachable right states | All reachable right states | Right states needed by the other cap |
|---:|---|---|---|---|
| 1 | $\{0\},\{4\}$ | $\{0,4\}$ | $\{0,4\},\{4,5\}$ | $\{0,1\}$ |
| 2 | $\{0,4\}$ | none | none | $\{0\},\{1\}$ |

For instance the first row can reach only the left state $\{0\}$ when going back from the first right state, and its only right neighbors are $\{0,4\}$ and $\{4,5\}$. Neither row reaches a compatible final cap state. Thus a $k$-branch transfer needs at least one extra edge. The certificate at the unrestricted minimum above has exactly $k+1$ branches. For the other pair, take cap edges $\{1,13\}$ and $\{2\}$, first-middle edges $\{0,1,6\}$ and edges $\{0,6\}$ in every later middle. Select positions $\{0,4\}$ at the left cap, $\{0,1\}$ on every later left-type interface and $\{0\}$ on every right-type interface. The first middle routes three units using three internal arcs, all others use two. Each has precisely one branch, with none in either cap. This attains the bound, including $k=1$. Lean verifies the middle table and proves by induction that no such chain reaches a direct right cap. The audit compares the Lean arc lists, port maps and cap states against the Python graph generator. The reduction from graph transfers to these states is the mathematical argument above. A second computation independently minimizes edge cost on the templates for every possible branch location and propagates the costs for all 51 odd lengths up to 101. [Lean port table and arbitrary-length induction](Tutte3Flow/TransferTemplates.lean) · [Supports and independent minimum-cost computation](scripts/round2_chain.py)

### 9.4 What root deletion, lifting and contraction actually preserve

In the original essentially 6-edge-connected graph the LTWZ lower cut bound can fail only at a degree-five singleton of boundary zero. At a degree-five singleton a nonzero boundary indeed gives $|\tau|=1$ and exactly meets the bound. **Deleting a spoke changes both inputs.** For a degree-five neighbor on exactly one spoke, deletion gives degree four and boundary $\pm1$, so $|\tau|=2$ and the required lower bound is six. Its deficit is still two. [LTWZ, Theorem 3.1](https://www.math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2013-3-flow-LTWZ.pdf)

There is also an exact list of new failures on nonsingleton shores. Reverse globally to have four edges out of $z$. In $H=G-z$ take a partition with at least two vertices on each side. Call $S$ the side meeting $j\le2$ of the five spokes, counting multiplicity. Let $a$ indicate that the minority spoke meets $S$, and let $r=|\delta_H(S)|$. The two lifted cuts in $G$ have sizes $r+j$ and $r+5-j$, both at least six. The required residual boundary on $S$ is $j-2a$. Applying the parity table of §1 yields precisely these possibilities for $r<4+|\tau_H(S)|$.

| $j$ | $r$ | Spokes seen by $S$ | Residual boundary modulo 3 |
|---:|---:|---|---:|
| 2 | 4 | Two majority | 2 |
| 2 | 5 | One of each | 0 |

For $j=0$ the cut already has size at least six. For $j=1$ it has size at least five with nonzero boundary. For $j=2$ its size is at least four, and the only candidates are four and five, giving the two rows. The numerical test is invariant under replacing a shore by its complement.

Both failures occur in eligible simple graphs. The order-22 example has two disjoint copies of $K_6$ minus a perfect matching, a central $C_9^2$, four edges from each end into the center, and root spokes distributed $2,2,1$. For every minority label at least one end gives the first failure. The order-16 example has $C_7^2$ and $C_8^2$ joined by five independent edges and gets two and three spokes respectively. A minority at either of the two spokes on the first block gives the second failure. Lifting those two oppositely directed spokes at $z$ replaces them by an edge internal to the first block, turning its original seven-cut into a nontrivial five-cut. Both graphs extend all five minority positions. All residual shores were enumerated on both examples. [Exact specifications](scripts/round2_paths.py) · [Cut enumeration and lift](scripts/round2_boundaries.py)

Contracting $z$ with neighbors has a separate arithmetic cost. For the zero boundary the LTWZ upper bound at a prospective new root is four at even cut size and seven at odd cut size. Among nontrivial shores of cut size at least six, only size seven fits. A pair $\{z,v\}$ has size $5+d(v)-2m_{zv}$ where $m_{zv}$ is the spoke multiplicity. In the simple 5-regular case this is eight for a neighbor. A root with two distinct neighbors in that case has cut nine if the neighbors are adjacent and eleven otherwise. Even a shore of size seven needs an extension back to the original prescribed star. The stronger essential-connectivity and excluded-cut-size hypotheses in Li–Li do not apply to these examples. [Li–Li, Appendix A](https://arxiv.org/html/2609.08377v1#A1)

**Extension with at most three deficient singletons, for arbitrary boundary.** Let $G,z$ satisfy the original cut assumptions, let $\beta$ be any zero-sum boundary, and prescribe any compatible star. If at most three vertices away from $z$ have degree five and boundary zero, the star extends. The two-vertex case follows directly from compatibility. For at most two such vertices, add one pinned spoke from $z$ to each, adjusting $\beta$ by the chosen signed contributions. The affected degrees become six and satisfy the lower bound. Every old nontrivial shore still has size at least six and passes for any new boundary. With one new spoke choose its sign to leave nonzero boundary at the new degree-six root. With two choose their signs so the new degree-seven root has zero boundary. With none the degree-five root already meets its upper bound. Apply LTWZ and remove the added edges. [LTWZ, Theorem 3.1](https://www.math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2013-3-flow-LTWZ.pdf)

With three, distinguish one of them, $x$, and give the other two oppositely directed new spokes. Suppose the preflow fails. Choose a tip-respecting quotient of minimum order where it still fails, keeping $z$ a singleton, deleting loops, and summing boundary values over parts. A quotient with only one nonroot part extends automatically. The chosen quotient is critical for that particular preflow since every further proper tip-respecting quotient extends. Distinguish the part containing $x$. Every other nonroot part is either a tame singleton or has degree at least six by the original nontrivial-cut assumption. If the part of $x$ is larger than a singleton, it also has degree at least six, so $7<d(x\text{'s part})+2$. If it is a singleton, its degree is five and the two new opposite spokes each miss it. In both cases the quotient is a tall tame easel, contradicting Theorem 1.18 of Árnadóttir et al. This deals with any number of other degree-five vertices whose boundaries are nonzero. The test panel had 38 instances for each fault count from zero to three, checked before and after augmentation. [Árnadóttir et al., Definitions 1.13 and 1.17 and Theorem 1.18](https://arxiv.org/html/2502.01451v3#S1) · [Arbitrary-boundary tests](scripts/round2_boundaries.py)

### 9.5 A density restriction on a rooted obstruction

Here is a complementary deduction using **Theorem 25 of Jafari's November 2026 preprint, version 4**. The cited external input is that a $\mathbb Z_3$-reduced graph on $h\ge5$ vertices has at most $3h-7$ edges. Reduced means it has no subgraph on at least two vertices realizing every zero-sum boundary. Such a graph is simple, since two parallel edges already realize all three terminal residues. The same bound applies to every induced subgraph on at least five vertices because reducedness is hereditary. The deductions below use that preprint as a theorem input. Its proof has no independent Lean verification here. [Jafari, §10 and Appendix B, Theorem 25](https://arxiv.org/html/2610.07034v4#A2)

Suppose a compatible pinned star fails for a prescribed boundary in $G$. In $H=G-z$, contract any nontrivial $\mathbb Z_3$-connected subgraph, discarding loops. A solution on the quotient extends by solving the induced internal boundary, whose sum is zero by conservation at the contracted vertex. Repeat to obtain a reduced $H'$, retaining the five spokes and their directions in the graph $G'$ obtained by restoring $z$. Every cut in $G'$ lifts to an original cut. For a nonroot part containing multiple original vertices and at least one other nonroot part in the quotient, its degree is at least six. Let $h=|V(H')|$. The case $h=1$ extends by the pinned directions. The cases $2\le h\le4$ contradict $5h-5\le2|E(H')|\le h(h-1)$.

In the reduced graph with its root restored put
\[
 b=|\{v\ne z:d_{G'}(v)=5\}|,\qquad t=\sum_{v\ne z}\max(0,d_{G'}(v)-6).
\]
Counting endpoints of the free edges gives $2|E(H')|=6h-b+t-5$. The density bound now gives
\[
                         b\ \ge\ t+9 .
\]
For every nonroot set $S$ of at least five vertices, the same argument on $H'[S]$ gives $b(S)-t(S)\ge14-|\delta_{G'}(S)|$. Each degree-five nonroot part was a singleton of the original graph. **Consequently every compatible root star extends, for every valid boundary, if the original graph has at most eight nonroot degree-five vertices.** This counts all degree-five vertices away from the root. The three-fault result in §9.4 counts only the ones with zero boundary. Li's earlier seven-five-cut theorem concerns unpinned group connectivity. [Li, Theorem 4(d-ii)](https://arxiv.org/pdf/2005.00297)

Equivalently, a failed star supplies a partition of $H$ into $h\ge5$ parts with at most $3h-7$ free edges across parts. Thus $3s-6$ crossing edges for every partition of $H$ into $s\ge5$ parts suffices for extension. For a large 5-regular graph the partition of $H$ into singletons already has only $5(h-1)/2$ crossing edges. The bound leaves precisely the sparse case of interest. Python counted every residual boundary in 24 constructed graphs with at most eight nonroot degree-five vertices. All 589,032 entries were positive. It also checked reducedness of all 424 induced subgraphs of order at least two on three small $K_{3,t}^{+}$ critical cores and verified the stated density bound where applicable. These tests support the deductions and do not independently prove the preprint. [Exact boundary counts](scripts/round2_boundaries.py)

### 9.6 What choosing the edge buys, and a limit even with both choices

In a vertex-minimal failed rooted instance one may choose **any** nonroot edge to contract. Section 8.7 gives a pinned partial orientation on reopening its ends, since any nonzero imbalance would permit inserting the edge immediately. Thus finding one good edge would suffice. Section 9.1 makes the quantifiers precise. For a fixed edge admitting a partial orientation, transfer *existence* is independent of the choice of partial orientation. Directed comparability and the minimum support retain that dependence.

A choice of both edge and orientation still cannot give any absolute support bound. In a simple graph of girth $g$, a transfer contains an undirected bypass, which together with the deleted edge gives a cycle. Thus every choice costs at least $g-1$. There are eligible graphs of arbitrarily large girth where a good edge actually exists for each fixed star, as follows.

*Existence of the graphs.* On the ball of reduced words of length at most $L\ge3$ in five involution letters, each letter swaps word pairs along the corresponding tree edges and fixes unmatched boundary points. Take the finite group generated by these five permutations, each tagged with the odd element in a second $\mathbb Z_2$ coordinate. A reduced word of positive length at most $L$ moves the empty word to a word of that length. The Cayley graph is therefore simple, bipartite, 5-regular and has girth greater than $L$. To check connectivity of cuts, choose a smallest minimum-cut shore of size $s$ at most half the order. Two distinct intersecting translates would have nonempty intersection and proper union. Submodularity would make the smaller intersection a minimum shore. Its translates consequently form blocks, and the stabilizer of a block acts transitively on it. If each vertex of the block has $a$ external edges then $sa=\lambda$, with $a\ge1$. If $\lambda<5$ then $s\le4$, and simplicity gives $\lambda\ge s(6-s)\ge5$. Now $\lambda=5$. If there is a nontrivial five-shore, take the smaller side. Its equal-size translates are again disjoint or equal because odd minimum cuts do not cross (§8.2). The same count forces $s=5$, $a=1$. The shore induces $K_5$, impossible in a bipartite graph. This checks both cut hypotheses.

*Existence of a good edge.* In any connected simple 5-regular bipartite graph choose a perfect matching $M$ containing the minority edge at $z$. A decomposition into five perfect matchings gives such an $M$. Orient its edges right to left and the others left to right, reversing globally as needed for the specified star. Write a matched pair as $(a_i,b_i)$, with $a_i$ on the left. Represent each nonmatching edge $a_i b_j$ by $i\to j$ and remove the root's matched pair. The remaining simple digraph has minimum outdegree at least three. A sink strongly connected component of order $s$ therefore has at least $3s$ arcs. One inward and one outward spanning arborescence at a common vertex use at most $2s-2$. Choose an arc outside their union. Its tail still reaches its head after deleting it. Expanding such a path through matching edges gives a directed bypass parallel to the chosen edge in the full orientation, avoiding $z$. Delete the edge and reverse the bypass to balance $G-e$. This provides the desired partial orientation and a path transfer. Direct tests with all five minority labels on $K_{5,5}$, the incidence graph of the projective plane over $\mathbb F_4$, and the symplectic generalized quadrangle over $\mathbb F_4$ give orders 10, 42 and 170, and girths 4, 6 and 8 respectively. [Finite-field constructions, min-cuts, girths and sign tests](scripts/round2_structure.py)

The chosen-edge search covered the following rooted construction instances. Every graph passed a minimum-cut check and a search for nontrivial five-cuts. All five minority labels for the specified root had a full extension and an actual path-repair certificate at a selected edge. Reversal supplies the opposite five signed stars. Candidates preferentially touched neighbors of the root and then vertices of higher degree. None of the results presumes those preferences always work.

| New search family | Eligible graphs | Star prescriptions with a chosen-edge path |
|---|---:|---:|
| Two root-deletion examples from §9.4 | 2 | 10 |
| Seven-cut chains and their perturbed versions | 16 | 80 |
| $K_{3,t}^{+}$ with cubic vertices raised to degree five | 21 | 105 |
| Flower-snark perturbations or covers | 9 | 45 |
| Petersen-derived covers, including irregular versions | 9 | 45 |
| **Total** | **57** | **285** |

The perturbed chains include changes of matching labels and added edges. The largest chain in this search has 102 vertices. The 29-witness optimization separately covers 19 random simple, four irregular, four flower-derived and two Petersen-derived cases of orders 20–40. These are labelled experiments, with no claim of population coverage. [Chosen-edge generator, tests and path certificates](scripts/round2_paths.py)

### 9.7 Lean inventory and reproduction

The default `lake build` includes every module below. The inventory lists all 21 public theorem declarations in the project and all eight private theorem declarations. The formal statements are over the frozen labelled multigraph representation. The public names in the five general flow modules and in `TransferReorientation` are in `FinMultigraph`. The finite examples have their own namespaces.

| Module | Public theorem declarations | Private theorems | Content |
|---|---|---|---|
| [Equivalence](Tutte3Flow/Equivalence.lean) | `hasMod3Orientation_iff_hasNowhereZeroZMod3Flow`, `hasNowhereZeroZMod3Flow_of_hasNowhereZeroIntFlow` | `degreeDifference` | Signs and modulo-three orientations, and reduction of an integer flow |
| [PrescribedDegrees](Tutte3Flow/PrescribedDegrees.lean) | `assignWithQuotas`, `exists_orientation_with_outdegrees_iff` | — | Hall assignment with quotas and the prescribed-outdegree cut criterion |
| [IntegralLift](Tutte3Flow/IntegralLift.lean) | `exists_intFlow_lifting`, `hasMod3Orientation_iff_hasNowhereZeroIntFlow` | `roundThirds` | An integer lift of each nonzero residue circulation preserving its residues, and the existence equivalence |
| [ModularBase](Tutte3Flow/ModularBase.lean) | `hasNowhereZeroIntFlow_iff_exists_modular_outdegrees` | `balance_iff_twice_outdegree` | The exact modular lattice and orientation-base intersection criterion |
| [EdgeInsertion](Tutte3Flow/EdgeInsertion.lean) | `pinned_insertion_iff_transfer`, `hasNowhereZeroIntFlow_adjoin_iff_transfer` | `divergence_as_sum`, `divergence_adjoin`, `divergence_one_add` | Pinned modular insertion equivalence and unpinned integer-flow specialization |
| [TransferReorientation](Tutte3Flow/TransferReorientation.lean) | `subset_divergence_reorient`, `transferSet_reorient_eq` | `divergence_columns`, `unit_divergence_reorient` | Symmetric-difference translation and equality of the full pinned transfer sets |
| [ChallengeSanity](Tutte3Flow/ChallengeSanity.lean) | `fourParallel_sanity`, `K4_sharpness` | — | In `Tutte3Flow.Sanity`, a 4-edge-connected positive example and a 3-edge-connected negative example |
| [TransferExample](Tutte3Flow/TransferExample.lean) | `partial_balanced`, `insertion_cuts`, `forced_free_directions`, `free_arcs_from_three`, `shortest_transfer`, `full_integer_flow` | — | In `Tutte3Flow.TransferExample`, the exact rooted fixed-edge obstruction to directed paths and its full graph's positive integer-flow certificate |
| [TransferTemplates](Tutte3Flow/TransferTemplates.lean) | `fork_table`, `no_tight_chain` | — | In `Tutte3Flow.SevenCut`, the finite two-edge fork table and the exclusion of a tight one-branch port sequence for any odd length |

The frozen [Challenge](Tutte3Flow/Challenge.lean) defines `Tutte3FlowConjecture`. Its SHA-256 is `cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6`, matching the pre-round value. The general reorientation results, the finite example and the port-sequence induction use kernel proofs. The arbitrary-length distance theorems, the density deductions and the bipartite path construction are mathematical proofs in this report. The audit checks that the project theorems' axioms are contained in `propext`, `Classical.choice` and `Quot.sound`. [Reproducible axiom audit](scripts/round2_audit.py)

Run from the repository root with the workspace Python environment. The witness test regenerates and compares the 29 labelled certificates. The optional `--milp` cross-checks every optimum. The Round 1 small-order census is unnecessary.

```sh
/Users/mw/miniconda3/bin/python3 -B scripts/round2_transfers.py --milp
/Users/mw/miniconda3/bin/python3 -B scripts/round2_paths.py
/Users/mw/miniconda3/bin/python3 -B scripts/round2_chain.py --min-cost
/Users/mw/miniconda3/bin/python3 -B scripts/round2_boundaries.py
/Users/mw/miniconda3/bin/python3 -B scripts/round2_structure.py
lake build
/Users/mw/miniconda3/bin/python3 -B scripts/round2_audit.py
shasum -a 256 Tutte3Flow/Challenge.lean
```

### 9.8 Remaining barrier and publication decision

A smallest failed rooted instance would have only trivial five-cuts, no parallel free edges, and no nontrivial $\mathbb Z_3$-connected subgraph disjoint from the root. In particular $G-z$ is reduced. For **every** free edge $xy$, a pinned orientation after contraction exists. When reopened it must be balanced at both ends, and every binary circulation after identifying $x,y$ must have zero imbalance at the split. Otherwise that edge solves the instance. Thus the exact missing implication is that **at least one edge in such a reduced graph has a binary circulation with nonzero split imbalance**. The lower bound of nine nonroot degree-five vertices constrains these graphs but allows arbitrarily large 5-regular ones. The maximizing-shore approach of §8 and the pairing description of §9.1 give no such existence proof. A genuine failure would disprove the universal conjecture by the rooted equivalence. If a concrete unrooted graph were needed, the five-copy construction in §8.5 converts a missing minority position into one. A failed directed-path test on its own supplies no missing position. [Kochol's rooted equivalence and Li's construction](https://arxiv.org/pdf/2005.00297) · [Han–Lai–Li, Theorem 1.3 on the essential-six formulation](https://lijiaao-dm-nk.com/pdf/pub/Jiaao06_4trees3flow_JGT2018.pdf)

**Publication and compute decision.** The best standalone candidate is a short constructive paper on the $18+12k$ family. It gives exact, unbounded neutral-exchange delay at deficit one on simple 5-regular graphs, an unbounded requirement for integer-divergent branch vertices in a specified partial orientation, and the exact support-versus-branching tradeoff, including the effect of freely choosing the partial orientation under the same fixed star. These quantities can all be stated and proved on a single explicit family. For an Opus formalization, the port-sequence induction is already available. The main remaining work is to model the glued graph, prove its cut and residue bounds, connect equality of graph costs to the verified port transitions, and lift the repeating witnesses to any odd length. The sample sizes and the maximum-bisection example are secondary. I found no matching exact-distance result in the sources checked. Historical priority remains unverified. The related work treats pseudoforest decompositions, random bisections, forbidden cut sizes and universal modular realization. [Ahanjideh–Kovács](https://arxiv.org/abs/2603.24175) · [Jafari on random regular graphs](https://arxiv.org/abs/2611.03763) · [Li–Li](https://arxiv.org/abs/2609.08377) · [Jafari on modular realization](https://arxiv.org/abs/2610.07034)

The $C_d^2$ expansion in §8.1 is a concise elementary route to the simple 5-regular restriction. The reduction objective already has a literature history and priority for this gadget is unverified. Include it as a supporting lemma if a paper needs it. The three-fault and eight-degree-five extension criteria are deductions from cited external results. The four-vertex example and the reorientation identity fit naturally as supporting examples and formal infrastructure. **Pause the general Tutte attack and move the next flagship run to another ProofAtlas #300–#500 target.** Resume this attack if a candidate can force a nonzero split imbalance on a reduced graph with many degree-five vertices. A larger repeat of the same random search would not settle that step.

## 10. MAX Round 3 — Final Verdict

**Case C.** Tutte's conjecture remains unresolved. Two rooted results survive this round. In a 5-edge-connected graph, if six vertices cover all edges away from a degree-five root, every compatible root star extends for **every boundary**. If an essentially 6-edge-connected graph has at most **eleven** nonroot degree-five vertices, every compatible **zero-boundary** star extends, using a recent external density theorem. The all-edge obstruction gives integer counting identities that hold simultaneously on known critical graphs.

### 10.1 The search for a reduced free core

Write $H=G-z$, $h=|V(H)|$, $s_v$ for the multiplicity of $zv$ and $\gamma$ for the required boundary on $H$ after fixing the five spokes. Group connectivity means realization of **every** zero-sum boundary in $\mathbb F_3$. A reduced graph has no group-connected subgraph on two or more vertices. In a 5-edge-connected graph the cuts around $v$ and $\{z,v\}$ give
\[
 d_H(v)\ge 5-s_v,\qquad d_H(v)\ge s_v\quad(h\ge2).
\]
With essential six-connectivity and $h\ge3$, the second bound improves to $s_v+1$. Thus $\delta(H)\ge3$ and $\sum_v(5-d_H(v))_+\le5$. Degree three can occur at a double spoke. Take $K_7$ on $0,\ldots,6$, join vertex 7 to $0,1,2$, and attach $z$ to $7,7,3,4,5$. The graph has minimum cut five, no nontrivial five-cut, and all five labelled star extensions. Its free core contains the clique. Assuming $\delta(H)\ge4$ in the reduced search would require a separate argument. [Cut and star checks](scripts/round3_reduced.py)

For a particular $G,z$, strong extension at $z$ for all original boundaries is equivalent to group connectivity of $H$. Test a boundary on $H$ by adding the divergence of a fixed star. Li's **universal** equivalence then implies that even one nontrivial reduced $H$ with a 5-edge-connected completion at a degree-five root would refute the Jaeger–Linial–Payan–Tarsi conjecture. The counterexample to unrooted group connectivity could be a different graph. To refute **Tutte** by §8.5 one must additionally certify a missing minority position for the **zero** original boundary. The search found no graph in the intersection. Consequently the number of minority positions tested on genuinely reduced, eligible cores was **zero**. [Li, Theorem 2 and Lemma 2](https://arxiv.org/pdf/2005.00297)

An induced subgraph suffices for a group-connectivity witness, since adding edges preserves group connectivity. A smallest nontrivial witness in a simple graph has minimum degree at least three. A leaf excludes boundary zero there. At degree two, prescribe a nonzero boundary at that vertex. Both incident directions are forced. An arbitrary boundary on the deletion can therefore be realized by adding the forced contributions and invoking group connectivity before deletion. This gives a smaller witness. Isolated vertices cannot occur in a nontrivial connected witness. The search either exhibits an induced subgraph by exact counts for every boundary, exhausts the candidate vertex sets, or uses the single-zero certificate below. Array counts have total $2^m$ and use fewer than 63 edges. The frontier algorithm uses Python integers. The root constructor enumerates every five-spoke multiset passing the deficit bound, verifies both cut hypotheses and tests all five labelled minority positions on each eligible reduced core. [Constructor and exact checks](scripts/round3_reduced.py) · [Free-core enumeration](scripts/round3_cores.py)

| $h$ | Free edges | Maximum degree in slice | Connected simple inputs | Failed degree deficit | Excluded by group-connected induced subgraph | Reduced survivors |
|---:|---:|---:|---:|---:|---:|---:|
| 9 | 20 | 5 | 1,151 | 0 | 1,151 | 0 |
| 9 | 21 | 7 | 12,982 | 6,676 | 6,306 | 0 |
| 9 | 22 | 8 | 11,465 | 2,244 | 9,221 | 0 |
| 10 | 23 | 6 | 305,148 | 235,113 | 70,035 | 0 |
| 11 | 25 | 5 | 289,371 | 0 | 289,371 | 0 |

A completable $H$ is connected because two components would each require five spokes. The degree caps follow from the total degree and the deficit, or from a 5-regular completion in the last row. For example $\sum(d_H-5)_+=2m-5h+\sum(5-d_H)_+$. The published reduced maxima at orders $2,\ldots,7$ are $1,3,6,8,11,13$. Averaging the order-seven bound gives $m\le\lfloor13\binom h2/\binom72\rfloor$ at orders eight and nine, whereas $2m\ge5h-5$. Together these exclude orders two through eight and give $20\le m\le22$ at nine. For order ten the exhaustive claim uses the $3h-7$ theorem, giving $m=23$. At eleven the table covers the regular-completion slice. Its first strong certificates have sizes five through ten with respective counts $133298,102396,49951,3601,122,3$. These enumerations concern free cores and all-boundaries witnesses. [Li–Luo–Wang, Lemma 2.10](https://www.lijiaao-dm-nk.com/pdf/pub/Jiaao08_Nowhere-zero3flow-ind_DM2018.pdf) · [Jafari v4, Theorem 25](https://arxiv.org/html/2610.07034v4#A2)

A missing boundary certifies reducedness if, for every edge, there is a realization whose only zero is that edge. If a strong subgraph contains $e$, the realization with sole zero at $e$ projects to a nowhere-zero realization after contracting the subgraph. Group connectivity then restores all its internal edges, contradicting the missing boundary. We checked zero-boundary certificates on each edge orbit of $K_{3,t}^+$ at all 31 orders $10,\ldots,40$, and at all 16 even orders in this range for both odd-rim wheels and books of $K_4$'s sharing an edge. At the first order we also checked every edge individually and all induced subsets. The orbits are the added hub edge and two hub-to-leaf types, the spine and two page-edge types, or the rim and spokes, respectively. The Petersen graph and the 36-vertex flower snark $J_9$ have another certificate. A zero orientation of a cubic graph makes each vertex a source or sink, forcing bipartiteness. Every proper subgraph of a connected cubic graph peels below minimum degree three. All these cores fail the five-spoke degree test. The four-rim wheel $W_4$ itself is group-connected. Augmenting $K_{3,t}$ or $K_{3,t}^+$, $t\ge6$, solely by leaf-to-leaf edges cannot work. Some leaf needs two new incident edges to meet the five-spoke budget. That leaf, the two new neighbors and two hubs contain $W_4$. [Constructors and checks](scripts/round3_reduced.py) · [Critical $K_{3,t}^+$ family](https://arxiv.org/abs/2003.09162) · [Li–Luo–Wang, Lemma 2.6](https://www.lijiaao-dm-nk.com/pdf/pub/Jiaao08_Nowhere-zero3flow-ind_DM2018.pdf)

The twelve-vertex JLPT ring of three $K_4$'s is reduced. Its only missing boundaries are the two nonzero constant vectors. Every one of its 42 simple one-edge augmentations realizes every boundary. A boundary missing after adding a column $a$ would require both $\gamma-a$ and $\gamma+a$ in the old missing set. Their difference is supported on the two endpoints, whereas the two distinct old holes differ at all twelve vertices. This excludes every pure edge augmentation of this seed. [Exact counts and construction](scripts/round3_reduced.py)

Minimum free degree four and the **total** density inequality can both hold in a reduced graph. Substituting a reduced graph for a vertex of another reduced graph preserves reducedness, with arbitrary attachment of the old incidences. A strong subgraph meeting distinct fibres projects to a nontrivial strong subgraph of the old graph, since arbitrary identifications preserve group connectivity by lifting each test boundary. A subgraph inside one fibre is ruled out by its reducedness. Starting from the JLPT ring, replace a maximum-degree vertex of degree $d$ by $K_{3,d}^+$, attaching one old incidence to each cubic leaf. Minimum degree stays at least four. Two new hubs have degree $d+1$. Each operation adds $d+2$ vertices and $3d+1$ edges. After eleven substitutions the simple reduced graph has $h=133$, $m=332$ and $2m\ge5h-5$. Its positive singleton deficits sum to **111**. This exposes precisely what the total-density relaxation loses. [Construction and counts](scripts/round3_reduced.py)

### 10.2 A vertex-cover theorem for arbitrary boundaries

**Theorem.** In any loopless 5-edge-connected multigraph with a degree-five vertex $z$, if the free edges have a vertex cover of size at most six, $H=G-z$ is $\mathbb Z_3$-connected. Consequently every compatible preorientation at $z$ extends for every prescribed boundary. Separating five-cuts are allowed.

First consider a cover of size five. If $h\ge10$, pad the cover to five and take five outside vertices. They are independent and miss at most five adjacencies in total to the cover in a reduced simple core. Every one of the 34 row-and-column isomorphism types of $K_{5,5}$ with five edges deleted has a group-connected induced subgraph. For 33 types there is an eight-vertex witness. The other deletes a perfect matching and the full graph has at least 18 realizations of each boundary. Fewer deletions are covered by monotonicity. The finite check enumerates sorted column masks of total weight five, minimizes under the 120 row permutations, and counts every boundary on each witness. [Five-cover check](scripts/round3_reduced.py)

For a six-cover and $h\ge12$, select six vertices outside a padded six-vertex cover. Each has at least three neighbors in it. Cap each outside degree at five, retaining at least 25 cross edges by the total deficit bound. Delete further edges to retain exactly 25, keeping each outside degree at least three. This is possible since the sum of those six lower bounds is 18. The 1,274 bipartite graphs up to independent permutations of both sides, with the six outside degrees in $[3,5]$ and 25 edges, all contain a strong subgraph. In fact the maximal induced subgraph of minimum degree three in **each** realizes every boundary. Its sizes $9,10,11,12$ occur $34,154,433,653$ times, respectively. This rules out the entire six-cover construction at every larger order, including the requested orders 25–40. [Exact bipartite certificate](scripts/round3_cover.py)

For $h=10,11$ use six cover vertices and respectively four or five outsiders. Generate every two-coloured bipartite cross graph with outside degrees at least three, total outside deficit at most five, and all possible hub-to-outsider adjacencies. Discard a cross graph containing a strong witness. Discard each inside edge whose addition alone produces a witness. Among subsets of remaining inside edges, retain every inclusion-minimal choice giving minimum degree at least three and combined deficit at most five. These predicates are monotone under addition. Every such choice has a strong induced witness. At four outsiders 393 of 404 input cross graphs passed the outside deficit, 272 of these were reduced, and 50,490 minimal augmentations were checked. At five outsiders 1,309 of 1,438 passed and 121 were reduced. None of those 121 can pass the incidence requirements using the allowable inside edges. The smaller orders are excluded in §10.1 using the published small-order values. [Enumeration and augmentation checks](scripts/round3_cover.py)

Finally, if the original $H$ fails some boundary, contract group-connected free subgraphs until its quotient is reduced, carrying the boundary by summing on parts and discarding loops. Failure persists since a solution lifts across each contraction. The quotient with $z$ restored remains 5-edge-connected, its root degree stays five, and the images of the old cover vertices cover every remaining free edge. The one-vertex quotient realizes its unique valid boundary. The preceding exclusions handle every larger quotient. This proves the theorem independently of the recent $3h-7$ preprint. The finite enumerations use nauty and exact integer counts in Python. They have not been replayed in the Lean kernel.

### 10.3 A rooted extension theorem with eleven nonroot degree-five vertices

**Theorem, using Jafari v4, Theorem 25.** Let $G$ be loopless, 5-edge-connected, with every nontrivial cut of size at least six. Fix a compatible **zero-boundary** star at a degree-five vertex $z$. If at most eleven vertices other than $z$ have degree five, the star extends. There is no bound on the order or the maximum degree. The proof has a finite low-order input and a separate argument for the equality case of the density bound. [External reduced-density theorem](https://arxiv.org/html/2610.07034v4#A2)

**First input, at most twelve odd vertices.** In any 5-edge-connected loopless graph with at most twelve odd-degree vertices the pinned zero-boundary assertion holds at a degree-five root, even with nontrivial five-cuts. Completely split off every even nonroot vertex using Mader's lemma, discarding loops. This preserves 5-edge-connectivity on the remaining vertices and the parity of each surviving degree. A discarded loop at an unpinned vertex can be lifted as a closed directed two-edge walk. Two old root incidences cannot be paired to form a loop at $z$, since that would leave its cut below five. There is always another odd vertex besides $z$. Each remaining virtual edge at the root carries the direction prescribed for its original incidence. An oriented paired edge lifts to a directed two-edge path of divergence zero at the removed vertex. Thus any failed example gives a failed example of order at most twelve. Choose a failing graph within that order bound minimizing order, then size. All nonroot degrees are five. Indeed, even vertices can be completely split and any remaining odd degree at least seven admits a single connectivity-preserving split reducing the size. Its free core is reduced by contraction minimality. Now $h$ is odd, $m=5(h-1)/2$ and $\Delta(H)\le5$. The case $h=1$ extends by compatibility. The small-order exclusion and the $(9,20,5),(11,25,5)$ rows of §10.1 cover all other possibilities. This pinned conclusion uses the free-core computation. The published odd-5-edge-connected small-order result concerns unpinned flows. [Mader's lemma as stated by Li, Lemma 3](https://arxiv.org/pdf/2005.00297) · [Li–Luo–Wang, Lemma 2.14](https://www.lijiaao-dm-nk.com/pdf/pub/Jiaao08_Nowhere-zero3flow-ind_DM2018.pdf) · [Free-core certificates](scripts/round3_cores.py)

**Second input, the case $P=7$.** Put $P(J)=3|V(J)|-|E(J)|$. Let $H$ be reduced of order $h\ge7$ with $P(H)=7$, and let $\gamma$ be any zero-sum boundary. Call a vertex *active* if its free degree is at most four, or if it is five and its boundary is nonzero. Let
\[
 X=\{v:d_H(v)>6\}\ \cup\ \{v:d_H(v)=6,\ \gamma(v)\ne0\}.
\]
If $|X|\le2$ and there is an active vertex, $H$ realizes $\gamma$.

To prove this, suppose $H$ is a smallest failure of the claim. Order seven is impossible since $r(7)=13<14$. For $h\ge8$, applying $m\le3(h-1)-7$ to each vertex deletion gives minimum degree at least three. Choose an active $u$. Delete $u$, pair some disjoint incident edges and replace each paired path by one edge. Orient all unpaired edges with the same sign at $u$, chosen to give $\gamma(u)$. On the remaining vertices subtract the signed contributions of the unpaired edges to form $\gamma'$. Every orientation of the resulting $J$ at $\gamma'$ lifts through the directed pairs, so $(J,\gamma')$ fails. The exact choices are as follows.

| $d_H(u)$ | $\gamma(u)$ | Pairs | Unpaired edges | $P(J)$ |
|---:|---|---:|---:|---:|
| 3 | 0 | 0 | 3 | 7 |
| 3 | nonzero | 1 | 1 | 6 |
| 4 | 0 | 2 | 0 | 6 |
| 4 | nonzero | 1 | 2 | 7 |
| 5 | nonzero | 2 | 1 | 7 |

In a row with $P(J)=7$, leave at least one neighbor outside $X$ unpaired. This is possible because $H$ is simple and $d_H(u)\ge3>|X|$. The following contraction argument explains why this neighbor will survive.

The graph $H-u$ is connected and bridgeless. Every singleton has degree at least two there, and every pair has cut at least two by simplicity. For a partition of $H-u$ with both shores of size at least three, take the shore $A$ containing at most two neighbors of $u$. The cut around $A$ in $H$ has size at least five. Indeed the density bounds on $A$ and $V(H)\setminus A$, each of size at least three, are $3|A|-6$ and $3|V(H)\setminus A|-6$, while $H$ has $3h-7$ edges. Removing $u$ costs at most two. Adding the paired edges preserves connectedness and bridgelessness in $J$. Here the bound $3s-6$ for $s=3,4$ is elementary and for $s\ge5$ follows from Theorem 25.

For any proposed contraction part $S$ of $J$ let $\sigma(S)=3(|S|-1)-e_J(S)$. A two-vertex part has $\sigma\ge1$ because the paired edges form a matching, so the multiplicity is at most two. For $s=|S|\ge3$, let $j$ count the added edges internal to $S$. Using $e_H(S)\le3s-6$ gives $\sigma\ge3-j$. Also $e_H(S)+2j\le e_H(S\cup\{u\})\le3s-3$ gives $\sigma\ge j$. Thus every part of size at least three saves at least two. Singletons save zero.

Take a contraction-minimal infeasible quotient $Q$ of $J$, deleting loops and summing the boundary over parts. It is reduced because contracting a strong subgraph would preserve failure. It stays connected and bridgeless. Order one realizes its boundary and a bridgeless two-vertex graph has a strong digon. For orders three and four, simplicity gives $P(Q)\ge6$. For larger orders, Theorem 25 gives $P(Q)\ge7$. Since
\[
 P(J)=P(Q)+\sum_{S\text{ a quotient part}}\sigma(S)\le7,
\]
at most one two-vertex part can have been merged, and no larger part can have been merged. Consequently $|V(Q)|\ge h-2\ge6$. Now $P(Q)\ge7$ applies. This rules out $P(J)=6$, and at $P(J)=7$ forces every part to be a singleton. In particular $J$ itself is reduced and simple. The distinguished unpaired neighbor outside $X$ either has new degree at most four, or started at degree six with zero boundary and now has degree five and nonzero boundary. It is active. Paired neighbors keep their degrees and boundaries. Unpaired neighbors drop a degree, and no new exceptional vertex can enter $X$. Thus $J$ satisfies the same hypotheses at smaller order, a contradiction. Jafari's Lemma 29 uses related splitting moves at $P=6$. The persistence at $P=7$ here requires the contraction savings and the surviving neighbor. [Jafari, Appendix B](https://arxiv.org/html/2610.07034v4#A2)

**Applying the two inputs.** Contract strong free subgraphs in a hypothetical pinned failure until $H$ is reduced. The cuts of the rooted quotient lift to original cuts. When $h\ge2$, each nonsingleton nonroot part has degree at least six by essential six-connectivity. Thus the nonroot count $b$ of degree-five vertices cannot increase. The small cases are already excluded. In the reduced quotient put $t=\sum_{v\ne z}(d_G(v)-6)_+$. Degree counting gives $2m=6h-b+t-5$, hence $P(H)=(b-t+5)/2\ge7$. If $P(H)\ge8$ and $b\le11$, then $b=11$ and $t=0$. There are exactly twelve odd vertices, including the root, and the first input applies. If $P(H)=7$, then $b=t+9$ and $t\le2$. All exceptional vertices for the residual boundary have original degree greater than six. A free degree-six vertex of original degree six lost no spokes and has residual boundary zero. Therefore $|X|\le2$.

There must be an active spoke endpoint. Any spoke at an original degree-five vertex leaves free degree at most four. At an original degree-six vertex, a single spoke leaves degree five with nonzero boundary, and two or more leave degree at most four. If all spokes touch higher degrees and no endpoint is active, a vertex of degree $d$ can accept at most $d-5$ spokes. At $t\le2$, one such vertex accepts at most three, or two degree-seven vertices accept at most four together. Neither accommodates five. Apply the second input to $\gamma$, and restore the contractions. This completes the proof.

The limitations of the descent are witnessed by actual reduced graphs. At order six, two $K_4$'s sharing an edge have $P=7$, active vertices, no exceptional vertices for $\gamma=0$, and no zero flow. At $P=8$, $K_{3,5}^+$ of order eight has the same failure with three, five and six as its vertex degrees. Thus the identical splitting conclusion cannot be asserted at the next potential. For verification the script checks the local signed lifts, all eligible splittings on 19 hereditary-sparse fixtures at $P=7$ (1,257 splits), 78,125 labelled placement/minority tests, 120 full star certificates at $b=9,10,11$, and 15 lifts through an even vertex including a discarded loop. The 19 fixtures test the cut and savings inequalities. Their reducedness is not assumed. The theorem is a mathematical proof with a computer-assisted finite input, using the stated external density theorem. [Split and threshold verification](scripts/round3_descent.py)

### 10.4 What nonconstant chord coefficients can certify

Fix a spanning tree $T$ of a connected free graph $H$, let $r=m-h+1$, and prescribe $\gamma$. For a reference tree edge $a$ with tail on the $S$-side of $T-a$, conservation gives its signed value
\[
 \ell_a(t)=\gamma(S)-\sum_{i\notin T}B_i(S)t_i,\qquad t_i\in\{1,-1\}.
\]
All tree equations hold because these $h-1$ cut equations determine the tree variables and the boundary is zero-sum. In $\mathbb F_3[t]/(t_i^2-1)$ the product $Q=\prod_{a\in T}\ell_a^2$ is precisely the indicator of a nowhere-zero completion of the chords. Its coefficient at $I\subseteq E\setminus T$ is
\[
 [t_I]Q=2^{-r}\sum_{\substack{Bf=\gamma\\ f_e\ne0\ \forall e}}\prod_{i\in I}f_i.
\]
This follows by orthogonality of the sign characters, since 2 is invertible in $\mathbb F_3$. The moment on the right is intrinsic to the selected labelled edges. There is a solution iff at least one coefficient is nonzero, in every tree basis.

A squarefree degree-$h-1$ coefficient of the **unsquared** product $\prod_a\ell_a$ is the permanent of the corresponding square minor of the fundamental cut matrix, modulo three. Terms involving a repeated variable cannot contribute to that top degree after $t_i^2=1$. The coefficient is independent of $\gamma$. A nonzero such permanent therefore proves group connectivity of the **whole** $H$. On a nontrivial reduced $H$ every one of these minors has zero permanent in every tree basis. This explains exactly why that attractive top-degree certificate cannot isolate the desired pinned boundary in the reduced case. Lower degrees of either product can depend on the boundary. Graph permanents and flow certificates have an existing literature. [Crump–DeVos–Yeats on permanents and graph orientations](https://www.numdam.org/item/10.4171/aihpd/35.pdf)

The nonzero/top-minor counts over all spanning trees were $0/16$ for $K_4$, $45/45$ for the four-rim wheel, $0/135$ for $K_{3,3}^+$ and $135/375$ for $K_5-e$. Exact counts at every boundary agreed with the chord computation. For $K_4$ and the wheel we also verified each individual Walsh coefficient against independent enumeration of all edge signs. On $K_7$ at zero boundary the integer solution count is 3,648, all coefficients of degrees zero through three vanish, and the minimum nonzero degree is four for each of the eleven unlabelled spanning-tree shapes. For the star centered at 0, the quartic on edges $12,14,15,23$, oriented by increasing labels, has coefficient 2. Reversal kills odd moments. Swapping the endpoints of one of two disjoint edges kills that quadratic moment. For incident edges orient all six edges away from their common vertex and multiply its boundary equation by one incident edge value. Symmetry gives $3648+5M=0$ modulo three, so the remaining quadratic moment $M$ vanishes as well. [Exact transforms, minors and direct sign checks](scripts/round3_algebra.py)

**There is no fixed degree at which a nonzero coefficient must appear, even after choosing the tree.** Take $k\ge7$, $k\equiv1\pmod3$. Start with a terminal clique $K_k$. Add $t\ge1$ disjoint triangles and join every vertex of each triangle to all $k$ terminals. Attach the five root spokes to distinct terminals. The free graph has vertex connectivity at least $k$, since deleting fewer than $k$ vertices leaves a terminal adjacent to every remaining vertex. In particular every nontrivial cut of the rooted graph has size at least $k$. Any compatible zero-boundary star extends. On each triangle use a directed cycle. At each terminal orient its three edges to this triangle alike, choosing signs at the $k$ terminals whose sum is zero modulo three. Such signs exist since $2j-k=0\bmod3$ has a solution in $0\le j\le k$. This balances the three interior vertices and contributes zero at each terminal. The clique realizes the residual terminal boundary by 6-edge-connectivity. [LTWZ, boundary theorem](https://www.math.wvu.edu/~cqzhang/Publication-files/my-paper/JCTB-2013-3-flow-LTWZ.pdf)

Consider one triangle with all its incident terminal edges, and fix an arbitrary required boundary at its terminals and zero at its interior. Rotating the three interior vertices acts on the realizations. A fixed realization has zero boundary at every terminal, since its three incident edges there agree. At zero terminal boundary the number fixed is
\[
 2\sum_{2j-k\equiv0\ (3)}\binom{k}{j}
     =\frac{2(2^k+2(-1)^k)}{3}.
\]
The binomial identity follows from the three-term roots-of-unity filter for the sum of $k$ independent signs. This is divisible by three when $k\equiv1\pmod3$, by checking $k=1,4\bmod6$ modulo nine. All other rotation orbits have size three. **Every conditional realization count for the block is thus zero modulo three.** If fewer than $t$ edges are marked in a moment, one of the $t$ edge-disjoint blocks is untouched. Condition on the entire exterior of that block. The marked product is fixed and its multiplicity is divisible by three. Summing gives zero. This applies to every choice of the marked edges, hence to every spanning tree. The sign-cube polynomial still has some nonzero coefficient since the star extends. These positive graphs deliberately contain group-connected subgraphs. A uniform low-degree bound within the hypothetical reduced class remains open. The script counts the conditional tables at $k=3,4,5,6,7,8,10$ and verifies all five stars on four completions of orders up to 38. [Block counts and graph certificates](scripts/round3_algebra.py)

Seymour's 6-flow conclusion and two disjoint spanning trees alone cannot force the split. For $K_4$ in lexicographic edge order the signed vector $(-3,1,2,-2,-1,-1)$ is already an integer 4-flow, and edges with zero-based indices $\{1,2,3\}$ and $\{0,4,5\}$ form disjoint spanning trees. Its zero boundary in the nowhere-zero mod-three problem is missing and every edge has a single-zero witness. In a large reduced core even three disjoint spanning trees would require $3(h-1)>3h-7$ edges. Fractional packing may still carry boundary-sensitive information. Neither the existence of a 6-flow nor a count divisible by three distinguishes the positive high-connectivity examples from a genuine missing boundary. [Checked $K_4$ data](scripts/round3_algebra.py) · [Han–Lai–Li on spanning trees and group connectivity](https://arxiv.org/abs/1610.04581)

### 10.5 Counting the obstructions at all edges simultaneously

Let $N_J(\gamma)$ count full sign assignments with divergence $\gamma$, with free edges labelled and root pins absorbed into $\gamma$. For $A\subseteq E(H)$ put $n_A=N_{H-A}(\gamma)$. It counts points of the affine space $\{f:Bf=\gamma\}$ whose zero set is **exactly** $A$. At a missing boundary the coordinate-zero hyperplanes cover this space. Having a positive $n_{\{e\}}$ for every edge says exactly that this cover is irredundant. These are the single-zero points supplied by contraction minimality. Fix the incidence column $a_e$. Partitioning assignments by the sign of $e$ gives
\[
 N_H(\eta)=N_{H-e}(\eta-a_e)+N_{H-e}(\eta+a_e).
\]
At $\eta=\gamma$ both natural-number terms vanish. Since $2=-1$ in the field, at **every** free edge one obtains
\[
 N_H(\gamma+a_e)=N_H(\gamma-a_e)=n_{\{e\}}>0.
\]
The equalities also hold without minimality if positivity is dropped. This is a condition on the *same* full boundary-count table across all edges. More generally, identifying any two distinct nonroot vertices in a vertex-minimal failure gives a solvable quotient. Lifting any resulting signs leaves only opposite endpoint errors. Hence at least one of the two shifted boundaries is present for that pair, even when the two vertices are nonadjacent. [Lean count and neighbor identities](Tutte3Flow/BoundaryDeck.lean)

Now fix an oriented simple cycle $C$. Adding the three multiples of its signed circulation partitions the affine space into lines. Hold fixed a line whose off-cycle coordinates are all nonzero. The three sets of cycle coordinates that vanish at its three points partition $C$, since each normalized cycle coordinate has exactly one vanishing shift. If the full boundary is missing all three classes are nonempty. A line with a zero off the cycle makes no contribution to any $n_A$ used below.

- For a triangle $C=\{e,f,g\}$ the class sizes are $1,1,1$. In particular $n_{\{e\}}=n_{\{f\}}=n_{\{g\}}$, with a bijection on each line fixing all off-cycle coordinates. The equality propagates between triangles sharing edges.
- For a square the sizes are $2,1,1$. Exactly when $e$ is alone in its class, the unique doubleton avoids $e$. Consequently
  \[
  n_{\{e\}}=\sum_{\{i,j\}\subseteq C\setminus\{e\}} n_{\{i,j\}},
  \qquad \sum_{e\in C}n_{\{e\}}=2\sum_{\{i,j\}\subset C}n_{\{i,j\}}.
  \]
  The counts on the right require all edges outside the designated pair to be nonzero. Chords outside the square cause no change to the identity.
- A theta graph has three internally disjoint paths with the same endpoints. Orient the paths in parallel and fix all off-theta coordinates. Starting at any point of the fibre, one can shift the three paths by $t_1,t_2,t_3$ exactly when $t_1+t_2+t_3=0$. For each path let $L_i$ be the shifts avoiding every zero on it. A full extension in that fibre exists exactly when $0\in L_1+L_2+L_3$, provided the exterior has no zero. Each $|L_i|\le2$. If all are nonempty but the sum misses zero, their sizes must be $1,1,1$ or $1,1,2$ in some order. Indeed any two two-element subsets of $\mathbb F_3$ already sum to the whole field. The same exterior must be used for all three lists. Choosing a different deletion solution for each edge does not guarantee this compatibility. [Line and plane tests](scripts/round3_deck.py)

On $K_{3,8}^+$ the single-edge counts are 84 on eight edges and 86 on the other seventeen. The zero boundary is missing. This graph already has $2m=5h-5$, but each leaf has degree three. On the twelve-vertex, minimum-degree-four JLPT ring at the all-one boundary, the counts are 16 on eighteen edges and 32 on six edges. This graph has insufficient total degree and its missing boundary would require more than five root incidences. Thus the simultaneous counting laws and positivity of *all* single-edge counts are consistent with failure on both sides of the proposed density/minimum-degree tests. The script checks every edge and every triangle and square on eleven critical boundary instances, and every allowed-set triple on the theta plane. These identities alone do not exploit the five-spoke budget. [Exact deletion tables](scripts/round3_deck.py)

In fact **both** shifted boundaries occur at every nonedge of the eleven-vertex $K_{3,8}^+$ (all 30 pairs) and of the JLPT ring (all 42 pairs). Thus strengthening the one-edge comparison to every pair of vertices still leaves these near examples. Their failures of the completion hypotheses are explicit above. [Pair-shift checks](scripts/round3_deck.py)

**A forced configuration away from the root.** Choose a zero-boundary failure minimizing order and then size among all rooted 5-edge-connected failures. The splitting and contraction arguments of §10.3 give 5-regularity and reducedness of $H$ for this choice. Its order is at least 14, so $h\ge13$ is odd. Let $A$ be the $k\le5$ distinct root neighbors, and $R=H-A$. Every vertex of $R$ has free degree five. There are $5k-5$ free incidences at $A$, hence
\[
 |E(R)|=\tfrac52(h-1)-(5k-5)+e_H(A),\qquad |V(R)|=h-k.
\]
A theta-free simple graph is a cactus in each connected component. Indeed, any 2-connected block other than a cycle has a chord of a cycle or a path through a component outside a cycle joining two distinct cycle vertices. These give a theta. A cactus on $s\ge1$ vertices has at most $3(s-1)/2$ edges, since each cyclic block adds at least two new vertices and exactly one more edge than new vertices, and each bridge adds one of each. For $h\ge15$, or $h=13$ and $k\le4$, the displayed edge count exceeds this bound. Thus $G-N[z]$ contains three internally vertex-disjoint paths with common endpoints, entirely among vertices untouched by the root.

The one remaining case has $h=13$ and $k=5$. If $R$ is theta-free the same count forces $e_H(A)=0$ and $R$ has eight vertices and ten edges. It is connected since a disconnected cactus on eight vertices has at most nine edges. There are eight possible simple cactus shapes of this order and size with maximum degree at most five. Between $R$ and $A$, every vertex of $A$ has degree four and each vertex $v$ of $R$ requires $5-d_R(v)$ cross edges. Generating all 668 bipartite types with the indicated right degrees and left degrees at most four, 118 match a cactus degree sequence. Permuting within equal-degree classes covers every compatible attachment. Among 10,875 tested labelled completions, the order-five, six and seven strong-subgraph tables exclude 855, 2,373 and 4,306. The other 3,341 each have an exact all-boundaries witness on an induced subgraph. This contradicts reducedness and proves the forced-theta conclusion at order 14 as well. The computation allows all such attachments before any test for essential connectivity. The forced topology supplies a two-dimensional space of shifts. The allowed-set calculation above pinpoints why topology alone does not settle the extension. [Cactus and attachment enumeration](scripts/round3_theta.py)

### 10.6 Formal verification and reproduction

The default build includes the new [BoundaryDeck module](Tutte3Flow/BoundaryDeck.lean). It adds five public kernel-checked theorems in the existing namespace.

| Theorem | Kernel-checked content |
|---|---|
| `boundaryCount_adjoin` | Exact natural-number count after adjoining an edge, as the sum of the two shifted counts |
| `boundaryCount_neighbors_of_gap` | Equality of both neighboring counts to the deletion count at a missing boundary |
| `divergence_add_circulation` | Adding any scalar multiple of a circulation preserves the boundary |
| `triangle_cycle_singletons` | Every class on a normalized three-shift triangle line is a singleton when they are all nonempty |
| `square_cycle_singleton_iff` | An edge is a singleton on a full three-class square precisely when one doubleton class avoids it |

The full graph triangle and square count identities use the line-partition proof in §10.5. The last two Lean theorems certify the finite class calculation. The rest of the inventory is §9.7, with one visibility change. The existing edge-divergence lemma in EdgeInsertion is now public so the counting proof reuses it. The project total is **27 public and seven private theorems**. The audit checked all 34 against the permitted core axioms. The degree and vertex-cover theorems, the polynomial family and the forced-theta proof are recorded in mathematical prose with exact Python tests. The frozen file's SHA-256 before and after the round is **cae23039c18784404fbcb83491226cf7e7cd4a1d8b3d5bfe5f24567493fbbea6**. [Full theorem audit](scripts/round2_audit.py) · [Frozen statement](Tutte3Flow/Challenge.lean)

From the workspace root, use its Python environment with NumPy, SciPy, NetworkX, Numba and nauty's graph and bipartite-graph generators available. All Round 3 inputs are generated deterministically.

~~~sh
/Users/mw/miniconda3/bin/python3 -B scripts/round3_reduced.py
/Users/mw/miniconda3/bin/python3 -B scripts/round3_cores.py
/Users/mw/miniconda3/bin/python3 -B scripts/round3_cover.py
/Users/mw/miniconda3/bin/python3 -B scripts/round3_descent.py
/Users/mw/miniconda3/bin/python3 -B scripts/round3_algebra.py
/Users/mw/miniconda3/bin/python3 -B scripts/round3_deck.py
/Users/mw/miniconda3/bin/python3 -B scripts/round3_theta.py
lake build
/Users/mw/miniconda3/bin/python3 -B scripts/round2_audit.py
shasum -a 256 Tutte3Flow/Challenge.lean
~~~

### 10.7 Remaining implication and publication decision

A failed zero-boundary star needs at least twelve original nonroot degree-five vertices under the essential-six hypotheses (using the cited density theorem). Its reduced quotient needs a vertex cover of at least seven. In a failure minimizing order and size one can also force a theta outside the closed root neighborhood. The remaining implication is to use the **same exterior assignment** to allow three shifts summing to zero on a theta, or to find a nonzero split imbalance by another operation on some free edge. A private point for every edge, exact triangle and square identities, and both boundary shifts available at every pair do not by themselves supply such an assignment. Likewise, high edge connectivity gives no absolute degree cutoff for the chord coefficients on positive instances. No implication here resolves §8.7 in general.

**Formalization and compute decision.** Move the next flagship run to another ProofAtlas target. For Opus, the first independent Round 3 candidate is the six-cover theorem. Its mathematical dependencies are published small-order bounds and reproducible finite certificates. A compact catalogue of induced witnesses with an independently checked isomorphism-cover certificate would make that theorem attractive for kernel formalization. The eleven-degree-five extension is the closer advance on Tutte itself. Before committing to a larger formalization, independently review its $P=7$ descent and Jafari's external density theorem. The Fourier construction is a short standalone obstruction to any bounded-degree certificate in this polynomial, in all tree bases. The Round 1–2 exact-distance family remains a separate candidate for a constructive paper. The literature checked includes pinned flow extension, critical density, and polynomial flow certificates. I found no statement matching the six-cover theorem, the pinned bound on eleven nonroot degree-five vertices or the arbitrary-degree cancellation construction in those sources. Historical priority remains unverified. [Li on pinned extension](https://arxiv.org/abs/2005.00297) · [Árnadóttir et al. on critical canvases](https://arxiv.org/abs/2502.01451) · [Jafari on reduced density](https://arxiv.org/html/2610.07034v4#A2) · [Crump–DeVos–Yeats on graph permanents](https://www.numdam.org/item/10.4171/aihpd/35.pdf)
