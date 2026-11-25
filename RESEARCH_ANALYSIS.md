# Tutte's 3-flow conjecture — research report

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
