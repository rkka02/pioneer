# Catch-Up on consecutive integers — Round 1

**Case C.** Every even-total prefix through $N=47$ evaluated to a draw. The universal conjecture remains unresolved. The five-token game has no first-player losses for any positive distinct weights. The Lean results include a complete four-token classification, the exact outcome of every positive five-term arithmetic progression, an obstruction to induction by adjoining a quartet, and a sufficient condition for a prefix draw involving three-token deletions. The large prefix values come from exact integer minimax. The final section gives reproduction commands.

The original paper gives exact values through 20 and Monte Carlo evidence at 23, 24, 27 and 28. In February 2019, Bernhard von Stengel reported exact computations through 34 and uniqueness of a strictly winning opening. The draws at 23, 24, 27, 28, 31 and 32 therefore replicate cases covered by that report. The local 35, 36, 39, 40, 43, 44 and 47 computations go beyond its stated range. [Original paper, Table 2](https://www.nealen.net/papers/catch-up-a-game-in-which-the-lead-alternates-2015.pdf) · [LSE seminar abstract, pp. 5–6](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf)

## Exact prefix values

All results are from Player 1's perspective. For the complete opening rows, every opening omitted from the third column loses. A row marked “two checked” gives the exact root value by opening reversal. The score-gap solver and the independent named-player solver each verified both non-losing openings in every such row. Additional individual openings in those rows were outside the test.

| $N$ | Total | Drawing openings | Value |
|---:|---:|---|---|
| 0 | 0 | Empty board | Draw |
| 3 | 6 | 1, 3 | Draw |
| 4 | 10 | 1, 2 | Draw |
| 7 | 28 | 1–4 | Draw |
| 8 | 36 | All | Draw |
| 11 | 66 | All except 10 | Draw |
| 12 | 78 | All | Draw |
| 15 | 120 | All | Draw |
| 16 | 136 | All | Draw |
| 19 | 190 | All | Draw |
| 20 | 210 | All | Draw |
| 23 | 276 | All | Draw |
| 24 | 300 | All | Draw |
| 27 | 378 | All | Draw |
| 28 | 406 | All | Draw |
| 31 | 496 | All | Draw |
| 32 | 528 | All | Draw |
| 35 | 630 | All | Draw |
| 36 | 666 | All | Draw |
| 39 | 780 | 1, 2 (two checked) | Draw |
| 40 | 820 | 1, 2 (two checked) | Draw |
| 43 | 946 | 1, 2 (two checked) | Draw |
| 44 | 990 | 1, 2 (two checked) | Draw |
| 47 | 1,128 | 1, 2 (two checked) | Draw |

The verified frontier for this round is $N=47$. The longer $N=48$ search ran for over 50 minutes without completing its first opening. The searches were stopped at the round cutoff, leaving $N=48$ unresolved.

Opening 1 holds in every nonempty row. Opening $N$ loses at 4 and 7. Opening $\lfloor N/2\rfloor$ holds in every complete row. For the odd-total controls through 28, the losing prefixes are 9, 10, 14 and 18. The other odd-total prefixes win. The respective unique winning openings for $N=1,2,5,6,13,17,21,22,25,26$ are $1,2,3,2,1,3,3,2,3,2$.

## Rules used in the computation

Let $R$ be the remaining set and $d$ the opponent's score minus the active player's score. Write $G(R,d)$ for the frozen outcome from the mover's perspective and $R-x$ for $R\setminus\{x\}$. The order of outcomes is loss, draw, win. With negation exchanging win and loss, the pick recurrence on a nonempty board is

$$
G(R,d)=\max_{x\in R}
\begin{cases}
G(R-x,d-x),&x<d,\\
-G(R-x,x-d),&x\ge d .
\end{cases}
$$

The empty board draws at $d=0$ and loses at $d>0$. Equalizing passes the turn. Every first pick from tied scores passes, so $G(S,0)=\operatorname{value}(S)$, including at $S=\varnothing$. Adding the same constant to both scores preserves even the frozen opening flag. The recurrence above agrees with its immediate-loss branch when $d>\sum R$. When $d=\sum R$, the result is a draw. [Lean definitions and proofs](CatchUpGame/ResearchLemmas.lean)

The safe gap cap for a prefix is **the original $N$**. A pick changes $d$ to $|d-x|\le\max(d,x)$. On passing, the new gap is at most the pick just taken. Opening 4 on $[1,4]$ leaves $d=4>\max\{1,2,3\}$ while catching up is feasible. Opening 2 on $[1,2]$ leaves $d=2>\sum\{1\}$. For a fixed initial set, $d$ has the parity of the sum already taken.

Three independent computations exercise different parts of the result.

- **Retrograde C++.** One row per subset stores the winning and losing deficits as two bitsets. For a pick $x$, child bit $j>0$ contributes at parent deficit $x+j$ with the same outcome. Child bits $0\le j\le x$ contribute at parent deficit $x-j$ with the opposite outcome. OR the option win masks and AND the option loss masks. Increasing subset masks form a topological order. This covers every subset and every deficit $0,\ldots,28$ for the 28-token run, using 2 GiB for rows. [Retrograde solver](scripts/retrograde.cpp)
- **Threshold C++.** Two Boolean questions ask whether the mover can win and whether the mover can avoid losing. A passed turn complements the answer to the other question. The search can stop after witnessing a successful pick. Cache hits compare the entire packed key. Replacing a colliding entry only costs time. An optional high-token suffix table packs one parity of gaps per board and supplies exact endgames. At a tied node, opening reversal can exclude a strict win from every alternative to a non-losing opening. The solver accepts arbitrary distinct nonnegative weights within its 64-bit key (token count plus deficit bits plus two flag bits at most 64). [Threshold solver](scripts/threshold.cpp)
- **Named-player C++.** With total $2H$, fix the opening and ask if its owner secures $H$. Use existential choice for that player, universal choice for the opponent, and both absolute scores to update the turn. If the opponent hits exactly $H$, the defender catches up by taking the rest. For a fixed board the scores sum to a known constant, so the cache needs just one score and the active player. The suffix cache can reconstruct the unique gap from its half and its known parity. The optional packed suffix tabulates the same fixed-player goal with opposite bit orders for defender-to-act and opponent-to-act states. The unrestricted runs set the number of permitted choices to $N$. Two successful openings give the root value by the theorem below. [Defense verifier](scripts/defense.cpp)

The Python cross-check instead enumerates **entire turns**. At positive $d$, a nonempty selection $B$ is a legal completed turn exactly when $\sum B\ge d$ and $\sum B-\max B<d$. Put the largest selection last to prove sufficiency. Necessity follows by removing the actual last pick and then comparing with the largest. At $d=0$ enumerate singletons. The insufficient-total branch assigns the rest to the active player. This algorithm computes signed minimax score margins. Taking their signs commutes with maximizing, minimizing and negating, yielding the frozen outcome. Its signs agree with C++ at **all 114,688** board/deficit pairs on $[1,13]$, including unreachable deficits. The scalar threshold search with its suffix table disabled and the retrograde computation also agree at **all 1,048,576** initial subset positions on $[1,20]$. [Whole-turn verifier and census](scripts/research.py)

## Which even-sum subsets are decisive?

There is an exact recursive graph criterion for any distinct set with at least two elements. It reduces classification to games with two tokens removed. For $a<b$, put $M_{ab}=G(S-\{a,b\},b-a)$, measured for the player who opened $a$ when the other player then selects $b$. If a score is already unreachable before the reply, give each nominal reply the forced terminal outcome, as permitted by the one-pick recurrence. Interchanging the two picks leaves the same lower-scoring player active and exchanges their identities. Hence $M_{ba}=-M_{ab}$, even when the second player still has picks left on the same turn. Draw an edge $a\to b$ when $M_{ab}$ is a strict win.

| First-pair graph | Root value |
|---|---|
| Some vertex has a strict edge to every other vertex | P1 win |
| Every vertex has an incoming strict edge | P1 loss |
| Some vertex has no incoming strict edge, and no vertex beats all others | Draw |

Indeed, P2 chooses the worst entry in the row of P1's opening. A strictly winning opening therefore makes every other opening lose. Two unbeaten vertices certify a draw. A single opening whose exact value is draw also certifies the root. Two non-losing openings $a,b$ also force their mutual first-pair value to be exactly draw. Each row guarantees a nonnegative entry against the other, and the entries are negatives. In particular, if every opening draws, **every ordered pair of distinct first picks draws** under optimal continuation. [Opening reversal and its consequences](CatchUpGame/ResearchLemmas.lean) · [Graph evaluator](scripts/research.py)

An arithmetic necessary condition at arbitrary deficit is
$$
 G(R,d)=\mathrm{draw}\ \Longrightarrow\ \exists A\subseteq R,\quad 2\sum A=\sum R+d .
$$
The Lean proof follows a drawing pick and complements the allocation when the turn passes. Conversely, an equal partition at tied scores gives a cooperative drawn play on positive weights. Each player takes only from their assigned half. Whenever their assigned half is exhausted, they have reached the half-total and the other player can finish. For consecutive even-total prefixes, the triple $1+2=3$ when needed and the outer-versus-inner pairs in each remaining quartet give such a partition.

**Closed classification through four positive tokens.** A singleton wins. A two-token initial board $u<v$ wins by opening $v$. For three tokens $a<b<c$, the minimax margin is $|a+b-c|$. For four $a<b<c<d$, it is
$$
 \min\{|a+d-b-c|,\ |a+b+c-d|\}.
$$
Thus through four tokens every partitionable board draws and every other positive nonempty board is won by P1. For any number of tokens, a token larger than the sum of the others wins by opening it. A token equal to that sum gives a drawing opening and hence a drawn game. Multiplying every token by any positive integer preserves the outcome. [Kernel-checked classifications, dominance and scaling](CatchUpGame/ResearchLemmas.lean)

Here is a derivation of the four-token formula. For two tokens $u<v$ and deficit $g$, the margin is $v-u-g$ for $g\le u$, and $u+v-g$ for $g>u$. In the second region the mover can take $u$ and then $v$. In the first, taking either immediately passes. For the four-token board write $t=b+c-d$, $A=a-t$, $B=a+t$, $U=b+d-a-c$, and $V=a+b+d-c$. Both $U$ and $V$ are positive. Substitution into the two-token formula gives the six upper entries of the first-pair margin matrix.

| First pair | Entry |
|---|---|
| $a,b$ | $A$ |
| $a,c$ | $A$ if $c\le a+b$, else $V$ |
| $a,d$ | $-U$ if $d\le a+b$, else $B$ |
| $b,c$ | $U$ if $c\le a+b$, else $V$ |
| $b,d$ | $-A$ if $d\le a+b$, else $B$ |
| $c,d$ | $-A$ if $d\le a+c$, else $B$ |

If $t\ge a$, row $b$ has minimum $t-a$. If $t\le-a$, row $d$ has minimum $-a-t$. In the interior $-a<t<a$ with $d>a+b$, row $a$ has minimum $\min(A,B)$. In the remaining interior case $d\le a+b$ we have $t>0$, and row $d$ has minimum $A$. In each case the exhibited row has nonnegative minimum, so every competing row has a nonpositive entry against it. These four minima give the displayed formula. In particular every isolated four-term consecutive interval draws.

**Five tokens already suffice to break the partition criterion.** On $\{4,5,6,7,8\}$ we have $7+8=4+5+6$, yet opening 4 wins. In increasing opening order the signed margins are $(2,-4,-2,-4,-2)$. On $\{4,5,6,7,12,14\}$ the balanced parts $\{4,6,14\}$ and $\{5,7,12\}$ each sum to 24, yet every opening loses by a minimax margin of 2. Defeating first replies for the six increasing openings are respectively $14,4,4,5,4,6$. Dilation gives infinite families of positive, partitionable examples of each decisive outcome. The two initial outcomes themselves are kernel-checked. [Lean witnesses](CatchUpGame/ResearchLemmas.lean) · [Margin and first-reply calculation](scripts/research.py)

**Five-term arithmetic progressions have a kernel-checked classification.** For $a,r>0$, the initial game on $a,a+r,a+2r,a+3r,a+4r$ draws exactly when $a=2r$. Otherwise P1 wins. When $0<a<r$ or $a>2r$, opening $a$ wins. When $r\le a<2r$, opening $a+2r$ wins. These claims follow by checking all four first replies using the three-token deficit formula. At $a=2r$, dilation reduces the game to $\{2,3,4,5,6\}$, whose drawing openings are 2 and 6. This proof works directly against the frozen outcome and is independent of the determinant computation below. [Five-term progression theorem](CatchUpGame/ResearchLemmas.lean)

The census covers all $2^{19}=524{,}288$ even-sum subsets of $[1,20]$ and all $2^{27}=134{,}217{,}728$ even-sum subsets of $[1,28]$, including the empty set. Partitionability was tested separately on every board. The C++ implementation splits the board into low and high halves and checks whether their attainable sums can add to half the total. Its $[1,20]$ table agrees entry for entry with the separate Python subset-sum computation. W, D and L are measured for P1.

| Size | $[1,20]$ unpartitionable W / L | $[1,20]$ partitionable W / D / L | $[1,28]$ unpartitionable W / L | $[1,28]$ partitionable W / D / L |
|---:|---:|---:|---:|---:|
| 0 | 0 / 0 | 0 / 1 / 0 | 0 / 0 | 0 / 1 / 0 |
| 1 | 10 / 0 | 0 / 0 / 0 | 14 / 0 | 0 / 0 / 0 |
| 2 | 90 / 0 | 0 / 0 / 0 | 182 / 0 | 0 / 0 / 0 |
| 3 | 480 / 0 | 0 / 90 / 0 | 1,456 / 0 | 0 / 182 / 0 |
| 4 | 1,773 / 0 | 0 / 672 / 0 | 8,278 / 0 | 0 / 2,005 / 0 |
| 5 | 4,280 / 0 | 307 / 3,165 / 0 | 33,057 / 0 | 1,495 / 14,588 / 0 |
| 6 | 5,651 / 110 | 2,365 / 11,182 / 12 | 85,278 / 1,302 | 19,538 / 81,990 / 80 |
| 7 | 2,746 / 132 | 6,576 / 29,230 / 76 | 118,648 / 4,797 | 115,241 / 352,093 / 1,241 |
| 8 | 218 / 11 | 7,269 / 55,480 / 112 | 59,071 / 4,178 | 329,178 / 1,154,013 / 8,113 |
| 9 | 6 / 1 | 4,038 / 79,909 / 26 | 7,074 / 503 | 476,446 / 2,960,836 / 8,591 |
| 10 | 0 / 1 | 1,279 / 90,970 / 2 | 641 / 104 | 428,567 / 6,127,269 / 3,973 |
| 11 | 0 / 0 | 254 / 83,726 / 0 | 151 / 34 | 277,636 / 10,458,672 / 597 |
| 12 | 0 / 0 | 20 / 63,070 / 0 | 32 / 10 | 136,534 / 15,075,666 / 137 |
| 13 | 0 / 0 | 1 / 38,759 / 0 | 7 / 0 | 49,846 / 18,671,226 / 1 |
| 14 | 0 / 0 | 0 / 19,320 / 0 | 0 / 1 | 13,317 / 20,043,255 / 11 |
| 15 | 0 / 0 | 0 / 7,752 / 0 | 0 / 0 | 2,398 / 18,718,682 / 0 |
| 16 | 0 / 0 | 0 / 2,445 / 0 | 0 / 0 | 315 / 15,212,064 / 0 |
| 17 | 0 / 0 | 0 / 570 / 0 | 0 / 0 | 20 / 10,737,070 / 0 |
| 18 | 0 / 0 | 0 / 90 / 0 | 0 / 0 | 1 / 6,560,553 / 0 |
| 19 and up | 0 / 0 | 0 / 11 / 0 | 0 / 0 | 0 / 5,849,469 / 0 |
| **All** | **15,254 / 255** | **22,109 / 486,442 / 228** | **313,889 / 10,929** | **1,850,532 / 132,019,634 / 22,744** |

Every even-sum subset of $[1,28]$ with 19 or more tokens draws, covering 5,849,469 boards. Exactly one 18-token board is decisive. It is $\{1,2,3,13,14,15\}\cup[17,28]$, and 13 is its unique winning opening. Fourteen is the largest cardinality admitting a first-player loss in this box. The independent threshold search confirms, for example, that all 14 openings of $\{3,5,6,8,15,16,18,19,20,21,23,24,25,27\}$ lose. [Census and example masks](scripts/retrograde.cpp) · [Independent Python census](scripts/research.py)

A density bound survives the full enumeration. For every nonempty even-sum $S$ with $M=\max S\le28$, the strict inequality $3|S|>2M+1$ implies a draw. All 4,638,228 boards satisfying this test drew. Of the 3,322,049 that contain token 1, opening 1 holds on all but $\{1,2,3,4,6\}$, whose drawing openings are 2 and 3. The strict boundary matters. The 7-token board $\{1,2,5,6,7,9,10\}$ and the 9-token board $\{1,2,6,7,8,10,11,12,13\}$ both satisfy $3|S|=2M+1$ and are P1 wins. The solver tests each board at its actual maximum and checks the child of opening 1 independently of the root outcome. The density implication beyond the enumerated range is a candidate generalization. [Density and opening checks](scripts/retrograde.cpp)

A separate search tested the density boundary on structured larger boards. For each $29\le M\le36$, take $k=\lfloor(2M+1)/3\rfloor+1$ tokens in a low interval $[1,p]$, $0\le p\le6$, and a disjoint high interval ending at $M$ with at most one token below $M$ removed. The code keeps a gap between the two intervals, removes duplicate descriptions, and tests every even-total board of that form. All 554 draw. [Family generator](scripts/research.py) · [Subset queries](scripts/threshold.cpp)

The unpartitionable even-sum board $\{3,6,7,9,10,13\}$ loses. The graph criterion decides an individual larger set. A closed arithmetic classification for arbitrary cardinality is still open in this analysis.

### A global five-token result

**Player 1 can never lose on five distinct positive tokens. Every drawn five-token board has exactly two drawing openings.** Hence six is the minimum number of distinct positive tokens on which Player 1 can lose, even if an equal partition is required. The upper bound is the Lean witness $\{4,5,6,7,12,14\}$. The lower bound uses the following finite reduction and a two-implementation exhaustive calculation.

For $m$ labelled positive integer weights $w=(w_1,\ldots,w_m)$ in strictly increasing order, record the sign of $\epsilon\cdot w$ for every $\epsilon\in\{-1,0,1\}^m$. These signs determine the entire game tree with its outcome labels. At any history both score comparisons and the frozen insufficient-total comparison are differences between sums of disjoint sets of tokens. Consequently, two weight vectors with the same signs induce identical passes, terminals and optimal opening outcomes. Equality signs must be preserved as well.

**Finite representative lemma.** Every such sign pattern has a strictly increasing positive integer representative with largest entry at most $\lfloor m^{m/2}\rfloor$. To prove this, keep the zero forms as equalities. Orient each nonzero form to be positive and require it to be at least 1. The original integer vector is feasible. These constraints include positivity and strict order. Minimize the sum of coordinates, then choose the lexicographically least minimizer. Existence follows by intersecting with the closed bounded sublevel set given by the original sum. At this point the active constraint normals span $\mathbb R^m$. Otherwise move a sufficiently small amount in either direction along a nonzero vector orthogonal to them. All inactive constraints still hold, and one direction decreases the sum or decreases the lexicographic choice at constant sum.

Choose $m$ independent active rows to form a square integer matrix $B$. Its entries belong to $\{-1,0,1\}$ and its right-hand side to $\{0,1\}^m$. Multiplying the minimizer by $|\det B|\ge1$ gives a positive integer vector with the same signs. By Cramer's rule each of its coordinates is the absolute value of a determinant with entries in $\{-1,0,1\}$. Hadamard's inequality bounds this by the product of its row norms, at most $m^{m/2}$. This proves the lemma. The representative preserves opening outcome signs even when its sum has different parity from the original. An extra coordinate for an initial deficit gives the same finite-representative argument for fixed-size subgames.

For $m=5$ the bound is 55. All $\binom{55}{5}=3{,}478{,}761$ increasing boards were enumerated. One evaluator uses the ten first-pair entries and the two-token margin formula. A separate absolute-score evaluator explores the entire pick tree from each prescribed opening. They agree on **17,393,805 individual opening margins**. The roots comprise 3,210,932 wins, 267,829 draws and **zero losses**. Every one of those drawn boards has exactly two drawing openings. This proves the two assertions for unbounded weights by the finite representative lemma. The numeric counts are for the enumerated boards and weight each representative separately. In particular a five-token board wins exactly when one opening strictly defeats all four alternatives in the first-pair matrix, and all other such boards draw. Its ten entries are determined by the two-token formula and a maximum over three picks. This five-token result is computer-assisted. The four-token formula and six-token witness have separate Lean kernel proofs. [Both five-token implementations](scripts/five.cpp)

## What the strategy tests rule out

A genuine copycat strategy works in the multiset variant when every positive weight has even multiplicity. From a tie, P2 answers each P1 pick with an equal copy and restores a tie. P1 can also force equality. Open with the smallest weight $m$. P1 now leads by $m$, and only $m$ has odd remaining multiplicity. P2 must pass after one pick because all live weights are at least $m$. If P2 takes $y>m$, P1 takes another $y$, restoring the lead and the multiplicity invariant. If P2 takes $m$, equal scores and even multiplicities have been restored with P1 to act. Repeating proves the multiset result. For the distinct interval, requiring an available adjacent mate $(1,2),(3,4),\ldots$ as the first pick of each defender turn gives guaranteed margins $(0,0)$ at 4, $(-2,-2)$ at 8 and $(-4,-4)$ at 12, measured for each constrained player.

On $[1,7]$, the legal pick history $2,3,5,4,7$ leaves $\{1,6\}$ and deficit 7. The mover takes everything and draws. The identical history on $[1,11]$ leaves $\{1,6,8,9,10,11\}$ at deficit 7. Taking 1 first wins by a minimax margin of 2. Every other first pick there draws. Thus a reachable drawn subgame can become winning when the next consecutive quartet is adjoined. Another example occurs on lifting $[1,8]$ to $[1,12]$ after $1,6,2,3,8$. Also, the two disjoint additive triples $\{2,7,9\}$ and $\{4,6,10\}$ draw individually, and their union is won by opening 4. [Kernel proofs of the first lift and the union](CatchUpGame/ResearchLemmas.lean) · [Whole-turn search](scripts/research.py)

The following margins are guaranteed by the constrained player when the opponent is unrestricted. Each entry gives (P1 using the rule, P2 using the rule), in each case measured for the player using it. P1 has a free initial opening. The minimum-overshoot policy may optimize amongst all completed turns tied for least overshoot. The complement rule requires the mate $N+1-x$ of the opponent's last pick as the first pick of the next turn whenever available, with all other choices free.

| $N$ | Smallest available | Largest available | Minimum overshoot | Complement when available |
|---:|---:|---:|---:|---:|
| 4 | −2, −4 | 0, −2 | −2, −4 | 0, −2 |
| 8 | −6, −8 | −2, −4 | −6, −8 | −4, −8 |
| 12 | −10, −12 | −4, −4 | −10, −12 | −10, −12 |

Requiring a defender to take an exact catch whenever one is possible also fails. At $N=8$, requiring any completed turn with sum equal to the deficit, with free play when none exists, changes the guaranteed margins to $(−4,−4)$. The weaker rule that requires an exact one-token catch only when the deficit itself is available gives $(−2,−2)$. At $N=12$ these two pairs become $(−8,−8)$ and $(−4,−4)$. Thus a proof using immediate equalization needs a condition on the resulting tied board.

The players also cannot generally force the **exact final score** against an opponent who deliberately seeks any unequal finish. At $N=3$, P1 can force equality by opening 3, and P2 can force it after every opening. At $N=4,7,8$, P1 has no such opening, and the openings after which P2 can force equality are respectively $\{2,3,4\}$, $\{5,6,7\}$ and $\{7,8\}$. At $N=11,12,15,16,19,20$, neither player can force exact equality after any prescribed opening. The search uses existential choices for the designated player and universal choices for their opponent, with equality as the sole successful terminal. [Whole-turn equality and restriction tests](scripts/research.py)

Endpoint choice also has limits. From openings 1 and 2 at $N=7$, restricting the defender to the smallest or largest remaining token loses both defenses. Allowing either of the two smallest or two largest saves both at 7, 8, 11 and 12. At 19 and 20, both of those opening defenses fail even under the enlarged rule. This tests the specified openings. [Constrained defense search](scripts/defense.cpp)

To inspect the optimal trees, we counted all first-pair positions $a<b$. The counts W / D / L for the lower opener are 1 / 2 / 0 at $N=3$, 3 / 3 / 0 at 4, 9 / 12 / 0 at 7, and 3 / 52 / 0 at 11. At 8, 12, 15, 16, 19 and 20, all $\binom N2$ such positions draw. At each of these ten small sizes, choosing the least currently optimal pick yields the play that takes $1,\ldots,\lfloor N/2\rfloor$ in order, then alternates the largest and smallest available token. At 8 this is $1,2,3,4,8,5,7,6$. The policy tests above allow adversarial deviations from such a principal variation. [Tree inspection](scripts/research.py)

## Round 2 — tied boards with an additive triple removed

Let $I=[1,N]$. The shortest reduction found in this round uses **one positive-deficit position and one family of tied boards**. Lean proves it in `draw_of_first_ray`. For $N\ge2$, it is enough that

1. $G(I-\{1,2\},1)=\mathrm{draw}$.
2. For each $3\le b\le N$, the opener of the tied board $I-\{1,b,b-1\}$ cannot win.

Open 1. After reply $b\ge3$, P1 takes $b-1$, ties immediately and hands P2 the board in condition 2. Against reply 2, condition 1 supplies the drawing continuation. Opening 1 therefore holds against every reply, and reply 2 prevents it from winning. P2's strategy also has a direct description. Against opening $b\ge3$, take 1 and then $b-1$ in the same turn. The scores tie, and P1 receives the board from condition 2. Against opening 2, take 1 and continue at deficit 1 on the boundary board. Against opening 1, take 2 and pass that same boundary position to P1. This supplies a defense for each player and proves the root draw. [One-opening reduction](CatchUpGame/ResearchLemmas.lean)

Lean also proves `hold_by_exact_subset`. If positive live tokens form a subset $C$ whose sum equals the current deficit and the opener of the tied remainder $R\setminus C$ cannot win, the current player can hold. Every proper prefix of the chosen tokens has sum strictly below the deficit, so the player is allowed to finish the entire subset and passes precisely at equality. This extends the single-token response $b-1$ to boards in which that token is missing. [Exact catch with several picks](CatchUpGame/ResearchLemmas.lean)

There is a second sufficient certificate in `draw_of_anchor_tests` for $N\ge4$. It verifies that opening 2 also holds against every response. Its three hypotheses are as follows.

1. $G(I-\{1,2\},1)=\mathrm{draw}$.
2. $G(I-\{2,4\},2)\ne\mathrm{loss}$.
3. For $a=1,2$ and every $a<b\le N$ with $b\ne 2a$, the tied board $I-\{a,b,b-a\}$ is a loss or draw for its opener.

To see how this supplies both defenses, open $a\in\{1,2\}$. After a larger reply $b$, P1 is behind by $b-a$. If $b\ne2a$, take the live token $b-a$ itself and pass at equality. Hypothesis 3 says P2 cannot win from there. The pair $1,2$ needs hypothesis 1 in both orders. The pair $2,4$ needs hypothesis 2 in its lower-first order. These possibilities exhaust the opponent's first picks. Now both openings hold, so reversal supplies P2 a defense against every opening. [Formal reduction](CatchUpGame/ResearchLemmas.lean)

At every admissible $N=11,12,15,16,19,20,23,24,27,28,31,32,35,36,39,40,43$, all $N-2$ eligible deletions for $a=1$ draw, as do all $N-3$ for $a=2$, and both exceptional gap positions draw. At $N=43$ this comprises 41 and 40 tied boards respectively. Through 28, both C++ implementations independently evaluated the deletion tests. Counts are per anchor, so a three-token set can occur in both columns. The small failures tell us where induction can start. At $N=4,7,8$ the counts of tied-deletion **wins** for anchors 1 and 2 are respectively $(2,1),(2,1),(1,1)$. Separately, for every admissible $7\le N\le28$, deleting any two same-parity tokens and starting again tied gives a draw. At $N=28$ this covers all 182 such pairs. The two-deletion experiment concerns tied scores, whereas the exceptional tests above use positive deficits. [Full deletion table through 28](scripts/retrograde.cpp) · [Threshold deletion tests through 43](scripts/threshold.cpp)

The positive-deficit boundary $G([3,N],1)$ also follows directly from the two verified non-losing openings 1 and 2. In particular this boundary is a draw at $N=47$.

The next proof target is to exclude a strict winning opener on the tied boards $I-\{1,b-1,b\}$ of the shorter reduction. By opening reversal it suffices to exhibit one exact drawing opening or two non-losing openings on each such board. A related first-pair program and existing endpoint results are recorded in the public Catch-Up research handoff. [Research handoff](https://github.com/bocowgill-collaborations/catch-up-research/blob/main/docs/research-handoff.md)

The density test gives a precise candidate for the tied-board part. If $N\ge11$ then the three-deletion boards have $3(N-3)>2N+1$, wherever their largest surviving token lies. Proving the density implication for all even-sum boards would itself settle the prefix conjecture. Its restricted form for three holes suffices for the tied-board hypothesis above.

For $a=1$ the holes are $1,b-1,b$. For $a=2$ they are $2,b-2,b$. A proposed induction can therefore track the locations of a missing adjacent or distance-two pair and state explicitly how an opponent's move changes those locations. The shorter reduction needs only the $1,2$ boundary. It leaves $\{3,\ldots,N\}$ at deficit 1, where an immediate exact catch is impossible. Proving this boundary draw and the adjacent-hole statement uniformly would settle all remaining prefixes. The distance-two holes and the $2,4$ boundary belong to the additional opening-2 certificate. The reachable quartet counterexample above is a regression test for any attempt to discard the holes or the deficit.

## Reproduction and assurance

Run these commands from the problem directory with Lean 4.36.0 and a C++17 compiler.

```sh
clang++ -O3 -march=native -std=c++17 scripts/retrograde.cpp -o /tmp/catch-retro
clang++ -O3 -march=native -std=c++17 scripts/threshold.cpp -o /tmp/catch-th
clang++ -O3 -march=native -std=c++17 scripts/defense.cpp -o /tmp/catch-defense
clang++ -O3 -march=native -std=c++17 scripts/five.cpp -o /tmp/catch-five
/tmp/catch-five

/tmp/catch-retro 28
/tmp/catch-retro 28 --anchors
/tmp/catch-retro 28 --census
/tmp/catch-retro 28 --density
/tmp/catch-th --anchors --small-first --endgame 22 --cache-bits 24 31 32 35 36
/tmp/catch-th --small-first --endgame 22 --cache-bits 24 31 32 35 36
/tmp/catch-th --two --small-first --endgame 24 --cache-bits 25 39 40
/tmp/catch-th --two --small-first --endgame 26 --cache-bits 25 43 44
/tmp/catch-th --two --small-first --endgame 28 --cache-bits 25 47
/tmp/catch-th --anchors --small-first --endgame 26 --cache-bits 24 39 40 43
/tmp/catch-defense 39 24 39 1 2
/tmp/catch-defense 40 24 40 1 2
/tmp/catch-defense 43 26 43 1 2
/tmp/catch-defense 44 26 44 1 2
/tmp/catch-defense 47 28 47 --packed 1 2

# Next unverified prefix
/tmp/catch-th --two --small-first --endgame 28 --cache-bits 25 48
/tmp/catch-defense 48 28 48 --packed 1 2

python3 scripts/research.py audit /tmp/catch-retro 13
python3 scripts/research.py compare-roots /tmp/catch-retro /tmp/catch-th 20
python3 scripts/research.py census /tmp/catch-retro 20
python3 scripts/research.py study /tmp/catch-retro 20
python3 scripts/research.py equality 3 4 7 8 11 12 15 16 19 20
python3 scripts/research.py density /tmp/catch-th 29 36
python3 scripts/research.py position 7 1 6 8 9 10 11
python3 scripts/research.py graph 4 5 6 7 12 14
python3 scripts/research.py set 4 5 6 7 8
/tmp/catch-th --set --small-first 4 5 6 7 12 14
/tmp/catch-th --set --gap 7 1 6 8 9 10 11
/tmp/catch-defense 8 4 8 --packed --reply 1 2
/tmp/catch-defense 19 0 2 --ends 1 2

python3 scripts/audit.py
```

The Python set evaluator accepts arbitrary-size integer weights and treats repeated inputs as distinct tokens, so it can also explore multisets. The frozen theorem uses finsets. Runtime of the unrestricted solvers grows exponentially. A restricted-defense `fails` output only rules out the specified policy.

The Lean audit builds the default library, executes `#print axioms` on all 46 public research definitions and theorems, and checks the output against `propext`, `Classical.choice` and `Quot.sound`. The library opts into Lake's legacy import format for the frozen source. The SHA-256 verified before and after the round is `0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3`. Lean proves the frozen implication for every $N\le12$. Its Boolean search short-circuits at successful moves, and `canReach_correct` proves that both Boolean thresholds agree with the list evaluator. The larger prefix values in the table come from the exact C++ searches. [Lean module](CatchUpGame/ResearchLemmas.lean) · [Axiom and integrity audit](scripts/audit.py)

## Round 2

**Case C. The prefix $N=48$ is an exact draw.** Openings 1 and 2 each guarantee P1 at least 588 points. Opening reversal supplies the upper bound. The universal conjecture remains open in this project. The fixed-point question has an exact answer for arbitrary distinct positive weights. The only nonempty tied board on which a defender can always hand back a lead of at most two is $\{1,2,3\}$. More generally, a persistent absolute cap $K$ requires $\lvert S\rvert \le4K$. A different pairing strategy does work on unbounded families once the defender has a sufficient lead. These results concern either designated player against unrestricted opposition. [Lean proofs](CatchUpGame/ResearchLemmas.lean)

### The exact-catch and small-overshoot fixed points

Write $O(R,d)$ when the opponent acts $d$ behind the designated defender, and $D(R,d)$ when the defender acts $d$ behind the opponent. A handoff happens at the first pick that reaches or crosses equality. The defender must avoid a final loss and obey the cap even on their final handoff. At $O(R,0)$ the opponent opens. For the requested search inside the ordinary drawn boards, each tied reentry must belong to that domain. A **persistent** cap allows successive capped handoffs. An **isolated** overshoot requires the defender's next completed turn to restore equality if play reaches that turn. The latter implements the proposed two-step return. In the optional **winning exit** experiment the defender may switch to unrestricted play at a position where ordinary minimax already gives that defender a strict win. [Fixed-point evaluator](scripts/closure.cpp)

For pure exact catches the greatest fixed point is $\{\varnothing\}$. An opponent can always open the minimum. Every nonempty subset of the remainder exceeds it, and the empty subset has sum zero. In particular, allowing the defender to choose *which* exact subset to take does not change this result. The independent bit scan rejects all 524,287 nonempty even boards in $[1,20]$ and all 8,388,607 in $[1,24]$. The two scans took under 0.01 seconds and 0.04 seconds, respectively, at the timer’s 0.01-second resolution. Even an opening that *can* be matched can require an overshoot. On $[1,8]$, an opening of 3 has the unique exact response $\{1,2\}$, handing the opponent the strictly winning board $[4,8]$. [Minimum obstruction and five-token witness](CatchUpGame/ResearchLemmas.lean)

The following classification holds without any parity assumption or maximum-weight cutoff. Every listed board works, and every omitted one fails. Intersecting it with the draw-domain condition at ties leaves the same list.

| Opponent's deficit $d$ | All $R$ with $O(R,d)$ under persistent cap 2 |
|---:|---|
| 0 | $\varnothing$, $\{1,2,3\}$ |
| 1 | $\varnothing$, $\{1\}$, and $\{a,a+1\}$ for every $a\ge1$ |
| 2 | $\varnothing$, $\{1\}$, $\{2\}$ |

To see the induction, let $m$ be the minimum. When $m\ge d$, playing $m$ gives the defender deficit $m-d$. Every remaining token $y$ exceeds it, so the defender must reply with a singleton and the next lead is $d+y-m$. From lead 1 only $y=m+1$ fits. From lead 2 no larger token fits. If $m=1<d=2$, the opponent can instead continue picking at deficit 1. Applying the smaller-board classification leaves only a few exceptional shapes. An alternative opening of $a$ refutes $\{1,a,a+1\}$ at deficit 2 for $a\ge2$. An opening of $a+1$ refutes a tied pair of disjoint adjacent pairs $\{a,a+1,b,b+1\}$ with $a+1<b$. For the surviving triple the replies to openings 1, 2, 3 can be 3, 3, and the sequence $1,2$. The induction and converse are in `capped_two_iff`. [Kernel proof](CatchUpGame/ResearchLemmas.lean)

The same minimum argument gives the general cap obstruction. While all tokens exceed $K$, each such round consumes two tokens and increases the lead by at least one. Thus $\lvert R\rvert \le2(K-d)$ there. With low tokens present, follow the minimum again. A continuing opponent pick removes one low token, and a completed round starting with a low token removes at most two tokens before returning control to the opponent. Strong induction gives $\lvert R\rvert \le2K+2\lvert \{x\in R:x\le K\}\rvert \le4K$ for distinct positive weights and $d\le K$. There is no fixed $K$ that covers all prefixes under this policy. For example, on $[1,8]$ after opening 1, reply 2 allows successive minimum opponent picks 3 and 5. Reply 4 is forced after 3 and no cap-two reply exists after 5. The only other permitted first reply, 3, allows the opponent to tie with 2, leaving $[4,8]$ for the defender to open. [Cardinality bounds](CatchUpGame/ResearchLemmas.lean)

**Exact counts.** Each cap-two entry is the number of tied members, including the empty board. The recursion visits strict subsets only, so the equations determine a unique fixed point, hence the greatest one. At an opponent node the recurrence intersects the sets of allowed continuations for all legal picks. At a defender node it takes their union and filters the outgoing lead on each handoff. This considers multi-pick turns and every legal ordering. The packed table stores the parity $d\equiv\sum R\pmod 2$ relevant to an even starting total. [Evaluator](scripts/closure.cpp) · [Independent completed-turn evaluator](scripts/round2.py)

| Universe | Pure exact | Persistent 2 | Isolated 2 | Persistent 2 with winning exits | Isolated 2 with winning exits |
|---|---:|---:|---:|---:|---:|
| $[1,20]$ | 1 | 2 | 2 | 35 | 12 |
| $[1,24]$ | 1 | 2 | 2 | 198 | 45 |
| $[1,28]$ | 1 | 2 | 2 | 853 | 135 |

In both winning-exit variants the only nonempty admissible prefix accepted through 28 is $[1,3]$. This rules out each of the proposed larger prefixes at 15, 16, 19, 20, 23, and 24 under either interpretation. For a persistent cap of **one** the literal tied counts at 20 and 24 are both one.

| Cap-two policy on $[1,28]$ | $O(R,1)$ | $O(R,2)$ | $D(R,1)$ | $D(R,2)$ |
|---|---:|---:|---:|---:|
| Persistent | 28 | 2 | 29 | 54 |
| Isolated | 1 | 2 | 4 | 5 |
| Persistent with winning exits | 10,387 | 217,529 | 1,778,370 | 2,419,318 |
| Isolated with winning exits | 4,154 | 206,984 | 1,767,753 | 2,398,728 |

These lists also characterize the defender-to-act companion explicitly. For $d>0$, choose a nonempty $C\subseteq R$, let $g=\sum C-d$, and require $0\le g\le2$, $\max C>g$, and $O(R\setminus C,g)$ from the classification. This is necessary and sufficient. In a legal completed turn its last token exceeds $g$. Conversely, place $\max C$ last. The preceding sum is then below $d$ and every preceding prefix is legal. At $d=0$ a nonterminal completed turn is a single pick. The Lean theorem for a prescribed overshoot splits the turn into preparatory tokens and a last token. A positive residual deficit before that final token guarantees the turn stays with the defender during preparation. For isolated overshoots, the positive-lead opponent list loses the adjacent pairs at $d=1$. Opening the smaller of an adjacent pair forces a second positive handoff. The singleton and empty cases still work, and the tied list stays the same. The defender-to-act rule uses $g=0$ when an exact return is due. [Whole-turn checker](scripts/round2.py)

For the one-cycle induction test, a tied return to the whole candidate class is accepted as an induction hypothesis, even when that specific class member would itself fail a later turn. The defender may exact-catch or use an isolated overshoot of 1 or 2. The table counts candidate roots that survive *all* opponent openings under that hypothesis. All columns include the empty board. The first failure in each class is $[1,4]$. With winning exits the third density success is $\{2,3,4,5\}$. [Class and induction tests](scripts/closure.cpp)

| Tied hypothesis on $[1,28]$ | Candidate boards | Successful roots | With winning exits |
|---|---:|---:|---:|
| $3\lvert S\rvert >2\max S+1$ | 4,638,229 | 2 | 3 |
| Complete lower bank reaching the maximum | 23,433,227 | 2 | 2 |
| Both conditions | 2,136,960 | 2 | 2 |

### When bank and pairing arguments work

**A complete bank can coexist with a winning opening.** Take
$$
S=\{1,2,3,7,9,11,14,15,22\},\qquad B=\{1,2,3,7,9\}.
$$
The bank realizes every sum from 0 to 22. The entire board realizes every sum from 0 to 84 by the same sorted-prefix coverage criterion. Its opening margins in increasing token order are $(-2,2,-2,-2,-4,-4,-6,-8,-8)$. Opening 2 wins. Lean independently certifies the complete bank and the win. Thus a gap anywhere in the board's subset sums cannot be necessary for a decisive outcome. For the earlier board $\{1,2,3,13,14,15\}\cup[17,28]$, 7 is indeed missing and opening 13 wins, but the new witness rules out that proposed explanation as a general criterion. [Lean witness](CatchUpGame/ResearchLemmas.lean) · [Opening-margin evaluator](scripts/research.py)

Among all nonempty even-total boards in $[1,28]$, 23,433,226 have a complete bank below the maximum whose sum reaches the maximum. Of these, 151 win, 23,433,075 draw, and zero lose. Requiring an actual low interval $[1,k]$ with $k(k+1)/2\ge\max S$ and a nonempty upper part gives 1,057,042 draws and zero decisive outcomes. Even here 22 boards lose on opening 1. A reproducible sample of another 7,948 boards with $7\le k\le12$ and up to eight upper tokens also gave all draws. The interval-bank condition remains an empirical candidate. [Exhaustive bank scan](scripts/retrograde.cpp) · [Larger-board generator](scripts/round2.py)

**An unbounded paired class with a bank.** Suppose the defender already leads by $d$. Write the remaining board as a disjoint bank $B$ and high pairs $(u_i,v_i)$, $u_i<v_i$. Put $W=\sum B$ and $E=\sum_i(v_i-u_i)$. The defender can hold whenever both inequalities below hold.
$$
W+E\le d,\qquad d+E\le x\quad\text{for every high token }x.
$$
If $W+E<d$, the defender wins. An opponent bank pick reduces $W$ and the defender's lead by the same amount. While any high pair remains, such a pick stays below the catch threshold. An opponent high pick $x$ passes the turn. The defender takes its mate $y$, which legally catches, and the new lead is $d+y-x$. The spread drops by $\lvert y-x\rvert $, preserving both inequalities, including a strict lower inequality when present. With only the bank left the opponent can score at most $W$. This gives a causal response for every opponent move, including several bank picks in one turn. The bank can have arbitrary gaps. [`bank_and_pairs` and the paired-interval theorem](CatchUpGame/ResearchLemmas.lean)

In particular, when $n\le d$ and $d+n\le a$, the mover on $[a,a+2n-1]$ at deficit $d$ cannot win. Pair consecutive tokens. Along the path of successive minimum picks from an eligible prefix this proves the leading player's side at $([2k+1,4k],k)$ and $([2k+2,4k+3],k+1)$. The moving player's side requires a different argument. For example, on the paired board $\{6,7,10,11,13,14\}$ at deficit 3, the mover loses by 2 under optimal play. [Interval theorem](CatchUpGame/ResearchLemmas.lean) · [Exact margin calculator](scripts/research.py)

**Only the maximum can save the mover on one infinite interval family.** For $n>0$ and $a\ge2n+1$, the mover on $[a,a+2n-1]$ at deficit $n$ loses after every pick below $a+2n-1$. Consequently the position draws if and only if picking the maximum holds. This includes the critical positions $([2k+1,4k],k)$ for the $4k$ prefixes.

For the strict paired win used here, it suffices that $E<d$ and $d+E\le z+1$ for each remaining token $z$. Whenever there is a live pair its spread is at least one, so every opponent pick still reaches the threshold. If the mover chooses $x=a+2i$, reply with $x+1$. The new lead and total spread are $n+1$ and $n-1$. If the mover chooses a nonmaximum $x=a+2i+1$, reply with $x+2$ and pair $x-1$ with $x+1$. The other pairs remain adjacent, the lead becomes $n+2$, and the total spread is $n$. In both cases the revised pairing guarantees a strict win. The original paired-interval bound rules out a strict win for the mover at the root. What remains for a uniform **draw** in this interval family is a single move, whose odd-length child on the $4k$ branch is $([2k+1,4k-1],3k)$. This child draws for every $1\le k\le14$, covering the boundary inside the $N=52,56$ games as well. More precisely, for every $3\le k\le14$ all $2k-1$ picks on the child draw. Equivalently, removing any $x$ from $[2k+1,4k-1]$ gives a draw at deficit $\lvert 3k-x\rvert$. At $k=2$ the middle choice 6 loses, and the two endpoints draw. [`high_interval_only_max` and `high_interval_draw_iff_max`](CatchUpGame/ResearchLemmas.lean)

**A density repair with explicit slack.** In $[1,M]$ there are $\lfloor(x-1)/2\rfloor$ disjoint pairs of distinct positive tokens summing to $x\le M$. If there are $h$ holes, then $x\ge2h+3$ suffices. Fewer holes than the number of pairs leave at least one pair $\{u,v\}$ intact after opening $x$. Taking $u$ then $v$ is legal and returns to equality. If $3\lvert S\rvert >2M+10$, the remaining board still satisfies $3\lvert R\rvert >2M+1$, since exactly three tokens were removed. This proves a defensive step for large openings sufficiently far above the density threshold. Small openings and the lowest density layers remain open. [`exact_pair_of_few_holes` and `dense_pair_repair`](CatchUpGame/ResearchLemmas.lean)

For maximum exactly 29 the complete minimax table gives 5,848,754 draws in the strict density class. For maximum exactly 30 it gives 8,244,773. Across both layers there are zero wins and zero losses. At maximum 31 a further 11,482,544 qualifying boards all draw. The exhaustive nonempty density count through 31 is **30,214,299 draws and zero exceptions**. The new contiguous-bank layers at 29, 30, and 31 have 524,288, 1,048,576, and 2,097,152 draws and zero decisive boards, bringing that total to 4,727,058. Each board is classified at its own maximum. [Parity-packed minimax and density scan](scripts/closure.cpp)

### Adaptive leads and the interval boundary

For an absolute cap the smallest successful values are already close to the largest token. Each ordered pair below gives the minimum for P2 at the tied root and for P1 after opening 1. The exhaustive cap search allows all tied reentries.

| $N$ | 3 | 4 | 7 | 8 | 11 | 12 | 15 | 16 | 19 | 20 | 23 | 24 | 27 | 28 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Minimum caps | 2,2 | 3,3 | 6,5 | 7,7 | 9,9 | 10,10 | 12,12 | 13,13 | 16,16 | 17,17 | 19,19 | 20,20 | 23,23 | 24,24 |

A cap based on the *rank* of a remaining token behaves differently. At each handoff allow a lead up to the $r$-th smallest token remaining **after** the handoff. With fewer than $r$ tokens remaining, allow every lead. In the following test both players are evaluated separately as the designated defender, all tied reentries are available, and play continues under the rule to the terminal score. The fixed-point computation for this test uses **no ordinary minimax table**. Through 28 the two implementations agree wherever compared. [Bottom-up closure](scripts/closure.cpp) · [Top-down designated-player search](scripts/defense.cpp)

| Rank | P2 from the tied start and P1 after opening 1 |
|---:|---|
| 3 | Both hold for every eligible $3\le N\le16$. At 19 only P1 holds. At 20 both fail. |
| 4 | Both hold for every eligible $3\le N\le28$. Both fail at 31, 32, and 35. |
| 5 | Both hold at 31, 32, and 35. |

An independent bottom-up rank-four run on all $2^{30}$ even-sum boards in $[1,31]$ gives 989,377,738 tied members and confirms that both designated roles fail on the prefix. At $N=31$ the exact list of opponent openings that defeat P2's rank-four policy is $1,2,3,10,11,12$. The other 25 openings allow P2 to hold with the same cap. At 28 the numbers of tied boards accepted by the ungated rank-three and rank-four rules are 56,530,680 and 124,720,381, respectively, out of 134,217,728. The count includes opener losses where the policy succeeds. In the separate experiment restricted to ordinary drawn tied boards and allowing unrestricted strictly winning exits, ranks 1 through 6 accept 282,840, 29,365,887, 84,470,865, 126,378,608, 130,126,516, and 131,481,099 tied boards. The domain has 132,019,634 members including the empty board. [Full-board counts](scripts/closure.cpp) · [Opening-by-opening reproduction](scripts/defense.cpp)

For $0<d\le a\le N$, put $R=[a,N]$. The theorem for a drawing $G(R,d)$ has three sufficient hypotheses.

1. $G([a+1,N],a-d)$ draws. Picking $a$ then gives a drawing continuation.
2. For $a<x<a+d$, the mover on $R\setminus\{x\}$ at deficit $x-d$ can hold.
3. For $a+d\le x\le N$, the opener of the tied board $R\setminus\{x,x-d\}$ cannot win. The singleton $x-d$ is a legal exact reply.

The second and third hypotheses prevent any strictly winning choice on $R$. Applying this at $(a,d)=(3,1)$ eliminates the entire short band in item 2. The composed Lean theorem `draw_of_two_offsets` proves sufficiency of a draw on $([4,N],2)$ and nonwinning tied boards $[a,N]\setminus\{x-1,x\}$ for $a=2,3$ and $a+1\le x\le N$. [Interval descent and its boundary specialization](CatchUpGame/ResearchLemmas.lean)

On every eligible $11\le N\le28$ the $[3,N]$ adjacent-hole remainders all draw, and $G([4,N],2)$ draws. Applying one more descent at $(4,2)$ leaves just $x=5$ in the short band. All its hypotheses hold at 11 and at every eligible $15\le N\le28$. The new threshold queries also validate both layers at 31 and 32. At 12 exactly one tied distance-two removal wins. At 7 and 8 respectively, three and two adjacent-hole remainders for $a=3$ win. Thus an induction starting from 11 can handle the $[3,N]$ step, while the next layer already needs the exception at 12. [Exact interval query](scripts/retrograde.cpp)

**New opening values.** Every opening draws at 39, 40, 43, and 44. Together with the earlier rows this covers every opening of every eligible prefix from 12 through 44. Round 1 had certified openings 1 and 2 at these sizes. The new fixed-player search verifies that P1 can hold after each of the other 37, 38, 41, and 42 openings, respectively. The scalar threshold solver independently replayed all the new openings at 39 and 40. A drawing root rules out a strict win from any opening, giving its exact value from this one bound. [Fixed-player opening search](scripts/defense.cpp)

**The new full prefix at 48, independently verified.** Its total is 1,176. With scalar minimax at interior ties, increasing pick order, a 29-token packed suffix and a $2^{26}$-entry transposition table, the exact threshold search returned both `48 1 holds` and `48 2 holds`. This run took approximately 7 minutes 24 seconds from creation of its output file to its final row. The independent fixed-player solver, which tracks both absolute scores and uses a separate packed suffix recurrence, reproduced both holds in approximately 2 minutes 34 seconds. A separate attempt using an opening-reversal shortcut at interior ties and preferring singleton exact catches had spent more than 50 minutes on its first conditional check. These are different full configurations. Root opening reversal applies in both. If one of two distinct nonlosing openings won strictly, reversing the two first picks would make the other opening lose. Thus the full root draws. The same reversal shows that $G([3,48],1)$ draws. The reported root is a computer-assisted minimax result using the kernel-verified reversal theorem. [Threshold solver](scripts/threshold.cpp) · [Opening reversal](CatchUpGame/ResearchLemmas.lean)

**The full prefix at 51 remains unresolved.** The 29-token scalar search spent over 30 minutes on opening 1. The independent fixed-player search with a 30-token suffix ran for over 22 minutes before the round cutoff. Neither search completed its first opening. The exact $N=51$ values below concern the indicated continuation.

**Large-prefix search.** On the consecutive minimum-pick path the deficit at $[a,N]$ is $\lfloor a/2\rfloor$, since a pick of $a$ changes it to $a-\lfloor a/2\rfloor$. The table gives exact unrestricted values from the mover's perspective. The last two columns count failed hypotheses 2 and 3 above. A winning tied-removal entry records a failed *particular repair*, even if another legal repair succeeds. [Minimum-ray and opening searches](scripts/threshold.cpp)

| $N$ | $a$ | $d$ | $G([a,N],d)$ | After taking $a$, next mover | Losing short-band children | Winning tied removals |
|---:|---:|---:|:---:|:---:|---:|---:|
| 48 | 20 | 10 | D | D | 0 | 0 |
| 48 | 21 | 10 | D | D | 0 | 0 |
| 48 | 22 | 11 | D | D | 0 | 3 |
| 48 | 23 | 11 | D | W | 0 | 0 |
| 48 | 24 | 12 | W | D | 11 | 13 |
| 48 | 25 | 12 | D | W | 0 | 0 |
| 51 | 26 | 13 | D | W | 0 | 0 |

In particular, at $N=48$ an argument that always peels the minimum and demands a draw at every boundary fails at $a=24$. The complete winning list there is $25,\ldots,36$. Picking 24 draws, and picking any larger token from 37 through 48 loses. At $a=23$ the drawing choices are exactly $36,38,40,42,44,46,47,48$. At the two center positions $([25,48],12)$ and $([26,51],13)$ only the maximum draws. Independent fixed-player searches confirm the outcome column for $21\le a\le25$ at 48 and $a=26$ at 51. The paired-interval theorem supplies the leading player's half of the two center draws at $N=48,51$ directly.

### Round 3 target

**Prove the two-offset adjacent-hole reduction by a strategy that can change its reply at an exceptional boundary.** The precise target, for eligible $N\ge15$, consists of the one role-symmetric draw $G([4,N],2)=\mathrm{draw}$ together with the one-sided bound on $[a,N]\setminus\{x-1,x\}$ for $a\in\{2,3\}$. These are sufficient for the original conjecture. The smaller eligible cases already follow from the kernel proof through 12. Track the missing pair explicitly. A prospective induction can discharge a branch when the residual admits the bank-and-pairs inequalities and can use the density repair only where its slack inequality holds. On the $4k$ branch the critical high interval has just one candidate move, so the odd interval with one possible deletion gives a concrete base family for the induction. The necessary additional step is a response covering the short-band or near-minimum exceptions while preserving a strictly smaller member of the induction family. The win at $([24,48],12)$ is a concrete regression test for any claimed uniform descent.

The October research handoff also singles out the lower ray and an exceptional boundary. Its recovery of a maximum companion assumes a nonempty, catchable smaller residual, and its two-buffer protocol still requires a uniform translation. It records a pair of adjacent-hole positions requiring different first repairs. This supports tracking the actual hole locations when using the new reduction. A separate October report describes kernel-checked examples through 16 and four open statements on unions of adjacent pairs tested within $[1,20]$. Neither source supplies the needed uniform response. [Research handoff](https://github.com/bocowgill-collaborations/catch-up-research/blob/main/docs/research-handoff.md) · [Daniel Puri, pp. 4–5](https://aixiv.online/pdf/2610.03026v1)

### Reproduction and verification

Build the tools from the project root. The maximum-31 profile and ungated rank scans each require an 8 GiB table. The 29-token opening searches use a 4 GiB suffix table plus a transposition cache. The fixed-point table can enumerate the state-by-state classes with the `--dump` option. The default fixed point restricts tied reentries to ordinarily drawn boards. The `--assume` option instead treats a tied reentry in the selected class as an induction hypothesis. The separate `--all-ties` mode removes the tied reentry restriction.

```sh
clang++ -O3 -march=native -std=c++17 scripts/closure.cpp -o /tmp/cu-closure
clang++ -O3 -march=native -std=c++17 scripts/retrograde.cpp -o /tmp/cu-retro
clang++ -O3 -march=native -std=c++17 scripts/threshold.cpp -o /tmp/cu-threshold
clang++ -O3 -march=native -std=c++17 scripts/defense.cpp -o /tmp/cu-defense

for n in 20 24 28; do
  /tmp/cu-closure "$n" 0 --pure
  for k in 1 2; do
    /tmp/cu-closure "$n" "$k"
    /tmp/cu-closure "$n" "$k" --isolated
    /tmp/cu-closure "$n" "$k" --winning-exit
    /tmp/cu-closure "$n" "$k" --isolated --winning-exit
  done
done
for class in density brown both; do
  /tmp/cu-closure 28 2 --isolated --assume "--$class"
  /tmp/cu-closure 28 2 --isolated --assume "--$class" --winning-exit
done
for r in 1 2 3 4 5 6; do
  /tmp/cu-closure 28 0 --rank "$r" --winning-exit
done
for k in $(seq 0 24); do /tmp/cu-closure 24 "$k" --all-ties; done
for k in 22 23 24; do /tmp/cu-closure 28 "$k" --all-ties; done
/tmp/cu-closure 28 0 --rank 3 --all-ties
/tmp/cu-closure 31 0 --rank 4 --all-ties
/tmp/cu-closure 31 0 --profiles
/tmp/cu-retro 28 --bank
/tmp/cu-retro 28 --intervals
python3 -B scripts/round2.py audit /tmp/cu-closure 12
python3 -B scripts/round2.py threshold /tmp/cu-threshold 12
python3 -B scripts/round2.py banks /tmp/cu-threshold 7 12 --trials 300
python3 -B scripts/research.py set 1 2 3 7 9 11 14 15 22
python3 -B scripts/research.py position 3 6 7 10 11 13 14
for n in 31 32; do
  for r in 4 5; do
    /tmp/cu-defense "$n" 23 "$n" --packed --rank "$r" --tied 1
  done
done
for r in 4 5; do /tmp/cu-defense 35 26 35 --packed --rank "$r" --tied 1; done
/tmp/cu-defense 31 23 31 --packed --rank 4 --defend $(seq 1 31)
/tmp/cu-defense 39 26 39 --packed $(seq 3 39)
/tmp/cu-defense 40 25 40 --packed $(seq 3 40)
/tmp/cu-defense 43 27 43 --packed $(seq 3 43)
/tmp/cu-defense 44 27 44 --packed $(seq 3 27)
/tmp/cu-defense 44 29 44 --packed $(seq 28 44)
/tmp/cu-threshold --plain-ties --small-first --endgame 24 --cache-bits 24 --opening-range 3 39 39
/tmp/cu-threshold --plain-ties --small-first --endgame 25 --cache-bits 24 --opening-range 3 40 40
for k in $(seq 1 14); do
  /tmp/cu-threshold --set --plain-ties --small-first --cache-bits 18 --endgame $((2*k-1)) --pick-values --gap $((3*k)) $(seq $((2*k+1)) $((4*k-1)))
done
/tmp/cu-threshold --small-first --prefer-exact --pair-cuts --endgame 22 --ray 3 4 31 32
/tmp/cu-threshold --small-first --plain-ties --endgame 26 --ray-moves 23 25 48
/tmp/cu-threshold --small-first --plain-ties --endgame 26 --ray-moves 26 26 51
/tmp/cu-defense 48 28 48 --packed --ray-positions 21 25
/tmp/cu-defense 51 26 51 --packed --ray-positions 26 26
/tmp/cu-threshold --small-first --prefer-exact --endgame 27 --ray 20 25 48
/tmp/cu-threshold --small-first --prefer-exact --pair-cuts --endgame 26 --ray 26 26 51

# The two nonlosing openings certify the unrestricted root.
/tmp/cu-threshold --plain-ties --small-first --endgame 29 --cache-bits 26 --two 48
/tmp/cu-defense 48 29 48 --packed 1 2

# Round 2 search for the next eligible root.
/tmp/cu-threshold --plain-ties --small-first --endgame 29 --cache-bits 26 --two 51
/tmp/cu-defense 51 30 51 --packed 1 2

lake build
python3 -B scripts/audit.py
```

The independent Python check compares both role bits at 26,624 parity-compatible states through maximum 12 for each of nine configurations. It enumerates completed turns with the largest selected token last. The C++ closure works one pick at a time. A second test verifies conditional openings, each minimum-ray column, all 4,096 ordinary tied outcomes through maximum 12 with the new bank-and-pairs cutoff enabled, and every single-pick value on the full 12-token board at deficits 0 through 12. Larger fixed points and interval evaluations are exact computer searches. A further comparison with full-turn minimax tests the maximum-only search rule on 18 high intervals, including examples on each side of its hypothesis. The universal cap classification, the positive reservoir class, the maximum-only theorem, and the conditional interval reductions are checked by the Lean kernel. [Independent checks](scripts/round2.py) · [Axiom audit](scripts/audit.py)

The final Lean 4.36.0 build succeeded. The audit inspected all 71 public research declarations, including the 25 added in this round. Their axiom dependencies are contained in `propext`, `Classical.choice`, and `Quot.sound`. The project source passed the placeholder and native-proof scan. The frozen target had SHA-256 `0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3` both before and after the round. The original 33,107 report bytes retain SHA-256 `53ccf38600a204ebf498ea94d21b4519093e6709196f3d5292b2db4a63cb9d86`.
