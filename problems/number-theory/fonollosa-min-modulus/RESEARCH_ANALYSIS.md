# Fonollosa’s minimum modulus conjecture — Round 1

**Case C. The general conjecture remains unresolved.** Write $f(n)=2^n-2^{\lfloor\log_2 n\rfloor}$.

- **One free residue, all $n\ge6$.** If $2^{n-1}\le N<2^n$ and a valid $n$-set contains $1,2,4,\ldots,2^{n-2}$, its remaining residue must be $2^{n-1}\pmod N$. For any positive $N$, Lean proves $f(n)\le N$ as soon as a valid $n$-set contains a translate of these powers multiplied by a unit.
- **Two free residues, $8\le n\le25$.** Exact computation and the reductions below rule out every subthreshold set containing **$n-2$ distinct residues** of the form $t+u2^i$, $0\le i<n-2$. Here $u$ may be a nonunit. The unit case alone leaves 1,157,841 pairs after pruning, across all 18 sizes. Each fails the exact multiset test.
- **Antipodal pairs, $n=10$.** A valid ten-set below 1016 cannot contain a pair at distance $N/2$. This computer-assisted conclusion uses Sitjar’s nine-set minimum, a four-modulus quotient census, and exact linear equations over $\mathbb F_2$ for the lifts.

The first unresolved size is ten. A counterexample there would have to avoid the two configurations above. The remaining ten-sets still require a proof or an exhaustive test.

## What the papers establish

Fonollosa’s Theorems A and B determine the least modulus for the single binary family. Translating its entries by one gives powers of two. With largest coin $H$, the fewest coins representing $v\ge0$ is $\lfloor v/H\rfloor+\operatorname{popcount}(v\bmod H)$. Splitting a coin gives every count from this minimum through $v$. Writing the gap as $g=2^n-N$, a gap with multiple set bits gives a positive-wrap collision in the upper half of the range. For a power-of-two gap exceeding $n$, the negative-wrap target $g-1$ admits $n$ coins. At the endpoint, $g-1<n$, and the digit-sum step excludes positive wraps. The paper reports exhaustive CP-SAT checks for all sets through $n=7$ and search evidence through $n=13$. [Fonollosa, arXiv:2607.08366v2, §§3–7](https://arxiv.org/html/2607.08366v2)

Inal proved the arbitrary finite abelian group bound $2^{n-1}\le |G|$. Equality forces an elementary abelian 2-group, with the translated differences forming a basis. The standard basis with a zero attains equality. This settles Fonollosa’s abelian-group question and explains why an improvement for cyclic groups needs additional information. [Inal’s preprint](https://doi.org/10.17605/OSF.IO/C58Q9) · [Fonollosa’s formalization of Inal’s theorem](https://github.com/jarfo/min-modulus/blob/master/MinModulus/AbelianMin.lean)

Théo Nicolas Sitjar’s November 2026 preprint, *A lower bound and the cases $n=8,9$ of Fonollosa’s minimum-modulus conjecture*, gives the strongest unconditional cyclic lower bound identified in this review. For $n\ge5$,

$$
 N\ge 2^{n-1}+\max\!\left(2n-2,\left\lceil\frac{2^{n-1}-1}{n-1}\right\rceil\right).
$$

One term comes from adjoining doubles and their complements to the subset sums, with an antipodal quotient argument. The other counts translated doubles outside the subset-sum image. Theorem B reports exhaustive minima **248** and **504** for $n=8,9$. Two implementations searched $128\ldots247$ and $256\ldots503$, using the same affine normal form and insertion criterion. The solver cross-check was incomplete. The paper also records the power-of-two modulus case and one affine orbit at $n=9,N=504$. Its tabulated general bounds at $n=8,9,10$ are 147, 288, 569. [Sitjar, 14 November 2026, Theorems A–C, §§4–6](https://www.alphaxiv.org/abs/2611.fonollosa-minimum-modulus-conjecture.pdf)

## Signed relations and two pivots

Put $c_a=m(a)-1$. Validity says every integral $c$ satisfying

$$
 c_a\ge-1,\qquad \sum c_a=0,\qquad \sum c_a a=0\quad\text{in }\mathbb Z/N
$$

vanishes on $A$. For a nonzero relation, the set $S$ of negative entries is nonempty, every entry on $S$ is $-1$, and the positive part is a multiset on $A\setminus S$ with size and sum equal to those of $S$. Conversely any such replacement gives a relation. The balance equation gives invariance under translation and unit dilation. Extending a relation by zero proves heredity.

For each $a\in A$, the map $F_a(T)=\sum_{x\in T}(x-a)$ is injective on subsets of $A\setminus\{a\}$. If two images agree, cancel their intersection and pad the smaller side with copies of the pivot. Counting gives $N\ge2^{n-1}$. When the pivot is zero, the full $2^n$ subsets fall into exactly the pairs $T,T\cup\{0\}$ with $0\notin T$. Changing the pivot by $h$ changes a difference of two sums by $-(|S|-|T|)h$. Thus counting independently at multiple pivots does not produce disjoint images.

Fix $a\ne b$ in $A$ and put $d=b-a$. For distinct $S,T\subseteq A\setminus\{a,b\}$ and $w=|S|-|T|$,

$$
 F_a(S)-F_a(T)\ne j d
 \qquad\bigl(\min(0,w)-1\le j\le\max(0,w)+1\bigr).             \tag{1}
$$

Indeed, an equality gives a balanced relation with entries $1_S-1_T$ off the pivots, $j-w$ at $a$, and $-j$ at $b$. In the indicated interval either all entries are at least $-1$, or their negatives are. The distinct subsets make the relation nonzero. In particular, if $d$ has order three, the three translates of the $2^{n-2}$ subset sums by $0,d,-d$ are disjoint, so **$N\ge3\cdot2^{n-2}$**. Lean proves (1) and the order-three bound. More generally, if $d$ has order $L$, adjacent positions in a coset cannot both be occupied, so each of the $N/L$ cosets holds at most $\lfloor L/2\rfloor$ subset sums. This gives $N\ge L\lceil 2^{n-2}/\lfloor L/2\rfloor\rceil$.

## Why a contiguous binary core forces the last residue

Let $H=2^{n-2}$ and $B=\{2^i:0\le i\le n-2\}$. Let $p$ represent the sum of $B\cup\{x\}$, with $0\le p<N$. The sum of the core is $2H-1$. If either $p$ or $p+N$ can be paid using exactly $n$ coins from $B$, those coins omit $x$ and contradict validity.

Every $v\in[n,4H-2]$ can be paid. In the greedy formula the quotient is at most three. At quotient three the remainder has at most $n-3$ set bits because it is less than $H-1$. At smaller quotients the bound $n-2$ bits suffices. Split coins to reach exactly $n$. Also every $4H+j$, $0\le j\le n-2$, can be paid for $n\ge6$. Use four top coins and at most $\lceil j/2\rceil\le n-4$ ones and twos, then split.

If $2H\le N<4H$, the first interval forces $p<n$. Now $p+N\in[n,4H+n-2]$. The two intervals leave only $p+N=4H-1$, which forces $x\equiv2H\pmod N$. This identity also gives $N\ge 2^n-n$ for every valid extension, with larger $N$ automatic and smaller $N<2^{n-1}$ excluded by Inal. Lean checks the identity, the lower bound and the last residue in `binary_core_wrap`, `binary_core_lower_bound` and `binary_extension_rigidity`. Affine invariance extends these results to every unit-affine image of the core. [Lean proofs](FonollosaMinModulus/ResearchLemmas.lean)

The sharp lower bound follows directly from the same wrap. Suppose $N<f(n)$ and put $g=4H-N$, $s=\lfloor\log_2 n\rfloor$, $K=2H$. The wrap gives $g=p+1\le n$, so $2^s<g<2^{s+1}$. The binary expansion of $g$ therefore has at least two ones. The value $v=K-1-g$ has at most $n-3$ ones in the complementary $n-1$ bits. Also $v\ge n-3$ for $n\ge6$. Represent $v$ with exactly $n-3$ core coins by splitting, and add three copies of $x=K$. The resulting integer sum is $4K-1-g=(2K-1)+N$, one wrap above the all-ones sum. This contradicts validity. The kernel checks this argument in `minModulus_le_of_binary_core`. The theorem `minModulus_le_of_affine_binary_core` applies it directly to a valid set containing $t+u2^i$ for $0\le i\le n-2$ and any unit $u$.

## Fixed integer sets and their exact least moduli

Here $N^*(A)$ requires the reduction of the fixed integer set to retain all $n$ elements. Write $N^*(A)=\infty$ if no modulus works. A three-term arithmetic progression $u,v,w$ already implies infinity. Replacing $u,w$ by $v,v$ preserves the integer sum. Every reduction either preserves that witness or loses cardinality.

**Conway–Guy, Lunnon, Bohman and Fibonacci.** In Bohman’s suffix-sum description, two consecutive equal gaps produce a three-term progression whenever there is a third suffix. The Conway–Guy gaps start $1,1$, so this applies for every $n\ge3$. At $n=8$ the explicit collision is $84+82=2\cdot83$. Both $d_{k,1}$ and $d_{k,2}$ have consecutive unit gaps at positions $k,k+1$, so their sets fail whenever $n\ge k+2$, in particular throughout the $n>2k$ range of Bohman’s Theorem 3. This covers the four Lunnon families $k=2,3$ at every requested size. Every four consecutive Fibonacci terms satisfy $F_i+F_{i+3}=2F_{i+2}$, including after translation. Every example of size $8\le n\le25$ in these ranges has $N^*=\infty$. Adjoining zero to a size-$(n-1)$ example retains the same witness here. The often-quoted ratios near 0.23513 and 0.22002 refer respectively to Conway–Guy and Bohman’s wider family in the distinct-subset-sum problem. [Bohman, §§2 and 4](https://www.ams.org/proc/1996-124-12/S0002-9939-96-03653-2/S0002-9939-96-03653-2.pdf) · [Bohman’s explicit gap sequences, §2](https://www.combinatorics.org/Volume_5/PDF/v5i1r3.pdf) · [Lunnon, §7](https://doi.org/10.1090/S0025-5718-1988-0917837-5)

**Greedy.** Start at zero and append the least larger integer preserving integer validity. This convention gives $2^i-1$. After translating by one, suppose the previous coins are $1,2,\ldots,H$. Any proposed $H<y<2H$ makes $2H-1+y$ payable with the new number of terms from the old coins, by the first interval above. The choice $y=2H$ works because the all-ones binary expansion of $4H-1$ is the unique minimum-coin representation. Thus the greedy $N^*$ equals $f(n)$ in every row below. The C++ program also tests the skipped candidates and computes those least moduli independently.

**Annealed candidates.** Each row specifies a fixed integer set $\{2^i:0\le i<n-2\}\cup\{u,v\}$. A walk varied the two additional residues and scored the number of outlier-multiplicity pairs admitting a competitor. The representative $v$ was taken negative. After translating the least element to zero, the term $4-v$ is smaller than $(1-v)+(2-v)$ in every row, so the displayed sets are non-super-increasing. The fixed representatives matter to the minimum across moduli. The $N^*$ column exhausts all moduli from Inal’s lower bound up to the first success. The last column belongs to the separate exhaustive unit-core census.

| $n$ | Greedy $N^*=f(n)$ | $u$ | $v$ | Annealed $N^*$ | Pairs surviving the one-point tests |
|---:|---:|---:|---:|---:|---:|
| 8 | 248 | 124 | -185 | 371 | 6,996 |
| 9 | 504 | 315 | -501 | 972 | 12,279 |
| 10 | 1,016 | 256 | -507 | 1,523 | 17,898 |
| 11 | 2,040 | 1,785 | -1,017 | 5,343 | 23,533 |
| 12 | 4,088 | 1,024 | -3,063 | 6,127 | 29,439 |
| 13 | 8,184 | 4,094 | -8,183 | 18,413 | 35,867 |
| 14 | 16,376 | 4,096 | -8,183 | 24,551 | 41,848 |
| 15 | 32,760 | 8,192 | -16,379 | 49,138 | 48,244 |
| 16 | 65,520 | 16,384 | -65,518 | 98,286 | 52,844 |
| 17 | 131,056 | 32,768 | -65,526 | 196,580 | 60,813 |
| 18 | 262,128 | 131,064 | -196,595 | 393,191 | 69,264 |
| 19 | 524,272 | 131,072 | -262,127 | 786,391 | 78,287 |
| 20 | 1,048,560 | 262,144 | -655,343 | 1,834,967 | 87,669 |
| 21 | 2,097,136 | 524,288 | -1,048,567 | 3,145,702 | 97,634 |
| 22 | 4,194,288 | 2,097,148 | -4,194,287 | 9,437,149 | 107,484 |
| 23 | 8,388,592 | 2,097,152 | -4,194,292 | 12,582,880 | 117,874 |
| 24 | 16,777,200 | 4,194,304 | -8,388,599 | 25,165,799 | 128,824 |
| 25 | 33,554,416 | 8,388,608 | -16,777,204 | 50,331,616 | 141,044 |

## Exhausting the two free residues

Write $d=n-3$, $H=2^d$, $S=2H-1$. The fixed core is the $d+1$ powers through $H$. For added integers $x,y$ occurring $i,j$ times, the core must pay

$$
 v\equiv S+(1-i)x+(1-j)y\pmod N
 \quad\text{with }k=n-i-j\text{ coins}.
$$

The program tests each lift $0\le v\le kH$ by the coin formula, requiring also $v\ge k$. Only $i=j=1,v=S$ is the baseline, and its representation is unique. This tests every multiset, including repeated entries.

For the unit core, an individual addition $x$ must first be valid at size $n-1$. Let $w=(S+x)\bmod N$. When $x$ is omitted, both $w$ and $w+N$ must fail with $n-1$ coins. Write $w=qH+(H-1-e)$. Above the length floor a value fails precisely if $q+d-\operatorname{popcount}(e)>k$. Enumerating these bit masks gives all possible failures in an interval. There are two cases.

- If $w<n-1$, enumerate failure values $w+N$ to recover every possible $N$.
- Otherwise $w\ge4H-1>2S$, by the coverage lemma. Two copies of $x$ require the residue $N+2S-w$ with $n-3$ coins. Enumerating its failure values again determines $N$.

The one-point test checks the remaining multiplicities. For each $N$, every unordered pair of surviving additions is then tested at size $n$. These two inversions of the congruence make the sweep through $n=25$ practical. The modulus-by-modulus implementation agrees in every row through $n=18$, including a direct loop over every single residue through $n=12$.

**Nonunit steps.** Translation and multiplication by a unit reduce a step $u$ to $g=\gcd(u,N)$. Write $N=gM$. The core itself is valid modulo $M$ after division by $g$, so $M\ge f(n-2)$. For $n\ge8$, $5 f(n-2)>2^n$, leaving $g=2,3,4$ below the target. The following reductions account for the two extra residues.

- **$g=2$.** Two even extras put the entire set in a subgroup of size $N/2<2^{n-1}$. With two odd extras, the all-ones target is even. After division by two, every residue mod $M<4H$ is payable by $n=d+3$ core coins. For its representative $w\ge n$, the greedy count is at most $3+d$. For $w<n$, use $w+M$, which lies between $n$ and $4H+n-2$. Values from $4H$ upward use four top coins and ones and twos. With just one odd extra, the even subset divided by two is a valid $(n-1)$-set. Its modulus satisfies $2^{n-2}\le M<2^{n-1}$, so rigidity forces the even extra to complete the binary powers. For the remaining odd $x$, an alternative must use it $1+2t$ times. The even coins divided by two must then pay their ordinary sum minus $tx$ with $n-1-2t$ coins. The program checked all 33,521,208 odd-residue choices over the eligible subthreshold moduli and sizes. None passed.
- **$g=3,4$.** For any $k\in\{n-2,n-1,n\}$, every residue mod $M$ is payable using $k$ core coins. Indeed every integer in $[k,3H-2]$ has greedy count at most $d+1\le k$. For a representative below $k$, add $M$. We have $M\ge f(n-2)\ge n$ and $M+n-1\le3H-2$, since $M<8H/3$ and $H\ge3n+2$ for $n\ge8$. Thus, modulo $g$, the two extras together must have a sum that no other choice of at most two extras can realize. A zero class can be omitted, identical classes permit two copies of one extra, and opposite classes permit omitting both. This exhausts $g=3$. For $g=4$ the only remaining case is an odd $x$ and $2y$ with $y$ odd.
- **The remaining $g=4$ case.** Test the even subset divided by two as above. Three copies of $x$ and zero of $2y$ would require $w=(S+(y-x)/2)\bmod M$ in $d$ coins. Every value in $[d,2H-2]$ is payable in $d$ coins by the same greedy count, and $M<2H$. Hence $0\le w<d$, which lists all possible $x\equiv y+2(S-w)\pmod{2M}$. For each of the two lifts mod $4M$, the program tested every permitted count of both extras. All 900 remaining choices failed.

**Search controls.** The two-coordinate walks scored 104,713 distinct ordered proposals counted separately by size and modulus. A separate search allowed every coordinate to move at $n=8,\ldots,12$, testing replacements at $f(n)-1,f(n)-2,3\cdot2^{n-2}+1$. Its 4,826,080 evaluations include repeats. Its best rival counts at $n=10$ were 1, 1 and 13 respectively. A direct modular knapsack DP cross-checked the binary oracle on 1,260 inputs. A separate integer-sum DP independently reproduced each of the first five annealed minima, starting its modulus scan at one. The family-wide exclusions use the exhaustive searches. [C++ source](scripts/round1_search.cpp)

## Antipodal quotients and the ten-element case

Write $N=2M$. Two distinct antipodal pairs would give an equality between sums of two different pairs by exchanging their endpoints. Thus a valid set has at most one antipodal pair. Collapse that pair to $b_j\in\mathbb Z/M$. If the projected set $B$ had a competing multiset, add one occurrence of $b_j$ and lift. At least one occurrence of $b_j$ is now available, so choosing its endpoint corrects either possible parity of the sum upstairs. The lifted multiset still differs from the baseline. Hence $B$ is valid and has $n-1$ elements. [Sitjar, Lemma 2.3](https://www.alphaxiv.org/abs/2611.fonollosa-minimum-modulus-conjecture.pdf)

There is also an exact test in the reverse direction. Fix valid $B=\{b_0,\dots,b_{r-1}\}$ modulo $M$, choose integer representatives, and replace $b_j$ by both $b_j$ and $b_j+M$. Each remaining lift is $b_i+M e_i$ with $e_i\in\mathbb F_2$. A competitor using either endpoint would project, after removing one occurrence of $b_j$, to the baseline on $B$. That leaves one of each other residue and exactly two endpoints. Their sum has the required parity only when both endpoints occur once.

It suffices therefore to examine the vectors $m$ with $m_j=0$, $\sum m_i=r+1$, and

$$
 \Delta(m)=\sum_i m_i b_i-\left(\sum_i b_i+b_j\right)\equiv0\pmod M .
$$

The sum difference upstairs, divided by $M$, is $\Delta(m)/M+\sum_{i\ne j}(m_i-1)e_i-1$. It must be odd for **every** such $m$. Consequently a valid lift exists **if and only if** the following simultaneous linear equations are consistent.

$$
 \sum_{i\ne j}(m_i-1)e_i = \Delta(m)/M \quad\text{in }\mathbb F_2.       \tag{2}
$$

A selection of rows whose left sides XOR to zero and whose right sides XOR to one certifies impossibility. The Python program re-evaluates the original integer multiplicity vectors in each certificate. Over all $8\le n\le25$ with $2f(n-1)<f(n)$, all 257 marked pivots of the canonical binary quotient at $M=f(n-1)$ gave contradictions. The longest retained certificate has 14 rows. At $n=8,16$ doubling reaches the threshold exactly.

For example, take $n=10$, $M=504$, $B=(1,2,4,\ldots,256)$ and split the entry 1. The vectors $(0,2,3,0,1,1,1,1,1)$ and $(0,2,1,0,1,1,1,1,3)$ give sums 512 and 1016. They agree entrywise mod 2 and their sums differ by exactly 504. The two equations (2) therefore contradict each other.

For an arbitrary antipodal ten-set below 1016, Sitjar’s minimum leaves only $M=504,505,506,507$. The nine-set census used affine normalization by the least pairwise $\gcd$ with $M$, as in Sitjar’s Lemma 5.1. If $g$ is this least gcd, a unit and a translation send its endpoints to $0,g$. Every other representative is greater than $g$, since its gcd with $M$ is at least $g$. When $g=1$, the search keeps the lexicographically least normalized form. A partial subset that transforms to a smaller sorted prefix also gives a smaller prefix for every completion.

For a valid partial set $D$ of size $k$ write $R_l(D)$ for the residues attainable using exactly $l$ entries, with repetition. A new residue $x$ is admissible precisely when

$$
 \sum_{a\in D}a+(1-h)x\ \notin R_{k+1-h}(D)
 \quad\text{for every } h\in\{0,2,3,\ldots,k+1\}.
$$

This follows by fixing the multiplicity $h$ of $x$. The case $h=1$ reduces to validity of $D$. Packed cyclic bitsets compute the exact recurrence $R_l(D\cup\{x\})=R_l(D)\cup(x+R_{l-1}(D\cup\{x\}))$. The program checks every possible rotation against scalar indexing and verifies every surviving leaf with a separate multiset-counting DP. [Sitjar, Lemmas 5.1–5.2](https://www.alphaxiv.org/abs/2611.fonollosa-minimum-modulus-conjecture.pdf)

| $M$ | Valid normalized nine-sets | Valid prefix nodes at depth eight |
|---:|---:|---:|
| 504 | 1 | 2,791,951 |
| 505 | 0 | 22,477 |
| 506 | 0 | 474,543 |
| 507 | 0 | 43,396 |

At 504 the sole normalized form is $\{0,1,3,7,15,31,63,127,255\}$, the binary quotient translated by $-1$. Unit-affine equivalences downstairs lift upstairs. Indeed a unit mod $M$ has an odd representative coprime to $2M$, and any translation lifts. Testing every marked pivot by (2) therefore disposes of the entire orbit. The census and parity certificates are executable finite verifications. The local Lean file proves the structural results listed in the audit below. [Quotient census](scripts/quotient_census.cpp) · [Lift certificates](scripts/antipodal_lifts.py)

## Round 2 — the non-antipodal ten-set search

Target the remaining unrestricted case $569\le N\le1015$, $n=10$, using the interval (1) as a completion test in the affine-normalized search. This works for every pair of chosen pivots, including a pair whose difference is a nonunit. An order-three difference already requires $N\ge768$.

Here is a precise capacity bound for a partial set. For pivots $a,b$, sort its current $F_a(T)$ in each coset of $\langle b-a\rangle$, in cyclic steps of $b-a$. Label each point by $h(T)=|T|$. From one occupied point to the next let $s$ be the positive gap and $\delta$ the increase in label. If the completion subdivides this arc into $k$ gaps, (1) gives

$$
 s\ \ge\ 2k+\sum_{\text{subgaps}}\max(0,\Delta h)
 \ \ge\ 2k+\max(0,\delta).
$$

For one occupied point its sole arc is the entire coset. An empty coset of order $L$ can contain at most $\lfloor L/2\rfloor$ points. Thus the sum of $\lfloor(s-\max(0,\delta))/2\rfloor$ over occupied arcs, plus the empty-coset capacities, must reach **256** for every pivot pair of a ten-set. A failure is a short, checkable certificate for discarding the entire branch. An exhaustive search still needs to resolve the branches that pass these tests. The capacity bound alone is insufficient to conclude the conjecture.

## Reproduction and proof audit

Run these commands in the challenge directory. The first executable prints the fixed-set minima, controls, parity tests and annealing counts by default. Its three switches run the exhaustive unit-core census, the modulus-by-modulus cross-check, and the free-coordinate search.

```sh
lake build
lake env lean scripts/check_axioms.lean
lake env leanchecker --verbose FonollosaMinModulus.Challenge FonollosaMinModulus.ResearchLemmas
shasum -a 256 FonollosaMinModulus/Challenge.lean
clang++ -std=c++17 -O3 -march=native scripts/round1_search.cpp -o /tmp/fonollosa-round1
/tmp/fonollosa-round1
/tmp/fonollosa-round1 --sparse
/tmp/fonollosa-round1 --pairs
/tmp/fonollosa-round1 --free
/Users/mw/miniconda3/bin/python3 scripts/antipodal_lifts.py --show 10
clang++ -std=c++17 -O3 -march=native scripts/quotient_census.cpp -o /tmp/fonollosa-quotients
/tmp/fonollosa-quotients 504
/tmp/fonollosa-quotients 505
/tmp/fonollosa-quotients 506
/tmp/fonollosa-quotients 507
```

Lean 4.36.0 builds the package with the research file imported by the root module. The 20 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The local Lean files contain zero occurrences of `sorry`, `admit`, or `native_decide`. Lake emits module-format warnings because the frozen challenge uses legacy imports and the research file imports that challenge. The SHA-256 of the frozen source at the start and end of the round was `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`.

## Round 2

**Case C.** Every valid cyclic $n$-set with $n\ge3$ satisfies

$$
                         N \ge \frac{9}{16}2^n .
$$

The proof is in Lean. The coefficient stays strictly above $1/2$ as $n\to\infty$. It improves Sitjar’s general bound for every $n\ge10$. At ten elements it gives 576, up from 569. An exchange enumeration and direct searches together rule out every ten-set through **613**, giving the unrestricted bound **$N\ge614$**. The known construction has modulus 1016. The gap between these statements remains open. [Sitjar, Theorem A](https://www.alphaxiv.org/abs/2611.fonollosa-minimum-modulus-conjecture.pdf) · [Fonollosa, Theorem A and Conjecture 1](https://arxiv.org/html/2607.08366v2)

### A fixed-factor cyclic lower bound

Fix pivots $a,b$, let $d=b-a$, $R=A\setminus\{a,b\}$, $r=n-2$, and write $F(S)=\sum_{x\in S}(x-a)$. Define $E_R(g)$ as the number of subsets $S\subseteq R$ admitting a $T\subseteq R$ with $|T|=|S|$ and $\sum T=\sum S+g$. Equal-rank subset sums on $R$ are injective, so each such $S$ has a unique mate.

For each $S\subseteq R$, place five labels $i=0,1,2,3,4$ in $\mathbb Z/N\times\{0,1\}$ using the map

$$
 (S,i)\longmapsto
 \left(F(S)+\left\lfloor\frac{i-|S|}{2}\right\rfloor d,\quad
                      (i-|S|)\bmod 2\right).
$$

For a coincidence of $(S,i)$ and $(T,j)$, put $w=|S|-|T|$. Equality of the second coordinates makes $J=(j-i+w)/2$ integral, and equality of the first gives $F(S)-F(T)=Jd$. Equation (1) forces $S=T$ if $\min(0,w)-1\le J\le\max(0,w)+1$. The only exceptions for these five labels have $w=0$ and $\{i,j\}=\{0,4\}$. Within the interval, $S=T$ leaves $J\in\{-1,0,1\}$ and $Jd=0$, so $i=j$. In the exceptional case the label-4 source has an equal-rank mate at displacement $2d$. Deleting exactly those label-4 points leaves an injection. In particular,

$$
                     5\cdot 2^r \le 2N+E_R(2d). \tag{R2.1}
$$

To bound the loss in (R2.1), fix $g\ne0$. Removing common coordinates from a source and its mate gives an ordered pair $(D,C)$ of disjoint sets of the same positive size $t$, with $\sum C-\sum D=g$. Call it an exchange. It occurs at exactly $2^{r-2t}$ sources, those containing $D$ and avoiding $C$.

Any two distinct exchanges satisfy **both** $D_i\cap C_j\ne\varnothing$ and $D_j\cap C_i\ne\varnothing$. Indeed the vector $1_{C_i}-1_{D_i}-1_{C_j}+1_{D_j}$ is balanced and has sum zero in the group. If $D_i\cap C_j$ were empty, all entries would be at least $-1$. Validity forces that vector to vanish, so the two exchanges would coincide. Interchanging the indices gives the other intersection.

The following argument uses the Bollobás set-pair inequality. [Bollobás, *On generalized graphs*](https://doi.org/10.1007/BF01904851)

Take a uniform random ordering of $R$. For an exchange of size $t$, the event that every point of $D$ precedes every point of $C$ has probability $1/\binom{2t}{t}$. The crossing property makes these events disjoint for different exchanges. Also $\binom{2t}{t}/4^t\le1/2$ for $t\ge1$, since the ratio of consecutive values is $(2t+1)/(2t+2)$. Summing their contributions gives

$$
 \frac{E_R(g)}{2^r}=\sum_{(D,C)}4^{-t}
 \le \frac12\sum_{(D,C)}\binom{2t}{t}^{-1}\le \frac12. \tag{R2.2}
$$

Lean proves (R2.2) by a finite injection. For each source it constructs four distinct images in two copies of the cube. The first two keep the subset and select either tie order. The other two toggle the least or greatest point of $D\cup C$ and select the tie order that puts all of $D$ before all of $C$, sorting members of the output subset first. The crossing property recovers the exchange from the output, and the source is then $(W\setminus C)\cup D$, where $W$ is the output subset.

For any pivot $a$, a cyclic group has at most one $b\ne a$ with $2(b-a)=0$. Thus $n\ge3$ supplies a pair with $2d\ne0$. Substituting (R2.2) in (R2.1) gives $9\cdot2^{n-2}\le4N$. The public Lean declarations are `RankPacking.equal_exchanges_cross`, `RankPacking.equal_rank_half`, `RankPacking.five_slots`, `RankPacking.nine_sixteenths_of_pivots`, and `RankPacking.cyclic_nine_sixteenths`, all in the `FonollosaMinModulus` namespace. [Lean source](FonollosaMinModulus/ResearchLemmas.lean)

### What the one-pivot and pairwise relaxations miss

- If $0,x\in A$ are distinct, $S,T\subseteq A\setminus\{0,x\}$ and $q x+\sum T=\sum S$ for $q\ge2$, the balancing coefficient at zero is $|S|-|T|-q$. A value at least $-1$ gives a forbidden signed relation. Hence a collision requires $|S|\le|T|+q-2$. In particular a doubled translate can meet only these ranks with $|S|\le|T|$. The valid binary ten-set at 1016 already contains $2\cdot3+1=7$ and $3\cdot1=3$. Consequently the union of doubled or tripled translates need not be disjoint from the anchored subset sums. The excess number of summands on the repeated side matters.
- At the prime 521 take $A=\{0,1,2,4,\ldots,256\}$. Its anchored subset-sum image $U$ is exactly $\{0,\ldots,511\}$, $U-U$ is the whole group, and its autocorrelation has value 512 at zero and total $512^2$. These properties coexist with the forbidden midpoint $0+2=1+1$. Surjectivity of the difference set and these Fourier moment identities alone cannot give the desired floor. This example concerns those particular relaxations.
- A relaxation assigning a fractional variable to each residue and each subset rank also loses the obstruction if it only imposes rank totals, pairwise forbidden-shift inequalities, and adjacent-site total capacity. At $N=569$ the uniform assignment $x_{z,k}=\binom8k/569$ has the right totals, satisfies each two-variable exclusion, and has adjacent total $512/569<1$. Inequality (R2.2) uses compatibility among entire exchanges.

An independent Python program checked (R2.1), the exact five-label image size $5\cdot2^r-E_R(2d)$, and (R2.2) on every anchored valid set of sizes 3 through 5 with $3\le N\le28$. This covered 9,488 sets and 48,924 unordered pivot pairs. [Independent checks](scripts/round2_verify.py)

### How much the two-pivot test detects

The seven-set $\{0,1,3,63,75,91,115\}$ modulo 120 passes the anchored subset-sum injection at **every** pivot. All seven cubes have 64 different sums. Yet its total is $348$, and the multiset $(0,0,0,3,75,75,75)$ has total $228$. Both totals are $108\bmod120$, and $120<f(7)=124$. This also limits a Fourier approach based on Parseval identities for all the individual anchored cubes. The interval test catches the example at $a=0,b=75$, since $1+63+91+115\equiv2\cdot75\bmod120$.

Lean proves an exact converse to (1) in `signed_zero_of_pivot_interval` for relations with at most two coefficients exceeding 1. Choose pivots $a,b$ including those coefficients. Among the other coordinates put $S=\{x:c_x=-1\}$ and $T=\{x:c_x=1\}$. Then $w=|S|-|T|=c_a+c_b$ and $F_a(S)-F_a(T)=c_b(b-a)$. Since $c_a,c_b\ge-1$, the integer $c_b$ lies in the forbidden interval in (1). If the interval test passes, $S=T$ and disjointness gives $S=T=\varnothing$. Balance now gives $c_a=-c_b\in\{-1,0,1\}$, and distinctness of the pivots forces both coefficients to vanish.

For ten points, three coefficients at least 2 use at least six negative entries. Each negative entry is $-1$. Counting ten coordinates leaves just two possible multiplicity patterns for a nontrivial relation escaping the interval tests. With $\sigma=\sum A$, they are

| Rival multiplicities, zeros omitted | Remaining modular test | Number of labeled choices |
|---|---|---:|
| $(3,3,3,1)$ | $\sigma=3(u+v+w)+x$, with $u,v,w,x$ distinct | 840 |
| $(4,3,3)$ | $\sigma=3(u+v+w)+u$, with $u,v,w$ distinct | 360 |

Thus all two-pivot intervals plus **1,200** scalar comparisons are an exact ten-set validity test. Equivalently the extra test is $\sigma\notin 3\Sigma_3(A)+A$, where $\Sigma_3(A)$ contains the sums of three distinct points and 3 denotes scalar multiplication. Lean also verifies the underlying bound on the number of multiplicities at least three in `triple_multiplicity_card_le`. The Python checker enumerates all $\binom{19}9=92{,}378$ multiplicity vectors, tests examples that pass every interval and fail each of the two exceptional patterns, and compares this characterization to direct multiset counts on the valid endpoint and 100 deterministic samples. [Structural verifier](scripts/round2_verify.py)

### Exact finite reduction for ten points

Write $\Delta=\{b-a:a,b\in A,\ a\ne b\}$. In the subthreshold range the antipodal result above gives $|\Delta|=90$. Indeed, equal differences give equal two-term sums. If either two-term sum is squarefree, its representation is unique by validity. The remaining possibility is equality of two doubles, which requires an antipodal pair. Of the elements of any cyclic group, at most $\sum_{j=1}^{16}\varphi(j)=80$ have order at most 16. Hence some $d\in\Delta$ has order greater than 16.

For fixed pivots let $m_t$ count the exchanges of size $t$ for $g=2d$. On the eight other coordinates,
$$
 E_R(g)=64m_1+16m_2+4m_3+m_4. \tag{R2.3}
$$
There is at most one singleton exchange since the directed differences are distinct. There are at most $\gcd(2,N)$ exchanges covering the entire ground set because their target set satisfies $2\sum C=\sum R+g$ and its subset sum is injective at fixed rank. For $2g\ne0$, two size-two exchanges cannot use the same four coordinates. On that support their target pairs would either differ in one point, giving an antipodal pair, or be complements, giving $g=-g$.

The following finite counting test runs on eight named coordinates, independently of $N$. It assumes distinct directed differences and $2g\ne0$. Rows represent exchanges by $v_i=1_{C_i}-1_{D_i}$. Two rows must cross and cannot be reverses. For up to six fixed rows the program also checks every integer choice $-2\le\lambda_i\le2$ with $\sum_i\lambda_i=0$, up to overall sign. If $\sum_i\lambda_i v_i$ is nonzero and either sign has every entry at least $-1$, validity rules out those rows. All arithmetic is exact. The maximum absolute entry of a tested linear combination is at most 12.

The enumeration identifies families up to permutations of the rows and of the eight coordinates. Sorting the eight column vectors for every row permutation gives a complete orbit key. The numbers of orbits after choosing 0, 1, 2, 3, 4 size-two rows are **1, 1, 4, 10, 0**. Fixing one size-three row (two in the first table row) gives the following upper bounds. Remaining size-three rows are vertices, with an edge for pairwise compatibility in the presence of the fixed rows. Any realizable extension is a clique. A proper coloring bounds its size, and exact branching on vertices determines the clique maximum in each graph.

| $m_2$ | Seeded orbits | First clique bound on $m_3$ | After checking all choices of seed |
|---:|---:|---:|---:|
| 0 | 15 | 16 | 14 |
| 1 | 9 | 11 | 10 |
| 2 | 61 | 6 | 6 |
| 3 | 32 | 3 | 3 |

For the last column, suppose a family contains $v$ size-three rows. Every choice of which one or two of those rows to fix initially must give a seed capable of attaining $v$. Delete candidate vertices or pairs violating that necessary condition and recompute the clique bound. The audit verifies upper bounds by a second search that branches on including or excluding a vertex and builds its independent color classes separately.

If no singleton occurs, (R2.3) and the table give $E_R(g)\le62$ for even $N$ and $E_R(g)\le61$ for odd $N$. If a singleton $x\to y$ occurs, every other exchange must remove $y$ and insert $x$ by crossing. Deleting that pair from the other exchanges gives distinct exchanges for displacement $2g$ on the remaining coordinates. Thus $E_R(g)\le2^{r-2}+E_{R\setminus\{x,y\}}(2g)$.

Apply this recursion to the pivot of order greater than 16. On six coordinates with no singleton, at most three size-two rows are possible by embedding in eight coordinates, and at most two full-support rows are possible, for a bound of 14. On four coordinates with no singleton the bound is one. With a singleton the four-coordinate bound becomes $4+1=5$. The order assumption keeps each doubled shift nonzero and excludes reversals where used. Therefore on eight coordinates $E_R(2d)\le\max(62,64+\max(14,16+5))=85$. Equation (R2.1) gives $2N\ge1195$, hence **$N\ge598$**.

For each $598\le N\le609$, (R2.1) requires $E_R(2d)\ge1280-2N$ for **every** pair. This exceeds the relevant parity bound for a configuration without singletons. For every $d\in\Delta$ with $4d\ne0$, one must therefore have $2d\in\Delta$. This is a simultaneous condition on the directed differences.

Write $N=hq$ with $h$ a power of two and $q$ odd. The differences divisible by $h$ project injectively to a set $H\subseteq\mathbb Z/q\setminus\{0\}$, invariant under negation and doubling. Every nonzero projected difference lies in $H$. Successive doublings enter the subgroup divisible by $h$, and doubling is a permutation of $H$. Write $c_j$ for occupancies of the classes modulo $h$. Then $|H|=\sum c_j(c_j-1)$. Each class is valid in a cyclic group of order $q$, giving $c_j\le1+\lfloor\log_2 q\rfloor$. The set must generate after translation since every proper subgroup has size $\le N/2<512$. For every divisor $p\mid q$, a class of size $c=pa+b$, $0\le b<p$, uses at least $(p-b)a(a-1)+ba(a+1)$ differences divisible by $p$. These counts must fit in $H$.

The program enumerates all class-size partitions and all unions of $\langle-1,2\rangle$-orbits in the odd quotient. It also checks that the projected points can form a clique with differences in $H$. At most $\max(0,(h-2)/2)$ unordered pairs project to coincident points, since their distinct directed differences would lie in the kernel and could use neither zero nor an antipode. For $q>1$, at least two distinct projections are needed by generation. When $q$ has at most two distinct prime factors there is a unit difference in the projection. Otherwise every pair agrees modulo one of those primes. If two points disagree modulo the first prime, they agree modulo the second, and every third point must then also agree modulo the second. This contradicts generation. Scaling a unit difference to 1 preserves the orbit test.

There is one more capacity constraint at a pivot in a class of size $c$. The other $c-1$ points of the class give groups of $2^{c-1}$ anchored sums in each occupied residue modulo $h$. Each residue can hold at most $q$ sums. Hence $2^{10-c}\le h\lfloor q/2^{c-1}\rfloor$. Equality requires the subset sums of the $10-c$ remaining projected points to be uniform modulo $h$. For each $1\le j\le\log_2 h$, evaluate their generating polynomial $\prod_x(1+z^{x-a})$ at a primitive $2^j$-th root of unity. Its value is zero, so some $x-a$ has 2-adic valuation $j-1$. This requires at least $\log_2 h$ distinct nonpivot classes.

For $598\le N\le609$, nine moduli have no orbit union passing the initial size and normalization checks. The other three fail as follows.

- At 600 four candidate unions fail the divisor counts.
- At 608 the odd quotient has order 19. The only candidate has $|H|=18$, and the possible occupancy partitions are $(3,3,3,1)$, $(4,2,2,2)$, and $(4,3,1,1,1)$. Choosing a largest class gives equality in the capacity bound. Each partition has fewer than five other classes, and $\log_2 32=5$.
- At 609 the only candidate of size 90 consists of the three orbits of 7, 21 and 87. Every difference is divisible by 3 or by 7. The two-coordinate argument above then forces a constant residue modulo 3 or 7, contradicting generation.

At 610 or 611, the only way for a pivot with $4d\ne0$ to lack a singleton is to have **three size-two and three size-three exchanges**. All other rows of the refined table, and the three-double case with at most two triples, give less than the required $1280-2N$. There are 12 six-row profiles up to relabeling, using the same bounded signed-relation test. For each profile normalize $d$ to $\gcd(d,N)$ by unit multiplication. For the rows' active points, fix the first point at zero and form the integer matrix $M$ of the remaining coefficients. The equations are $Mx=2d\mathbf1\pmod N$. The program computes $D=UMV$ in Smith normal form, verifies this equation and $|\det U|=|\det V|=1$ over the integers, and enumerates every solution of the diagonal congruences. Distinct-difference and hereditary validity checks discard active sets that cannot occur. For a surviving eight-set $R$, test every translation in the completion $\{0,d\}\cup(t+R)$. Pivot differences of order three are already excluded in this range by the order-three bound.

| $N$ | Relative solutions across profiles and normalized pivots | Passing active sets | Valid completions | Passing sets with unassigned coordinates |
|---:|---:|---:|---:|---:|
| 610 | 29,424 | 72 | 0 | 0 |
| 611 | 7,350 | 0 | 0 | 0 |

Consequently the doubling condition on $\Delta$ holds at 610 and 611 as well. Neither odd quotient admits an orbit union of the necessary size. This proves the unrestricted, computer-assisted ten-set lower bound **$N\ge612$**. The finite enumerations use Python integer arithmetic, bounded NumPy integer arrays, and exactly checked Smith transformations. The five-label inequality and the general $9/16$ bound have separate Lean proofs. [Exchange enumeration, quotient tests, and modular lifts](scripts/round2_profiles.py)

### Direct ten-set searches

The C++17 census fixes a difference whose gcd with $N$ is the least among all pairs and maps it to that gcd $g$ by an affine unit map. Any point between 0 and $g$ would give a smaller gcd. For $g=1$, choose the representation with the least sorted third residue $z$ among all ordered unit pairs. Screening every triple against this minimum is sound because each possible third point is at least the sorted third for its ordered pair. The full nonunit mode chooses, after $0,g$, the least point outside $p\mathbb Z/N$, where $p$ is the least prime factor of $g$. A generating set contains such a point. The solver also fixes the second such point when the subgroup cannot contain nine valid points. At $N=1008$, the sole nine-set orbit of order 504 gives at least two unit differences to every odd outlier upon doubling its points, as checked over all 504 odd residues. With $g=2$ the solver minimizes the first odd coordinate over all normalized pairs at gcd two. A triple giving a smaller value rules out that representation. All remaining coordinates are searched in increasing order, including those below the fixed witnesses.

At a partial set $P$ of size $k$, the solver stores $R_j(P)$, the exact residues reachable by $j$ summands with repetition, for $0\le j\le10$. When adjoining $x$, a competitor for the enlarged set uses either zero copies of $x$, or $h=2,\ldots,k+1$ copies. One copy reduces to validity of $P$. The enlarged set is valid precisely when $\sum P+(1-h)x$ is absent from $R_{k+1-h}(P)$ for every competing $h$. Heredity permits pruning a failed partial set. A proper partial set with $R_{10}(P)=\mathbb Z/N$ cannot be extended. At depth eight a final target outside $R_{10}(P)$ fixes the sum of the last pair. The solver includes the order-three, antipodal, and cyclic coset capacity cuts from Round 1. The upper-modulus searches apply the capacity test to selected pivots. Every surviving leaf is checked by a scalar count of unordered multisets. [C++ search](scripts/round2_ten.cpp)

| $N$ | Completed coverage | Shards | Valid ten-sets found |
|---:|---|---:|---:|
| 593 | All | 584 | 0 |
| 598 | All, including nonunit differences | 3,720 | 0 |
| 599 | All | 590 | 0 |
| 601 | All | 592 | 0 |
| 612 | All, combining the unit and nonunit runs | 603 + 8,751 | 0 |
| 613 | All | 604 | 0 |
| 1013 | Unit normalization, $z\ge24$ | 982 | 0 |
| 1014 | Unit normalization, $z\ge192$ | 815 | 0 |
| 1015 | Unit normalization, $z\ge27$ | 981 | 0 |
| 1014 | All sets with no unit difference | All nonunit gcds | 0 |
| 1015 | All sets with no unit difference | All nonunit gcds | 0 |

The full searches at 593, 598, 599 and 601 provide independent checks of the exchange argument. At 612 the unit search discarded 1,280,496,089 nodes whose ten-term sums already covered the group. Together the complete 612 and 613 runs raise the continuous floor from 612 to **614**. At 1015 every surviving possibility has a unit difference and minimum third residue between 3 and 26 inclusive. A third residue of 2 would give a midpoint. The modulus as a whole remains open. At 1014, a larger run starting at third residue 80 stopped before exhausting its interval. The completed unit certificate there starts at 192.

For a separate endpoint check, the Python verifier uses arbitrary-precision residue bitsets and counts representations up to two. It exhausted the $z\ge80$ unit branches of 1013. At 1013, 1014 and 1015 it also checked every increasing completion of $(0,1,3,120,161,265)$, giving zero valid leaves. The C++ solver checked that six-point prefix and the prefixes $(0,1,4,113,164,248)$ and $(0,1,5,85,119,126)$ at all three moduli. All nine input prefixes were themselves valid, so these are tests of genuine extension branches. Both verifiers recovered $(0,1,3,7,15,31,63,127,255,511)$ at 1016 from a proper prefix. [Independent Python verifier](scripts/round2_verify.py)

Across **all 447 moduli** in $569\le N\le1015$, every valid ten-set must have a unit difference. For 281 moduli with at most two distinct prime factors this follows from generation and the two-coordinate argument. The C++ census exhausted the other 166, covering 1,256,319 nonunit shards with zero valid leaves. The cyclic coset capacity test discarded 191,987 partial sets in this run. A separate run using a sorted third coordinate exhausted all 36 odd moduli with at least three prime factors and also returned zero. Consequently the unit normalization $(0,1,\ldots)$ suffices throughout the remaining unrestricted search.

There is a second check of the no-unit branch for six squarefree moduli. For a product of three primes, write each point as a triple of residues. If every difference is a nonunit, every pair agrees in a coordinate. A generating family of at least five points lies in the union of three coordinate lines through one center. To see this, choose two points differing in exactly two coordinates and let their common coordinate be the first. Points outside their first-coordinate plane must have one of the two crossed pairs of remaining coordinates. If both crossed pairs occur, those two outside points have to share their first coordinate, and the inside points have only the two original possibilities. That would give at most four points. If just one crossed pair occurs, the three lines follow. If no pair differs in exactly two coordinates, the family varies in at most one coordinate and cannot generate.

After translating the center to zero and scaling each occupied axis to contain 1, enumerate valid axis subsets. For each axis keep the counts, saturated at two, of $k$-term multisets with the required local sum for $0\le k\le10$. Multiplying the three counts and summing over compatible lengths checks the CRT set, including an optional center. This found zero valid ten-sets without a unit difference at **935, 957, 969, 986, 1001 and 1015**. At 969 it tested 6,240 normalized combinations of internally valid blocks. At the other five moduli no such combination reached size ten. At 1015 the three axis orders are 5, 7 and 29. In particular the exhaustive line test found zero valid five-point blocks of order 29. [Independent CRT enumeration](scripts/round2_verify.py)

### Counterexample search across construction families

The C++ family search used every size $10\le n\le20$. For ordinary integer constructions it used $N=f(n)-\delta$ with $\delta=1,2,3,5,9,17$. The subgroup and CRT constructions chose nearby multiples and coprime products, respectively. Ratios in the geometric constructions were $29/15,39/20,49/25,63/32,79/40,89/45$. Powers and rounding were computed with integers. The mixed-radix and CRT choices use the fixed seed in the source. Counts are generated inputs, so repeated inputs, if present, count each time. [Construction definitions and C++ witness generator](scripts/round2_families.cpp)

| Construction | Inputs | Repeated residues | Distinct sets with an explicit rival |
|---|---:|---:|---:|
| Pure powers of three | 66 | 0 | 66 |
| Mixed radix 2 and 3 | 792 | 0 | 792 |
| Rounded geometric | 396 | 0 | 396 |
| Greedy Golomb ruler | 66 | 0 | 66 |
| Quadratic Sidon construction | 264 | 1 | 263 |
| Subgroup and cosets | 396 | 10 | 386 |
| Coprime CRT products | 1,056 | 56 | 1,000 |
| **Total** | **3,036** | **67** | **2,969** |

Every distinct-residue input had a squarefree submultiset and a different multiset of the same size, at most six, with identical sum modulo the tested modulus. The Python checker independently validated every certificate, including the modulus, index range, cardinalities and sum. This rules out those inputs at their tested moduli. [Certificate checker](scripts/round2_verify.py)

### Round 3 target

**At $N=1015$, exhaust the remaining unit-normalized third residues $3\le z\le26$ by fixing the final sum at depth six.** For a valid six-point prefix $P$, let $H(P)=(\mathbb Z/N)\setminus R_{10}(P)$. For each $\sigma\in H(P)$ keep an admissible seventh point $x$ only if $\sigma\in H(P\cup\{x\})$. Join $x,y$ when $\sigma\in H(P\cup\{x,y\})$. A valid completion requires **four pairwise adjacent points** summing to $\sigma-\sum P$. Hashing pair sums enumerates all such quadruples. The ordinary multiset DP or the exact interval criterion above can verify every candidate. The graph is a necessary condition because a representation from any proper partial set omits a point of the proposed ten-set.

The Python prototype already eliminates three six-point prefixes at 1015 by counting vertices. Their sets of possible final sums initially had 17, 10 and 9 elements, respectively. None retained four seventh points at the same sum. The prefix $(0,1,3,56,233,253)$ started with 33 possible sums. Two sums retained four vertices apiece, their graphs had five edges in total, and neither had a four-clique. The binary six-point prefix left 753 sums after the vertex check, so the existing exact extension search remains relevant on structured prefixes. [Target-conditioned prototype](scripts/round2_verify.py)

The eight-label version of the global packing gives context for this choice. Label distance $t$ permits a collision between distinct subsets only when the rank difference $w$ has the same parity as $t$ and $|w|\le t-4$. At $n=10,N=1015$ it forces at least $2048-2030=18$ excess labels per pivot pair. On the known valid set at 1016 the measured loss ranges from **384 to 1,024** across the 45 pivot pairs. This large slack is why the target-sum graph is the more discriminating endpoint test in these experiments.

### Reproduction and kernel checks

```sh
lake build
lake env lean scripts/check_axioms.lean
lake env leanchecker --verbose FonollosaMinModulus.Challenge
lake env leanchecker --verbose FonollosaMinModulus.ResearchLemmas
lake env leanchecker --fresh --verbose FonollosaMinModulus.ResearchLemmas
shasum -a 256 FonollosaMinModulus/Challenge.lean
clang++ -std=c++17 -O3 -march=native -pthread scripts/round2_ten.cpp -o /tmp/fon-round2-ten
clang++ -std=c++17 -O3 -march=native scripts/round2_families.cpp -o /tmp/fon-round2-families
py=/Users/mw/miniconda3/bin/python3
OPENBLAS_NUM_THREADS=1 "$py" -B scripts/round2_profiles.py --audit
"$py" -B scripts/round2_verify.py small
"$py" -B scripts/round2_verify.py structure
"$py" -B scripts/round2_verify.py targets
"$py" -B scripts/round2_verify.py nonunit-range /tmp/fon-round2-ten 569 1015 5
"$py" -B scripts/round2_verify.py nonunits
"$py" -B scripts/round2_verify.py shards 1013 80 1013
for n in 1013 1014 1015; do
  "$py" -B scripts/round2_verify.py prefix "$n" 0,1,3,120,161,265
done
for n in 593 598 599 601 613; do /tmp/fon-round2-ten "$n" 0 2 "$n" 4; done
/tmp/fon-round2-ten 612 1 2 612 4
/tmp/fon-round2-ten 612 -1 2 612 4
/tmp/fon-round2-ten 1013 1 24 1013 4
/tmp/fon-round2-ten 1014 1 192 1014 4
/tmp/fon-round2-ten 1015 1 27 1015 4
/tmp/fon-round2-ten 1015 -1 2 1015 4
/tmp/fon-round2-ten 1016 1 3 3 1 standard 7,15,31
/tmp/fon-round2-families --certificates > /tmp/fon-round2-certificates
"$py" -B scripts/round2_verify.py certificates /tmp/fon-round2-certificates
```

Lean 4.36.0 built the root module. An invocation replaying both modules concurrently crashed in the import loader. The individual module replays listed above and the fresh-environment replay each exited successfully. All 27 public declarations in the audit use only `propext`, `Classical.choice`, and `Quot.sound`. The local Lean files contain no proof placeholders or native decision tactics. Lake reports legacy-import module-format warnings. The frozen challenge had the requested SHA-256 before and after Round 2, `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`.

## Round 3 — Final Push & Campaign Synthesis

**Case C.** Every valid cyclic set of size $n\ge3$ satisfies

$$
                         N\ \ge\ \frac{11}{16}\,2^n. \tag{R3.1}
$$

This improves the Round 2 coefficient $9/16$ by $1/8$ and gives $N\ge704$ at $n=10$. A nondegenerate affine copy of $\{0,1,3\}$ gives $N\ge(3/4)2^n$, even when its step is a nonunit. Both statements apply directly to the frozen definition. For ten points, a finite refinement and exhaustive computation raise the floor to **724**. Two independent searches exclude **1015**, immediately below the conjectured minimum of 1016. The neighboring moduli **1013 and 1014** are also excluded. Every ten-point counterexample must therefore satisfy **$724\le N\le1012$**. [Lean proofs](FonollosaMinModulus/ResearchLemmas.lean) · [Census results](scripts/round3_results.txt)

Inequality (R3.1) exceeds Sitjar’s general formula at every $n\ge6$. Write $t=2^{n-4}$. The new gain over $2^{n-1}$ is $3t$. This exceeds $2n-2$ at six and doubles at each step. The other term in Sitjar’s gain is $\lceil(8t-1)/(n-1)\rceil\le2t$ since $n-1\ge5$. [Sitjar, Theorem A](https://doi.org/10.5281/zenodo.24228247)

### Eight labels and exchanges of different sizes

Fix $a\ne b$ in $A$, put $d=b-a$, $R=A\setminus\{a,b\}$ and $H=2^{|R|}$. Use the map from (R2.1) with the eight labels $0\le i<8$. Suppose the images of $(i,S)$ and $(j,T)$ coincide, with $i\ge j$. Set

$$
 p=\left\lfloor\frac{i-|S|}{2}\right\rfloor-
   \left\lfloor\frac{j-|T|}{2}\right\rfloor,\qquad q=i-j-p .
$$

Equality in the parity coordinate gives $|T|-|S|=p-q$. Equality in the cyclic coordinate gives $F_a(T)-F_a(S)=pd$. If $p<2$ or $q<2$, the Round 1 pivot interval gives $T=S$. Then $0\le p=q\le1$ and $pd=0$, so the labels agree. Otherwise $p,q\ge2$ and $p+q\le7$.

Write $D=S\setminus T$ and $C=T\setminus S$. The rule $(p,q,D,C)$ has disjoint sides and satisfies

$$
 |C|+q=|D|+p,\qquad \sum C-\sum D=pb-qa.
$$

Its possible source subsets contain $D$ and avoid $C$. There are $H/2^{|D|+|C|}$ such sources. Deleting the labels from $p+q$ through $7$ on these sources suffices for this rule. Every remaining label has a distinct image in two copies of the cyclic group. Thus

$$
 8H\ \le\ 2N+\sum_{u} (8-p_u-q_u)\frac{H}{2^{|D_u|+|C_u|}} . \tag{R3.2}
$$

The sum runs over all admissible rules, including rules with an empty side. This last detail matters when the two exchanged subsets have different sizes.

**Joint crossing.** Distinct rules $u,v$ satisfy $D_u\cap C_v\ne\varnothing$ whenever $p_u\le p_v+1$ and $q_v\le q_u+1$. Indeed, subtract their equations using the coefficient vector

$$
 1_{C_u}-1_{D_u}+1_{D_v}-1_{C_v}
 +(q_u-q_v)1_a+(p_v-p_u)1_b.
$$

A missing intersection would make every coefficient at least $-1$. The coefficients sum to zero and their weighted sum vanishes. Validity forces the vector to vanish. Its pivot entries first identify the two signatures. Its other entries then identify both disjoint sides, contradicting distinctness.

In any $2\times2$ square of signatures this crossing holds in both directions. In a uniformly ordered ground set, the events that all of $D_u$ precedes all of $C_u$ are therefore disjoint. Each has probability $1/\binom{h}{|D_u|}$ for $h=|D_u|+|C_u|$, including probability one when either side is empty. This permutation argument gives the weighted Bollobás set-pair inequality. The Lean proof counts finite permutations and source subsets with natural-number arithmetic. [Set-pair counting proof](FonollosaMinModulus/SetPairCounting.lean)

**The three squares.** Take $4d\ne0$. An order-three difference already gives $N\ge3H$, so assume $3d\ne0$. In the following table, each entry lists a signature and its weight $8-p-q$.

| Square | Signatures and weights | Maximum total charge |
|---|---|---:|
| Central | $(2,2):4$, $(3,2):3$, $(2,3):3$, $(3,3):2$ | $3H/2$ |
| First outer | $(4,2):2$, $(4,3):1$, $(5,2):1$ | $H/2$ |
| Second outer | $(2,4):2$, $(3,4):1$, $(2,5):1$ | $H/2$ |

For either outer square, a weight-two rule has side sizes differing by two, so $\binom h{|D|}/2^h\le1/4$. A weight-one rule has nonempty union and ratio at most $1/2$. Multiplication by the separating-event probabilities and summation give the two outer bounds. Pascal's recurrence proves the binomial estimates in Lean. For the gap-two estimate it suffices to check $h\le9$ directly and propagate the uniform row bound from $h=9$.

If the central square has no $(2,2)$ singleton exchange, its weight-four rules have $h\ge4$ and ratio at most $3/8$. The other rules have $h\ge1$ and weight at most three. If a singleton $x\mapsto y$ exists, it costs $H$. Every other central rule removes $y$ and inserts $x$. Delete those two forced coordinates from its separating event. The resulting pairs still cross in both directions. For residual size $h'>0$ their binomial ratio is at most $1/2$. Their original cylinders have an extra factor $1/4$ and their weights are at most four, so their total costs at most $H/2$. If $h'=0$, the ranks require $p=q$. The weight-four reverse exchange would give $4d=0$. The remaining weight is at most two and obeys the same estimate. This proves the central bound in both cases. Iterating a singleton argument only applies at levels where a singleton exists.

Substitution in (R3.2) gives $8H\le2N+5H/2$. A suitable pivot pair always exists. In a cyclic group the nonzero elements killed by two all have the same representative $N/2$. Choose distinct $a,b,c$ and put $x=b-a$, $y=c-a$. If $4x=4y=0$, then either both doubles vanish, exactly one vanishes, or the two nonzero doubles coincide. The first forces $x=y$. The second gives $x=2y$ or $y=2x$. In the last case $x-y$ and $2x$ are the same nonzero involution, giving $x+y=0$. Each of the latter possibilities gives a forbidden midpoint. Consequently a pair with $4d\ne0$ exists as soon as $n\ge3$.

For the stronger conditional result take $c=3b-2a\in R$. There is a rule $(3,2,\varnothing,\{c\})$. Its empty removal side and directed crossing force every rule with $q\le3$ to be this very rule. Its charge is $3H/2$. The square with $q\ge4$ contributes at most $H/2$, giving $8H\le2N+2H$. In particular a sub-768 ten-set cannot have a unit normalization with third coordinate three. The coefficient $3/4$ is a ceiling for a single constant valid at every $n\ge3$. The triple $\{0,1,3\}$ at $N=6$ attains it. Its ten three-term multisets have integer sums $0,1,2,3,3,4,5,6,7,9$, with just one congruent to four.

**Other label counts.** In the relaxation with no $(2,2)$ singleton and pivot order larger than the diagonal signatures, give each signature its total separating-event probability. Each unit square has total probability at most one. The sharp values of this *relaxation* for consecutive labels are shown below. The script reconstructs primal and dual witnesses from an LP solution and checks every inequality and equality over exact rational numbers. For unequal sides with size gap $g>0$, its binomial maximum occurs by row $g^2$, as the ratio of consecutive same-parity terms is $(h+2)(h+1)/((h+2)^2-g^2)$. [Exact certificate checker](scripts/round3_slots.py)

| Labels | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|
| Allowed charge divided by $H$ | $3/8$ | $3/4$ | $13/8$ | $5/2$ | $16873/4096$ | $11753/2048$ |
| Resulting coefficient of $2^n$ | $37/64$ | $21/32$ | $43/64$ | $11/16$ | $19991/32768$ | $8727/16384$ |

Replacing the parity coordinate by $(i-u|S|)\bmod k$ changes the label distance to $(k-u)p+uq$. The same rational test gives $21853/32768$, $43031/65536$ and $27/40$ for $(k,u,L)=(3,1,11),(4,1,14),(5,2,18)$ respectively. These optimizations bound the stated signature model. They leave room for extra relations between squares or different maps. In particular, one-way crossing alone does not give the two-way permutation inequality for unequal sides. The ordered pairs $(\{x\},\varnothing),(\varnothing,\{x\})$ have the requisite forward intersection, yet their two event probabilities sum to two.

**Why eight is optimal in this relaxation.** There is an exact obstruction valid for every layer count $k$, slope $0\le u\le k$ and label length $L$. Put $\lambda=L/k$ and $\theta=u/k$. Give event mass one to each of the four signatures $(2,2),(2,4),(4,2),(4,4)$. Every unit square contains at most one of them. Their admissible binomial ratios in the relaxation are $3/8,1/4,1/4,1/2$. Each weighted positive part has threshold $(1-\theta)p+\theta q$. The two off-diagonal thresholds average to three, so convexity gives the following lower bound on the relaxed maximum loss divided by $kH$,

$$
 \tfrac38(\lambda-2)_+ + \tfrac12(\lambda-3)_+
                   +\tfrac12(\lambda-4)_+ .
$$

Subtracting this expression from $\lambda$ gives at most $\lambda/8+9/4\le11/4$ for $\lambda\le4$, and at most $17/4-3\lambda/8\le11/4$ for $\lambda\ge4$. Division by four caps the provable coefficient at **$11/16$**. The four masses give a feasible witness for the relaxation. Simultaneous realization by a cyclic set imposes additional conditions. The eight-label proof attains the ceiling of this entire class of signature-square estimates. Any improvement must use an additional restriction on simultaneous exchanges or another packing map.

### A finite refinement for ten points

Round 2 gives a unit difference throughout the remaining ten-point interval. Normalize that pair to $a=0,b=1$ and retain the eight other coordinates. For each signature and pair of side sizes $d,c$ there are $2^{8-d-c}$ source subsets per rule. In each signature square the permutation budget is **840**. A rule consumes $840/\binom{d+c}{d}$ units. This common denominator covers all rows up to eight. The following restrictions make the integer optimization stronger than the continuous square estimates.

- A rule with an empty side forbids every other rule with which directed crossing would require a point in that side. The checker enumerates exactly which signatures have such a rule. In its own signature the rule is unique.
- When one side is a singleton and the other has size $k$, the singleton centres are distinct and each opposite side contains every other centre. At $k+1$ centres every opposite side consists exactly of the other centres. Consequently all centre doubles agree. A cyclic group has at most two preimages under doubling, which rules this out for $k\ge2$. For $k=1$, two rules would be reverses, forcing twice the displacement to vanish.
- For $d=c=2$, enumerate five distinct removal edges on eight labelled points. An insertion edge must avoid its own removal edge and meet all four others. The test finds 420 labelled assignments with a reverse exchange and 672 further assignments with equal total coordinate multiplicities on the two sides. These would force $2g=0$ and $5g=0$ respectively for the common displacement $g$. Here $g=p$ before conditioning and $g=p+2$ after stripping the forced coordinates of a central singleton. Since $p\in\{2,3\}$, the modulus is too large for either equality. For fewer than eight coordinates, embedding in the same eight-point ground set preserves the test.
- Four such rules are impossible below 1016 as well. Relabel the first rule to $\{0,1\}\mapsto\{2,3\}$ on the eight coordinate **indices**. Generate the other three ordered pairs of disjoint edges with both crossings, distinct sides and no reversals. Sorting the columns of the incidence matrix gives 37 types. Permuting the four rows gives eight types. One yields a nonzero balanced signed relation with every entry at least $-1$. Three yield a small nonzero multiple of the unit equal to zero. Each of the other four uses five coordinates. Translate one coordinate to zero and multiply the resulting four linear equations by the adjugate. In two types a determinant of absolute value two forces two distinct coordinates into the same doubling fibre. In the other two a determinant of absolute value four puts three into one quadrupling fibre. Each possibility gives an antipodal pair in the cyclic group. The Round 1 antipodal exclusion therefore gives a cap of three rules. The checker verifies each signed relation, integer dependency, determinant and repeated entry exactly.

The program enumerates the one-sided signatures and runs an integer knapsack independently on each square. With a distinguished central singleton it charges 256 for that rule and uses six free coordinates in the residual permutation test. The maximum admitted loss is 608 without the singleton and 624 with it. Hence $2N\ge2048-624$ and **$N\ge712$**. The knapsack deliberately permits combinations that need not be jointly realizable. Every actual profile satisfies its constraints. [Exact enumeration and knapsack](scripts/round3_profiles.py)

A further computation in the same checker excludes the residual $(2,2)$ singleton and gives maximum loss 604 in the distinguished case. With no distinguished singleton, loss greater than 604 requires the two one-sided signatures $\{(3,4),(4,2)\}$, their reflections $\{(2,4),(4,3)\}$, or $\{(2,4),(4,2)\}$. These facts give a short list of necessary prefixes. Through 719 the loss exceeds 608, so there must be disjoint pairs $x,x+2$ and $u,u+4$ off the pivots. At 720 and 721 a valid set must contain the same chain unless both outer one-sided rules occur. In the first configuration their intersection forces the points $-3,7$. Reflection in $1/2$, meaning $t\mapsto1-t$ in any modulus, covers the second. In the third configuration the removal and insertion pairs intersect and have sums $-2$ and $4$. They give three distinct points $x,4-x,-2-x$. These reductions use the directed crossing criterion and work for composite moduli.

At 722 and 723, the required losses are 604 and 602. If there is no chain and none of $(4,2),(2,4),(4,3),(3,4)$ is one-sided, the maximum admitted loss is 600. Up to reflection, these one-sided rules give either a point $4$ or a pair $x,4-x$. In the former case the global minimum third coordinate must be four, since the three-quarters theorem already excludes three. In the latter case fix the four-point prefix $0,1,x,4-x$. Two of the six unknown coordinates share one of five colors, giving a six-point prefix for the target-sum test. These are unrestricted exclusions at each modulus once the listed cases have been exhausted.

The primary program exhausted the fixed configurations at all twelve moduli $712,\ldots,723$, visiting 28,613,281 six-point prefixes and 46,293,689 target graphs. The independent implementation visited 27,922,400 six-point prefixes and checked 766 candidate ten-sets. Both returned zero. At 722 and 723 the additional full $z=4$ searches visited 7,619,629 primary and 7,775,182 independent six-point prefixes, also with zero valid leaves. Thus the **continuous unrestricted ten-point floor is $N\ge724$**. The formal general theorem gives 704 directly. The extra twenty moduli use the finite profile proof and the two C++ checks.

### The target-sum census at 1015

All ten-point candidates below 1016 that survived Round 2 have a unit difference. At 1015 the independent nonunit check used the CRT axes of orders $5,7,29$. A unit pair can be sent to $0,1$. Among all such normalizations choose the smallest possible third coordinate $z$. Then $A$ contains $0,1,z$, every other representative is larger than $z$, and normalizing any ordered unit pair in any triple of $A$ gives a third coordinate at least $z$. A midpoint excludes $z=2$. Round 2 exhausted $z\ge27$. The new search takes all the remaining values $3\le z\le26$.

For a prefix $P$ write $R_j(P)$ for the residues attainable by exactly $j$ entries, with repetition, and $H_j(P)$ for their complement. Inserting $x$ updates the rows by $R_j(P+x)=R_j(P)\cup(x+R_{j-1}(P+x))$. Heredity permits rejecting any prefix with a rival to its own all-ones sum. For a proper prefix, any candidate final sum $\sigma$ must belong to $H_{10}(P)$, since a representation supported entirely on $P$ omits a final point.

- **Four-clique search.** The primary solver reuses the Round 2 reachability code through a shared header. At six points, fix $\sigma$ and retain a vertex $x$ only if $\sigma-hx\notin R_{10-h}(P)$ for $1\le h\le10$. An edge $x,y$ requires $\sigma-hx-jy\notin R_{10-h-j}(P)$ for every $h,j\ge1$ with $h+j\le10$. A valid completion gives a four-clique of total weight $\sigma-\sum P$. Hashing pairs strictly to the left of the third vertex visits each sorted quadruple with that sum. For prefixes with more than 48 available sums, the solver fixes the first tail vertex, updates the exact rows and performs the corresponding triangle test. Every surviving clique goes through the insertion test and a scalar count from the frozen definition. [Primary C++ solver](scripts/round3_clique.cpp)
- **Independent check.** The second implementation generates forbidden normalized triples by taking affine images of $\{0,1,t\}$ for $2\le t<z$. It builds reachability rows with circular 64-bit reads. It enumerates increasing tail coordinates by nested loops, determines the last coordinate by subtraction, and checks each resulting ten-set by exact insertion. It uses no clique edges. It branches to a seven-point prefix above 30 available sums. A second entry point traverses the high-$z$ interval with sorted lists and a shared table of affine minima. [Independent C++ verifier](scripts/round3_verify.cpp)
- **Three-color reduction.** Color the seven unchosen residues. At least one color occurs three times. Choose its first three representatives in increasing order as the next coordinates of the prefix. The four remaining points may include *smaller* representatives of the other colors. The implementation retains them. For these shards the fourth coordinate runs all the way to $N-3$. The solvers use different colorings. Sorted shards instead run to $N-7$. The faster primary mode also propagates hereditary validity to all future candidates. A shard reports completion only after joining all workers.
- **Positive controls.** From $0,1,3,7,15,31$ at 1016 both solvers recover $0,1,3,7,15,31,63,127,255,511$. The color-cover search also finds it from the single chosen fourth coordinate 127 in the primary implementation and 31 in the independent one. In the first control the remaining four coordinates all precede at least one of the three chosen color representatives. This checks the ordering issue directly.

The primary 1015 run completed **23,884** fourth-coordinate jobs for $3\le z\le26$, reached **562,690,729** six-point prefixes and tested **680,066,873** target graphs with enough vertices. Zero sum-compatible cliques survived the full graph and normalization checks. Prefix and graph counts refer to visits in their respective decompositions. Together with the earlier high-third-coordinate and nonunit results this excludes every ten-set at 1015.

The independent run for $3\le z\le26$ reached **147,554,700** six-point prefixes and tested **3,160** complete tuples. Its separate traversal of *all* 981 higher third coordinates, $27\le z\le1007$, reached 150,420,183 six-point prefixes and tested 51 complete tuples. Every validity count was zero. Repeating the independent CRT-axis enumeration gave zero ten-point candidates at 1015 with no unit pair. Thus the independent coverage includes both the large-third-coordinate interval and the nonunit case.

### Neighboring moduli

At the prime 1013 every difference of distinct residues is a unit. The primary solver exhausted $3\le z\le23$ in 20,937 fourth-coordinate jobs, reaching 107,589,956 six-point prefixes and 1,087,761 target graphs with zero surviving cliques. For the same low range the independent verifier visited 107,766,244 six-point prefixes and tested 1,410 complete candidates, all of which failed. Its separate high-third-coordinate traversal exhausted $24\le z\le1005$, visiting 29,523,167 six-point prefixes with zero candidate ten-sets. Together with the Round 2 high-range census, this gives two complete checks at 1013.

At $1014=2\cdot3\cdot13^2$, there is a short additional reduction for the independent no-unit check. A valid ten-set generates the group after translation, since a proper subgroup has order at most 507 and the ten-point theorem requires 704. Opposite-parity differences generate every difference. For two points of the same parity, subtract their differences to a common point of the other parity. If every difference is a nonunit, each opposite-parity difference has odd gcd greater than one with 1014. At least one such gcd is three, since every larger odd divisor is divisible by 13. A unit scaling and a translation give the pair $0,3$. At least two points lie outside $3\mathbb Z$, whose order 338 is below the nine-point bound 352. Fix its first two outside points and then a same-color pair among the six remaining points in five colors. The independent completion algorithm exhausted 52 normalized third-coordinate roots, visited 1,606,144 six-point prefixes, and tested 2,319 complete tuples. All failed validity.

For the unit normalization at 1014, the primary solver covered $3\le z\le44$ in 41,475 fourth-coordinate jobs, with 301,221,521 six-point prefixes, 17,918,233 target graphs and zero surviving cliques. Its additional run at $45\le z\le49$ covered 4,820 jobs and 17,907,559 prefixes, again with zero cliques. The independent $z=3$ check visited 14,314,829 six-point prefixes and tested 11,279 complete tuples. All failed. The separate upper traversal covered all 962 values $45\le z\le1006$, with 586,692,698 six-point prefixes and 17,705 complete tuples, all invalid. Together with the no-unit check these ranges exhaust 1014. Independent traversals overlap at $z=3$, at $45\le z\le49$, and on the Round 2 interval $z\ge192$.

### Reproduction and axiom audit

Lean 4.36.0 built the root module and all three fresh kernel replays exited successfully. The following commands reproduce those checks from the project root. Running fresh checks one module at a time also avoids the multi-module loader issue recorded in Round 2.

```sh
lake build
lake env lean scripts/check_axioms.lean
lake env leanchecker --fresh --verbose FonollosaMinModulus.Challenge
lake env leanchecker --fresh --verbose FonollosaMinModulus.SetPairCounting
lake env leanchecker --fresh --verbose FonollosaMinModulus.ResearchLemmas
shasum -a 256 FonollosaMinModulus/Challenge.lean
```

The axiom inventory covers 41 public proof declarations. Exactly five depend on `propext` and `Quot.sound` alone. They are `BinaryCoins.complement_gap`, `SetPairs.binom_half`, `SetPairs.binom_three_eighths`, `SetPairs.binom_quarter_gap_two`, and `RankSlots.four_signature_relaxation_ceiling`. The other 36, including the unconditional and conditional density theorems, depend on exactly `propext`, `Classical.choice`, and `Quot.sound`. The per-declaration audit names all 41. The source scan found zero uses of `sorry`, `admit`, or `native_decide` in the local Lean modules. Lake emits its legacy-import notices for the existing modules. [Axiom inventory](scripts/check_axioms.lean)

Use an ordinary Python interpreter with SciPy and SymPy. The two C++17 binaries have separate implementations of the affine and reachability calculations. A primary shard records every fourth-coordinate job. The audit checks the exact integer interval, rejects duplicate or missing jobs, matches component sums to the final counters, and hashes the sorted branch results. The stored digests are independent of worker scheduling. [Coverage checks](scripts/round3_census.py) · [Machine results](scripts/round3_results.txt)

```sh
py=/Users/mw/miniconda3/bin/python3
outdir=/tmp/fonollosa-round3
mkdir -p "$outdir"
clang++ -std=c++17 -O3 -march=native -pthread scripts/round3_clique.cpp -o "$outdir/clique"
clang++ -std=c++17 -O3 -march=native -pthread scripts/round3_verify.cpp -o "$outdir/verify"
"$py" -B scripts/round3_profiles.py
"$py" -B scripts/round3_slots.py

"$py" -B scripts/round3_census.py run primary "$outdir/clique" 7 "$outdir" 1015 3 26
"$py" -B scripts/round3_census.py run independent "$outdir/verify" 6 "$outdir" 1015 3 26
"$py" -B scripts/round3_census.py audit --independent "$outdir" 1015 3 26
"$outdir/verify" upper 1015 27 1007 4 > "$outdir/upper-1015.log"
"$py" -B scripts/round3_census.py upper "$outdir/upper-1015.log" 1015 27 1007
"$py" -B scripts/round2_verify.py nonunits > "$outdir/crt.log"

"$py" -B scripts/round3_census.py run primary "$outdir/clique" 7 "$outdir" 1013 3 23
"$py" -B scripts/round3_census.py run independent "$outdir/verify" 5 "$outdir" 1013 3 23
"$py" -B scripts/round3_census.py audit --independent "$outdir" 1013 3 23
"$outdir/verify" upper 1013 24 1005 4 > "$outdir/upper-1013.log"
"$py" -B scripts/round3_census.py upper "$outdir/upper-1013.log" 1013 24 1005

"$py" -B scripts/round3_census.py run primary "$outdir/clique" 7 "$outdir" 1014 3 49
"$py" -B scripts/round3_census.py audit "$outdir" 1014 3 44
"$py" -B scripts/round3_census.py run independent "$outdir/verify" 3 "$outdir" 1014 3 3
"$py" -B scripts/round3_census.py audit --independent "$outdir" 1014 3 3
"$outdir/verify" upper 1014 45 1006 4 > "$outdir/upper-1014.log"
"$py" -B scripts/round3_census.py upper "$outdir/upper-1014.log" 1014 45 1006
"$outdir/verify" nonunit 1014 4 > "$outdir/nonunit-1014.log"

for n in {712..717}; do "$outdir/clique" profile "$n" 4 > "$outdir/profile-$n.log"; done
for n in {718..723}; do "$outdir/clique" profile-fast "$n" 4 > "$outdir/profile-$n.log"; done
for n in {712..723}; do "$outdir/verify" profile "$n" 4 > "$outdir/ind-profile-$n.log"; done
for n in 722 723; do
  "$py" -B scripts/round3_census.py run primary "$outdir/clique" 4 "$outdir" "$n" 4 4
  "$py" -B scripts/round3_census.py run independent "$outdir/verify" 4 "$outdir" "$n" 4 4
  "$py" -B scripts/round3_census.py audit --independent "$outdir" "$n" 4 4
done
"$py" -B scripts/round3_census.py report "$outdir" > "$outdir/results.txt"
cmp "$outdir/results.txt" scripts/round3_results.txt

"$outdir/clique" 1016 3 7 7 1 15,31
"$outdir/verify" 1016 3 7 7 1 15 31
"$outdir/clique" 1016 3 127 127 1 cover-fast
"$outdir/verify" 1016 3 31 31 1 cover
```

The original report prefix is 52,094 bytes with SHA-256 `ca9dbcbb30af6cb78b0d5afd54fee7177fcb282995900ac3d29cac410744341e`. Its hash can be reproduced with `head -c 52094 RESEARCH_ANALYSIS.md | shasum -a 256`. The frozen target has SHA-256 `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`.

### Standalone contributions, ranked

1. **The unconditional $11/16$ cyclic bound.** Directed crossing for unequal exchanges permits a joint estimate over signatures. The four-signature witness identifies exactly what the local permutation argument loses. The $3/4$ theorem for an affine $\{0,1,3\}$ exhibits the gain from a single one-sided exchange.
2. **The ten-point boundary census and continuous lower bound.** Exact target-sum searches, an independent completion algorithm and checked normalization ranges turn numerical searches into reproducible exclusions. The eight-coordinate exchange classification explains why only a few fixed configurations can approach equality in the finite bound.
3. **Binary-core rigidity for every $n\ge6$.** With one unknown coordinate, the full conjectured lower bound and the forced residue follow from the binary-coin argument. Allowing two unknown coordinates and nonunit steps gives the finite extension exclusions through $n=25$ recorded in Round 1.
4. **Antipodal and nonunit reductions for ten points.** The nine-point quotient, parity lifting and CRT axes exclude these obstructions across the subthreshold search. Together they justify the single unit-pair normalization used in the endpoint census.

The remaining mathematical question is which signature families can coexist *across* the three squares and across different choices of pivot pair. The four-signature relaxation witness gives a concrete target. Realizing its weight requires many $2$-by-$2$ exchanges in the central square and efficient off-centre exchanges on both sides. The finite ten-point argument already rules out four such central exchanges. A dimension-independent stability theorem for these simultaneous requirements would address the gap left by (R3.1).
