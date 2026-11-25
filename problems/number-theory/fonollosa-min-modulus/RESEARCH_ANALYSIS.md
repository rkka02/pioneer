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
