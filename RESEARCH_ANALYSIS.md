# Fourier entropy and influence on the uniform cube

## MAX Round 1 · 25 November 2026

**Case C.** A finite, balanced, monotone Boolean function has ordinary Fourier entropy divided by influence in the interval

$$
 [\,6.5218511673478223969022,\;6.5218511673478223969023\,].
$$

In particular every constant in the frozen conjecture satisfies **$C>6.52185116734782239690$**. This raises the previous local floor $6.521850225089574148$ by about $9.42\times10^{-7}$. The proof below establishes bounded pooled loss on all four model families investigated, including towers with arbitrarily rare branching. A perfectly packed matching obeys an exact score identity, and sufficiently dense partial matchings also preserve a common component bound. The universal bound on pooled loss and the original FEI conjecture remain unresolved. The numerical lower bound is locally certified in Python. [Round 1 certificate](scripts/max1_spinal_seed.py) · [Published 18-bit starting point](https://numaro.tech/research/fourier-entropy-influence-2026/)

### A finite witness with a tuned singleton

Use sign convention, base-two logarithms, squared Walsh masses $p_S$, $H=\sum p_S\log_2(1/p_S)$ and $I=\sum |S|p_S$. Let $g$ be Numaro's 18-bit seed. Its nine core bits index 512 addresses. Nine disjoint edges read independent private selector bits. The endpoint pairs and the truth table outside those edges are specified in §2 below. Each edge has probability $r=1/256$ and there is one edge in each core direction. Write $c_0$ for the sign table on the core with zeros on those edges, and $v$ for the table that is $+1,-1$ at each ordered pair and zero elsewhere. Distinguish the first core bit of $g$. Its singleton coefficient is $q=57/256$, and $I_0=261/128$. [Seed table](scripts/walsh.py)

For a balanced monotone $F$ with distinguished singleton $x$, build $P(F)$ from four copies in a **single path**. At each of the first three copies, substitute the next copy only at the distinguished input, keeping every other input an independent dictator. Distinguish the deepest copy's distinguished input. Under one such substitution, coefficients avoiding the slot persist. Those using the slot are multiplied by a nonempty coefficient of the child. The occupied slot has probability $I_j(F)=x$ by monotonicity. The product formula for entropy and additivity of degree give, with $s=1+x+x^2+x^3$,
$$
 \widehat{P(F)}(\{\text{distinguished bit}\})=x^4,\qquad
 H(P(F))=sH(F),\qquad I(P(F))-1=s(I(F)-1).
$$
This realizes a singleton near $0.00246$ while preserving the amplified score $H/(I-1)$.

Define $F_0=g$. To obtain $F_{k+1}$, on **each** of the nine host edges evaluate a separate $P(F_k)$, identifying its distinguished input with the free core bit on that edge. The private inputs of the nine copies are disjoint. Keep the exterior of the host and distinguish its first core bit again. Each inserted gate is balanced and the exterior sums to zero. Monotonicity across core edges follows from the original selector table being monotone for every choice of independent selector signs. Inside each matched edge it follows from the inner gate. Thus the singleton–influence identity holds at every stage.

Put $n_0=18$, $x_0=q$, $t=x_k^4$, $s=1+x_k+x_k^2+x_k^3$, $H_c(t)=\sum_T\eta((\widehat c_0(T)+t\widehat v(T))^2)$ and $\eta(y)=y\log_2(1/y)$. The private-empty slice is $c_0+t v$. Every term containing a private variable comes from exactly one edge. Fixing its eight address bits makes $256$ copies with amplitude divided by $256$. On every edge the omitted singleton mass is $t^2$. In the first core direction only its parallel edge changes the singleton mean, by $r t$. The resulting exact recursion is
$$
\begin{aligned}
 x_{k+1}&=q+r t,\qquad n_{k+1}=9+36(n_k-1),\\
 I_{k+1}&=I_0+9r\,s(I_k-1),\\
 H_{k+1}&=H_c(t)+9r\{sH_k-\eta(t^2)+16(1-t^2)\}.
\end{aligned}
$$
For influence, replacing the original selector on one edge changes the sum of singleton coefficients by $r(I(P(F_k))-1)$. This also follows by counting spectral degrees. The interval $0\le x<1/4$ is invariant, so $9rs<0.047$. The additive entropy terms are bounded since the private-empty slice is a subprobability on 512 characters. This recursion cannot generate unbounded $H/I$.

| Shared stages $k$ | Arity $n_k$ | Certified $H_k/(I_k-1)$ interval |
|---:|---:|---|
| 1 | 621 | $[6.52185093166204148858,\,6.52185093166204148859]$ |
| 2 | 22,329 | $[6.52185115673538563879,\,6.52185115673538563880]$ |
| 4 | 28,937,385 | $[6.52185116732622372142,\,6.52185116732622372143]$ |
| 10 | 62,990,386,838,799,273 | $[6.52185116734782239690,\,6.52185116734782239691]$ |

Take the depth-80 disjoint self-composition of $F_{10}$, a specific function on $62{,}990{,}386{,}838{,}799{,}273^{80}$ bits. Balanced composition gives its **ordinary** ratio as $[H_{10}/(I_{10}-1)](1-I_{10}^{-80})$. The interval at the start of the report encloses this value. The verifier uses integer WHTs, rational logarithm bounds from the atanh series in §2, and outward dyadic interval arithmetic. An independent exact factored WHT of the entire 621-variable first stage gives 8,117 nonempty magnitude/degree bins, mass one, and $I_1=1146757521141/549755813888$. It reproduces the entropy interval from the transfer. An ordinary WHT checks the single-slot substitution on a complete small cube. This is a finite witness for a lower bound. [Executable certificate](scripts/max1_spinal_seed.py)

### What can be charged to influence in the pooled loss

For $i\in S$ with $p_S>0$ put $\ell_i(S)=\log_2(1+p_{S-i}/p_S)$ and $A(S)=\sum_{i\in S}\ell_i(S)$. Set $A(\varnothing)=0$ and omit zero masses. Decompose
$$
 P_2=\sum_{S\ne\varnothing}\frac{p_S}{|S|}A(S)^2=D+X,\quad
 D=\sum_{S,i\in S}\frac{p_S}{|S|}\ell_i(S)^2,\quad
 X=\sum_{S}\frac{p_S}{|S|}\sum_{i\ne j\in S}\ell_i(S)\ell_j(S).
$$
Throughout, the empty set contributes zero to each quotient. For $I>0$, giving each incidence $(S,i)$ mass $p_S/I$ defines a probability measure. Cauchy–Schwarz gives $\mathbb E_p A\le\sqrt{IP_2}$, including biased functions. [Formalized for the frozen spectrum](FEI/ResearchLemmas.lean)

**A degree-sensitive tail bound.** Fix $i$. Write $u_T=\widehat{E_i f}(T)$, $v_T=\widehat{D_i f}(T)$ for $i\notin T$. The two physical functions are half the sum and difference of the sign restrictions. They have disjoint supports, their squares sum to one, and $|D_i f|$ is the indicator of a set of density $\alpha_i=I_i$. Therefore $\|D_i f\|_{3/2}^2=\alpha_i^{4/3}$ and $\sum_T(u_T^2+v_T^2)=1$. Bonami–Beckner with $\rho=1/\sqrt2$ gives $\sum_T 2^{-|T|}v_T^2\le\alpha_i^{4/3}$. Hölder with exponents $4/3,4$ yields
$$
\begin{aligned}
 \sum_{S\ni i}p_S\,2^{(\ell_i(S)-3|S|)/4}
 &=2^{-3/4}\sum_{T:v_T\ne0}(2^{-|T|}v_T^2)^{3/4}(u_T^2+v_T^2)^{1/4}\\
 &\le 2^{-3/4}\alpha_i .
\end{aligned}
$$
The subtraction of $3|S|$ is essential here. The earlier bent lookup has an unbounded exponential moment for the unshifted loss. The physical-space disjointness also gives the exact signed Walsh convolution identities $u*v=0$ and $u*u+v*v=\mathbf1_{\{0\}}$, where convolution is the unnormalized sum over symmetric difference of frequency indices. The estimate above uses the norms implied by the Boolean identities. [Cube hypercontractivity, chapter 9](https://arxiv.org/abs/2105.10386) · [Integer WHT and fourth-root checks](scripts/max1_boolean.py)

Set $U=(\ell_i-3|S|)_+$ under the incidence law. Markov gives $\Pr(U>s)\le2^{-(s+3)/4}$ for $s>0$. On $k=|S|\ge1$ one has $\ell_i^2/k\le3\ell_i+3U+U^2$. Tail integration proves
$$
 D\le3\mathbb E_p A+c_0 I,\qquad
 c_0=2^{-3/4}\left(\frac{12}{\ln2}+\frac{32}{(\ln2)^2}\right)<50.
$$
Consequently a universal $X\le K I$ would give $y^2\le3y+c_0+K$ for $y=\sqrt{P_2/I}$, and hence $y\le3+\sqrt{c_0+K}$. Conversely $0\le X\le P_2$. This equivalence is for the proposed second-moment strengthening. FEI itself requires only a first moment.

**Restrictions of several coordinates.** For a fixed block $B$, put $L_B=H(S\cap B\mid S\setminus B)$. At outside frequency $T$, the restricted amplitude as a function of the fixed input is $h_T(x_B)=\sum_{U\subseteq B}a_{T\cup U}\chi_U(x_B)$. Parseval identifies the marginal at $T$ with $\mathbb E h_T^2$. The entropy drop equals $L_B+J_B$ with $J_B=(\ln2)^{-1}\sum_T\operatorname{Ent}(h_T^2)$, where $\operatorname{Ent}(w)=\mathbb E[w\ln w]-\mathbb Ew\ln\mathbb Ew$. The cube logarithmic Sobolev inequality in uniform sign normalization gives $0\le J_B\le (2/\ln2)\sum_{i\in B}I_i$. The chain rule gives $L_B\ge\sum_{i\in B}L_i$. Thus the minimum of $L_B/\sum_{i\in B}I_i$ over positive-influence blocks is attained by a singleton. This rules out an improvement of the optimal **erasure** ratio just by bundling a predetermined block. A tree that changes its next block after observing previous answers can still have a different total cost. [Logarithmic Sobolev inequality on the cube](https://arxiv.org/abs/2105.10386) · [Exact block marginal and restriction checks](scripts/max1_boolean.py)

For a singleton, the mass from the missing-bit side of the conditional binary entropy is at most $(\log_2 e)I_i$, by $\ln(1+x)\le x$. Thus $\sum_i L_i\le\mathbb E_p A+(\log_2 e)I$. A bound on $y$ gives a relevant coordinate with $L_i/I_i\le y+\log_2 e$ when $y$ is replaced by its uniform upper bound. Induction uses the influence drop $I_i$ and the preceding bound for $J_i$. The fractional-certificate guarantee of a large coordinate in a low-degree polynomial does not give a bound on the mixed losses of *two* incident spectral deletions. The two-coordinate calculation below pinpoints what is missing from that route. [One-coordinate reduction](https://doi.org/10.5281/zenodo.24126590) · [Turturean's theorem](https://arxiv.org/abs/2611.09773)

A class of potential functions also has a sign obstruction. For $\Psi_w=\sum_S p_S w(|S|)$ the one-step drop is exactly $\sum_{S\ni i}p_S[w(|S|)-w(|S|-1)]$, because averaging the two child masses merges each Walsh pair. Every nondecreasing $w$ makes this drop nonnegative. Thus adding such a potential to $H$ cannot reduce any one-coordinate entropy drop. This includes the nonnegative, influence-bounded potentials $\mathrm{Var}(f)$, $I-\mathrm{Var}(f)$ and $\mathrm{Var}(f)-\sum_{|S|=1}p_S$. More generally bounded increments of $w$ change the charge by at most $\|\Delta w\|_\infty I_i$. A potential that tracks information about which coefficients overlap can behave differently. The tests compare the exact drops on ordinary signed WHTs for four weight functions. [Potential checks](scripts/max1_boolean.py)

### Exact recursion for pooled loss in towers

Let a gate $g$ receive independent copies of the same sign, of mean $\mu$. Expand its multilinear extension at $\mu$. Its biased squared coefficients are $(\partial_S g(\mu))^2(1-\mu^2)^{|S|}$. Normalize the nonempty coefficients by their sum, obtaining an occupied-set law $\pi$. The output mean is $g(\mu,\ldots,\mu)$. In a composed function the nonempty spectral sample first chooses occupied children from $\pi$, then independently chooses a nonempty spectral sample in each. This follows by expanding each centered child in its ordinary nonempty Walsh coefficients. It works with a different bias at every level.

Let $K$ be the total number of spectral leaves in such a nonempty sample. Write $r$ for incoming empty-to-active odds at the root of a subtree. When the occupied set is $S$ of size at least two, the deletion odds passed to child $j\in S$ are $r_j=\pi_{S-j}/\pi_S$ (zero for a missing numerator). For a singleton $S=\{j\}$ they are $r/\pi_{\{j\}}$. A deletion that leaves its child nonempty cancels every factor outside that child. Thus changing the incoming $r$ changes the loss only if the entire sample is one leaf. Such all-unary paths have weights $u=\prod \pi_{\{j\}}$ and loss $\log_2(1+r/u)$.

Use polynomials $F(z)=\mathbb E z^K$, $B(z,r)=\mathbb E z^K A$, $V(z,r)=\mathbb E z^K A^2$. At the bottom $F=z$ and the one-leaf loss is $\log_2(1+r)$. At any stage the incoming correction to $B(z,0)$ is $z\sum_u u\log_2(1+r/u)$, counting paths with multiplicity. For $V(z,0)$ square the logarithm in that correction. For a gate outcome with $k$ children write $b_j=B(z,r_j)$ and $v_j=V(z,r_j)$ computed in the preceding stage. Independence gives its three contributions
$$
 F^k,\qquad F^{k-1}\sum_j b_j,\qquad
 F^{k-1}\sum_j v_j+2 F^{k-2}\sum_{j<l} b_j b_l .
$$
Average with $\pi$ and omit the last term when $k=1$. Tracking only ordered products for distinct leaves retains the same cross-child term and has zero unary correction to its second polynomial. Finally $r=p_\varnothing/(1-p_\varnothing)$, and
$$ P_2/I=\frac1{\mathbb E K}\int_0^1 V(z,r)\,\frac{dz}{z}. $$
The common nonempty probability cancels. The integrand is a polynomial with nonnegative coefficients, hence convex. Midpoint lower sums and trapezoid upper sums on a dyadic mesh certify the integral even when the largest degree is $18^{20}$. The program uses integer gate WHTs, exact rational biased laws, outward 112-bit dyadics, and rational intervals obtained by widening correctly rounded 75-digit decimal logarithms before conversion to base two. Two full-cube, two-level comparisons cover both balanced and unequal-bias transfers, for both $P_2$ and $X$. [Exact transfer](scripts/max1_pool.py)

| Gates from leaves to root | Depths | Enclosures for $P_2/I$ in depth order |
|---|---|---|
| Rare switch, width 2 | 1, 4, 12 | $[.612516,.612703]$, $[1.682360,1.685447]$, $[1.621493,1.624914]$ |
| Rare switch, width 5 | 1, 4, 12 | $[.304004,.304191]$, $[.892071,.893024]$, $[1.325086,1.327418]$ |
| Rare switch, width 8 | 1, 4, 12 | $[.039461,.039513]$, $[.148821,.149021]$, $[.383476,.384039]$ |
| Widths $1,4,7,2,8,3$ | 3, 6 | $[.585810,.586544]$, $[1.169681,1.171707]$ |
| Iterated Tribes with widths $(2,2)$ | 2, 4, 5, 6 | $[5.015724,5.020262]$, $[8.056519,8.069127]$, $[6.922736,6.936383]$, $[6.368926,6.382321]$ |
| Skewed Tribes with widths $(1,3)$ | 2, 4, 5, 6 | $[3.059046,3.061069]$, $[7.649530,7.658329]$, $[8.080724,8.092680]$, $[7.033917,7.047191]$ |
| Numaro | 4, 12, 20 | $[11.577976,11.583951]$, $[11.107185,11.113052]$, $[11.104862,11.110728]$ |

For the Numaro tower, $X/I$ alone lies in $[10.401556,10.406978]$ at depth 4 and $[11.104850,11.110716]$ at depth 20. A finer sweep across depths 2–10 gives $[11.579469,11.580964]$ at depth 4, the largest of these nine disjoint intervals. Any universal constant for $P_2/I$ must therefore be **at least 11.579469**.

### Why the tested towers stay bounded at every depth

Choose a spectral leaf with the incidence law. At a gate on the path back from that leaf the probability of a marked outcome $(S,j)$ is $\pi_S/\bar k$ for each $j\in S$, where $\bar k=\sum_S |S|\pi_S$. Indeed every occupied child has the same expected number of descendant leaves. Iterating this count makes the marked outcomes independent along the path, with possibly different laws at different levels. Write
$$
 w_1=\sum_j\pi_{\{j\}},\quad d_b=\bar k-w_1,\quad
 y_j=\log_2(1/\pi_{\{j\}}),\quad m_a=\sum_j\pi_{\{j\}} y_j^a,\quad
 M=\sum_{|S|\ge2}\pi_S\sum_{j\in S}\log_2^2(1+\pi_{S-j}/\pi_S).
$$
Omit zero-mass summands. The chance of branching at this level is $h=d_b/\bar k$. Trace the unary steps from the leaf to the nearest branching node. The leaf loss for incoming root odds zero is bounded by the branching-node loss plus the sum $Y$ of the encountered $y_j$. This follows from $\log_2(1+r/u)\le\log_2(1+r)+\log_2(1/u)$ for $0<u\le1$. If the path is all unary, its loss with zero root odds is zero.

Suppose $m_1/d_b\le b_1$, $m_2/d_b\le b_2$ and $M/d_b\le b_*$ throughout the tower. Then $\mathbb EY\le b_1$ and $\mathbb EY^2\le b_2+2b_1^2$. At each level the recurrence for the first moment is $m_1/\bar k+(1-h)\mathbb EY_{\rm rem}$. For the second moment it is $m_2/\bar k+2(m_1/\bar k)\mathbb EY_{\rm rem}+(1-h)\mathbb EY_{\rm rem}^2$. Induction gives the claims, including truncated paths. Conditional on stopping, the mean squared branching loss at that level is $M/d_b$. Jensen within each nonempty set and $(a+b)^2\le2a^2+2b^2$ now give an all-depth bound on $P_2/I$ of
$$ 2b_*+2b_2+4b_1^2 \tag{R1} $$
for incoming root odds zero. For a balanced fixed gate with $d_b>0$, use the three actual ratios for its law. A balanced gate with $d_b=0$ is a signed dictator: in a linear Boolean polynomial the coefficient of each $x_ix_j$ in its square vanishes. A signed dictator adds zero unary cost. For the Numaro gate, certified upper endpoints in (R1) give **$P_2/I<28.643021$ at every depth**. The numerical enclosures above are much tighter for the indicated depths. [Spine and transfer calculations](scripts/max1_pool.py)

For every balanced Boolean gate, with $p=\pi_{\{j\}}$, one has $\sqrt p=|\widehat g(\{j\})|\le I_j$. Therefore $\sum_j(\sqrt p-p)\le d_b$. Put $z=-\frac12\ln p$ and use $e^z-1\ge z,\ z^2/2$ to obtain $m_1/d_b\le2/\ln2<3$ and $m_2/d_b\le8/(\ln2)^2<18$.

* **Arbitrarily rare near-dictators.** The switch reads $x$ unless all $w$ control bits vanish, in which case it reads $y$. Put $\delta=2^{-w}$. The two singleton magnitudes are $1-\delta,\delta$, and every nonempty control subset paired with exactly one of $x,y$ has magnitude $\delta$. Expanding the rare address indicator proves this spectrum. $I=1+w\delta$ and $d_b=w\delta+2\delta(1-\delta)$. Branching deletions have loss at most one except at the $w$ sets containing $x$ and just one control. Their mass is $\delta^2$ each and their exceptional loss is at most $2w+1$. Thus $M/d_b\le1+\delta(2w+1)^2<8$. The factor $2^{-w}(2w+1)^2$ attains its integer maximum at $w=2$, as seen by comparing consecutive terms. Equation (R1) gives **$P_2/I\le88$ for any depth and any sequence of widths**, even when the total probability of ever branching along the marked path is small.
* **Biased iterated and skewed Tribes.** For widths $(2,2)$ use the indicator of success. For $(1,3)$ complement all inputs and use the indicator of failure. At a common rare-bit probability $u$ the respective rare-event polynomials are $P=x_1x_2+x_3x_4-x_1x_2x_3x_4$ and $P=x_1[1-(1-x_2)(1-x_3)(1-x_4)]$. Starting at $u=1/2$, each update $P(u,\ldots,u)$ lies in $(0,u]$. In both cases $P(u)\le3u^2$ and $\partial_{12}P(u)\ge1/4$. The normalized active pair probability $[u(1-u)]^2(\partial_{12}P)^2/[P(u)(1-P(u))]$ is at least $1/192$. Hence $d_b\ge1/96$. The four singleton terms give $m_1\le4,\ m_2\le8$, using $\max_{0<v\le1}v\log_2^a(1/v)=(a/(e\ln2))^a$. Also $\log_2^2(1+r)\le3r$ since $\ln(1+r)\le\sqrt r$. Summing predecessor masses gives $M\le3\cdot4=12$. Formula (R1) therefore bounds the zero-odds part by $593664$. Positive root odds change only degree one. For any Boolean output, writing $a=|\widehat f(\{j\})|>0$ gives $a^2\ell_j^2\le a^2(1+2\log_2(1/a))^2\le36a$. The last bound follows from $(1+b)^2\le2+2b^2$ and $z^2e^{-z}\le2$ for $z\ge0$. Use $\sum a\le I$ to obtain **$P_2/I<594000$ at every depth** for these two biased towers. The coarse constant proves finiteness. The table records their observed scale. The script also checks the biased gate estimates at $u=2^{-w}$ through $w=128$.

### An exact limit for every fixed balanced gate

For a finite balanced gate $g$ with $I_g>1$, its iterated disjoint compositions $g^{\circ n}$ satisfy
$$
 \lim_{n\to\infty}\frac{P_2(g^{\circ n})}{I_g^n}
 =\lim_{n\to\infty}\frac{X(g^{\circ n})}{I_g^n}
 = m(g)^2 .
$$
The constant can be calculated from **one gate WHT**. With the notation of (R1), let $\theta=w_1/I_g$. Draw a geometric number $N$ of unary steps with $\Pr(N=a)=(1-\theta)\theta^a$. Each unary tag $j_l$ has probability $\pi_{\{j_l\}}/w_1$. Independently draw a branching incidence $(S,i)$ with probability $\pi_S/d_b$, $|S|\ge2$. Set $R=\pi_{S-i}/\pi_S$ and
$$ m(g)=\mathbb E\log_2\!\left(1+\frac{R}{\prod_{l=1}^N\pi_{\{j_l\}}}\right). $$
The empty product is one, which covers the case $w_1=0$. For a signed dictator set $m=0$. The truncated sum over $N<h$ equals $m_h=\mathbb E_p A(g^{\circ h})/I_g^h$ by the marked-leaf calculation. If $L$ is the largest branching loss and $Y$ the largest unary $y_j$ (use zero when absent), the omitted mean is at most $\theta^h[L+Y(h+\theta/(1-\theta))]$. The 32-step rational enclosures give **$11.10680911758109427\le m(g)^2\le11.10680911758109428$ for Numaro**. For the width-2 rare switch they give $[1.60528628245960889,1.60528628269120502]$. The finite-depth series also agrees with an independent two-level WHT. [Certified limiting series](scripts/max1_pool.py)

Here is why the limiting **second** moment equals the square of this first moment. Sample a nonempty spectral tree under its ordinary law. Write $K$ for its leaf count, and let the leaf-biased tree law assign density $K/I_g^n$ to this tree. Then $P_2/I_g^n$ is the second moment of $A/K$ under the leaf-biased law. Cut the tree $h$ levels above the leaves. Conditional on the upper tree with $J\ge1$ frontier vertices, the $J$ subtrees below it are independent copies of the depth-$h$ tree. Truncate their incoming odds to zero, and write $(A_j,K_j)$ for their loss and size. The centered variables $A_j-m_h K_j$ have mean zero. Since $K=\sum K_j\ge J$,
$$
 \mathbb E_{\rm leaf}\left(\frac{\sum_j A_j}{K}-m_h\right)^2
 \le \frac{\operatorname{Var}(A_1-m_h K_1)}{I_g^n}.
$$
Indeed, conditionally on $J$, the expected square of the centered sum is $J$ times the variance. With $h$ fixed, the displayed bound tends to zero. Restoring the incoming odds can change only leaves whose bottom $h$ marked steps were all unary. Jensen bounds the squared change in the empirical average by the incidence expectation of the squared change of a single leaf. This is at most $\sum_{a\ge h}(1-\theta)\theta^a(L+aY)^2$, uniformly in $n\ge h$. Let $n$ tend to infinity and then $h$ tend to infinity. The triangle inequality proves convergence in mean square to $m(g)$. Finally every loss in a depth-$n$ tree is at most $L+nY$, so $D/I_g^n\le (L+nY)^2/I_g^n\to0$. The direct diagonal recursion gives $D/I\in[0.000011,0.000012]$ at Numaro depth 20.

There is a distinction between the global question and this tower limit. **FEI is equivalent to uniform boundedness of these limiting second moments over balanced finite gates.** If FEI holds, $\mathbb E_p A\le\sum_i L_i\le H$ on every finite tower gives $m(g)\le C$. Conversely, a bound $m(g)\le B$ bounds $\mathbb E_p A(g)/I_g$ for every balanced gate, since the depth-one expectation is the first nonnegative term of its series. Given any sign function $f$, balance the product of $k$ independent copies by multiplying by an independent sign $z$. Its spectral sample always contains $z$, and all other blocks are independent ordinary samples of $f$. All original deletion odds persist and deletion of $z$ has odds zero. The influence is $1+kI(f)$ and the mean loss is $k\mathbb E_p A(f)$. Divide by $k$, pass to the limit, and apply the first-moment restriction argument above. This implication leaves the finite one-gate quantity $P_2(f)/I(f)$ free to be larger. [Product and balance checks](scripts/max1_boolean.py)

The spine estimate for a given gate cannot simply be maximized over all gates. For a balanced example take $z$ times the single-output bent lookup described next. Every term with a private label now has degree at least two, and its private deletion still has loss $\log_2(1+2^m)$. These terms have mass $1/2$, while $d_b\le 1+I(f)=m/2+2$. Thus $M/d_b\ge\log_2^2(1+2^m)/(m+4)$ diverges. Jensen before pooling the leaves discards needed information even within balanced gates.

### Several lookups sharing the same bent address

Fix even $m\ge2$, $N=2^m$, and $t\ge1$. All $t$ gates receive the same address $x$ and the same bent sign $h(x)=(-1)^{\sum_{j=1}^{m/2}x_jx_{j+m/2}}$. Gate $j$ reads $h(x)$ if its private switch is zero and its private table entry $y_{j,x}$ otherwise. Take the product of the $t$ outputs. In the expansion select a subset $U$ of tables. Its term is the switch pattern indicator times $h(x)^{t-|U|}\prod_{j\in U}y_{j,x}$. Each $U$ has mass $2^{-t}$. For $U\ne\varnothing$ all labels in a nonzero coefficient have the same address, and every address and switch frequency has magnitude $2^{-t}/N$ for that label tuple. At $U=\varnothing$ the coefficients on each switch frequency are $2^{-t}\widehat{h^t}$. The elementary two-bit transform of $(-1)^{x_1x_2}$ gives bent magnitudes $1/\sqrt N$ by tensoring. For even $t$, $h^t=1$.

Writing $a=2^{-t}$, the resulting entropy and influence are
$$ H=2t+2m(1-a)+ma\,\mathbf1_{t\ {\rm odd}},\qquad
 I=t+\tfrac m2(1-a\,\mathbf1_{t\ {\rm even}}). $$
In particular $H\le4I$. For $|U|\ge2$ every deletion has odds one. For $U=\varnothing$ every present bit also has odds one. When $|U|=1$, only the private-label deletion is exceptional. Its odds are $N$ for odd $t$, and for even $t$ they are $N^2$ at address frequency zero and zero elsewhere. The number $k$ of address and switch bits conditional on a singleton $U$ has law $\operatorname{Bin}(m+t,1/2)$. These cases yield the exact finite binomial sum in the script.

For a uniform bound put $L=2m+1$, an upper bound for the exceptional log loss. On a singleton $U$ the excess of $A^2/|S|$ over $|S|$ is at most $2L+L^2/(k+1)$. Here $\mathbb E[1/(k+1)]=2(1-2^{-(m+t+1)})/(m+t+1)$. Since $L\le2(m+t)$, $\Pr(|U|=1)=t2^{-t}\le1/2$, and $I\ge3(m+t)/8$, we obtain **$P_2/I\le17$ for every $m,t$**. For $m=64$, exact intervals at $t=2,3,8$ are $[.962112,.962113]$, $[3.600735,3.600736]$, $[.998454,.998455]$. The change with parity comes from the private-empty slice. Ordinary WHTs on the 12- and 17-bit truth tables ($m=2,\ t=2,3$) independently check $H$, $I$ and $P_2/I$. [Lookup calculation](scripts/max1_lookup.py)

### Dense edge and subcube packing without monotonicity

In a $k$-bit core, $k\ge2$, take any matching of cube edges covering fraction $\alpha$ of the vertices and put $d=k-1$. On each edge install a balanced gate $G$, reusing the free core bit and giving the gate a separate private block. Orientations and output signs can vary by edge. The distinguished singleton magnitude $t\in[0,1]$ is common. Give the exterior arbitrary signs of total zero. Let $C$ be the core mean after private averaging. It equals $\pm t$ with opposite signs at each matched pair and equals the exterior sign elsewhere. Let $b$ be the balanced Boolean completion obtained by replacing each oriented $\pm t$ with $\pm1$, retaining the chosen orientation when $t=0$. For a real core, use $H(C)=\sum\eta(\widehat C^2)$ and $I(C)=\sum|S|\widehat C(S)^2$.

The private-empty slice has spectrum $\widehat C$. Every nonempty-private coefficient of $G$ is copied with multiplier $2^{-d}$ onto $2^d$ characters. It gains mean degree $d/2$. The total mass of such coefficients in $G$ is $1-t^2$. Distinct edges have disjoint nonempty private frequency labels. Hence the glued function $F$ satisfies
$$
\begin{aligned}
 H(F)&=\alpha H(G)+H(C)-\alpha\eta(t^2)+2\alpha d(1-t^2),\\
 I(F)&=\alpha I(G)+I(C)-\alpha t^2+\tfrac{\alpha d}{2}(1-t^2).
\end{aligned}
$$

**Perfect matching.** Here $C=t b$. The exact identities reduce to
$$
 \begin{aligned}
 H(F)&=H(G)+t^2H(b)+2d(1-t^2),\\
 I(F)-1&=(I(G)-1)+t^2(I(b)-1)+\tfrac d2(1-t^2).
 \end{aligned}
$$
Thus if $G$ and $b$ both satisfy $H\le R(I-1)$, so does $F$ for $R\ge4$. Whenever denominators are positive, the score is a weighted average of the component scores and 4, with the excess-influence contributions as weights. This identity includes nonparallel matchings and arbitrary changes in arity between stages. It explains why operating at active fraction **one**, with no geometric damping, still cannot accumulate an excess beyond the component bound. For parallel edges the completion can be $b(s,x)=s\,g(x)$ with *any* Boolean $g$, giving $H(b)=H(g)$ and $I(b)-1=I(g)$. Proving a uniform component bound just from the geometry of that matching would already settle FEI.

**Near-perfect matching.** The same inheritance holds with $R\ge6$ when $\alpha\ge255/256$. To see this, put $\beta=1-\alpha$. Across every hard-sign change of $b$ the magnitudes in $C$ differ in signed value by at least $2t$. Each matched edge accounts for exactly $t^2$ times its hard-sign energy. By the edge form of the real Dirichlet energy,
$$ I(F)-1\ge\alpha(I(G)-1)+t^2(I(b)-1)+(1-t^2)(\alpha d/2-\beta). $$
For the entropy, the map $a\mapsto\sum_j\eta(a_j^2)$ is $2(k+4)$-Lipschitz on the real Euclidean unit ball of dimension $2^k$. Indeed its gradient has entries $2a_j(\log_2(1/a_j^2)-\log_2 e)$ with limit zero at $a_j=0$. Under the subprobability masses $p_j=a_j^2$, the tail mass of $(\log_2(1/p_j)-k)_+$ at $s>0$ is at most $2^{-s}$ by counting entries. Its $L^2(p)$ norm is at most $\sqrt2\log_2 e$. The triangle inequality gives the claimed gradient norm since $(1+\sqrt2)\log_2 e<4$. Apply this bound in Walsh coordinates using $\|C-tb\|_2=(1-t)\sqrt\beta$ in uniform probability normalization. With $\eta(t^2)\le(1-t^2)\log_2 e$ this gives
$$ H(F)\le\alpha H(G)+t^2H(b)+(1-t^2)\,[2\alpha d+\beta\log_2 e+2\sqrt\beta(k+4)]. $$
For $\beta\le1/256$, $k+4\le6d$ and the bracket is at most $2\alpha d+2\beta+3d/4\le6(\alpha d/2-\beta)$. This proves inheritance at the same $R$ through an arbitrary number of sufficiently dense stages, even as $t$ approaches one. The optimal density threshold remains open here.

For a partition by general subcubes $j$ of codimension $c_j$ and mass $w_j=2^{-c_j}$, allow each gate $G_j$ to reuse **all** free coordinates of its cell. Put $h_j=\mathbb E_{\rm private} G_j$ on that face, glue these means to form $C$, and put $Q=\sum_j w_j c_j(1-\|h_j\|_2^2)$. The same coefficient count gives
$$
\begin{aligned}
 H(F)&=H(C)+\sum_j w_j[H(G_j)-H(h_j)]+2Q,\\
 I(F)&=I(C)+\sum_j w_j[I(G_j)-I(h_j)]+Q/2 .
\end{aligned}
$$
These identities isolate the residual core term for mixed codimension. Private frequency collisions between different cells would invalidate the coefficient count. Related work treats selector identities and orthogonal multiplexers with shared data. [Shmalo, §8](https://arxiv.org/html/2610.16069v1)

Nine ordinary WHT comparisons covered small partial and perfect matchings, including edge-count influence. Eight mixed-codimension partitions with random gates were checked against their entire magnitude/degree histograms. The edge search scored 960 instances from dimensions 3–10 with even-parity coset induced matchings, scrambled quarter and half matchings, matchings missing one edge, and perfect matchings. It used both singleton types of the published seed and a rare switch. The highest screened $H/(I-1)$ for the three gates had certified intervals $[6.217295300,6.217295301]$, $[6.265906411,6.265906412]$ and $[4.343117667,4.343117668]$. A separate search tested 720 stages of self-dual circuits that switch to permuted copies of the **same** state on affine cosets and apply a nonlinear sign on the selected branch. The highest screened ordinary and amplified scores lay in $[2.149505948,2.149505949]$ and $[4.536634068,4.536634069]$. All screening spectra used integer WHTs, with floating entropy for ranking and rational interval certification of the finalists. These are search results, with no claim of exhaustive optimization. [Packing experiments](scripts/max1_packing.py) · [Shared-data circuits](scripts/max1_lookup.py)

### Single target for MAX Round 2

**Bound the mean deletion loss conditional on a branching incidence of one balanced gate, or construct gates for which it diverges.** Explicitly, for $g$ balanced with $d_b>0$ the target is
$$
 B(g)=\frac{\sum_{|S|\ge2}p_S\sum_{i\in S}\log_2(1+p_{S-i}/p_S)}
             {\sum_{|S|\ge2}|S|p_S}\ \le K .
$$
This target is **equivalent to the frozen FEI conjecture**. For the geometric formula above,
$$ B(g)\le m(g)\le B(g)+m_1/d_b\le B(g)+2/\ln2 . $$
The first inequality uses $\prod\pi_{\{j_l\}}\le1$. For the second, removing the product from inside the logarithm costs at most the sum of the unary $y_j$'s, of mean $m_1/d_b$. In fact the optimal constants in three versions agree. Let $S_*=\sup_{f:I>0}\mathbb E_p A(f)/I(f)$. The signed product construction gives the same supremum when restricted to balanced gates. On such gates $\mathbb E_p A/I\le B(g)\le m(g)$, and $m(g)$ itself is a limit of first-moment ratios of balanced gates. Consequently $S_*=\sup_g B(g)=\sup_g m(g)$, allowing infinity. For $C_*=\sup_{f:I>0}H(f)/I(f)$ the entropy and restriction bounds above give $S_*\le C_*\le S_*+3\log_2 e$. A sequence with $B(g)\to\infty$ yields ordinary FEI counterexamples by taking sufficiently deep finite towers, since $H/I\ge\mathbb E_p A/I\to m(g)$ along each tower.

The objective can be optimized on a single balanced truth table. All $\binom{16}{8}=12{,}870$ balanced four-bit tables give a certified maximum in $[1.234836598539,1.234836598540]$, using outward integer lookup tables for each neighboring coefficient pair. The best of 24 balanced-swap runs across 6, 8 and 10 bits gave $[1.6626249532,1.6626249533]$. These runs screened 49,920 candidate swaps with integer WHT updates, then verified the finalist with rational logarithm bounds. Numaro gives $B(g)\in[2.229077005129,2.229077005130]$. Its depth-20 tower gives $[3.332687971824671,3.332687971824672]$ because the singleton mass at depth $d$ is $w_1^d$. Its computed limit forces $S_*\ge3.3326879718301103$. [Branching-loss search and extremal tower check](scripts/max1_branch_search.py)

One possible way to prove the target is the global mixed bound $X\le K'I$ above. It is sufficient and its finite-dimensional formulation is stronger than the necessary tower-limit condition. The depth-20 computation already requires $K'\ge11.104850$. On a fixed two-coordinate face, write $f=a+s b+t c+st d$. The Boolean equations give $ad+bc=ab+cd=ac+bd=0$ and $a^2+b^2+c^2+d^2=1$ pointwise on the remaining cube. They supply joint signed convolution identities after Walsh transformation. Turning them into a budget for simultaneous large neighboring odds, or directly into a first-moment budget for $B(g)$, is the missing inference.

A specific tempting strengthening fails. In the single-output bent lookup above, take one private-label coordinate $i$ and an address coordinate $j$. On **every** positive-mass set containing both, $\ell_i=\log_2(1+2^m)$ and $\ell_j=1$. Therefore the pair's contribution divided by $\sum_{S\supseteq\{i,j\}}p_S/|S|$ is *exactly* $\log_2(1+2^m)$. The denominator is positive. Full WHTs give $[2.32192809,2.32192810]$ and $[4.08746284,4.08746285]$ at $m=2,4$. A pairwise charge proportional to its own incidence weight cannot work. A successful charge has to draw on other pairs or on a global Boolean identity. The stronger second-moment target could still fail on functions satisfying ordinary FEI. [Pair obstruction and Boolean identities](scripts/max1_boolean.py)

### Round 1 reproduction and formalization

From the repository root, run the six new Python programs and the default Lean build.

```sh
python3 -B scripts/max1_pool.py
python3 -B scripts/max1_spinal_seed.py
python3 -B scripts/max1_packing.py
python3 -B scripts/max1_lookup.py
python3 -B scripts/max1_boolean.py
python3 -B scripts/max1_branch_search.py
lake build
```

The Boolean verifier checks the new degree-sensitive estimate with integer fourth-root enclosures, the two-coordinate equations, the separated diagonal and mixed contributions, and block restrictions. Its test set includes all 256 three-bit functions and eight structured tables covering the Numaro seed, biased composed Tribes, a one-point Tribes perturbation, a multi-output lookup, a rare switch and three nonlinear shared-data circuits.

Five new Lean theorems prove the Boolean mean/derivative identities, the four two-coordinate face equations, the pooled Cauchy–Schwarz inequality for the actual frozen spectrum, the numerical closure of the mixed-loss estimate, and score inheritance given the two perfect-matching identities. The default Lean 4.36.0 build succeeded with zero errors and zero warnings. The hypercontractive estimate, tower limit, gluing arguments and numerical witness are proved or certified in the mathematics and Python above. Their end-to-end formalization remains open. The frozen file's SHA-256 is also recorded in §8. [ResearchLemmas.lean](FEI/ResearchLemmas.lean)

## Previous xhigh investigation · archived results

**Case C · 25 November 2026.** Every constant satisfying the frozen FEI inequality must obey

$$
\boxed{C>6.521850225089574148.}
$$

This lower bound comes from an explicit sequence of balanced monotone Boolean functions. Its gain over the published 18-variable construction is approximately $4.51417\times10^{-6}$. A single 162-variable seed already gives $C>6.521850083658612443$ by balanced composition. The sequence has a finite limiting score. A universal upper bound and a family with divergent $H/I$ both remain open in this investigation. [Published certificate and prior bound](https://numaro.tech/research/fourier-entropy-influence-2026/) · [Constant registry](https://teorth.github.io/optimizationproblems/constants/71a.html) · [Local exact verifier](scripts/certificate.py)

Two barriers emerged separately. On a balanced monotone function on $18^8$ bits, **every** one-coordinate restriction has entropy drop greater than $7.1114920488$ times the coordinate's influence. On an explicit bent-function/address family, the logarithmic loss of deleting one spectral variable has unbounded normalized moment of every order strictly greater than one, even though $H/I\to3$. The first result constrains the constant in a proof by induction. The second constrains attempts to prove that induction by a stronger moment inequality.

## 1. Normalization and benchmark

Write $a_S=2^{-n}\sum_x f(x)(-1)^{\langle S,x\rangle}$, $p_S=a_S^2$, $\eta(u)=u\log_2(1/u)$, and $\eta(0)=0$. Use $H=\sum_S\eta(p_S)$, $I=\sum_S |S|p_S$, $I_i=\sum_{S\ni i}p_S$. Bit 1 has sign $-1$. Parseval and agreement with edge-count influence already have Lean proofs. [Frozen statement](FEI/Challenge.lean) · [Existing normalization proofs](FEI/ChallengeSanity.lean)

Numaro's 18-bit seed $g$ has $I_0=261/128$, $H_0=6.77660530900597808\ldots$, and **ordinary** $H_0/I_0=3.3233926419646176\ldots$. Its **amplified** score is $H_0/(I_0-1)=6.52184571092304657565\ldots$. The reported $6.5218$ applies via iteration. Rounding the certified lower bound up to $6.53$ would exclude constants without justification. The separate min-entropy benchmark $128/45$ concerns a 30-bit example. Integer WHTs of its 5- and 6-bit factors give largest composed mass $1/4096$ and $I=135/32$, hence $12/(135/32)=128/45$. [Numaro](https://doi.org/10.5281/zenodo.21497769) · [Independent replay and pinned source](https://github.com/teorth/optimizationproblems/pull/216) · [Biswas–Sarkar, equations 13 and 15](https://eccc.weizmann.ac.il/report/2022/180/download/)

**Amplification.** For a balanced sign function $g$ on disjoint blocks, sampling the spectrum of $f\circ(g,\ldots,g)$ first samples $S\sim p_f$, then independently samples $U_i\sim p_g$ in each block $i\in S$. Indeed the product expansion gives exactly those coefficients. Balance forces each $U_i$ to be nonempty, so the union uniquely specifies $S$ and all $U_i$. Entropy and expected cardinality are therefore $H_f+I_fH_g$ and $I_fI_g$. For a balanced seed of entropy $h$ and influence $a>1$, depth $d$ self-composition has
$$
I_d=a^d,\qquad H_d/I_d=\frac{h}{a-1}(1-a^{-d}).
$$
Thus every universal constant bounds $h/(a-1)$, including for monotone seeds if the domain of the conjecture is restricted to monotone functions. We use this argument only after constructing each balanced seed. [O'Donnell–Tan](https://arxiv.org/abs/1304.1347) · [Hod](https://arxiv.org/abs/1711.00762)

## 2. A shared-variable construction improving the lower bound

### The function

Identify the first nine bits with a little-endian integer $x\in[0,511]$. At most core inputs, $g$ is constant in its other nine bits. At the following nine edges $(u_j,v_j)$, it equals the sign of a private bit $y_j$ at both endpoints, in the order shown.

```text
(78,79)   (113,121)  (228,484)  (170,186)  (149,151)
(338,466) (284,316)  (291,295)  (393,457)
```

The constant signs off the edges are encoded by `BASE` in [walsh.py](scripts/walsh.py). Equivalently take the published table with all $y_j=0$. Reconstructing all $2^{18}$ signs gives the published comma-separated-table SHA-256 `f8a7bb2c738d86368305111633376b1a3a83d8ee1f1abcc9a37d841b0f9c7839`. Balance and monotonicity are checked on the entire table. [Original construction](https://github.com/teorth/optimizationproblems/pull/130)

Each pair varies in exactly one core bit, denoted $s_j$. At $u_j$ its bit value is zero. Let $G(s,z)$ be any balanced monotone sign gate with one distinguished bit. Define $B_m(G)$, for $m=8,9$, by replacing the selectors on the **last** $m$ edges. When $x\in\{u_j,v_j\}$ on a replaced edge, output $G(s_j,z_j)$. The $z_j$ blocks are private and mutually disjoint, and $s_j$ is the existing core bit. On every other input use the old output. Take $G=g$ initially, distinguishing bit 9 in zero-based indexing, the first private selector.

Every replaced edge has probability $r=1/256$ because its eight fixed bits select it independently of the free bit. Consequently replacement preserves the mean zero. For monotonicity within an edge use monotonicity of $G$. Two adjacent core inputs on distinct active edges would violate monotonicity of the original table for some independent selector settings, so there are no such adjacencies. At an active-to-constant adjacency, the constant has the required order for either sign. Private coordinates inherit monotonicity from their gate. These facts apply at every depth.

### Why sharing a bit changes the score

Let $t=\widehat G(\{s\})$. The two conditional means of $G$ are $t,-t$. Average the new function over all private inputs and denote its 512-entry real core by $c$. On each replaced edge this puts $t,-t$ at the two endpoints. On a retained edge the average is zero. Put $H_c=\sum_A\eta(\widehat c(A)^2)$. The core alone can have mass less than one.

For a nonempty private frequency $U$ in a replaced block, the allowed coefficients come from multiplying its gate term by the indicator of the eight fixed address bits. For each $b\in\{0,1\}$ the gate coefficient indexed by $U$ and free-bit exponent $b$ produces $2^8$ coefficients of absolute value $r|\widehat G(b,U)|$. The free-bit exponent distinguishes the two lists. Distinct private blocks have disjoint nonempty frequencies. Any coefficient involving private frequencies from two blocks vanishes. Only the all-private-empty slice can interfere, and it is precisely $\widehat c$. The nonempty-private mass inside $G$ is $1-t^2$. Summing $\eta$ gives
$$
 H(B_m(G))=H_c+(9-m)\,16r+
 mr\big[H(G)-\eta(t^2)+16(1-t^2)\big]. \tag{1}
$$
The $16$ is $2\log_2(1/r)$. In particular the entropy increment from modifying $t$ can have either sign. This interference term accounts for the improvement.

For a monotone Boolean sign function, each singleton coefficient equals the corresponding influence, by conditioning on the other bits. On one replacement the sum of core singleton coefficients gains $rt$, entirely in the free coordinate. New private singleton coefficients sum to $r(I(G)-t)$. The old selector contributed $r$. Thus independently of $t$,
$$
 I(B_m(G))=I_0+mr\,(I(G)-1). \tag{2}
$$
The verifier also computes this influence from the full degree-weighted spectral histogram.

### Exact numerical certificate and limiting argument

| Balanced seed | Arity | Nonzero Walsh coefficients | Exact $I$ | $H/(I-1)$, truncated |
|---|---:|---:|---:|---:|
| Published $g$ | 18 | 2,770 | $261/128$ | 6.521845710923046575 |
| $B_8(g)$ | 146 | 5,671,658 | $8485/4096$ | 6.521849759686848433 |
| $B_9(g)$ | 162 | 6,380,242 | $68013/32768$ | 6.521850083658612443 |
| $B_9(B_8(g))$ | 1,314 | evaluated by (1) | $2177613/1048576$ | 6.521850220674542359 |

To improve the finite bound, put $G_0=g,\ G_{k+1}=B_8(G_k)$, distinguishing the first, retained selector of each $G_k$. Its singleton coefficient is **exactly $r$** for every $k$ because the gate reads this bit on its original two cells and ignores it elsewhere. Let $X$ denote either $H$ or $I$. In (1) the core and $t$ are now fixed for each $m$, and (2) has the same slope. Hence
$$
 X(B_m(G_k))=X(B_m(g))+mr[X(G_k)-X(g)].
$$
The difference $X(G_k)-X(g)$ is $[X(B_8(g))-X(g)]\sum_{j=0}^{k-1}(8r)^j$. For the explicit sequence $B_9(G_k)$ this gives
$$
 X_* = X(B_9(g))+\frac{9r}{1-8r}[X(B_8(g))-X(g)].
$$
In particular $I_*=65925/31744$, and rational intervals give
$$
 7.022535362392475238 < H_* < 7.022535362392475239,\qquad
 6.521850225089574148 < H_* /(I_*-1) < 6.521850225089574149.
$$
Apply the disjoint amplification argument to **each finite** $B_9(G_k)$ and then pass to this limit. A single finite witness also clears the displayed floor. Take the depth-72 disjoint self-composition of $B_9(G_{12})$. Its arity is $11{,}309{,}262{,}457{,}122^{72}$. Its **ordinary** $H/I$ lies between $6.52185022508957414827$ and $6.52185022508957414828$, using rational bounds and the exact finite-depth formula. This yields the stated lower bound, and the factor $8r=1/32$ explains why extending this particular recursion cannot make the ratio diverge.

**Verification method.** [certificate.py](scripts/certificate.py) reconstructs the private-empty slice by integer WHT. For each possible nonzero private-frequency type it independently transforms a core vector with just the two conditional branch coefficients at the two endpoints. It counts coefficients by magnitude and degree, verifies integer Parseval and checks (2). This is an exact factored WHT of the 146- and 162-bit functions. The full truth tables of those functions are unnecessary. As cross-checks it compares the entire histogram with an ordinary 18-bit WHT and with an ordinary 19-bit WHT using a three-input majority replacement. These checks include influence by counting edges on the dense cubes. A second calculation propagates the full magnitude/degree histogram through all twelve inner substitutions and the final outer substitution. Fixing eight address bits copies a private term of degree $d$ to degrees $d+j$ with multiplicities $\binom8j$. This calculation recovers the finite witness bound directly from 19,011 histogram bins, independently of the affine entropy recurrence.

The only transcendental operation in the numerical certificate is $\log_2$. To bound $\ln x$ on $[1,2]$, set $z=(x-1)/(x+1)$, use the first 40 terms of $2\sum_{j\ge0}z^{2j+1}/(2j+1)$, and bound the omitted sum by $2z^{81}/(81(1-z^2))$. Mantissa reduction and division by an enclosure for $\ln 2$ give rational intervals for every log. All bounds use `Fraction` arithmetic with outward rounding to dyadics. The final comparison with the previous interval and the strict decimal floor are rational tests. This is a local, reproducible computer-assisted result. Independent external review and an end-to-end Lean proof of the numerical record are outstanding.

## 3. Coordinate restriction and adaptive induction

At a fixed coordinate $i$, let $u=a_S,v=a_{S+i}$ for $i\notin S$. The two child coefficients are $u+v,u-v$. If $P_+,P_-$ are their spectral laws, their mean $M$ has masses $u^2+v^2$. For a spectral sample $X\sim p$, define $L_i=H(1_{i\in X}\mid X\setminus\{i\})$. With $J_i=H(M)-[H(P_+)+H(P_-)]/2$, the entropy and influence drops are exactly
$$
 \Delta_i=L_i+J_i,\qquad
 I-\tfrac12(I_++I_-)=I_i=\sum_S v^2=\tfrac14\|f_+-f_-\|_2^2.
$$
These follow by entropy chain rule and edge averaging, respectively. In particular $0\le L_i\le h_2(I_i)$.

The mixing term has a linear bound. Within a pair of mass $M_S>0$ the contribution to $J_i$ is $M_S[1-h_2((1+z)/2)]$, $z=2uv/M_S$. The Taylor series of the bracket in even powers of $z$ has nonnegative coefficients summing to one at $z=1$, so it is at most $z^2$ on $[-1,1]$. Consequently $J_i\le4\sum_S u^2v^2/(u^2+v^2)\le4I_i$. The sharp constant $2/\ln 2$ and the equivalence of FEI to $\sum_i L_i=O(I)$ are given by Shmalo. For the latter equivalence, $\sum_i L_i\le H$ follows by the chain rule and conditioning. Conversely the summed bound yields a relevant coordinate with bounded $L_i/I_i$, and induction uses the two drop identities above. Thus the uncontrolled cost resides in conditional spectral entropy. [Shmalo, one-coordinate step](https://doi.org/10.5281/zenodo.24126590) · [González–MacManus–Pereyra](https://arxiv.org/abs/2606.00246)

### An explicit monotone obstruction for a prescribed coordinate

Take $k$ disjoint width-$w$ ANDs, $w\ge2$, with OR as the top gate. Write $T$ for its sign table on $n=wk$ bits and $y$ for the point with exactly the first block set to 1. Form $F(x,b)$ with $F(x,1)=T(x)$ and $F(x,0)=T(x)$ except that it is logically false at $y$. Removing this minimal true point preserves monotonicity. The two branches differ at one point, hence $I_b=2^{-n}$, and $|v_S|=2^{-n}$ at **every** base frequency $S$.

For nonempty $S$, let $j(S)$ count blocks it misses. The product of the indicators that each tribe fails gives
$$
 |\widehat T(S)|=2^{1-n}(2^w-1)^{j(S)}.
$$
Indeed an untouched block has coefficient $1-2^{-w}$, and every nonempty character of a failure indicator has magnitude $2^{-w}$. Since $u_S$ differs from $\widehat T(S)$ by $\pm2^{-n}$, $|u_S/v_S|\ge(2^w-1)^{j(S)}$. Keeping the $v_S^2$ term of binary conditional entropy yields
$$
 \frac{\Delta_b}{I_b}\ \ge\ \frac{L_b}{I_b}
 \ \ge\ 2k(2^{-w}-2^{-n})\log_2(2^w-1).
$$
Here $2^{-n}\sum_{S\ne\varnothing}j(S)=k(2^{-w}-2^{-n})$. At fixed width the bound diverges. For $w=2,k=9$, the WHT gives $I_b=2^{-18}$, $L_b/I_b=10.5625361$, $\Delta_b/I_b=13.40326964$, and ordinary $H/I=4.44034174$. This calculation addresses the actual entropy increment for the one-point perturbation. A large total-variation distance divided by influence alone would not imply it. The underlying $\delta$-Tribes construction is from González–MacManus–Pereyra. Other monotone bad-coordinate families are already known. [Section 5 of the $\delta$-Tribes paper](https://arxiv.org/html/2606.00246v1) · [Shmalo, hidden coordinates](https://aixiv.online/abs/2611.01296)

### A lower bound even when the coordinate is chosen optimally

Use a depth-$d$ disjoint tower of the published seed $g$. A leaf specifies one gate input at each level along its path. At the bottom start with a restricted dictator of means $+1,-1$, entropy drop zero and influence one. Suppose the restricted distinguished child now has means $\pm\mu$ and average entropy drop $\delta$. Monotonicity and balance make $\mu$ its chosen leaf influence. Write $a_S,b_S$ for the outer coefficients excluding/including its input $j$, and $\alpha=I_j(g)$. The new influence and positive conditional-mean magnitude equal $\alpha\mu$. The new entropy drop is
$$
 \delta'=\alpha\delta+
 \sum_S\left[\eta(a_S^2)+\eta(\mu^2 b_S^2)-
 \tfrac12\eta((a_S+\mu b_S)^2)-\tfrac12\eta((a_S-\mu b_S)^2)\right]. \tag{3}
$$
To derive this, in the special block the empty frequency has coefficient $a_S\pm\mu b_S$. Each nonempty private frequency has coefficient $b_S$ times its child coefficient. Applying the product entropy identity gives the displayed correction. The other active blocks contribute their entropies times their activation probabilities. Averaging the two restrictions cancels the $2a_S b_S\mu$ cross terms, so these contributions cancel in the drop. This derivation also works starting with the constant restricted leaves.

The integer WHT finds exactly two types of histograms $(|a_S|,|b_S|)$ on $b_S\ne0$, verified separately at all 18 coordinates. Their $\alpha$'s are $57/256$ and $1/256$. Therefore all $18^4=104{,}976$ coordinates are covered by $2^4$ paths of types. Applying (3) with rational log intervals proves
$$
 7.051852835007
 <\min_i\Delta_i/I_i
 <7.051852835008.
$$
The same calculation over all $2^8$ path types at depth eight encloses the minimum in $[7.111492048889,\ 7.111492048890]$. This obstruction persists at every greater depth. In (3) each summand is nonnegative. For $w=\mu b_S$, insert $\eta(a_S^2+w^2)$ between the first and second pairs of terms. One difference is a mass times a binary entropy and the other is nonnegative by concavity of $\eta$. Dividing (3) by $\alpha\mu$ therefore shows that adding a level never decreases the leaf ratio. An adaptive choice at the root cannot justify a one-step bound with constant 7.11. This leaves room for a larger universal constant or amortization across steps. It gives no lower bound of 7 for FEI itself.

As a stress test at genuinely high **ordinary** ratio, the depth-20 tower has $H/I=6.52184148657428\ldots$. Evaluating (3) from exact WHT factors gives $\Delta_i/I_i$ of approximately $7.1117428890,\ 8.4814596388,\ 7.3395224177$ along all-strong, all-weak and alternating paths respectively. These are selected paths, evaluated at 160-digit decimal precision. The depth-four and depth-eight minima use exhaustive path types and rigorous intervals. A direct 16-bit WHT validates (3) at all leaves of a smaller nonsymmetric balanced tower. [Tower verifier](scripts/towers.py)

## 4. Deletion loss and a counterexample to higher-moment proofs

For $i\in S$ with $p_S>0$, set $\ell_i(S)=\log_2(1+p_{S-i}/p_S)$ and $A(S)=\sum_{i\in S}\ell_i(S)$. Use zero contributions for zero-mass sets. Expanding the two sides of each binary conditional entropy gives
$$
 \mathbb E_p A(S)\ \le\ \sum_i L_i
 \le\ \mathbb E_p A(S)+(\log_2 e)I .
$$
For the upper bound use $p_T\log_2(1+p_{T+i}/p_T)\le(\log_2 e)p_{T+i}$ on the side where the bit is absent. For a nonconstant function, under the probability measure assigning mass $p_S/I$ to each incidence $(S,i)$, $i\in S$, FEI is equivalent to bounded mean deletion loss.

**A family defeating even a slightly stronger moment.** For even $m\ge2$, set $N=2^m$, let $x$ be an $m$-bit address, $y_0,\ldots,y_{N-1}$ be independent sign bits and $b$ one switch bit. For $b=0$ output the quadratic bent sign $(-1)^{x_L\cdot x_R}$. For $b=1$ output $y_x$. The transform of the bent sign has constant magnitude $1/\sqrt N$, by summing first over $x_R$. The core-only slice thus has $2N$ masses $1/(4N)$. For each $y_j$, its coefficient is the transform of the indicator $1_{\{b=1,x=j\}}$, giving $2N$ masses $1/(4N^2)$. These disjoint groups exhaust Parseval. In each group the $m+1$ switch/address frequencies are uniform. Consequently
$$
 H=\tfrac32m+2,\qquad I=\tfrac12m+1 .
$$
Deleting the private label of a term in the second group has odds $N$, and these terms have total mass $1/2$. Thus for every fixed $\theta,\epsilon>0$
$$
 \frac1I\sum_{S,i\in S}p_S(p_{S-i}/p_S)^\theta
 \ \ge\ \frac{2^{\theta m}}{m+2},\qquad
 \frac1I\sum_{S,i\in S}p_S\ell_i(S)^{1+\epsilon}
 \ \ge\ \frac{[\log_2(1+2^m)]^{1+\epsilon}}{m+2}.
$$
Both diverge. In particular an exponential-tail estimate for individual incidence losses fails, and even a uniform integrable envelope for their tails is impossible. Choosing even $m$ just above threshold $t$ gives tail probability at least $1/(m+2)$. Individual distributions can still have bounded mean. Dense WHTs at $m=2,4$ (7 and 21 variables) reproduce the analytic entropy, influence and moment formulas. For $m=64$, evaluation of the exact groups gives quarter-power moment divided by $I$ about $993.95$, with $H/I=2.9697$. [Deletion experiments](scripts/deletion.py)

## 5. Noise flow, localization and certificates

* **Normalized noise.** Put $q_t(S)=p_S e^{-2t|S|}/Z_t$, $D=|S|$. Differentiation on the support gives $H'(q_t)=2\operatorname{Cov}_{q_t}(D,\log_2 q_t)$ (derivative with respect to $t$), and $(\mathbb E_{q_t}D)'=-2\operatorname{Var}_{q_t}D$. Odd majority is balanced with equal nonzero singleton coefficients. As $t\to\infty$, $q_t$ tends to uniform on its $n$ singletons, so $H(q_t)/\mathbb E_{q_t}D\to\log_2 n$. A uniform FEI estimate along the whole normalized path fails already for this monotone family. Entropy can even increase initially. Flipping one truth-table entry of full parity on three bits gives mass $9/16$ at degree three and $1/16$ at each other set. The covariance identity gives a positive initial slope $(27/32)\log_2 9$, although the limiting entropy is zero. We checked both derivatives against central differences and the majority limit against WHTs through 19 bits.
* **Information lost by level tilting.** Tilting preserves the conditional distribution within each level. Parity on two bits and the four-bit Boolean sign $[a(b+c)+d(b-c)]/2$ are both homogeneous of degree two. Their entropies are respectively 0 and 2 for every normalized tilt, as verified by WHT. For the unnormalized flow $m_t=p e^{-2tD}$, $\sum\eta(m_t)=Z_t H(q_t)+\eta(Z_t)$. Controlling the scalar mass or its derivatives leaves within-level entropy undetermined. A successful interpolation must supply information beyond level masses.
* **Pathwise localization.** In the orthonormal basis for a product measure where one sign bit has mean $u$, the dictator has squared coefficients $u^2,1-u^2$. Its entropy divided by expected degree equals $h_2(1-u^2)/(1-u^2)$, unbounded as $u\to1$. The WHT of the uniform dictator and its exact biased basis expansion give $4.3974,8.4399,12.4425$ for $u=1-2^{-k}$, $k=4,8,12$. Thus a pointwise bound along localization in this normalization fails. There is a drift obstruction at the uniform starting point as well. Splitting the bit mean from zero to $+\varepsilon$ or $-\varepsilon$ with equal probabilities gains $h_2(\varepsilon^2)$ in expected spectral entropy for quadratic variation $\varepsilon^2$. Their ratio diverges. The WHT-based one-bit test checks both regimes. An integrated drift estimate would need to account for this initial gain. We obtained no such estimate from the Eldan–Gross process. [Eldan–Gross](https://arxiv.org/abs/1909.12067)
* **Fractional certificates and tails.** Turturean proves $\max_i I_i\ge c\,\operatorname{Var}(f)^{5/2}/d^6$ for bounded degree-$d$ polynomials. Combined with $L_i\le h_2(I_i)$, this still leaves a cost per unit influence logarithmic in the inverse guaranteed influence. The first-moment tail bound $d\,\Pr_p(|S|\ge d)\le I$ controls mass only. For example, the degree-one projection of majority on three bits takes value $3/2$ at the all-positive input. As a second test, the minimum fractional certificate cost at an input to AND is $n$ on its sole true point and 1 elsewhere. On the true input each singleton flip forces unit weight. On a false input one zero bit suffices and the opposite output forces total weight at least one. Its average divided by $I=n2^{1-n}$ reaches $2048.46875$ at $n=16$ and diverges. This rules out charging that entire average budget to influence. The all-pairs bijection theorem gives no immediate charge for the magnitude ratio of two adjacent Walsh coefficients. [Turturean's theorem](https://arxiv.org/abs/2611.09773) · [Author's formalization](https://github.com/physical-superintelligence/aaronson-ambainis)

## 6. Search coverage

Dense Boolean spectra are computed from truth tables by integer butterfly transforms. Coefficients have denominator $2^n$. Squared weights and edge counts are dyadic. Exploratory entropy and scores use float64 unless an interval or other precision is specified. The finite maxima below are rounded. Dense test sizes stay within the integer accumulator bounds. For huge functions, the stated factorization specifies which transforms were actually run.

| Search | Outcome |
|---|---|
| All sign tables on 1, 2, 3, 4 bits | Maximum ordinary $H/I$ at $n=4$ was 3.40247555. Maximum over functions of best relevant $\Delta_i/I_i$ was 4.86766875, worst relevant split 5.92178378. Constant tables were checked and excluded from ratios. |
| Disjoint, skewed, iterated Tribes and threshold gates | Eight width-two tribes gave ordinary 4.32959787 and split ratio 6.0037461. A two-level tribes example gave 3.68415331. The 9-bit recursive majority had $H=5,\ I=9/4$. |
| Bent perturbations and sparse masks | Selecting a bent sign or its one-point flip on a 16-bit base gave worst split 20.3280154 with ordinary ratio 1.99996292. Restricting a quadratic to parity-check subspaces and returning a constant elsewhere gave ratios 1.8923–2.1321 in the 14-bit trials. |
| Address and shared-pointer tables | Ordinary 3-address-bit lookup gave 2.4. Parity of adjacent data bits gave 1.71428571. One to six traversals of a reused four-entry pointer table on 14 inputs gave 2.54545–2.63369 at the tested hop counts. |
| Replace two constant core cells by fresh selectors | All $247^2=61{,}009$ balanced pairs. Best amplified score 6.47202624, below the parent. |
| Controlled transposition of two inputs to the published seed | All 153 transpositions. Best amplified score 6.50490996, verified against a dense 19-bit WHT. |
| One shared variable between two seed copies | 136 targeted replacements, testing two outer positions, every other shared outer bit, two inner positions and two orientations. 40 balanced, 96 biased. Best balanced score 6.52184636334. For 18 independent small checks the signed coefficient/degree histogram agreed with a full WHT. |
| Nine simultaneous edge replacements | Two $3^9$ grids, allowing default, shared input, or inverted shared input at each edge, for a weak or strong inner coordinate. The weak grid chose nine positive copies. The strong grid retained the default. Oppositely biased pairs of restricted gates on all 72 ordered host pairs per scale gave at most 6.52178858. Majority inner gates of odd arity 3–15 scored below the seed. |
| Random shared-variable gates and hill climbing | 256 twenty-gate circuits for each $n=6,8,10,12$. Largest sampled ordinary ratio 3.73976402. Single-flip greedy searches for either ordinary ratio or pooled loss used six random starts and 120 moves per objective and dimension $n=6,8,10$. The gates built from the published seed were more productive. |

The deterministic searches probe specified constructions. Search maxima give no universal upper bound. The preprint landscape also includes new special-class results, e.g. a claimed uniform bound for all linear thresholds. None of the arguments here assumes a universal constant for arbitrary decision trees or imports the Aaronson–Ambainis conclusion as FEI. [Threshold-function preprint](https://arxiv.org/abs/2610.16069) · [Decision-tree results](https://www.cs.cmu.edu/~odonnell/papers/fei.pdf)

## 7. Two targets for an Astra max run

1. **Test pooling over the elements of a set before taking a second moment.** One falsifiable strengthening is
   $$
      P_2(f):=\sum_{S\ne\varnothing}p_S\,A(S)^2/|S|\ \le\ K I(f).
   $$

   Cauchy–Schwarz would give $\mathbb E_p A(S)\le\sqrt{I P_2}$. Section 3 would then prove FEI with $C\le\sqrt K+\log_2 e+4$. In the bent lookup, averaging first spreads the loss of one private-label deletion over a set typically containing about $m/2$ address bits. Here $P_2/I$ was 2.55046 at $m=4$ and 4.73140 at $m=64$. For a calculation at arbitrary $m$, take $K_0\sim\operatorname{Bin}(m+1,1/2)$. Then $P_2=\tfrac12\mathbb E[K_0+(K_0+\log_2(1+2^m))^2/(K_0+1)]$. The maximum through all four-bit functions was 4.85664. The published seed gave 4.35105. At depth 18 of its tower, 16 exact-law spectral samples comprising 4,521,520 leaves gave a ratio-of-sums estimate of 11.09. Those 16 sets are the sampling units. This estimate has no certified error bound. A priority is an analytic or exact-recursion test on near-dictator balanced towers with increasingly rare branching and on multi-output lookup gates. An unbounded $P_2/I$ would refute this strengthening only. The Boolean-specific inequality needed to bound $P_2$ is unproved.
2. **Optimize information gained when a core bit is reused.** For any new core partition into disjoint edges, measure the Walsh transform of the core with endpoint means $\pm t$. Equation (1) gives the exact change in entropy and (2) gives its price for monotone gates. A concrete search is to maximize the gain after subtracting $R(I-1)$, with $R=6.521850225089574148$, using gates with a retained singleton of prescribed $t$. For the present nine-edge core, the interference correction in (1) peaks on the tested grid $t=j/2000$ ($1\le j\le200$) at $t=0.0025$, gaining about $5.684\times10^{-6}$ bits relative to zero sharing with intrinsic gate entropy held fixed. Realizing that value at competitive influence requires a Boolean gate. Test arities and host fractions increasing with the recursion, while preserving a nonzero entropy gain per stage. The example here has a geometric damping factor $1/32$. To obtain a disproof one would have to bound the accumulated gain **relative to influence** along an unbounded sequence. A positive change in an amplified score at one stage establishes only a lower bound. The core-cell, biased-pair, controlled-swap and overlap searches above provide initial controls for that experiment.

## 8. Reproduction and Lean scope

From the repository root, use Python 3.9+ with NumPy. These runs used Python 3.9.6 and NumPy 2.0.2. No network or external certificate download is needed to replay the bound.

```sh
python3 -B scripts/certificate.py
python3 -B scripts/towers.py
python3 -B scripts/experiments.py
python3 -B scripts/deletion.py
python3 -B scripts/gate_search.py
python3 -B scripts/core_search.py
python3 -B scripts/control_swap.py
python3 -B scripts/overlap.py
python3 -B scripts/adversarial.py
lake build
```

[walsh.py](scripts/walsh.py) supplies the common WHT and the hash-checked 18-bit input. [certificate.py](scripts/certificate.py) verifies the strict lower bound. [towers.py](scripts/towers.py) verifies the all-coordinate lower bound for induction. [experiments.py](scripts/experiments.py) and [deletion.py](scripts/deletion.py) check the analytic obstructions. [gate_search.py](scripts/gate_search.py), [core_search.py](scripts/core_search.py), [control_swap.py](scripts/control_swap.py), [overlap.py](scripts/overlap.py) and [adversarial.py](scripts/adversarial.py) reproduce the searches.

[ResearchLemmas.lean](FEI/ResearchLemmas.lean) proves the product entropy identity, the entropy contribution of dyadic copies, the spectral tail bound in the frozen normalization, the closed ratio recurrence, and its limit consequence for realizable FEI families. The last theorem explicitly assumes the family and its recurrence. The numerical certificate and the combinatorial construction rely on the mathematical arguments above and the Python checks. They have not been formalized end to end. The default `lake build` compiled the auxiliary results with zero errors or warnings. The SHA-256 of `FEI/Challenge.lean` before and after this work was `6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b`.


