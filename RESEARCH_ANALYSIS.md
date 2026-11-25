# Fourier entropy and influence on the uniform cube

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


