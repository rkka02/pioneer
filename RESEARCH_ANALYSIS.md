# Fourier entropy and influence on the uniform cube

## MAX Round 4

**Case C.** I obtained a stronger, Lean-checked comparison for the signed dyadic grid energy, a sharp logarithmic price for single-frequency crossings and an obstruction to reserves based on bounded-order marginals of the future block, and an equivalent fixed-error matrix approximation problem. The latter admits a dimension-free bound for coded phase gates with arbitrary shared labels. On the counterexample side, the finite seeds in the #132 sensitivity separation have $H/I\to4$ as their parameters grow. A 20-bit instance of the #192 reporting rule exhibits its intended variance gain and has $H/I\in[2.62727268,2.62727269]$. The universal bounds on $R_{\mathcal T}/I$, $B$ and $X/I$ remain open. The best finite ordinary $H/I$ certified in this project is still $[6.5218511673478223969022,6.5218511673478223969023]$ from Round 1.

All entropy units are bits unless a natural logarithm is displayed. For a sign $f$, write $a_S=\widehat f(S)$, $p_S=a_S^2$, $K=|S|$, $H=H(p)$ and $I=\sum_S Kp_S$. The numerical experiments below use integer Walsh transforms, exact finite recurrences and rational enclosures. A bound for a family is accompanied by its argument.

### The signed grid lies below half-entropy

For $r_h(s)=\operatorname{dist}(s,h\mathbb Z)$ set $g(s)=\sum_{m\ge0}r_{2^{-m}}(s)^2$, $\phi(s)=s^2\log_2(1/|s|)$ with $\phi(0)=0$, and $G(f)=\sum_S g(a_S)$. For every Boolean function, including biased and constant functions,
$$
 \boxed{\quad 0\le H(f)/2-G(f)\le 2I(f).\quad} \tag{4.1}
$$
Consequently **$R_{\mathcal T}\le G\le H/2$ for every full restriction tree**, and $0\le H/2-R_{\mathcal T}\le(38/3)I$ by the fine-scale loss in Round 3. At $s=2^{-j}$ the $j$ coarsest scales each contribute $s^2$ and the others vanish, so $g(s)=\phi(s)$ exactly.

Here is the scalar argument. On $[0,1]$, $g(1-s)=g(s)$. For $s\le1/2$, $g(s)=s^2+g(2s)/4$ and $\phi$ satisfies the same recurrence. Induct on the number of grid levels, using reflection for $s>1/2$, to get $g(s)\le s(1-s)$: the small-side induction gives $s^2+(2s)(1-2s)/4=s/2\le s(1-s)$. On $1/2\le s\le1$, the chord bound $\log_2(1/s)\ge1/s-1$ proves $g\le\phi$, and $\phi\le s^2$ there. Doubling down to that interval gives $0\le\phi(s)-g(s)\le s^2$ everywhere. For the empty coefficient also use $\phi(s)\le1-s^2$, from $-p\ln p\le1-p$ and $2\ln2\ge1$. The total error is therefore at most $2(1-p_\varnothing)\le2I$. At dimension $n$ the Walsh amplitudes have denominator dividing $2^n$, so the sum in (4.1) is finite. Lean proves this grid cutoff, (4.1), and the equivalence of a uniform grid bound with the frozen FEI statement. The tree consequence uses the mathematical restriction identity in Round 3. [Lean proofs](FEI/ResearchLemmas.lean) · [Dyadic checks](scripts/max4_reserve.py)

### What pays for a whole prefix of data queries

I first tested a future variance budget on the Round 3 bent-plus-data prefix. Write $N=2^n$ for even $n$. Half the address rows return independent data signs, the other half return the quadratic bent sign, and a fresh sign balances the output. For future influences $\alpha_j$, the expected decrease in $\sum_j\alpha_j(1-\alpha_j)$ after revealing **all** data is exactly $(n+1)/(4N)$. Indeed, the decrease for bit $j$ is the variance of its conditional influence. Across the distinguished address direction there are $N/2$ independent fair disagreement indicators of weight $2/N$. In each other address direction there are $N/4$ independent fair indicators on the data half and a deterministic count on the other half. The tag has zero variance. At $n=12$ the budget spends $13/16384$, queried influence is $1/2$, and $R_{\rm data}\in[2.659513,2.659514]$. The prefix cost grows as $n/4+O(1)$. [Exact variance and endpoint tests](scripts/max4_reserve.py)

There is a two-block identity that identifies the missing information. Split physical inputs into $X,Y$ and the frequency into $U,T$ on those blocks. Let $x\in X$ be uniform and $b_T(x)=\sum_U a_{U,T}\chi_U(x)$. Use the joint law $\Pr(x,T)=b_T(x)^2/|X|$, and define $\Pr(U,y)$ by interchanging the blocks. Both have the spectral marginal on their frequency coordinate. The chain rule and Parseval give
$$
 H(p)-\mathbb E_x H(f_x)=H_p(U\mid T)+I(X;T),\qquad
 H_p(U\mid T)=\mathbb E_y H(f^y)+I(U;Y)-I_p(U;T). \tag{4.2}
$$
In particular a frequency label may recover information about future physical bits. For each $T$, the cube log-Sobolev inequality applied to $b_T$ gives $\operatorname{Ent}_2(b_T^2)\le(2/\ln2)\sum_U |U|a_{U,T}^2$. Summing yields $I(X;T)\le(2/\ln2)I_X$. Also $I(U;Y)\le (2/\ln2)\sum_{U\ne0,T}|T|p_{U,T}+\delta/\ln2$ with $\delta=\Pr(U\ne0)$. Apply log-Sobolev only on $U\ne0$, and use $b_0(y)^2\le1$ in the interchanged law to bound the other row by $-(1-\delta)\log_2(1-\delta)$. [Cube log-Sobolev inequality](https://www-users.cse.umn.edu/~bobko001/papers/1998_JFA_BL.pdf) · [Tests of both joint laws](scripts/max4_reserve.py)

More precisely, let $R_X$ be the coarse cost incurred when a fixed order reveals $X$ before $Y$. Put $u_T=a_{0,T}$, $e_T=\sum_{U\ne0}p_{U,T}$ and $\Gamma=\sum_T |u_T|\sqrt{e_T}$. Then
$$
 \left|R_X-\tfrac12 H_p(U\mid T)\right|
 \le 18 I_X+8\Gamma,\qquad \Gamma\le\sqrt{\delta(1-\delta)}. \tag{4.3}
$$
To see why the error need not scale with the dimension of $Y$, write $d=\phi-g$. On $0<s\le1$, let $k=\lfloor\log_2(1/s)\rfloor$. The first $k$ grid terms have derivative $2ks$ in total away from corners. The absolute derivative of the remaining sum is at most $\sum_{m\ge k}2^{-m}\le4s$. The difference between $\phi'(s)$ and $2ks$ is at most $(2+1/\ln2)s$. The grid series is absolutely continuous since the Lipschitz constants of its terms are summable. Integration and evenness give $|d(s)-d(t)|\le4|s^2-t^2|$. The root rows with $U\ne0$ contribute at most $\delta$ to the discrepancy. On the other rows use $\mathbb E(b_T-u_T)^2=e_T$ and $\mathbb E|b_T^2-u_T^2|\le2|u_T|\sqrt{e_T}+e_T$. This costs another $8\Gamma+4\delta$. The fine scales cost at most $(32/3)I_X$, by telescoping on this prefix, and (4.2) costs at most $I_X/\ln2$. This proves (4.3). Its square-root allowance matters because on the single-selector bent switch from Round 3, $R_X=2/\sqrt N$ while $H_p(U\mid T)\le h_2(2/N)$. [Scalar, block, and prefix checks](scripts/max4_reserve.py)

**A Boolean martingale obstruction with all low-order future marginals fixed.** Take $N=2^n$ data signs $x_y$, an address $y\in\mathbb F_2^n$, guard bits $z\in\mathbb F_2^r$, and a balancing sign $(-1)^t$. For a full-rank map $L$ set
$$
 F=(-1)^{t+z\cdot Ly}x_y .
$$
Query the data first. Each data bit costs $1/N$ in influence at every surviving query. On the Walsh side $U$ is the singleton of a uniform address, $T$ contains the tag, its $z$ mask is $Ly$, and its $y$ mask is independent and uniform. This follows by taking the transform of one address point at a time. Hence $H=2n$, $I=2+(n+r)/2$, $I(U;Y)=n$, $I_p(U;T)=r$, and $H_p(U\mid T)=n-r$. Here $Y$ comprises all future bits. The subtraction of spectral mutual information in (4.2) can be macroscopic.

If $\ker L$ has minimum distance $>d$, **every marginal on at most $d$ future frequency coordinates is exactly the same at every data-prefix node**. After fixing all data, a future translation $(v,w)$ in the address and guard coordinates has zero autocorrelation if $Lv\ne0$, by averaging over $z$. If $v=0,w\ne0$, average over $y$ and use full rank. This proves the vanishing of every nontrivial parity moment of order at most $d$ on these bits. The tag is always present. Partial data restrictions average the fully restricted future spectral laws by Parseval. One may take $r=\lceil n/2\rceil$ and $d=\lfloor n/16\rfloor$ for all large $n$. For a random binary matrix the probability of a short kernel vector is at most $2^{-r}\sum_{j=1}^d\binom nj=o(1)$, and the probability of row-rank failure is at most $2^{r-n}$. In particular, a node potential determined only by these low-order future marginals has zero drop throughout the prefix, for an arbitrary function of those marginals.

At any fixed supported future mask, the partial Walsh coefficient starts at zero and takes $q=2^{n-r}$ independent signed steps of size $1/N$, interleaved with zero steps. This includes the mask consisting only of the tag. Write $W_q$ for the unscaled walk. Its prefix quadratic variation is $q/N^2$. The exact coarse cost divided by this variation, **also equal to the entire prefix cost** after summing the $N2^r$ masks, is
$$
 \sum_{h=8,16,\ldots,N}\left(1-\mathbb E r_h(W_q)^2/q\right)
 =\tfrac12\log_2 q+O(1). \tag{4.4}
$$
Here $h$ uses integer numerator units. Telescope the single-scale grid cost, including $q$ unit child residuals. For $h\le\sqrt q$ the error from one per scale is at most $h^2/(4q)$. For larger $h$, the contribution is at most $4\mathbb E W_q^4/(qh^2)\le12q/h^2$, since no distance is lost on $|W_q|\le h/2$. Both errors sum geometrically. At $(n,r)=(14,1)$ the exact value lies in $[5.19520686,5.19520687]$ while the data influence is one. Thus per-frequency local time can exceed its entire prefix variation by an unbounded factor, even for a future mask of degree one. The family itself has bounded ordinary $H/I$. [Factored integer WHT, dense check and exact occupation sums](scripts/max4_reserve.py)

**Even the *full* quadratic variation of a terminal singleton is insufficient.** In fact one can identify the scalar price up to an additive constant times the variation in squares. For a single coefficient martingale starting at zero, with fair branches $M\mapsto M\pm v$, let $Q=\sum\mathbb E v^2>0$, $V=\sum\mathbb E|v|$, and let $R^{(1)}$ be its accumulated coarse cost. Then
$$
 R^{(1)}\le Q\,[\log_2(V/Q)+2].
$$
The increments have magnitude at most one. At each fixed scale $h$, telescoping the nonnegative same-grid costs bounds its coarse part by $\sum\mathbb E r_h(v)^2\le\min(Q,hV/2)$, since the starting grid residual vanishes. There are at most $1+\log_2(V/Q)$ dyadic scales at or above $Q/V$. Sum the smaller scales geometrically. For a fixed surviving frequency, $V$ itself is bounded by the total queried influence: before taking the absolute value each increment is the signed conditional average of a half-difference of Boolean outputs.

The logarithm has **sharp leading constant one**, even on an actual Boolean coefficient path with $|T|=1$. Let $B=2^a$. Take $J=aB^2$ independent fair steps of a simple random walk starting at zero, absorbed on reaching $\pm B$. If its final position is $w$, use $a+1$ fresh fair bits to output $+1$ with probability $(B+w)/(2B)$, otherwise $-1$. Call that deterministic Boolean table $h$, and take $f=z h$ with a fresh tag $z$. Reveal all steps and rounding bits, retaining only $T=\{z\}$. During the steps the coefficient martingale is $W_j/B$ and at the end it is exactly $\pm1$, so its entire $Q$ is one. The mean absorption time is $B^2$ from zero, by the solution $B^2-w^2$ of the elementary hitting-time recurrence (finiteness follows from the chance of $2B$ identical next steps). Thus $\Pr(\tau>J)\le1/a$, and $\mathbb E(\tau\wedge J)/B^2=\mathbb E W_J^2/B^2\ge1-1/a$. For each integer grid height $8,16,\ldots,B$ the prefix cost is $B^{-2}[\mathbb E(\tau\wedge J)-\mathbb E r_h(W_J)^2]$. The total endpoint loss on these scales is at most $1/3$. Hence $R^{(1)}\ge(a-2)(1-1/a)-1/3$, while $B(1-1/a)\le V\le B+a+1$. This disproves a dimension-free scalar local-time bound even after all other coordinates have been accounted for in this martingale. The physical influence of the walk already grows at least linearly in $B$. At $B=32,J=5120$, exact integer recursion through the last rounding bit gives $Q=1$ and $R^{(1)}\in[2.99321705,2.99321706]$. A smaller instance also checks the path means against the dense Boolean WHT. [Stopped walks and exact terminal checks](scripts/max4_reserve.py)

### Reporting rules, block symmetry and the #192 readout

The reporting rule omits one score. Its exceptional cell $A$ is the event that only the selected leaf fails its interval test. The all-pass cell is $B$. The identity $\mathbf1_A=\mathbf1_P-\mathbf1_B$, with $P$ testing the unselected leaves, saves one input in the degree of each term. For Fourier entropy the terms interfere when squared. I used the paper's conditional-mean score to preserve this interference in the experiments. [Reporting construction](frontier_refs/192_sqrt_degree_disproof__sections_02-reporting.tex) · [Alternative reports](frontier_refs/192_sqrt_degree_disproof__sections_03-alternatives.tex)

One finite example **actually beats the variance benchmark**. Use five independent sums of four signs, one center and four leaves. The leaf intervals are the singletons $2,0,-2,-4$. At center values $4,2,0,-2,-4$, select leaves numbered $1,2,3,4,3$, respectively. Report the $A$ tag, all leaf values on $B$, or the center and the unselected leaves elsewhere. For the total raw bit sum $D$ and report $\mathcal W$, exact counts give
$$
 \Pr(A)=17/2048,\quad \operatorname{Var}(D\mid A)=1147/289<4,\quad
 \operatorname{Var}(\mathbb E[D\mid\mathcal W])/4=557065/139264>4.
$$
The unobserved sum has variance four on each ordinary report. On $A$, condition on the center and use the excluded-singleton distribution of the selected leaf. All $2^{20}$ inputs independently reproduce the resulting moments. Each report cell has degree at most 16 in the raw bits. The sign of its conditional mean (positive at zero) has $I=113091/32768$, $H/I\in[2.62727268,2.62727269]$, $B\in[.79146471,.79146472]$, $X/I\in[1.03608801,1.03608802]$. For biased examples here and below, $B$ denotes the same incidence formula evaluated on their spectra. In twelve other finite refined/coarse and bin-selected reports on 4, 8 and 12 bits, $H/I<2.621$. A two-copy readout has $H/I\in[2.81946427,2.81946428]$ and $R_{\rm fixed}=1/8$. These finite choices probe the rule and the variance mechanism. The paper also iterates changing observations, with CLT parameters chosen afresh at each stage. [Reporting WHT and exact orbit counts](scripts/max4_reporting.py) · [Amplification](frontier_refs/192_sqrt_degree_disproof__sections_01-observations.tex) · [Mean-cost refinement](frontier_refs/192_sqrt_degree_disproof__sections_04-mean-cost.tex) · [Weighted schedule](frontier_refs/192_sqrt_degree_disproof__sections_05-weighted.tex)

I also tested switching to the Round 1 spinal gate on $A$. Balance the off-event score sign with a fresh tag. If $F_0$ uses a private dictator on $A$, replacing it by **any** disjoint balanced $g$ gives $H(F)=H(F_0)+\Pr(A)H(g)$ and $I(F)=I(F_0)+\Pr(A)(I(g)-1)$. The empty private row is the unchanged off-event table. Each nonempty private row is the product of a coefficient of $\mathbf1_A$ and a coefficient of $g$. Parseval and the entropy product formula give both identities. Consequently $H(F)/(I(F)-1)$ is a weighted average of the two amplified scores. The three hosts have scores below $2.495$; this substitution cannot improve the spinal gate's amplified score. The verifier checks the transfer against dense substitutions and applies uniformly to the certified spinal gate. [Switch tests](scripts/max4_reporting.py)

**A uniform theorem for the final averaging step.** Let a Boolean sign on $M$ blocks of $b$ bits be invariant under simultaneous permutations of the whole blocks. There is no symmetry assumption within a block. For every $M$,
$$
 \sqrt{P_2/I}\ \le\ 2b+\sqrt{20}+(3+4\sqrt2)/\ln2 \qquad (I>0). \tag{4.5}
$$
In particular $X/I$ is bounded for the sign of any sum of identically specified $b$-bit report scores, throughout arbitrarily many copies. The bound depends on the size of the observation entering the averaging stage.

Let $J$ count occupied blocks in a spectral sample, and size-bias its law by $Kp_S/I$. For $0\le\rho<1$,
$$
 \mathbb E_{\rm inc}\rho^{J-1}\le\sqrt{2^{b-1}/[M(1-\rho)]}.
$$
For a marked bit keep its block and refresh each other block independently with probability $1-\rho$. Apply this noise to $D=(f(x)-f(x^{(i)}))/2$. The marked block has two possible symbols $a,a'$ in this difference. Among the refreshed blocks, those landing in $\{a,a'\}$ contribute fair binomial counts. Conditional on their number $L$ and the other symbols, changing the marked symbol translates this binomial by one. Block permutation symmetry bounds the averaged half-difference by its total variation from the translate, at most $1/\sqrt{L+1}$ by the central binomial coefficient bound. Here $L$ has law $\operatorname{Bin}(M-1,(1-\rho)2^{1-b})$. Cauchy–Schwarz and $\mathbb E[1/(L+1)]\le1/[M(1-\rho)2^{1-b}]$ bound the noised derivative pointwise. Since $|D|=D^2$, its noise correlation costs at most this bound times $I_i$. Sum over bits and use Parseval to obtain the display.

Taking $\rho=1-1/j$ gives $\Pr_{\rm inc}(J\le j)\le e\,2^{(b-1)/2}\sqrt{j/M}$, with the $j=1$ case at $\rho=0$. Thus $\|\ln(M/J)\|_2\le2+(b-1)\ln2+2\sqrt2$, by integrating the exponential tail past $2+(b-1)\ln2$. To price a frequency with $J=j>0$ give it comparison mass $q_S=2^{-j}/[\binom Mj(2^b-1)^j]$. These masses sum to at most one. Conditional on nonemptiness, write $p'$ for the spectral law. The positive part of $\log_2(q_S/p'_S)$ has second moment at most $2/(\ln2)^2$ by Markov. The rest of the description costs at most $j[1+b+\log_2 e+\log_2(M/j)]$ plus the bias price $\log_2(1/\Pr(K>0))$. In the norm $L^2(p_S/K,\ K>0)$ the latter costs at most $\sqrt{20 I}$ by the bias argument in Round 3, and $j\le K$. Minkowski gives the stated constant after adding $\sqrt{2I}/\ln2$ for the conversion from the surprise moment $U=\sum_{K>0}p_S\log_2^2(1/p_S)/K$ to $P_2$, as proved in Round 3, equation (1). The same estimate bounds $H/I$ since the nonempty entropy is at most $\sqrt{IU}$ and the empty atom costs at most $I/\ln2$. [Integer block-refresh checks](scripts/max4_reporting.py) · [Earlier coordinate-symmetry result of O'Donnell–Wright–Zhou](https://www.cs.cmu.edu/~odonnell/papers/fei.pdf)

### The labelled-tournament construction has limiting seed ratio four

Use the actual #132 finite seed including its final OR. Write $L=d+2$, $b=LM$, $k=2M^2+1$, $r=\lceil\sqrt M\rceil$, $g=1+r+\cdots+r^{d-1}$, $m=br^d$ and $n=bM(kr)^d$. The result below holds uniformly over its edge labellings whenever $M\to\infty$ with $M\ge9^{d+1}$. If $F$ denotes the sign of that seed, then
$$
 H(F)/I(F)\longrightarrow 4,\qquad U(F)/I(F)\longrightarrow 16.
$$
In particular $\limsup X/I\le(4+\sqrt2/\ln2)^2$, $\limsup B\le4+\sqrt2/\ln2$, and $\limsup R_{\mathcal T}/I\le2$ uniformly in the reveal tree. The large block sensitivity is measured at a special input. The uniform spectral law is controlled by the rare target certificates. [Tournament definition](frontier_refs/132_sens_vs_block_sens__sections_01-construction.tex) · [Final OR and power separation](frontier_refs/132_sens_vs_block_sens__sections_03-separation.tex) · [Exact verifier](scripts/max4_tournament.py)

Here are the estimates behind the limits. For the acceptance event $E$ write $\mu=\Pr(E)$. Ignore the vetoes and count successful target certificates with multiplicity. At the base, $W_0$ is the indicator of the $M$ centers. Recursively, $W_\ell$ is the sum over the $k$ rows of the product of the $r$ independent child counts in that row. At the final OR sum the $M$ counts. Then $W\ge\mathbf1_E$. This polynomial is a sum of $D=M^{1+r^d}k^g$ indicators, each fixing exactly $m$ fair bits, so $A=\mathbb EW=D2^{-m}$. Write $a_\ell=\mathbb EW_\ell$, $b_\ell=\mathbb EW_\ell^2/a_\ell$. Independence gives
$$
 a_0=M2^{-b},\quad a_\ell=k a_{\ell-1}^r,\qquad
 b_0=1,\quad b_\ell=b_{\ell-1}^r+(k-1)a_{\ell-1}^r.
$$
The final second-moment ratio is $b_d+(M-1)a_d$. All $a_\ell\le a_0$ in this range. The ratio is at most $(1+Ma_0)(1+a_0)^g$.

For the actual acceptance probabilities, two winning rows are incompatible because the directed edge between them vetoes the target of one of them. Each row uses distinct children. Its acceptance probability is the $r$th power of the previous strongest density times $(1-\mu_{\rm weak})^{M^2}$. Every weak density is at most $\beta=M2^{-b}\sum_{j\le d}\binom bj$ at the base and at most $a_\ell$ thereafter. Iteration and the elementary lower bound on the final OR give $\mu/A\ge 1-\ell_0$ for $\ell_0=M^2g\beta+Ma_0$. With $x=(g+M)a_0$ and $x,\ell_0<1/2$, this proves
$$
 \|\mathbf1_E-W\|_2^2/\mu
 \le(\mathbb EW^2-\mu)/\mu\le \eta=(2x+\ell_0)/(1-\ell_0).
$$
Indeed $(W-\mathbf1_E)^2\le W^2-\mathbf1_E$ on each input. Uniformly, $\eta=2^{-\Omega(b)}$, $\log n=o(b)$ and $\log D=o(m)$, directly from the displayed parameters and $d+1\le\log_9 M$.

Write $\mathcal D(v)=\sum_S |S|\widehat v(S)^2$. Its normalized value on $W_0$ is $b/2$, since the centers are isolated. Across a recursive row layer $\mathcal D(W_\ell)/a_\ell$ is $r b_{\ell-1}^{r-1}$ times the preceding value, by the product rule on disjoint blocks and additivity of the Dirichlet energy of the row sum. The final OR count preserves that ratio. Consequently $\mathcal D(W)/A=(m/2)(1+o(1))$ and is at least $m/2$. For the true spectral law $q_S=\widehat{\mathbf1_E}(S)^2/\mu$, the Dirichlet triangle inequality gives
$$
 \sqrt{\mathbb E_q K}\ \ge\ \sqrt{m/2}-\sqrt{n\eta}.
$$
The reverse triangle bound likewise gives $\mathbb E_q K\sim m/2$. The Walsh support of $W$ has at most $D2^m$ members, and $q$ has at most $\eta$ mass outside it. Also $\max q_S\le\mu$ by the triangle inequality on the event. Hence
$$
 \log_2(1/\mu)\le H(q)\le m+\log_2D+h_2(\eta)+n\eta .
$$
The sign's nonempty masses are $4\mu q_S$, with $q_\varnothing=\mu$, and $I=4\mu\,\mathbb E_q K$. Substitution gives the entropy ratio limit. For a finite upper certificate retain the negative term from the factor four: $H(F)/(4\mu)\le 2m-(2-\log_2 e)(1-\mu)+h_2(\eta)+n\eta+\log_2(A/\mu)$. This follows by bounding the empty sign entropy by $4\mu(1-\mu)\log_2 e$. At $(d,M)=(1,81)$ the gate has $n=2,324,700,081$ and $H/I<3.99954276$. At $(2,729)$ the bound is $H/I<3.99999953$. These are one-sided analytical certificates computed with rational error bounds. As a separate moment check, the exact 243-bit base at $M=81$ has $U/I\in[15.45221473,15.45221474]$ by integer convolution on block parities and degrees.

For the surprise moment, each of the $D$ Fourier support cubes of $W$ has a binomial $(m,1/2)$ degree profile. The squared normalized Walsh law of $W$ has maximum atom at most $A$, since $W\ge0$ and $\mathbb EW^2\ge A$. Its probability of $|K-m/2|>\epsilon m$ is therefore at most $2D^2e^{-2\epsilon^2m}$. For the true $q$, the squared triangle inequality multiplies this bound by $2\mathbb EW^2/\mu$ and adds $2\eta$. Within the union of supports, $q$-mass with surprise exceeding $m+\log_2D+s$ is at most $2^{-s}$ by counting. The lower surprise bound is $\log_2(1/\mu)=m-o(m)$. Choose $\epsilon=o(1)$ with $\epsilon^2m\gg\log D+\log n$, and $s=o(m)$ with $s\gg\log n$. The total exceptional mass is $o(n^{-2})$. Every positive sign mass has surprise at most $2n$. On the remaining nonempty masks the sign surprise is $(2+o(1))m$ and $K=(1/2+o(1))m$. This proves $U/I\to16$ and that $d_b/I\to1$. Cauchy–Schwarz, the comparison with $P_2$ and (4.1) give the other stated limits superior.

The paper's separate power family fixes $d=9$ and self-composes one finite biased seed. Its $H/I$ also converges to a finite limit, which need not equal the seed-parameter limit above. In general let a fixed gate have minimum accepting weight $w\ge2$, $c$ minimum witnesses, and an iteration of input densities $p_j\to0$. Its outer density at bias $p$ is $c p^w+O(p^{w+1})$. The **conditional** mean outer spectral degree $b(p)$, restricted to nonempty masks in the orthonormal biased basis, is $w+O(p)$. Indeed the biased sign degree sum is $4p(1-p)\sum_i\Pr_{-i}(\partial_i\mathbf1_E\ne0)=4wc p^w+O(p^{w+1})$. Divide by the new sign variance. For the composed gate let $t_j,s_j$ be the mean degree and entropy conditional on nonemptiness. Expansion in centered child signs gives $t_{j+1}=b(p_j)t_j$, $s_{j+1}=b(p_j)s_j+h_j$, where $h_j$ is the conditional outer entropy, bounded by the fixed arity. The selected outer masks are recovered from the nonempty leaf blocks. Since $\sum p_j<\infty$, $t_j/w^j$ has a finite positive limit, $\sum h_j/t_{j+1}$ converges, and $\log(1/p_j)/w^j$ converges by the density recurrence. Using $H/I=s_j/t_j+h_2(v_j)/(v_jt_j)$ with $v_j=4p_j(1-p_j)$ proves convergence. For the actual $d=9$ seed, $w=Lr^d$ follows by meeting all targets in a row and leaving all veto rows zero. Its first density is at most $M^2 2^{-11M}<1/(2n^2)$, since $n\le M^{27}$ in the paper's range. Subsequently $\mu(p)\le n^wp^w\le p/2$ there. The verifier checks the biased recursion against a direct two-level WHT and obtains $[3.65153883,3.65153884]$ at depth three for a scaled nine-bit tournament. For that nine-bit gate itself $R_{\rm fixed}/I=5/108$, $B\in[.82892973,.82892974]$ and $X/I\in[.49181591,.49181592]$. [Biased and scaled checks](scripts/max4_tournament.py)

### A sign obstruction beyond plateaued phases

Retain the thick floor of Round 3, remove its tag, and write the proposed coefficients as $2^{-d}A_s\sigma(s)$, where $A_s-1$ is supported on degrees $\le k$ and the increment at **every** weight-$k$ mask has nonzero magnitude $u_k$ or $2u_k$. Split native frequency coordinates into $a$ bits $u$ and $b$ bits $v$, with $b\ge k$. Consider the nonplateaued phases
$$
 \sigma(u,v)=(-1)^{u\cdot\pi(v)+h(v)}
$$
with arbitrary Boolean $h$ and arbitrary vector-valued $\pi$. A necessary condition for a Boolean inverse is the following. For every weight-$k$ mask $R$ on the $v$ coordinates, **no nonzero linear component of $\pi$ has an affine certificate through $R$ of codimension $\ell\le d-k-\log_2|A_{0,R}-1|$**. An affine certificate means that the component is constant throughout the flat. It even suffices for the component to be constant on the intersection of that flat with the upper face $\{V:V\supseteq R\}$. In particular this excludes maps with an affine output component or an output component depending on at most that many parity tests. The uniform forbidden codimension in the thick-floor examples at $k=4,16,64,256$ is respectively $2,26,172,950$.

To prove it, fix the first physical coordinates to $z$. The floor part of this row has Fourier coefficients $2^{a-d}(-1)^{h(v)}\mathbf1_{\pi(v)=z}$. The correction has degree $\le k$, and at $R$ it is exactly $2^{-d}\sigma(0,R)(A_{0,R}-1)$, because no positive $u$ degree fits above $R$. Choose $z$ with the opposite component value. Project onto the affine frequency flat through $R$ by a signed average over its $\ell$ dual physical directions, then take the $R$th Walsh derivative. Every surviving superset from the floor has disappeared. The result is the constant correction at $R$, up to the removable character convention for the derivative. On a Boolean row this is a signed average of $2^{k+\ell}$ signs, hence belongs to $2^{1-k-\ell}\mathbb Z$. The displayed range makes the nonzero correction strictly smaller. This proof uses a row of the **signed** inverse.

Twelve exact tests at $k=4$ used $a=3,4,5,6$ and three phase types at each width. Every example was genuinely nonplateaued and had Walsh gcd valuation exactly $a$, within Round 3's admissible range. Linear-component and two-parity nonlinear-component cases were excluded by the row certificate. Four unrestricted maps also failed direct inversion. One projection of each candidate to a true tagged sign gave $H/I$ between $2.0360$ and $2.050999$, and $B$ between $.6879$ and $.6960$. The general thick-floor signing problem remains open. [Exact row projections, certificates and integer WHT tests](scripts/max4_signings.py)

### A matrix formulation and a two-sided influence bound

For uniform cubes $X,Y$ form the real matrix $M_{xy}=f(x,y)/\sqrt{|X||Y|}$. Write $\lambda$ for its squared singular values, $S(M)=H(\lambda)$, and $r_\epsilon(M)$ for the minimum rank capturing $1-\epsilon$ of its squared Frobenius norm. Equivalently it is the least number of leading $\lambda_j$ with that mass. For **one fixed error**, for example $\epsilon=1/4$,
$$
 \boxed{\quad\mathrm{FEI}\quad\Longleftrightarrow\quad
  \exists K\ \forall f,\ X,Y:\quad \log_2 r_{1/4}(M)\le K\,(I_X+I_Y).\quad} \tag{4.6}
$$
It is also equivalent to $S(M)\le K(I_X+I_Y)$. Paraashar–Saurabh use the singular-value entropy of sign matrices in quantum communication and identify the spectrum of an XOR matrix. Here the proposed resource on the physical sides is average edge disagreement, and the approximation uses uniform mean squared error. [Paraashar–Saurabh, §1.1 and `6](https://arxiv.org/html/2611.06451v1)

For clarity, in the two Walsh bases the diagonal of $MM^\mathsf{T}$ is the $U$-marginal of $p$ (after conjugating on $X$). Entropy of a diagonal is at least spectral entropy by concavity applied to the squared orthogonal change-of-basis entries. Hence $S(M)\le H_p(U)\le H(f)$. Markov on $\log_2(1/\lambda)$ shows $\log_2 r_\epsilon\le S(M)/\epsilon$. Conversely tensor powers of any sign matrix are normalized sign matrices, with additive influence and product singular law. For fixed $\epsilon\in(0,1)$,
$$
 \lim_{j\to\infty}j^{-1}\log_2 r_\epsilon(M^{\otimes j})=S(M).
$$
Indeed the law of large numbers puts mass $1-o(1)$ on probabilities between $2^{-j(S+\alpha)}$ and $2^{-j(S-\alpha)}$ for each $\alpha>0$. They number at most $2^{j(S+\alpha)}$, and capturing mass $1-\epsilon$ requires at least $(1-\epsilon-o(1))2^{j(S-\alpha)}$ of them. Finally $f(x,y)=h(x\oplus y)$ has squared singular values $\widehat h(S)^2$ by Walsh diagonalization, and influence $2I(h)$. A general rank bound with constant $K$ would thus give FEI with $C=2K$. The project certificate requires any such $K$ to exceed $3.26092558$. This reduction permits arbitrary real low-rank approximants.

**The future cost can be paid in a basis chosen for the column family.** Put $v_y=f(\cdot,y)/\sqrt{|X|}$. Let $\widetilde I_Y$ sum, over $Y$ directions, the expected projective disagreement $\min(d,1-d)$ between adjacent columns, where $d$ is their Hamming disagreement fraction. For any *one fixed* real orthonormal row basis $(e_j)$, use $\Pr(j\mid y)=|\langle e_j,v_y\rangle|^2$. If $W_X$ denotes the minimum of $\mathbb E_y H(j\mid y)$ over common bases, then
$$
 0\le S(M)-W_X\le (2/\ln2)\widetilde I_Y . \tag{4.7}
$$
The upper bound follows from $S(M)\le H(j)=H(j\mid Y)+I(j;Y)$. Apply cube log-Sobolev to $|\langle e_j,v_y\rangle|$ and sum over $j$. The summed squared increments on each edge are at most $\min_\pm\|v_y\pm v_{y'}\|^2=4\min(d,1-d)$. The lower bound follows by using an eigenbasis of $MM^\mathsf{T}$, where $H(j)=S(M)$. This is the mixed-basis version of (4.2) with a free choice of measurement. [Rational orthogonal bases and exact Gram eigenvalue enclosures](scripts/max4_rank.py)

Here is a class where this freedom pays the cost even with arbitrarily many shared labels. On disjoint row blocks $x_j$, allow arbitrary Boolean events $A_j(x_j)$, arbitrary events $B_j(y)$ on **the same** column bits, and arbitrary local sign phases $a(x),b(y)$. For
$$
 f(x,y)=a(x)b(y)(-1)^{\sum_j\mathbf1_{A_j}(x_j)\mathbf1_{B_j}(y)}
 \qquad\text{one has}\qquad
 S(M)\le 2 I_X+(2/\ln2)\widetilde I_Y. \tag{4.8}
$$
Complement the events to have densities $\mu_j,\delta_j\le1/2$, absorbing the resulting single-party phases. On block $j$ take the unit constant and the normalized centered sign of $A_j$ as the first two basis vectors, omitting a trivial feature. Use their tensor basis multiplied by $a(x)$. On a column with $B_j=1$ the second basis outcome has probability $\theta_j=4\mu_j(1-\mu_j)$, and otherwise it has probability zero. The product structure gives $H(j_{\rm outcome}\mid Y)=\sum_j\delta_j h_2(\theta_j)$. For $0\le u\le1/2$, $0\le s\le1$, $s\le4u$, one has $h_2(s)\le4u\log_2(1/u)$. If $u\le1/8$, use monotonicity up to $4u$ and $h_2(4u)\le4u\log_2(e/(4u))$. For $u\in[1/8,1/4]$ and $u\in[1/4,1/2]$ the right-hand side is at least one. On a row edge where $A_j$ changes, averaging over $y$ gives disagreement at least $\delta_j$ for either local phase choice. Edge isoperimetry gives $I_X\ge2\sum_j\delta_j\mu_j\log_2(1/\mu_j)$. Combining these estimates with (4.7) proves (4.8). The constant allows unrestricted correlations or simultaneous changes among the $B_j$. It bounds singular-value entropy. An arbitrary Boolean function of the column bits can still occur in a single label. [Exact shared-feature experiments](scripts/max4_rank.py) · [Formal binary entropy estimate](FEI/ResearchLemmas.lean)

**Sharp rank-two case.** Every real sign matrix of rank at most two satisfies $S(M)\le2(I_X+I_Y)$, and two is optimal. For a short proof let $u$ be the rarer output density. Testing the constant unit vectors gives $\lambda_1\ge(1-2u)^2$. Hence the second eigenvalue is at most $4u$, the binary entropy bound above applies, and edge isoperimetry gives $I_X+I_Y\ge2u\log_2(1/u)$. Sharpness follows from the sign that flips only when both sides equal zero, on $w$ bits per side. Set $\mu=\delta=2^{-w}$. Its two nonzero squared singular values sum to one and have product $4\mu(1-\mu)\delta(1-\delta)$, from the two-by-two matrix grouped by event membership on each side. Thus the small one is asymptotic to $4\mu\delta$, and $I=2\mu\delta\log_2(1/(\mu\delta))$. Their entropy divided by $I$ tends to two. At $w=30$ it lies in $[1.98142316,1.98142317]$. Lean also proves the entropy estimate directly from this determinant for arbitrary $\mu,\delta\le1/2$. [Eigenvalue and tensor-rank certificates](scripts/max4_rank.py) · [Lean scalar theorems](FEI/ResearchLemmas.lean)

The bent-prefix columns give an exact stress test of (4.6): their squared singular law across data versus future is $1/2$ once and $1/N$ on each of $N/2$ other directions. These are the disjoint Walsh rows on the future address cube. Thus $r_{1/4}=1+N/4$ at queried influence $1/2$. For the guarded example the $N$ orthogonal address rows are equiprobable, $r_{1/4}=3N/4$, and the address alone pays projective influence $n/2$. On the published 18-bit seed, a split at four core bits has $r_{1/4}=3$, $S(M)\in[2.28969599,2.28969600]$, and $G=13247/4096$. The verifier brackets eigenvalues using the exact integer Gram characteristic polynomial and signed evaluations, and checks the Gram matrix independently for product and XOR cases. [Rank checks](scripts/max4_rank.py)

### What transferred from the frontier sources

| Source | Mechanism and its scope here |
|---|---|
| [#119 reserve](frontier_refs/119_courtade_kumar_entropy__build_sections_reserve.tex), [thinning](frontier_refs/119_courtade_kumar_entropy__build_sections_thinning.tex), [flow](frontier_refs/119_courtade_kumar_entropy__build_sections_flow.tex) | The reserve is a convex perspective in variance capacity and residual **binary-output** entropy. The sharp flow uses an inverse entropy deficit. The thinning proof exposes an independent flag and conditions on it. Exposing a label before pricing its residual information transfers to (4.2) and (4.7). The canonical optimizer uses equal-output corners in a binary join. The guarded example keeps even high-order future marginals fixed while information moves between data and a joint Fourier label. A potential based on their drop cannot pay (4.4). |
| [#192 observations](frontier_refs/192_sqrt_degree_disproof__sections_01-observations.tex) and [#132 recurrences](frontier_refs/132_sens_vs_block_sens__sections_02-recurrences.tex) | Conditional-mean readout, merged report cells and the tournament veto have different effects on amplitudes. The 20-bit table preserves the positive variance margin. Independent target counts and a relative error estimate control the entire #132 seed regime. |
| [#127 edge recovery](frontier_refs/127_ptf_avg_sensitivity__sections_04-edge-recovery.tex) and [parity coupling](frontier_refs/127_ptf_avg_sensitivity__sections_05-parity-coupling.tex) | The weighted grading recovers agreeing physical edges from a Hilbert–Schmidt anticommutator, and couples opposite threshold signs using a degree bound. The basis-independent squared-increment estimate preceding (4.8) is the edge calculation that survives here. An FEI gate supplies neither a low-degree threshold representation at the required cost nor that paper's grade coupling for singular-value tails. |
| [#186 restriction estimate](frontier_refs/186_friedgut_kalai_hypergraph__restriction.tex) | Averaging a squared restricted coefficient gives its full outside marginal, as in (4.2) and the guarded-prefix proof. The additional suppression in #186 comes from the permutation group remaining after a vertex restriction. Preserved permutation symmetry of repeated report blocks gives (4.5). General restrictions have no such orbit estimate. |
| [#379 guards](frontier_refs/379_sunflowers_exp__guard.tex), [filters](frontier_refs/379_sunflowers_exp__filter.tex) and [mask recurrence](frontier_refs/379_sunflowers_exp__recurrence.tex) | The construction keeps group controls, corrects false equalities by signed masks and pays overhead when an active set shrinks by a fixed fraction. The analogous signed filter gives the affine certificate obstruction above. A restriction of a Boolean sign need not shrink a guarded frequency label at that rate. Its walk can take $2^{n-r}$ unit steps with all the stated marginals unchanged. No tensor-price inequality from the sunflower theorem was assumed. |
| [PSI Lean repository](https://github.com/physical-superintelligence/aaronson-ambainis), [independent completion proof, Lemma 4](https://arxiv.org/html/2611.12795v1) | Fractional certificates on opposite output sets yield an influential query in terms of the two densities and certificate budgets. This locates a physical edge. It supplies no budget for the signed Walsh fibers in (4.3). On the guarded lookup the desired future payment is available explicitly through $I(U;Y)$ in (4.2). |
| [Paraashar–Saurabh](https://arxiv.org/html/2611.06451v1), [Potapov](https://arxiv.org/abs/2609.21563), [Kelman–Kindler–Lifshitz–Minzer–Safra](https://arxiv.org/abs/1911.10579) | The first paper's XOR singular law leads directly to the fixed-error test (4.6). Potapov's plateaued class has a common nonzero spectral magnitude. The signs tested above already meet the earlier divisibility range with multiple nonzero magnitudes. The spectral concentration result of Kelman and coauthors gives a natural comparison with an exponent of order $I\log(1+I)$ at fixed error. Removing that logarithm remains the hard part on XOR matrices. |

I used the public AI-proofs catalogue to locate related entries and used the linked primary manuscripts for the mathematical statements. The public #71a compilation lists the earlier Numaro threshold $6.521845710923046575$ for the universal constant. The stronger finite number quoted in this report is the local Round 1 certificate. [AI-proofs catalogue](https://github.com/subroy13/awesome-ai-proofs) · [Public #71a table](https://teorth.github.io/optimizationproblems/constants/71a.html)

**Single target for Round 5 of 5.** Prove or refute $\log_2 r_{1/4}(M)\le K(I_X+I_Y)$ for normalized Boolean sign matrices with the two physical cubes as axes. A concrete opportunity is to extend the common orthogonal basis from (4.8) to columns whose row features overlap. It suffices to capture three quarters of the average squared column norm in one subspace of dimension $2^{O(I_X+I_Y)}$. The guarded examples specify the necessary credit from the other side, the rank-two examples price rare rows and rare columns sharply, and the XOR tensor-power converse converts a uniform estimate into the full frozen theorem.

**Reproduction.** Run the following in the repository root. The first five commands exercise the new results. The Lean build checks the grid-energy sandwich, its FEI equivalence and the binary entropy lemmas. An axiom audit of `fourierGridEnergy_bounds`, `fei_iff_grid_bound`, `gridLayer_tail_zero` and `rank_two_entropy_scalar` returned only `propext`, `Classical.choice` and `Quot.sound`. The frozen challenge SHA-256 is `6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b`.

```sh
python3 -B scripts/max4_reserve.py
python3 -B scripts/max4_rank.py
python3 -B scripts/max4_reporting.py
python3 -B scripts/max4_tournament.py
python3 -B scripts/max4_signings.py
lake build
shasum -a 256 FEI/Challenge.lean
```

## MAX Round 3

**Case C.** This round gives a tree formulation of FEI in terms of crossing dyadic midpoints. A balanced Boolean family rules out bounding the sum of those crossings over all candidate queries at a node. The global bounds on $B$ and $X/I$ are both open here. We prove a uniform bound on $P_2/I$, hence on $X/I$, for several classes allowing linear data coding. In particular, $P_2<60I$ for nonconstant quadratic lookups on affine cells with distinct parity labels, even after an arbitrary linear recoding of all address and data bits. The best certified finite ordinary $H/I$ in this project is still the Round 1 interval $[6.5218511673478223969022,6.5218511673478223969023]$.

Throughout this section, $a_S=\widehat f(S)$ is normalized, $p_S=a_S^2$, $K=|S|$ and $I=\sum Kp_S$. All logarithms measuring information are in bits. Write $\ell_i=\log_2(1+p_{S-i}/p_S)$ on supported incidences and $A=\sum_{i\in S}\ell_i$. The numerator of $B$ is $\sum_{K\ge2}p_S A(S)$ and its denominator is $\sum_{K\ge2}Kp_S$. The pooled second moment is $P_2=\sum_{K>0}p_S A(S)^2/K$. Its cross terms comprise $X$. Numerical intervals below use integer Walsh coefficients and outward rational logarithm bounds.

### What the isoperimetric deficit controls

Fix a coordinate subcube $C$ by setting $d\ge3$ bits to zero, with $\mu=2^{-d}$. Let $A$ have the same measure, $D=A\triangle C$, $\rho=\Pr(D)$, $h_U=1-2\mathbf1_U$, and $\varepsilon=I(h_A)-2d\mu$. Write $D_u$ for the section at fixed-bit assignment $u$. There is an exact overlap formula,
$$
\varepsilon=I(h_D)-4\mu\sum_{i=1}^d\Pr_y(D_0\triangle D_{e_i}).
$$
On a crossing edge the sign of $h_A=h_C h_D$ changes precisely when one factor changes. The edges on which both change have base assignments $0,e_i$, each of measure $\mu$. Equal volume gives $\Pr_y(D_0)=\sum_{u\ne0}\Pr_y(D_u)=\rho/(2\mu)$. Thus $I(h_D)\le\varepsilon+2(d+1)\rho$. If $\rho\le\mu^3$, edge isoperimetry also gives $I(h_D)\ge2\rho\log_2(1/\rho)\ge6d\rho$. Absorbing the overlap proves
$$
 I(h_D)\le\frac{3d}{2d-1}\,\varepsilon\le\frac95\,\varepsilon.
$$
The zero-defect case follows directly. This controls the entire boundary of the perturbation. Stability theorems supply geometric proximity to extremizers under small excess. The next example specifies what may still occur inside that neighborhood. [Ellis](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/almost-isoperimetric-subsets-of-the-discrete-cube/3E878F4F45A483ADE934A011884FC716) · [Ellis–Keller–Lifshitz](https://arxiv.org/abs/1702.01675) · [Keevash–Long](https://ora.ox.ac.uk/objects/uuid%3A621130cf-eed4-456d-b640-0dcd4fabf5cd)

For an arbitrary free-bit event $E$, move the occupied vertex in each outer fiber from $0$ to $e_z$ precisely on $E$. Each fiber still has one occupied vertex. The data boundary and the signed slice from Round 2 obey
$$
 \rho=2\mu\Pr(E),\qquad \varepsilon=2\mu I(h_E),\qquad
 b_V=-2\mu\widehat{\mathbf1_E}(V),\qquad
 \mathcal E_z(A,C)=4\mu^2\mathcal E(E).
$$
Here $\mathcal E(E)$ includes only deletions with nonempty parent, as in Round 2. Both amplitudes on each retained edge have the same multiplier. In particular, for positive deficit the ratio is exactly $2\mu\mathcal E(E)/I(h_E)$.

**Even fixing $d=3$ and requiring the added and removed islands each to be connected leaves the single-slice question equivalent to FEI.** Under failure of FEI, the two-copy mask of Round 2 gives events $E_j$ with $I(h_{E_j})\to0$ and $\mathcal E(E_j)\to\infty$. Indeed its retained edges between two active balanced copies contribute $2\delta N(f)$, with both child and parent nonempty. Introduce a fresh bit and take a set $J_j$ whose lower face is full and whose upper face is $E_j$. This connects every upper vertex to the lower face. The full defect is also connected, since the two copies of the island touch across the $z$ edges. For each retained data edge there are two frequency copies, with both endpoint magnitudes halved. Thus $\mathcal E(J_j)\ge\mathcal E(E_j)/2$ and $I(h_{J_j})=I(h_{E_j})/2+1-\Pr(E_j)$. Multiply $\mathbf1_{J_j}$ by the indicator of a point on $w$ fresh bits to obtain the final island. Its boundary is $2^{-w}(I(h_{J_j})+2w\Pr(J_j))$, it stays connected, and summing the $2^w$ copies retains at least $2^{-w}\mathcal E(J_j)$. A **fixed** sufficiently large $w$ makes both tolerances hold for all large $j$, and the inherited slice still diverges. In the other direction $\mathcal E_z\le N(h_A)\le H(h_A)$ and FEI would bound the slice. The stability information controls the size and boundary of an island while allowing this arbitrary internal gate. An exact finite instance at $d=3,w=14$ has $\rho=45/4194304$ and $\varepsilon=175/524288$, both below $1/512$. [Section identities and connected-island WHT tests](scripts/max3_stability.py)

### What signed congruences enforce at each precision

For each nonzero $a_s$, write $j_s$ for its reduced dyadic denominator exponent. At precision $m\ge0$ let $V=\{s:j_s>m\}$, $e_s=j_s-m$, and join two copies of $V$ by an edge $t\sim v$ precisely when
$$
 2^m\sum_{s\supseteq t\cup v}a_s\notin\mathbb Z.
$$
**There is a perfect matching, and there is a transport with $e_s$ units of capacity at each copy of $s$.** Every edge satisfies $|t\cup v|\ge m+2$, by the signed coface congruence. The empty coface sum is $f(0)$, an integer.

To prove both assertions put $M=\bigoplus_{s\in V}\mathbb Z/2^{e_s}\mathbb Z$. The form $\sum_s 2^m a_s x_sy_s\bmod1$ on $M$ is perfect because each diagonal entry has odd reduced numerator. Write $u_t(s)=\mathbf1_{t\subseteq s}$. The form on $u_t,u_v$ gives exactly the adjacency test because discarded coefficients contribute integers. For any $B\subseteq V$, the subgroup generated by its rows projects onto $M_B$, by lifting representatives and solving the unit triangular incidence system over $\mathbb Z$. Write $N$ for its neighbors. The same argument gives surjectivity onto $M_{V\setminus N}$ for the rows outside $N$. Their annihilator therefore injects into $M_N$ by coordinate projection and contains the span of the rows of $B$. Consequently $M_B$ is a quotient of a subgroup of $M_N$. Taking orders gives $\sum_B e_s\le\sum_N e_s$. Taking minimum generator counts gives $|B|\le|N|$, since the generator count of a finite abelian 2-group is the dimension of its 2-torsion and cannot increase in a subgroup or quotient. Apply Hall, respectively to expanded copies and single vertices. The binary independence argument for the finest plane has a precedent in Potapov's proof. The finite-group argument retains different precisions in one pairing. [Potapov, §3](https://arxiv.org/html/2609.21563v1) · [Explicit matching tests](scripts/max3_grids.py)

**The transport cannot in general preserve squared amplitudes, even on the larger graph $|t\cup v|\ge m+2$.** Take $z\,{\rm Maj}_{2b+1}$ with an independent sign $z$. Its maximum amplitude is $c=\binom{2b}{b}/4^b$. Indeed, the derivative in any majority bit is, up to sign, a central-layer indicator of measure $c$, and the singleton coefficients attain $c$ before the tag. The total mass at degree two is $(2b+1)c^2\to2/\pi>1/2$. The largest $m$ with $2^{-m}\ge2c$ tends to infinity. The squared distance of every coefficient to the grid at this scale equals its squared amplitude. Two degree-two vertices have union of size at most four, so a self-coupling supported on eligible edges cannot carry these masses when $m\ge3$, since it would send more than half the mass into less than half. At $2b+1=4095$ the degree-two mass is in $[.63669750,.63669751]$ and $m=5$. [Exact central-layer and dense checks](scripts/max3_grids.py)

There is also a stronger unsigned test. For an affine frequency flat $F$ of codimension $r\ge1$, $S\in F$, let $h=2^{1-r}$ and $t=a_S\bmod h\in[0,h)$. Then
$$
 p(F)-a_S^2\ \ge\ t(h-t).
$$
The partial Walsh coefficient on the $r$ physical directions, multiplied by the appropriate remaining character, is $h\mathbb Z$-valued, has mean $a_S$ and second moment $p(F)$. If $a_S\in[jh,(j+1)h]$, average $(Y-jh)(Y-(j+1)h)\ge0$ and subtract the squared mean. The dyadic construction below passes even this conditional variance test. [Grid variance tests](scripts/max3_grids.py) · [Formalized scalar inequality](FEI/ResearchLemmas.lean)

### A two-shell vector that survives the finer signed tests

There are unit **real** Walsh vectors with divergent $B$ and $X/I$ which satisfy the matchings at every precision, the affine variance tests at every codimension, and the signed flat congruences at every codimension above $O(k\log k)$. This improves the relaxation in Round 2, where a single parity count at the finest bit sufficed to exclude every signing.

Take $k=4^b$, $n=k^2$, and append a mandatory balancing bit to the $n$ core frequencies. Put $\beta=2^{-s}$, $d=(n+s)/2$, and start every supported numerator at $1$ in units of $2^{-d}$. We use $s=\log_2 k$, or $s=2\lfloor\lfloor\log_2\binom n{k-1}\rfloor/8\rfloor$ for a thinner floor. In each shell $j=k-1,k$ let $M_j=\binom nj$ and $D=(4^d-2^n)/2$. Pair its coefficients and replace each pair by $(1+b,1-b)$. This adds $2b^2$ units of squared mass and preserves the signed sum. Both shell sizes are even since $n$ is a power of two. Set $u_j$ to the largest power of two at most $\sqrt{D/M_j}$. Start all pairs with $b=u_j$, and upgrade $\lfloor(D-M_j u_j^2)/(6u_j^2)\rfloor$ pairs to $b=2u_j$. The deficit on that shell is less than $6u_j^2$.

Fill the remaining deficit on degree-two pairs using increments $2\cdot4^e$ in decreasing order. With $t=\min(\log_2 u_{k-1},\log_2 u_k,\lfloor(n-1)/2\rfloor)$ the deficit is divisible by $2\cdot4^t$, including its initial term $4^d-2^n$. At most three pairs per exponent suffice by base four. There are $O(n)$ pairs needed and $\binom n2$ positions available for large $k$. This gives exact Parseval. All supported numerators are odd and congruent to $1\bmod 2^t$. At every $m<d$, complementation of the core coordinates within the tagged slice is a signed-graph perfect matching because each union is the whole tagged set, whose coface has only the unchanged top coefficient. The capacities $d-m$ are constant. At $m\ge d$ the active set is empty.

An affine flat of ambient codimension $r$ meeting the support contains at least $2^{n-r}$ of its points for $r\le n$. Its baseline signed sum belongs to $2^{1-r}\mathbb Z$, since $d\le n-1$. Every correction belongs to that grid if $r\ge d-t+1=O(\log M_k)=O(k\log k)$. Larger codimensions giving a finer grid are automatic. The largest amplitude is $O(M_{k-1}^{-1/2})$ by construction, including the degree-two fill, and is at most $\beta/2$ for both choices of $s$ for large $k$. Thus all shifted Chang tests of Round 2 hold. To check the stronger variance test put $h=2^{1-r}$. When $h\ge2|a_S|$ the necessary total is $a_S^2+t'(h-t')=h|a_S|$, where $t'=a_S\bmod h$. The floor alone gives $p(F)\ge\beta h/2$. If $h<2|a_S|$ and $r\le d$, the *other* points have mass at least $\beta h/4\ge h^2/4$. For $r>d$ the variance correction is zero. Missing amplitudes impose no additional cost.

The upper shell has mass at least $(1-\beta)/8$. Each of its $k$ core parents has squared odds at least $M_k/(144 M_{k-1})=(n-k+1)/(144k)$, using $u_j>\sqrt{D/M_j}/2$ and $u_j-1\ge u_j/2$ for large $k$. Meanwhile $I\le1+k+\beta n/2+2=O(k)$. This shell forces $B=\Omega(\log k)$ and $X/I=\Omega(\log^2 k)$ for the **constructed vector**. At $k=256$ the thicker floor gives certified lower bounds $B>2.002211$ and $X/I>11.964215$. Its signed flat congruences already hold at every codimension $r\ge1208$ out of 65,537 dimensions.

The displayed signs have inverse value $2^{n-d}>1$ at zero. Moreover, for the **thin** floor every signing is impossible for all sufficiently large $k$. Remove the tag. The squared tail past degree $k$ is at most $\beta=2^{-\Theta(k\log k)}$. The cube theorem of Keller–Klein would give squared distance $O(\beta)$ to a Boolean sign of degree at most $k$ (apply their indicator theorem and rescale). In their error term $\beta(2e\ln(1/\beta)/k)^k=o(1)$ for this choice of $\beta$. Each coefficient of the approximating sign on the upper shell belongs to $2^{1-k}\mathbb Z$ by the degree granularity argument of Round 2. Our coefficients there have magnitudes $O(M_k^{-1/2})<2^{-k}$. Their total squared distance to that grid is the entire shell mass, bounded below by $(1-\beta)/8$. This contradicts Parseval. For the thicker floor $\beta=1/k$ the approximation theorem's hypothesis fails. We have neither a Boolean signing nor a sign-independent exclusion there. [Keller–Klein, cube Theorem 1.7](https://arxiv.org/html/1901.08839v1) · [Integer construction, WHT inversion and exact shell certificates](scripts/max3_grids.py)

**A dual obstruction applies even to the thicker floor.** Any assignment of signs to the prescribed magnitudes can be written $2^{-d}\sigma(S)A_S$, where $A_S$ are the signed odd numerators above and $\sigma$ is a Boolean sign on the core frequency cube. Write $H_\sigma(x)=\sum_S\sigma(S)\chi_S(x)$, with no normalization. A Boolean inverse $f$ would give
$$
  2^d f(x)=H_\sigma(x)+P(x),\qquad
  P(x)=\sum_S \sigma(S)(A_S-1)\chi_S(x),\quad \deg P\le k .
$$
Let $a$ be the exponent of the largest power of two dividing every $H_\sigma(x)$. Then
$$
 t\le a\le k+\log_2 u_k<n/2
$$
for all sufficiently large $k$, for both floor sizes. The first inequality follows by reduction modulo $2^t$. For the second, fix an upper-shell $R$ with increment $u_k$ in absolute value. At least one such pair remains by the choice of the lower power. On every $R$-face the alternating sum of $P$ equals $\pm2^ku_k$, since no other supported monomial contains $R$. Hence $2^{\min(a,d)}\mid 2^ku_k$. Since $k+\log_2 u_k\le d+k-\tfrac12\log_2 M_k<n/2\le d$ for large $k$, this proves the bound. In fact some $H_\sigma$ on **each** such face fails divisibility by $2^{k+1}u_k$. A plateaued phase has constant nonzero Walsh magnitude $2^j$ with $j\ge n/2$, by integer Parseval. Thus this excludes every plateaued residue phase, including every quadratic phase and its linear recodings. At $k=4$ the upper bound on $a$ is already six, compared with eight for bent phases. Nine alternating integer-WHT projections started from a bent and a cubic phase yielded genuine tagged Boolean gates with $B$ in $[.7671583,.7671584]$ and $[.7820097,.7820098]$ respectively. Neither reconstructed the prescribed squared law. [Dual divisibility, face tests and Boolean projections](scripts/max3_phases.py)

There is a separate obstruction to a coded lookup realizing these magnitudes. Suppose a core function is affine as a sign on every coset of an $r$-dimensional physical subspace $V$, with the affine function allowed to depend on the coset. Let $\pi$ restrict frequencies to $V$. For any function,
$$
 \sum_{\lambda\in V^*}\max_{\pi S=\lambda}|a_S|
 \le\mathbb E_{\text{cosets }Y}\|\widehat{f|_Y}\|_1 .
$$
Each full coefficient is a signed average of partial coefficients at the same $\lambda$. For an affine sign the fiber norm is one. Among the core frequency basis vectors, choose $r$ whose images are independent. Their $k$-subsets give $\binom rk$ different labels, each containing an upper-shell amplitude of magnitude at least $(u_k-1)2^{-d}\ge1/(8\sqrt{M_k})$ for large $k$. Hence $\binom rk\le8\sqrt{\binom nk}$ and $r=O(\sqrt{nk})=O(k^{3/2})$. This excludes a linear address/data split with a positive fraction of the $k^2$ coordinates entering affinely, in **any** linear basis. At $k=256$ the exact amplitude bound gives $r\le2637$ out of 65,536 core coordinates. The same inequality lower-bounds the mean fiber spectral norm for nonlinear data. [Partial-transform and dimension checks](scripts/max3_phases.py)

### Linear coding of data in symmetric and composed gates

We use the following inverse-degree surprise estimate for a spectral law. Write $s(S)=-\log_2 p_S$ on its support and put $U=\sum_{K>0}p_S s(S)^2/K$. For any law on subsets,
$$
 \sqrt{P_2}\le\sqrt U+\sqrt{2I}/\ln 2. \tag{1}
$$
Indeed, expose membership bits in a fixed order. On present bits let $h_i$ be minus the log of the conditional presence probability given the prefix. Then $\sum_{i\in S}h_i\le s(S)$. Summing over the full outside of bit $i$ gives $\mathbb E[\mathbf1_{i\in S}2^{\ell_i-h_i}]\le\Pr(i\in S)$, as the outside marginal times the prefix presence probability sums to that marginal presence probability. Markov and integration give $\mathbb E\sum_{i\in S}(\ell_i-h_i)_+^2\le2I/(\ln2)^2$. Apply Cauchy–Schwarz on each set and the triangle inequality. This argument allows arbitrary recodings of the support.

**Coded block symmetry.** Suppose a Boolean sign is symmetric within $r$ nonempty blocks. Substitute independent signed parity forms for all inputs, and optionally multiply the output by any character. In the resulting coordinates, uniformly in the block sizes, the number of physical bits and the recoding,
$$
 P_2\le\left[\sqrt{4352r}\,(17/\ln2+1)+2r+\sqrt{20}+2\sqrt2/\ln2\right]^2 I. \tag{2}
$$
Here independence means full row rank over $\mathbb F_2$. The spectrum undergoes an injective affine map and its probabilities are permuted onto its image. Native coordinate symmetry need not survive in the resulting truth table.

For the proof let $W_{\mathbf k}$ be the native masses at block counts $\mathbf k$. Within each profile the native spectrum is uniform. In a native block of length $l$ put $j=\min(k,l-k)$, $J=\sum W_{\mathbf k}j$ and $Q=\sum W_{\mathbf k}k(l-k)$. The estimate uses degree measured from either end of the block,
$$
 \sum_{\mathbf k:j>0} W_{\mathbf k} j\log_2^2(el/j)\le (17/\ln2)^2 J. \tag{3}
$$
For $l\ge2$ take the half-difference $D=(f(x)-f(x+e_u+e_v))/2$ for a pair in this block. Its Fourier multiplier selects exactly one of $u,v$. Noise the other $l-2$ bits of the block by keeping each with probability $\rho$. With $b$ refreshed fair bits, $D$ vanishes when the two specified bits differ. When they agree, its conditional expectation is at most the total variation between a binomial $(b,1/2)$ and its translate by two, at most $2/\sqrt{1+b}$ by unimodality. Since $|D|=D^2$, summing the noise correlations over pairs and using $\mathbb E[(1+b)^{-1}]\le1/((l-1)(1-\rho))$ gives
$$
 \sum_{0<k<l} k(l-k)W_{\mathbf k}\rho^{k-1}
 \le 2Q/\sqrt{(l-1)(1-\rho)} .
$$
Multiplication by the parity of this whole block interchanges $k$ and $l-k$ and preserves symmetry and $Q$. Take $\rho=1-1/d$ for integer $d\ge1$ and use both orientations, with $(l/2)j\le k(l-k)\le lj$. Under the $jW/J$ law this gives $\Pr(j\le d)\le32\sqrt{d/l}$, with $d=1$ following from the surviving $k=1$ term. Integration gives $\mathbb E\ln^2(l/j)\le256$, proving (3). Blocks with $J=0$ contribute zero.

Select a full-rank square minor of the affine injection's linear part. Expanding its determinant by the native column blocks partitions its output rows into disjoint sets, one per block, with invertible square submatrices on their own block. Conditional on all other native bits and the profile, the $l$ selected output bits for a block thus distinguish its $\binom lj$ equiprobable points. For $j\ge1$ the chance of output weight at most $j/32$ on these rows is at most
$$
 \frac{\sum_{a\le j/32}\binom la}{\binom lj}\le2^{-j/2}.
$$
For $j<32$ the numerator is one. Otherwise bound it by $(32el/j)^{j/32}$ via the binomial generating function and use $\binom lj\ge(l/j)^j$, $l/j\ge2$. It follows that the selected rows have mean weight at least $j/128$. The entire output weight $K'$ has $\mathbb E[\mathbf1_{K'>0}/K'\mid\mathbf k]\le34/j$ for each positive $j$, interpreting the integrand as zero at zero. By disjointness $\sum_b J_b\le128I$.

For completeness, the possible bias costs a universal amount. If the rarer output sign has measure $\delta>0$, put $d=\log_2(1/\delta)$ and $q_S=\widehat{\mathbf1_E}(S)^2/\delta$. Bonami–Beckner at noise $1/\sqrt2$ gives $\mathbb E_q 2^{-K'}\le2^{-d/3}$. Hence $\mathbb E_q[\mathbf1_{K'>0}/K']\le6/d+2^{-d/6}\le10/d$. Writing $v=\Pr_p(K'>0)=4\delta(1-\delta)\ge\delta$, nonempty masses are $4\delta q_S$. Edge isoperimetry gives $2\delta d\le I$, so the squared contribution of the constant surprise $\log_2(1/v)$ to $U$ is $\le20I$. Constant signs satisfy (2) directly.

Let $W'$ be the law of the native profile conditional on $K'>0$. Its unconditional mass satisfies $W\ge vW'$. The profile weights $q(\mathbf k)=2^{-2r-\sum_b j_b}$ sum to at most one since there are at most two choices of $k_b$ for each $j_b$. Thus $(\log_2(q/W'))_+$ has conditional second moment at most $2/(\ln2)^2$. The entire surprise is $\log_2(1/W)+\sum_b\log_2\binom{l_b}{j_b}$. Bound the first term by $\log_2(1/v)+2r+\sum_bj_b+(\log_2(q/W'))_+$. For the binomial terms, Cauchy–Schwarz across blocks, the reciprocal bound and (3) give squared cost at most $34r(17/\ln2)^2\sum_bJ_b$. The $\sum_b j_b$ term costs at most $34r\sum_bJ_b$. Combine in $L^2(p\mathbf1_{K'>0}/K')$, using $v\le I$, then use (1). This yields exactly (2). [Pair-derivative noise, profile, pivot-volume and recoded WHT checks](scripts/max3_symmetry.py)

This includes a symmetric function of an arbitrarily long list of parity inputs with **bounded linear redundancy** $t$. Choose a basis from the list and absorb its signs in the free coordinates. The $t$ dependent forms are affine in those coordinates. Group the free coordinates by their column patterns in the $t$ forms and their original block, obtaining at most $r2^t$ symmetry blocks. A translation on the independent inputs only changes Walsh signs. Apply (2) with the new block count. Unbounded redundancy permits even an arbitrary Boolean gate as a threshold of a multiset of signed parities, by clearing denominators in its Walsh expansion, duplicating terms, and absorbing its constant term in the threshold. Uniformity in $t$ for that entire class would require a global result. [Dependent parity threshold tests](scripts/max3_symmetry.py)

**Linearly recoded disjoint gate towers.** Fix a finite alphabet of noncharacter balanced gates. Take any full, uniform-depth tree of disjoint substitutions from this alphabet, with gates allowed to vary from node to node. Allow arbitrary invertible linear changes of the leaf variables at each subtree prior to its use, input translations, and a final output character. Then $P_2\le C_{\rm alphabet} I$ independently of depth and of the linear maps. Changes on disjoint child domains form a block diagonal leaf transformation. Composition with the parent's change gives a single leaf transformation at the root. A bounded-arity linear recoding of a local gate can also be included in the finite alphabet. Reuse of overlapping child domains is a separate operation.

Let $b$ be the maximum arity, $q<1$ the largest spectral atom of any gate, $L$ the maximum nonzero atom surprise and $\lambda=\min I(g)>1$. The last strict inequality follows since a balanced gate with $I=1$ is supported at level one, and squaring a degree-one sign forces all products of distinct linear coefficients to vanish. A frequency sample follows a tree in which each active gate independently chooses its active children with its own spectral law. Every active node has a child by balance. The final set therefore determines the genealogy, with probability equal to the product of the local masses. Let $Z_l$ count the nodes at level $l$, $M=Z_{D-1}$ the number of bottom gates and $V=\sum_{l<D} Z_l$. The surprise is at most $LV$.

Conditional on the genealogy above the bottom, there are $M$ independent final samples with largest joint atom at most $q^M$. They occupy a native linear coordinate space of dimension at most $bM$. Select a full-rank output projection on that space. A Hamming ball of radius $cM$ in this projection contains at most $2^{bM h_2(c/b)}$ possible samples, even after an affine shift. Choose $c>0$ so small that $2^{b h_2(c/b)}\le q^{-1/2}$. Then $\Pr(K'\le cM\mid{\rm genealogy})\le q^{M/2}$. It follows that $\mathbb E[K'\mid{\rm genealogy}]\ge c(1-\sqrt q)M$ and $\mathbb E[\mathbf1_{K'>0}/K'\mid{\rm genealogy}]\le C_q/M$, since $Mq^{M/2}$ is bounded. Also $Z_l\le M$ pointwise and $\mathbb E Z_{l+1}\ge\lambda\mathbb E Z_l$. Minkowski gives
$$
 \|V/\sqrt M\|_2\le\sum_{l<D}\sqrt{\mathbb E Z_l}
 \le \sqrt{\mathbb E M}/(1-\lambda^{-1/2}).
$$
Together these bound $U/I$ and (1) proves the assertion. For the recoded five-bit bent-times-dictator gate used at both levels, a shear crossing the five data blocks gives $I=13/2$ and $U/I\in[5.03958362,5.03958363]$ on 25 bits by exact convolution. Mixed three/five-bit towers also admit a complete truth-table WHT and agree with the factorization. The constants depend on the alphabet. [Tower verifier](scripts/max3_towers.py)

**Reversible routing on the same data.** At each fresh address bit choose one of two invertible linear maps on the same data coordinates, then evaluate a fixed base sign. Track the distinct Boolean truth tables produced by partial compositions in application order, where the next step composes the current table with one of two maps on the right. The possible states are permuted by each map on the whole finite orbit. If the final number of reachable distinct states is $w$, the support size is nondecreasing. Its minimum positive probability can halve only on a strict increase. At an equal-size step each of the two branches maps onto the new support, so every resulting state has probability at least the preceding minimum. Thus every reached state has probability at least $2^{1-w}$. Let $\delta$ be the least positive disagreement distance between the relevant distinct states (including the two successors of each query), and $\alpha$ the least positive final-state data-bit influence. Omit an empty minimum. Future common maps preserve Hamming distance. Every active query or data bit has influence at least $\eta=2^{1-w}\min(\delta,\alpha)$. For any coordinate under its own marked-incidence law, $\mathbb E2^{\ell_i}\le1/I_i$ by summing each outside marginal once. Integrating the positive tail above $\log_2(1/\eta)$ and applying Cauchy–Schwarz on each set gives
$$
 P_2/I\le\big(\log_2(1/\eta)+\sqrt2/\ln2\big)^2 .
$$
For a base sign of algebraic degree at most $b$ over $\mathbb F_2$, one can take $\delta\ge 2^{-b}$ and $\alpha\ge2^{1-b}$ whenever positive. The difference polynomials have degrees at most $b$ and $b-1$ respectively. A nonzero multilinear bit polynomial of degree $d$ is nonzero on at least $2^{-d}$ of the cube by induction on a variable in a leading monomial. Thus bounded-width programs of bounded algebraic degree allow arbitrarily many stages of actual data reuse. At depths $2,5,9$ the tested controlled shears of the five-bit quadratic gate had $4,12,128$ reachable states and $X/I$ respectively in $[.19631945,.19631946]$, $[.07900021,.07900022]$, and $[.13660120,.13660121]$. [Shared-data programs and exact marginal checks](scripts/max3_codes.py)

**Code-shell searches.** For $v\in\mathbb F_2^n$, the directional influence is $\alpha(v)=(1-\sum_S p_S\chi_S(v))/2$. The least possible influence over all invertible input recodings is the sum of a minimum-weight binary linear basis with these costs, computable exactly by greedy elimination. A character modulation can replace $\alpha(v)$ by $1-\alpha(v)$. Optimizing even this choice independently on each basis vector gives a lower bound for the balanced-only search. For a unate function and $v_i=1$, pairing $x$ with $x+v$ gives $|\hat f(\{i\})|\le\alpha(v)$. Unateness gives $|\hat f(\{i\})|=I_i(f)$. Every invertible basis matrix has a nonzero permutation term in its determinant, so its cost is at least the original $I$. In particular, unmodulated linear changes of inputs cannot improve the ordinary entropy ratio of the monotone seed.

For the binary Hamming $[7,4,3]$, BCH $[15,7,5]$, and Reed–Muller $\mathrm{RM}(1,4),\mathrm{RM}(2,4)$ codes, we searched every output sign depending on codeword weight, every balancing character on the **message bits**, and every invertible change of message basis. Here the objective was the amplified score $H/(I-1)$ of a balanced noncharacter gate. The joint maximum was in $[4.697291787712,4.697291787713]$, attained for a BCH gate with minimized $I=25/16$. Safe interval pruning is used only for this score. For $B$ and $X/I$ we separately evaluated all 26,040 balanced presentations from nonconstant Hamming code weight patterns modulo negation and coordinate permutation, including repeated functions. Constant weight patterns add only characters with zero losses. The respective maxima are in $[.998199172,.998199173]$ and $[.183219559,.183219560]$. The direct objectives on the other codes were tested on selected recodings only. [Exact influence optimization](scripts/max3_codes.py) · [Direct deletion-odds search](scripts/max3_code_odds.py)

**A uniform bound with all address and data bits recoded together.** Partition address space into disjoint affine cells $C_j$ of codimensions $r_j$. On cell $j$ return $(-1)^{Q_j(x)}\chi_{\lambda_j}(y)$, where $Q_j$ is quadratic on that cell and the labels $\lambda_j$ are distinct arbitrary parities of the same data bits. After any full-rank linear substitution mixing address and data, and any output character, **$P_2<60I$ for every nonconstant resulting gate**. This includes multiple adaptive stages of affine address queries compiled into such a leaf partition. It allows different quadratics on the leaves and arbitrarily many dense, linearly dependent data labels. Distinctness of the final labels prevents coherent addition between cells.

To prove it, the native frequency piece for cell $j$ is selected with probability $2^{-r_j}$ and is uniform on an affine flat of dimension $d_j=r_j+q_j$, where $q_j$ is the rank of the quadratic polar form on the cell's tangent space. Indeed the squared transform of a quadratic sign on a vector space is $2^{-q_j}$ on a coset of the radical's annihilator and zero elsewhere, by summing first over the difference of two physical arguments. Extending from the cell adds its $r_j$ annihilator directions. Distinct labels keep the pieces disjoint, and affine frequency injection preserves each dimension. On the recoded flat, choose $d_j$ pivot coordinates. Their values are independent fair bits, so the output degree $K'$ dominates $D\sim\operatorname{Bin}(d_j,1/2)$ pointwise in this coupling. Then $\mathbf1_{K'>0}/K'\le 2/(1+D)$ with the quotient set to zero at zero. Its expectation is at most $4/(d_j+1)$. The surprise on this piece is $d_j+r_j\le 2d_j$. Consequently $U\le16\mathbb E d_j\le32I$, and (1) gives $P_2\le(\sqrt{32}+\sqrt2/\ln2)^2 I<60I$. This same proof applies to any disjoint affine-flat mixture whose piece of dimension $d$ has mass at least $2^{-d}$. It tolerates the equal-influence jump in $X$ from the five-bit example. [Full mixed-coordinate WHT and flat-by-flat checks](scripts/max3_towers.py)

### Peeling affine cells with a controlled tail

Suppose the rarer sign event $E$ of measure $0<\mu\le1/2$ is a disjoint union of affine subspaces of arbitrary orientations. Let $E_m$ be the union of its cells of codimension $>m$ and $\tau_m=\Pr(E_m)$. Then
$$
 U\le1280\sum_{m\ge0}(2m+1)\frac{\tau_m}{1+\log_2(1/\tau_m)}, \tag{4}
$$
with zero summands for empty tails. In particular, a presentation satisfying $\tau_m\le2^{-\gamma m}$, $0<\gamma\le1$, gives $P_2/I=O(\gamma^{-2})$ under arbitrary invertible physical recodings. This allows different orientations, unbounded codimensions and an unbounded number of cells. Closely related entropy estimates for one-sided affine certificates and weighted affine decompositions are due to Paraashar and Saurabh. Equation (4) controls the inverse-degree-weighted square of the surprise. [Paraashar–Saurabh, Theorems 4.1–4.3](https://arxiv.org/html/2611.06451v1)

Indeed, the coefficients of $\mathbf1_{E\setminus E_m}$ lie on $2^{-m}\mathbb Z$, since each affine indicator has coefficients zero or $\pm2^{-c}$ for its codimension $c$. If $b_S=\widehat{\mathbf1_E}(S)$ satisfies $0<|b_S|\le2^{-m-1}$, its distance to this grid is $|b_S|$, at most $|\widehat{\mathbf1_{E_m}}(S)|$. The inverse-degree noise estimate used in (2) bounds the sum of $b_S^2/K$ on these nonempty frequencies by $10\tau_m/\log_2(1/\tau_m)$. For $x=\log_2(1/|b_S|)\ge1$, $x^2\le4\sum_{m+1\le x}(2m+1)$. Sum this inequality with $p_S=4b_S^2$, $s(S)=2x-2$, and use $\tau_m\le1/2$ to obtain (4). Under the exponential tail, $(m+1)/(1+\log_2(1/\tau_m))\le1/\gamma$ and $\sum_m\tau_m\le\mu(\log_2(1/\mu)+3)/\gamma$ by splitting the geometric series at $\log_2(1/\mu)/\gamma$. Finish with $I\ge2\mu\log_2(1/\mu)$ and (1).

The tail hypothesis cannot hold with fixed $\gamma$ for every Boolean sign even after choosing the best one-sided affine partition. Every affine subspace of dimension $s$ contains a word of weight at least $s$ and one of weight at most $n-s$, by setting its $s$ free coordinates to all ones or all zeros. Either monochromatic side of odd majority therefore requires codimension at least $(n+1)/2$ in every cell. Its $\tau_m=1/2$ for $m<(n+1)/2$ makes the sum on the right of (4) grow at least quadratically in $n$, although its influence is $\Theta(\sqrt n)$. [Affine cell decomposition, shear and majority checks](scripts/max3_peeling.py)

### A signed restriction identity and the Round 4 target

For a dyadic step $h=2^{-m}$ let $r_h(u)=\operatorname{dist}(u,h\mathbb Z)$ and set
$$
 G(f)=\sum_{m\ge0}\sum_S r_{2^{-m}}(a_S)^2.
$$
This sum terminates on a finite Boolean cube. For $0<|u|\le1$ put $x=\log_2(1/|u|)$. The first $\lfloor x\rfloor$ terms equal $u^2$, and the remaining sum is at most $4u^2/3$ by the geometric series of squared half-steps. Thus the nonempty-frequency contribution is between $H_{\ne\emptyset}/2-v$ and $H_{\ne\emptyset}/2+4v/3$, where $v=1-p_\emptyset\le I$. For the empty coefficient, all grids contain $1$, so its error equals that of $s=1-|a_\emptyset|\le v$. Its total is at most $s^2(\log_2(1/s)+4/3)\le2v$ by continuity at zero. The empty entropy satisfies $-p_\emptyset\log_2 p_\emptyset\le v/\ln2$. In particular
$$
 H/2-2I\ \le\ G(f)\ \le\ H/2+10I/3. \tag{5}
$$

At a query $i$, let $u=a_T$, $v_i=a_{T+i}$ for $T$ in the remaining variables. The two restrictions have normalized coefficients $u+v_i,u-v_i$. The loss in grid energy is the sum over $T,h$ of
$$
 c_h(u,v_i)=r_h(u)^2+r_h(v_i)^2-
    \tfrac12\{r_h(u+v_i)^2+r_h(u-v_i)^2\}.
$$
It is nonnegative. The first two errors are half the optimal sum of squared errors on $u+v_i,u-v_i$ when the two rounded grid numerators must have the same parity, by the parallelogram identity. The remaining terms are the unrestricted optimum. If the nearest integers have the same parity the cost is zero. Otherwise the cheaper parity change costs
$$
 c_h=\tfrac h2\left(h-2\max\{r_h(u+v_i),r_h(u-v_i)\}\right).
$$
A tie costs zero. When $h>4|v_i|$, there is a positive cost only if the segment from $u-v_i$ to $u+v_i$ straddles a grid midpoint, and the formula simplifies to
$$
 c_h=h\big(|v_i|-\operatorname{dist}(u,h(\mathbb Z+\tfrac12))\big)_+ . \tag{6}
$$
Indeed the segment then contains at most one midpoint, with the more distant grid residual equal to $h/2$ minus the nearer endpoint's distance to the midpoint. **At most one** such dyadic $h$ contributes for a given pair. Midpoints at two distinct dyadic scales differ by at least half the smaller step, which exceeds $2|v_i|$. Every other scale is covered by
$$
 \sum_{h\le4|v_i|}c_h\le\sum_{h\le4|v_i|}h^2/2\le(32/3)v_i^2 .
$$

On any full coordinate-restriction tree $\mathcal T$, let $R_{\mathcal T}(f)$ sum (6) over the queried pairs with $h>4|v_i|$, weighting each node by its probability of being reached. At leaves the grid potential vanishes. The queried influences telescope to $I(f)$ because restriction on $i$ preserves, on average, every other bit's influence. Therefore
$$
 0\le G(f)-R_{\mathcal T}(f)\le(32/3)I(f),\qquad
 R_{\mathcal T}-10I/3\le H/2\le R_{\mathcal T}+38I/3 . \tag{7}
$$
This is a signed Walsh reformulation with an explicit error and a single possible coarse scale per pair. It holds for every order. The code checks exact potential drops and complete tree sums for fixed, random and adaptively chosen orders. For example, on one ten-bit truth table $G=17563/4096$, $I=1267/256$, and the fixed-order coarse sum is $279/1024$. [Integer nearest-grid and tree tests](scripts/max3_carries.py)

**Why the bound must allow amortization.** Take $n\ge4$ even, $N=2^n$, and $b(x)=(-1)^{x_1x_2+\cdots+x_{n-1}x_n}$. In the half $x_1=1$ keep $b(x)$. At each of the $N/2$ points $x_1=0$ return a distinct data sign $y_x$. Multiply by an independent tag to balance. On the empty data slice the amplitudes are those of $b\mathbf1_{x_1=1}$, zero at half the core frequencies and $\pm N^{-1/2}$ at the others, by the two-point difference of the bent transform. Each one-data-bit slice has all amplitudes of magnitude $1/N$. There are no larger data slices. Thus $H=3n/2$ and $G=3n/4$. Each data-bit influence is $1/N$. The core directions cost $1/2$ each except for bit $2$, which costs $3/4$ since it always flips $b$ on the retained half. With the tag, $I=n/2+7/4$.

For **each** data query the nonzero empty-data amplitudes are midpoints at step $h=2/\sqrt N>4/N$. Formula (6) gives total coarse cost exactly $1/\sqrt N$ at the root for that coordinate. Consequently summing over the potential data queries already costs $\sqrt N/2$, exponentially larger than $I$. This refutes both a uniform per-query bound proportional to its influence and a per-node bound on the sum over all candidate queries proportional to total influence. Equation (7) still gives $R_{\mathcal T}\le3n/4$ on any actual tree. In particular, with $n=16$ the root sum just over data queries is $128$, while $I=39/4$ and $G=12$. Along a fixed order of data queries the parent numerator at a given frequency acquires independent unit Rademacher increments, which explains why the initial midpoint charge cannot be reused at every stage. On the smaller single-selector bent switch the distinguished coarse-cost/influence ratio is $2^{n/2}$ as well. [Sparse WHT, dense reconstruction and exact binomial path sums](scripts/max3_selectors.py) · [Single-selector test](scripts/max3_carries.py)

**Even the accumulated influence of a whole query prefix can be insufficient.** Query all $M=N/2$ data bits first in any fixed order. Each still has influence $1/N$ when queried, since the address row it controls is untouched. Their total queried influence is exactly $1/2$. Yet their accumulated coarse cost satisfies
$$
 n/4-4/3\le R_{\rm data}\le n/4+8/3 .
$$
To verify this, use integer numerator units and write $H$ for an integer dyadic step from $8$ through $N$ in this paragraph. At a uniform core frequency let the initial parent be $s\in\{0,\pm\sqrt N\}$ with $\Pr(s=0)=1/2$. After the $M$ queries its law is $Y=s+W_M$, where $W_M$ is a simple symmetric walk independent of $s$ in law. Telescoping that single scale over the prefix gives its exact contribution
$$
 R_H=M/N+N^{-1}\mathbb E\big[r_H(s)^2-r_H(Y)^2\big].
$$
All scales in this sum are coarse for the queried coefficient $1/N$. For $H\le\sqrt N$, the initial residue vanishes. Each of these $n/2-2$ scales contributes between $1/2-H^2/(4N)$ and $1/2$, with total error at most $1/3$. For $H\ge2\sqrt N$, $r_H(s)^2=s^2$. Since $\mathbb E(Y^2-s^2)=M$, we obtain $R_H\le N^{-1}\mathbb E[Y^2\mathbf1_{|Y|\ge H/2}]\le 4\mathbb E Y^4/(NH^2)$. The fourth moment is $11N^2/4-N$ by the Rademacher fourth moment, giving at most $11/3$ summed over the larger steps. These estimates prove the bounds. The verifier independently computes the cost by visiting probabilities at each query and by this endpoint formula. [Exact selector-prefix checks](scripts/max3_selectors.py)

**Single target for Round 4 of 5.** Prove or refute $R_{\mathcal T}(f)\le K I(f)$ for the fixed reveal order $1,\ldots,n$. Equation (7) makes this sufficient and necessary for FEI. The quantitative question is how often the successive partial Walsh coefficients on one restriction path can approach a dyadic midpoint within the next increment, weighted by the height and penetration in (6). For each fixed surviving frequency those coefficients form a martingale up to the first query in that frequency. The prefix example forces the charge to use influence from still-unqueried coordinates. It also gives an exact test of any proposed amortization before tackling general Boolean terminal truth tables.

**Verification.** Run each of the ten linked Round 3 Python scripts directly with Python 3 and NumPy. Integer transforms check Parseval and physical edge counts where dense truth tables are used. Larger instances use the stated exact recurrences or multiplicities. Six new Lean lemmas prove nearest-grid optimality, nonnegativity and a per-scale upper bound for the restriction drop, the squared half-step bound, the finite signed-grid variance bound, and the scalar defect-bound absorption. The full mathematical estimates above are in this report. The project builds with Lean 4.36.0. The frozen challenge's SHA-256 is **6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b**. [Lean lemmas](FEI/ResearchLemmas.lean)

## MAX Round 2 · 26 November 2026

**Case C. Whether $\sup_{g\ {\rm balanced}}B(g)$ is finite remains open in this investigation.** We obtained a dimension-independent bound for the contribution of every fixed range of degrees to $B$, a bound $X<78I$ for all nonconstant symmetric Boolean functions, and an additive bound for repeated lookups with shared linear address bits. We also constructed a sequence of dyadic unit Walsh vectors with divergent $B$ and $X/I$. A signed congruence on one affine flat excludes **every** Boolean signing of these vectors. This exposes a gap in a proof using unsigned affine mass tests. The best certified ordinary $H/I$ witness here remains the Round 1 interval $[6.5218511673478223969022,6.5218511673478223969023]$.

The unrestricted mixed bound $X\le K I$ is still undecided. There is an exact dichotomy near a dictator. If the bound holds, $X$ goes to zero on the rare masks constructed below as their influence goes to one. If the bound fails anywhere, one can choose such masks for which **unnormalized $X$ tends to infinity**. For the original first-moment question, even an absolute bound on **one Fourier slice of a tiny perturbation of a subcube** would settle FEI. The Round 3 target below specifies that slice and gives its exact two-copy transfer.

Write $a_S=\widehat f(S)$, $p_S=a_S^2$, $W_k=\sum_{|S|=k}p_S$, $I=\sum kW_k$, $d_b=I-W_1$, and $K=|S|$. On the support of $p$ put
$$
\ell_i(S)=\log_2(1+p_{S-i}/p_S),\quad A(S)=\sum_{i\in S}\ell_i(S),\quad N(f)=\mathbb E_p A(S).
$$
The branching incidence law gives each $(S,i)$, $i\in S$, $K\ge2$, mass $p_S/d_b$. Its mean loss is $B$ when $d_b>0$. The full incidence law uses $p_S/I$. The mixed quantity $X$ sums $p_S\ell_i(S)\ell_j(S)/K$ over **ordered distinct** pairs. $P_2=\sum_{K>0}p_S A(S)^2/K$. The Round 1 reduction below gives $\sup B<\infty\iff{\rm FEI}$. A large incidence **mean** alone puts no positive lower bound on the fraction exceeding a fixed multiple of that mean. For example, multiplying a balanced gate by $m$ mandatory parity bits increases $I$ by $m$, leaves $N$ unchanged, and adds $m$ zero-loss incidences per sample. Applied conditionally to gates with $N/I=R\to\infty$, $m=\lceil I\sqrt R\rceil$ gives a diverging mean with a vanishing proportion of positive-loss incidences. [Tensor checks](scripts/max2_certificates.py)

### Why degree two cannot drive divergence

Let $V=D_i f$ on the remaining cube, and put $d_i=\operatorname{Var}V=I_i-p_{\{i\}}$. These quantities sum to $d_b$. For an independent copy $V'$ and $1\le q\le2$,
$$
 \mathbb E|V-\mathbb EV|^q\le\mathbb E|V-V'|^q
 \le\mathbb E(V-V')^2=2d_i .
$$
The first inequality is conditional Jensen. The second uses the integer differences of the ternary derivative. Write $u_T=a_T$, $v_T=a_{T+i}$ for $i\notin T$. Bonami–Beckner at noise $1/\sqrt2$ applied to $V-\mathbb EV$ gives $\sum_{T\ne\varnothing}2^{-|T|}v_T^2\le(2d_i)^{4/3}$. Applying Hölder with exponents $4/3,4$ to $(2^{-|T|}v_T^2)^{3/4}(u_T^2+v_T^2)^{1/4}$ and using $\sum_T(u_T^2+v_T^2)=1$ gives
$$
 \sum_{\substack{S\ni i\\K\ge2}}p_S\,2^{(\ell_i(S)-3(K-1))/4}\le2d_i .
$$
Consequently $\Pr_b(\ell>s,\ K\le D)\le\min(1,2^{1+(3(D-1)-s)/4})$. Integration gives **$B_{\le D}\le3(D-1)+4+4/\ln 2$**, where the denominator is the full $d_b$. This bound and every fixed-degree moment bound obtained by integrating the same tail are independent of arity and of proximity to a dictator. Moreover
$$
 \Pr_b(K\le D)\le 2^{D-1+4/3}\max_i d_i^{1/3}.
$$
Indeed, truncate the centered noise estimate at $D-1$, multiply by $2^{D-1}$, and sum over $i$. By Cauchy–Schwarz and the uniform second moment on this range, $B_{\le D}\to0$ whenever $\max_i d_i\to0$. This includes $W_1\to1$, since $d_i\le\sum_{k\ge2}W_k$. The unresolved contribution can escape to increasing $K$. [Centered WHT tests](scripts/max2_levels.py) · [Cube hypercontractivity](https://arxiv.org/abs/2105.10386)

There is a second obstruction to $W_1=1-\varepsilon$, $W_2\asymp\varepsilon$ as $\varepsilon\downarrow0$. Let $L=\sum_i a_{\{i\}}x_i$. From $(L^2-1)=(L-f)(L+f)$, Cauchy–Schwarz, and degree-one and degree-two hypercontractivity,
$$
 \|L^2-1\|_2^2
 \le\sqrt\varepsilon\,\|(L+f)(L^2-1)\|_2
 \le (1+3\sqrt3)\sqrt\varepsilon\,\|L^2-1\|_2 .
$$
Thus $4\sum_{i<j}p_{\{i\}}p_{\{j\}}\le39\varepsilon$. For $W_1\ge1/2$, this implies $\max_i p_{\{i\}}\ge W_1-39\varepsilon/(2W_1)\ge1-40\varepsilon$. After multiplication by the corresponding signed dictator, $f$ differs from $+1$ on a set of density $\delta\le20\varepsilon$. The original pairs shift to levels one and three. Applying noise $1/\sqrt2$ to this set's indicator gives $W_2\le 4\cdot2^3\delta^{4/3}$. The test checks these inequalities on signed WHTs, including the 18-bit seed, asymmetric tie cuts, a Tribes composition, and single-address dictator perturbations. For the latter $B_{\le2}$ falls from $[.352260,.352261]$ at 6 bits to $[.000436,.000437]$ at 18. [Integer and rational checks](scripts/max2_levels.py)

The proposed parent/child **scalings themselves do occur**. Let $h$ be the sign threshold at weight $t=\lfloor(n+\lfloor\sqrt n\rfloor)/2\rfloor$, positive below $t$. Its singleton coefficient is $c=\binom{n-1}{t-1}2^{1-n}$ and its pair coefficient is $c_2=c(n+1-2t)/(n-1)$ by differencing adjacent threshold layers. A selector choosing $h(x)$ or $-h(y)$ on fresh $n$-bit blocks balances the output. Its private singleton and within-block pair magnitudes are $c/2$ and $|c_2|/2$. With $\mu=\mathbb Eh$,
$$
 I=nc+(1+\mu^2)/2,\qquad W_1=\mu^2+nc^2/2,\qquad
 M=\tfrac12\binom n2 c_2^2 .
$$
Here $M$ is the two blocks' within-pair mass. Stirling's formula gives $M=\Theta(1)$, $I=\Theta(\sqrt n)$ and each pair has two losses $\ell=\log_2(1+c^2/c_2^2)=\Theta(\log n)$. The corresponding terms of $B$ and $X/I$ are $2M\ell/d_b$ and $M\ell^2/I$. At $n=4096$ these lie in $[.044615,.044616]$ and $[.263885,.263886]$, with $M\in[.058540,.058541]$. A constant $W_2$ in this example still accounts for a vanishing fraction of branching incidences. [Factorized and full-cube checks](scripts/max2_symmetric.py)

### Shifted Chang bounds and the diffuse parents

For each frequency $T$, the signed character shift of $f$ with positive mean equals $1-2\mathbf1_E$, where $\delta_T=\Pr(E)=(1-|a_T|)/2$. If $m_i$ is the mean of $x_i$ under the uniform law on $E$, entropy subadditivity gives $\sum_i[1-h_2((1+m_i)/2)]\le\log_2(1/\delta_T)$. The binary entropy deficit is at least $m_i^2/(2\ln2)$. Therefore
$$
 \sum_i p_{T\triangle\{i\}}\le8\delta_T^2\ln(1/\delta_T).
$$
For $|a_T|\le1/4$ the right side is at least $8(3/8)^2\ln(8/3)>1$, so the entire collection of these shifted inequalities already follows from Parseval there. At a nonempty heavy parent $|a_T|>1/4$ one can instead charge its children to branching influence. For $i\notin T$, $|a_{T+i}|\le\mathbb E|D_i f-\mathbb E D_i f|\le2d_i$. Since $\ln(1+r)\le\sqrt r$, that parent's charge is at most $2|a_T|d_b/\ln2$. Summing uses $\sum_{\rm heavy}|a_T|\le4\sum_T p_T=4$. **All heavy nonempty parents together contribute at most $8\log_2 e$ to $B$.** The dyadic construction below shows why doing more shifts with the same level-one bound cannot control the light parents. [All-center and heavy-parent tests](scripts/max2_levels.py)

### A uniform mixed-moment bound for symmetric signs

For a symmetric sign $f$, $D_i f$ at remaining weight $j$ is half the difference of consecutive radial signs. In the noise operator $T_\rho$, condition on the refreshed coordinates among the other $n-1$ bits. Their count is $b\sim\operatorname{Bin}(n-1,1-\rho)$. Conditional on those coordinates, the remixed weight is a shifted $\operatorname{Bin}(b,1/2)$. Its total variation distance to its unit shift is its central mass, at most $1/\sqrt{b+1}$, by unimodality and the central binomial bound. This bounds the absolute conditional mean of the derivative for every starting input, including radial tables with many sign changes. Cauchy–Schwarz and $\mathbb E(1+b)^{-1}=(1-\rho^n)/(n(1-\rho))$ now give
$$
 \sum_k kW_k\rho^{k-1}=\sum_i\mathbb E[D_i f\,T_\rho D_i f]\le I/\sqrt{n(1-\rho)}.
$$
Taking $\rho=1-1/d$ gives $\Pr_{\rm inc}(K\le d)\le e\sqrt{d/n}$ for $d\ge1$, including $d=1$ by direct evaluation. Hence $\mathbb E_{\rm inc}\ln^2(n/K)\le8e$ by integration. Symmetry makes the loss at $k\ge2$ equal to $\log_2(1+(n-k+1)W_{k-1}/(kW_k))$. It is at most $\log_2(n/k)+\log_2(1+W_{k-1}/W_k)$. The incidence expectation of $\mathbf1_{k\ge2}W_{k-1}/W_k$ is at most $\sum_{j\ge1}(j+1)W_j/I\le2$. Using $\ln^2(1+r)\le r$ and the triangle inequality in $L^2$ proves
$$
 \frac{X}{I}\le\mathbb E_{\rm inc}\mathbf1_{K\ge2}\ell_i^2
 \le\frac{(\sqrt{8e}+\sqrt2)^2}{(\ln2)^2}<78 .
$$
This strengthens the ordinary FEI conclusion on this class. The derivative noise method for symmetric gates and its antichain counterpart for thresholds have antecedents. The extra step here is the second-moment charge on adjacent level weights. [O'Donnell–Wright–Zhou](https://www.cs.cmu.edu/~odonnell/papers/fei.pdf) · [Shmalo, Lemmas 3.3–3.4](https://arxiv.org/html/2610.16069v1) · [Krawtchouk and dense WHT tests](scripts/max2_symmetric.py)

For a sign invariant under permutations within each of $r$ disjoint blocks, let $n_j,k_j$ be the size and occupied count of block $j$ at a marked incidence in that block. Refresh just that block in the same argument, holding all other inputs fixed. Normalizing by its influence gives $\|\ln(n_j/k_j)\|_2\le\sqrt{8e}$, also after averaging over the marked block. Use the multidegree weights $W_{\mathbf k}$. Under the full incidence law, $Z=\mathbf1_{K\ge2}W_{\mathbf k-e_j}/W_{\mathbf k}$ has mean at most $1+r$, since summing over the children of a nonempty parent counts at most $K_{\rm parent}+r$. Markov gives $\Pr(\ln(1+Z)>\ln(r+2)+s)\le e^{-s}$ for $s>0$. The same argument bounds
$$
 X/I\le\left((\sqrt{8e}+\sqrt2)/\ln2+\log_2(r+2)\right)^2 .
$$
The tests include 24 multiblock tables, all balanced symmetric tables at $n=6,8,10,12$, arbitrary radial signs to $n=128$, and the balanced two-branch thresholds above. [Radial and block checks](scripts/max2_symmetric.py)

There is a related deterministic bound **without symmetry**. Conditional on $K=k$ under the incidence law, the mean of $p_{S-i}/p_S$ is at most $R_k=(n-k+1)W_{k-1}/(kW_k)$ by counting every possible parent. Thus $(\ell_i-\log_2(1+R_k))_+$ has second moment at most $2/(\ln2)^2$ on that level. For an arbitrary nonconstant sign, putting $L_k=\mathbf1_{k\ge2}\log_2(1+R_k)$ on occupied levels gives
$$
 \sqrt{X/I}\le \|L_K\|_{2,{\rm inc}}+\sqrt2/\ln2
 \le \frac{\ln(n/I)+3\sqrt2}{\ln2}.
$$
For the last inequality apply the adjacent-weight estimate above and use $\Pr_{\rm inc}(K<I e^{-s})\le e^{-s}$, from $\sum_{k< I e^{-s}}kW_k\le I e^{-s}$. Thus any mixed divergence must also have vanishing influence per active coordinate after irrelevant variables are removed. The first bound can be stronger when adjacent level weights scarcely overlap. [Individual level-profile checks](scripts/max2_rounding.py)

### When many expensive label deletions occur at once

Consider $F(x,y)=h(x)\chi_{\Phi(x)}(y)$ with arbitrary Boolean sign $h$ and set-valued map $\Phi$. Write $U=\Phi(x)$, $\delta_U=\Pr(\Phi=U)$ and $q_U(T)=\widehat{h\mathbf1_{\{\Phi=U\}}}(T)^2/\delta_U$. The joint spectral law is $\delta_Uq_U(T)$. Let $A_y$ sum the deletion losses on labels, $I_y=\mathbb E|U|$, $I_x=\mathbb E|T|$, $I=I_x+I_y$. Then, for **arbitrary** cells and signs,
$$
 \sum_{T,U:\,K>0}p_{T,U} A_y^2/K\le47 I,\qquad K=|U|+|T|.
$$
Here is the argument. For any law on a set of bits, reveal the bits in a fixed order, writing $h_i=-\log_2\Pr(i\text{ present}\mid\text{prefix})$ on present bits. The sum of $h_i$ over present bits is bounded by the surprise of the whole outcome, since the absent-bit terms are nonnegative. With $\ell_i^\delta=\log_2(1+\delta_{U-i}/\delta_U)$, the present-bit likelihood ratio satisfies
$$
 \mathbb E_\delta[\mathbf1_{i\in U}2^{\ell_i^\delta-h_i}]\le\Pr_\delta(i\in U).
$$
To see this, sum over the outside bits with a positive present row. The summand becomes their marginal probability times the prefix probability of presence. Including the remaining outside rows only increases the sum, to $\Pr(i\in U)$. For full label deletion, the joint odds are $(\delta_{U-i}/\delta_U)(q_{U-i}(T)/q_U(T))$. Hence the loss is at most $\ell_i^\delta+[\log_2(q_{U-i}(T)/q_U(T))]_+$, taking the correction zero for missing parents. The last likelihood ratio has conditional expectation at most one under $q_U$. Both positive excesses, over all marked label incidences, have second moment at most $2 I_y/(\ln2)^2$ by Markov and tail integration. For each excess family $e_i$, $(\sum e_i)^2/K\le\sum e_i^2$.

Put $d=\log_2(1/\delta_U)$. Hypercontractivity of $h\mathbf1_{\{\Phi=U\}}$ gives $\mathbb E_{q_U}2^{-|T|}\le2^{-d/3}$. Jensen gives $\mathbb E|T|\ge d/3$, and $\Pr(|T|<d/6)\le2^{-d/6}$. For nonempty $U$, $\mathbb E[d^2/K]\le6d+d^2 2^{-d/6}\le10d$. Combining the surprise term with the two excesses by the triangle inequality yields
$$
 \left(\sum p A_y^2/K\right)^{1/2}\le\sqrt{30 I_x}
       +2\sqrt{2I_y}/\ln2\le\sqrt{47I}.
$$
For **affine** cells and a sign quadratic on each cell, the conditional Fourier law is uniform on an affine subspace invariant under addition of the cell's orthogonal complement. A uniform vector there has $d=\operatorname{codim}(\text{cell})$ independent fair pivot coordinates. Hence $\mathbb E|T|\ge d/2$ and $\mathbb E[d^2/K]\le d^2\mathbb E[1/(1+\operatorname{Bin}(d,1/2))]\le2d$. Every address loss is at most one. With $4 I_x$ in place of $30I_x$, Minkowski gives **$P_2\le(1+\sqrt{4+8/(\ln2)^2})^2 I<31I$**. The arbitrary-cell theorem only controls the labels. Taking one cell and arbitrary $h$ leaves the unrestricted problem on the address bits. [Fiber identities, integer WHTs and likelihood-ratio checks](scripts/max2_fibers.py)

For an explicit stress test, take $t$ independent switches. Each switch uses a control to select a bent quadratic sign on $m$ even address bits or the data bit indexed by those bits. Multiply the switches and one independent balancing sign. In the spectral draw $u\sim\operatorname{Bin}(t,1/2)$ data labels have loss $L=\log_2(1+2^m)$ **simultaneously**. The number of address/control bits $b\sim\operatorname{Bin}(t(m+1),1/2)$ is independent of $u$ and these bits cost one each. The balancing bit costs zero. This follows by writing the two control slices and using the constant-magnitude Walsh spectrum of the bent sign and of each point indicator. Thus
$$
 X=\mathbb E\frac{b(b-1)+2buL+u(u-1)L^2}{1+b+u},\qquad I=1+t(m+2)/2 .
$$
The exact binomial sums give $X/I\in[3.5648113,3.5648114]$ for $(m,t)=(32,16)$ and $[3.7679373,3.7679374]$ for $(128,8)$. The full 15-bit WHT at $(2,2)$ agrees. [Simultaneous deletion tests](scripts/max2_fibers.py)

### Repeated routing through shared linear addresses

Let $L_j$ be binary linear maps on the same address $x$, and let $Q$ be a fixed quadratic polynomial over $\mathbb F_2$. Use distinct data tables for different input positions $j$. For **any** Boolean gate $g$ and
$$
 F(x,y)=(-1)^{Q(x)}g(y_{1,L_1x},\ldots,y_{t,L_tx})
$$
one has
$$
 I_F\ge I_g,\qquad N(F)-N(g)\le5(I_F-I_g),\qquad
 P_2(F)-P_2(g)\le74(I_F-I_g).
$$
These are additive inequalities. They telescope through arbitrarily many such routings, including changes of arity or address maps between steps.

Draw a frequency $U$ of $g$. A compatible data tuple fixes an affine fiber of codimension $r=\operatorname{rank}(L_j:j\in U)$. Let $q$ be the rank of the polar form of $Q$ restricted to its kernel. Every nonzero joint squared coefficient in that tuple is $p_g(U)2^{-2r-q}$. Indeed, squaring the normalized quadratic character sum on the kernel and changing variables to the difference of its two arguments kills all differences outside the polar radical. On the radical the remaining summand is a character, giving either zero or $2^{-q}$. The fiber density contributes $2^{-2r}$. Each tuple therefore contributes $2^{-r}p_g(U)$ by Parseval, and $U$ has its original marginal. The conditional address law is uniform on an affine subspace with at least $r$ fair pivot bits. Its size $D$ stochastically dominates $\operatorname{Bin}(r,1/2)$.

Removing data bit $j$ saves $d_j=r_U-r_{U-j}$ ranks, with $\sum_{j\in U}d_j\le r$ by rank submodularity. The parent kernel contains the child kernel, so its polar rank is at least $q$. The label loss is therefore at most $\ell_j(g)+2d_j$, also when the parent vanishes. Address losses are at most one. Thus $A(F)\le A_g(U)+D+2r$, with $\mu=\mathbb E[D\mid U]\ge r/2$ and $I_F-I_g=\mathbb E D$. This proves the first-moment increment.

For $u=|U|\ge1$ let $a=\mathbb E[(u+D)^{-1}\mid U]$, $v=\mathbb E[D/(u+D)\mid U]$. Then $ra\le3v$. In fact $(r-3D)/(u+D)$ decreases with $D$, so it suffices to check a binomial $D$. Its mean under weights $1/(u+D)$ is minimized at $u=1$, since $(1+D)/(u+D)$ increases with $D$. At $u=1$ the claim is $(r+3)2(1-2^{-r-1})/(r+1)\le3$, by direct inspection for $r\le2$ and cancellation for $r\ge3$. Also $r^2a\le2r$ by the binomial reciprocal formula. Expanding gives $\mathbb E[(D+2r)^2/(u+D)]\le\mu+12r\le25\mu$. Set $b=A_g(U)/u$. Subtracting $A_g(U)^2/u$ from the conditional upper bound for the new square leaves at most
$$
 uv(14b-b^2)+25\mu\le49uv+25\mu\le74\mu.
$$
For $u=0$, $r=0$ and the address-only cost is at most $\mu$. This proves the pooled increment. Across 48 signed gate/map choices the largest observed increment per unit added influence was in $[2.95771078,2.95771079]$. [Exact slice and dense WHT checks](scripts/max2_routing.py)

The disjoint data-table assumption matters. An invertible linear change of five **data** bits carries a quadratic bent sign on four variables times a dictator to two presentations whose uniform spectra are odd affine hyperplanes. Take their check weights to be five and two. Both have $I=5/2$ and the same multiset of Fourier magnitudes. In the first, every deletion leaves the support, so $X=0$. In the second, there is one constrained bit and $b\sim\operatorname{Bin}(3,1/2)$ free bits in the sample. Thus $X=\mathbb E[b(b-1)/(1+b)]=7/16$. A pooled increment bound proportional to the increase of influence also fails here, since the first $P_2$ is zero and the second is positive. This gives a finite obstruction to extending the routing proof to general data coding. [Explicit truth tables and Walsh checks](scripts/max2_routing.py)

### What Boolean arithmetic excludes

Two exact necessary conditions probe information lost by replacing $a_S$ by $p_S$.

1. If $C$ is an affine flat of frequencies of codimension $r\ge1$ and $T\in C$, then $p(C)\ge2^{1-r}|a_T|$. After a binary linear change of variables, $C$ fixes $r$ frequency bits. Let $b(y)$ be the corresponding partial Walsh coefficient on the $r$ physical bits at each outside input $y$. A sum of $2^r$ signs is even, so $b(y)\in2^{1-r}\mathbb Z$. Parseval on $y$ gives $p(C)=\mathbb E_y b(y)^2\ge2^{1-r}|\mathbb E_y b(y)\chi(y)|$, as required. There is also a **signed** congruence $\sum_{T\in C}a_T\in2^{1-r}\mathbb Z$ by evaluating $b$ at $y=0$. In particular if $2^{-d}$ is a common grid step of the entire spectrum and $r\le d$, the number of odd grid numerators on $C$ must be even, independently of signs.
2. For any nonempty supported $S$ let $d_\uparrow(S)=\max\{|R|:R\supseteq S,\ a_R\ne0\}$. Then $a_S\in2^{1-d_\uparrow(S)}\mathbb Z$. In the ordinary $\{0,1\}$ multilinear representation, each nonconstant monomial coefficient is an even integer by finite differences of a sign. The coefficient at $T$ is $(-2)^{|T|}\sum_{R\supseteq T}a_R$. Invert the upper-set sums by Möbius inversion, observing that every nonzero contributing sum lies on the asserted grid. On the region $K\ge\lambda d_\uparrow(S)$, $0<\lambda\le1$, the surprise $-\log_2p_S$ is at most $2K/\lambda$. Using the present-bit prefix estimate above with the spectral law itself, write $A$ as bounded by this surprise plus positive excesses of total squared cost at most $2I/(\ln2)^2$. This gives $\sum_{\rm region}p_S A(S)^2/K\le(2/\lambda+\sqrt2/\ln2)^2 I$. It rules out a mixed divergence confined to levels comparable to their own highest supported coface. [Affine-flat, grid and regional moment tests](scripts/max2_certificates.py)

For signed coefficients there is an exact converse at the level of hyperplanes. For a real vector $a$ of unit squared norm, the inverse Walsh values are Boolean iff $\sum_T a_T$ is an odd integer and $\sum_{\langle T,x\rangle=1}a_T$ is an integer for every nonzero $x$ (inner products modulo two). Indeed the inverse value at $x$ is the total sum minus twice the hyperplane sum. All inverse values are thus odd integers with mean square one, which forces every value to be a sign. Necessity follows by subtracting two physical values. The characterization still requires **one common choice of signs**. [Signed WHT checks](scripts/max2_certificates.py)

Another exact constraint is that a single spectral membership bit independent of all the other bits can have marginal only $0,1/2,1$. In the nondegenerate case every nonzero pair of absolute integer Walsh numerators is $(at,bt)$ for fixed coprime positive integers $a,b$. Integer Parseval gives $(a^2+b^2)\sum t^2=4^n$. If just one of $a,b$ is odd their squared sum is odd and greater than one. If both are odd the sum is $2\bmod4$, so it must be two. This excludes an exactly independent biased coordinate, but supplies no quantitative bound for nearly independent coordinates. [Tests on all three-bit functions, random four-bit functions and the Numaro seed](scripts/max2_certificates.py)

**A relaxation with divergent $B$ and $X/I$.** The simplest examples put equal spectral mass on the two uniform levels $k-1,k$ in $n=2^k$ dimensions. The $k$-level deletion odds are $(n-k+1)/k$. These laws pass the shifted Chang bounds and the single-origin centered derivative noise test used above, yet at $k=128$ they give $B>60.737254$, $X/I>7291.792156$. A uniform floor makes even the affine **mass** constraints possible. In $n=k^2$, place mass $(1-1/k)/2$ uniformly on each of the same two levels and distribute $1/k$ uniformly on the entire cube. Append a mandatory sign bit for balance. For all sufficiently large $k$, all amplitudes are at most $1/(2k)$. Every codimension-$r$ flat meeting the support contains mass at least $2^{-r}/k$. Its mass thus passes the first condition above. The marked $k$-level has constant mass, $I=\Theta(k)$, and all $k$ core deletions have odds $\Theta(k)$. It contributes $\Omega(\log k)$ to $B$ and $\Omega(\log^2 k)$ to $X/I$. These are squared spectra of normalized **real** functions. [Two-shell and symbolic WHT checks](scripts/max2_levels.py) · [Uniform-floor check](scripts/max2_certificates.py)

There is a stronger relaxation where **all Walsh amplitudes are dyadic**, Parseval is exact, and an explicit congruence excludes any Boolean realization. Take $k=4^b\ge4$, $n=k^2$, $d=n/2+\log_4 k$. On the $n$ core bits start every amplitude at $c=2^{-d}$, of total mass $1/k$. Replace the amplitudes on levels $j=k-1,k$ by $a_j=2^{-\lceil\log_4(8\binom nj)\rceil}$. Each new shell mass lies in $(1/32,1/8]$. The odds $a_{k-1}^2/a_k^2\ge(n-k+1)/(4k)$. Fill the remaining mass by raising distinct degree-two amplitudes to $2^u c\le1/(2k)$. In units of $c^2$ each increment is $4^u-1$. The remainder is divisible by three, including initially since $4^d-2^n$ is divisible by three. Greedily use the largest affordable step up to the cap. The cap uses at most $8k^2$ positions, and every lower exponent uses at most four positions, as $4^{u+1}-1=4(4^u-1)+3$. There are sufficient pairs for $k\ge16$ since $8k^2+4d<\binom n2$, and the program verifies $k=4$ directly. The unit increment at $u=1$ in this divisible-by-three remainder is three, which finishes the normalization.

Again append a mandatory bit. The floor gives all affine mass bounds, every amplitude is at most $1/(2k)$, and every shifted Chang test is vacuous. Influence is $O(k)$ since the floor costs $n/(2k)$, the two shells cost at most $k/4$, the fill costs at most two and the mandatory bit costs one. Thus the same lower orders $\Omega(\log k)$ and $\Omega(\log^2 k)$ follow from just the upper shell. On the flat that requires a particular $k$-subset of the core to be present, $2^{n-k}-1$ entries have odd numerator in units of $c$. The other core entry is the enlarged $k$-subset itself. The half with absent mandatory bit has zero coefficients. The codimension is $k\le d$, contradicting the signed congruence. The verifier uses full integer WHT inversion at $k=4$ and rational multiplicities through $k=256$. This singles out a multi-frequency Boolean constraint that an unsigned mass proof misses. It gives no estimate on how much additional spectral mass enforcing all the congruences would require. [Dyadic construction and sign obstruction](scripts/max2_certificates.py)

Turturean's Theorem 3.1 constructs a permutation of a physical level set with coordinate agreements bounded by the corresponding edge-boundary counts. Using the shifted sign $f\chi_T$ in this theorem gives physical boundaries $I_i(f)$ for $i\notin T$ and $1-I_i(f)$ for $i\in T$. A separate such bound for each $T$ allows the same physical edges to be counted many times. We found no simultaneous charging of $p_{T+i}\ell_i$ to those budgets. Shmalo's pivotal-antichain argument supplies a rank tail for specific derivative supports, and the orthogonal multiplexer formulas exploit separation of private frequencies. The block-noise and disjoint-table proofs above identify corresponding conditions under which a mixed bound does follow. The general degree-sensitive entropy estimates of Kelman, Kindler, Lifshitz, Minzer and Safra also permit a logarithmic loss in increasing degree. [Turturean, §§3–4](https://arxiv.org/html/2611.09773v1) · [Shmalo, §§3, 8](https://arxiv.org/html/2610.16069v1) · [Kelman et al.](https://arxiv.org/abs/1911.10579)

### Rounding the two shells to genuine Boolean signs

Thresholding the inverse WHT produces a Boolean gate, but can substantially increase influence. For finite tests we signed integer amplitudes on $k-1,k$ with constant, quadratic or independent phases, took the sign of the inverse transform, and added a mandatory balancing bit. At $(n,k)=(16,4)$ the three contributions of the original upper shell to $B$ were in $[.222476,.222477]$, $[.326007,.326008]$ and $[.436761,.436762]$. The corresponding balanced influences were $3239/512$, $10885/2048$ and $24401/4096$. As a separate check all 1,024 integer phase choices with amplitudes two and one at $(4,2)$ give mean influence $25/16$ before balancing, verified both by WHT and by counting sign changes of the terms that flip on one edge. [Exact rounded gates and edge counts](scripts/max2_levels.py)

There is a bound for **the entire ensemble** when the coefficients have independent centered Gaussian amplitudes. Let their variances be an arbitrary probability law $v_T$, let $P(x)=\sum_T\sqrt{v_T}\,Z_T\chi_T(x)$ with $Z_T$ independent standard normals, and put $f=\operatorname{sgn}P$. For a fresh sign $z$,
$$
 \mathbb E H(zf)\le24\,\mathbb E I(zf).
$$
This controls the ratio of expectations. An exceptional deterministic choice of coefficients could behave differently.

To prove it, set $\tau_i=\sum_{T\ni i}v_T$, and write $\bar p=\mathbb E p(f)$. At inputs whose difference is $x$, the Gaussian correlation is $c(x)=\sum_T v_T\chi_T(x)$. Rotational symmetry in the plane of the two normal vectors gives disagreement probability $\arccos(c(x))/\pi$. Hence $\bar I=\mathbb E I(f)=(2/\pi)\sum_i\arcsin\sqrt{\tau_i}$, and the Walsh transform of $\bar p$ is $(2/\pi)\arcsin(c(x))$. Expand the arcsine in a positive power series. Its coefficient at $m=2j+1$ is $w_m=(2/\pi)\binom{2j}j4^{-j}/m$, its even coefficients are zero, and the weights sum to one. Thus $\bar p$ samples $m$ with this law and takes the symmetric difference of $m$ independent samples from $v$. The central binomial bound gives $w_m\le m^{-3/2}$.

The mixing entropy is less than 24 bits. Indeed the comparison law $1/(m(m+1))$ costs at most $2\mathbb E\log_2(m+1)$ bits. Dyadic bin $[2^j,2^{j+1})$ has mass at most $2^{-j/2}$, and $2\sum_{j\ge0}(j+1)2^{-j/2}<24$. At coordinate $i$ the conditional probability of membership is $u_m=(1-(1-2\tau_i)^m)/2\le m\tau_i$. For $\tau=\tau_i>0$, entropy subadditivity and the binary entropy bound $h_2(u)\le u\log_2(e/u)$ give a conditional entropy cost at most
$$
 \frac{\tau}{\ln2}\sum_{m\le1/\tau}m^{-1/2}\ln(e/(m\tau))
     +\sum_{m>1/\tau}m^{-3/2}
 \le (6/\ln2+2\sqrt2)\sqrt\tau .
$$
The integral of the first decreasing summand from zero to $1/\tau$ is $6/\sqrt\tau$ before its prefactor. The second sum is at most $2/\sqrt{\lfloor1/\tau\rfloor}$. The zero marginal costs zero. By concavity, $\mathbb E H(f)\le H(\bar p)\le24+(6/\ln2+2\sqrt2)\sum_i\sqrt{\tau_i}$. Since $\arcsin x\ge x$ and $(6/\ln2+2\sqrt2)\pi/2<24$, balancing proves the claim. [Certified Walsh inversion of the arcsine kernel](scripts/max2_rounding.py)

For the proposed two-shell law there is a **mixed-moment bound as well**. Take $v$ uniform with mass $1/2$ on each of $k-1,k$, $2\le k\le n$. Then $\bar p$ is radial and $\bar I=(2n/\pi)\arcsin\sqrt{(k-1/2)/n}\ge(2/\pi)\sqrt{n(k-1/2)}>1$. In the symmetric-difference representation, the size $K$ after $m$ steps is at most $mk$. For any $d\ge1$,
$$
 \mathbb E_{\bar p}[K\mathbf1_{K\le d}]
 \le\sum_m w_m\min(d,mk)\le(2+2\sqrt2)\sqrt{kd}.
$$
For $d<k$ use the bound $d$. Otherwise split at $d/k$ and use the same two integral comparisons. Dividing by $\bar I$ gives $\Pr_{\rm inc,\bar p}(K\le d)\le10\sqrt{d/n}$. The radial proof above gives $\|\ln(n/K)\|_2\le\sqrt{80}$. Including singleton parents costs $\mathbb E_{\rm inc}[\bar W_{K-1}/\bar W_K]\le1+1/\bar I\le2$. Consequently $\sqrt{P_2(\bar p)/\bar I}\le(\sqrt{80}+\sqrt2)/\ln2$.

To pass back to the individual Boolean functions, for any mixture of spectral laws $p_\omega$ define the posterior density $r_S(\omega)=p_\omega(S)/\bar p_S$ relative to the mixing law. For every supported incidence,
$$
 \ell_i^\omega(S)\le\ell_i^{\bar p}(S)+[\log_2(r_{S-i}/r_S)]_+ .
$$
Under the posterior at $S$, the likelihood ratio on the right has expectation at most one. A missing parent has zero cost. Integrating its exponential tail and using $(\sum e_i)^2/K\le\sum e_i^2$ gives the general comparison
$$
 \sqrt{\mathbb E P_2(p_\omega)}\le\sqrt{P_2(\bar p)}+\sqrt{2\bar I}/\ln2.
$$
Combining the bounds yields **$\mathbb E X(f)\le\mathbb E P_2(f)<290\,\mathbb E I(f)$** for the Gaussian two-shell ensemble. The mandatory sign preserves $N$, weakly decreases $P_2$, and gives $d_b(zf)\ge I(f)$. Cauchy–Schwarz thus gives $\mathbb E N(zf)<18\,\mathbb E d_b(zf)$. This controls the mean under sampling proportional to branching influence across gates. At $(n,k)=(18,4)$ certified inversion gives $\bar I\in[5.23301130,5.23301131]$ and $H(\bar p)\in[14.76243088,14.76243321]$. The certificate checks the posterior calculation on finite mixtures and also uses the 18-bit Numaro spectrum as a nonradial Gaussian variance law for the entropy bound. [Mean-law and mixture certificates](scripts/max2_rounding.py)

### Direct balanced optimization

We optimized $B$ and $X/I$ separately at every arity from 8 through 18, using 1,440 candidate moves in 22 runs. The moves were balanced sign swaps, invertible linear shears, and conditional permutations of a truth-table coordinate. The starts included asymmetric tie cuts and sharing up to nine Numaro selectors. Each trial used an integer WHT. Floating-point scores selected moves, and the final winners were re-evaluated by rational interval arithmetic. Both winning runs returned the 18-bit seed with $B\in[2.2290770051,2.2290770052]$ and $X/I\in[2.4953466921,2.4953466922]$. These are finite search outcomes. The Round 1 disjoint tower already has $X/I>11.104850$ at depth 20. [Search and exact finalist checks](scripts/max2_search.py)

### Localizing the first moment and the mixed moment

Let $f$ be balanced, $J=I(f)\ge1$, and form the product $F_t$ of $t\ge2$ independent copies. Activate it at a single point $E$ on $w$ fresh bits, of density $\delta=2^{-w}$. Define $h=1+\mathbf1_E(F_t-1)$ and $G=z h$ with an independent sign $z$. The following are exact:
$$
\begin{aligned}
 W_1(G)&=(1-\delta)^2,& I(G)&=1+\delta(tJ+w),\\
 d_b(G)&=\delta(tJ+w+2-\delta),&
 N(G)&=\delta\{tN(f)+w+w\delta(L-1)\},\\
 L&=\log_2(1+(1-\delta)^2/\delta^2).
\end{aligned}
$$
For a nonempty data frequency the Walsh coefficient of $h$ is $\pm\delta\,\widehat F_t(S)$ at every control frequency. Its data loss copies the original since an occupied sample has at least two nonempty blocks. Its address contribution summed over samples is $\delta w/2$. At empty data the coefficients are $1-\delta$ at empty controls and $\pm\delta$ elsewhere. The address losses there contribute $\delta w/2+w\delta^2(L-1)$. Multiplication by $z$ adds one to every degree and contributes no loss. Removing the singleton losses of **$h$** therefore gives the especially simple identity
$$
 \sum_{|S|\ge2}p_S(h)A_h(S)=\delta\{tN(f)+w(1-\delta)\}.
$$
For $\delta\le1/4$ this is also exactly the raw loss of $G$ at parents of amplitude at most $1/4$. Multiplication by $z$ identifies the omitted terms with deletions to its heavy singleton. [Dense masks, depth-20 transfer and rational checks](scripts/max2_local.py)

If FEI fails, the Round 1 tower theorem supplies balanced gates with $R=N(f)/J\to\infty$. Take $t=2$ and $w=\lceil\log_2(2J\sqrt R)\rceil$. Then $\delta\,2N(f)\ge\sqrt R/2$ while $\delta(2J+w)\to0$, uniformly for $J\ge1$ since $\log(J)/J$ is bounded. Thus $G$ approaches a dictator in disagreement probability $\delta/2$ and in influence, while $N(G)\to\infty$. Conversely FEI implies $N(G)=N(h)\le H(h)\le C(I(G)-1)$ on these masks. The middle inequality follows by bounding the present-bit loss by the full conditional entropy and summing the erasures by the entropy chain rule. For comparison, at $w=32$ the two-copy depth-20 Numaro gate gives $I(h)\in[.000718927984,.000718927985]$ and raw branching loss in $[.002395945266,.002395945267]$. Existing rare-activation reductions for ordinary entropy motivate this calculation. [Shalev](https://arxiv.org/abs/1806.03646) · [Shmalo, §8.4](https://arxiv.org/html/2610.16069v1) · [New deletion-loss transfer](scripts/max2_local.py)

For the **mixed moment**, suppose $\sup X(f)/I(f)=\infty$ over nonconstant signs. First reduce to balanced $b$ with $J=I(b)\ge1$. For a source $f$ of influence $I_0$, set $b=z\prod_{j=1}^t f(x_j)$, taking $t=1$ if $I_0\ge1/2$, else $t=\lceil1/I_0\rceil$. On the samples with exactly one nonempty data block of size $k\ge2$, all ordered pairs of data losses are retained and $k/(k+1)\ge2/3$. With $V=\operatorname{Var}f\le I_0$,
$$
 X(b)\ge(2/3)t(1-V)^{t-1}X(f),\qquad J=1+t I_0 .
$$
For $t=1$ the empty product is one. For $I_0<1/2$, $(1-I_0)^{1/I_0}\ge1/4$ and $tI_0\ge1$. In both cases $X(b)/J\ge X(f)/(12I_0)$.

Write $R=X(b)/J\to\infty$, choose $w=\lceil\log_2(J\sqrt R)\rceil$, and mask **one** balanced copy, $G=z[1+\mathbf1_E(b-1)]$. The Round 1 degree-sensitive tail for $(\ell_i-3K)_+$ implies
$$
 X_{\{K\le w\}}(b)\le18w^3+150J .
$$
Indeed, on each set $A^2/K\le\sum\ell_i^2$, and $\ell_i^2\le18K^2+2(\ell_i-3K)_+^2$. Sum the first term over its $K$ incidences and integrate the previous tail for the second. Uniformly for $J\ge1$, $w^3/J=O(1+\log^3 R)=o(R)$. On $K\ge w+1$ all data pairs survive, and the new degree is at most $K+w+1\le2K$. After summing the control copies,
$$
 X(G)\ge(\delta/2)X_{\{K\ge w+1\}}(b)\to\infty,\qquad I(G)\to1 .
$$
If the global mixed bound holds, then on every mask $G=zh$ one instead has $X(G)\le X(h)\le K'I(h)=K'(I(G)-1)$: the extra sign increases the denominator and has zero loss. This proves the stated **zero-or-infinity dichotomy**, leaving the choice of alternative unresolved. [Ordered-pair and tensor transfer checks](scripts/max2_local.py)

### Single target for Round 3 · rare perturbations of a subcube

Let $A$ be a cube event of measure $\mu$, and $h_A=1-2\mathbf1_A$. Define the **unnormalized** sum with nonempty parents
$$
 \mathcal E(A)=4\sum_{\substack{|S|\ge2\\\widehat{\mathbf1_A}(S)\ne0}}
 \widehat{\mathbf1_A}(S)^2\sum_{i\in S}
 \log_2\!\left(1+\frac{\widehat{\mathbf1_A}(S-i)^2}{\widehat{\mathbf1_A}(S)^2}\right).
$$
For $r\ge2$, take $\mu=2^{-r-1}$ and a subcube $C$ of that measure such that
$$
 \Pr(A\triangle C)\le\mu^3,\qquad
 I(h_A)-2\mu\log_2(1/\mu)\le\mu^3 .
$$
Here $2\mu\log_2(1/\mu)$ is the minimum possible influence at this dyadic volume. Let $J_C$ be the fixed coordinates of the subcube, choose one $z\in J_C$, and for $V\subseteq J_C^c$ put $b_V=\widehat{\mathbf1_A-\mathbf1_C}(V\cup\{z\})$. **The Round 3 target is a dimension-independent absolute upper bound on $\mathcal E_z(A,C)$ for these triples $(A,C,z)$**, where
$$
 \mathcal E_z(A,C)=4\sum_{\substack{V\subseteq J_C^c,\,|V|\ge2\\ b_V\ne0}}
 b_V^2\sum_{i\in V}\log_2(1+b_{V-i}^2/b_V^2).
$$
Both endpoints of every such edge have amplitude at most $\Pr(A\triangle C)\le\mu^3$. All other fixed coordinates are absent from the frequency. This absolute, unnormalized bound is **equivalent to FEI**. [Edge isoperimetry](https://arxiv.org/abs/1702.01675) · [Nested-mask and single-slice verifier](scripts/max2_local.py)

In fact $\mathcal E_z(A,C)\le\mathcal E(A)$ since the subcube has zero Fourier coefficient at any frequency using a free bit. FEI gives $\mathcal E(A)\le N(h_A)\le C_{\rm FEI} I(h_A)\to0$ as $r\to\infty$ in this class. For the converse, use the balanced $G=zh$ above with $I(G)\to1$, $N(G)\to\infty$, and $\Pr(G\ne z)=\delta/2\to0$. Gate $\{G=-1\}$ on one additional point of $r$ fresh bits of density $\eta=2^{-r}$. Compare this event $A$ to the subcube requiring that same point and $z=-1$. Now
$$
 \mu=\eta/2,\qquad \Pr(A\triangle C)=\eta\delta/2,\qquad
 I(h_A)-2\mu(r+1)=\eta(I(G)-1),\qquad \mathcal E(A)\ge\eta N(G).
$$
The influence identity follows by counting control and data edges, or by Parseval on the activation slices. For the last inequality, each supported data set of size at least two replicates at every outer control frequency. Deleting one data bit keeps its parent nonempty and preserves its odds. The squared mass after summing the replicas is $\eta p_S(G)$. Singletons of balanced $G$ have zero old loss.

For the single slice one can compute an **equality**. The signed difference of indicators is the outer point indicator times $z\mathbf1_{\{h=-1\}}$. Thus $b_V=-(\eta/2)\widehat h(V)$ for nonempty $V$, and the earlier two-copy identity gives
$$
 \mathcal E_z(A,C)=\eta^2\delta\{2N(f)+w(1-\delta)\}.
$$
For each $r$ choose the inner example far enough along its sequence that $\eta\delta/2,\eta(I(G)-1)\le\mu^3$ and $2\delta N(f)\ge\eta^{-3}$. All three conditions are compatible by the first masking proof. Then $\mathcal E_z(A,C)\ge2^r$. The same argument works for any prescribed positive tolerance in place of $\mu^3$. For $X$, the second masking retains at least $\eta/2$ of the mixed mass above degree $r+1$. The low-degree bound just proved and $I(G)\to1$ give the analogous conditional divergence of $X(h_A)$ even on these near-minimizing rare sets.

In a finite nested check, take two copies of the depth-20 Numaro gate, $w=38$ inner and $r=6$ outer control bits. The volume is $1/128$, the distance to the comparison subcube is $2^{-45}$, and the boundary excess lies in $[.00000017551986,.00000017551987]$, below $\mu^3$. The selected slice satisfies $\mathcal E_z(A,C)\in[.0000000091398111,.0000000091398112]$. A possible approach for Round 3 is to apply the signed affine congruences to the difference of the indicator and its nearby subcube, charging its diffuse data coefficients using the small boundary excess. The cost of the embedded data boundary is proportional to its tiny activation probability, and that probability also multiplies its inherited deletion loss. A distance or boundary estimate alone has yet to control their ratio. [Exact high-depth example and low-dimensional full WHT comparisons](scripts/max2_local.py)

### Reproduction and Lean scope

From the project root, run each of the eight scripts with Python 3 and NumPy. Each is deterministic. Dense WHTs use integer butterflies. Structured examples above full-cube size use exact fiber, radial, product or marked-leaf formulas. Logarithmic certificates use rational intervals from correctly rounded and widened logarithms, with outward rounding when printing. The Gaussian kernel uses rational arcsine and arctangent series with explicit remainders. Floating-point move selection is confined to the optimization. The new Lean lemmas prove the branching mass identity in the frozen normalization, a ternary derivative inequality, the integer two-square obstruction, the quadratic absorption step in routing, a signed mean bound for a quantized slice, the unit-energy rigidity of odd inverse values, and the scaling of a deletion loss under Walsh replication. The analytic theorems above are proved in this report. [Lean lemmas](FEI/ResearchLemmas.lean)

~~~sh
python3 scripts/max2_levels.py
python3 scripts/max2_symmetric.py
python3 scripts/max2_fibers.py
python3 scripts/max2_routing.py
python3 scripts/max2_certificates.py
python3 scripts/max2_rounding.py
python3 scripts/max2_search.py
python3 scripts/max2_local.py
lake build
shasum -a 256 FEI/Challenge.lean
~~~

All eight Round 2 scripts exited successfully. The final `lake build` completed successfully (4,168 jobs) with no warnings or errors, and the seven new auxiliary lemmas contain no proof placeholders. The frozen challenge SHA-256 is `6bd49da1bc4ada83635a00f9c4957aa4a8e42ae74cc570b1e8ceaabab8d6634b`, identical to the starting file and the repository version.

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


