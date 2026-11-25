# Astra MAX Escalation — Round 2 of 3 (Fourier Entropy–Influence Conjecture)

You are resuming session `01a212d2-dcd9-7c42-aade-61e556a007b8` at **`model_reasoning_effort="max"`** for Round 2 of 3.
Your Round 1 results were phenomenal:
- New certified finite balanced monotone record: $6.5218511673478223969022 \le H/I \le 6.5218511673478223969023$.
- Proved the exact tower limit $P_2(g^{\circ n})/I_g^n \to m(g)^2$, uniform bounds on rare switches / Tribes / multi-output bent lookups, and the dense shared-variable packing theorem ($\alpha \ge 255/256$).
- Proved the **exact FEI-equivalent single-gate target**:
  $$B(g) := \frac{\sum_{|S| \ge 2} p_S \sum_{i \in S} \log_2(1 + p_{S-i}/p_S)}{\sum_{|S| \ge 2} |S| p_S} = \frac{\sum_{|T| \ge 1} \sum_{i \notin T} p_{T+i} \log_2(1 + p_T/p_{T+i})}{\sum_{|T| \ge 1} \sum_{i \notin T} p_{T+i}},$$
  with $S_* = \sup_{g \text{ balanced}} B(g) = \sup_{g \text{ balanced}} m(g)$ and $S_* \le C_* \le S_* + 3\log_2 e$!

Now go **ALL-IN** on **settling whether $\sup_{g \text{ balanced}} B(g) < \infty$ (Case A: proves full FEI!) or $\sup_{g \text{ balanced}} B(g) = \infty$ (Case B: disproves full FEI!)**. Keep `FEI/Challenge.lean` completely untouched!

## Focused Attack Plan for MAX Round 2

### 1. Proving $B(g) \le K$ (Case A — Complete FEI Proof)
Look closely at why $B(g)$ is vastly cleaner than raw $H/I$:
- Singletons $|S|=1$ are completely stripped out of both numerator and denominator.
- For $B(g)$ to be large ($\ge M$), the typical incidence $(T, T+i)$ (drawn with probability $\propto p_{T+i}$ over $|T| \ge 1, i \notin T$) MUST have $p_T / p_{T+i} \ge 2^{\Omega(M)}$.
- Attack $B(g) \le K$ (or the sufficient mixed quadratic bound $X(f) \le K' I(f)$, which STILL survived every single Round-1 stress test!) using **global Boolean constraints**:
  1. **Shifted-character / Chang / Hypercontractive analysis on $g_T(x) = g(x) \chi_T(x)$:** For any nonempty $T$, $g_T$ is STILL Boolean with empty coefficient $\hat{g}(T)$ and degree-1 coefficients $\hat{g}(T \triangle \{i\})$. When $p_T$ is large, Chang's inequality / Bonami–Beckner / Talagrand severely restricts the level-1 energy $\sum_{i \notin T} p_{T+i}$ relative to $1 - p_T$! What happens when you sum over ALL $T$ (or partition $T$ into dyadic buckets of $p_T \in [2^{-k-1}, 2^{-k}]$) and relate $\sum_{T \in \mathcal{B}_k} \sum_{i \notin T} p_{T+i}$ to total branching degree $d_b$ using **Parseval + $f^2 = 1$ (spectral convolution / $L_4$ / hypercontractivity / $D_i g \cdot E_i g \equiv 0$)**?
  2. **Global amortization / fractional-certificate / controlled-bijection ideas** (check whether the ideas in Turturean `arXiv:2611.09773` or Shmalo `arXiv:2610.16069` — e.g. bounding $\sum_i L_i$ or $B(g)$ via level-by-level or coordinate-tree decomposition — extend beyond LTFs!).
  3. **Test $X(f) \le K' I(f)$ to destruction or proof!** You already proved $X/I$ stays bounded on every tested tower and multi-output lookup (and only failed the *pairwise-local* charge, NOT the global bound!). Either **construct an explicit family where $X(f)/I(f) \to \infty$** (killing $X/I$ cleanly so Round 3 doesn't waste time on it!) OR **prove $X(f) \le K' I(f)$ globally** (which IMMEDIATELY proves full FEI!!).

### 2. Disproving $B(g) \le K$ (Case B — Finding $B(g) \to \infty$!)
Remember: to **DISPROVE FEI**, you do NOT need $H/I \to \infty$ directly on one step — you ONLY need a sequence of balanced Boolean gates $g_m$ with **$B(g_m) \to \infty$** (then depth-$d$ disjoint towers $g_m^{\circ d}$ automatically force $H/I \to \infty$!).
Think deeply about **WHY every previous construction had $B(g) = O(1)$**, and try to BREAK that mechanism directly:
- In bent-lookup, a set $S$ with $|S| \approx m/2$ had only **ONE** coordinate $i \in S$ with huge odds $p_{S-i}/p_S = 2^m$, while the other $m/2 - 1$ coordinates had odds $1$, so averaging over $i \in S$ gave $\approx m / (m/2) = 2$!
- **TO MAKE $B(g) \to \infty$, we need a balanced Boolean function where a typical high-degree set $S$ ($|S| \ge 2$) has $\omega(1)$ ratio of $\sum_{i \in S} \log_2(1 + p_{S-i}/p_S)$ to $|S|$!**
  That can happen in ONLY TWO WAYS:
  1. **Small $|S|$ ($|S| = 2$ or $3$!) with HUGE $p_{S-i}/p_S$**, while $d_b$ is dominated by $|S| \approx O(1)$! Wait: CAN a balanced Boolean function put a constant fraction of its branching influence $d_b$ on **degree-2 (or degree-$O(1)$) sets $S$** whose singleton parents $p_{\{j\}}$ are exponentially larger than $p_S$?!
     - **TEST THIS RIGHT NOW!!** Suppose $g$ is close to a linear combination of singletons (or a **perturbed majority / perturbed symmetric / perturbed LTF / sparse degree-2 Boolean modification** where $p_{\{j\}} \sim 1/n$ and $p_{\{j,k\}} \sim 1/n^2$ or $1/n^{1+\alpha}$)! Wait: if $p_{\{j\}} \sim 1/n$ and $p_{\{j,k\}} \sim 1/n^2$, then $p_{\{j\}}/p_{\{j,k\}} \sim n$, so $\log_2(1 + p_{\{j\}}/p_{\{j,k\}}) \sim \log_2 n$!!
     - **HOLD EVERYTHING!! CHECK THAT!!** Take a balanced **symmetric / threshold / Tribes / majority-of-biased** Boolean function on $n$ variables where BOTH degree-1 AND degree-2 Fourier weights are nonzero (e.g., $\mathrm{Maj}_n$ shifted by $+1$, or $\mathbf{1}[\sum x_i \ge 1]$ adjusted for balance, or $\mathrm{OR}$/$\mathrm{AND}$/$\mathrm{XOR}$ of dictators with one asymmetric bit, or $g(x) = \mathrm{sgn}(\sum_{i=1}^n x_i + \text{perturbation})$)!
       - Wait: if $\sum_{|S|=2} p_S$ is a **constant fraction of $d_b$**, AND $p_{\{i\}} \sim 1/n$ while $p_{\{i,j\}} \sim 1/n^2$ (for all $\binom{n}{2}$ pairs!), then $\sum_{|S|=2} p_S \sim \Theta(1)$, $p_T/p_{T+i} \sim \Theta(n)$, and the numerator would get $\Theta(\log n)$ while the denominator is $d_b$!!
       - Why didn't LTFs violate FEI? Because for LTFs, if $d_b = O(\sqrt{n})$ (like Majority!), then $W_2 \sim O(1/\sqrt{n})$ is ONLY a $1/n$-fraction of $d_b$, NOT a constant fraction! What about **non-LTF** symmetric or low-influence functions where **$W_1 \approx 1 - \varepsilon$ and $W_2 \approx \varepsilon$** (with $d_b \approx 2\varepsilon$) while $p_{\{i,j\}} \ll p_{\{i\}}$?!
       - **Check Chang's / hypercontractive obstruction on $W_2 \approx d_b$!** If you try to make $W_1 \approx 1 - \varepsilon$ and $W_2 \approx \varepsilon$ with tiny $p_{\{i,j\}}$, does $g^2 = 1$ force $p_{\{i,j\}}$ to be concentrated, OR can $B(g)$ actually diverge?! Test BOTH analytically and in Python!
  2. **Large $|S|$ where MANY coordinates $i \in S$ simultaneously have huge odds $p_{S-i}/p_S \gg 1$:** e.g., $k$-fold composed / coupled bent lookups, recursive shared-address tables, or direct discrete optimization of $B(g)$ (not $H/I$!) over balanced functions on $n = 8..18$!

## Required Outputs (Round 2 of 3)
- **Keep `FEI/Challenge.lean` completely untouched** (verify SHA-256).
- **Zero bluffing.** Every claim backed by exact proof or exact Python WHT / interval verification.
- **If Case A (Complete Proof!) or Case B (Diverging $B(g_m) \to \infty$ / FEI Disproof!):**
  - Write complete, self-contained `PROOF.md`.
  - Write **`FEI/Blueprint.lean`** importing `FEI.Challenge`, `FEI.ChallengeSanity`, `FEI.ResearchLemmas`, decomposing the full proof into 15–40 line lemmas with proof hints above every `sorry`, ending in `FourierEntropyInfluenceConjecture` (or `¬ FourierEntropyInfluenceConjecture`), and verify `lake build` compiles with ZERO errors!
- **If still Case C:**
  - Update `RESEARCH_ANALYSIS.md` with Round 2 findings (including the exact fate of $X/I$, the degree-2/symmetric/hypercontractive test of $B(g)$, any new record lower bound, new Lean lemmas in `FEI/ResearchLemmas.lean`, and the single sharpest target for Round 3 of 3!).
