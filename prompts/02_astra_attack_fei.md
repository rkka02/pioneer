# Research Mission: Attack the Fourier Entropy–Influence (FEI) Conjecture (ProofAtlas #412)

We have frozen the canonical, unweakened Lean 4 statement of the **Fourier Entropy–Influence (FEI) Conjecture** (Friedgut & Kalai, 1996) in `FEI/Challenge.lean`:
> $\exists C > 0,\ \forall n \in \mathbb{N},\ \forall f : \{-1,1\}^n \to \{-1,1\},\ H(\hat{f}^2) \le C \cdot \mathrm{Inf}(f).$

Your mission as our flagship mathematical reasoning engine (`GPT-6.2 Astra`, `xhigh`) is to conduct a **deep, rigorous, zero-bluff mathematical attack** on `FourierEntropyInfluenceConjecture` — aiming to discover either a **complete proof** or an **asymptotic counterexample family** — and if a viable proof/disproof emerges, architect a clean Lean 4 lemma blueprint (`FEI/Blueprint.lean`) ready for downstream formalization by Claude Code (`Opus 5.5`).

## Rules of Engagement (STRICT)
1. **DO NOT edit `FEI/Challenge.lean`.** It is frozen.
2. **ABSOLUTE MATHEMATICAL HONESTY — ZERO BLUFFING:**
   - Every candidate inequality, potential function, restriction lemma, or counterexample family MUST be stress-tested empirically in Python using exact fast Walsh–Hadamard transforms (`WHT`)!
   - Remember: as of 2026, explicit balanced monotone Boolean functions already achieve $H(\hat{f}^2)/\mathrm{Inf}(f) \ge 6.5218$ (around $n=18$), and Fourier min-entropy / influence reaches $\ge 128/45 \approx 2.8444$. Any claimed proof with $C < 6.53$ is **immediately false**, and any inductive inequality MUST be verified against high-ratio extremal functions (e.g., iterated/skewed Tribes, O'Donnell–Tan / Hodžić–Rotteler / recursive threshold / address / pointer-chasing / bent-modified functions) in Python before trusting it!
   - If an approach hits a genuine counterexample or barrier, **document it explicitly** rather than handwaving past it.

## Known Frontier Context (Build Beyond It)
- **Known special classes where FEI holds:** Decision trees (O'Donnell–Wright–Zhou / Wan–Wright–Wu, via random-walk/entropy induction with $C$ matching average depth!), symmetric functions, read-once formulas, bounded-degree / bounded-sensitivity / random LTFs, monotone functions under restricted assumptions, plateaued functions.
- **Classic barrier in coordinate-restriction induction:** Splitting $f$ along coordinate $i$ gives $\hat{f}(S) = (\widehat{f_0}(S) \pm \widehat{f_1}(S))/2$. For an arbitrary single coordinate $i$, $H(\hat{f}^2) - \frac{1}{2}(H(\hat{f_0}^2) + H(\hat{f_1}^2))$ is NOT bounded by $C \cdot \mathrm{Inf}_i(f)$ alone (because $\mathrm{Inf}_i(f)$ can be tiny while mixing two very different spectra $f_0, f_1$ — or rather, check the exact Jensen/mix bound using $\mathrm{Inf}_i(f) = \frac{1}{4}\|f_0 - f_1\|_2^2$!).
- **CRITICAL RECENT INSPIRATION (Nov 2026):** In the exact same Boolean Fourier analysis domain, **#460 Aaronson–Ambainis** was just proved in Lean 4 (PSI / Turturean, Nov 2026) using **fractional certificates**, **Fourier tail control**, and **controlled bijections / determinant arguments** (connecting to Lovett–Zhang). Think carefully about whether randomized decision trees / fractional certificates / certificate-entropy / entropy-splitting along *high-variance or adaptive coordinates* or *noisy Bonami–Beckner / Ornstein–Uhlenbeck semigroup interpolation* $\frac{d}{dt} H(\widehat{T_t f}^2)$ gives a genuinely new handle on FEI!
- **Wait — Semigroup / Noise-Flow Differential Approach:** Consider $p_t(S) = \hat{f}(S)^2 e^{-2t|S|}$ (or normalized $q_t(S)$ / hypercontractive interpolation / log-Sobolev / Talagrand / Eldan–Gross stochastic localization on the hypercube!). Can stochastic localization (Eldan–Gross 2020/2022, which already gave revolutionary proofs of KKL, Talagrand, and Kahn–Kalai-adjacent Boolean inequalities!) control $H(\hat{f}^2)$ along the Brownian/martingale restriction path $f_t$?!
- **Adversarial Counterexample Search (What if FEI is FALSE?!):**
  - Disjoint balanced composition $f \circ g$ preserves boundedness of $H/\mathrm{Inf}$.
  - What about **shared-variable composition**, **unbalanced composition**, **algebraic codes / bent functions + sparse low-influence masking**, **address/index functions with correlated data bits**, or **recursive constructions where $\mathrm{Inf}$ grows slower than $H$**?
  - Use Python + fast Walsh–Hadamard Transform (`WHT`) to systematically probe whether $H(\hat{f}^2)/\mathrm{Inf}(f)$ can be driven arbitrarily high as $n \to \infty$!

## Required Deliverables in `/Users/mw/Desktop/math/pioneer/fei`
1. **`RESEARCH_ANALYSIS.md`**: Detailed, honest research report documenting:
   - All proof strategies and counterexample searches explored, Python scripts run (`scripts/`), and exact numerical tests/counterexamples to candidate lemmas.
   - Final verdict:
     - **Case A (Full Proof Found):** Complete, self-contained, verified mathematical proof (with explicit universal constant $C$, verified $> 6.5218$!) and clear explanation of how it overcomes the coordinate-splitting barrier.
     - **Case B (Counterexample Family Found):** Explicit infinite family $f_k : \{-1,1\}^{n_k} \to \{-1,1\}$ with rigorous proof that $H(\hat{f}_k^2) / \mathrm{Inf}(f_k) \to \infty$ as $k \to \infty$ (plus Python WHT verification for small $k$).
     - **Case C (No Full Proof Yet, Strongest Partial/Next Frontier):** Exact bottleneck diagnosis, any genuinely new theorem or record bound discovered, and concrete hypotheses for an Astra `max` escalation run.
2. **If Case A or Case B:**
   - Write **`FEI/Blueprint.lean`** (importing `FEI.Challenge`, compiling cleanly with `lake build`) containing the **exact Lean 4 architecture**: helper definitions, fine-grained lemmas (15–40 lines each when filled), mathematical proof hints above every `sorry`, and the top-level theorem proving `FourierEntropyInfluenceConjecture` (or `¬ FourierEntropyInfluenceConjecture`)!
   - Confirm via `lake build` that `FEI/Blueprint.lean` compiles cleanly with ZERO errors.
3. **If Case C:**
   - Save all Python WHT / search / verification scripts under `scripts/` and any verified auxiliary Lean lemmas cleanly compiling with `lake build`.
