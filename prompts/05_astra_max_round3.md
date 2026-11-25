# Astra MAX Escalation — Round 3 of 5 (Fourier Entropy–Influence Conjecture)

The user has expanded our cap to **5 `max` rounds** on session `01a212d2-dcd9-7c42-aade-61e556a007b8`.
Your Round 2 results dramatically narrowed the entire FEI landscape:
- Proved fixed-degree $B_{\le D} \le 3(D-1) + 4 + 4/\ln 2$ (and $\to 0$ as $W_1 \to 1$),
- Proved $X < 78I$ for all symmetric Boolean functions (and multiblock generalization),
- Proved $\mathbb{E} H(zf) \le 24\mathbb{E} I(zf)$ for all Gaussian ensembles and $\mathbb{E} X < 290\mathbb{E} I$ for Gaussian two-shell ensembles,
- Proved additive telescoping $N(F) - N(g) \le 5(I_F - I_g)$ and $P_2(F) - P_2(g) \le 74(I_F - I_g)$ for repeated disjoint-table linear-address routing + quadratic phase,
- Proved the **dyadic two-shell parity obstruction** (unsigned affine mass + shifted Chang tests are insufficient; signed affine-flat congruences $\sum_{T \in C} a_T \in 2^{1-r}\mathbb{Z}$ rule out every Boolean signing!),
- Proved the **regional granularity bound** on $K \ge \lambda d_\uparrow(S)$ and isolated the **exact Round 3 single-slice subcube-perturbation reduction** $\mathcal{E}_z(A, C)$!

Do NOT repeat Round 1–2 tests. For **MAX Round 3 of 5**, strike straight at the **TWO deepest remaining openings** exposed by Round 2 (keeping `FEI/Challenge.lean` completely untouched!):

## Priority Attack Plan for MAX Round 3

### 1. Positive Proof Attack: Quantifying the Signed Boolean Constraint & Effective Granularity
Round 2 proved TWO remarkable structural facts:
1. **Unsigned spectral constraints fail** (dyadic two-shell passes every shifted Chang & unsigned affine-mass bound yet diverges).
2. **Every supported $S$ with $K \ge \lambda d_\uparrow(S)$ ALREADY satisfies the full pooled $P_2/I$ bound** because $a_S \in 2^{1 - d_\uparrow(S)}\mathbb{Z}$!
3. **Full FEI $\iff$ uniform absolute bound on $\mathcal{E}_z(A, C)$** for rare subcube perturbations ($\Pr(A \triangle C) \le \mu^3$, excess boundary $\le \mu^3$).

Attack this head-on from THREE sharp mathematical angles:
- **Angle 1A — Quantifying the Signed Affine-Flat Congruences ($\sum_{T \in C} a_T \in 2^{1-r}\mathbb{Z}$):**
  - You proved that a diverging dyadic two-shell spectrum breaks parity on a codimension-$k$ flat.
  - Can you turn the **full system of signed affine-flat congruences** (or the equivalent physical-space **Boolean cube / Gowers-like / Möbius-inversion / decision-tree-residual / edge-isoperimetric** decomposition of $\mathbf{1}_A - \mathbf{1}_C$) into a **quantitative inequality** bounding $\mathcal{E}_z(A, C)$ or $B(g)$ or $N(f)$?
  - Specifically, look at $\Delta = \mathbf{1}_A - \mathbf{1}_C \in \{-1, 0, 1\}$ (or more generally ANY Boolean function $f$): instead of the fragile global $d_\uparrow(S)$, can you decompose $f$ (or $\Delta$) into pieces $f = \sum_m g_m$ (e.g., via **cube-partition / junta-plus-sparse / recursive high-degree peeling / martingale / entropy-chain-rule over a data-dependent revealing order**) where EACH piece has controlled granularity relative to its degree AND its boundary cost charges cleanly to $I(f)$?
- **Angle 1B — Direct Analysis of the Single-Slice Target $\mathcal{E}_z(A, C)$:**
  - In the Round 3 target, $A$ is a subset of the cube of volume $\mu = 2^{-r-1}$ whose edge boundary exceeds the Harper/subcube minimum $2\mu\log_2(1/\mu)$ by at most $\mu^3$!
  - **CRITICAL TOOL CHECK:** By **Ellis–Keller–Lifshitz / Keevash–Long / Kahn–Kalai / Friedgut–Kalai–Naor / Harper stability (sharp edge-isoperimetric stability on the Boolean cube!)**, sets $A$ with tiny excess edge boundary $\varepsilon = I(h_A) - 2\mu\log_2(1/\mu)$ have rigid geometric structure (they are extremely close to a subcube $C$, and the *perturbation* $A \triangle C$ itself sits near the boundary of $C$ or forms tiny isolated islands!).
  - Wait: if $A \triangle C$ sits on a single subcube / tiny island, your Round 2 reduction ALREADY showed that embedding an arbitrary counterexample inside a tiny subcube preserves the ratio! So check carefully: does **Harper stability** add any genuine constraint on the *internal* structure of $A \triangle C$, OR does the exact scaling invariance prove that $\mathcal{E}_z(A,C)$ requires a scale-invariant Boolean spectral inequality on $h$ itself? Diagnose this with razor precision — do NOT chase a tautology!
- **Angle 1C — Resolving the Mixed Moment $X(f)/I(f)$ Globally (or Killing It!):**
  - Remember: $X(f) \le K I(f)$ STILL has ZERO counterexamples across ALL Boolean functions, and implies FULL FEI!
  - Can you EITHER prove $X(f) \le K I(f)$ for a much wider class (or all Boolean functions!) OR finally **construct a Boolean family with $X(f)/I(f) \to \infty$** (which by your Round 2 dichotomy also makes unnormalized $X(G) \to \infty$ as $I(G) \to 1$)?

### 2. Counterexample Hunt in the Exact Uncharted Blind Spot of Round 2: Shared/Coded Data + High-Degree Shells!
Look at the **ONE construction that broke Round 2's additive routing theorem (line 129)**:
- **Invertible linear coding of the *data* bits** (an invertible linear transformation on data bits jumped $X$ from $0$ to $7/16$ at identical $I = 5/2$!).
- Explore **iterated / multi-stage coded-data constructions** AND **structured non-Gaussian Boolean functions with $K \ll d_\uparrow(S)$**:
  1. **Iterated Coded-Data Multiplexers / Linear-Code-Coupled Gates:** Start from your line-129 5-bit coded bent×dictator gadget (or higher-dimensional linear-code hyperplanes / Reed–Muller / BCH / dual Hamming / quadratic forms over $\mathbb{F}_2$ composed with shared coded data tables!) and iterate / compose! Does $X(f)/I(f)$ or $B(g)$ grow unboundedly?!
  2. **Deterministic Non-Gaussian Two-Shell Boolean Approximations:** Round 2 proved that *random* Gaussian signs of a two-shell spectrum stay bounded ($\mathbb{E} X < 290 \mathbb{E} I$). What about **deterministic, algebraically structured** Boolean functions (e.g., **indicator of a union of disjoint affine subspaces / cosets of codes / Reed–Muller / bent-sum cascades / majority-of-parities / symmetric-of-bent**) whose spectrum concentrates heavily on two adjacent high-degree shells while keeping influence small?!
  3. **Push the Certified Lower Bound Record (`71a`) if a Breakthrough Construction Emerges!** (Note: don't spend Round 3 tweaking decimals by $10^{-7}$ on Numaro's 9-edge core — ONLY chase lower-bound improvements if a genuinely new structural family promises a *macro* jump like $> 6.6$, $> 7$, or divergence!)

## Required Outputs (Round 3 of 5)
- **Keep `FEI/Challenge.lean` completely untouched** (verify SHA-256 `6bd49da1...`).
- **Zero bluffing.** Every claim backed by proof or exact Python WHT / rational interval verification.
- **If Case A (Complete Proof!) or Case B (Diverging $B(g)$ / FEI Disproof!):**
  - Write complete, self-contained `PROOF.md`.
  - Write **`FEI/Blueprint.lean`** importing `FEI.Challenge`, `FEI.ChallengeSanity`, `FEI.ResearchLemmas`, decomposing the full proof into 15–40 line lemmas with proof hints above every `sorry`, ending in `FourierEntropyInfluenceConjecture` (or `¬ FourierEntropyInfluenceConjecture`), and verify `lake build` compiles cleanly!
- **If still Case C:**
  - Prepend **`## MAX Round 3`** to `RESEARCH_ANALYSIS.md` with all new theorems, exact scripts, any new Lean lemmas in `FEI/ResearchLemmas.lean` (`lake build` passing), AND the single sharpest target for **Round 4 of 5**!
