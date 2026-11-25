# Research Mission: Attack Tutte's 3-Flow Conjecture (ProofAtlas #355)

We have frozen the canonical, unweakened Lean 4 statement of **Tutte's 3-Flow Conjecture** in `Tutte3Flow/Challenge.lean`:
> Every finite 4-edge-connected multigraph admits a nowhere-zero integer 3-flow (equivalently, a nowhere-zero $\mathbb{Z}/3\mathbb{Z}$-flow / modulo-3 orientation).

Your mission as our flagship mathematical reasoning engine (`GPT-6.2 Astra`, `xhigh`) is to conduct a **deep, rigorous, zero-bluff mathematical attack** on `Tutte3FlowConjecture` — aiming to discover either a **complete proof** or a **counterexample** — and if a viable proof/disproof emerges, architect a clean Lean 4 lemma blueprint (`Tutte3Flow/Blueprint.lean`) ready for downstream formalization by Claude Code (`Opus 5.5`).

## Rules of Engagement (STRICT)
1. **DO NOT edit `Tutte3Flow/Challenge.lean`.** It is frozen.
2. **ABSOLUTE MATHEMATICAL HONESTY — ZERO BLUFFING:**
   - Every intermediate claim/lemma MUST be stress-tested against small adversarial graphs (including Petersen-derived graphs, flower snarks, 5-regular 5-edge-connected graphs, and boundary-function instances `(G, β)`!).
   - You have full access to Python in this workspace: **USE PYTHON** to empirically test candidate inductive hypotheses, boundary functions, discharging rules, splitting-off lemmas, and potential counterexamples before trusting any lemma!
   - If an approach hits a genuine obstruction, **explicitly document the exact counterexample/obstruction** rather than handwaving past it.

## Known Frontier Context (Do Not Rediscover Trivially; Build Beyond It)
- **Tutte (1954/1972):** Nowhere-zero integer 3-flow $\iff$ nowhere-zero $\mathbb{Z}_3$-flow $\iff$ mod-3 orientation ($\deg^+(v) \equiv \deg^-(v) \pmod 3$).
- **Kochol (2001):** Tutte's 3-flow conjecture for 4-edge-connected graphs is equivalent to the **5-edge-connected** case (and to bridgeless graphs with at most three 3-edge-cuts; minimal counterexample is 5-edge-connected, has no non-trivial 4-edge-cuts, and in fact reductions exist to 5-regular / odd-5-edge-connected structures).
- **Thomassen (2012) & Lovász–Thomassen–Wu–Zhang (LTWZ, 2013):** Every **6-edge-connected** (more generally, odd-7-edge-connected / $(3k-2)$-edge-connected for mod-$k$) graph admits a mod-3 orientation (and every 6-edge-connected graph is $\mathbb{Z}_3$-connected? Wait: check precisely — LTWZ proved $d$-strongly connected / boundary-function theorem with $|E(A, A^c)| \ge 6$ or specific boundary slack!).
- **Why LTWZ stops at 6-edge-connected:** Analyze the exact arithmetic bottleneck in LTWZ's boundary-function induction (`(G, β)` with root vertex `z_0` of degree bounded, lifting pairs of edges at `z_0`, and the contraction step when a tight cut of size 5 appears!).
- **Recent 2024–2026 frontier:** Li et al. (`arXiv:2609.08377`, Sept 2026) handled 4-edge-connected graphs allowing 5-edge-cuts when all edge-cuts of sizes $6, \dots, 40$ are forbidden; Ahanjideh–Kovács (`arXiv:2603.24175`, Mar 2026) gave a new characterization for simple 5-valent graphs.

## Strategic Directions to Explore (Don't Settle for the First Idea)
Explore and stress-test multiple genuinely distinct attack vectors:
1. **Refining/Breaking the LTWZ (2013) Inductive Barrier (6 → 5):**
   - Can a sharper boundary-function invariant (incorporating parity, 2-connected/3-edge-cut structure, multiple roots, fractional/convex relaxation, or a non-linear potential function over cuts) survive the 5-edge-cut tight case?
   - Test EVERY candidate inductive statement in Python on 5-edge-connected graphs with arbitrary valid $\mathbb{Z}_3$-boundaries $\beta$ (including graphs built from $K_6$, Petersen lifts, $K_5$ with splits, and glued 5-cuts)!
2. **Algebraic / Polynomial / Linear-Algebraic & Matroidal Formulations:**
   - Reformulate mod-3 orientation as solving $B x \equiv 0 \pmod 3$ with $x \in \{\pm 1\}^E$ (or $\prod_v (1 - (\sum_{e \ni v} \sigma_{v,e} x_e)^2)$ / Combinatorial Nullstellensatz / Alon–Tarsi / Chevalley–Warning / permanent / quadratic forms over $\mathbb{F}_3$ / cycle-space non-vanishing vectors).
   - Can 5-edge-connectivity force non-vanishing of a specific coefficient or guarantee a nowhere-zero vector in the $\mathbb{F}_3$-cycle space $\ker_{\mathbb{F}_3}(B)$ via matroid / Tutte polynomial / rank-drop inequalities?
3. **Counterexample Hunting (Adversarial Construction):**
   - What if Tutte's 3-Flow Conjecture is **FALSE**?! (Remember: many classic conjectures like Hadwiger, Ryser, Borsuk, Li–Li fell to subtle counterexamples!)
   - Check systematically in Python (using SAT / ILP / Z3 / algebraic search over $\mathbb{F}_3$): are there small/medium 5-edge-connected (or 4-edge-connected) graphs without mod-3 orientations — e.g., constructed by gluing gadgets with forced $\mathbb{Z}_3$-boundaries (non-$\mathbb{Z}_3$-connected 4- or 5-edge-connected graphs! Wait: Jaeger conjectured every 5-edge-connected graph is $\mathbb{Z}_3$-connected — can you first search for a 5-edge-connected graph that is NOT $\mathbb{Z}_3$-connected?!)?
4. **Reductions / Discharging / Local Reconfiguration:**
   - Reconfiguration of partial mod-3 orientations (minimizing number of bad vertices modulo 3; Kempe-like directed path/cycle switching; discharging on minimal counterexample).

## Required Deliverables in `/Users/mw/Desktop/math/pioneer/tutte3flow`
1. **`RESEARCH_ANALYSIS.md`**: Detailed, honest research report documenting:
   - All attack vectors explored, Python verification scripts run (`scripts/`), and exact counterexamples that refuted any naive lemmas.
   - Final verdict:
     - **Case A (Full Proof Found):** Complete, self-contained, verified mathematical proof + clear explanation of how it bypasses the LTWZ 6-vs-5 barrier.
     - **Case B (Counterexample Found):** Explicit finite 4-edge-connected multigraph + machine-checkable certificate (Python + Lean) proving `¬ HasNowhereZeroIntFlow 3`.
     - **Case C (No Full Proof Yet, Strongest Partial/Next Frontier):** Exact bottleneck analysis, any genuine new partial theorem discovered (verified against literature!), and concrete hypotheses for an Astra `max` escalation run.
2. **If Case A or Case B:**
   - Write **`Tutte3Flow/Blueprint.lean`** (importing `Tutte3Flow.Challenge`, compiling cleanly with `lake build`) containing the **exact Lean 4 architecture**: all helper definitions, decomposed lemmas (target 15–40 lines each when filled), clear mathematical proof comments above every `sorry`, and the top-level theorem proving `Tutte3FlowConjecture` (or `¬ Tutte3FlowConjecture`) from those lemmas!
   - Also verify via `lake build` that `Tutte3Flow/Blueprint.lean` typechecks cleanly with ZERO errors.
3. **If Case C:**
   - Still save all Python experiment scripts under `scripts/` and any verified auxiliary Lean lemmas (e.g., `Tutte3Flow/Equivalence.lean` proving `HasMod3Orientation G → HasNowhereZeroIntFlow G 3` — Tutte's equivalence!) cleanly compiling with `lake build`.
