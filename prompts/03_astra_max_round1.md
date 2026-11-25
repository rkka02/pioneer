# Astra MAX Escalation — Round 1 of 2 (Tutte's 3-Flow Conjecture)

You are resuming your previous session on `Tutte3FlowConjecture` with **`model_reasoning_effort="max"`**.
Do NOT repeat completed small-order censuses or basic background already recorded in `RESEARCH_ANALYSIS.md`. Focus all reasoning depth on **breaking through to a complete proof or a genuine counterexample** of `Tutte3FlowConjecture` (still strictly keeping `Tutte3Flow/Challenge.lean` untouched!).

## Priority Breakthrough Directions for This MAX Run

### 1. Base-Polyhedron & Discrete Convexity Reformulation (ALL 5-Edge-Connected Multigraphs)
First, clarify precisely what Kochol's (2001) reduction gives (5-edge-connected multigraphs, and whether 5-regularity is genuinely equivalent without creating 4-cuts — do NOT assume 5-regularity unless rigorously justified!).
For **ANY** finite 5-edge-connected loopless multigraph $G$, our Lean-verified theorem `exists_orientation_with_outdegrees_iff` + `exists_intFlow_lifting` already reduces `Tutte3FlowConjecture` completely to:
> Does the orientation base polyhedron
> $$B(G) = \left\{ q \in \mathbb{Z}^V : \sum_{v \in V} q(v) = |E|,\quad \sum_{v \in S} q(v) \ge e(S)\ \forall S \subseteq V \right\}$$
> intersect the modular lattice coset $L(G) = \{ q \in \mathbb{Z}^V : \forall v,\ 2q(v) \equiv d(v) \pmod 3 \}$?

Notice the exact geometry behind the 6-vs-5 barrier:
- The fractional center $q^* = \frac{1}{2} d$ satisfies $q^*(S) - e(S) = \frac{1}{2} |\delta(S)|$ for every shore $S$.
- At 6-edge-connectivity, the slack is $\ge 3$ (the exact lattice step size 3!). At 5-edge-connectivity, the slack is $\ge 5/2$ — **only $1/2$ short of 3**, and equality $5/2$ ONLY occurs at odd cuts of size 5!
- Investigate deeply:
  1. **Rounding / Discrepancy / Submodular-Base Intersection:** Can $q^* = \frac{1}{2}d$ be rounded into $B(G) \cap L(G)$ using a polymatroid / laminar-tight-set / Lovász-splitting / iterative-rounding / Beck–Fiala-style linear-algebraic rounding argument that exploits the $5/2$ slack + integrality of $e(S)$ and $3\mathbb{Z}$ step parity?
  2. **Equal-Deficit Lattice Escape (General $q \in L(G)$):** Your `xhigh` run found that on EVERY tested graph (including all 7,841 order-12 graphs, the 18-vertex obstruction, and the flower-snark derivative), every stalled positive-deficit state in $L(G)$ escaped to strictly lower deficit $D(q) = \max_S (e(S) - q(S))$ after **at most ONE neutral ($D$-preserving) single-step exchange** ($q \mapsto q + 3 e_u - 3 e_w$)!
     - First, **stress-test this conjecture ruthlessly in Python** on larger and weirder 5-edge-connected multigraphs (including glued 5-cuts, multiple stalled pockets, non-5-regular 5-edge-connected graphs, random/adversarial `n=20..40` graphs): can you find ANY 5-edge-connected graph with a trapped level-set component (no escape via neutral single swaps, or requiring $> 1$ neutral swap)?
     - Second, analyze the **lattice of maximizing shores** $\mathcal{M}(q)$ (plus the near-maximizing shores $f_q(S) \in \{d-1, d-2\}$ that block direct descent!). Since $f_q$ is supermodular, $\mathcal{M}(q)$ has a unique minimum $S_{\min}$ and maximum $S_{\max}$. Can you prove a **strict lexicographic descent theorem** (either via single neutral exchanges or via a **multi-vertex augmenting chain** along the tight-shore poset) showing that whenever $D(q) > 0$, there exists a finite chain of $3\mathbb{Z}$-exchanges strictly reducing $D(q)$?
     - Watch out for parity and slack: remember $2 f_q(S) = 2e(S) - 2q(S) = \sum_{v\in S}(d(v)-2q(v)) - |\delta(S)|$. What constraints do $d(S) \ge 5$ and $f_q(S_{\min}) = d > 0$ force on vertices INSIDE $S_{\min}$ and OUTSIDE $S_{\max}$?

### 2. Dual / Min-Max & Separating 5-Cut Composition
- If $B(G) \cap L(G) = \emptyset$, what **dual certificate** (combinatorial, linear-algebraic, or matroidal) must exist?
- On graphs with separating 5-cuts, test whether $|\mathrm{supp}\, p| \ge 3$ always holds for zero-boundary 5-edge-connected halves (or find a counterexample half with $|\mathrm{supp}\, p| \le 2$!). If a half with $|\mathrm{supp}\, p| \le 2$ exists, gluing two such halves with mismatched permutation **IMMEDIATELY CONSTRUCTS A COUNTEREXAMPLE TO TUTTE'S 3-FLOW CONJECTURE!!** Check this aggressively in Python!

### 3. Adversarial Counterexample Hunting (Don't Ignore Case B!)
- Search specifically for a rooted 5-edge-connected zero-boundary half (5 dangling ports) whose minority-port support has size $\le 2$ (or even $\le 1$)! Remember: by your §2 formula $2 \sum_{i=1}^5 p_i q_{\pi(i)}$, finding ANY two 5-edge-connected halves with $|\mathrm{supp}\, p| + |\mathrm{supp}\, q| \le 5$ immediately yields a 5-edge-connected counterexample to Tutte's 3-Flow Conjecture!

## Required Outputs
- **Zero bluffing.** Test every lemma on adversarial instances before claiming it.
- **If Case A (Complete Proof) or Case B (Counterexample):**
  - Write a completely self-contained `PROOF.md` with every step verified.
  - Write **`Tutte3Flow/Blueprint.lean`** (importing `Tutte3Flow.Challenge`, `Tutte3Flow.Equivalence`, `Tutte3Flow.PrescribedDegrees`, `Tutte3Flow.IntegralLift`) decomposing the entire proof into clean 15–40 line lemmas with proof comments above every `sorry`, ending in `theorem tutte3Flow_resolved : Tutte3FlowConjecture` (or `¬ Tutte3FlowConjecture`), and verify `lake build` succeeds with ZERO errors!
- **If still Case C:**
  - Update `RESEARCH_ANALYSIS.md` with the new Round-1 MAX theorems, obstructions, exact Python scripts, any new Lean-verified lemmas, and the sharpest single target for MAX Round 2.
