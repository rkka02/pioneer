# Task: Formalize and Freeze `Tutte3Flow/Challenge.lean` (Tutte's 3-Flow Conjecture)

You are formalizing the canonical, unweakened statement of **Tutte's 3-Flow Conjecture (1972)** in Lean 4 (`v4.36.0` + Mathlib) inside `/Users/mw/Desktop/math/pioneer/tutte3flow`.

## Requirements for `Tutte3Flow/Challenge.lean`

1. **Full, Unweakened Statement (Finite Multigraphs + Nowhere-Zero Integer 3-Flow)**
   - Define a clean, completely transparent `FinMultigraph (V E : Type*)` structure (allowing parallel edges; self-loops allowed and handled naturally because loops cross 0 cuts and contribute 0 net flow).
   - Define `cutEdges (G : FinMultigraph V E) (S : Finset V)` as the set of edges with one endpoint in `S` and the other in `Sᶜ` (i.e., `(G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S)`).
   - Define `IsKEdgeConnected (G : FinMultigraph V E) (k : ℕ) : Prop` as: for every `S : Finset V`, if `S.Nonempty` and `S ≠ Finset.univ`, then `k ≤ (G.cutEdges S).card`.
   - Define `IsNowhereZeroIntFlow (G : FinMultigraph V E) (k : ℕ) (f : E → ℤ) : Prop` as:
     - `∀ e : E, f e ≠ 0 ∧ |f e| < k`, and
     - `∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => G.src e = v), f e) = (∑ e ∈ Finset.univ.filter (fun e => G.dst e = v), f e)`.
   - Define `HasNowhereZeroIntFlow (G : FinMultigraph V E) (k : ℕ) : Prop := ∃ f, G.IsNowhereZeroIntFlow k f`.
   - Also define the equivalent **nowhere-zero `ZMod 3`-flow** (`HasNowhereZeroZMod3Flow`) and **modulo-3 orientation** (`HasMod3Orientation`) in `Challenge.lean` so downstream proof files can cleanly reference them, while keeping the headline conjecture statement strictly the classical **integer nowhere-zero 3-flow**:
     ```lean
     def Tutte3FlowConjecture : Prop :=
       ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
         (G : FinMultigraph V E),
         G.IsKEdgeConnected 4 → G.HasNowhereZeroIntFlow 3
     ```
   - Make sure `Tutte3Flow/Challenge.lean` has **ZERO `sorry`**, **ZERO custom axioms**, clean imports, and compiles cleanly with `lake build Tutte3Flow.Challenge`.

2. **Mandatory Non-Vacuity & Sharpness Sanity Checks (`Tutte3Flow/ChallengeSanity.lean`)**
   - Create `Tutte3Flow/ChallengeSanity.lean` importing `Tutte3Flow.Challenge`, and prove (with **ZERO `sorry`**):
     1. A concrete 4-edge-connected multigraph (e.g., 2 vertices with 4 parallel edges, AND/OR $K_5$) satisfies `IsKEdgeConnected 4` and `HasNowhereZeroIntFlow 3` (proves hypotheses are non-vacuous).
     2. The complete graph $K_4$ satisfies `IsKEdgeConnected 3` AND `¬ HasNowhereZeroIntFlow 3` (proves the connectivity threshold `4` is sharp and the flow definition is NOT vacuously satisfied!).
     3. Prove `HasMod3Orientation G ↔ HasNowhereZeroZMod3Flow G` (and `HasNowhereZeroIntFlow G 3 → HasNowhereZeroZMod3Flow G`) cleanly in `ChallengeSanity.lean` (or `Tutte3Flow/Equivalence.lean`).

3. **Verification**
   - Run `lake build` and confirm **zero errors, zero warnings on sorry/axioms**.
   - Keep `Tutte3Flow/Challenge.lean` minimal, crystal clear, and audit-ready so we can freeze it read-only before starting the proof attack.
