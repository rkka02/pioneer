# Astra MAX Attack — Round 1: Catch-Up Game Even-Sum Draw Conjecture

## Frozen Target (`CatchUpGame/Challenge.lean` — READ-ONLY, NEVER MODIFY!)
**Catch-Up Even-Sum Draw Conjecture (Isaksen–Ismail–Brams–Nealen, 2015):**
Two players play **Catch-Up** on the finite set $S = \{1, 2, \dots, N\}$ starting at scores $(0, 0)$:
1. On the first move, Player 1 picks **one** number $x \in S$ and passes the turn.
2. On every subsequent turn, the active player picks numbers one by one from the remaining set until their cumulative score becomes **$\ge$** the opponent's score, at which point the turn passes. (If taking all remaining numbers still leaves them behind, they take everything and lose.)
3. When $S$ becomes empty, higher score wins; equal score is a draw.

**Conjecture (`CatchUpConjecture`):** Whenever the total sum $T_N = N(N+1)/2$ is **even** (equivalently $N \equiv 0, 3 \pmod 4$), optimal play ALWAYS results in a **draw** (`value (Finset.Icc 1 N) = .draw`).

*Background:* Previously verified by exact backward induction only up to $N \le 20$ (and only MCTS heuristics for $N = 23, 24, 27, 28$). Completely open as of late 2026!

## Mission: Go Straight for the Kill (Case A Full Proof OR Case B Counterexample!)
You have full access to `/Users/mw/miniconda3/bin/python3` (NumPy, Numba), `clang++ -O3 -march=native`, Lean 4.36.0 (`lake build`), and `web_search`.

### Attack Strategy (Hit BOTH Sides Hard!)
1. **Immediate High-Speed Exact C++ Solver & Structure Mining (Case B Test + Strategy Discovery!):**
   - Notice a HUGE state-space collapse:
     - `valueAux remaining s_me s_opp false` depends ONLY on `(remaining, gap)` where `gap = s_opp - s_me` (since scores only enter through their difference `s_opp - s_me`!) — AND `0 ≤ gap ≤ remaining.sum` (and actually `gap ≤ max(remaining)` at the start of every turn, or bounded by the last picked element!).
     - Even more: you can write a **blazing-fast C++17 alpha-beta + transposition-table / retrograde solver** to solve Catch-Up **EXACTLY** for:
       - ALL even-sum $N = 3, 4, 7, 8, 11, 12, 15, 16, 19, 20, \mathbf{23, 24, 27, 28, \dots}$!!
       - **AND ALSO** solve **arbitrary finite subsets** $S \subset \mathbb{N}$ of even sum (e.g. $\{1, \dots, N\}$ minus pairs, arithmetic progressions, general multiset/subset families!) to discover **WHAT INVARIANT** keeps a position drawable!!
   - **IF ANY $N \equiv 0, 3 \pmod 4$ (e.g., $N = 23, 24, 27, 28, \dots$) IS NOT A DRAW — CASE B!**
     - Extract a compact winning strategy tree (a winning strategy for P1 or P2 only needs ONE move per winner node and ALL responses per loser node — often tiny!), verify it independently, AND **write a COMPLETE, ZERO-`sorry` Lean 4 disproof (`CatchUpGame/Solution.lean` proving `¬ CatchUpConjecture`)** with `lake build` + `#print axioms` passing (standard axioms ONLY, no `native_decide`!) and write `PROOF.md`!
2. **Direct Constructive Proof Attack (Case A Test — Explicit Draw Strategy!):**
   - To prove `value (Finset.Icc 1 N) = .draw`, you need **TWO** explicit non-losing strategies:
     1. **Player 1 can force at least a draw** (existence of an opening move $x_1 \in \{1, \dots, N\}$ and response strategy guaranteeing `s_1 ≥ s_2` at the end), AND
     2. **Player 2 can force at least a draw** (for EVERY opening move $x_1 \in \{1, \dots, N\}$ of Player 1, a response strategy guaranteeing `s_2 ≥ s_1` at the end)!
   - **THINK LIKE A COMBINATORIAL GAME THEORIST!**
     - First, check if a **strategy-stealing** or **symmetry / pairing / mirror / complementary-sum** argument works!
       - Wait: on $\{1, \dots, 4k\}$, pair $(1, 4k), (2, 4k-1), \dots, (2k, 2k+1)$ — every pair sums to $4k+1$, and there are $2k$ (EVEN!) pairs! Wait: what about pairing $(1, 4k-1), (2, 4k-2), \dots$ or grouping into zero-sum quads $\{a, a+3\}$ vs $\{a+1, a+2\}$ (each quad splits into two equal sums $2a+3 = 2a+3$!!)?!
       - **WAIT A SECOND!! STOP AND LOOK AT QUADS $\{4j+1, 4j+2, 4j+3, 4j+4\}$!!**
         - On $\{1, \dots, 4k\}$: the set partitions into $k$ disjoint quads $\{4j+1, 4j+2, 4j+3, 4j+4\}$ where $(4j+1)+(4j+4) = (4j+2)+(4j+3)$!
         - On $\{1, \dots, 4k+3\}$: $\{1, 2, 3\}$ has $1 + 2 = 3$, and the remaining $\{4, \dots, 4k+3\}$ partitions into $k$ quads $\{4j+4, 4j+5, 4j+6, 4j+7\}$ with equal pair sums!!
         - Wait: can a player maintain a **pairing / involution / copycat / bounded-lead / greedy** invariant across turns?! Why does naive pairing break? Because Catch-Up forces you to STOP as soon as `s_me' ≥ s_opp`, so you might NOT be allowed to pick a mate on the same turn if you already caught up!
         - **INSPECT THE ACTUAL OPTIMAL PLAY TREES** for $N = 3, 4, 7, 8, 11, 12, 15, 16, 19, 20$ in C++/Python! Look for:
           - Which opening moves $x_1$ draw for P1 (does $x_1 = N$ or $x_1 = 1$ or $x_1 = \lfloor N/2 \rfloor$ ALWAYS draw?!)?
           - What is the **simplest structural invariant** $\Phi(S, \text{gap})$ on remaining sets $S$ and lead `gap` such that $\Phi$ is preserved by a simple explicit move rule (e.g., always respond to keep `gap` small, or maintain a partition of $S$ into balanced pairs/triples/blocks, or reduce $N \to N - 4$!!)?
           - **HOLD ON — CHECK INDUCTION $N \to N - 4$ (OR GENERALIZED EVEN-SUM SETS $S$)!** Wait: which even-sum sets $S \subset \mathbb{N}$ are NOT draws?! Knowing the **exact characterization** (or small counterexample sets $S$ with even sum where Catch-Up is NOT a draw!) will IMMEDIATELY tell you what special property of $\{1, \dots, N\}$ forces the draw (or breaks down at large $N$)!
   - **IF YOU FIND A FULL PROOF — CASE A!**
     - Write `PROOF.md` AND **write a COMPLETE, ZERO-`sorry` Lean 4 proof (`CatchUpGame/Solution.lean` proving `CatchUpConjecture`)**, verify `lake build` + `#print axioms` (standard axioms ONLY)!

## Required Outputs
- **NEVER modify `CatchUpGame/Challenge.lean`** (verify SHA-256 before and after!).
- **Zero bluffing.** Every claim backed by rigorous proof, exact C++/Python verification, or Lean 4 kernel proof.
- **If Case A (Full Proof!) or Case B (Counterexample!):**
  - Produce `PROOF.md` + `CatchUpGame/Solution.lean` (imported by `CatchUpGame.lean`) proving `CatchUpConjecture` OR `¬ CatchUpConjecture`, compiling cleanly under `lake build` with **ZERO `sorry`**, **ZERO `admit`**, **ZERO `native_decide`**, standard axioms ONLY!
- **If Case C (Unresolved in Round 1):**
  - Write `RESEARCH_ANALYSIS.md` with exact backward-induction table (including new exact values for $N > 20$!), characterization of non-draw even-sum subsets $S$, all proved partial theorems & strategy-invariant tests, all scripts in `scripts/`, kernel-verified Lean 4 lemmas in `CatchUpGame/ResearchLemmas.lean` (`lake build` + axiom audit clean), and the sharpest Round 2 attack!
