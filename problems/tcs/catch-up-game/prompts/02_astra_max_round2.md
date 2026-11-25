# Astra MAX Escalation — Round 2 of 3: Catch-Up Game Even-Sum Draw Conjecture

The user has authorized **up to 3 `max` rounds** on session `01a21437-2605-7452-938a-521cfb56a95b`.
Your Round 1 work was phenomenal:
- Extended exact verification of the conjecture from $N \le 34$ (von Stengel 2019) all the way to **$N = 47$** (all openings draw for $12 \le N \le 36$; dual-solver verified openings 1 & 2 for $N = 39, 40, 43, 44, 47$),
- Proved globally that **6 tokens are necessary and sufficient for a first-player loss** on arbitrary distinct positive integers (finite representative lemma $m^{m/2}$ + 3,478,761-board dual check + Lean witness $\{4,5,6,7,12,14\}$),
- Exhaustively enumerated all **134,217,728** even-sum subsets of $[1, 28]$ and discovered the razor-sharp **density threshold $3|S| > 2\max(S) + 1 \implies \mathrm{draw}$** (zero exceptions across all 4,638,228 boards in $[1, 28]$ and 554 boundary boards in $[29, 36]$!),
- Formalized **46 Lean 4 public declarations** (including exact proof for all $N \le 12$, `hold_by_exact_subset`, and the exact reduction `draw_of_first_ray`: it suffices to prove $G([3, N], 1) = \mathrm{draw}$ and $G([1, N] \setminus \{1, b-1, b\}, 0) \ne \mathrm{win}$!).

Do NOT repeat Round 1. For **MAX Round 2 of 3**, **GO STRAIGHT FOR A COMPLETE CASE A PROOF** (while keeping an eye open for any Case B surprise!) — keeping `CatchUpGame/Challenge.lean` completely untouched (`SHA-256: 0c7b6e8f...`):

## Attack Priority 1 — Break Through to a Complete Proof (Case A!) via Explicit Self-Inductive Invariants!

Look closely at the **two killer clues** from your Round 1 data:
1. **Why did $\{1, 2, 3, 13, 14, 15\} \cup [17, 28]$ fail while EVERY board with $3|S| > 2M + 1$ drew?**
   Because losing/winning boards need a **subset-sum gap** (missing small/medium tokens so the defender cannot catch up cleanly without breaking parity or leaving an un-equalizable endgame)!
2. **You ALREADY proved `hold_by_exact_subset` in Lean 4:**
   Whenever the defender faces deficit $d > 0$ and finds a subset $C \subseteq R$ with $\sum C = d$ such that the tied remainder $R \setminus C$ is in a **non-winning tied class $\mathcal{T}$** (where the next opener cannot win), the defender IMMEDIATELY holds!

**ATTACK THIS HEAD-ON FROM THREE CONCRETE ANGLES:**

### Angle 1A — The "Small-Bank / Brown-Completeness + Top-Cancellation" Explicit Strategy!
Think! Suppose a tied board $R$ has even sum and consists of:
- A **"small bank"** $B \subseteq R$ that is **Brown-complete** (every integer in $[0, \sum B]$ is a subset sum of $B$, i.e., sorted $b_1 < b_2 < \dots < b_k$ satisfies $b_i \le 1 + \sum_{j < i} b_j$) — notice on $[1, N]$, just the bottom $k \approx \sqrt{2N}$ tokens have $\sum B \approx k^2/2 \ge N$, leaving **almost ALL of the board** untouched!
- A **"large reservoir"** $L = R \setminus B$ above $B$!
Now watch what happens if the defender plays from a **tied** board $R \in \mathcal{T}$:
- Opponent opens with **ONE** single token $x \in R$, creating deficit $d = x$.
- **Case 1 (Large opponent pick $x \in L$):** Instead of greedily burning the small bank $B$, can the defender pick **one large token $y \in L$** close to $x$ (either $y < x$ plus a tiny bank subset $C \subseteq B$ of sum $x - y$, **equalizing immediately** via `hold_by_exact_subset` while shrinking $L$ by 2 and barely touching $B$!! — OR $y > x$ passing a tiny lead $y - x$ that forces the opponent to shrink $L$ or stay near zero!!)?
- **Case 2 (Small opponent pick $x \in B$):** Even simpler — either cancel $x$ with a subset of $B$ (or a pair from $L$ / single $y$ giving tiny overshoot $y - x$), keeping $B$ Brown-complete (or keeping an explicit pairing/density invariant)!
- **CRITICAL TEST:** Notice that in your Round 1 test (`RESEARCH_ANALYSIS.md`, p. 167), requiring an *unconditional* immediate exact catch failed because you let the subset $C$ be *arbitrary* — whereas choosing $C$ **specifically to preserve Brown-completeness / density / pairing of the remaining board** (using `hold_by_exact_subset` ONLY onto boards inside $\mathcal{T}$!) avoids that trap completely!
- **TEST THIS IN C++ RIGHT NOW!** Using your exact `retrograde.cpp` 134M-board database on $[1, 28]$, test whether there exists a clean, **100% self-inductive class $\mathcal{T}$ of tied even-sum boards** (and companion small-deficit class $\mathcal{D}$) such that:
  1. $[1, N] \in \mathcal{T}$ for all sufficiently large admissible $N$ (with all smaller $N$ already proved!), AND
  2. For EVERY $R \in \mathcal{T}$ and EVERY opponent opening $x \in R$:
     - Either there is an exact-catch subset $C \subseteq R \setminus \{x\}$ with $\sum C = x$ and $R \setminus (\{x\} \cup C) \in \mathcal{T}$ (wait: check on $[1, 28]$ if **100% of boards in a clean subclass $\mathcal{T}$ admit an exact-catch subset $C$ keeping $R \setminus (\{x\} \cup C) \in \mathcal{T}$**!!),
     - OR a 2-step overshoot move $(x \to y > x)$ lands in $\mathcal{D}$ where every reply returns to $\mathcal{T}$!
- **WHOA — CHECK THAT EXACT QUESTION FIRST IN C++ ON $[1, 28]$:**
  > On the set $\mathcal{W}_{\mathrm{draw}}$ of ALL even-sum boards in $[1, 28]$ that draw: does there exist a **nonempty downward-closed-under-exact-catch** subset $\mathcal{T}$ (a fixed point of the operator $\Phi(\mathcal{T}) = \{R \text{ even-sum} : \forall x \in R,\ \exists C \subseteq R \setminus \{x\},\ \sum C = x \text{ and } R \setminus (\{x\} \cup C) \in \mathcal{T}\}$ — i.e., **the "always-exact-catch" core!**) that contains $[1, N]$ for $N \ge N_0$?!
  - **STOP AND THINK ABOUT HOW MIND-BLOWING THAT TEST IS!!**
  - Compute the exact **greatest fixed point $\mathcal{T}^*$** of the pure-exact-catch operator $\Phi$ on $[1, 20]$ and $[1, 24]$ in C++ in **under 5 seconds**!!
    - Remember: in Round 1 you tested *forced* exact catch (where the opponent could choose which exact catch? No, where you *had* to catch if possible — wait, why did it fail at $N=8$ and $N=12$?! Check whether $[1, 15], [1, 16], [1, 19], [1, 20], [1, 23], [1, 24]$ lie in $\mathcal{T}^*$, OR whether pure exact catch ALWAYS fails on some opening like $x = 1$ because no subset of $R \setminus \{1\}$ sums to $1$!!).
    - **AHA!! OF COURSE!!** On $x = 1$, NO subset of $R \setminus \{1\}$ sums to $1$! That's the **ONLY** reason pure exact-catch fails: when $x = \min(R)$ (or $x$ is smaller than any subset sum of $R \setminus \{x\}$)!
    - **NOW COMPUTE THE GREATEST FIXED POINT $\mathcal{T}_1^*$ OF THE "EXACT-CATCH-OR-SMALL-OVERSHOOT" OPERATOR** (where for $x \in R$, you may EITHER exact-catch $\sum C = x$ back into $\mathcal{T}_1^*$ OR overshoot by $1$ or $2$ into a tiny-gap companion set $\mathcal{D}_1^*$ — **EXACTLY mirroring your `draw_of_first_ray` theorem**!!)!
    - Seeing $\mathcal{T}_1^*$ and $\mathcal{D}_1^*$ explicitly on $[1, 20]$ / $[1, 24]$ will show you **WITH X-RAY VISION** the exact simple combinatorial invariant that closes inductively for ALL $N$!!

### Angle 1B — Direct Proof of the Density Theorem ($3|S| > 2M + 1 \implies \mathrm{draw}$) or Bounded-Hole Induction!
- Test directly in C++ on $[1, 28]$ whether the density class $\{S : 3|S| > 2\max(S) + 1\}$ is **closed** under a simple defensive turn (or what slightly refined condition — e.g., $c_1 |S| > c_2 \max(S) + c_3$, or **bounded number of holes** $M - |S| \le f(M)$, or **minimum-prefix + density** — IS closed)!
- Also check the **generalization of `draw_of_first_ray`** to **arbitrary intervals $[a, b]$** or **intervals with $h$ holes** (`[1, N] \ H`):
  - Notice `draw_of_first_ray` reduced $I = [1, N]$ to `[3, N]` at deficit `1` AND `[1, N] \ {1, b-1, b}` at deficit `0`!
  - What happens if you apply `draw_of_first_ray` **AGAIN** to `[3, N]` at deficit `1` (or shift/pair consecutive elements `(2k-1, 2k)` so every pair has difference `1`!!)?!
  - **WAIT A SECOND!!** On `[3, N]` at deficit `1`, EVERY adjacent pair `(x, x+1)` has difference `1`! What happens if P1/P2 uses adjacent pairs `(x, x+1)` to keep deficit $\in \{0, 1\}$?! Check what stops adjacent-pair play at $N = 8, 12$ and whether a **2-step lookahead / 3-token block** fixes it!

### Angle 1C — Literature Cross-Pollination (`bocowgill-collaborations/catch-up-research` & 2025–2026 papers)
- In Round 1 you cited `github.com/bocowgill-collaborations/catch-up-research/blob/main/docs/research-handoff.md`! Use `web_search` to inspect any useful structural lemmas or open obstacles documented there so we don't repeat dead ends and can build straight past them!
- Also check if $N = 48$ can be resolved faster (e.g., via opening reversal on openings `1, 2` with better move ordering / symmetry / hash packing — or if a surprise non-draw lurks at $N = 48$ or $N = 51$)!

## Required Outputs (Round 2 of 3)
- **NEVER modify `CatchUpGame/Challenge.lean`** (verify SHA-256 `0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3`).
- **Zero bluffing.** Every claim backed by rigorous proof, exact C++/Python verification, or Lean 4 kernel proof.
- **If Case A (Full Proof!) or Case B (Counterexample!):**
  - Produce `PROOF.md` + `CatchUpGame/Solution.lean` (imported by `CatchUpGame.lean`) proving `CatchUpConjecture` OR `¬ CatchUpConjecture`, with `lake build` + `scripts/audit.py` passing (ZERO `sorry`, ZERO `admit`, ZERO `native_decide`, standard axioms ONLY!).
- **If still Case C:**
  - Append **`## Round 2`** to `RESEARCH_ANALYSIS.md` (keeping Round 1 intact!), presenting:
    1. Exact greatest-fixed-point $\mathcal{T}_1^*$ / invariant-closure results from the 134M-board database (showing EXACTLY which explicit invariants close and which fail!),
    2. All newly proved structural / density / bounded-hole / interval theorems (with new kernel-verified Lean 4 proofs in `CatchUpGame/ResearchLemmas.lean`, `scripts/audit.py` passing with standard axioms only!),
    3. Any extended exact prefix results ($N = 48, \dots$),
    4. The single sharpest attack target for **Round 3 of 3**!
