# Catch-Up Game Even-Sum Draw Conjecture

- **Field:** Theoretical Computer Science — Combinatorial Game Theory
- **Catalog References:** Bernhard von Stengel, *"Catch-Up: A Rule to Make Going First an Advantage"* ([MPRA Paper 108784](https://mpra.ub.uni-muenchen.de/108784/), 2019), `google-deepmind/formal-conjectures` (`FormalConjectures/Paper/CatchUpConjecture.lean`)
- **Status:** Open (Full conjecture and $N = 51$ unresolved — **Case C**); **new world record for exact prefix verification ($N = 48$ exact draw; every opening draws for $12 \le N \le 44$)**, **6-token necessity & sufficiency theorem for first-player loss**, **68,199,392-board exhaustive density verification through $\max \le 32$**, **universal infinite-family draw theorems** (critical high intervals, 10-token adjacent holes, arbitrary bank embeddings, exact upper minimum-pick ray), and **137 kernel-verified Lean 4 theorems** (`77` public / `60` private; `88` public research declarations, `28,259` audited constants, zero `sorry`) across 3 `max` rounds.
- **Frozen Challenge Statement:** [`CatchUpGame/Challenge.lean`](CatchUpGame/Challenge.lean)
  - **SHA-256:** `0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3`
  - Statement: for every $N \in \mathbb{N}$ such that $N(N+1)/2$ is even (i.e., $N \equiv 0, 3 \pmod 4$), the two-player Catch-Up game on $\{1, \ldots, N\}$ (turn passes upon reaching or exceeding the opponent's score) ends in an exact draw under optimal play.

---

## Headline Results

Full proofs, C++/Python exact verifiers, and verification ledgers across all three rounds are documented in [`RESEARCH_ANALYSIS.md`](RESEARCH_ANALYSIS.md).

1. **Exact Prefix Verification Extended to $N = 48$ (beats published $N \le 34$):**
   - Verified every eligible prefix $N \equiv 0, 3 \pmod 4$ through **$N = 48$** is an exact draw (independently confirmed at $N = 48$ by dual scalar/fixed-player C++17 solvers + Lean opening reversal, with both players guaranteeing `588`).
   - Verified that **every** legal first move draws for every eligible $12 \le N \le 44$.
   - Kernel-proved the exact outcome along the **entire upper tail** of the minimum-pick path (`upper_minimum_ray`): for every $N$ and $\lfloor N/2 \rfloor + 2 \le a \le N$, $G([a, N], \lfloor a/2 \rfloor)$ is a strict loss when the interval length is even and a strict win when odd (with explicit boundary transitions characterized at $N = 48$ and $N = 51$).
2. **Translation-Stable Infinite-Family Draw Theorems (Lean 4 Kernel-Verified):**
   - **Critical high intervals $([a, a+2n-1], n)$:** Proved exact draw for **every height $a \ge 2n - 1$** across $1 \le n \le 8$ in Lean 4 (`high_interval_draw_through_eight`, via kernel-verified uniform-strategy soundness `shiftHold_sound`) and $1 \le n \le 16$ via exact packed two-bitset computation ([`scripts/uniform.cpp`](scripts/uniform.cpp)). For arbitrary $n$, proved the leading player always holds (`high_interval_nonwin`), every non-maximum pick strictly loses for $a \ge 2n + 1$ (`high_interval_only_max`), and reduced the full general-$n$ proof to strict interior deletions (`high_interval_of_interior_holes`).
   - **Ten-token adjacent-hole family (`ten_interval_adjacent_holes`):** Removing any adjacent pair from $[a, a+9]$ yields a tied draw for **every** $a \ge 1$ and all 9 hole positions.
   - **Arbitrary bank embedding (`bank_pair_draw` & `draw_of_bank_lift`):** Any finite set $B$ of positive tokens with sum $W = \sum B$ embeds into a tied draw $B \cup \{W+1, W+2, W+3\}$ (and more generally $B \cup \{W+e, u, v\}$ whenever $e = v - u$ and $W + 2e \le u$).
   - **Exact prefix reduction (`draw_of_two_offsets`):** Reduced `value [1, N] = draw` to checking $([4, N], 2)$ plus non-winning tied adjacent deletions from $[2, N]$ and $[3, N]$.
3. **Minimum First-Player Loss & Universal Fixed-Cap Obstruction:**
   - **6 tokens are necessary and sufficient for a first-player loss** on arbitrary distinct positive integers: Lean 4 kernel witness $\{4, 5, 6, 7, 12, 14\}$ (`six_loss`), combined with a finite-representative bound ($m^{m/2}$) and exhaustive independent verification of all **3,478,761** normalized 5-token boards (zero first-player losses), plus exact closed-form formulas for 3-token, 4-token, and 5-term arithmetic-progression boards.
   - **Fixed-overshoot cap impossibility (`capped_two_iff`, `capped_card_bound`):** Kernel-proved that no strategy capping overshoot at any fixed $K$ can prove the conjecture for arbitrary prefixes (any board holding under cap $K$ has at most $4K$ tokens exceeding $K$).
4. **68,199,392-Board Exhaustive Density Verification & Brown-Completeness Refutation:**
   - Exhaustively verified that **every** nonempty even-sum board $S \subseteq \{1, \ldots, 32\}$ satisfying $3|S| > 2\max(S) + 1$ is a draw: **68,199,392 draws, 0 wins, 0 losses** (`30,214,299` through $\max \le 31$ + `37,985,093` at $\max = 32$), along with all **8,921,362** even-sum boards containing the contiguous bank $[1, 8]$ through $\max \le 32$ ([`scripts/layer.cpp`](scripts/layer.cpp)).
   - Kernel-proved that Brown-completeness alone does not force a draw (`complete_bank_counterexample`): $\{1, 2, 3, 7, 9, 11, 14, 15, 22\}$ is Brown-complete with even sum 84, yet is a first-player win.

---

## Lean 4 Verification (`137` Theorems / `88` Public Declarations)

Built with **Lean 4.36.0** + **Mathlib `v4.36.0`**. Zero `sorry`, zero `admit`, zero `native_decide`; [`scripts/audit.py`](scripts/audit.py) inspects all **88 public research declarations** (`77` public theorems + `11` public definitions/inductives, alongside `60` private helper theorems) and all **28,259 constants** (`28,187` in `ResearchLemmas` + `72` in `Challenge`), verifying that every dependency lies strictly within Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| File | Role |
|---|---|
| [`CatchUpGame/Challenge.lean`](CatchUpGame/Challenge.lean) | Frozen, read-only conjecture statement (1:1 with `formal-conjectures`) |
| [`CatchUpGame/ResearchLemmas.lean`](CatchUpGame/ResearchLemmas.lean) | Gap-value equivalence, opening reversal, exact $N \le 12$ kernel proof, 6-token witness, $4K$ cap obstruction, `bank_and_pairs`, `draw_of_two_offsets`, `shiftHold_sound`, `high_interval_draw_through_eight`, `ten_interval_adjacent_holes`, `bank_pair_draw`, `upper_minimum_ray` |

---

## Reproduction

```bash
# 1. Verify frozen statement integrity
shasum -a 256 CatchUpGame/Challenge.lean
# Expected: 0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3

# 2. Build all 88 public Lean 4 declarations and audit all 28,259 constants
lake build
python3 -B scripts/audit.py

# 3. Compile and audit the exact C++17 solvers (uniform high-interval, 32-layer density, fixed-player, scalar)
clang++ -O3 -march=native -std=c++17 -pthread scripts/uniform.cpp -o /tmp/cu3-uniform
clang++ -O3 -march=native -std=c++17 -pthread scripts/layer.cpp -o /tmp/cu3-layer
clang++ -O3 -march=native -std=c++17 -pthread scripts/defense.cpp -o /tmp/cu3-defense
clang++ -O3 -march=native -std=c++17 scripts/threshold.cpp -o /tmp/cu3-threshold
python3 -B scripts/round3.py audit /tmp/cu3-uniform /tmp/cu3-defense /tmp/cu3-layer
python3 -B scripts/round3.py examples
```
