# Astra MAX Escalation — Round 3 of 3 (Grand Finale: Fonollosa's Minimum Modulus Conjecture)

This is the **3rd and final `max` round** on session `01a21437-0d41-7bd3-99f2-01c11afec3c9`.
Your Round 2 breakthrough was extraordinary:
- **New published-record general cyclic lower bound, kernel-verified in Lean 4 (`RankPacking.cyclic_nine_sixteenths`):**
  $$N \ge \frac{9}{16} \cdot 2^n \qquad (\forall n \ge 3),$$
  beating Sitjar's Nov 2026 Theorem A for every $n \ge 10$ (27 audited Lean 4 declarations, `leanchecker --fresh` passed, zero `sorry`, standard axioms only!),
- Raised the unrestricted $n = 10$ lower bound to **$N \ge 614$**, eliminated ALL nonunit-difference 10-sets across all 447 moduli $569 \le N \le 1015$, and narrowed $N = 1015$ down to unit-normalized $(0, 1, z, \dots)$ with $3 \le z \le 26$!

Make **Round 3 of 3** an unforgettable finale! Strike BOTH high-leverage objectives below (keeping `FonollosaMinModulus/Challenge.lean` completely untouched, `SHA-256: 3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`):

## Objective 1 — Push the Unconditional General Cyclic Lower Bound STRICTLY ABOVE $\frac{9}{16} \cdot 2^n$ (Lean 4 Kernel-Verified!) — AND Swing for Case A!
Look at the **immediate structural goldmine** sitting right inside your Round 2 proof of (R2.1)–(R2.2):
1. **Immediate $\frac{9}{16} \to \frac{37}{64}$ (and sharper!) Upgrade via Singleton-Exclusion + $t \ge 2$ Bollobás:**
   - In (R2.2), you bounded $\binom{2t}{t}/4^t \le \frac{1}{2}$, which is ONLY attained at $t = 1$ (a singleton exchange $x \to y$ with $y - x = 2d$)!
   - For ALL $t \ge 2$, $\binom{2t}{t}/4^t \le \mathbf{\frac{3}{8}}$!
   - Meanwhile, whenever $4d \ne 0$ and there is NO antipodal collision on $g = 2d$ (automatically true whenever $d$ has order $> 4$ — guaranteed for all $n \ge 5$ in ANY cyclic group!):
     - **Case 1 (No singleton exchange for $g = 2d$):** Every exchange has $t \ge 2$, so $E_R(2d) \le \frac{3}{8} \cdot 2^r$ directly by Bollobás!
     - **Case 2 (A singleton exchange $x \to y$ exists for $g = 2d$):** As you ALREADY proved in Round 2 (eq on p. 283), every other exchange crosses $\{x, y\}$, giving $E_R(2d) \le 2^{r-2} + E_{R \setminus \{x, y\}}(4d) \le \left(\frac{1}{4} + \frac{1}{8}\right) 2^r = \frac{3}{8} \cdot 2^r$ (and recursing once more gives $\le \frac{11}{32} \cdot 2^r$, or in the limit $\le \frac{1}{3} \cdot 2^r$ when $2^k d$ stays non-antipodal!!)!
   - Plugging $E_R(2d) \le \frac{3}{8} \cdot 2^r$ into (R2.1) `5 · 2^r ≤ 2N + E_R(2d)` **IMMEDIATELY** gives:
     $$N \ge \frac{37}{64} \cdot 2^n \quad (= 0.578125 \cdot 2^n)!!$$
2. **GO EVEN FURTHER — Multi-Slot ($6, 7, 8, \dots$ labels), Skew Bollobás, Multi-Pivot Averaging, & Exact Optimization of the Constant $c$ in $N \ge c \cdot 2^n$!**
   - **TEST THIS CAREFULLY:** What happens when you generalize (R2.1) from **5 labels** to **$L = 6, 7, 8, \dots$ labels** (or **3-pivot / $k$-pivot** labelings on $R = A \setminus \{a_1, \dots, a_k\}$!) using **skew Bollobás** ($\sum_{(D, C)} \binom{|D|+|C|}{|D|}^{-1} \le 1$ for unequal-size crossing exchanges $(D, C)$ with $|C| - |D| = w$!)?
     - Specifically check: for $L$ labels in $\mathbb{Z}/N \times \{0, 1\}$, which label collisions occur, how does skew Bollobás bound EACH collision class $E_R^{(w)}(jd)$, AND do **simultaneous collisions at DIFFERENT $(w, j)$** also satisfy **joint crossing / mutual exclusion** (or does averaging over all $\binom{n}{2}$ pivot pairs $(a, b)$ kill the singleton/double-exchange mass because $|\Delta| = n(n-1)$ allows at most ONE pair to achieve $y - x = 2d$ per $d$, and even tighter: **how many pairs $(a, b)$ can have large $E_R(2(b-a))$ simultaneously**?!)?
   - **Can you push the unconditional constant $c$ in $N \ge c \cdot 2^n$ past $\frac{37}{64}$ to $\frac{5}{8} = 0.625$, $\frac{2}{3}$, $\frac{3}{4}$, or even $1 - o(1)$ / full Case A?!**
   - **Formalize your STRONGEST new unconditional general lower bound in Lean 4** (`FonollosaMinModulus/ResearchLemmas.lean` — or `Solution.lean` if Case A!) with ZERO `sorry`, ZERO `admit`, ZERO `native_decide`, `lake build` + `leanchecker --fresh` + standard axioms ONLY!

## Objective 2 — Complete the $N = 1015$ Target-Sum Four-Clique Exhaustion (`3 ≤ z ≤ 26`) & Tighten $n = 10$!
Execute your Round 2 target cleanly:
1. Implement the **depth-6 target-sum four-clique solver** in blazing-fast multi-threaded C++17 (`-O3 -march=native -pthread`) to **100% exhaust the remaining $3 \le z \le 26$ unit-normalized prefixes at $N = 1015$** (and also $N = 1014, 1013$ if fast!).
   - **If a valid 10-set exists at $N = 1015$ (or $1014, 1013$)** $\implies$ **INSTANT CASE B DISPROOF OF FONOLLOSA'S CONJECTURE!!** Verify independently and write a ZERO-`sorry` Lean 4 `Solution.lean` proving `¬ FonollosaMinModulusConjecture`!
   - **If ZERO valid 10-sets exist at $N = 1015$** $\implies$ you establish the **first-ever complete exclusion of $N = f(10) - 1 = 1015$** (the single most dangerous boundary modulus just below $2^{10} - 8 = 1016$!), independently double-checked!
2. Also see how high your **new Objective 1 lower bound + Round 2 exchange/profile bounds** push the continuous unrestricted $n = 10$ lower bound above $614$ (e.g., to $640+$ or $700+$?)!

## Required Outputs (Round 3 of 3)
- **NEVER modify `FonollosaMinModulus/Challenge.lean`** (verify SHA-256 `3a275f872e63da865d3636a81abd5d9065e75716389f450564d42515666d1d91`).
- **Zero bluffing.** Every claim backed by rigorous proof, exact C++/Python verification, or Lean 4 kernel proof.
- **If Case A (Full Proof!) or Case B (Counterexample!):**
  - Produce `PROOF.md` + `FonollosaMinModulus/Solution.lean` proving `FonollosaMinModulusConjecture` OR `¬ FonollosaMinModulusConjecture`, compiling cleanly with `lake build` + `leanchecker --fresh` + standard axioms ONLY!
- **If still Case C (Final 3-Round Synthesis):**
  - Append **`## Round 3 — Final Push & Campaign Synthesis`** to `RESEARCH_ANALYSIS.md` (keeping Rounds 1–2 byte-identical!), presenting:
    1. Your strongest new unconditional cyclic lower bound $N \ge c \cdot 2^n$ (and its Lean 4 kernel proof + `leanchecker --fresh` + full axiom inventory),
    2. Complete outcome of the $N = 1015$ (`3 ≤ z ≤ 26`) exhaustion and updated continuous $n = 10$ range,
    3. Reproducible verification commands, and
    4. Ranked list of the **top publishable standalone contributions** from this 3-round campaign!
