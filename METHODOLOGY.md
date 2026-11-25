# Pioneer Research Methodology

**Pioneer** is an open, multi-domain mathematical research repository combining frontier AI mathematical reasoning, exact symbolic/numerical verification, and **Lean 4** formal verification across open problems in combinatorics, analysis, number theory, algebra, geometry, probability, and theoretical computer science.

---

## 1. Repository Organization

Problems are organized strictly by **mathematical field** rather than by any single external benchmark or list, so that problems from ProofAtlas, the Erdős Problem list, `teorth/optimizationproblems`, arXiv preprints, and independent research live side-by-side cleanly:

```text
pioneer/
├── README.md                  # Master scoreboard & catalog overview
├── METHODOLOGY.md             # This protocol
├── catalog.json               # Machine-readable registry (field, tags, external IDs, status, Lean stats)
└── problems/
    ├── combinatorics/
    │   └── tutte-3-flow/
    ├── analysis/
    │   └── fourier-entropy-influence/
    ├── number-theory/         # Created on demand
    ├── algebra/               # Created on demand
    ├── geometry/              # Created on demand
    ├── probability/           # Created on demand
    └── tcs/                   # Created on demand
```

Each problem directory is a **self-contained Lean 4 + verification project** containing:
- `README.md` — concise summary, external references, frozen challenge SHA-256, headline results, Lean inventory, and reproduction commands.
- `<Pkg>/Challenge.lean` — frozen, audited Lean 4 statement of the full unweakened conjecture.
- `<Pkg>/*.lean` — kernel-verified auxiliary theorems, reductions, sanity checks, and standalone results.
- `RESEARCH_ANALYSIS.md` — complete, chronological mathematical write-up across all research rounds (honestly distinguishing proved theorems, computer-assisted results, obstructions, and remaining open gaps).
- `scripts/` — exact integer/rational Python verifiers, C++ census tools, and Lean axiom auditors.
- `prompts/` — full prompt trail used to drive multi-round reasoning sessions for complete transparency and reproducibility.

---

## 2. Frozen-Challenge Integrity Protocol

To guarantee zero goal-post moving or accidental statement weakening:
1. **Prior-art audit:** Before starting any target, audit against published literature, recent arXiv preprints, `openai/math`, `awesome-ai-proofs`, `google-deepmind/formal-conjectures`, and live GitHub repositories.
2. **Statement freeze:** Formalize the **exact, unweakened** open problem in `<Pkg>/Challenge.lean` (plus `<Pkg>/ChallengeSanity.lean` proving sharpness/nontriviality witnesses so vacuous formulations are caught immediately).
3. **Immutability lock:** Mark `Challenge.lean` read-only (`0444`), record its **SHA-256 hash**, and re-verify the hash after every single research round.

---

## 3. Multi-Round Research & Verification Pipeline

1. **Deep Mathematical Exploration (Multi-Round Escalation):**
   - Start with an `xhigh` reconnaissance round to map reductions, small-order censuses, and sharp obstructions.
   - Escalate through consecutive `max` rounds (continuing the same reasoning context so no mathematical insight is lost and zero work is repeated), incorporating cross-pollination from recent frontier mathematical papers and open repositories.
   - Explicitly classify every round as:
     - **Case A** — Complete proof of the frozen conjecture (triggers immediate `Blueprint.lean` + full Lean 4 formalization),
     - **Case B** — Explicit disproof / counterexample (triggers exact verification + Lean 4 refutation), or
     - **Case C** — Unresolved overall, with honest reporting of all newly proved partial theorems, world-record constants, obstructions, and Lean-verified modules.
2. **Zero-Bluffing Verification Standard:**
   - All numerical certificates use **exact integer/rational arithmetic** with outward-rounded interval bounds (never uncertified floating-point claims).
   - Large enumerations use **two independent implementations** plus independent combinatorial checks (e.g., Burnside counts).
   - All Lean 4 modules must compile cleanly via `lake build` with **zero `sorry`**, **zero `admit`**, **zero `native_decide`**, and pass automated `#print axioms` checks permitting only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. **Formalization Scaling:**
   - Full proofs, disproofs, and flagship standalone theorems can be handed to downstream Lean 4 formalization sprints (e.g., Claude Opus 5.5) against the frozen `Challenge.lean` or standalone theorem targets.
