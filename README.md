# Justin Sun Prize Lean formalizations — JSP-301 & JSP-307

Lean 4 (mathlib) formal proofs of two problems from The Justin Sun Prize problem bank, by **Shiqiang Chen (GitHub: shunfeng8421)**.

## JSP-492 — Superlinear number of pairs at a fixed distance on a sphere

**Problem (catalog JSP-000492, Erdős #605; Swanepoel–Valtr Thm 1):** Can the number of pairs at one distance in a finite spherical point set grow superlinearly?

**Answer: Yes.** Swanepoel–Valtr (2004) and Erdős–Hickerson–Pach (1989): on the unit sphere the number of unit-distance pairs can be at least c·n·√(log n) for a constant c > 0.

The machine-checked Lean 4 (mathlib) proof is in **Jsp492.lean**:
- Jsp492.swanepoel_valtr — Theorem 1 of Swanepoel–Valtr in D=√2 critical-diameter form: ∃ c > 0 (c = 1/(72√3)), ∀ n ≥ 2, ∃ B ⊆ sphere 0 (1/√2), |B| = n ∧ c·n·√(log n) ≤ unorderedUnitPairs B.
- Jsp492.jsp492_official — official catalog corollary: ∃ f : ℕ → ℝ with  → ∞, ∀ n ≥ 2, ∃ B ⊆ sphere 0 1, |B| = n ∧ n·f(n) ≤ unorderedUnitPairsAtSqrt2 B.

Build: Lean 4.34.0 (lean-toolchain), mathlib 4.34.0 (lakefile.toml); lake exe cache get, then lean Jsp492.lean. Axioms: [propext, Classical.choice, Quot.sound].


## JSP-301 — Consecutive powerful numbers need not be squares

**Problem:** If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No.** `12167 = 23³` and `12168 = 2³·3²·13²` are consecutive powerful numbers, and neither is a square (both lie strictly between 110² and 111²).
The machine-checked proof is in **`Jsp301.lean`**, central theorem `Jsp301.JSP_301`.

## JSP-307 — Consecutive integers with strictly decreasing largest prime factors

**Problem:** Can three consecutive integers have strictly decreasing largest prime factors?

**Answer: Yes.** `13, 14, 15` have largest prime factors `13 > 7 > 5`:
- `13 = 13` — LPF 13
- `14 = 2·7` — LPF 7
- `15 = 3·5` — LPF 5

The machine-checked proof is in **`Jsp307.lean`**, central theorem `Jsp307.JSP_307 : ∃ n, IsLPF n 13 ∧ IsLPF (n+1) 7 ∧ IsLPF (n+2) 5`.
Mathematical existence due to Erdős–Pomerance [ErPo78] and Balog [Ba01]; this is a formalization-only contribution.

## Reproduce

```sh
git clone <repo-url>
cd jsp301
lake build Jsp301     # or: lake env lean Jsp301.lean
lake env lean Jsp307.lean
```
Toolchain pinned `leanprover/lean4:v4.34.0`, mathlib v4.34.0. No `sorry`/`axiom`/`admit`.

## Identity
Formalization: Shiqiang Chen. First-public-visibility timestamps: JSP-301 — 2026-09-16 19:09 UTC (initial repo creation); JSP-307 — added to this public repository 2026-09-17.
