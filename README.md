# Justin Sun Prize Lean formalizations — JSP-301 & JSP-307

Lean 4 (mathlib) formal proofs of two problems from The Justin Sun Prize problem bank, by **Shiqiang Chen (GitHub: shunfeng8421)**.

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
