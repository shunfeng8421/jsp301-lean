# JSP-301 — Consecutive powerful numbers need not be squares

Lean 4 (mathlib) formal proof / disproof of the problem **JSP-000301** from
The Justin Sun Prize problem bank:

> **If two consecutive positive integers are powerful, must at least one be a
> perfect square?**

**Answer: No.** A counterexample is the consecutive pair

```
12167 = 23³            (powerful, not a square)
12168 = 2³ · 3² · 13²  (powerful, not a square)
```

Both numbers are powerful (every prime divisor appears to exponent ≥ 2), and
neither is a perfect square, since both lie strictly between the consecutive
squares 110² = 12100 and 111² = 12321.

This repository contains the formal statement and a machine-checked Lean proof
of these facts.
The central theorem is `Jsp301.JSP_301`.

## Highlights

* `def Jsp301.IsPowerful n` — every prime `p | n` also satisfies `p² | n`.
* `def Jsp301.IsSquare n` — `n = m²` for some `m`.
* `theorem Jsp301.JSP_301 : ∃ n m, m = n + 1 ∧ IsPowerful n ∧ IsPowerful m ∧ ¬ IsSquare n ∧ ¬ IsSquare m`

## Build

```sh
git clone <repo-url>
cd jsp301
lake exe cache get     # fetch prebuilt mathlib
lake build Jsp301
```

Toolchain pinned in `lean-toolchain`: `leanprover/lean4:v4.34.0`
(matches `require mathlib` at `rev = "v4.34.0"`).

## Source

* Erdős/Golomb problem statement as catalogued in the Justin Sun Prize problem
  bank (JSP-000301). The counterexample appears in M. V. Subbarao, and related
  families in the "powerful numbers" literature.
* Full factorizations verified directly by `norm_num`/`rfl` inside Lean.

## Identity

Formalization: Shiqiang Chen (GitHub: shunfeng8421). **Published 2026-09-17
(UTC 2026-09-16 19:09)**. First-public-visibility timestamp for this
formalized counterexample is the creation date of this repository.