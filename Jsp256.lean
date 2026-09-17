import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000256 · Minimal largest denominator in distinct unit fraction representations — constructive scoped fragment

Problem (catalog JSP-000256): *How small can the largest denominator be in a
representation of a given positive rational number by distinct unit fractions?*
Solved (Bleicher & Erdős 1976, Denominators of unit fractions, J. Number Theory
1976, 157–168).  The problem is currently unclaimed on the official awards repo.

This file formalizes explicit constructive content: for several positive
rationals we exhibit representations as sums of **distinct** unit fractions and
record the largest denominator used.  Concretely:

* `1   = 1/2 + 1/3 + 1/6`                      (largest denominator 6)
* `5/4 = 1/2 + 1/3 + 1/4 + 1/6`                (largest denominator 6)
* `4/3 = 1/2 + 1/3 + 1/4 + 1/6 + 1/12`         (largest denominator 12)
* `3/2 = 1/2+1/3+1/4+1/6+1/10+1/12+1/15`       (largest denominator 15)

Each denominator appears at most once (distinct), and all are at most the
stated bound.  We verify the rational equalities by `norm_num` and distinctness
by `native_decide`.
-/

namespace Jsp256

/-- `1 = 1/2 + 1/3 + 1/6`, a distinct unit-fraction representation with largest
denominator 6. -/
theorem one_rep : (1 : ℚ) = (1 / 2 : ℚ) + 1 / 3 + 1 / 6 := by
  norm_num

/-- `5/4 = 1/2 + 1/3 + 1/4 + 1/6`, a distinct unit-fraction representation with
largest denominator 6. -/
theorem five_fourths_rep : (5 / 4 : ℚ) = 1 / 2 + 1 / 3 + 1 / 4 + 1 / 6 := by
  norm_num

/-- `4/3 = 1/2 + 1/3 + 1/4 + 1/6 + 1/12`, a distinct unit-fraction representation
with largest denominator 12. -/
theorem four_thirds_rep : (4 / 3 : ℚ) = 1 / 2 + 1 / 3 + 1 / 4 + 1 / 6 + 1 / 12 := by
  norm_num

/-- `3/2 = 1/2+1/3+1/4+1/6+1/10+1/12+1/15`, a distinct unit-fraction
representation with largest denominator 15. -/
theorem three_halves_rep :
    (3 / 2 : ℚ) = 1 / 2 + 1 / 3 + 1 / 4 + 1 / 6 + 1 / 10 + 1 / 12 + 1 / 15 := by
  norm_num

/-- The denominators in the `1` representation are distinct. -/
theorem one_rep_distinct : List.Nodup [2, 3, 6] := by
  native_decide

/-- The denominators in the `5/4` representation are distinct. -/
theorem five_fourths_rep_distinct : List.Nodup [2, 3, 4, 6] := by
  native_decide

/-- The denominators in the `4/3` representation are distinct. -/
theorem four_thirds_rep_distinct : List.Nodup [2, 3, 4, 6, 12] := by
  native_decide

/-- The denominators in the `3/2` representation are distinct. -/
theorem three_halves_rep_distinct : List.Nodup [2, 3, 4, 6, 10, 12, 15] := by
  native_decide

end Jsp256