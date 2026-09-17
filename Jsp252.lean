import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000252 · Subsets whose reciprocal sum is one — constructive scoped fragment

Problem (catalog JSP-000252): *How many subsets of a finite integer range have
reciprocal sum exactly one?*  Solved (Stark 2024, On a problem involving unit
fractions).  The problem is currently unclaimed on the official awards repo.

This file formalizes explicit constructive content: several subsets of the
range `[1,30]` have reciprocal sum exactly one:

* `{2,3,6}`         : 1/2+1/3+1/6 = 1
* `{2,3,8,24}`      : 1/2+1/3+1/8+1/24 = 1
* `{2,3,9,18}`      : 1/2+1/3+1/9+1/18 = 1
* `{2,3,10,15}`     : 1/2+1/3+1/10+1/15 = 1
* `{2,4,5,20}`      : 1/2+1/4+1/5+1/20 = 1
* `{2,4,6,12}`      : 1/2+1/4+1/6+1/12 = 1

Each is a distinct-unit-fraction representation of 1 with denominators in the
range.  We verify the rational equalities by `norm_num`.
-/

namespace Jsp252

/-- `1/2+1/3+1/6 = 1`. -/
theorem rep_236 : (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 6 := by norm_num

/-- `1/2+1/3+1/8+1/24 = 1`. -/
theorem rep_23824 : (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 8 + 1 / 24 := by norm_num

/-- `1/2+1/3+1/9+1/18 = 1`. -/
theorem rep_23918 : (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 9 + 1 / 18 := by norm_num

/-- `1/2+1/3+1/10+1/15 = 1`. -/
theorem rep_231015 : (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 10 + 1 / 15 := by norm_num

/-- `1/2+1/4+1/5+1/20 = 1`. -/
theorem rep_24520 : (1 : ℚ) = 1 / 2 + 1 / 4 + 1 / 5 + 1 / 20 := by norm_num

/-- `1/2+1/4+1/6+1/12 = 1`. -/
theorem rep_24612 : (1 : ℚ) = 1 / 2 + 1 / 4 + 1 / 6 + 1 / 12 := by norm_num

/-- At least six distinct subsets of `[1,30]` have reciprocal sum one (each
stated above), giving a constructive lower bound on the count in the problem.
-/
theorem at_least_six_subsets :
    (1 : ℚ) = 1/2 + 1/3 + 1/6 ∧
    (1 : ℚ) = 1/2 + 1/3 + 1/8 + 1/24 ∧
    (1 : ℚ) = 1/2 + 1/3 + 1/9 + 1/18 ∧
    (1 : ℚ) = 1/2 + 1/3 + 1/10 + 1/15 ∧
    (1 : ℚ) = 1/2 + 1/4 + 1/5 + 1/20 ∧
    (1 : ℚ) = 1/2 + 1/4 + 1/6 + 1/12 := by
  norm_num

end Jsp252