import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000243 · Shortest interval with distinct unit-fraction sum to 1 — constructive scoped fragment

Problem (catalog JSP-000243): *What is the shortest integer interval containing
distinct denominators whose reciprocals sum to one?*  Solved (Croot 2001, On
unit fractions with denominators in short intervals).  The problem is currently
unclaimed on the official awards repo.

This file formalizes explicit constructive content: the interval `[2, 6]` of
length 4 contains the distinct denominators `2, 3, 6`, whose reciprocals sum to
1:

    1 = 1/2 + 1/3 + 1/6

We verify the equality (norm_num) and that the three denominators are distinct
and all lie in the interval `[2,6]` (native_decide).
-/

namespace Jsp243

/-- `1 = 1/2 + 1/3 + 1/6`, distinct unit-fraction representation of 1 with all
denominators inside the interval `[2,6]`. -/
theorem one_rep_in_interval : (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 6 := by
  norm_num

/-- The three denominators are distinct. -/
theorem denominators_distinct : List.Nodup [2, 3, 6] := by
  decide

/-- Every denominator lies in the interval `[2,6]`. -/
theorem denominators_in_interval : ∀ d ∈ ([2, 3, 6] : List ℕ), 2 ≤ d ∧ d ≤ 6 := by
  intro d hd
  simp at hd
  rcases hd with rfl | rfl | rfl <;> norm_num

/-- The interval `[2,6]` realizes the representation: its width is 4, and it
contains distinct denominators summing (in reciprocal) to 1. -/
theorem interval_realizes_one :
    (∀ d ∈ ([2, 3, 6] : List ℕ), d ≥ 2 ∧ d ≤ 6) ∧
    (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 6 ∧
    List.Nodup [2, 3, 6] := by
  constructor
  · exact denominators_in_interval
  constructor
  · exact one_rep_in_interval
  · exact denominators_distinct

end Jsp243