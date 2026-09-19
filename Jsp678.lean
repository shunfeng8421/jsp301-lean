import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

/-!
# JSP-000678 · Values of n + totient(n) — constructive scoped fragment

Problem (catalog JSP-000678): *Does the set of values of an integer plus its
totient have positive density?*  Solved (GIL24, Numbers of the form k + f(k),
J. Number Theory 2024, 58–85).  The problem is currently unclaimed on the
official awards repo.

This file formalizes explicit constructive content: concrete values attained by
`n + Nat.totient n` (the integer plus Euler's totient function):

* 2 + φ(2) = 3    (φ(2)=1)
* 3 + φ(3) = 5    (φ(3)=2)
* 4 + φ(4) = 6    (φ(4)=2)
* 5 + φ(5) = 9    (φ(5)=4)
* 6 + φ(6) = 8    (φ(6)=2)
* 7 + φ(7) = 13   (φ(7)=6)
* 8 + φ(8) = 12   (φ(8)=4)

These exhibit elements of the set {n + φ(n)}.  Each concrete value is decided by
`native_decide` (totient of a concrete natural is finite/computable).
-/

namespace Jsp678

/-- φ(2) = 1, so 2 + φ(2) = 3. -/
theorem value_2_attained : 2 + Nat.totient 2 = 3 := by decide

/-- φ(3) = 2, so 3 + φ(3) = 5. -/
theorem value_3_attained : 3 + Nat.totient 3 = 5 := by decide

/-- φ(4) = 2, so 4 + φ(4) = 6. -/
theorem value_4_attained : 4 + Nat.totient 4 = 6 := by decide

/-- φ(5) = 4, so 5 + φ(5) = 9. -/
theorem value_5_attained : 5 + Nat.totient 5 = 9 := by decide

/-- φ(6) = 2, so 6 + φ(6) = 8. -/
theorem value_6_attained : 6 + Nat.totient 6 = 8 := by decide

/-- φ(7) = 6, so 7 + φ(7) = 13. -/
theorem value_7_attained : 7 + Nat.totient 7 = 13 := by decide

/-- φ(8) = 4, so 8 + φ(8) = 12. -/
theorem value_8_attained : 8 + Nat.totient 8 = 12 := by decide

/-- Several distinct values 3,5,6,9,8,13,12 are attained by n + φ(n). -/
theorem several_values_attained :
    (2 + Nat.totient 2 = 3) ∧ (3 + Nat.totient 3 = 5) ∧
    (4 + Nat.totient 4 = 6) ∧ (5 + Nat.totient 5 = 9) ∧
    (6 + Nat.totient 6 = 8) ∧ (7 + Nat.totient 7 = 13) ∧
    (8 + Nat.totient 8 = 12) := by
  repeat' decide

end Jsp678
