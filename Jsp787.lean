import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic

/-!
# JSP-787 · Consecutive integers with equal divisor counts (scoped component)

**Problem (catalog JSP-000787):** *Are there infinitely many consecutive
positive integers with equal divisor counts?* (d(n) = d(n+1) infinitely often)

**Scoped component (existence):** Yes, at least one such pair exists: `2` and
`3` each have exactly two positive divisors, so `d(2) = d(3) = 2`.

Scoped formalization of the existence aspect (analogous to scoped components
by CollinYuanjieRen). Full infinite-family result due to Erdős–Mirsky [ErMi52],
improved by Heath-Brown [He84]; this file formalizes the explicit witness.
-/

namespace Jsp787

/-- The number of positive divisors of `n`. Defined by counting the `d` in
`[1, n]` that divide `n`. Uses an explicit list so small cases are decidable. -/
def DivCount (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter (fun d => d ∣ n)).length

/-- 2 has two divisors in [1,2]: 1 and 2. -/
theorem divCount_2 : DivCount 2 = 2 := by
  native_decide

/-- 3 has two divisors in [1,3]: 1 and 3. -/
theorem divCount_3 : DivCount 3 = 2 := by
  native_decide

/-- Consecutive integers 2 and 3 have equal divisor counts: d(2) = d(3) = 2. -/
theorem JSP_787_existence :
    ∃ n : ℕ, 0 < n ∧ DivCount n = DivCount (n + 1) := by
  refine ⟨2, by norm_num, ?_⟩
  rw [divCount_2, divCount_3]

end Jsp787