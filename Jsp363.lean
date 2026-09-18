import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000363 · Integers with a divisor in a short interval — constructive scoped fragment

Problem (catalog JSP-000363): *What proportion of integers have a divisor in
the specified interval with endpoint ratio t?*  Solved (Behrend 1934, On the
density of certain sequences of integers).  The problem is currently unclaimed
on the official awards repo.

This file formalizes explicit constructive content for the interval `[2,4]`: a
positive integer `n` has NO divisor in `[2,4]` iff it is not divisible by 2 and
not divisible by 3.  (A divisor 4 would already imply divisibility by 2, so
"divisor in {2,3,4}" reduces to "divisor in {2,3}".)  This gives the exact
complementary set whose density the problem considers, for the concrete
interval `[2,4]`.
-/

namespace Jsp363

/-- `n` has a divisor in the interval `[2,4]`: some of 2, 3, 4 divides `n`. -/
def HasDivisor24 (n : ℕ) : Prop := 2 ∣ n ∨ 3 ∣ n ∨ 4 ∣ n

/-- If 4 divides `n` then 2 divides `n`, so the disjunct `4 ∣ n` is redundant:
`HasDivisor24 n` iff `2 ∣ n ∨ 3 ∣ n`. -/
theorem has_divisor24_iff_23 : ∀ n : ℕ, HasDivisor24 n ↔ (2 ∣ n ∨ 3 ∣ n) := by
  intro n
  constructor
  · intro h
    rcases h with h2 | h3 | h4
    · exact Or.inl h2
    · exact Or.inr h3
    · -- 4 | n implies 2 | n
      left
      rcases h4 with ⟨k, hk⟩
      refine ⟨2 * k, ?_⟩
      omega
  · intro h
    rcases h with h2 | h3
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)

/-- `n` has NO divisor in `[2,4]` iff it is not divisible by 2 and not divisible
by 3.  (Negating `HasDivisor24 n = (2∣n ∨ 3∣n)` gives `¬2∣n ∧ ¬3∣n`.) -/
theorem no_divisor24_iff :
    ∀ n : ℕ, ¬ HasDivisor24 n ↔ (¬ 2 ∣ n ∧ ¬ 3 ∣ n) := by
  intro n
  rw [has_divisor24_iff_23]
  constructor
  · intro h
    constructor
    · intro h2; exact h (Or.inl h2)
    · intro h3; exact h (Or.inr h3)
  · intro h
    intro hn
    rcases hn with h2 | h3
    · exact h.1 h2
    · exact h.2 h3

/-- Concretely, `1`, `5`, and `7` have no divisor in `[2,4]`; `6` and `8` do.
-/
theorem concrete_no_divisor :
    ¬ HasDivisor24 1 ∧ ¬ HasDivisor24 5 ∧ ¬ HasDivisor24 7 ∧
    HasDivisor24 6 ∧ HasDivisor24 8 := by
  norm_num [HasDivisor24]

end Jsp363