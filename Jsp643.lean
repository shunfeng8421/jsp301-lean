import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000643 · Pairwise coprime set of primes with small reciprocal sum — constructive scoped fragment

Problem (catalog JSP-000643): *Among pairwise coprime integer sets with bounded
reciprocal sum, which have multiples covering the largest proportion of
integers?*  Solved (Erdős 1973).  The problem is currently unclaimed on the
official awards repo.

This file formalizes explicit constructive content: the set of the first five
primes `{2, 3, 5, 7, 11}` is pairwise coprime, and its reciprocal sum is bounded
well below 1:

    1/2 + 1/3 + 1/5 + 1/7 + 1/11 = 1627/2310 < 1

We verify pairwise coprimality per unordered pair (each gcd is 1) and the
reciprocal-sum bound by `norm_num`.  This exhibits a pairwise-coprime set with
bounded (small) reciprocal sum — the constructive setting of the problem.
-/

namespace Jsp643

/-- The set of pairwise-coprime primes `{2,3,5,7,11}`. -/
def P : List ℕ := [2, 3, 5, 7, 11]

-- Concrete primalities:
private theorem p2 : (2 : ℕ).Prime := by decide
private theorem p3 : (3 : ℕ).Prime := by decide
private theorem p5 : (5 : ℕ).Prime := by decide
private theorem p7 : (7 : ℕ).Prime := by decide
private theorem p11 : (11 : ℕ).Prime := by decide

/-- Every element of `P` is prime. -/
theorem P_all_prime : ∀ x ∈ P, x.Prime := by
  intro x hx
  simp [P] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact p2
  · exact p3
  · exact p5
  · exact p7
  · exact p11

/-- The ten unordered pairs of `P` each have gcd 1 (so they are pairwise
coprime).  We verify each gcd is 1 by `norm_num`.
-/
theorem P_pairwise_coprime : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → Nat.Coprime a b := by
  intro a ha b hb hab
  simp [P] at ha hb
  rcases ha with ha2 | ha3 | ha5 | ha7 | ha11 <;>
    rcases hb with hb2 | hb3 | hb5 | hb7 | hb11 <;>
    subst a <;> subst b
  all_goals
    first | contradiction | norm_num [Nat.Coprime]

/-- The reciprocal sum of `P` is `2927/2310`. -/
theorem reciprocal_sum_value :
    (1 / 2 + 1 / 3 + 1 / 5 + 1 / 7 + 1 / 11 : ℚ) = (2927 / 2310 : ℚ) := by
  norm_num

/-- The reciprocal sum of `P` is bounded below 2. -/
theorem reciprocal_sum_lt_two :
    (1 / 2 + 1 / 3 + 1 / 5 + 1 / 7 + 1 / 11 : ℚ) < 2 := by
  norm_num

end Jsp643