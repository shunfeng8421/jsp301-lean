import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000428 · Large pairwise noncoprime subsets of an integer interval — constructive scoped fragment

Problem (catalog JSP-000428): *How large can a pairwise noncoprime subset of
an integer interval containing a specified integer be?*  Solved (Erdős 1973).
The problem is currently unclaimed on the official awards repo.

This file formalizes explicit constructive content: for the interval `[1,20]`
the subset of even numbers `{2,4,6,8,10,12,14,16,18,20}` is pairwise
non-coprime — any two distinct even numbers share the divisor 2, so their gcd
is at least 2 (not 1).  This is a pairwise-noncoprime subset of size 10.
-/

namespace Jsp428

/-- The even numbers `2,4,...,20`, the even subset of `[1,20]`. -/
def evens20 : List ℕ := [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]

/-- 2 divides every element of `evens20`. -/
theorem two_divides_all : ∀ x ∈ evens20, 2 ∣ x := by
  intro x hx
  simp [evens20] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Any two elements of `evens20` have gcd divisible by 2. -/
theorem pair_gcd_div_two (a b : ℕ) (ha : a ∈ evens20) (hb : b ∈ evens20) :
    2 ∣ Nat.gcd a b := by
  have h2a : 2 ∣ a := two_divides_all a ha
  have h2b : 2 ∣ b := two_divides_all b hb
  exact Nat.dvd_gcd h2a h2b

/-- The ten even numbers `2,4,...,20` are pairwise non-coprime: if two shared a
common divisor 2, they cannot be coprime (coprime would force 2 ∣ 1). -/
theorem evens20_pairwise_noncoprime :
    ∀ a ∈ evens20, ∀ b ∈ evens20, a ≠ b → ¬ Nat.Coprime a b := by
  intro a ha b hb hab hcop
  have h2g : 2 ∣ Nat.gcd a b := pair_gcd_div_two a b ha hb
  -- Coprime means gcd = 1, so 2 | 1, absurd
  rw [Nat.coprime_iff_gcd_eq_one] at hcop
  rw [hcop] at h2g
  norm_num at h2g

end Jsp428