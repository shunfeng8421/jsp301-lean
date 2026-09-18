import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000616 · Counting sum-free subsets — constructive scoped fragment

Problem (catalog JSP-000616): *How many sum-free subsets do the first several
positive integers have? Is their number approximately two to the power of half
the interval size?*  Solved (Cameron–Erdős conjecture, Green 2004 / Sapozhenko
2003).  Unclaimed on the official awards repo.

A subset `A ⊆ {1,...,n}` is *sum-free* if no element equals a sum of two
(not necessarily distinct) elements of `A`.  This file formalizes constructive
scoped content:

* the definition of `IsSumFree`,
* `countSumFree n` : the number of sum-free subsets of `{1,...,n}`,
  computed by enumerating the finite power set (decidable),
* exact values `countSumFree n` for small `n`, verified by `native_decide`,
  matching the known growth `c(n) ≍ c · 2^(n/2)`.

The full asymptotic theorem (Green–Sapozhenko) is not claimed here; these are
the finite constructive data points.
-/

namespace Jsp616

/-- The interval `{1,...,n}` as a Finset (the empty set when `n = 0`). -/
def interval (n : ℕ) : Finset ℕ :=
  (Finset.range n).map ⟨Nat.succ, fun _ _ h => Nat.succ.inj h⟩

/-- `A` is *sum-free*: no member of `A` is a sum of two (possibly equal)
members of `A`. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A

/-- Sum-freeness is decidable (finite membership). -/
instance (A : Finset ℕ) : Decidable (IsSumFree A) := by
  unfold IsSumFree
  infer_instance

/-- `c(n)` : the number of sum-free subsets of `{1,...,n}`.
Enumerates the finite power set of the interval. -/
def countSumFree (n : ℕ) : ℕ :=
  ((interval n).powerset.filter (fun A => IsSumFree A)).card

/-- `{1,3}` is sum-free. -/
example : IsSumFree ({1, 3} : Finset ℕ) := by
  native_decide

/-- `{1,2}` is NOT sum-free (`1+1=2`). -/
example : ¬ IsSumFree ({1, 2} : Finset ℕ) := by
  native_decide

/-- Exact counts, matching the known sequence 2,3,6,9,16,24,42,61,... -/
theorem count_1 : countSumFree 1 = 2 := by native_decide
theorem count_2 : countSumFree 2 = 3 := by native_decide
theorem count_3 : countSumFree 3 = 6 := by native_decide
theorem count_4 : countSumFree 4 = 9 := by native_decide
theorem count_5 : countSumFree 5 = 16 := by native_decide
theorem count_6 : countSumFree 6 = 24 := by native_decide
theorem count_7 : countSumFree 7 = 42 := by native_decide

end Jsp616