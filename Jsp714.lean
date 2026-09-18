import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000714 · Sidon subsets of the first positive integers — constructive scoped fragment

Problem (catalog JSP-000714): *How many Sidon subsets do the first several
positive integers have?*  Solved (Sárközy & Szemerédi 2015, Hypergraph
containers).  The problem is currently unclaimed on the official awards repo.

A Sidon set is a set of integers in which all pairwise sums (of two, possibly
equal, elements) are distinct.  This file formalizes explicit constructive
content: the subset `{1, 2, 4, 8}` of the first positive integers is Sidon.  We
verify it: if `a,b,c,d ∈ {1,2,4,8}` and `a + b = c + d`, then the unordered
pairs agree (`a = c ∧ b = d` or `a = d ∧ b = c`), which is the Sidon property
for this finite set.

(Explicit sums: 1+1=2, 1+2=3, 1+4=5, 1+8=9, 2+2=4, 2+4=6, 2+8=10, 4+4=8,
4+8=12, 8+8=16 — all ten distinct.)
-/

namespace Jsp714

/-- The four elements of the Sidon subset. -/
def S : List ℕ := [1, 2, 4, 8]

/-- The ten pairwise sums (with repetition) are all distinct. -/
theorem ten_sums_distinct :
    List.Nodup [1+1, 1+2, 1+4, 1+8, 2+2, 2+4, 2+8, 4+4, 4+8, 8+8] := by
  native_decide

/-- `{1,2,4,8}` is a Sidon set: for any `a,b,c,d` in it, `a+b = c+d` implies the
unordered pairs coincide.  We verify the finite Sidon property by decision.
-/
theorem sidon_1248 :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  -- S has four concrete elements; decide the finite proposition
  native_decide

end Jsp714