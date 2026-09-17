import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-000385 · Permuting naturals so adjacent sums are prime — constructive scoped fragment

Problem (catalog JSP-000385): *Can all natural numbers be permuted so that every
adjacent pair has prime sum?* (Erdős–Graham [ErGr80], book text — no standalone
paper identified).  The problem is currently unclaimed on the official awards repo.

This file formalizes the explicit constructive core of the known block argument:
the block `[1,2,3,4,7,6,13,10,9,8,11,12,5,14]` realizes the local pattern whose
every adjacent pair has prime sum.  We verify all thirteen adjacent sums are
prime (each by `decide`).
-/

namespace Jsp385

/-- The 14-term block `[1,2,3,4,7,6,13,10,9,8,11,12,5,14]`. -/
def block : List ℕ := [1, 2, 3, 4, 7, 6, 13, 10, 9, 8, 11, 12, 5, 14]

-- The prime values appearing as adjacent sums:
private theorem prime_3 : (3 : ℕ).Prime := by decide
private theorem prime_5 : (5 : ℕ).Prime := by decide
private theorem prime_7 : (7 : ℕ).Prime := by decide
private theorem prime_11 : (11 : ℕ).Prime := by decide
private theorem prime_13 : (13 : ℕ).Prime := by decide
private theorem prime_17 : (17 : ℕ).Prime := by decide
private theorem prime_19 : (19 : ℕ).Prime := by decide
private theorem prime_23 : (23 : ℕ).Prime := by decide

/-- The first adjacent pair sums to a prime: `1 + 2 = 3`. -/
theorem pair_1_2_prime : Nat.Prime (1 + 2) := by
  norm_num [prime_3]

/-- All thirteen adjacent sums of the block are prime.  Adjacent pairs
`(1,2),(2,3),(3,4),(4,7),(7,6),(6,13),(13,10),(10,9),(9,8),(8,11),(11,12),
(12,5),(5,14)` sum to `3,5,7,11,13,19,23,19,17,19,23,17,19`, all prime. -/
theorem all_adjacent_pairs_prime :
    Nat.Prime (1 + 2) ∧ Nat.Prime (2 + 3) ∧ Nat.Prime (3 + 4) ∧
    Nat.Prime (4 + 7) ∧ Nat.Prime (7 + 6) ∧ Nat.Prime (6 + 13) ∧
    Nat.Prime (13 + 10) ∧ Nat.Prime (10 + 9) ∧ Nat.Prime (9 + 8) ∧
    Nat.Prime (8 + 11) ∧ Nat.Prime (11 + 12) ∧ Nat.Prime (12 + 5) ∧
    Nat.Prime (5 + 14) := by
  norm_num [prime_3, prime_5, prime_7, prime_11, prime_13, prime_17, prime_19, prime_23]

end Jsp385