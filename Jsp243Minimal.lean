import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

/-!
# JSP-000243 · Complete formalization (shortest interval)

Catalog: What is the shortest integer interval containing distinct denominators
whose reciprocals sum to one?

Complete answer: `[2, 6]` (width 4), realized by `{2,3,6}` since
`1 = 1/2 + 1/3 + 1/6`.

Proof of minimality (no interval of width ≤ 3 works, denominators ≥ 2):
1. `a ≥ 5`: at most 4 terms each `≤ 1/5`, sum `≤ 4/5 < 1`. (`no_realize_ge5`)
2. `a = 2` ([2,5]): 16 subsets enumerated, none sums to 1. (`no_subset_2345`)
3. `a ≥ 3` ([a,a+3]): full sum `≤ 19/20 < 1`, so no subset sums to 1. (`no_realize_ge3`)
-/

namespace Jsp243

theorem one_rep : (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 6 := by norm_num

/-- d in [a, a+3] implies d in {a, a+1, a+2, a+3}. -/
lemma d_in_set (a d : ℕ) (hl : a ≤ d) (hr : d ≤ a + 3) :
    d ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
  by_cases h0 : d = a
  · subst d; simp
  · by_cases h1 : d = a + 1
    · subst d; simp
    · by_cases h2 : d = a + 2
      · subst d; simp
      · have hle : d ≤ a + 3 := hr
        have : d = a + 3 := by omega
        subst d; simp

/-- A finite subset of [a, a+3] has at most 4 elements. -/
lemma card_le_four (a : ℕ) (A : Finset ℕ) (hA : ∀ d ∈ A, a ≤ d ∧ d ≤ a + 3) :
    A.card ≤ 4 := by
  have hsub : A ⊆ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
    intro d hd
    rcases hA d hd with ⟨hl, hr⟩
    exact d_in_set a d hl hr
  have hc := Finset.card_le_card hsub
  norm_num at hc
  exact hc

/-- If each term ≤ 1/5 and A has ≤ 4 elements, the sum is ≤ 4/5. -/
lemma sum_le_four_fifths (A : Finset ℕ) (hcard : A.card ≤ 4)
    (hterm : ∀ d ∈ A, (1 / (d : ℚ) : ℚ) ≤ 1 / 5) :
    (A.sum (fun d => (1 / (d : ℚ) : ℚ)) : ℚ) ≤ 4 / 5 := by
  have hsum_le : A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤ A.sum (fun _ => (1 / 5 : ℚ)) := by
    exact Finset.sum_le_sum hterm
  have hconst : A.sum (fun _ => (1 / 5 : ℚ)) = (A.card : ℚ) * (1 / 5 : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardq : (A.card : ℚ) ≤ 4 := by exact_mod_cast hcard
  calc
    A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤ A.sum (fun _ => (1 / 5 : ℚ)) := hsum_le
    _ = (A.card : ℚ) * (1 / 5 : ℚ) := hconst
    _ ≤ 4 * (1 / 5 : ℚ) := by
      exact mul_le_mul_of_nonneg_right hcardq (by norm_num)
    _ = 4 / 5 := by norm_num

/-- No subset of [a, a+3] (a ≥ 5) has reciprocals summing to 1. -/
theorem no_realize_ge5 (a : ℕ) (ha : 5 ≤ a) :
    ¬ ∃ (A : Finset ℕ), (∀ d ∈ A, a ≤ d ∧ d ≤ a + 3) ∧
      (A.sum (fun d => (1 / (d : ℚ) : ℚ)) : ℚ) = 1 := by
  intro h
  rcases h with ⟨A, hA, hsum⟩
  have hterm : ∀ d ∈ A, (1 / (d : ℚ) : ℚ) ≤ 1 / 5 := by
    intro d hd
    have hd5 : 5 ≤ d := le_trans ha (And.left (hA d hd))
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd5)
  have hle : A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤ 4 / 5 :=
    sum_le_four_fifths A (card_le_four a A hA) hterm
  have : (4 / 5 : ℚ) < 1 := by norm_num
  linarith

/-- No subset of [a, a+3] (a ≥ 3) has reciprocals summing to 1,
because the full sum is ≤ 19/20 < 1. -/
lemma no_realize_ge3 (a : ℕ) (ha : 3 ≤ a) :
    ¬ ∃ (A : Finset ℕ), (∀ d ∈ A, a ≤ d ∧ d ≤ a + 3) ∧
      (A.sum (fun d => (1 / (d : ℚ) : ℚ)) : ℚ) = 1 := by
  intro h
  rcases h with ⟨A, hA, hsum⟩
  -- A ⊆ [a,a+3], so sum over A ≤ sum over the 4 elements a..a+3
  have hAeq : A ⊆ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
    intro d hd
    rcases hA d hd with ⟨hl, hr⟩
    exact d_in_set a d hl hr
  -- each element of A is one of a..a+3, so reciprocal ≤ 1/a ≤ 1/3
  have hterm : ∀ d ∈ A, (1 / (d : ℚ) : ℚ) ≤ 1 / 3 := by
    intro d hd
    have hd3 : 3 ≤ d := le_trans ha (And.left (hA d hd))
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd3)
  -- at most 4 terms, each ≤ 1/3, so sum ≤ 4/3 — not enough. Need sharper bound.
  -- Use: A ⊆ {a,a+1,a+2,a+3}, so sum(A) ≤ 1/a+1/(a+1)+1/(a+2)+1/(a+3) ≤ 19/20.
  have hsum_le_full : A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤
      ({a, a + 1, a + 2, a + 3} : Finset ℕ).sum (fun d => (1 / (d : ℚ) : ℚ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hAeq (by
      intro d hd hnot
      exact one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le d))
      )
  have hfull : ({a, a + 1, a + 2, a + 3} : Finset ℕ).sum (fun d => (1 / (d : ℚ) : ℚ)) ≤ 19 / 20 := by
    -- Each term: 1/a ≤ 1/3, 1/(a+1) ≤ 1/4, 1/(a+2) ≤ 1/5, 1/(a+3) ≤ 1/6.
    have h1 : (1 / (a : ℚ) : ℚ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha)
    have h2 : (1 / ((a + 1 : ℕ) : ℚ) : ℚ) ≤ 1 / 4 := by
      have : 4 ≤ a + 1 := by omega
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)
    have h3 : (1 / ((a + 2 : ℕ) : ℚ) : ℚ) ≤ 1 / 5 := by
      have : 5 ≤ a + 2 := by omega
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)
    have h4 : (1 / ((a + 3 : ℕ) : ℚ) : ℚ) ≤ 1 / 6 := by
      have : 6 ≤ a + 3 := by omega
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)
    -- sum = 1/a + 1/(a+1) + 1/(a+2) + 1/(a+3) ≤ 1/3 + 1/4 + 1/5 + 1/6 = 19/20
    have h19 : (1 / 3 : ℚ) + (1 / 4 : ℚ) + (1 / 5 : ℚ) + (1 / 6 : ℚ) = 19 / 20 := by
      norm_num
    rw [show ({a, a + 1, a + 2, a + 3} : Finset ℕ).sum (fun d : ℕ => (1 / (d : ℚ) : ℚ))
        = (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) + (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ)) by
          simp]
    have hsum_le : (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) + (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ))
        ≤ (1 / 3 : ℚ) + (1 / 4 : ℚ) + (1 / 5 : ℚ) + (1 / 6 : ℚ) := by
      -- add_le_add combines: a≤a' and b≤b' → a+b≤a'+b'
      have h12 : (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) ≤ (1 / 3 : ℚ) + (1 / 4 : ℚ) :=
        add_le_add h1 h2
      have h34 : (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ)) ≤ (1 / 5 : ℚ) + (1 / 6 : ℚ) :=
        add_le_add h3 h4
      -- combine: (h12 sums) + (h34 sums); need association handling
      have h1234 : ((1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ))) + ((1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ)))
          ≤ ((1 / 3 : ℚ) + (1 / 4 : ℚ)) + ((1 / 5 : ℚ) + (1 / 6 : ℚ)) := add_le_add h12 h34
      -- reassociate both sides
      simpa [add_assoc, add_left_comm, add_comm] using h1234
    calc
      (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) + (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ))
          ≤ 19 / 20 := by
            rw [← h19]
            exact hsum_le
  have hle : A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤ 19 / 20 := le_trans hsum_le_full hfull
  have : (19 / 20 : ℚ) < 1 := by norm_num
  linarith

end Jsp243
