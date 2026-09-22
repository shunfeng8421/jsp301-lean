import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Jsp243

theorem d_in_set (a d : ℕ) (hl : a ≤ d) (hr : d ≤ a + 3) :
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

lemma card_le_four (a : ℕ) (A : Finset ℕ) (hA : ∀ d ∈ A, a ≤ d ∧ d ≤ a + 3) :
    A.card ≤ 4 := by
  have hsub : A ⊆ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
    intro d hd
    rcases hA d hd with ⟨hl, hr⟩
    exact d_in_set a d hl hr
  have hc := Finset.card_le_card hsub
  norm_num at hc
  exact hc

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

lemma full_le_ge3 (a : ℕ) (ha : 3 ≤ a) :
    ({a, a + 1, a + 2, a + 3} : Finset ℕ).sum (fun d : ℕ => (1 / (d : ℚ) : ℚ)) ≤ 19 / 20 := by
  have h1 : (1 / (a : ℚ) : ℚ) ≤ (1 / 3 : ℚ) :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha)
  have h2 : (1 / ((a + 1 : ℕ) : ℚ) : ℚ) ≤ (1 / 4 : ℚ) := by
    have : (4 : ℕ) ≤ a + 1 := by omega
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)
  have h3 : (1 / ((a + 2 : ℕ) : ℚ) : ℚ) ≤ (1 / 5 : ℚ) := by
    have : (5 : ℕ) ≤ a + 2 := by omega
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)
  have h4 : (1 / ((a + 3 : ℕ) : ℚ) : ℚ) ≤ (1 / 6 : ℚ) := by
    have : (6 : ℕ) ≤ a + 3 := by omega
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast this)
  have hsum_le : (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) + (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ))
      ≤ (1 / 3 : ℚ) + (1 / 4 : ℚ) + (1 / 5 : ℚ) + (1 / 6 : ℚ) := by
    have h12 : (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) ≤ (1 / 3 : ℚ) + (1 / 4 : ℚ) :=
      add_le_add h1 h2
    have h34 : (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ)) ≤ (1 / 5 : ℚ) + (1 / 6 : ℚ) :=
      add_le_add h3 h4
    have h1234 : ((1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ))) + ((1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ)))
        ≤ ((1 / 3 : ℚ) + (1 / 4 : ℚ)) + ((1 / 5 : ℚ) + (1 / 6 : ℚ)) := add_le_add h12 h34
    simpa [add_assoc, add_left_comm, add_comm] using h1234
  have h19 : (1 / 3 : ℚ) + (1 / 4 : ℚ) + (1 / 5 : ℚ) + (1 / 6 : ℚ) = 19 / 20 := by norm_num
  calc
    ({a, a + 1, a + 2, a + 3} : Finset ℕ).sum (fun d : ℕ => (1 / (d : ℚ) : ℚ))
        = (1 / (a : ℚ) : ℚ) + (1 / ((a + 1 : ℕ) : ℚ)) + (1 / ((a + 2 : ℕ) : ℚ)) + (1 / ((a + 3 : ℕ) : ℚ)) := by
          simp [add_assoc, add_comm, add_left_comm]
    _ ≤ 19 / 20 := by
          exact le_trans hsum_le (le_of_eq h19)

theorem no_realize_ge3 (a : ℕ) (ha : 3 ≤ a) :
    ¬ ∃ (A : Finset ℕ), (∀ d ∈ A, a ≤ d ∧ d ≤ a + 3) ∧
      (A.sum (fun d => (1 / (d : ℚ) : ℚ)) : ℚ) = 1 := by
  intro h
  rcases h with ⟨A, hA, hsum⟩
  have hAeq : A ⊆ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
    intro d hd
    rcases hA d hd with ⟨hl, hr⟩
    exact d_in_set a d hl hr
  have hsum_le_full : A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤
      ({a, a + 1, a + 2, a + 3} : Finset ℕ).sum (fun d => (1 / (d : ℚ) : ℚ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hAeq (by
      intro d hd hnot
      exact one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le d))
      )
  have hle : A.sum (fun d => (1 / (d : ℚ) : ℚ)) ≤ 19 / 20 :=
    le_trans hsum_le_full (full_le_ge3 a ha)
  have : (19 / 20 : ℚ) < 1 := by norm_num
  linarith

-- a = 2 case: no subset of {2,3,4,5} sums to 1
lemma no_subset_2345b (S : Finset ℕ) (hS : S ⊆ ({2,3,4,5} : Finset ℕ))
    (hsum : (S.sum (fun d => (1 / (d : ℚ) : ℚ)) : ℚ) = 1) : False := by
  -- S has ≤ 4 elements, each in {2,3,4,5}; enumerate membership
  by_cases h2 : 2 ∈ S
  · by_cases h3 : 3 ∈ S
    · by_cases h4 : 4 ∈ S
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({2,3,4,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx; exact hS hx
            · intro hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({2,3,4} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({2,3,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({2,3} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
    · by_cases h4 : 4 ∈ S
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({2,4,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({2,4} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({2,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({2} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; subst x; exact h2
          rw [hSx] at hsum
          norm_num at hsum
  · by_cases h3 : 3 ∈ S
    · by_cases h4 : 4 ∈ S
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({3,4,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({3,4} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({3,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({3} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; subst x; exact h3
          rw [hSx] at hsum
          norm_num at hsum
    · by_cases h4 : 4 ∈ S
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({4,5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = ({4} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; subst x; exact h4
          rw [hSx] at hsum
          norm_num at hsum
      · by_cases h5 : 5 ∈ S
        · have hSx : S = ({5} : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf ⊢
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx; subst x; exact h5
          rw [hSx] at hsum
          norm_num at hsum
        · have hSx : S = (∅ : Finset ℕ) := by
            ext x
            constructor
            · intro hx
              have hxf : x ∈ ({2,3,4,5} : Finset ℕ) := hS hx
              simp at hxf
              rcases hxf with rfl | rfl | rfl | rfl <;> simp_all
            · intro hx; simp at hx
          rw [hSx] at hsum
          norm_num at hsum

/-- **Main theorem**: [2,6] is the shortest interval with distinct-denominator reciprocal sum 1.
Minimality: no interval [a, a+3] (width ≤ 3) with a ≥ 2 admits such a subset. -/
theorem shortest_interval :
    (1 : ℚ) = 1 / 2 + 1 / 3 + 1 / 6 ∧
    ∀ a : ℕ, 2 ≤ a →
      ¬ ∃ (A : Finset ℕ), (∀ d ∈ A, a ≤ d ∧ d ≤ a + 3) ∧
        (A.sum (fun d => (1 / (d : ℚ) : ℚ)) : ℚ) = 1 := by
  constructor
  · norm_num
  · intro a ha
    -- case a = 2 or a ≥ 3
    by_cases h2 : a = 2
    · -- a = 2: [2,5] via no_subset_2345b
      subst a
      intro h
      rcases h with ⟨A, hA, hsum⟩
      have hS : A ⊆ ({2,3,4,5} : Finset ℕ) := by
        intro d hd
        rcases hA d hd with ⟨hl, hr⟩
        exact d_in_set 2 d hl hr
      exact no_subset_2345b A hS hsum
    · -- a ≥ 3
      have ha3 : 3 ≤ a := by omega
      exact no_realize_ge3 a ha3

end Jsp243