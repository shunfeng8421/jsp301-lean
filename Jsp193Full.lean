import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace JSP193Full

open scoped BigOperators

lemma exists_prime_above (m : ℕ) : ∃ p, m < p ∧ Nat.Prime p := by
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (m + 1)
  exact ⟨p, by linarith, hp⟩

noncomputable def primeSeq : ℕ → ℕ
  | 0 => 2
  | n+1 => (exists_prime_above (primeSeq n)).choose

lemma primeSeq_prime : ∀ n, Nat.Prime (primeSeq n) := by
  intro n
  induction n with
  | zero => change Nat.Prime 2; decide
  | succ n ih => rw [primeSeq]; exact (exists_prime_above (primeSeq n)).choose_spec.2

lemma primeSeq_strict : ∀ n, primeSeq n < primeSeq (n+1) := by
  intro n; rw [primeSeq]; exact (exists_prime_above (primeSeq n)).choose_spec.1

lemma primeSeq_lt_of_lt {a b : ℕ} (h : a < b) : primeSeq a < primeSeq b := by
  induction h with
  | refl => exact primeSeq_strict a
  | step _ ih => exact lt_trans ih (primeSeq_strict _)

lemma primeSeq_injective : Function.Injective primeSeq := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact False.elim ((ne_of_lt (primeSeq_lt_of_lt hlt)) hab)
  · exact False.elim ((ne_of_lt (primeSeq_lt_of_lt hgt)) hab.symm)

lemma primeSeq_ge_add_two (n : ℕ) : n + 2 ≤ primeSeq n := by
  induction n with
  | zero => norm_num [primeSeq]
  | succ n ih =>
      have h1 : n + 2 ≤ primeSeq n := ih
      have h2 : primeSeq n < primeSeq (n+1) := primeSeq_strict n
      omega

-- ================ coprime squares ================
lemma distinct_prime_coprime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hneq : p ≠ q) :
    Nat.Coprime p q := by
  apply Nat.coprime_comm.mp
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hdvd
  have : q ∣ p ↔ q = p := Nat.prime_dvd_prime_iff_eq hq hp
  exact hneq (this.mp hdvd).symm

lemma distinct_prime_sq_coprime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hneq : p ≠ q) :
    Nat.Coprime (p ^ 2) (q ^ 2) := (distinct_prime_coprime hp hq hneq).pow 2 2

lemma not_squarefree_of_sq_dvd {m p : ℕ} (hp : p.Prime) (hdiv : p ^ 2 ∣ m) :
    ¬ Squarefree m := by
  intro hsq
  have h := (Nat.squarefree_iff_prime_squarefree).mp hsq p hp
  have hp2 : p * p = p ^ 2 := by ring
  have hpp : p * p ∣ m := by rwa [← hp2] at hdiv
  exact h hpp

-- ================ CRT assembly ================
lemma i_add_one_lt_sq (i : ℕ) : i + 1 < (primeSeq i) ^ 2 := by
  have hge : i + 2 ≤ primeSeq i := primeSeq_ge_add_two i
  nlinarith [sq_nonneg (primeSeq i), sq_nonneg (i + 2), hge]

lemma pairwise_coprime_range (n : ℕ) :
    (List.range n).Pairwise (fun i j => Nat.Coprime ((primeSeq i) ^ 2) ((primeSeq j) ^ 2)) := by
  rw [List.pairwise_iff_getElem]
  intro i j hij hi hj
  have hgi : (List.range n)[i] = i := by simpa using Nat.getElem_range i n hi
  have hgj : (List.range n)[j] = j := by simpa using Nat.getElem_range j n hj
  have hne : i ≠ j := by omega
  have hiq : Nat.Prime (primeSeq ((List.range n)[i])) := by
    rw [hgi]; exact primeSeq_prime i
  have hjq : Nat.Prime (primeSeq ((List.range n)[j])) := by
    rw [hgj]; exact primeSeq_prime j
  have hneq : (List.range n)[i] ≠ (List.range n)[j] := by
    rw [hgi, hgj]; exact hne
  exact distinct_prime_sq_coprime hiq hjq (fun h => hneq (primeSeq_injective h))

theorem jsp000193_squarefree_gaps_unbounded :
    ∀ n : ℕ, 1 ≤ n → ∃ N : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ n → ¬ Squarefree (N + i) := by
  intro n hn
  let s : ℕ → ℕ := fun i => (primeSeq i) ^ 2
  let a : ℕ → ℕ := fun i => (primeSeq i) ^ 2 - (i + 1)
  have co : (List.range n).Pairwise (fun i j => Nat.Coprime ((primeSeq i) ^ 2) ((primeSeq j) ^ 2)) :=
    pairwise_coprime_range n
  rcases Nat.chineseRemainderOfList a s (List.range n) co with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro i hi1 hin
  let j : ℕ := i - 1
  have hjelt : j ∈ List.range n := by
    simp [j]
    omega
  have hle : j + 1 ≤ (primeSeq j) ^ 2 := by
    have := i_add_one_lt_sq j
    omega
  have hkj := hk j hjelt
  -- hkj : k ≡ a j [MOD (primeSeq j)^2]
  have hkj_add : k + (j + 1) ≡ a j + (j + 1) [MOD (primeSeq j)^2] := hkj.add_right (j + 1)
  have haj : a j + (j + 1) = (primeSeq j)^2 := by
    unfold a
    exact Nat.sub_add_cancel hle
  have hk0 : k + (j + 1) ≡ 0 [MOD (primeSeq j)^2] := by
    have h1 : k + (j + 1) ≡ (primeSeq j)^2 [MOD (primeSeq j)^2] := by
      rwa [haj] at hkj_add
    exact h1.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  have hdvd : (primeSeq j)^2 ∣ k + (j + 1) := Nat.modEq_zero_iff_dvd.mp hk0
  have hns : ¬ Squarefree (k + (j + 1)) := not_squarefree_of_sq_dvd (primeSeq_prime j) hdvd
  have hji : j + 1 = i := by dsimp [j]; omega
  simpa [hji] using hns

end JSP193Full