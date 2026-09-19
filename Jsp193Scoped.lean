import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace JSP193Scoped

def N : ℕ := 65335225716547

-- Divisibility with explicit quotients, kernel-checked by norm_num.
lemma dvd_4_N1 : 4 ∣ N + 1 := by norm_num [N]
lemma dvd_9_N2 : 9 ∣ N + 2 := by norm_num [N]
lemma dvd_25_N3 : 25 ∣ N + 3 := by norm_num [N]
lemma dvd_49_N4 : 49 ∣ N + 4 := by norm_num [N]
lemma dvd_121_N5 : 121 ∣ N + 5 := by norm_num [N]
lemma dvd_169_N6 : 169 ∣ N + 6 := by norm_num [N]
lemma dvd_289_N7 : 289 ∣ N + 7 := by norm_num [N]
lemma dvd_361_N8 : 361 ∣ N + 8 := by norm_num [N]

-- If p.Prime and p^2 | m then m is not squarefree.
lemma not_squarefree_of_sq_dvd {m p : ℕ} (hp : p.Prime) (hdiv : p ^ 2 ∣ m) :
    ¬ Squarefree m := by
  intro hsq
  have h := (Nat.squarefree_iff_prime_squarefree).mp hsq p hp
  have hp2 : p * p = p ^ 2 := by ring
  have hpp : p * p ∣ m := by rwa [← hp2] at hdiv
  exact h hpp

lemma not_squarefree_N_add_1 : ¬ Squarefree (N + 1) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 2) (by simpa using dvd_4_N1)

lemma not_squarefree_N_add_2 : ¬ Squarefree (N + 2) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 3) (by simpa using dvd_9_N2)

lemma not_squarefree_N_add_3 : ¬ Squarefree (N + 3) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 5) (by simpa using dvd_25_N3)

lemma not_squarefree_N_add_4 : ¬ Squarefree (N + 4) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 7) (by simpa using dvd_49_N4)

lemma not_squarefree_N_add_5 : ¬ Squarefree (N + 5) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 11) (by simpa using dvd_121_N5)

lemma not_squarefree_N_add_6 : ¬ Squarefree (N + 6) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 13) (by simpa using dvd_169_N6)

lemma not_squarefree_N_add_7 : ¬ Squarefree (N + 7) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 17) (by simpa using dvd_289_N7)

lemma not_squarefree_N_add_8 : ¬ Squarefree (N + 8) :=
  not_squarefree_of_sq_dvd (by decide : Nat.Prime 19) (by simpa using dvd_361_N8)

theorem exists_8_consecutive_nonsquarefree :
    ∃ N : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ 8 → ¬ Squarefree (N + i) := by
  refine ⟨N, ?_⟩
  intro i hi1 hi8
  interval_cases i
  · exact not_squarefree_N_add_1
  · exact not_squarefree_N_add_2
  · exact not_squarefree_N_add_3
  · exact not_squarefree_N_add_4
  · exact not_squarefree_N_add_5
  · exact not_squarefree_N_add_6
  · exact not_squarefree_N_add_7
  · exact not_squarefree_N_add_8

end JSP193Scoped
