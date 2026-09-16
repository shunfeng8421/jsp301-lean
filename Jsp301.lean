import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-301 · Consecutive powerful numbers need not be squares

**Problem (catalog JSP-000301):** *If two consecutive positive integers are
powerful, must at least one be a perfect square?*

**Resolution (disproof):** No. The consecutive integers
`12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2` are both powerful, yet neither is a
perfect square. Each lies strictly between the consecutive squares
`110^2 = 12100` and `111^2 = 12321`.
-/

namespace Jsp301

/-- A natural number is **powerful**: every prime divisor appears to exponent ≥ 2. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A natural number is a perfect square. -/
def IsSquare (n : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 2 = n

/-! ## `12167` is powerful: its only prime divisor is `23`, with exponent 3 -/

theorem powerful_12167 : IsPowerful 12167 := by
  intro p hp hpd
  -- p | 12167 = 23^3, so p | 23, hence (23 prime) p = 23
  have h23 : 12167 = 23 ^ 3 := by norm_num
  have hp_dvd_23 : p ∣ 23 := by
    rw [h23] at hpd
    exact hp.dvd_of_dvd_pow hpd
  have hp_eq_23 : p = 23 :=
    (Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 23 by decide)).mp hp_dvd_23
  -- then p^2 = 23^2 divides 12167
  rw [hp_eq_23]
  use 23
  norm_num

/-! ## `12168` is powerful: prime divisors `2, 3, 13`, each with square dividing -/

lemma prime_dvd_of_dvd_mul3 {p a b c : ℕ} (hp : p.Prime) (h : p ∣ a * b * c) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  -- a*b*c = (a*b)*c; p prime divides product ⇒ divides a factor
  rcases hp.dvd_mul.mp h with h1 | hc
  · -- h1 : p ∣ a*b
    rcases hp.dvd_mul.mp h1 with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hc)

theorem powerful_12168 : IsPowerful 12168 := by
  intro p hp hpd
  have h : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num
  rw [h] at hpd
  have hp_dvd_2 : p ∣ 2 ^ 3 ∨ p ∣ 3 ^ 2 ∨ p ∣ 13 ^ 2 := by
    exact prime_dvd_of_dvd_mul3 hp hpd
  rcases hp_dvd_2 with h2 | h3 | h13
  · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 2 by decide)).mp hp2
    rw [hp_eq]
    use 3042          -- 2^2 | 12168
    norm_num
  · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 3 by decide)).mp hp3
    rw [hp_eq]
    use 1352          -- 3^2 | 12168
    norm_num
  · have hp13 : p ∣ 13 := hp.dvd_of_dvd_pow h13
    have hp_eq : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 13 by decide)).mp hp13
    rw [hp_eq]
    use 72            -- 13^2 | 12168
    norm_num

/-! ## Neither number is a perfect square (both lie in the gap (110², 111²)) -/

lemma not_square_between {n a b : ℕ} (hlt : a ^ 2 < n) (hgt : n < b ^ 2)
    (hstep : b = a + 1) : ¬ IsSquare n := by
  intro h
  rcases h with ⟨m, hm⟩
  have ham : a < m := by
    by_contra hnot
    have hma : m ≤ a := le_of_not_gt hnot
    have hm2 : m ^ 2 ≤ a ^ 2 := by exact Nat.pow_le_pow_left hma 2
    nlinarith
  have hmb : m < b := by
    by_contra hnot
    have hbm : b ≤ m := le_of_not_gt hnot
    have hb2 : b ^ 2 ≤ m ^ 2 := by exact Nat.pow_le_pow_left hbm 2
    nlinarith
  rw [hstep] at hmb
  nlinarith [ham]

theorem not_square_12167 : ¬ IsSquare 12167 := by
  apply not_square_between (a := 110) (b := 111)
  · norm_num
  · norm_num
  · norm_num

theorem not_square_12168 : ¬ IsSquare 12168 := by
  apply not_square_between (a := 110) (b := 111)
  · norm_num
  · norm_num
  · norm_num

/-
## The main result
-/
set_option linter.style.whitespace false

/-- JSP-301: two consecutive powerful numbers, neither a square. -/
theorem JSP_301 :
    ∃ n m : ℕ, m = n + 1 ∧ IsPowerful n ∧ IsPowerful m ∧ ¬ IsSquare n ∧ ¬ IsSquare m := by
  refine ⟨12167, 12168, by norm_num, powerful_12167, powerful_12168,
    not_square_12167, not_square_12168⟩

end Jsp301