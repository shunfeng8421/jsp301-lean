import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# JSP-307 · Consecutive integers with strictly decreasing largest prime factors

**Problem (catalog JSP-000307):** *Can three consecutive integers have strictly
decreasing largest prime factors?*

**Resolution (existence):** Yes. The consecutive integers `13, 14, 15` have
largest prime factors `13 > 7 > 5`:

* `13 = 13` (prime) — largest prime factor `13`
* `14 = 2 · 7` — largest prime factor `7`
* `15 = 3 · 5` — largest prime factor `5`

So `P(13) = 13 > P(14) = 7 > P(15) = 5`.

(Erdős–Pomerance [ErPo78] conjectured, Balog [Ba01] proved infinitely many such
triples; this explicit witness settles the existence form in Lean.)
-/

namespace Jsp307

/-- `p` is the largest prime factor of `n`: `p` is a prime divisor of `n`, and
every prime divisor of `n` is `≤ p`. -/
def IsLPF (n p : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ≤ p

/-- Any prime divisor of a positive integer is at most the integer. -/
lemma prime_dvd_le {n q : ℕ} (hn : 0 < n) (hq : q.Prime) (h : q ∣ n) : q ≤ n :=
  Nat.le_of_dvd hn h

/-! ## 13 is prime, 7 and 5 are prime -/
private theorem prime_13 : (13 : ℕ).Prime := by decide
private theorem prime_7 : (7 : ℕ).Prime := by decide
private theorem prime_5 : (5 : ℕ).Prime := by decide
private theorem prime_2 : (2 : ℕ).Prime := by decide
private theorem prime_3 : (3 : ℕ).Prime := by decide

/-! ## Witnesses -/

theorem lpf_13 : IsLPF 13 13 := by
  refine ⟨prime_13, ?_, ?_⟩
  · norm_num
  · intro q hq hq13
    have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hq13
    rw [this]

theorem lpf_14 : IsLPF 14 7 := by
  refine ⟨prime_7, ?_, ?_⟩
  · norm_num
  · intro q hq hq14
    have h14 : 14 = 2 * 7 := by norm_num
    rw [h14] at hq14
    have hq2or7 : q = 2 ∨ q = 7 := by
      rcases (Nat.Prime.dvd_mul hq).mp hq14 with h2 | h7
      · left
        exact (Nat.prime_dvd_prime_iff_eq hq prime_2).mp h2
      · right
        exact (Nat.prime_dvd_prime_iff_eq hq prime_7).mp h7
    rcases hq2or7 with rfl | rfl <;> norm_num

theorem lpf_15 : IsLPF 15 5 := by
  refine ⟨prime_5, ?_, ?_⟩
  · norm_num
  · intro q hq hq15
    have h15 : 15 = 3 * 5 := by norm_num
    rw [h15] at hq15
    have hq3or5 : q = 3 ∨ q = 5 := by
      rcases (Nat.Prime.dvd_mul hq).mp hq15 with h3 | h5
      · left
        exact (Nat.prime_dvd_prime_iff_eq hq prime_3).mp h3
      · right
        exact (Nat.prime_dvd_prime_iff_eq hq prime_5).mp h5
    rcases hq3or5 with rfl | rfl <;> norm_num

/-! ### Main result -/

/-- Three consecutive integers (13,14,15) have strictly decreasing largest prime
factors: P(13)=13 > P(14)=7 > P(15)=5. -/
theorem JSP_307 :
    ∃ n : ℕ, IsLPF n 13 ∧ IsLPF (n + 1) 7 ∧ IsLPF (n + 2) 5 := by
  refine ⟨13, lpf_13, ?_, ?_⟩
  · simpa using lpf_14
  · simpa using lpf_15

end Jsp307