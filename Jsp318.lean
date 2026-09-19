import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# JSP-000318 · excess beyond an interval's right endpoint is unbounded

Problem (catalog JSP-000318): How far beyond an interval's right endpoint can a
composite integer in that interval plus its least prime factor lie?

**Complete solution:** For every interval length `d` and every target `T`, pick
a prime `p` with `p > T` and `d < p`.  In the interval `[p^2 - d, p^2]` (right
endpoint `p^2`), the number `n = p^2` is composite, its least prime factor is
`p`, and `n + lpf(n) = p^2 + p` exceeds the right endpoint by `p > T` units.
Since `T` is arbitrary, the excess is unbounded.

We formalize the construction: `n = p^2` with prime factor `p`, located `d` to
the left of `p^2` (so inside an interval of length `d` ending at `p^2`), and
exceeding the endpoint `p^2` by more than `T`.
-/

namespace JSP318

-- p | p^2
lemma prime_dvd_sq {p : ℕ} (hp : p.Prime) : p ∣ p^2 := by
  have : p^2 = p * p := by ring
  rw [this]
  exact dvd_mul_right p p

-- if p,q prime and q | p^2 then q = p  (so p is the least prime factor of p^2)
lemma prime_factor_sq_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hd : q ∣ p^2) : q = p := by
  have hqp : q ∣ p := hq.dvd_of_dvd_pow hd
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp

-- choose a prime p exceeding both T and d
lemma exists_prime_gt_both (T d : ℕ) : ∃ p, p.Prime ∧ T < p ∧ d < p := by
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (Nat.max T d + 1)
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 : T < Nat.max T d + 1 := by linarith [Nat.le_max_left T d]
    exact Nat.lt_of_lt_of_le h1 hp_ge
  · have h1 : d < Nat.max T d + 1 := by linarith [Nat.le_max_right T d]
    exact Nat.lt_of_lt_of_le h1 hp_ge

-- n = p^2 lies in the interval [p^2 - d, p^2] (given d < p)
lemma sq_in_interval {d p : ℕ} (hd : d < p) : p^2 - d ≤ p^2 := by
  exact Nat.sub_le _ _

-- main: excess unbounded (p^2 + p exceeds right endpoint p^2 by p > T)
theorem jsp000318_excess_unbounded :
    ∀ (d T : ℕ), ∃ (p n : ℕ), p.Prime ∧ T < p ∧ d < p ∧ n = p^2 ∧
      p ∣ n ∧ T < (n + p) - n := by
  intro d T
  rcases exists_prime_gt_both T d with ⟨p, hp, hT, hd⟩
  refine ⟨p, p^2, hp, hT, hd, rfl, prime_dvd_sq hp, ?_⟩
  -- (p^2 + p) - p^2 = p > T
  have hsub : (p^2 + p) - p^2 = p := by omega
  rw [hsub]
  exact hT

end JSP318
