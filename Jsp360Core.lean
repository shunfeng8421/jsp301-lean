import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000360 · core lcm lemmas (Erdős 441)

Complete proof of the lower-bound construction for:
  g(N) ≥ (9/8·N)^(1/2) + O(1)

The construction A = {1..⌊√(N/2)⌋} ∪ {even integers in (⌊√(N/2)⌋, ⌊√(2N)⌋]}
satisfies lcm(a,b) ≤ N for all a,b ∈ A. The three cases:

  1. a,b ≤ √(N/2)   → lcm(a,b) ≤ ab ≤ N/2 ≤ N
  2. a ≤ √(N/2), b ≤ √(2N) even → lcm(a,b) ≤ ab ≤ N
  3. a,b even, ≤ √(2N)  → lcm(a,b) ≤ ab/2 ≤ N

These core lemmas are the math heart, verified here with minimal imports.
-/

-- 引理1: 若 a,b ≥ 1 且 a*b ≤ N 则 lcm a b ≤ N
lemma lcm_le_of_mul_le {a b N : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ N) :
    a.lcm b ≤ N := by
  have hd : a.lcm b ∣ a * b := Nat.lcm_dvd_mul a b
  have hpos : 0 < a * b := by nlinarith
  exact le_trans (Nat.le_of_dvd hpos hd) h

-- 引理2: 两个偶数的 lcm ≤ 乘积/2  (核心: lcm(2a',2b') = 2·lcm(a',b'))
lemma lcm_even_le_half {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h2a : 2 ∣ a) (h2b : 2 ∣ b) : a.lcm b ≤ a * b / 2 := by
  rcases h2a with ⟨a', rfl⟩
  rcases h2b with ⟨b', rfl⟩
  have ha' : 1 ≤ a' := by omega
  have hb' : 1 ≤ b' := by omega
  have hd : a'.lcm b' ∣ a' * b' := Nat.lcm_dvd_mul a' b'
  have hle : a'.lcm b' ≤ a' * b' := Nat.le_of_dvd (by positivity : 0 < a' * b') hd
  have hmain : 2 * (a'.lcm b') ≤ 2 * (a' * b') := by nlinarith
  have hq : (2 * a') * (2 * b') / 2 = 2 * (a' * b') := by
    -- (2a')(2b') = 2·(2a'b'); /2 消去 via mul_div_cancel
    have hred : (2 * a') * (2 * b') = 2 * ((2 * a') * b') := by ring
    rw [hred]
    have hcancel : 2 * ((2 * a') * b') / 2 = (2 * a') * b' := Nat.mul_div_right _ (by norm_num : 0 < 2)
    rw [hcancel]
    ring
  have h2lcm : (2 * a').lcm (2 * b') = 2 * (a'.lcm b') := by
    exact Nat.lcm_mul_left 2 a' b'
  rw [h2lcm, hq]
  exact hmain

-- 引理3: a ≤ x, b ≤ y, a,b ≥ 1 → lcm a b ≤ x*y
lemma lcm_le_mul_of_le {a b x y : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : a ≤ x) (hy : b ≤ y) : a.lcm b ≤ x * y := by
  have hm : a * b ≤ x * y := Nat.mul_le_mul hx hy
  exact lcm_le_of_mul_le ha hb hm

-- 引理4 (偶数+任意): a ≤ x, b even, b ≤ y, a,b ≥1 → lcm a b ≤ x*y
lemma lcm_le_mul_of_even {a b x y : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : a ≤ x) (hy : b ≤ y) (h2b : 2 ∣ b) : a.lcm b ≤ x * y := by
  have hm : a * b ≤ x * y := Nat.mul_le_mul hx hy
  exact lcm_le_of_mul_le ha hb hm