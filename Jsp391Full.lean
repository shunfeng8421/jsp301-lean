import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# JSP-000391 — Graham–Pollak: d_n = u_{2n+1} − 2·u_{2n−1} ∈ {0,1} (COMPLETE)

Merged P0–P3.  u₁=1, u_{n+1} = step(u_n), step u = Nat.sqrt(2u(u+1)).
d_n := u_{2n+1} − 2·u_{2n−1} is a binary digit (0 or 1).

Structure:
- P2: step(step u) − 2u ∈ {0,1}  (full proof; Nat-arithmetic heavy)
- P2a: u strictly increasing, u ≥ 1
- P3: u_{2n+1} = step(step(u_{2n-1})), so d_n = step(step(u_{2n-1}))−2·u_{2n−1} ∈ {0,1}
-/

namespace Jsp391

/-- Integer step ⌊√(2u(u+1))⌋. -/
def step (u : ℕ) : ℕ := Nat.sqrt (2 * u * (u + 1))

/-- The Graham–Pollak sequence. -/
def u : ℕ → ℕ
| 0 => 0
| n + 1 => if n = 0 then 1 else step (u n)

/-- u (n+1) = step (u n) for n ≥ 1. -/
theorem u_rec {n : ℕ} (hn : 1 ≤ n) : u (n + 1) = step (u n) := by
  cases n with
  | zero => omega
  | succ k => simp [u]

-- ── P2 supporting lemmas (Nat arithmetic) ─────────────────────────

/-- 2u(u+1) < (2u-1)^2 for u ≥ 3. -/
theorem square_bound (u : ℕ) (hu : 3 ≤ u) : 2 * u * (u + 1) < (2 * u - 1) ^ 2 := by
  have hsub : ((2 * u - 1 : ℕ) : ℤ) = 2 * (u : ℤ) - 1 := by
    have hge : (1 : ℕ) ≤ 2 * u := by omega
    rw [Nat.cast_sub hge]
    rw [Nat.cast_mul]
    norm_num
  have hpos : (0 : ℤ) < 2 * (u : ℤ) * (u : ℤ) - 6 * (u : ℤ) + 1 := by
    nlinarith [sq_nonneg (u - 3 : ℕ)]
  have hinZ : (2 * (u : ℤ) * (u + 1)) < (2 * (u : ℤ) - 1) * (2 * (u : ℤ) - 1) := by
    nlinarith
  have hL : ((2 * u * (u + 1) : ℕ) : ℤ) = 2 * (u : ℤ) * (u + 1) := by
    push_cast
    ring
  have hR : (((2 * u - 1) ^ 2 : ℕ) : ℤ) = (2 * (u : ℤ) - 1) * (2 * (u : ℤ) - 1) := by
    rw [Nat.cast_pow]
    rw [hsub]
    ring
  rw [← hL, ← hR] at hinZ
  exact_mod_cast hinZ

/-- step u ≤ 2u−2 for u ≥ 3. -/
theorem step_le_2u_sub2 (u : ℕ) (hu : 3 ≤ u) : step u ≤ 2 * u - 2 := by
  have hlt : step u < 2 * u - 1 := by
    rw [step]
    apply Nat.sqrt_lt'.2
    exact square_bound u hu
  omega

/-- Lemma A: 2u² ≤ step u·(step u+1). -/
theorem step_sq_bound (u : ℕ) (hu : 3 ≤ u) : 2 * u * u ≤ step u * (step u + 1) := by
  by_contra h
  have hs_lt : step u * (step u + 1) < 2 * u * u := by omega
  have h_gt : 2 * u * (u + 1) < (step u + 1) * (step u + 1) := by
    have hlt := Nat.lt_succ_sqrt (2 * u * (u + 1))
    simpa [step] using hlt
  have h_gt' : step u * (step u + 1) + (step u + 1) > 2 * u * u + 2 * u := by
    nlinarith
  have hs_gt : 2 * u < step u + 1 := by nlinarith
  have hs_le : step u + 1 ≤ 2 * u - 1 := by
    have h2 := step_le_2u_sub2 u hu
    omega
  omega

/-- Lemma B: step u·(step u+1) < 2(u+1)². -/
theorem step_sq_upper (u : ℕ) (hu : 3 ≤ u) : step u * (step u + 1) < 2 * (u + 1) * (u + 1) := by
  have hs_le : step u ≤ 2 * u - 1 := by
    have h2 := step_le_2u_sub2 u hu
    omega
  have hsq : step u * step u ≤ 2 * u * (u + 1) := by
    simpa [step] using Nat.sqrt_le (2 * u * (u + 1))
  have hs_est : step u * (step u + 1) ≤ 2 * u * (u + 1) + 2 * u := by
    nlinarith [hsq, hs_le]
  have htarget : 2 * u * (u + 1) + 2 * u < 2 * (u + 1) * (u + 1) := by
    nlinarith
  exact lt_of_le_of_lt hs_est htarget

/-- P2 main: step(step u) − 2u ∈ {0,1} for u ≥ 3. -/
theorem step_step_digit (u : ℕ) (hu : 3 ≤ u) :
    step (step u) - 2 * u = 0 ∨ step (step u) - 2 * u = 1 := by
  have h_lo : 2 * u ≤ step (step u) := by
    rw [step]
    have hA : 2 * u * u ≤ step u * (step u + 1) := step_sq_bound u hu
    have hs : (2 * u) * (2 * u) ≤ 2 * (step u * (step u + 1)) := by nlinarith
    have hrad : (2 * step u * (step u + 1)) = 2 * (step u * (step u + 1)) := by ring
    rw [hrad]
    exact Nat.le_sqrt.2 hs
  have h_up : step (step u) < 2 * u + 2 := by
    have hB : step u * (step u + 1) < 2 * (u + 1) * (u + 1) := step_sq_upper u hu
    rw [step]
    have h2B : 2 * step u * (step u + 1) < (2 * u + 2) ^ 2 := by
      nlinarith
    exact Nat.sqrt_lt'.2 h2B
  have : step (step u) ≤ 2 * u + 1 := by omega
  omega

-- ── P2a: u is positive and strictly increasing ──────────────────────

/-- step is positive for u ≥ 1. -/
theorem step_pos (u : ℕ) (hu : 1 ≤ u) : 1 ≤ step u := by
  have h : 1 ≤ 2 * u * (u + 1) := by nlinarith
  have hs : 1 * 1 ≤ 2 * u * (u + 1) := by simpa using h
  exact Nat.le_sqrt.2 hs

/-- u < step u for u ≥ 1. -/
theorem step_gt_u (u : ℕ) (hu : 1 ≤ u) : u < step u := by
  have hnot : ¬ step u < u + 1 := by
    intro hs
    have hs' : 2 * u * (u + 1) < (u + 1) ^ 2 := Nat.sqrt_lt'.1 hs
    nlinarith
  have hle : u + 1 ≤ step u := by omega
  omega

/-- u n ≥ 1 for n ≥ 1. -/
theorem u_pos : ∀ n : ℕ, n ≥ 1 → 1 ≤ u n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => omega
      | succ m =>
          by_cases h0 : m = 0
          · subst m; norm_num [u]
          · have hm : 1 ≤ m := by omega
            have hm_lt : m < m + 1 := by omega
            have hprev : 1 ≤ u m := ih m hm_lt hm
            have hstep : 1 ≤ step (u m) := step_pos (u m) hprev
            have hrs : u (m + 1) = step (u m) := by simp [u, h0]
            rw [hrs]
            exact hstep

/-- u is strictly increasing: u n < u (n+1) for n ≥ 1. -/
theorem u_strict_mono (n : ℕ) (hn : 1 ≤ n) : u n < u (n + 1) := by
  have hpos : 1 ≤ u n := u_pos n hn
  have hstep : u n < step (u n) := step_gt_u (u n) hpos
  rw [u_rec hn]
  exact hstep

-- ── P3: d_n ∈ {0,1} ────────────────────────────────────────────────

/-- d_n := u_{2n+1} − 2·u_{2n−1}. -/
def d (n : ℕ) : ℕ := u (2 * n + 1) - 2 * (u (2 * n - 1))

/-- u_{2n+1} = step(step(u_{2n-1})) for n ≥ 1. -/
theorem u_odd_composition (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n + 1) = step (step (u (2 * n - 1))) := by
  have h1 : u (2 * n) = step (u (2 * n - 1)) := by
    -- u_rec with index 2n-1 gives u((2n-1)+1) = step(u(2n-1)); show 2n-1+1 = 2n
    have hi : 1 ≤ 2 * n - 1 := by omega
    have hrec := u_rec (n := 2 * n - 1) hi
    -- 2n-1 + 1 = 2n for n ≥ 1 (truncation: 2n-1 ≥ 1)
    have hstep : (2 * n - 1) + 1 = 2 * n := by omega
    simpa [hstep] using hrec
  have h2 : u (2 * n + 1) = step (u (2 * n)) := by
    have hi : 1 ≤ 2 * n := by omega
    exact u_rec (n := 2 * n) hi
  rw [h2, h1]

/-- u(2n−1) ≥ 3 for n ≥ 2: since u is increasing and 2n−1 ≥ 3, and u(3)=3. -/
theorem u_odd_ge_three (n : ℕ) (hn : 2 ≤ n) : 3 ≤ u (2 * n - 1) := by
  have hk : 3 ≤ 2 * n - 1 := by omega
  -- monotone (for a ≥ 1): if a ≤ b then u a ≤ u b. Induct on b.
  have hmono : ∀ a b : ℕ, 1 ≤ a → a ≤ b → u a ≤ u b := by
    intro a b ha1 hab
    -- induct on b, keeping the standard succ structure
    induction b using Nat.strong_induction_on with
    | h b ih =>
        by_cases ha : a = b
        · subst a; rfl
        · have hlt : a < b := lt_of_le_of_ne hab ha
          -- since a ≥ 1 and a < b, b ≥ 2 so b-1 ≥ 1
          have hb_ge : 1 ≤ b - 1 := by omega
          have ha_le : a ≤ b - 1 := by omega
          -- ih is ∀ m, m < b → (a ≤ m → u a ≤ u m)  (a fixed)
          have hua : u a ≤ u (b - 1) := ih (b - 1) (by omega) ha_le
          -- u(b-1) < u(b-1+1) = u b via u_strict_mono
          have hstep : u (b - 1) < u b := by
            have hs := u_strict_mono (b - 1) hb_ge
            -- u(b-1) < u((b-1)+1) and (b-1)+1 = b
            have hplus : (b - 1) + 1 = b := by omega
            simpa [hplus] using hs
          exact le_trans hua (le_of_lt hstep)
  have h3 : u 3 = 3 := by native_decide
  have hge : 3 ≤ u 3 := by simpa [h3]
  have hu3 : u 3 ≤ u (2 * n - 1) := hmono 3 (2 * n - 1) (by omega) hk
  exact le_trans hge hu3

/-- P3 main theorem: d_n ∈ {0,1} for n ≥ 2. -/
theorem d_mem_zero_one (n : ℕ) (hn : 2 ≤ n) :
    d n = 0 ∨ d n = 1 := by
  have hn1 : 1 ≤ n := by omega
  have hcomp := u_odd_composition n hn1
  have hu : 3 ≤ u (2 * n - 1) := u_odd_ge_three n hn
  have hd : step (step (u (2 * n - 1))) - 2 * u (2 * n - 1) = 0 ∨
            step (step (u (2 * n - 1))) - 2 * u (2 * n - 1) = 1 :=
    step_step_digit (u (2 * n - 1)) hu
  rw [d, hcomp]
  exact hd

end Jsp391