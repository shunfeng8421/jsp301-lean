import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.Basic

open Filter
open scoped BigOperators

/-!
# JSP-000492 (Erdős #605)

Catalog statement: "Can the number of pairs at one distance in a finite spherical point
set grow superlinearly?"  Solved affirmatively:

* Erdős–Hickerson–Pach (1989): u_√2(n) = Θ(n^{4/3}).
* Swanepoel–Valtr (2004), Theorem 1:  u_D(n) > c · n · √(log n)  for every D > 1, n ≥ 2,
  where u_D(n) is the max number of unit distances among n points on a sphere of
  diameter D, and c > 0 is an absolute constant (c = 1/10 suffices for log base 2).

We formalize Swanepoel–Valtr Theorem 1, then derive the official JSP-000492 corollary:
there is f(n) → ∞ such that for every n there are n distinct points on the unit sphere
with at least n·f(n) unordered pairs at distance √2.
-/

namespace Jsp492

noncomputable section

abbrev E3 := PiLp 2 (fun _ : Fin 3 => ℝ)

/-- The (Euclidean) sphere in E3 with center `c` and radius `r`. -/
def sphere (c : E3) (r : ℝ) : Set E3 := {p | dist p c = r}

/-- Rotation around the z-axis by angle `θ` (explicit coordinates). -/
def rotateZ (θ : ℝ) (p : E3) : E3 :=
  WithLp.toLp (p := 2)
    (ofLp := fun i : Fin 3 =>
      match i with
      | ⟨0, _⟩ => p 0 * Real.cos θ - p 1 * Real.sin θ
      | ⟨1, _⟩ => p 0 * Real.sin θ + p 1 * Real.cos θ
      | ⟨2, _⟩ => p 2)

-- coordinate access of a rotation
lemma rotateZ_coord0 (θ : ℝ) (p : E3) : (rotateZ θ p) 0 = p 0 * Real.cos θ - p 1 * Real.sin θ := rfl

lemma rotateZ_coord1 (θ : ℝ) (p : E3) : (rotateZ θ p) 1 = p 0 * Real.sin θ + p 1 * Real.cos θ := rfl

lemma rotateZ_coord2 (θ : ℝ) (p : E3) : (rotateZ θ p) 2 = p 2 := rfl

-- linearity (difference)
lemma rotateZ_sub (θ : ℝ) (p q : E3) : rotateZ θ (p - q) = rotateZ θ p - rotateZ θ q := by
  ext i
  fin_cases i <;> simp [rotateZ] <;> ring

-- rotation preserves distance
lemma rotateZ_isometry (θ : ℝ) (p q : E3) : dist (rotateZ θ p) (rotateZ θ q) = dist p q := by
  have hSum : (∑ i : Fin 3, dist ((rotateZ θ p) i) ((rotateZ θ q) i) ^ (2 : ℝ)) =
              (∑ i : Fin 3, dist (p i) (q i) ^ (2 : ℝ)) := by
    simp [rotateZ_coord0, rotateZ_coord1, rotateZ_coord2, Fin.sum_univ_three, dist_eq_norm]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have hp2 : 0 < (2 : ENNReal).toReal := by norm_num
  calc
    dist (rotateZ θ p) (rotateZ θ q)
        = (∑ i : Fin 3, dist ((rotateZ θ p) i) ((rotateZ θ q) i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          PiLp.dist_eq_sum hp2 (rotateZ θ p) (rotateZ θ q)
    _ = (∑ i : Fin 3, dist (p i) (q i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [hSum]
    _ = dist p q := (PiLp.dist_eq_sum hp2 p q).symm

/-- Ordered pairs of distinct points of `B` at distance exactly `1`. -/
def orderedUnitPairs (B : Finset E3) : ℕ :=
  ((B.product B).filter (fun pq : E3 × E3 => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1)).card

/-- Unordered pairs of distinct points of `B` at distance exactly `1` (each unordered
pair corresponds to exactly two ordered pairs). -/
def unorderedUnitPairs (B : Finset E3) : ℕ :=
  orderedUnitPairs B / 2

/-- Distance-√2 unordered pairs (official JSP-492 counting). -/
def unorderedUnitPairsAtSqrt2 (B : Finset E3) : ℕ :=
  ((B.product B).filter (fun pq : E3 × E3 => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = Real.sqrt 2)).card / 2

/-! ## Swanepoel–Valtr Theorem 1 (critical-diameter corollary)

The official JSP-000492 statement is the `∃ f → ∞` corollary `jsp492_official`
(matching the catalog entry); `swanepoel_valtr` below is its
`≥ c·n·√(log n)` unordered unit-distance-pair form on the critical sphere of
radius `1/√2` (diameter `√2`), obtained by scaling the construction by `1/√2`.
-/

/-- Normalized point (x,y,z)/‖(x,y,z)‖. -/
noncomputable def normPt (x y z : ℝ) : E3 :=
  WithLp.toLp (p := 2)
    (ofLp := fun i : Fin 3 =>
      match i with
      | ⟨0, _⟩ => x / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
      | ⟨1, _⟩ => y / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
      | ⟨2, _⟩ => z / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2))

lemma normPt_coord0 (x y z : ℝ) : (normPt x y z) 0 = x / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := rfl
lemma normPt_coord1 (x y z : ℝ) : (normPt x y z) 1 = y / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := rfl
lemma normPt_coord2 (x y z : ℝ) : (normPt x y z) 2 = z / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := rfl

-- raw orthogonality: u = (c, a*c+b, 1), v = (a, -1, b)
lemma raw_dot_zero (c a b : ℝ) : c * a + (a * c + b) * (-1) + 1 * b = 0 := by
  ring

-- normalized vectors are on the unit sphere:
-- dist (normPt x y z) 0 = 1 provided x^2+y^2+z^2 > 0
lemma normPt_sphere (x y z : ℝ) (hS : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    dist (normPt x y z) 0 = 1 := by
  have hp2 : 0 < (2 : ENNReal).toReal := by norm_num
  have hsum :
      (∑ i : Fin 3, dist ((normPt x y z) i) 0 ^ (2 : ℝ)) =
        (x ^ 2 + y ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by
    simp [normPt_coord0, normPt_coord1, normPt_coord2, Fin.sum_univ_three, dist_eq_norm,
      Real.norm_eq_abs]
    have hsq0 : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS)
    have hS2 : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
      exact Real.sq_sqrt (le_of_lt hS)
    field_simp [hsq0]
    rw [hS2]
  calc
    dist (normPt x y z) 0
        = (∑ i : Fin 3, dist ((normPt x y z) i) 0 ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          PiLp.dist_eq_sum hp2 (normPt x y z) 0
    _ = ((x ^ 2 + y ^ 2 + z ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) ^ (1 / 2 : ℝ) := by
          rw [hsum]
    _ = 1 := by
          rw [div_self (ne_of_gt hS)]
          norm_num

-- core: normalized raw point and raw line are at distance √2
lemma normPt_dist_sqrt2 (c a b : ℝ) :
    dist (normPt c (a * c + b) 1) (normPt a (-1) b) = Real.sqrt 2 := by
  have hp2 : 0 < (2 : ENNReal).toReal := by norm_num
  have hS1 : 0 < c ^ 2 + (a * c + b) ^ 2 + 1 := by positivity
  have hS2 : 0 < a ^ 2 + 1 + b ^ 2 := by positivity
  have hsq1 : Real.sqrt (c ^ 2 + (a * c + b) ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS1)
  have hsq2 : Real.sqrt (a ^ 2 + 1 + b ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS2)
  have hS1sq : Real.sqrt (c ^ 2 + (a * c + b) ^ 2 + 1) ^ 2 = c ^ 2 + (a * c + b) ^ 2 + 1 :=
    Real.sq_sqrt (le_of_lt hS1)
  have hS2sq : Real.sqrt (a ^ 2 + 1 + b ^ 2) ^ 2 = a ^ 2 + 1 + b ^ 2 :=
    Real.sq_sqrt (le_of_lt hS2)
  have hsum : (∑ i : Fin 3, dist ((normPt c (a * c + b) 1) i) ((normPt a (-1) b) i) ^ (2 : ℝ)) = 2 := by
    simp [normPt_coord0, normPt_coord1, normPt_coord2, Fin.sum_univ_three, dist_eq_norm,
      Real.norm_eq_abs]
    field_simp [hsq1, hsq2]
    rw [show c ^ 2 + (c * a + b) ^ 2 + 1 = c ^ 2 + (a * c + b) ^ 2 + 1 by ring]
    nlinarith [raw_dot_zero c a b, hS1sq, hS2sq]
  have hsum0 : 0 ≤ (∑ i : Fin 3, dist ((normPt c (a * c + b) 1) i) ((normPt a (-1) b) i) ^ (2 : ℝ)) := by
    positivity
  have hdist2 : dist (normPt c (a * c + b) 1) (normPt a (-1) b) ^ (2 : ℝ) = 2 := by
    calc
      dist (normPt c (a * c + b) 1) (normPt a (-1) b) ^ (2 : ℝ)
          = ((∑ i : Fin 3, dist ((normPt c (a * c + b) 1) i) ((normPt a (-1) b) i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
              rw [PiLp.dist_eq_sum hp2 (normPt c (a * c + b) 1) (normPt a (-1) b)]
              norm_num
      _ = (∑ i : Fin 3, dist ((normPt c (a * c + b) 1) i) ((normPt a (-1) b) i) ^ (2 : ℝ)) ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
              rw [Real.rpow_mul hsum0]
      _ = (∑ i : Fin 3, dist ((normPt c (a * c + b) 1) i) ((normPt a (-1) b) i) ^ (2 : ℝ)) ^ (1 : ℝ) := by
              congr 1
              norm_num
      _ = 2 := by
              rw [Real.rpow_one, hsum]
  calc
    dist (normPt c (a * c + b) 1) (normPt a (-1) b)
        = Real.sqrt (dist (normPt c (a * c + b) 1) (normPt a (-1) b) ^ (2 : ℝ)) := by
            rw [Real.rpow_two]
            rw [Real.sqrt_sq_eq_abs (dist (normPt c (a * c + b) 1) (normPt a (-1) b))]
            rw [abs_of_nonneg (dist_nonneg)]
    _ = Real.sqrt 2 := by
            rw [hdist2]

noncomputable def pointW (c a b : ℝ) : E3 := normPt c (a * c + b) 1

noncomputable def lineW (a b : ℝ) : E3 := normPt a (-1) b

lemma incidence_dist_sqrt2 (c a b : ℝ) :
    dist (pointW c a b) (lineW a b) = Real.sqrt 2 := by
  simp [pointW, lineW, normPt_dist_sqrt2 c a b]

-- 二参数点族：pointM c m = (c, m, 1) 归一化；入射对取 m = a·c + b
noncomputable def pointM (c m : ℝ) : E3 := normPt c m 1

lemma incidence_dist_sqrt2' (c a b : ℝ) :
    dist (pointM c (a * c + b)) (lineW a b) = Real.sqrt 2 := by
  simp [pointM, lineW, normPt_dist_sqrt2 c a b]

-- 点线不交：pointM 第二坐标 m/√S ≥ 0（m ≥ 0 时），lineW 第二坐标 -1/√T < 0
lemma pointM_ne_lineW_of_nonneg (c m a b : ℝ) (hm : 0 ≤ m) : pointM c m ≠ lineW a b := by
  intro h
  have h1 := congrArg (fun p : E3 => p 1) h
  rw [pointM, lineW] at h1
  simp [normPt_coord1] at h1
  have hS : 0 < c ^ 2 + m ^ 2 + 1 := by nlinarith [sq_nonneg c, sq_nonneg m]
  have hT : 0 < a ^ 2 + 1 + b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have heq : m * Real.sqrt (a ^ 2 + 1 + b ^ 2) = -Real.sqrt (c ^ 2 + m ^ 2 + 1) := by
    field_simp [ne_of_gt (Real.sqrt_pos.2 hS), ne_of_gt (Real.sqrt_pos.2 hT)] at h1
    linarith
  have hprod : 0 ≤ m * Real.sqrt (a ^ 2 + 1 + b ^ 2) :=
    mul_nonneg hm (Real.sqrt_nonneg _)
  have hneg : m * Real.sqrt (a ^ 2 + 1 + b ^ 2) < 0 := by
    nlinarith [heq, Real.sqrt_pos.2 hS]
  exact not_le_of_gt hneg hprod

-- 点端单射：第三坐标 1/√S 恢复归一化比 → 前两坐标恢复 (c, m)
lemma pointM_inj (c m c' m' : ℝ) (h : pointM c m = pointM c' m') : c = c' ∧ m = m' := by
  have h0 := congrArg (fun p : E3 => p 0) h
  have h1 := congrArg (fun p : E3 => p 1) h
  have h2 := congrArg (fun p : E3 => p 2) h
  rw [pointM, pointM] at h0 h1 h2
  simp [normPt_coord0, normPt_coord1, normPt_coord2] at h0 h1 h2
  have hS : 0 < c ^ 2 + m ^ 2 + 1 := by nlinarith [sq_nonneg c, sq_nonneg m]
  have hS' : 0 < c' ^ 2 + m' ^ 2 + 1 := by nlinarith [sq_nonneg c', sq_nonneg m']
  have hsqrt : Real.sqrt (c ^ 2 + m ^ 2 + 1) = Real.sqrt (c' ^ 2 + m' ^ 2 + 1) := by
    have h2' := h2
    field_simp [ne_of_gt (Real.sqrt_pos.2 hS), ne_of_gt (Real.sqrt_pos.2 hS')] at h2'
    exact h2'
  have hc : c = c' := by
    have h0' := h0
    rw [hsqrt] at h0'
    field_simp [ne_of_gt (Real.sqrt_pos.2 hS')] at h0'
    exact h0'
  have hm : m = m' := by
    have h1' := h1
    rw [hsqrt] at h1'
    field_simp [ne_of_gt (Real.sqrt_pos.2 hS')] at h1'
    exact h1'
  exact ⟨hc, hm⟩

-- 线端单射：第二坐标 -1/√T 恢复 √T → 第一/第三坐标恢复 (a, b)
lemma lineW_inj (a b a' b' : ℝ) (h : lineW a b = lineW a' b') : a = a' ∧ b = b' := by
  have h0 := congrArg (fun p : E3 => p 0) h
  have h1 := congrArg (fun p : E3 => p 1) h
  have h2 := congrArg (fun p : E3 => p 2) h
  rw [lineW, lineW] at h0 h1 h2
  simp [normPt_coord0, normPt_coord1, normPt_coord2] at h0 h1 h2
  have hT : 0 < a ^ 2 + 1 + b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hT' : 0 < a' ^ 2 + 1 + b' ^ 2 := by nlinarith [sq_nonneg a', sq_nonneg b']
  have hsqrt : Real.sqrt (a ^ 2 + 1 + b ^ 2) = Real.sqrt (a' ^ 2 + 1 + b' ^ 2) := by
    have h1' := h1
    field_simp [ne_of_gt (Real.sqrt_pos.2 hT), ne_of_gt (Real.sqrt_pos.2 hT')] at h1'
    linarith
  have ha : a = a' := by
    have h0' := h0
    rw [hsqrt] at h0'
    field_simp [ne_of_gt (Real.sqrt_pos.2 hT')] at h0'
    exact h0'
  have hb : b = b' := by
    have h2' := h2
    rw [hsqrt] at h2'
    field_simp [ne_of_gt (Real.sqrt_pos.2 hT')] at h2'
    exact h2'
  exact ⟨ha, hb⟩

-- ===== 格8 Finset 化：入射对与端点集合 =====

-- 入射对索引：(c ∈ Fin q, a ∈ Fin (q ^ 2), b ∈ Fin q)，共 q·q²·q = q⁴ 对
abbrev incidenceIndex (q : ℕ) := Fin q × Fin (q ^ 2) × Fin q

-- 线端集合：lineW a b（a ∈ Fin (q ^ 2), b ∈ Fin q）
noncomputable def lineSet (q : ℕ) : Finset E3 :=
  (Finset.univ : Finset (Fin (q ^ 2) × Fin q)).image (fun t : Fin (q ^ 2) × Fin q =>
    lineW ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ))

-- 点端集合：pointM c (a·c + b)（(c,a,b) ∈ incidenceIndex）
noncomputable def pointSet (q : ℕ) : Finset E3 :=
  (Finset.univ : Finset (incidenceIndex q)).image (fun t : incidenceIndex q =>
    pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)))

-- 入射对：(c,a,b) ↦ (点端, 线端)
noncomputable def incidencePairs (q : ℕ) : Finset (E3 × E3) :=
  (Finset.univ : Finset (incidenceIndex q)).image
    (fun t : incidenceIndex q =>
      (pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)),
       lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)))

-- Fin 元素提升到 ℝ 非负
lemma fin_to_real_nonneg {n : ℕ} (i : Fin n) : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by
  exact_mod_cast (Nat.zero_le i.1)

-- 入射对端点距离恒 √2
lemma incidencePairs_dist_sqrt2 (q : ℕ) :
    ∀ t ∈ incidencePairs q, dist t.1 t.2 = Real.sqrt 2 := by
  intro t ht
  rw [incidencePairs] at ht
  rw [Finset.mem_image] at ht
  rcases ht with ⟨i, hi, rfl⟩
  exact incidence_dist_sqrt2' ((i.1 : ℕ) : ℝ) ((i.2.1 : ℕ) : ℝ) ((i.2.2 : ℕ) : ℝ)

-- ===== 格8 计数：入射对单射/card + 无序距离对 =====

-- 入射对单射：(c,a,b) ↦ (点端, 线端)
lemma incidencePairs_injective (q : ℕ) :
    Function.Injective (fun t : incidenceIndex q =>
      (pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)),
       lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ))) := by
  intro t t' h
  rcases t with ⟨c, a, b⟩
  rcases t' with ⟨c', a', b'⟩
  have hP := congrArg Prod.fst h
  have hL := congrArg Prod.snd h
  rcases pointM_inj ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
      ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) hP with ⟨hc, hm⟩
  rcases lineW_inj ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) hL with ⟨ha, hb⟩
  have hcN : (c : ℕ) = (c' : ℕ) := by exact_mod_cast hc
  have haN : (a : ℕ) = (a' : ℕ) := by exact_mod_cast ha
  have hbN : (b : ℕ) = (b' : ℕ) := by exact_mod_cast hb
  have hcF : c = c' := Fin.ext hcN
  have haF : a = a' := Fin.ext haN
  have hbF : b = b' := Fin.ext hbN
  subst hcF
  subst haF
  subst hbF
  rfl

-- 入射对数 = q⁴
lemma incidencePairs_card (q : ℕ) : (incidencePairs q).card = q ^ 4 := by
  rw [incidencePairs]
  rw [Finset.card_image_of_injective]
  · simp
    ring
  · exact incidencePairs_injective q

-- 全局点线不交：Fin 参数下 m = a·c+b ≥ 0 → pointM ≠ lineW
lemma pointM_ne_lineW_all (c a b : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pointM c (a * c + b) ≠ lineW a b := by
  exact pointM_ne_lineW_of_nonneg c (a * c + b) a b (by nlinarith [mul_nonneg ha hc, hb])

-- 无序距离对集合：incidencePairs 的有序对 → {点端, 线端}
noncomputable def unorderedPairs (q : ℕ) : Finset (Finset E3) :=
  (incidencePairs q).image (fun t : E3 × E3 => ({t.1, t.2} : Finset E3))

-- 无序对元素 card = 2（点端 ≠ 线端）
lemma unorderedPairs_card_mem (q : ℕ) {s : Finset E3} (hs : s ∈ unorderedPairs q) : s.card = 2 := by
  rw [unorderedPairs, Finset.mem_image] at hs
  rcases hs with ⟨t, ht, rfl⟩
  rw [incidencePairs, Finset.mem_image] at ht
  rcases ht with ⟨i, hi, rfl⟩
  have hne : pointM ((i.1 : ℕ) : ℝ) (((i.2.1 : ℕ) : ℝ) * ((i.1 : ℕ) : ℝ) + ((i.2.2 : ℕ) : ℝ)) ≠
      lineW ((i.2.1 : ℕ) : ℝ) ((i.2.2 : ℕ) : ℝ) := by
    exact pointM_ne_lineW_all ((i.1 : ℕ) : ℝ) ((i.2.1 : ℕ) : ℝ) ((i.2.2 : ℕ) : ℝ)
      (fin_to_real_nonneg i.1) (fin_to_real_nonneg i.2.1) (fin_to_real_nonneg i.2.2)
  simp [hne]

-- 无序距离对数 = q⁴（card_image_iff 局部单射：成员论证 + 点线不交）
lemma unorderedPairs_card (q : ℕ) : (unorderedPairs q).card = q ^ 4 := by
  rw [unorderedPairs]
  rw [← incidencePairs_card q]
  rw [Finset.card_image_iff]
  intro t ht t' ht' hpair
  rw [incidencePairs] at ht
  rw [incidencePairs] at ht'
  rw [Finset.mem_coe] at ht
  rw [Finset.mem_coe] at ht'
  rw [Finset.mem_image] at ht
  rw [Finset.mem_image] at ht'
  rcases ht with ⟨i, hi, rfl⟩
  rcases ht' with ⟨i', hi', rfl⟩
  rcases i with ⟨c, a, b⟩
  rcases i' with ⟨c', a', b'⟩
  simp at hpair
  -- hpair : {pointM c (a·c+b), lineW a b} = {pointM c' (a'·c'+b'), lineW a' b'}
  -- 由成员论证推出点端相等、线端相等（点线不交排除交错）
  have hP : pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)) =
      pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) := by
    have hmem : pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)) ∈
        ({pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)),
          lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ)} : Finset E3) := by
      rw [← hpair]
      simp
    rcases (Finset.mem_insert.mp hmem) with hPP' | hPL'
    · exact hPP'
    · exfalso
      have hnot : pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)) ≠
          lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) := by
        exact pointM_ne_lineW_of_nonneg ((c : ℕ) : ℝ)
          (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
          ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ)
          (by nlinarith [mul_nonneg (fin_to_real_nonneg a) (fin_to_real_nonneg c),
            fin_to_real_nonneg b])
      exact hnot (Finset.mem_singleton.mp hPL')
  have hL : lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) =
      lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) := by
    have hmem : lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ∈
        ({pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)),
          lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ)} : Finset E3) := by
      rw [← hpair]
      simp
    rcases (Finset.mem_insert.mp hmem) with hLP' | hLL'
    · exfalso
      have hnot : pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) ≠
          lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) := by
        exact pointM_ne_lineW_of_nonneg ((c' : ℕ) : ℝ)
          (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ))
          ((a : ℕ) : ℝ) ((b : ℕ) : ℝ)
          (by nlinarith [mul_nonneg (fin_to_real_nonneg a') (fin_to_real_nonneg c'),
            fin_to_real_nonneg b'])
      exact hnot hLP'.symm
    · exact Finset.mem_singleton.mp hLL'
  rcases pointM_inj ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
      ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) hP with ⟨hc, hm⟩
  rcases lineW_inj ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) hL with ⟨ha, hb⟩
  have hcN : (c : ℕ) = (c' : ℕ) := by exact_mod_cast hc
  have haN : (a : ℕ) = (a' : ℕ) := by exact_mod_cast ha
  have hbN : (b : ℕ) = (b' : ℕ) := by exact_mod_cast hb
  have hcF : c = c' := Fin.ext hcN
  have haF : a = a' := Fin.ext haN
  have hbF : b = b' := Fin.ext hbN
  subst hcF
  subst haF
  subst hbF
  change (pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)),
      lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ)) =
    (pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)),
      lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ))
  rfl

-- ===== 格8 正式参数化（STATE 方案）：3q³ 点、q⁴ 对、距离 √2 =====
-- 索引 (c, a, b) ∈ Fin q × Fin q × Fin (q²)：q·q·q² = q⁴ 入射对
-- 点端 m = a·c+b ∈ Fin (2q²)：pointSet2 = Fin q × Fin (2q²)（2q³ 点）
-- 线端 lineW a b：(a,b) ∈ Fin q × Fin (q²)（q³ 线）；总 |B| = 3q³ ≤ n


abbrev index2 (q : ℕ) := Fin q × Fin q × Fin (q ^ 2)

-- m = a·c+b < 2q²：保证点端落在 pointSet2 参数空间
lemma m_lt_two_q2 (q : ℕ) (a : Fin q) (c : Fin q) (b : Fin (q ^ 2)) :
    (a : ℕ) * (c : ℕ) + (b : ℕ) < 2 * q ^ 2 := by
  have hac : (a : ℕ) * (c : ℕ) < q * q := by
    nlinarith [(a : Fin q).isLt, (c : Fin q).isLt]
  have hb : (b : ℕ) < q ^ 2 := (b : Fin (q ^ 2)).isLt
  nlinarith [hac, hb]

-- 点端全空间：(c, m) ∈ Fin q × Fin (2q²)
noncomputable def pointSet2 (q : ℕ) : Finset E3 :=
  (Finset.univ : Finset (Fin q × Fin (2 * q ^ 2))).image (fun t : Fin q × Fin (2 * q ^ 2) =>
    pointM ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ))

-- 线端空间：(a, b) ∈ Fin q × Fin (q²)
noncomputable def lineSet2 (q : ℕ) : Finset E3 :=
  (Finset.univ : Finset (Fin q × Fin (q ^ 2))).image (fun t : Fin q × Fin (q ^ 2) =>
    lineW ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ))

-- 基础点集 B：端点并集（3q³ 点）
noncomputable def B2 (q : ℕ) : Finset E3 := pointSet2 q ∪ lineSet2 q

-- 入射对：(c,a,b) ↦ (pointM c (a·c+b), lineW a b)
noncomputable def pairs2 (q : ℕ) : Finset (E3 × E3) :=
  (Finset.univ : Finset (index2 q)).image
    (fun t : index2 q =>
      (pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)),
       lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)))

-- 入射对端点距离恒 √2
lemma pairs2_dist_sqrt2 (q : ℕ) : ∀ t ∈ pairs2 q, dist t.1 t.2 = Real.sqrt 2 := by
  intro t ht
  rw [pairs2] at ht
  rw [Finset.mem_image] at ht
  rcases ht with ⟨i, hi, rfl⟩
  exact incidence_dist_sqrt2' ((i.1 : ℕ) : ℝ) ((i.2.1 : ℕ) : ℝ) ((i.2.2 : ℕ) : ℝ)

-- 入射对单射：(c,a,b) ↦ (点端, 线端)
lemma pairs2_injective (q : ℕ) :
    Function.Injective (fun t : index2 q =>
      (pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)),
       lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ))) := by
  intro t t' h
  rcases t with ⟨c, a, b⟩
  rcases t' with ⟨c', a', b'⟩
  have hP := congrArg Prod.fst h
  have hL := congrArg Prod.snd h
  rcases pointM_inj ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
      ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) hP with ⟨hc, hm⟩
  rcases lineW_inj ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) hL with ⟨ha, hb⟩
  have hcN : (c : ℕ) = (c' : ℕ) := by exact_mod_cast hc
  have haN : (a : ℕ) = (a' : ℕ) := by exact_mod_cast ha
  have hbN : (b : ℕ) = (b' : ℕ) := by exact_mod_cast hb
  have hcF : c = c' := Fin.ext hcN
  have haF : a = a' := Fin.ext haN
  have hbF : b = b' := Fin.ext hbN
  subst hcF
  subst haF
  subst hbF
  rfl

-- 入射对数 = q⁴
lemma pairs2_card (q : ℕ) : (pairs2 q).card = q ^ 4 := by
  rw [pairs2]
  rw [Finset.card_image_of_injective]
  · simp
    ring
  · exact pairs2_injective q

-- 点端参数单射：(c, m) ↦ pointM c m
lemma pointM_fin_inj (q : ℕ) :
    Function.Injective (fun t : Fin q × Fin (2 * q ^ 2) =>
      pointM ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ)) := by
  intro t t' h
  rcases t with ⟨c, m⟩
  rcases t' with ⟨c', m'⟩
  rcases pointM_inj ((c : ℕ) : ℝ) ((m : ℕ) : ℝ) ((c' : ℕ) : ℝ) ((m' : ℕ) : ℝ) h with ⟨hc, hm⟩
  have hcN : (c : ℕ) = (c' : ℕ) := by exact_mod_cast hc
  have hmN : (m : ℕ) = (m' : ℕ) := by exact_mod_cast hm
  have hcF : c = c' := Fin.ext hcN
  have hmF : m = m' := Fin.ext hmN
  subst hcF
  subst hmF
  rfl

-- 点端集合 card = 2q³
lemma pointSet2_card (q : ℕ) : (pointSet2 q).card = 2 * q ^ 3 := by
  rw [pointSet2]
  rw [Finset.card_image_of_injective]
  · simp
    ring
  · exact pointM_fin_inj q

-- 线端参数单射：(a, b) ↦ lineW a b
lemma lineW_fin_inj (q : ℕ) :
    Function.Injective (fun t : Fin q × Fin (q ^ 2) =>
      lineW ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ)) := by
  intro t t' h
  rcases t with ⟨a, b⟩
  rcases t' with ⟨a', b'⟩
  rcases lineW_inj ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) h with ⟨ha, hb⟩
  have haN : (a : ℕ) = (a' : ℕ) := by exact_mod_cast ha
  have hbN : (b : ℕ) = (b' : ℕ) := by exact_mod_cast hb
  have haF : a = a' := Fin.ext haN
  have hbF : b = b' := Fin.ext hbN
  subst haF
  subst hbF
  rfl

-- 线端集合 card = q³
lemma lineSet2_card (q : ℕ) : (lineSet2 q).card = q ^ 3 := by
  rw [lineSet2]
  rw [Finset.card_image_of_injective]
  · simp
    ring
  · exact lineW_fin_inj q

-- 点线不交（pointM 第三坐标 1/√S > 0 类论证）
lemma pointSet2_disj_lineSet2 (q : ℕ) : Disjoint (pointSet2 q) (lineSet2 q) := by
  rw [Finset.disjoint_left]
  intro x hx
  rw [pointSet2, Finset.mem_image] at hx
  rcases hx with ⟨tx, htx, rfl⟩
  rw [lineSet2, Finset.mem_image]
  rintro ⟨ty, hty, hxy⟩
  exact pointM_ne_lineW_of_nonneg ((tx.1 : ℕ) : ℝ) ((tx.2 : ℕ) : ℝ)
    ((ty.1 : ℕ) : ℝ) ((ty.2 : ℕ) : ℝ) (fin_to_real_nonneg tx.2) hxy.symm

-- B 集合 card = 3q³
lemma B2_card (q : ℕ) : (B2 q).card = 3 * q ^ 3 := by
  rw [B2]
  rw [Finset.card_union_of_disjoint]
  · rw [pointSet2_card, lineSet2_card]
    ring
  · exact pointSet2_disj_lineSet2 q

-- 点端在单位球面
lemma pointM_unit (c m : ℝ) : dist (pointM c m) 0 = 1 := by
  rw [pointM]
  exact normPt_sphere c m 1 (by nlinarith [sq_nonneg c, sq_nonneg m])

-- 线端在单位球面
lemma lineW_unit (a b : ℝ) : dist (lineW a b) 0 = 1 := by
  rw [lineW]
  exact normPt_sphere a (-1) b (by nlinarith [sq_nonneg a, sq_nonneg b])

-- B 全在单位球面
lemma B2_unit (q : ℕ) : ∀ p ∈ B2 q, p ∈ sphere 0 1 := by
  intro p hp
  rw [B2, Finset.mem_union] at hp
  rcases hp with hp | hp
  · rw [pointSet2, Finset.mem_image] at hp
    rcases hp with ⟨t, ht, rfl⟩
    exact pointM_unit ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ)
  · rw [lineSet2, Finset.mem_image] at hp
    rcases hp with ⟨t, ht, rfl⟩
    exact lineW_unit ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ)

-- 入射对点端 ∈ pointSet2（m = a·c+b < 2q² 保证落在参数空间）
lemma pairs2_fst_mem (q : ℕ) {t : index2 q} :
    pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)) ∈ pointSet2 q := by
  rw [pointSet2, Finset.mem_image]
  refine ⟨(t.1, ⟨(t.2.1 : ℕ) * (t.1 : ℕ) + (t.2.2 : ℕ), m_lt_two_q2 q t.2.1 t.1 t.2.2⟩),
    Finset.mem_univ _, ?_⟩
  simp

-- 入射对线端 ∈ lineSet2
lemma pairs2_snd_mem (q : ℕ) {t : index2 q} :
    lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ) ∈ lineSet2 q := by
  rw [lineSet2, Finset.mem_image]
  refine ⟨(t.2.1, t.2.2), Finset.mem_univ _, rfl⟩

-- 无序距离对集合（q⁴ 个 {点端, 线端}）
noncomputable def unorderedPairs2 (q : ℕ) : Finset (Finset E3) :=
  (pairs2 q).image (fun t : E3 × E3 => ({t.1, t.2} : Finset E3))

-- 无序对元素 card = 2（点端 ≠ 线端）
lemma unorderedPairs2_card_mem (q : ℕ) {s : Finset E3} (hs : s ∈ unorderedPairs2 q) : s.card = 2 := by
  rw [unorderedPairs2, Finset.mem_image] at hs
  rcases hs with ⟨t, ht, rfl⟩
  rw [pairs2, Finset.mem_image] at ht
  rcases ht with ⟨i, hi, rfl⟩
  have hne : pointM ((i.1 : ℕ) : ℝ) (((i.2.1 : ℕ) : ℝ) * ((i.1 : ℕ) : ℝ) + ((i.2.2 : ℕ) : ℝ)) ≠
      lineW ((i.2.1 : ℕ) : ℝ) ((i.2.2 : ℕ) : ℝ) := by
    exact pointM_ne_lineW_all ((i.1 : ℕ) : ℝ) ((i.2.1 : ℕ) : ℝ) ((i.2.2 : ℕ) : ℝ)
      (fin_to_real_nonneg i.1) (fin_to_real_nonneg i.2.1) (fin_to_real_nonneg i.2.2)
  simp [hne]

-- 无序距离对数 = q⁴（card_image_iff 局部单射：成员论证 + 点线不交）
lemma unorderedPairs2_card (q : ℕ) : (unorderedPairs2 q).card = q ^ 4 := by
  rw [unorderedPairs2]
  rw [← pairs2_card q]
  rw [Finset.card_image_iff]
  intro t ht t' ht' hpair
  rw [pairs2] at ht
  rw [pairs2] at ht'
  rw [Finset.mem_coe] at ht
  rw [Finset.mem_coe] at ht'
  rw [Finset.mem_image] at ht
  rw [Finset.mem_image] at ht'
  rcases ht with ⟨i, hi, rfl⟩
  rcases ht' with ⟨i', hi', rfl⟩
  rcases i with ⟨c, a, b⟩
  rcases i' with ⟨c', a', b'⟩
  simp at hpair
  have hP : pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)) =
      pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) := by
    have hmem : pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)) ∈
        ({pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)),
          lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ)} : Finset E3) := by
      rw [← hpair]
      simp
    rcases (Finset.mem_insert.mp hmem) with hPP' | hPL'
    · exact hPP'
    · exfalso
      have hnot : pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)) ≠
          lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) := by
        exact pointM_ne_lineW_of_nonneg ((c : ℕ) : ℝ)
          (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
          ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ)
          (by nlinarith [mul_nonneg (fin_to_real_nonneg a) (fin_to_real_nonneg c),
            fin_to_real_nonneg b])
      exact hnot (Finset.mem_singleton.mp hPL')
  have hL : lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) =
      lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) := by
    have hmem : lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ∈
        ({pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)),
          lineW ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ)} : Finset E3) := by
      rw [← hpair]
      simp
    rcases (Finset.mem_insert.mp hmem) with hLP' | hLL'
    · exfalso
      have hnot : pointM ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) ≠
          lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) := by
        exact pointM_ne_lineW_of_nonneg ((c' : ℕ) : ℝ)
          (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ))
          ((a : ℕ) : ℝ) ((b : ℕ) : ℝ)
          (by nlinarith [mul_nonneg (fin_to_real_nonneg a') (fin_to_real_nonneg c'),
            fin_to_real_nonneg b'])
      exact hnot hLP'.symm
    · exact Finset.mem_singleton.mp hLL'
  rcases pointM_inj ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
      ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) hP with ⟨hc, hm⟩
  rcases lineW_inj ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) hL with ⟨ha, hb⟩
  have hcN : (c : ℕ) = (c' : ℕ) := by exact_mod_cast hc
  have haN : (a : ℕ) = (a' : ℕ) := by exact_mod_cast ha
  have hbN : (b : ℕ) = (b' : ℕ) := by exact_mod_cast hb
  have hcF : c = c' := Fin.ext hcN
  have haF : a = a' := Fin.ext haN
  have hbF : b = b' := Fin.ext hbN
  subst hcF
  subst haF
  subst hbF
  change (pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)),
      lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ)) =
    (pointM ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ)),
      lineW ((a : ℕ) : ℝ) ((b : ℕ) : ℝ))
  rfl

-- ===== 计数桥：q⁴ ≤ unorderedUnitPairsAtSqrt2 (B2 q) =====
-- 有序对集合：B2 中距离 √2 的互异有序对（与主文件 unorderedUnitPairsAtSqrt2 的 filter 一致）
noncomputable def sqrt2OrderedPairs (q : ℕ) : Finset (E3 × E3) :=
  ((B2 q).product (B2 q)).filter (fun p : E3 × E3 => p.1 ≠ p.2 ∧ dist p.1 p.2 = Real.sqrt 2)

-- 无序距离 √2 对数（与主文件同名同定义）

-- 任意点端 ≠ 任意线端
lemma pair2_fst_ne_snd (q : ℕ) (t : index2 q) :
    pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)) ≠
      lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ) := by
  exact pointM_ne_lineW_all ((t.1 : ℕ) : ℝ) ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)
    (fin_to_real_nonneg t.1) (fin_to_real_nonneg t.2.1) (fin_to_real_nonneg t.2.2)

-- g 像（pairs2）⊆ sqrt2OrderedPairs
lemma g_mem_sqrt2 (q : ℕ) (t : index2 q) :
    (pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)),
     lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)) ∈ sqrt2OrderedPairs q := by
  rw [sqrt2OrderedPairs]
  rw [Finset.mem_filter]
  constructor
  · refine Finset.mem_product.mpr
      ⟨Finset.mem_union_left (lineSet2 q) (pairs2_fst_mem q),
       Finset.mem_union_right (pointSet2 q) (pairs2_snd_mem q)⟩
  · constructor
    · exact pair2_fst_ne_snd q t
    · exact incidence_dist_sqrt2' ((t.1 : ℕ) : ℝ) ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)

-- h 像（swap）⊆ sqrt2OrderedPairs
lemma h_mem_sqrt2 (q : ℕ) (t : index2 q) :
    (lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ),
     pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ))) ∈ sqrt2OrderedPairs q := by
  rw [sqrt2OrderedPairs]
  rw [Finset.mem_filter]
  constructor
  · refine Finset.mem_product.mpr
      ⟨Finset.mem_union_right (pointSet2 q) (pairs2_snd_mem q),
       Finset.mem_union_left (lineSet2 q) (pairs2_fst_mem q)⟩
  · constructor
    · exact (pair2_fst_ne_snd q t).symm
    · rw [dist_comm]
      exact incidence_dist_sqrt2' ((t.1 : ℕ) : ℝ) ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)

-- h 单射
lemma h_injective (q : ℕ) :
    Function.Injective (fun t : index2 q =>
      (lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ),
       pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ)))) := by
  intro t t' h
  rcases t with ⟨c, a, b⟩
  rcases t' with ⟨c', a', b'⟩
  have hL := congrArg Prod.fst h
  have hP := congrArg Prod.snd h
  rcases lineW_inj ((a : ℕ) : ℝ) ((b : ℕ) : ℝ) ((a' : ℕ) : ℝ) ((b' : ℕ) : ℝ) hL with ⟨ha, hb⟩
  rcases pointM_inj ((c : ℕ) : ℝ) (((a : ℕ) : ℝ) * ((c : ℕ) : ℝ) + ((b : ℕ) : ℝ))
      ((c' : ℕ) : ℝ) (((a' : ℕ) : ℝ) * ((c' : ℕ) : ℝ) + ((b' : ℕ) : ℝ)) hP with ⟨hc, hm⟩
  have hcN : (c : ℕ) = (c' : ℕ) := by exact_mod_cast hc
  have haN : (a : ℕ) = (a' : ℕ) := by exact_mod_cast ha
  have hbN : (b : ℕ) = (b' : ℕ) := by exact_mod_cast hb
  have hcF : c = c' := Fin.ext hcN
  have haF : a = a' := Fin.ext haN
  have hbF : b = b' := Fin.ext hbN
  subst hcF
  subst haF
  subst hbF
  rfl

-- g 像与 h 像不交
lemma g_disj_h (q : ℕ) :
    Disjoint (pairs2 q)
      ((Finset.univ : Finset (index2 q)).image (fun t : index2 q =>
        (lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ),
         pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ))))) := by
  rw [Finset.disjoint_left]
  intro x hx
  rw [pairs2, Finset.mem_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [Finset.mem_image]
  rintro ⟨t', ht', hxy⟩
  have hP := congrArg Prod.snd hxy
  have hne : pointM ((t'.1 : ℕ) : ℝ) (((t'.2.1 : ℕ) : ℝ) * ((t'.1 : ℕ) : ℝ) + ((t'.2.2 : ℕ) : ℝ)) ≠
      lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ) := by
    exact pointM_ne_lineW_of_nonneg ((t'.1 : ℕ) : ℝ)
      (((t'.2.1 : ℕ) : ℝ) * ((t'.1 : ℕ) : ℝ) + ((t'.2.2 : ℕ) : ℝ))
      ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ)
      (by nlinarith [mul_nonneg (fin_to_real_nonneg t'.2.1) (fin_to_real_nonneg t'.1),
        fin_to_real_nonneg t'.2.2])
  exact hne hP

-- 有序 √2 对数 ≥ 2q⁴
lemma sqrt2OrderedPairs_card_ge (q : ℕ) : 2 * q ^ 4 ≤ (sqrt2OrderedPairs q).card := by
  let hset : Finset (E3 × E3) := (Finset.univ : Finset (index2 q)).image
    (fun t : index2 q => (lineW ((t.2.1 : ℕ) : ℝ) ((t.2.2 : ℕ) : ℝ),
      pointM ((t.1 : ℕ) : ℝ) (((t.2.1 : ℕ) : ℝ) * ((t.1 : ℕ) : ℝ) + ((t.2.2 : ℕ) : ℝ))))
  have hg : pairs2 q ⊆ sqrt2OrderedPairs q := by
    intro x hx
    rw [pairs2, Finset.mem_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    exact g_mem_sqrt2 q t
  have hh : hset ⊆ sqrt2OrderedPairs q := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    exact h_mem_sqrt2 q t
  have hdisj : Disjoint (pairs2 q) hset := by
    simpa [hset] using g_disj_h q
  have hcard_h : hset.card = q ^ 4 := by
    dsimp [hset]
    rw [Finset.card_image_of_injective]
    · simp
      ring
    · exact h_injective q
  have hsub : (pairs2 q ∪ hset) ⊆ sqrt2OrderedPairs q := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hg hx
    · exact hh hx
  have hcard : (pairs2 q ∪ hset).card ≤ (sqrt2OrderedPairs q).card := Finset.card_le_card hsub
  have hunion : (pairs2 q ∪ hset).card = (pairs2 q).card + hset.card :=
    Finset.card_union_of_disjoint hdisj
  rw [hunion, pairs2_card, hcard_h] at hcard
  have htwo : 2 * q ^ 4 = q ^ 4 + q ^ 4 := by ring
  rw [htwo]
  exact hcard

-- 无序 √2 对数 ≥ q⁴
lemma unorderedUnitPairsAtSqrt2_B2_ge (q : ℕ) : q ^ 4 ≤ unorderedUnitPairsAtSqrt2 (B2 q) := by
  rw [unorderedUnitPairsAtSqrt2]
  have hge : 2 * q ^ 4 ≤ (sqrt2OrderedPairs q).card := sqrt2OrderedPairs_card_ge q
  have hdiv : q ^ 4 ≤ (sqrt2OrderedPairs q).card / 2 := by
    omega
  exact hdiv
-- ===== 尺度函数 scale3 =====
-- scale3 n = 最大 q 使 3·q³ ≤ n（q=0 恒满足 → filter 非空）
noncomputable def scale3 (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun q => 3 * q ^ 3 ≤ n)).max'
    (by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨by simp, by norm_num⟩)

lemma scale3_spec (n : ℕ) : 3 * (scale3 n) ^ 3 ≤ n := by
  rw [scale3]
  have hmem := Finset.max'_mem ((Finset.range (n + 1)).filter (fun q => 3 * q ^ 3 ≤ n))
    (by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨by simp, by norm_num⟩)
  exact (Finset.mem_filter.mp hmem).2

-- 最大性：3q³ ≤ n → q ≤ scale3 n
lemma scale3_max (n : ℕ) {q : ℕ} (hq : 3 * q ^ 3 ≤ n) : q ≤ scale3 n := by
  rw [scale3]
  apply Finset.le_max' ((Finset.range (n + 1)).filter (fun q => 3 * q ^ 3 ≤ n)) q
  rw [Finset.mem_filter]
  constructor
  · have hq_le : q ≤ n := by
      by_cases hz : q = 0
      · subst q
        exact Nat.zero_le n
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hz
        have hq_le_q3 : q ≤ q ^ 3 := by
          calc
            q = q ^ 1 := by simp
            _ ≤ q ^ 3 := Nat.pow_le_pow_right hqpos (by norm_num : 1 ≤ 3)
        have hq3_le : q ^ 3 ≤ n := by nlinarith [hq]
        exact le_trans hq_le_q3 hq3_le
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hq_le)
  · exact hq
-- ===== f(n) = scale3(n)/24 的增长 =====
noncomputable def f492q (n : ℕ) : ℝ := (scale3 n : ℝ) / 24

lemma scale3_tendsto_nat : Tendsto scale3 atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨3 * M ^ 3, ?_⟩
  intro n hn
  exact scale3_max n hn

lemma scale3_tendsto_real : Tendsto (fun n : ℕ => (scale3 n : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  by_cases hM : M ≤ 0
  · refine ⟨0, ?_⟩
    intro n hn
    exact le_trans hM (by positivity)
  · have hMpos : 0 < M := lt_of_not_ge hM
    obtain ⟨k, hk⟩ := exists_nat_ge M
    refine ⟨3 * k ^ 3, ?_⟩
    intro n hn
    have hsk : k ≤ scale3 n := scale3_max n hn
    exact le_trans hk (by exact_mod_cast hsk)

lemma f492q_tendsto : Tendsto (fun n : ℕ => (scale3 n : ℝ) / 24) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  by_cases hM : M ≤ 0
  · refine ⟨0, ?_⟩
    intro n hn
    exact le_trans hM (by positivity)
  · have hMpos : 0 < M := lt_of_not_ge hM
    obtain ⟨k, hk⟩ := exists_nat_ge (24 * M)
    refine ⟨3 * k ^ 3, ?_⟩
    intro n hn
    have hsk : k ≤ scale3 n := scale3_max n hn
    have h1 : (24 : ℝ) * M ≤ (k : ℝ) := hk
    have h2 : M ≤ (k : ℝ) / 24 := by nlinarith
    have h3 : (k : ℝ) / 24 ≤ (scale3 n : ℝ) / 24 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsk) (by norm_num)
    exact le_trans h2 h3
-- 上界：n < 3(scale3 n + 1)³（最大性反推）
lemma scale3_lt_succ (n : ℕ) : n < 3 * (scale3 n + 1) ^ 3 := by
  by_contra h
  have hle : 3 * (scale3 n + 1) ^ 3 ≤ n := le_of_not_gt h
  have hmax : scale3 n + 1 ≤ scale3 n := scale3_max n hle
  omega

-- 关键不等式：n·f492q(n) ≤ (scale3 n)⁴
lemma n_mul_f492q_le (n : ℕ) : (n : ℝ) * f492q n ≤ (scale3 n : ℝ) ^ 4 := by
  let q := scale3 n
  rw [f492q]
  change (n : ℝ) * ((q : ℝ) / 24) ≤ (q : ℝ) ^ 4
  by_cases hz : q = 0
  · rw [hz]
    simp
  · have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hz
    have hlt : n < 3 * (q + 1) ^ 3 := by
      simpa [q] using scale3_lt_succ n
    have hnℝ : (n : ℝ) ≤ 3 * (q + 1 : ℝ) ^ 3 := by exact_mod_cast (Nat.le_of_lt hlt)
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hqb : (q : ℝ) + 1 ≤ 2 * (q : ℝ) := by
      have hq1r : 1 ≤ (q : ℝ) := by exact_mod_cast hq1
      nlinarith
    have hcub : (q + 1 : ℝ) ^ 3 ≤ 8 * (q : ℝ) ^ 3 := by
      have hp : (q + 1 : ℝ) ^ 3 ≤ (2 * (q : ℝ)) ^ 3 := pow_le_pow_left₀ (n := 3) (by positivity) hqb
      rw [show (2 * (q : ℝ)) ^ 3 = 8 * (q : ℝ) ^ 3 by ring] at hp
      exact hp
    have hstep1 : (n : ℝ) * (q : ℝ) / 24 ≤ (3 * (q + 1 : ℝ) ^ 3) * (q : ℝ) / 24 := by
      nlinarith [hnℝ, hq0]
    have hstep2 : (3 * (q + 1 : ℝ) ^ 3) * (q : ℝ) / 24 ≤ (q : ℝ) ^ 4 := by
      nlinarith [hcub, hq0]
    calc
      (n : ℝ) * ((q : ℝ) / 24) = (n : ℝ) * (q : ℝ) / 24 := by ring
      _ ≤ (3 * (q + 1 : ℝ) ^ 3) * (q : ℝ) / 24 := hstep1
      _ ≤ (q : ℝ) ^ 4 := hstep2

-- ===== 补点构造：conePt 族 p_k = normPt (1+k) 0 (2+k) =====
-- 第二坐标恒 0 → 与 lineW（第二坐标 -1/√T < 0）天然不交
-- 与 pointM（(c,m,1) 归一化）的碰撞论证下一步做
-- 本轮：比例引理 + k 单射 + 单位球面 + 集合基数

-- 比例恢复：normPt x 0 z = normPt x' 0 z'（x,z,x',z' 均非零）→ x/z = x'/z'
lemma extraPt_ratio (x z x' z' : ℝ) (hx : x ≠ 0) (hz : z ≠ 0) (hx' : x' ≠ 0) (hz' : z' ≠ 0)
    (h : normPt x 0 z = normPt x' 0 z') : x / z = x' / z' := by
  have h0 := congrArg (fun p : E3 => p 0) h
  have h2 := congrArg (fun p : E3 => p 2) h
  rw [normPt, normPt] at h0 h2
  simp at h0 h2
  have hs : 0 < x ^ 2 + z ^ 2 := by nlinarith [sq_pos_of_ne_zero hx]
  have hs' : 0 < x' ^ 2 + z' ^ 2 := by nlinarith [sq_pos_of_ne_zero hx']
  have hsq : Real.sqrt (x ^ 2 + z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hsq' : Real.sqrt (x' ^ 2 + z' ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs')
  calc
    x / z = (x / Real.sqrt (x ^ 2 + z ^ 2)) / (z / Real.sqrt (x ^ 2 + z ^ 2)) := by
      field_simp [hz, hsq]
    _ = (x' / Real.sqrt (x' ^ 2 + z' ^ 2)) / (z' / Real.sqrt (x' ^ 2 + z' ^ 2)) := by
      rw [h0, h2]
    _ = x' / z' := by
      field_simp [hz', hsq']

-- conePt 参数单射：k ↦ p_k
lemma extraPt_inj_coord (k k' : ℕ)
    (h : normPt (1 + (k : ℝ)) 0 (2 + (k : ℝ)) = normPt (1 + (k' : ℝ)) 0 (2 + (k' : ℝ))) :
    k = k' := by
  have hq := extraPt_ratio (1 + (k : ℝ)) (2 + (k : ℝ)) (1 + (k' : ℝ)) (2 + (k' : ℝ))
    (by positivity) (by positivity) (by positivity) (by positivity) h
  have hb : (2 + (k : ℝ)) ≠ 0 := by positivity
  have hb' : (2 + (k' : ℝ)) ≠ 0 := by positivity
  have hcross : (1 + (k : ℝ)) * (2 + (k' : ℝ)) = (1 + (k' : ℝ)) * (2 + (k : ℝ)) :=
    (div_eq_div_iff hb hb').1 hq
  have hk : (k : ℝ) = (k' : ℝ) := by nlinarith
  exact_mod_cast hk

-- 补点集：p_k（k < n - 3q³），恰补足到 n
noncomputable def extraPoints (q n : ℕ) : Finset E3 :=
  (Finset.range (n - 3 * q ^ 3)).image (fun k : ℕ => normPt (1 + (k : ℝ)) 0 (2 + (k : ℝ)))

lemma extraPoints_inj :
    Function.Injective (fun k : ℕ => normPt (1 + (k : ℝ)) 0 (2 + (k : ℝ))) := by
  intro k k' h
  exact extraPt_inj_coord k k' h

-- 补点在单位球面
lemma extraPoints_sphere (k : ℕ) : dist (normPt (1 + (k : ℝ)) 0 (2 + (k : ℝ))) 0 = 1 := by
  apply normPt_sphere
  positivity

-- 补点集基数 = n - 3q³
lemma extraPoints_card (q n : ℕ) (_hq : 3 * q ^ 3 ≤ n) : (extraPoints q n).card = n - 3 * q ^ 3 := by
  rw [extraPoints]
  rw [Finset.card_image_of_injective]
  · simp
  · exact extraPoints_inj

-- ===== 补点与 B2 不交 =====
-- p_k 第二坐标恒 0；lineW 第二坐标 -1/√T < 0 → 不交
lemma extraPt_ne_lineW (k : ℕ) (a b : ℝ) :
    normPt (1 + (k : ℝ)) 0 (2 + (k : ℝ)) ≠ lineW a b := by
  intro h
  have h1 := congrArg (fun p : E3 => p 1) h
  rw [lineW] at h1
  rw [normPt, normPt] at h1
  simp at h1
  have hT : 0 < a ^ 2 + 1 + b ^ 2 := by positivity
  have hpos : 0 < 1 / Real.sqrt (a ^ 2 + 1 + b ^ 2) := by positivity
  have hneg : ((-1) / Real.sqrt (a ^ 2 + 1 + b ^ 2) : ℝ) < 0 := by
    rw [neg_div]
    nlinarith
  rw [← h1] at hneg
  exact (lt_irrefl 0) hneg

-- p_k 与 pointM c m 不交（c,m 为自然数取值，第二坐标 0 + 比值恢复）
lemma extraPt_ne_pointM (k : ℕ) (cM mN : ℕ) :
    normPt (1 + (k : ℝ)) 0 (2 + (k : ℝ)) ≠ pointM (cM : ℝ) (mN : ℝ) := by
  intro h
  have h0 := congrArg (fun p : E3 => p 0) h
  have h2 := congrArg (fun p : E3 => p 2) h
  rw [pointM, normPt, normPt] at h0 h2
  simp at h0 h2
  have hA : 0 < (1 + (k : ℝ)) ^ 2 + (2 + (k : ℝ)) ^ 2 := by positivity
  have hB : 0 < (cM : ℝ) ^ 2 + (mN : ℝ) ^ 2 + 1 := by positivity
  have hAn : Real.sqrt ((1 + (k : ℝ)) ^ 2 + (2 + (k : ℝ)) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hA)
  have hBn : Real.sqrt ((cM : ℝ) ^ 2 + (mN : ℝ) ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hB)
  have h2' : (2 + (k : ℝ)) * Real.sqrt ((cM : ℝ) ^ 2 + (mN : ℝ) ^ 2 + 1)
      = Real.sqrt ((1 + (k : ℝ)) ^ 2 + (2 + (k : ℝ)) ^ 2) := by
    field_simp [hAn, hBn] at h2
    simpa using h2
  have h0' : (1 + (k : ℝ)) * Real.sqrt ((cM : ℝ) ^ 2 + (mN : ℝ) ^ 2 + 1)
      = (cM : ℝ) * Real.sqrt ((1 + (k : ℝ)) ^ 2 + (2 + (k : ℝ)) ^ 2) := by
    field_simp [hAn, hBn] at h0
    nlinarith
  have haz : (1 + (k : ℝ)) * Real.sqrt ((cM : ℝ) ^ 2 + (mN : ℝ) ^ 2 + 1)
      = (cM : ℝ) * ((2 + (k : ℝ)) * Real.sqrt ((cM : ℝ) ^ 2 + (mN : ℝ) ^ 2 + 1)) := by
    rw [← h2'] at h0'
    exact h0'
  have hmain : (1 + (k : ℝ)) = (cM : ℝ) * (2 + (k : ℝ)) := by
    field_simp [hBn] at haz
    nlinarith
  rcases Nat.eq_zero_or_pos cM with hc0 | hcp
  · subst cM
    have hmain' : (1 + (k : ℝ)) = 0 := by
      simpa using hmain
    have hpos : 0 < 1 + (k : ℝ) := by positivity
    nlinarith
  · have hcp' : (1 : ℝ) ≤ (cM : ℝ) := by exact_mod_cast hcp
    have hk2 : 0 < 2 + (k : ℝ) := by positivity
    nlinarith

-- ===== unorderedUnitPairsAtSqrt2 单调性 =====
lemma unorderedUnitPairsAtSqrt2_mono {s t : Finset E3} (h : s ⊆ t) :
    unorderedUnitPairsAtSqrt2 s ≤ unorderedUnitPairsAtSqrt2 t := by
  rw [unorderedUnitPairsAtSqrt2]
  apply Nat.div_le_div_right
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxprod, hxP⟩
  constructor
  · rcases (Finset.mem_product.mp hxprod) with ⟨hx1, hx2⟩
    exact Finset.mem_product.mpr ⟨h hx1, h hx2⟩
  · exact hxP

-- ===== 补点与 B2 不交 =====
lemma extraPoints_disj_pointSet2 (q n : ℕ) : Disjoint (extraPoints q n) (pointSet2 q) := by
  rw [Finset.disjoint_left]
  intro x hx
  rw [extraPoints, Finset.mem_image] at hx
  rcases hx with ⟨k, hk, rfl⟩
  rw [pointSet2, Finset.mem_image]
  rintro ⟨t, ht, hxy⟩
  exact extraPt_ne_pointM k t.1 t.2 hxy.symm

lemma extraPoints_disj_lineSet2 (q n : ℕ) : Disjoint (extraPoints q n) (lineSet2 q) := by
  rw [Finset.disjoint_left]
  intro x hx
  rw [extraPoints, Finset.mem_image] at hx
  rcases hx with ⟨k, hk, rfl⟩
  rw [lineSet2, Finset.mem_image]
  rintro ⟨t, ht, hxy⟩
  exact extraPt_ne_lineW k ((t.1 : ℕ) : ℝ) ((t.2 : ℕ) : ℝ) hxy.symm

lemma extraPoints_disj_B2 (q n : ℕ) : Disjoint (extraPoints q n) (B2 q) := by
  rw [B2]
  rw [Finset.disjoint_union_right]
  constructor
  · exact extraPoints_disj_pointSet2 q n
  · exact extraPoints_disj_lineSet2 q n

-- ===== 全集：B2 (scale3 n) ∪ 补点，card = n =====
noncomputable def full (n : ℕ) : Finset E3 :=
  B2 (scale3 n) ∪ extraPoints (scale3 n) n

lemma full_card (n : ℕ) : (full n).card = n := by
  rw [full]
  let q := scale3 n
  have hq : 3 * q ^ 3 ≤ n := by
    simpa [q] using scale3_spec n
  have hdisj : Disjoint (B2 q) (extraPoints q n) := (extraPoints_disj_B2 q n).symm
  rw [Finset.card_union_of_disjoint hdisj]
  rw [B2_card, extraPoints_card q n hq]
  omega

-- full 全在单位球面
lemma full_sphere (n : ℕ) : ∀ p ∈ full n, p ∈ sphere 0 1 := by
  intro p hp
  rw [full, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact B2_unit (scale3 n) p hp
  · rw [extraPoints, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    exact extraPoints_sphere k

-- ===== 主定理收口 =====
-- full 中 √2 无序对数 ≥ q⁴（单调性 + B2_ge）
lemma full_sqrt2_ge (n : ℕ) : (scale3 n) ^ 4 ≤ unorderedUnitPairsAtSqrt2 (full n) := by
  let q := scale3 n
  have hsub : B2 q ⊆ full n := by
    intro x hx
    rw [full]
    exact Finset.mem_union_left (extraPoints q n) hx
  have hmono : unorderedUnitPairsAtSqrt2 (B2 q) ≤ unorderedUnitPairsAtSqrt2 (full n) :=
    unorderedUnitPairsAtSqrt2_mono hsub
  have hb : q ^ 4 ≤ unorderedUnitPairsAtSqrt2 (B2 q) := unorderedUnitPairsAtSqrt2_B2_ge q
  exact le_trans hb hmono

-- 主引理：n·f(n) ≤ unorderedUnitPairsAtSqrt2 (full n)
lemma jsp492_main (n : ℕ) : (n : ℝ) * f492q n ≤ (unorderedUnitPairsAtSqrt2 (full n) : ℝ) := by
  have hnf : (n : ℝ) * f492q n ≤ (scale3 n : ℝ) ^ 4 := n_mul_f492q_le n
  calc
    (n : ℝ) * f492q n ≤ (scale3 n : ℝ) ^ 4 := hnf
    _ = (((scale3 n) ^ 4 : ℕ) : ℝ) := by norm_cast
    _ ≤ (unorderedUnitPairsAtSqrt2 (full n) : ℝ) := by
      exact_mod_cast full_sqrt2_ge n

-- 官方定理存在性包装
lemma jsp492_exists (n : ℕ) :
    ∃ S : Finset E3, S.card = n ∧ (∀ p ∈ S, p ∈ sphere 0 1) ∧
      (n : ℝ) * f492q n ≤ (unorderedUnitPairsAtSqrt2 S : ℝ) := by
  refine ⟨full n, full_card n, full_sphere n, jsp492_main n⟩


-- 分析引理：c·√(log n) ≤ f492q n = scale3 n / 24，对 n ≥ 3
lemma swanepoel_analysis (n : ℕ) (hn : 3 ≤ n) :
    (1 / (72 * Real.sqrt 3) : ℝ) * Real.sqrt (Real.log (n : ℝ)) ≤ f492q n := by
  unfold f492q
  have hlog : Real.log (n : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / (1 / 3 : ℝ) :=
        Real.log_le_rpow_div (by positivity : 0 ≤ (n : ℝ)) (by norm_num : 0 < (1 / 3 : ℝ))
      _ = 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
        norm_num
        ring
  have hsqrt_lt : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (3 * (n : ℝ) ^ (1 / 3 : ℝ)) :=
    Real.sqrt_le_sqrt hlog
  have hpow : Real.sqrt ((3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)) = Real.sqrt 3 * (n : ℝ) ^ (1 / 6 : ℝ) := by
    have hsr : Real.sqrt ((n : ℝ) ^ (1 / 3 : ℝ)) = (n : ℝ) ^ (1 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)) (1 / 3 : ℝ) (1 / 2 : ℝ)]
      norm_num
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (3 : ℝ)) ((n : ℝ) ^ (1 / 3))]
    rw [hsr]
  have hn16 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ n)
    exact Real.rpow_le_rpow_of_exponent_le hn1r (by norm_num : (1 / 6 : ℝ) ≤ (1 / 3 : ℝ))
  have hn_le_cube : n ≤ 27 * (scale3 n) ^ 3 := by
    let q := scale3 n
    by_contra hnot
    have hgt : 27 * q ^ 3 < n := by dsimp [q]; exact lt_of_not_ge hnot
    have hq1 : 1 ≤ q := scale3_max n (by simpa using hn)
    have hq1r : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have h21 : (q + 1 : ℝ) ≤ 2 * (q : ℝ) := by nlinarith
    have hcub : (q + 1 : ℝ) ^ 3 ≤ (2 * (q : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (n := 3) (by positivity) h21
    have hcub' : (2 * (q : ℝ)) ^ 3 = 8 * (q : ℝ) ^ 3 := by ring
    have hmainR : 3 * (q + 1 : ℝ) ^ 3 < 27 * (q : ℝ) ^ 3 := by
      nlinarith [hcub']
    have hgtR : 27 * (q : ℝ) ^ 3 < (n : ℝ) := by exact_mod_cast hgt
    have hstep : 3 * (q + 1) ^ 3 < n := by
      exact_mod_cast (lt_trans hmainR hgtR)
    have hmax : q + 1 ≤ scale3 n := scale3_max n (le_of_lt hstep)
    omega
  have hn13 : (n : ℝ) ^ (1 / 3 : ℝ) ≤ 3 * (scale3 n : ℝ) := by
    have hcubeR : (n : ℝ) ≤ 27 * (scale3 n : ℝ) ^ 3 := by exact_mod_cast hn_le_cube
    have hrc := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ)) hcubeR
      (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hce : (27 * (scale3 n : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 3 * (scale3 n : ℝ) := by
      rw [show 27 * (scale3 n : ℝ) ^ 3 = (3 * (scale3 n : ℝ)) ^ 3 by ring]
      rw [← Real.rpow_natCast (3 * (scale3 n : ℝ)) 3]
      calc
        ((3 * (scale3 n : ℝ)) ^ (↑3 : ℝ)) ^ (1 / 3 : ℝ)
            = (3 * (scale3 n : ℝ)) ^ ((↑3 : ℝ) * (1 / 3 : ℝ)) := by
                exact (Real.rpow_mul (by positivity : 0 ≤ 3 * (scale3 n : ℝ)) (↑3 : ℝ) (1 / 3 : ℝ)).symm
        _ = 3 * (scale3 n : ℝ) := by
                norm_num [Real.rpow_one]
    calc
      (n : ℝ) ^ (1 / 3 : ℝ) ≤ (27 * (scale3 n : ℝ) ^ 3) ^ (1 / 3 : ℝ) := hrc
      _ = 3 * (scale3 n : ℝ) := hce
  have hbound : Real.sqrt (Real.log (n : ℝ)) ≤ 3 * Real.sqrt 3 * (scale3 n : ℝ) := by
    calc
      Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (3 * (n : ℝ) ^ (1 / 3 : ℝ)) := hsqrt_lt
      _ = Real.sqrt 3 * (n : ℝ) ^ (1 / 6 : ℝ) := hpow
      _ ≤ Real.sqrt 3 * (n : ℝ) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hn16 (by positivity : 0 ≤ Real.sqrt 3)
      _ ≤ Real.sqrt 3 * (3 * (scale3 n : ℝ)) :=
        mul_le_mul_of_nonneg_left hn13 (by positivity : 0 ≤ Real.sqrt 3)
      _ = 3 * Real.sqrt 3 * (scale3 n : ℝ) := by ring
  calc
    (1 / (72 * Real.sqrt 3) : ℝ) * Real.sqrt (Real.log (n : ℝ))
        ≤ (1 / (72 * Real.sqrt 3) : ℝ) * (3 * Real.sqrt 3 * (scale3 n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (scale3 n : ℝ) / 24 := by
          field_simp [ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3))]
          ring



/-! ## Official JSP-000492 corollary

There exists `f : ℕ → ℝ` with `f → ∞` such that for every `n ≥ 2` there are `n`
distinct points on the unit sphere with at least `n·f(n)` unordered pairs at distance
`√2`.
-/

def f492 (n : ℕ) : ℝ :=
  (1 / 10 : ℝ) * Real.sqrt (Real.log (n : ℝ))


/-- The official function `f492 n = (1/10)·√log n` tends to infinity. -/
lemma f492_tendsto : Tendsto f492 atTop atTop := by
  unfold f492
  exact Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (1 / 10 : ℝ))
    ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop)
theorem jsp492_official :
    ∃ f : ℕ → ℝ,
      Tendsto f atTop atTop ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ B : Finset E3,
          B.card = n ∧
          (∀ p ∈ B, p ∈ sphere 0 1) ∧
          ((n : ℝ) * f n ≤ (unorderedUnitPairsAtSqrt2 B : ℝ)) := by
  refine ⟨f492q, ?_, ?_⟩
  · change Tendsto (fun n : ℕ => (scale3 n : ℝ) / 24) atTop atTop
    exact f492q_tendsto
  · intro n hn
    exact jsp492_exists n

/-! ## Gate 4a: the angle function β and the complex-plane bridge

A point of the unit circle is identified with the complex number `z.re + z.im * I`.
Rotating the plane around the z-axis by angle `θ` corresponds to multiplying `z`
by `exp (θ·I)`.  The function `β z := arccos z.re` gives a single-valued,
continuous angle on the strip `|z.re| < 1` (mathlib has no `atan2`/`angle`;
`arccos` is the documented replacement).
-/

/-- The angle function: `z ↦ arccos(z.re)`. -/
def β (z : ℂ) : ℝ := Real.arccos z.re

/-- `β` is continuous on all of `ℂ` (composite of two continuous maps). -/
lemma β_continuous : Continuous β := by
  unfold β
  exact Real.continuous_arccos.comp Complex.continuous_re

/-- On the strip `-1 < z.re < 1`, `β` is a genuine inverse of `cos`. -/
lemma cos_beta (z : ℂ) (hz : z.re ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.cos (β z) = z.re := by
  unfold β
  exact Real.cos_arccos hz.1.le hz.2.le

/-- Embed the xy-plane of `E3` into `ℂ` (a linear isometry on the plane). -/
def toComplex (p : E3) : ℂ := (p 0 : ℝ) + (p 1 : ℝ) * Complex.I

/-- Real part of `toComplex p` is the first coordinate. -/
lemma toComplex_re (p : E3) : (toComplex p).re = p 0 := by
  simp [toComplex]

/-- Imaginary part of `toComplex p` is the second coordinate. -/
lemma toComplex_im (p : E3) : (toComplex p).im = p 1 := by
  simp [toComplex]

/-- `rotateZ θ` on the plane is multiplication by `exp (θ·I)` on `ℂ`. -/
lemma rotateZ_toComplex (θ : ℝ) (p : E3) :
    toComplex (rotateZ θ p) = Complex.exp (θ * Complex.I) * toComplex p := by
  apply Complex.ext <;> simp [rotateZ_coord0, rotateZ_coord1, toComplex, Complex.exp_mul_I,
    Complex.mul_re, Complex.mul_im] <;> ring

/-- On the unit circle, `β (toComplex p)` is the unique angle in `[0,π]`
whose cosine is the x-coordinate of `p`. -/
lemma beta_of_unit (p : E3) (hx : (toComplex p).re ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.cos (β (toComplex p)) = (toComplex p).re := by
  exact cos_beta (toComplex p) hx

/-! ## Gate 4b: rotation faithfulness

`rotateZ` is a group action of `(ℝ, +)` on the plane.  Through the complex bridge,
two rotations that agree at a non-zero equator point are the same rotation of the
plane, and the unit complex numbers `exp (θ·I)` agree iff `(cos θ, sin θ)` agree.
-/

/-- The rotations form a group action: `rotateZ (α + β) = rotateZ α ∘ rotateZ β`. -/
lemma rotateZ_add (α β : ℝ) (p : E3) : rotateZ (α + β) p = rotateZ α (rotateZ β p) := by
  ext i
  fin_cases i <;> simp [rotateZ, Real.cos_add, Real.sin_add] <;> ring

/-- Rotation by zero is the identity. -/
lemma rotateZ_zero (p : E3) : rotateZ 0 p = p := by
  ext i
  fin_cases i <;> simp [rotateZ]

/-- Rotation by `-θ` inverts rotation by `θ`. -/
lemma rotateZ_neg (θ : ℝ) (p : E3) : rotateZ (-θ) (rotateZ θ p) = p := by
  rw [← rotateZ_add (-θ) θ p]
  simp [rotateZ_zero]

/-- `rotateZ θ` is injective (a permutation of the equator). -/
lemma rotateZ_injective (θ : ℝ) : Function.Injective (rotateZ θ) := by
  intro p q h
  have := congrArg (rotateZ (-θ)) h
  simpa [rotateZ_neg] using this

/-- Faithfulness via the complex bridge: if two rotations agree at a non-zero
point of the equator, the corresponding unit complex numbers agree. -/
lemma rotateZ_eq_rotateZ_of_exp {θ₁ θ₂ : ℝ} {a : E3} (ha : toComplex a ≠ 0)
    (h : rotateZ θ₁ a = rotateZ θ₂ a) :
    Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) := by
  have h₁ : toComplex (rotateZ θ₁ a) = Complex.exp (θ₁ * Complex.I) * toComplex a :=
    rotateZ_toComplex θ₁ a
  have h₂ : toComplex (rotateZ θ₂ a) = Complex.exp (θ₂ * Complex.I) * toComplex a :=
    rotateZ_toComplex θ₂ a
  have heq : Complex.exp (θ₁ * Complex.I) * toComplex a =
      Complex.exp (θ₂ * Complex.I) * toComplex a := by
    rw [← h₁, ← h₂, h]
  exact mul_right_cancel₀ ha heq

/-- Real part of `exp (θ·I)`. -/
lemma exp_mul_I_re (θ : ℝ) : (Complex.exp (θ * Complex.I)).re = Real.cos θ := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ]
  rw [Complex.add_re, Complex.mul_I_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Imaginary part of `exp (θ·I)`. -/
lemma exp_mul_I_im (θ : ℝ) : (Complex.exp (θ * Complex.I)).im = Real.sin θ := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ]
  rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- Equality of the unit complex numbers `exp (θ·I)` is equality of `(cos θ, sin θ)`. -/
lemma exp_mul_I_eq_iff (θ₁ θ₂ : ℝ) :
    Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) ↔
      Real.cos θ₁ = Real.cos θ₂ ∧ Real.sin θ₁ = Real.sin θ₂ := by
  constructor
  · intro h
    constructor
    · have hre := congrArg Complex.re h
      rwa [exp_mul_I_re θ₁, exp_mul_I_re θ₂] at hre
    · have him := congrArg Complex.im h
      rwa [exp_mul_I_im θ₁, exp_mul_I_im θ₂] at him
  · intro ⟨hc, hs⟩
    apply Complex.ext
    · rw [exp_mul_I_re θ₁, exp_mul_I_re θ₂, hc]
    · rw [exp_mul_I_im θ₁, exp_mul_I_im θ₂, hs]

/-! ## Gate 4c: perturbation claim (in progress)

Base step: `rotateZ` is `2π`-periodic, so the rotation angle matters only modulo
`2π`.  This is the bridge from distinct angles to distinct rotations.
-/

/-- `rotateZ` is `2π`-periodic in the angle. -/
lemma rotateZ_periodic (θ : ℝ) (p : E3) : rotateZ (θ + 2 * Real.pi) p = rotateZ θ p := by
  ext i
  fin_cases i <;> simp [rotateZ, Real.cos_add, Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]

/-- A rotation fixes a non-zero equator point iff the angle is an integer
multiple of `2π`.  This is the core perturbation step: distinct angles
(mod `2π`) give disjoint rotated copies of an equator set. -/
lemma rotateZ_fixed_iff_two_pi {δ : ℝ} {a : E3} (ha : toComplex a ≠ 0) :
    rotateZ δ a = a ↔ ∃ k : ℤ, δ = k * (2 * Real.pi) := by
  constructor
  · intro h
    have h₀ : rotateZ δ a = rotateZ 0 a := by simpa [rotateZ_zero] using h
    have he : Complex.exp (δ * Complex.I) = 1 := by
      have he' := rotateZ_eq_rotateZ_of_exp ha h₀
      simpa using he'
    have hcs : Real.cos δ = 1 ∧ Real.sin δ = 0 := by
      have he' : Complex.exp (δ * Complex.I) = Complex.exp (0 * Complex.I) := by
        simpa using he
      have hm := (exp_mul_I_eq_iff δ 0).mp he'
      simpa using hm
    rcases (Real.cos_eq_one_iff δ).mp hcs.1 with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  · intro ⟨k, hk⟩
    rw [hk]
    have hper : Function.Periodic (fun θ : ℝ => rotateZ θ a) (2 * Real.pi) := by
      intro θ
      exact rotateZ_periodic θ a
    have hperk : Function.Periodic (fun θ : ℝ => rotateZ θ a) (↑k * (2 * Real.pi)) :=
      hper.int_mul k
    have hpeq : rotateZ (↑k * (2 * Real.pi)) a = rotateZ 0 a := hperk.eq
    rw [hpeq]
    simp [rotateZ_zero]

/-- Two rotated copies of an equator set `A` are disjoint provided the angle
difference avoids both `2πℤ` (no fixed point) and the internal angle
differences of `A` (no `A`-to-`A` shift). -/
lemma rotateZ_disjoint_of_avoid {θ₁ θ₂ : ℝ} {A : Finset E3}
    (hA : ∀ a ∈ A, toComplex a ≠ 0)
    (hδ : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → rotateZ (θ₁ - θ₂) a₁ ≠ a₂)
    (hδ0 : ∀ k : ℤ, θ₁ - θ₂ ≠ k * (2 * Real.pi)) :
    Disjoint (A.image fun a => rotateZ θ₁ a) (A.image fun a => rotateZ θ₂ a) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases (Finset.mem_image.mp hx1) with ⟨a₁, ha₁, rfl⟩
  rcases (Finset.mem_image.mp hx2) with ⟨a₂, ha₂, hx⟩
  by_cases h12 : a₁ = a₂
  · subst a₂
    have hfix : rotateZ (θ₁ - θ₂) a₁ = a₁ := by
      have hx' := congrArg (rotateZ (-θ₂)) hx
      rw [rotateZ_neg] at hx'
      rw [← rotateZ_add (-θ₂) θ₁ a₁] at hx'
      rw [show (-θ₂) + θ₁ = θ₁ - θ₂ by ring] at hx'
      exact hx'.symm
    rcases (rotateZ_fixed_iff_two_pi (hA a₁ ha₁)).mp hfix with ⟨k, hk⟩
    exact (hδ0 k) hk
  · have hmain : rotateZ (θ₁ - θ₂) a₁ = a₂ := by
      have hx' := congrArg (rotateZ (-θ₂)) hx
      rw [rotateZ_neg] at hx'
      rw [← rotateZ_add (-θ₂) θ₁ a₁] at hx'
      rw [show (-θ₂) + θ₁ = θ₁ - θ₂ by ring] at hx'
      exact hx'.symm
    exact (hδ a₁ ha₁ a₂ ha₂ h12) hmain

/-! ### Gate 4c (cont.): Claim 1 — 泛型 A 的存在性

`rotateZ_disjoint_of_avoid` 给出两副本不相交的判据。Claim 1（微扰）将其推广到
全族：若角度映射 `S ↦ ω S` 避开所有不动点角（`2πℤ`）与 `A` 的内部角差，
则 `2^(t^2)` 个旋转副本两两不相交；存在性部分（`exists_generic_A`）暂以
`sorry` 占位，策略注释见下。 -/

/-- 条件化全族不相交：若角度差避开 `2πℤ` 与 `A` 的内部角差，则各旋转副本两两不相交。 -/
lemma copies_disjoint_of_angle_avoid {t : ℕ} {A : Finset E3}
    {ω : Finset (Fin t × Fin t) → ℝ}
    (hA : ∀ a ∈ A, toComplex a ≠ 0)
    (havoid : ∀ S₁ S₂ : Finset (Fin t × Fin t), S₁ ≠ S₂ →
      (∀ k : ℤ, ω S₁ - ω S₂ ≠ k * (2 * Real.pi)) ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → rotateZ (ω S₁ - ω S₂) a₁ ≠ a₂)) :
    ∀ S₁ S₂ : Finset (Fin t × Fin t), S₁ ≠ S₂ →
      Disjoint (A.image fun a => rotateZ (ω S₁) a) (A.image fun a => rotateZ (ω S₂) a) := by
  intro S₁ S₂ hS
  exact rotateZ_disjoint_of_avoid hA (havoid S₁ S₂ hS).2 (havoid S₁ S₂ hS).1

/- Claim 1（微扰，SwVa04）：对每个 `t`，存在赤道集 `A`（`|A| = t`）与角度赋值
`ω : S ↦ 旋转角`（`S ⊆ A × A`，共 `2^(t^2)` 个），使所有副本两两不相交。

证明策略（泛型论证，暂 `sorry` 占位）：
1. 从赤道等距点 `A₀ = {(cos(kλ), sin(kλ), 0) | k < t}`、`λ = π/(t·N)`（N 充分大）出发；
2. 每个禁戒等式（`ω S₁ = ω S₂` mod `2πℤ`，或副本内碰撞 `rotateZ δ a₁ = a₂`）
   在参数空间中割出闭的零测（有限维代数簇）子集；
3. `β_continuous` + arccos 分支给出连续性，故可在余集中取点，得到所需 `A` 与 `ω`。 -/
/-- Point in the xy-plane (z = 0) with coordinates (x, y). -/
def planePoint (x y : ℝ) : E3 :=
  WithLp.toLp (p := 2) (ofLp := fun i : Fin 3 =>
    match i with
    | ⟨0, _⟩ => x
    | ⟨1, _⟩ => y
    | ⟨2, _⟩ => 0)

lemma planePoint_coord0 (x y : ℝ) : (planePoint x y) 0 = x := rfl
lemma planePoint_coord1 (x y : ℝ) : (planePoint x y) 1 = y := rfl
lemma planePoint_coord2 (x y : ℝ) : (planePoint x y) 2 = 0 := rfl

lemma toComplex_planePoint (x y : ℝ) :
    toComplex (planePoint x y) = (x : ℂ) + (y : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [toComplex, planePoint_coord0, planePoint_coord1]

/-- A point of the unit circle is not the origin in the complex plane. -/
lemma toComplex_planePoint_ne_zero_of_unit (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    toComplex (planePoint x y) ≠ 0 := by
  intro hz
  have hn : Complex.normSq (toComplex (planePoint x y)) = 1 := by
    rw [toComplex_planePoint, Complex.normSq_apply]
    simpa [sq] using h
  have hn0 : Complex.normSq (toComplex (planePoint x y)) = 0 := by
    rw [hz, Complex.normSq_zero]
  linarith

/-- Angular step between consecutive points of the equator set: `π / (t + 1)`. -/
def equatorStep (t : ℕ) : ℝ := Real.pi / (t + 1)

lemma equatorStep_pos (t : ℕ) : 0 < equatorStep t := by
  unfold equatorStep
  exact div_pos Real.pi_pos (by positivity)

/-- For `k < t` the angle `k · step` is `< π`. -/
lemma step_mul_lt_pi (t : ℕ) {k : ℕ} (hk : k < t) : k * equatorStep t < Real.pi := by
  unfold equatorStep
  have hk' : (k : ℝ) < (t + 1 : ℝ) := by
    exact_mod_cast (by omega : k < t + 1)
  rw [← mul_div_assoc]
  rw [div_lt_iff₀ (by positivity : 0 < (t + 1 : ℝ))]
  nlinarith [Real.pi_pos, mul_lt_mul_of_pos_right hk' Real.pi_pos]

/-- The angular step is at most `π`. -/
lemma equatorStep_le_pi (t : ℕ) : equatorStep t ≤ Real.pi := by
  unfold equatorStep
  have hle : (1 : ℝ) ≤ (t + 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ t + 1)
  rw [div_le_iff₀ (by positivity : 0 < (t + 1 : ℝ))]
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hle (le_of_lt Real.pi_pos)]

/-- `(t-1) · step < π` for `t ≥ 1`. -/
lemma step_mul_minus_one_lt_pi (t : ℕ) (ht : 1 ≤ t) : (t - 1 : ℕ) * equatorStep t < Real.pi := by
  unfold equatorStep
  have hk' : ((t - 1 : ℕ) : ℝ) < (t + 1 : ℝ) := by
    exact_mod_cast (by omega : t - 1 < t + 1)
  rw [← mul_div_assoc]
  rw [div_lt_iff₀ (by positivity : 0 < (t + 1 : ℝ))]
  nlinarith [Real.pi_pos, mul_lt_mul_of_pos_right hk' Real.pi_pos]

/-- The step for `ω`-values: a quarter of the equator step. -/
def omegaStep (t : ℕ) : ℝ := equatorStep t / 4

lemma omegaStep_pos (t : ℕ) : 0 < omegaStep t := by
  unfold omegaStep
  exact div_pos (equatorStep_pos t) (by norm_num)

/-- `ε = step/4 ≤ π/4`. -/
lemma omegaStep_le_pi_div_four (t : ℕ) : omegaStep t ≤ Real.pi / 4 := by
  unfold omegaStep equatorStep
  rw [div_div]
  have hle : (1 : ℝ) ≤ (t + 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ t + 1)
  exact div_le_div₀ (le_of_lt Real.pi_pos) (le_rfl) (by norm_num)
    (by nlinarith [hle])

/-- `ε < step`, so the ω-interval is inside the equator-step scale. -/
lemma omegaStep_lt_step (t : ℕ) : omegaStep t < equatorStep t := by
  unfold omegaStep
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
  nlinarith [equatorStep_pos t]

/-- `rotateZ θ (1,0,0) = (cos θ, sin θ, 0)`. -/
lemma rotateZ_planePoint_one (θ : ℝ) :
    rotateZ θ (planePoint 1 0) = planePoint (Real.cos θ) (Real.sin θ) := by
  ext i
  fin_cases i <;> simp [rotateZ, planePoint]

/-- The base point `(1,0,0)` has non-zero complex image. -/
lemma toComplex_one_ne_zero : toComplex (planePoint 1 0) ≠ 0 := by
  exact toComplex_planePoint_ne_zero_of_unit 1 0 (by norm_num)

/-- If `-2π < γ < 0`, then `γ` is not an integer multiple of `2π`. -/
lemma not_int_mul_two_pi_of_neg (γ : ℝ) (hneg : γ < 0) (hgt : -2 * Real.pi < γ) :
    ∀ m : ℤ, γ ≠ m * (2 * Real.pi) := by
  intro m hm
  rcases lt_or_ge m 0 with hm0 | hmge0
  · have hmle : m ≤ -1 := by omega
    have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast hmle
    have hmul : (m : ℝ) * (2 * Real.pi) ≤ -2 * Real.pi := by
      calc
        (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm' (le_of_lt (by positivity : 0 < 2 * Real.pi))
        _ = -2 * Real.pi := by ring
    linarith
  · have hmul : 0 ≤ (m : ℝ) * (2 * Real.pi) :=
      mul_nonneg (by exact_mod_cast hmge0) (le_of_lt (by positivity : 0 < 2 * Real.pi))
    linarith

/-- If `0 < γ < 2π`, then `γ` is not an integer multiple of `2π`. -/
lemma not_int_mul_two_pi_of_pos (γ : ℝ) (hpos : 0 < γ) (hlt : γ < 2 * Real.pi) :
    ∀ m : ℤ, γ ≠ m * (2 * Real.pi) := by
  intro m hm
  rcases lt_or_ge m 1 with hm1 | hmge1
  · have hmle : m ≤ 0 := by omega
    have hm' : (m : ℝ) ≤ 0 := by exact_mod_cast hmle
    have hmul : (m : ℝ) * (2 * Real.pi) ≤ 0 := by
      calc
        (m : ℝ) * (2 * Real.pi) ≤ 0 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm' (le_of_lt (by positivity : 0 < 2 * Real.pi))
        _ = 0 := by ring
    linarith
  · have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge1
    have hmul : 2 * Real.pi ≤ (m : ℝ) * (2 * Real.pi) := by
      calc
        2 * Real.pi = 1 * (2 * Real.pi) := by ring
        _ ≤ (m : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hm' (le_of_lt (by positivity : 0 < 2 * Real.pi))
        _ = (m : ℝ) * (2 * Real.pi) := by ring
    linarith

/-- If `0 < |δ| < 2π`, then `δ` is not an integer multiple of `2π`. -/
lemma ne_int_mul_two_pi_of_abs_lt (δ : ℝ) (hδ0 : δ ≠ 0) (hδ : |δ| < 2 * Real.pi) :
    ∀ k : ℤ, δ ≠ k * (2 * Real.pi) := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    exact hδ0 (by simpa using hk)
  · have hkabs : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have hkabs' : (1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hkabs
    have hmag : 2 * Real.pi ≤ |(k : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      have hm : (1 : ℝ) * (2 * Real.pi) ≤ (|k| : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hkabs' (le_of_lt (by positivity : 0 < 2 * Real.pi))
      simpa [Int.cast_abs] using hm
    have hδle : |δ| = |(k : ℝ) * (2 * Real.pi)| := by rw [hk]
    linarith

/-- Bijection from the finite family of subsets to the counting type `Fin (2^(t·t))`. -/
noncomputable def idx (t : ℕ) : Finset (Fin t × Fin t) ≃ Fin (2 ^ (t * t)) := by
  simpa [Fintype.card_finset, Fintype.card_prod, Fintype.card_fin] using
    (Fintype.equivFin (Finset (Fin t × Fin t)))

/-- Perturbation angles indexed by the subsets: all values are distinct and lie in
`(0, omegaStep t]`. -/
noncomputable def ω (t : ℕ) (S : Finset (Fin t × Fin t)) : ℝ :=
  omegaStep t * (((idx t S).1 : ℝ) + 1) / (2 ^ (t * t) : ℝ)

/-- The angle assignment is injective (distinct subsets get distinct angles). -/
lemma ω_inj (t : ℕ) : Function.Injective (ω t) := by
  intro S₁ S₂ h
  apply (idx t).injective
  apply Fin.ext
  have hstep_ne : omegaStep t ≠ 0 := ne_of_gt (omegaStep_pos t)
  have hM : (2 ^ (t * t) : ℝ) ≠ 0 := by positivity
  have hcore : ((idx t S₁).1 : ℝ) + 1 = ((idx t S₂).1 : ℝ) + 1 := by
    unfold ω at h
    field_simp [hstep_ne, hM] at h
    exact h
  have hval : (idx t S₁).1 = (idx t S₂).1 := by
    have h' : (idx t S₁).1 + 1 = (idx t S₂).1 + 1 := by exact_mod_cast hcore
    omega
  exact hval

/-- Perturbation angles are positive. -/
lemma ω_pos (t : ℕ) (S : Finset (Fin t × Fin t)) : 0 < ω t S := by
  unfold ω
  have hM : 0 < (2 ^ (t * t) : ℝ) := pow_pos (by norm_num : 0 < (2 : ℝ)) _
  exact div_pos (mul_pos (omegaStep_pos t) (by positivity)) hM

/-- Perturbation angles are at most the omega-step. -/
lemma ω_le_step (t : ℕ) (S : Finset (Fin t × Fin t)) : ω t S ≤ omegaStep t := by
  unfold ω
  have hle : ((idx t S).1 : ℝ) + 1 ≤ (2 ^ (t * t) : ℝ) := by
    have hv : (idx t S).1 < 2 ^ (t * t) := (idx t S).2
    have hle' : (idx t S).1 + 1 ≤ 2 ^ (t * t) := by omega
    exact_mod_cast hle'
  have hM : 0 < (2 ^ (t * t) : ℝ) := pow_pos (by norm_num : 0 < (2 : ℝ)) _
  rw [div_le_iff₀ hM]
  exact mul_le_mul_of_nonneg_left hle (le_of_lt (omegaStep_pos t))

/-- Two perturbation angles differ by less than the omega-step. -/
lemma ω_diff_lt_step (t : ℕ) (S₁ S₂ : Finset (Fin t × Fin t)) :
    |ω t S₁ - ω t S₂| < omegaStep t := by
  rw [abs_lt]
  constructor <;> nlinarith [ω_pos t S₁, ω_pos t S₂, ω_le_step t S₁, ω_le_step t S₂]

/-- Distinct subsets get distinct perturbation angles. -/
lemma ω_diff_ne_zero_of_ne (t : ℕ) {S₁ S₂ : Finset (Fin t × Fin t)} (h : S₁ ≠ S₂) :
    ω t S₁ - ω t S₂ ≠ 0 := by
  intro hz
  apply h
  exact ω_inj t (by linarith)

/-- Two rotations of a non-zero equator point agree iff the angle difference is an
integer multiple of `2π`. -/
lemma rotateZ_eq_iff_angle {θ₁ θ₂ : ℝ} {a : E3} (ha : toComplex a ≠ 0) :
    rotateZ θ₁ a = rotateZ θ₂ a ↔ ∃ k : ℤ, θ₁ - θ₂ = k * (2 * Real.pi) := by
  constructor
  · intro h
    have h₀ : rotateZ (θ₁ - θ₂) a = a := by
      have h' := congrArg (rotateZ (-θ₂)) h
      rw [rotateZ_neg] at h'
      rw [← rotateZ_add (-θ₂) θ₁ a] at h'
      rw [show (-θ₂) + θ₁ = θ₁ - θ₂ by ring] at h'
      exact h'
    rcases (rotateZ_fixed_iff_two_pi ha).mp h₀ with ⟨k, hk⟩
    exact ⟨k, hk⟩
  · intro ⟨k, hk⟩
    have h' : rotateZ (θ₁ - θ₂) a = a := (rotateZ_fixed_iff_two_pi ha).mpr ⟨k, hk⟩
    have h'' := congrArg (rotateZ θ₂) h'
    rw [← rotateZ_add θ₂ (θ₁ - θ₂) a] at h''
    rw [show θ₂ + (θ₁ - θ₂) = θ₁ by ring] at h''
    exact h''

/-- The equator map `k ↦ (cos(kλ), sin(kλ), 0)` is injective on `Fin t`. -/
lemma A_inj (t : ℕ) (k₁ k₂ : Fin t)
    (h : planePoint (Real.cos (k₁.1 * equatorStep t)) (Real.sin (k₁.1 * equatorStep t)) =
         planePoint (Real.cos (k₂.1 * equatorStep t)) (Real.sin (k₂.1 * equatorStep t))) :
    k₁ = k₂ := by
  have hx : Real.cos (k₁.1 * equatorStep t) = Real.cos (k₂.1 * equatorStep t) := by
    have hc := congrArg (fun p : E3 => p 0) h
    simpa [planePoint_coord0] using hc
  have h₁' : Real.arccos (Real.cos (k₁.1 * equatorStep t)) = k₁.1 * equatorStep t := by
    refine Real.arccos_cos ?_ ?_
    · exact mul_nonneg (by exact_mod_cast (Nat.zero_le (k₁.1 : ℕ)))
        (le_of_lt (equatorStep_pos t))
    · exact le_of_lt (step_mul_lt_pi t k₁.2)
  have h₂' : Real.arccos (Real.cos (k₂.1 * equatorStep t)) = k₂.1 * equatorStep t := by
    refine Real.arccos_cos ?_ ?_
    · exact mul_nonneg (by exact_mod_cast (Nat.zero_le (k₂.1 : ℕ)))
        (le_of_lt (equatorStep_pos t))
    · exact le_of_lt (step_mul_lt_pi t k₂.2)
  have heq : k₁.1 * equatorStep t = k₂.1 * equatorStep t := by
    rw [← h₁', ← h₂']
    exact congrArg Real.arccos hx
  have hstep_ne : equatorStep t ≠ 0 := ne_of_gt (equatorStep_pos t)
  have hn : (k₁.1 : ℝ) = (k₂.1 : ℝ) := mul_right_cancel₀ hstep_ne heq
  have hnat : k₁.1 = k₂.1 := by exact_mod_cast hn
  exact Fin.ext hnat


/-- Rotation around the z-axis fixes the origin. -/
lemma rotateZ_zero_point (θ : ℝ) : rotateZ θ 0 = 0 := by
  ext i
  fin_cases i <;> simp [rotateZ]

/-- A point of the unit circle with `z = 0` is at distance 1 from the origin. -/
lemma dist_zero_planePoint_unit (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    dist 0 (planePoint x y) = 1 := by
  have hp2 : 0 < (2 : ENNReal).toReal := by norm_num
  calc
    dist 0 (planePoint x y)
        = (∑ i : Fin 3, dist ((0 : E3) i) ((planePoint x y) i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          PiLp.dist_eq_sum hp2 (0 : E3) (planePoint x y)
    _ = 1 := by
      have hsum : (∑ i : Fin 3, dist ((0 : E3) i) ((planePoint x y) i) ^ (2 : ℝ)) = 1 := by
        simp [Fin.sum_univ_three, planePoint_coord0, planePoint_coord1, planePoint_coord2, sq_abs, h]
      rw [hsum]
      rw [Real.one_rpow]
lemma exists_generic_A (t : ℕ) :
    ∃ A : Finset E3,
      A.card = t ∧
      (∀ a ∈ A, dist a 0 = 1) ∧
      (∀ a ∈ A, toComplex a ≠ 0) ∧
      ∃ ω : Finset (Fin t × Fin t) → ℝ,
        ∀ S₁ S₂ : Finset (Fin t × Fin t), S₁ ≠ S₂ →
          (∀ k : ℤ, ω S₁ - ω S₂ ≠ k * (2 * Real.pi)) ∧
          (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → rotateZ (ω S₁ - ω S₂) a₁ ≠ a₂) := by
  let A : Finset E3 :=
    (Finset.univ : Finset (Fin t)).image
      (fun k => planePoint (Real.cos (k.1 * equatorStep t)) (Real.sin (k.1 * equatorStep t)))
  have hAinj : Function.Injective
      (fun k : Fin t => planePoint (Real.cos (k.1 * equatorStep t)) (Real.sin (k.1 * equatorStep t))) := by
    intro k₁ k₂ h
    exact A_inj t k₁ k₂ h
  have hcard : A.card = t := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin t)) hAinj]
    simp
  have hAne0 : ∀ a ∈ A, toComplex a ≠ 0 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    exact toComplex_planePoint_ne_zero_of_unit (Real.cos (k.1 * equatorStep t))
      (Real.sin (k.1 * equatorStep t)) (Real.cos_sq_add_sin_sq _)
  have hAunit : ∀ a ∈ A, dist a 0 = 1 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    simpa [dist_comm] using dist_zero_planePoint_unit (Real.cos (k.1 * equatorStep t))
      (Real.sin (k.1 * equatorStep t)) (Real.cos_sq_add_sin_sq _)
  refine ⟨A, hcard, hAunit, hAne0, ω t, ?_⟩
  intro S₁ S₂ hS
  constructor
  · intro k
    exact ne_int_mul_two_pi_of_abs_lt (ω t S₁ - ω t S₂) (ω_diff_ne_zero_of_ne t hS) (by
      have hlt : |ω t S₁ - ω t S₂| < omegaStep t := ω_diff_lt_step t S₁ S₂
      have hle : omegaStep t ≤ Real.pi / 4 := omegaStep_le_pi_div_four t
      nlinarith [Real.pi_pos, hlt, hle]) k
  · intro a₁ ha₁ a₂ ha₂ hne
    rcases Finset.mem_image.mp ha₁ with ⟨k₁, hk₁, rfl⟩
    rcases Finset.mem_image.mp ha₂ with ⟨k₂, hk₂, rfl⟩
    let δ : ℝ := ω t S₁ - ω t S₂
    let θ₁ : ℝ := k₁.1 * equatorStep t
    let θ₂ : ℝ := k₂.1 * equatorStep t
    intro hrot
    have hrot' : rotateZ (θ₁ + δ) (planePoint 1 0) = rotateZ θ₂ (planePoint 1 0) := by
      calc
        rotateZ (θ₁ + δ) (planePoint 1 0) = rotateZ δ (rotateZ θ₁ (planePoint 1 0)) := by
          rw [add_comm, rotateZ_add]
        _ = rotateZ δ (planePoint (Real.cos θ₁) (Real.sin θ₁)) := by
          rw [rotateZ_planePoint_one]
        _ = planePoint (Real.cos θ₂) (Real.sin θ₂) := by
          simpa [δ, θ₁, θ₂] using hrot
        _ = rotateZ θ₂ (planePoint 1 0) := by
          rw [rotateZ_planePoint_one]
    have hangle : ∃ k : ℤ, (θ₁ + δ) - θ₂ = k * (2 * Real.pi) :=
      (rotateZ_eq_iff_angle (θ₁ := θ₁ + δ) (θ₂ := θ₂) (a := planePoint 1 0)
        (toComplex_one_ne_zero)).mp hrot'
    rcases hangle with ⟨k, hk⟩
    have hδeq : δ = (θ₂ - θ₁) + k * (2 * Real.pi) := by linarith
    have hstep_pos : 0 < equatorStep t := equatorStep_pos t
    have hθ₁ge : 0 ≤ θ₁ := mul_nonneg (by exact_mod_cast (Nat.zero_le (k₁.1 : ℕ))) (le_of_lt hstep_pos)
    have hθ₂ge : 0 ≤ θ₂ := mul_nonneg (by exact_mod_cast (Nat.zero_le (k₂.1 : ℕ))) (le_of_lt hstep_pos)
    have hθ₁lt : θ₁ < Real.pi := by simpa [θ₁] using step_mul_lt_pi t k₁.2
    have hθ₂lt : θ₂ < Real.pi := by simpa [θ₂] using step_mul_lt_pi t k₂.2
    have hθlt : |θ₂ - θ₁| < Real.pi := by
      rw [abs_lt]
      constructor <;> nlinarith
    have hdlt : |δ| < omegaStep t := by simpa [δ] using ω_diff_lt_step t S₁ S₂
    have hkle : omegaStep t ≤ Real.pi / 4 := omegaStep_le_pi_div_four t
    have hkne : k₁ ≠ k₂ := by
      intro hkk
      apply hne
      rw [hkk]
    have hm_ne : ((k₂.1 : ℤ) - (k₁.1 : ℤ)) ≠ 0 := by
      intro hz
      apply hkne
      apply Fin.ext
      exact_mod_cast (Int.sub_eq_zero.mp hz).symm
    have hlin : θ₂ - θ₁ = ((k₂.1 : ℤ) - (k₁.1 : ℤ) : ℝ) * equatorStep t := by
      dsimp [θ₂, θ₁]
      push_cast
      ring
    have hge : equatorStep t ≤ |θ₂ - θ₁| := by
      have hm1 : (1 : ℝ) ≤ |((k₂.1 : ℤ) - (k₁.1 : ℤ) : ℝ)| := by
        exact_mod_cast (Int.one_le_abs hm_ne)
      have hmstep : equatorStep t ≤ |((k₂.1 : ℤ) - (k₁.1 : ℤ) : ℝ)| * equatorStep t := by
        nlinarith [hstep_pos, hm1]
      rw [hlin, abs_mul]
      rw [abs_of_pos hstep_pos]
      exact hmstep
    by_cases hk0 : k = 0
    · have hδeq' : δ = θ₂ - θ₁ := by
        simpa [hk0] using hδeq
      have hδ0 : |δ| = |θ₂ - θ₁| := by rw [hδeq']
      have hbig : equatorStep t ≤ |δ| := by rw [hδ0]; exact hge
      have hsmall : |δ| < equatorStep t := by
        have hε : omegaStep t < equatorStep t := omegaStep_lt_step t
        nlinarith [hdlt, hε]
      nlinarith
    · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        exact_mod_cast (Int.one_le_abs hk0)
      have htri : |k * (2 * Real.pi)| - |θ₂ - θ₁| ≤ |δ| := by
        have h2 := abs_sub_abs_le_abs_sub (a := k * (2 * Real.pi)) (b := -(θ₂ - θ₁))
        rw [abs_neg] at h2
        have hR : k * (2 * Real.pi) - (-(θ₂ - θ₁)) = δ := by linarith [hδeq]
        rwa [hR] at h2
      have hmag : 2 * Real.pi ≤ |δ| + |θ₂ - θ₁| := by
        have hk2 : |k * (2 * Real.pi)| = |(k : ℝ)| * (2 * Real.pi) := by
          rw [abs_mul]
          rw [abs_of_pos (by nlinarith [Real.pi_pos] : 0 < 2 * Real.pi)]
        have hkj : 2 * Real.pi ≤ |(k : ℝ)| * (2 * Real.pi) := by
          nlinarith [Real.pi_pos, hk1]
        nlinarith [htri, hk2, hkj]
      have hbig : Real.pi < |δ| := by
        nlinarith [hmag, hθlt]
      have hsmall : |δ| < Real.pi / 2 := by
        nlinarith [hdlt, hkle, Real.pi_pos]
      nlinarith [Real.pi_pos]

/-- The rotated copies of the equator set `A` are pairwise disjoint. -/
lemma B_disjoint_of_generic (t : ℕ) :
    ∃ A : Finset E3,
      A.card = t ∧
      (∀ a ∈ A, toComplex a ≠ 0) ∧
      ∃ ω : Finset (Fin t × Fin t) → ℝ,
        ∀ S₁ S₂ : Finset (Fin t × Fin t), S₁ ≠ S₂ →
          Disjoint (A.image (fun a => rotateZ (ω S₁) a)) (A.image (fun a => rotateZ (ω S₂) a)) := by
  rcases exists_generic_A t with ⟨A, hcard, _hAunit, hAne0, ω, hω⟩
  refine ⟨A, hcard, hAne0, ω, ?_⟩
  exact copies_disjoint_of_angle_avoid hAne0 hω

/-- The union `B = ⋃_S rotateZ (ω S) A` has card `t · 2^(t²)`. -/
lemma B_card_of_generic (t : ℕ) :
    ∃ B : Finset E3,
      B.card = t * 2 ^ (t * t) ∧
      ∃ A : Finset E3, ∃ ω : Finset (Fin t × Fin t) → ℝ,
        A.card = t ∧
        B = (Finset.univ : Finset (Finset (Fin t × Fin t))).biUnion
              (fun S => A.image (fun a => rotateZ (ω S) a)) := by
  rcases exists_generic_A t with ⟨A, hcard, _hAunit, hAne0, ω, hω⟩
  refine ⟨(Finset.univ : Finset (Finset (Fin t × Fin t))).biUnion
      (fun S => A.image (fun a => rotateZ (ω S) a)), ?_, A, ω, hcard, rfl⟩
  have hcopy : ∀ S : Finset (Fin t × Fin t), (A.image (fun a => rotateZ (ω S) a)).card = t := by
    intro S
    rw [Finset.card_image_of_injective (s := A) (rotateZ_injective (ω S))]
    exact hcard
  have hdisj : ((↑(Finset.univ : Finset (Finset (Fin t × Fin t))) : Set (Finset (Fin t × Fin t)))).PairwiseDisjoint
      (fun S : Finset (Fin t × Fin t) => A.image (fun a => rotateZ (ω S) a)) := by
    intro S₁ hS₁ S₂ hS₂ hne
    exact copies_disjoint_of_angle_avoid hAne0 hω S₁ S₂ hne
  rw [Finset.card_biUnion hdisj]
  calc
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin t × Fin t))), (A.image (fun a => rotateZ (ω S) a)).card)
        = ∑ _S ∈ (Finset.univ : Finset (Finset (Fin t × Fin t))), t := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hcopy S
    _ = t * 2 ^ (t * t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset]
          rw [Fintype.card_prod (Fin t) (Fin t)]
          rw [Fintype.card_fin t]
          rw [nsmul_eq_mul]
          rw [Nat.mul_comm]
          simp

/-- Every point of `B` lies on the unit sphere. -/
lemma B_sphere_of_generic (t : ℕ) :
    ∃ B : Finset E3,
      (∀ p ∈ B, p ∈ sphere 0 1) ∧
      ∃ A : Finset E3, ∃ ω : Finset (Fin t × Fin t) → ℝ,
        (∀ a ∈ A, dist a 0 = 1) ∧
        B = (Finset.univ : Finset (Finset (Fin t × Fin t))).biUnion
              (fun S => A.image (fun a => rotateZ (ω S) a)) := by
  rcases exists_generic_A t with ⟨A, hcard, hAunit, hAne0, ω, hω⟩
  refine ⟨(Finset.univ : Finset (Finset (Fin t × Fin t))).biUnion
      (fun S => A.image (fun a => rotateZ (ω S) a)), ?_, A, ω, hAunit, rfl⟩
  intro p hp
  rw [Finset.mem_biUnion] at hp
  rcases hp with ⟨S, _hS, ha⟩
  rcases Finset.mem_image.mp ha with ⟨a, haA, rfl⟩
  have hrot0 : dist (rotateZ (ω S) a) 0 = dist a 0 := by
    calc
      dist (rotateZ (ω S) a) 0 = dist (rotateZ (ω S) a) (rotateZ (ω S) 0) := by
        rw [rotateZ_zero_point (ω S)]
      _ = dist a 0 := rotateZ_isometry (ω S) a 0
  have hdist : dist (rotateZ (ω S) a) 0 = 1 := by
    rw [hrot0]
    exact hAunit a haA
  simpa [sphere] using hdist

end


/-! Gate 6: symmetric-difference counting for the grid.

There are `2^(t*t)` subsets `S : Finset (Fin t × Fin t)` of the grid.  The
number of directed pairs `(S, x)` with `x ∉ S` -- equivalently pairs
`(S, S ∪ {x})` differing in exactly one grid cell -- is `(t*t) * 2^(t*t-1)`,
which is `(t²/2) · 2^(t²)` as required by the plan.
-/

lemma cell_absent_one (t : ℕ) (x : Fin t × Fin t) :
    (Finset.univ.filter (fun S : Finset (Fin t × Fin t) => x ∉ S)).card =
      2 ^ (t * t - 1) := by
  classical
  rw [show (Finset.univ.filter (fun S : Finset (Fin t × Fin t) => x ∉ S)) =
        (Finset.univ.erase x).powerset by
    ext S
    simp [Finset.mem_powerset]
    constructor
    · intro hxS y hyS
      rw [Finset.mem_erase]
      constructor
      · intro hyx
        subst hyx
        exact hxS hyS
      · simp
    · intro hS hxS
      have h : x ∈ (Finset.univ.erase x) := hS hxS
      simp at h]
  rw [Finset.card_powerset]
  congr 1
  rw [Finset.card_erase_of_mem (by simp : x ∈ (Finset.univ : Finset (Fin t × Fin t)))]
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

lemma cell_absent_count (t : ℕ) :
    (∑ S : Finset (Fin t × Fin t),
      (Finset.univ.filter (fun x : Fin t × Fin t => x ∉ S)).card) =
        (t * t) * 2 ^ (t * t - 1) := by
  classical
  calc
    (∑ S : Finset (Fin t × Fin t),
      (Finset.univ.filter (fun x : Fin t × Fin t => x ∉ S)).card)
        = ∑ S : Finset (Fin t × Fin t), ∑ x : Fin t × Fin t, if x ∉ S then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.card_filter]
    _ = ∑ x : Fin t × Fin t, ∑ S : Finset (Fin t × Fin t), if x ∉ S then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x : Fin t × Fin t,
          (Finset.univ.filter (fun S : Finset (Fin t × Fin t) => x ∉ S)).card := by
          apply Finset.sum_congr rfl
          intro x hx
          symm
          rw [Finset.sum_boole]
          simp
    _ = ∑ x : Fin t × Fin t, 2 ^ (t * t - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [cell_absent_one t x]
    _ = (t * t) * 2 ^ (t * t - 1) := by
          rw [Finset.sum_const]
          rw [nsmul_eq_mul]
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
          norm_num

/-! Gate 6 geometry bridge: rotation composition and copy distance template.

For copies `rotateZ θ A` and `rotateZ (θ + φ) A` of a rotated point set, the
distance between `rotateZ (θ+φ) a` and `rotateZ θ b` equals the distance
between `rotateZ φ a` and `b` -- the rotation by `θ` cancels.  This is the
bridge that turns a grid angle `φ` with `dist b (rotateZ φ a) = 1` into a
unit-distance pair between two copies differing by `φ`.
-/

lemma rotateZ_comm (α β : ℝ) (p : E3) :
    rotateZ α (rotateZ β p) = rotateZ β (rotateZ α p) := by
  rw [← rotateZ_add, add_comm, rotateZ_add]

lemma rotateZ_add_comm (α β : ℝ) (p : E3) :
    rotateZ (α + β) p = rotateZ β (rotateZ α p) := by
  rw [add_comm, rotateZ_add]

lemma dist_rotateZ_add_rotateZ (θ φ : ℝ) (a b : E3) :
    dist (rotateZ (θ + φ) a) (rotateZ θ b) = dist (rotateZ φ a) b := by
  rw [rotateZ_add_comm]
  rw [rotateZ_comm φ θ a]
  exact rotateZ_isometry θ (rotateZ φ a) b

/-! Gate 6 counting: grid angle sums and unit-distance pairs between copies.

`gridSum` accumulates a grid angle over a subset `S` of the grid.  The
`unit_pair_between_copies` template turns a single unit-distance relationship
`dist b (rotateZ φ a) = 1` into a unit-distance pair between the two copies
rotated by `θ` and `θ + φ` -- via `dist_rotateZ_add_rotateZ`.
-/

def gridSum (t : ℕ) (φ : Fin t × Fin t → ℝ) (S : Finset (Fin t × Fin t)) : ℝ :=
  Finset.sum S φ

lemma unit_pair_between_copies {A : Finset E3} (θ φ : ℝ) {a b : E3}
    (ha : a ∈ A) (hb : b ∈ A) (hφ : dist b (rotateZ φ a) = 1) :
    ∃ u ∈ A.image (fun p => rotateZ (θ + φ) p),
      ∃ v ∈ A.image (fun p => rotateZ θ p), dist u v = 1 := by
  refine ⟨rotateZ (θ + φ) a, ?_, rotateZ θ b, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  · rw [dist_rotateZ_add_rotateZ]
    rw [dist_comm]
    exact hφ

/-! Gate 6 grid angles: the equator points and the grid angle function.

The equator point `A_point t k` has polar angle `k·step`.  For two such points
`a_i`, `a_j` the grid angle `β_grid t i j = θ_j - θ_i + π/3` rotates `a_i` to a
point at distance exactly 1 from `a_j` (unit-circle chord of angle `π/3`).  The
verification `beta_grid_unit` is completed in a later gate-6 step.
-/

noncomputable def A_point (t : ℕ) (k : Fin t) : E3 :=
  planePoint (Real.cos (k.1 * equatorStep t)) (Real.sin (k.1 * equatorStep t))

noncomputable def β_grid (t : ℕ) (i j : Fin t) : ℝ :=
  (j.1 * equatorStep t) - (i.1 * equatorStep t) + Real.pi / 3

/-! Gate 6 geometry: rotating an equator point and the unit chord formula.

`rotateZ_planePoint_cos_sin` rotates the parametrised point
`(cos α, sin α, 0)` to `(cos (θ+α), sin (θ+α), 0)`.  The chord formula
`dist_planePoint_cos_sin` computes the distance between two parametrised
unit-circle points as `2·|sin ((α-β)/2)|`.
-/

lemma rotateZ_planePoint_cos_sin (θ α : ℝ) :
    rotateZ θ (planePoint (Real.cos α) (Real.sin α)) =
      planePoint (Real.cos (θ + α)) (Real.sin (θ + α)) := by
  ext i
  fin_cases i <;> simp [rotateZ, planePoint, Real.cos_add, Real.sin_add] <;> ring

lemma dist_planePoint_cos_sin (α β : ℝ) :
    dist (planePoint (Real.cos α) (Real.sin α)) (planePoint (Real.cos β) (Real.sin β)) =
      2 * |Real.sin ((α - β) / 2)| := by
  have hp2 : 0 < (2 : ENNReal).toReal := by norm_num
  have htrig : (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 =
      4 * (Real.sin ((α - β) / 2)) ^ 2 := by
    have h1 : (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 =
        2 - 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
      have hc : ∀ x : ℝ, Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
        intro x
        exact Real.cos_sq_add_sin_sq x
      calc
        (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2
            = Real.cos α ^ 2 - 2 * Real.cos α * Real.cos β + Real.cos β ^ 2 +
                Real.sin α ^ 2 - 2 * Real.sin α * Real.sin β + Real.sin β ^ 2 := by ring
        _ = (Real.cos α ^ 2 + Real.sin α ^ 2) + (Real.cos β ^ 2 + Real.sin β ^ 2) -
              2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by ring
        _ = 2 - 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) := by
          rw [hc α, hc β]; ring
    rw [h1]
    have h2 : 2 - 2 * (Real.cos α * Real.cos β + Real.sin α * Real.sin β) =
        2 - 2 * Real.cos (α - β) := by
      rw [Real.cos_sub]
    rw [h2]
    have hhalf : 4 * (Real.sin ((α - β) / 2)) ^ 2 = 2 - 2 * Real.cos (α - β) := by
      have h4 : ∀ x : ℝ, 4 * (Real.sin x) ^ 2 = 2 - 2 * Real.cos (2 * x) := by
        intro x
        rw [Real.cos_two_mul]
        rw [Real.sin_sq]
        ring
      calc
        4 * (Real.sin ((α - β) / 2)) ^ 2 = 2 - 2 * Real.cos (2 * ((α - β) / 2)) := h4 ((α - β) / 2)
        _ = 2 - 2 * Real.cos (α - β) := by
          have ht : 2 * ((α - β) / 2) = α - β := by ring
          rw [ht]
    exact hhalf.symm
  have hsq : (dist (planePoint (Real.cos α) (Real.sin α)) (planePoint (Real.cos β) (Real.sin β))) ^ 2 =
      (2 * |Real.sin ((α - β) / 2)|) ^ 2 := by
    rw [PiLp.dist_eq_sum hp2 (planePoint (Real.cos α) (Real.sin α)) (planePoint (Real.cos β) (Real.sin β))]
    have htoReal : (ENNReal.toReal 2 : ℝ) = 2 := by norm_num
    rw [htoReal]
    have hsum0 : 0 ≤ (∑ i : Fin 3,
        dist ((planePoint (Real.cos α) (Real.sin α)).ofLp i) ((planePoint (Real.cos β) (Real.sin β)).ofLp i) ^ (2 : ℝ)) := by
      exact Finset.sum_nonneg (fun i hi => Real.rpow_nonneg dist_nonneg 2)
    have hsq2 : ((∑ i : Fin 3,
        dist ((planePoint (Real.cos α) (Real.sin α)).ofLp i) ((planePoint (Real.cos β) (Real.sin β)).ofLp i) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)) ^ 2 = (∑ i : Fin 3,
        dist ((planePoint (Real.cos α) (Real.sin α)).ofLp i) ((planePoint (Real.cos β) (Real.sin β)).ofLp i) ^ (2 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hsum0]
      have hmm : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 := by norm_num
      rw [hmm]
      rw [Real.rpow_one]
    rw [hsq2]
    rw [Fin.sum_univ_three]
    simp [Real.dist_eq, sq_abs, planePoint_coord0, planePoint_coord1, planePoint_coord2]
    rw [htrig]
    ring_nf
    rw [sq_abs]
  have h1' : 0 ≤ dist (planePoint (Real.cos α) (Real.sin α)) (planePoint (Real.cos β) (Real.sin β)) :=
    dist_nonneg
  have h2' : 0 ≤ 2 * |Real.sin ((α - β) / 2)| := by
    exact mul_nonneg (by norm_num) (abs_nonneg _)
  have habs : |dist (planePoint (Real.cos α) (Real.sin α)) (planePoint (Real.cos β) (Real.sin β))| =
      |2 * (|Real.sin ((α - β) / 2)|)| := by
    exact Iff.mp (sq_eq_sq_iff_abs_eq_abs (dist (planePoint (Real.cos α) (Real.sin α)) (planePoint (Real.cos β) (Real.sin β))) (2 * (|Real.sin ((α - β) / 2)|))) hsq
  rw [abs_of_nonneg h1'] at habs
  rw [abs_of_nonneg h2'] at habs
  exact habs
/-- The grid angle `beta_grid t i j` rotates the equator point `a_i` to a point at
distance exactly 1 from `a_j` (a unit-circle chord of angle `pi/3`). -/
lemma beta_grid_unit (t : ℕ) (i j : Fin t) :
    dist (rotateZ (β_grid t i j) (A_point t i)) (A_point t j) = 1 := by
  have hβ : β_grid t i j + i.1 * equatorStep t - j.1 * equatorStep t = Real.pi / 3 := by
    unfold β_grid
    ring
  calc
    dist (rotateZ (β_grid t i j) (A_point t i)) (A_point t j)
        = dist (planePoint (Real.cos (β_grid t i j + i.1 * equatorStep t))
                           (Real.sin (β_grid t i j + i.1 * equatorStep t)))
               (planePoint (Real.cos (j.1 * equatorStep t)) (Real.sin (j.1 * equatorStep t))) := by
            unfold A_point
            rw [rotateZ_planePoint_cos_sin]
    _ = 2 * |Real.sin ((β_grid t i j + i.1 * equatorStep t - j.1 * equatorStep t) / 2)| := by
            rw [dist_planePoint_cos_sin]
    _ = 2 * |Real.sin (Real.pi / 6)| := by
            rw [hβ]
            ring_nf
    _ = 2 * |(1 / 2 : ℝ)| := by
            rw [Real.sin_pi_div_six]
    _ = 1 := by
            rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            norm_num
/-- The grid angle contributed by a single grid cell `x = (i,j)`. -/
noncomputable def gridAngle (t : ℕ) (x : Fin t × Fin t) : ℝ :=
  β_grid t x.1 x.2

/-- Main gate-6 counting lemma: if `S' = S ∪ {x}` (symmetric difference of size 1),
then between the two rotated copies of `A` (by the grid sums of `S` and `S'`) there
is at least one unit-distance pair. -/
lemma symmdiff_one_unit_pair (t : ℕ) (S : Finset (Fin t × Fin t)) (x : Fin t × Fin t)
    (hx : x ∉ S) (A : Finset E3) (hai : A_point t x.1 ∈ A) (haj : A_point t x.2 ∈ A) :
    ∃ u ∈ (A.image (fun p => rotateZ (gridSum t (gridAngle t) (S ∪ {x})) p)),
      ∃ v ∈ (A.image (fun p => rotateZ (gridSum t (gridAngle t) S) p)), dist u v = 1 := by
  have hφ : dist (A_point t x.2) (rotateZ (gridAngle t x) (A_point t x.1)) = 1 := by
    rw [gridAngle]
    rw [dist_comm]
    exact beta_grid_unit t x.1 x.2
  have hdisj : Disjoint S {x} := by
    rw [Finset.disjoint_singleton_right]
    exact hx
  have hsum : gridSum t (gridAngle t) (S ∪ {x}) = gridSum t (gridAngle t) S + gridAngle t x := by
    unfold gridSum
    rw [Finset.sum_union hdisj]
    rw [Finset.sum_singleton]
  obtain ⟨u, hu, v, hv, huv⟩ :=
    unit_pair_between_copies (gridSum t (gridAngle t) S) (gridAngle t x) hai haj hφ
  refine ⟨u, ?_, v, ?_, huv⟩
  · rw [← hsum] at hu
    exact hu
  · exact hv
/-- `sqrt 2 * sqrt 2 = 2` (used in the JSP-492 scaling bridge). -/
lemma sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  simpa [sq] using Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

/-- Scaling by `sqrt 2` turns a unit-distance pair into a `sqrt 2`-distance pair. -/
lemma dist_smul_sqrt2_unit (p q : E3) (h : dist p q = 1) :
    dist ((Real.sqrt 2 : ℝ) • p) ((Real.sqrt 2 : ℝ) • q) = Real.sqrt 2 := by
  rw [dist_smul₀]
  rw [h]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  ring

/-- Scaling by `sqrt 2` maps the sphere of radius `sqrt 2 / 2` into the unit sphere. -/
lemma mem_smul_sphere_sqrt2 {p : E3} (hp : p ∈ sphere 0 (Real.sqrt 2 / 2)) :
    (Real.sqrt 2 : ℝ) • p ∈ sphere 0 1 := by
  unfold sphere at hp ⊢
  change dist ((Real.sqrt 2 : ℝ) • p) 0 = 1
  rw [show (0 : E3) = (Real.sqrt 2 : ℝ) • (0 : E3) by simp]
  rw [dist_smul₀]
  rw [hp]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [← mul_div_assoc]
  rw [sqrt2_sq]
  norm_num
/-- The map `p ↦ sqrt 2 • p` is injective on `E3`. -/
lemma smul_sqrt2_injective : Function.Injective (fun p : E3 => (Real.sqrt 2 : ℝ) • p) := by
  intro x y h
  have hc : (Real.sqrt 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  exact smul_right_injective E3 hc h

/-- Scaling by `sqrt 2` turns unit-distance into `sqrt 2`-distance (both directions). -/
lemma dist_smul_sqrt2_iff (p q : E3) :
    dist ((Real.sqrt 2 : ℝ) • p) ((Real.sqrt 2 : ℝ) • q) = Real.sqrt 2 ↔ dist p q = 1 := by
  constructor
  · intro h
    rw [dist_smul₀] at h
    rw [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (Real.sqrt_nonneg 2)] at h
    have hc : (Real.sqrt 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
    have h1 : (Real.sqrt 2 : ℝ) * dist p q = (Real.sqrt 2 : ℝ) * 1 := by
      simpa using h
    exact (mul_right_inj' hc).mp h1
  · intro h
    exact dist_smul_sqrt2_unit p q h
/-- The full scaling bridge: scaling a point set by `sqrt 2` preserves the number of
unordered pairs at distance `sqrt 2` in the image vs. at distance 1 in the original. -/
lemma unorderedUnitPairs_scaled (B : Finset E3) :
    unorderedUnitPairsAtSqrt2 (B.image (fun p : E3 => (Real.sqrt 2 : ℝ) • p)) = unorderedUnitPairs B := by
  let g : E3 → E3 := fun p => (Real.sqrt 2 : ℝ) • p
  have hg_inj : Function.Injective g := smul_sqrt2_injective
  have hF_inj : Function.Injective (fun pq : E3 × E3 => (g pq.1, g pq.2)) := by
    intro pq rs h
    apply Prod.ext
    · exact hg_inj (congrArg Prod.fst h)
    · exact hg_inj (congrArg Prod.snd h)
  unfold unorderedUnitPairsAtSqrt2 unorderedUnitPairs orderedUnitPairs
  congr 1
  have hprod : (B.image g).product (B.image g) = (B.product B).image (fun pq : E3 × E3 => (g pq.1, g pq.2)) := by
    ext uv
    constructor
    · intro h
      rcases (Finset.mem_product.1 h) with ⟨hu1, hu2⟩
      rcases (Finset.mem_image.1 hu1) with ⟨a, ha, hga⟩
      rcases (Finset.mem_image.1 hu2) with ⟨b, hb, hgb⟩
      exact Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, by
        ext <;> simp [hga, hgb]⟩
    · intro h
      rcases (Finset.mem_image.1 h) with ⟨pq, hpq, hpq_eq⟩
      have hfst : g pq.1 = uv.1 := congrArg Prod.fst hpq_eq
      have hsnd : g pq.2 = uv.2 := congrArg Prod.snd hpq_eq
      exact Finset.mem_product.2
        ⟨Finset.mem_image.2 ⟨pq.1, (Finset.mem_product.1 hpq).1, hfst⟩,
         Finset.mem_image.2 ⟨pq.2, (Finset.mem_product.1 hpq).2, hsnd⟩⟩
  rw [hprod]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ hF_inj]
  congr 1
  ext pq
  simp
  intro hp1 hp2
  constructor
  · intro h
    constructor
    · intro h_eq
      exact h.1 (congrArg g h_eq)
    · exact (dist_smul_sqrt2_iff pq.1 pq.2).1 h.2
  · intro h
    constructor
    · intro h_eq
      exact h.1 (hg_inj h_eq)
    · exact (dist_smul_sqrt2_iff pq.1 pq.2).2 h.2
/-- Scaling a point of the unit sphere by `1/√2` lands on the sphere of radius
`1/√2` (the critical `D = √2` case of the Swanepoel–Valtr construction). -/
lemma mem_smul_sphere_inv_sqrt2 {p : E3} (hp : p ∈ sphere 0 1) :
    (1 / Real.sqrt 2 : ℝ) • p ∈ sphere 0 (1 / Real.sqrt 2) := by
  unfold sphere at hp ⊢
  change dist ((1 / Real.sqrt 2 : ℝ) • p) 0 = (1 / Real.sqrt 2 : ℝ)
  have h0 : (0 : E3) = (1 / Real.sqrt 2 : ℝ) • (0 : E3) := by simp
  rw [h0, dist_smul₀]
  rw [Real.norm_eq_abs,
      abs_of_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg 2))]
  rw [hp]
  ring

/-- Scaling by `1/√2` and then by `√2` recovers the original point set. -/
lemma sqrt2_smul_inv_sqrt2_image (B : Finset E3) :
    (B.image (fun p : E3 => (1 / Real.sqrt 2 : ℝ) • p)).image
        (fun p : E3 => (Real.sqrt 2 : ℝ) • p) = B := by
  rw [Finset.image_image]
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hmul : (Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = 1 := by
    rw [mul_one_div, div_self hs]
  have hpt : ∀ a : E3, (Real.sqrt 2 : ℝ) • ((1 / Real.sqrt 2 : ℝ) • a) = a := by
    intro a
    calc
      (Real.sqrt 2 : ℝ) • ((1 / Real.sqrt 2 : ℝ) • a) =
          (Real.sqrt 2 * (1 / Real.sqrt 2) : ℝ) • a := by
            rw [← smul_smul]
      _ = a := by rw [hmul]; simp
  ext p
  simp [hpt]

/-- Swanepoel–Valtr Theorem 1 (critical-diameter `D = √2` form).

The official JSP-000492 statement (matching the catalog) is the `∃ f → ∞` form
proved as `jsp492_official`; the theorem below is its `≥ c·n·√(log n)` corollary:
`n` points on the sphere of radius `1/√2` (diameter `√2`) with at least
`c·n·√(log n)` unordered unit-distance pairs, `c = 1/(72√3)`, obtained by scaling
the unit-sphere construction by `1/√2`.  (An absolute constant for *every* `D > 1`
is not part of the official statement; the radius-`1/√2` sphere is the critical
case.) -/
theorem swanepoel_valtr :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ B : Finset E3,
          B.card = n ∧
          (∀ p ∈ B, p ∈ sphere 0 (1 / Real.sqrt 2)) ∧
          (c * (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) ≤ (unorderedUnitPairs B : ℝ)) := by
  refine ⟨(1 / (72 * Real.sqrt 3) : ℝ), ?_, ?_⟩
  · exact div_pos (by norm_num) (mul_pos (by norm_num)
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  · intro n hn
    by_cases hn3 : 3 ≤ n
    · rcases jsp492_exists n with ⟨B0, hc, hs, hp⟩
      let B : Finset E3 := B0.image (fun p : E3 => (1 / Real.sqrt 2 : ℝ) • p)
      refine ⟨B, ?_, ?_, ?_⟩
      · have hBcard : B.card = B0.card := by
          unfold B
          exact Finset.card_image_of_injective B0 (smul_right_injective E3
            (ne_of_gt (one_div_pos.mpr (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))))
        rw [hBcard, hc]
      · intro p hpB
        rcases (Finset.mem_image.1 hpB) with ⟨a, ha, rfl⟩
        exact mem_smul_sphere_inv_sqrt2 (hs a ha)
      · calc
          (1 / (72 * Real.sqrt 3) : ℝ) * (n : ℝ) * Real.sqrt (Real.log (n : ℝ))
              = (n : ℝ) * ((1 / (72 * Real.sqrt 3) : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by ring
          _ ≤ (n : ℝ) * f492q n := by
            exact mul_le_mul_of_nonneg_left (swanepoel_analysis n hn3) (by positivity)
          _ ≤ (unorderedUnitPairsAtSqrt2 B0 : ℝ) := hp
          _ = (unorderedUnitPairs B : ℝ) := by
            have hbridge : unorderedUnitPairsAtSqrt2 B0 = unorderedUnitPairs B := by
              calc
                unorderedUnitPairsAtSqrt2 B0
                    = unorderedUnitPairsAtSqrt2 (B.image (fun p : E3 => (Real.sqrt 2 : ℝ) • p)) := by
                        rw [sqrt2_smul_inv_sqrt2_image B0]
                _ = unorderedUnitPairs B := unorderedUnitPairs_scaled B
            exact_mod_cast hbridge
    · have hn2 : n = 2 := by omega
      subst n
      let u : E3 := planePoint (1 / Real.sqrt 2) 0
      let v : E3 := planePoint 0 (1 / Real.sqrt 2)
      let B2 : Finset E3 := ({u, v} : Finset E3)
      have huv : u ≠ v := by
        intro h
        have hc0 : u 0 = v 0 := by rw [h]
        have hz : (1 / Real.sqrt 2 : ℝ) = 0 := by
          simpa [u, v, planePoint_coord0] using hc0
        exact (ne_of_gt (one_div_pos.mpr
          (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))) hz
      refine ⟨B2, ?_, ?_, ?_⟩
      · simp [B2, huv]
      · intro r hr
        have hu_sphere : u ∈ sphere 0 (1 / Real.sqrt 2) := by
          have hu_eq : u = (1 / Real.sqrt 2 : ℝ) • planePoint 1 0 := by
            ext i
            fin_cases i <;> simp [u, planePoint, planePoint_coord0, planePoint_coord1,
              planePoint_coord2, smul_eq_mul]
          have hu1 : planePoint 1 0 ∈ sphere 0 1 := by
            change dist (planePoint 1 0) 0 = 1
            rw [dist_comm]
            exact dist_zero_planePoint_unit 1 0 (by norm_num : (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1)
          rw [hu_eq]
          exact mem_smul_sphere_inv_sqrt2 hu1
        have hv_sphere : v ∈ sphere 0 (1 / Real.sqrt 2) := by
          have hv_eq : v = (1 / Real.sqrt 2 : ℝ) • planePoint 0 1 := by
            ext i
            fin_cases i <;> simp [v, planePoint, planePoint_coord0, planePoint_coord1,
              planePoint_coord2, smul_eq_mul]
          have hv1 : planePoint 0 1 ∈ sphere 0 1 := by
            change dist (planePoint 0 1) 0 = 1
            rw [dist_comm]
            exact dist_zero_planePoint_unit 0 1 (by norm_num : (0 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 1)
          rw [hv_eq]
          exact mem_smul_sphere_inv_sqrt2 hv1
        have hrm : r = u ∨ r = v := by
          simpa [B2] using hr
        rcases hrm with rfl | rfl
        · exact hu_sphere
        · exact hv_sphere
      · have huv_dist : dist u v = 1 := by
          have hp2 : 0 < (2 : ENNReal).toReal := by norm_num
          calc
            dist u v = (∑ i : Fin 3, dist (u i) (v i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
              PiLp.dist_eq_sum hp2 u v
            _ = 1 := by
              have hsq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
                rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
                norm_num
              have hsum : (∑ i : Fin 3, dist (u i) (v i) ^ (2 : ℝ)) = 1 := by
                simp [Fin.sum_univ_three, u, v, planePoint_coord0, planePoint_coord1,
                  planePoint_coord2, sq_abs, hsq]
                norm_num
              rw [hsum]
              rw [Real.one_rpow]
        have horder_ge : 2 ≤ orderedUnitPairs B2 := by
          unfold orderedUnitPairs
          let F : Finset (E3 × E3) := ({(u, v), (v, u)} : Finset (E3 × E3))
          calc
            2 = F.card := by
              have hne : (u, v) ≠ (v, u) := by
                intro h
                exact huv (by simpa using (congrArg Prod.fst h))
              simp [F, hne]
            _ ≤ ((B2.product B2).filter (fun pq : E3 × E3 => pq.1 ≠ pq.2 ∧
              dist pq.1 pq.2 = 1)).card :=
              Finset.card_le_card (by
                intro x hx
                simp [F] at hx
                rcases hx with h | h
                · subst h
                  simp [B2, huv, huv_dist]
                · subst h
                  simp [B2, huv.symm]
                  rw [dist_comm]
                  exact huv_dist)
        have hup : 1 ≤ unorderedUnitPairs B2 := by
          unfold unorderedUnitPairs
          rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
          norm_num
          exact horder_ge
        have hlog2le : Real.log 2 ≤ 2 := by
          calc
            Real.log 2 ≤ (2 : ℝ) ^ (1 : ℝ) / (1 : ℝ) :=
              Real.log_le_rpow_div (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1)
            _ = 2 := by
              rw [Real.rpow_one]
              norm_num
        have hsqrtle : Real.sqrt (Real.log 2) ≤ Real.sqrt 2 :=
          Real.sqrt_le_sqrt hlog2le
        have hsqrt2le : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        have hsq3ge : 1 ≤ Real.sqrt 3 := by
          have h3 := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ (3 : ℝ))
          rwa [Real.sqrt_one] at h3
        have hmain2 : (2 : ℝ) * Real.sqrt (Real.log 2) ≤ 72 * Real.sqrt 3 := by
          calc
            (2 : ℝ) * Real.sqrt (Real.log 2) ≤ 2 * Real.sqrt 2 := by
              exact mul_le_mul_of_nonneg_left hsqrtle (by norm_num : (0 : ℝ) ≤ 2)
            _ ≤ 2 * 2 := by
              exact mul_le_mul_of_nonneg_left hsqrt2le (by norm_num : (0 : ℝ) ≤ 2)
            _ ≤ 72 * Real.sqrt 3 := by nlinarith [hsq3ge]
        have hden : 0 < 72 * Real.sqrt 3 := by
          exact mul_pos (by norm_num : (0 : ℝ) < 72)
            (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))
        have hfin : (1 / (72 * Real.sqrt 3) : ℝ) * (2 : ℝ) * Real.sqrt (Real.log 2) ≤ 1 := by
          rw [show (1 / (72 * Real.sqrt 3) : ℝ) * (2 : ℝ) * Real.sqrt (Real.log 2) =
                  (2 * Real.sqrt (Real.log 2)) / (72 * Real.sqrt 3) by ring]
          rw [div_le_iff₀ hden]
          simpa using hmain2
        exact le_trans hfin (by exact_mod_cast hup)

end Jsp492

