import Mathlib.Algebra.Group.Center
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.Data.List.OfFn
import Rl2

open Set

universe u

namespace Jsp125

variable {G : Type u} [Group G]

-- ============ 1. 消去引理 ============
lemma commute_cancel_left (x y z : G) (hxy : Commute x y) (hxyz : Commute x (y * z)) :
    Commute x z := by
  have h1 : y * x * z = y * z * x := by
    calc
      y * x * z = x * y * z := by rw [hxy]
      _ = x * (y * z) := by group
      _ = (y * z) * x := hxyz
      _ = y * z * x := by group
  have h1' : y * (x * z) = y * (z * x) := by
    calc
      y * (x * z) = y * x * z := by rw [← mul_assoc]
      _ = y * z * x := h1
      _ = y * (z * x) := by rw [mul_assoc]
  exact mul_left_cancel h1'

lemma commute_cancel_right (x y z : G) (hxz : Commute x z) (hxyz : Commute x (y * z)) :
    Commute x y := by
  have h1 : x * y * z = y * x * z := by
    calc
      x * y * z = x * (y * z) := by group
      _ = (y * z) * x := hxyz
      _ = y * (z * x) := by group
      _ = y * (x * z) := by rw [← hxz]
      _ = y * x * z := by group
  exact mul_right_cancel h1

-- (iii') 用：B 换 y 且 x*B 换 y ⟹ x 换 y
lemma commute_cancel_mul_right (x y B : G) (hB : Commute B y) (hc : Commute (x * B) y) :
    Commute x y := by
  have h1 : (x * y) * B = (y * x) * B := by
    calc
      (x * y) * B = x * (y * B) := by group
      _ = x * (B * y) := by rw [hB]
      _ = (x * B) * y := by group
      _ = y * (x * B) := hc
      _ = (y * x) * B := by group
  exact mul_right_cancel h1

-- ============ 2. 乘积交换引理（List 版 + Fin 桥接） ============
lemma commute_list (l : List G) (x : G) (hx : ∀ j : ℕ, ∀ hj : j < l.length, Commute x (l.get ⟨j, hj⟩)) :
    Commute x l.prod := by
  induction l with
  | nil =>
      simp [Commute, List.prod_nil, mul_one, one_mul]
  | cons a t ih =>
      rw [List.prod_cons]
      exact Commute.mul_right
        (by simpa using hx 0 (by simp))
        (ih (fun j hj => by simpa using hx j.succ (by simp [hj])))

lemma commute_prod (n : ℕ) (b : Fin n → G) (x : G) (hx : ∀ j : Fin n, Commute x (b j)) :
    Commute x (List.ofFn b).prod := by
  apply commute_list (List.ofFn b) x
  intro j hj
  have hj' : j < n := by simpa [List.length_ofFn] using hj
  have hget : (List.ofFn b).get ⟨j, hj⟩ = b ⟨j, hj'⟩ := by
    simp [List.get_ofFn, List.length_ofFn]
  rw [hget]
  exact hx ⟨j, hj'⟩

-- 关键：x 换除 b i 外所有因子 ⟹ x 不换乘积（List 版，索引干净）
lemma not_commute_list (l : List G) (x : G) (i : ℕ) (hi : i < l.length)
    (hx : ∀ j : ℕ, ∀ hj : j < l.length, j ≠ i → Commute x (l.get ⟨j, hj⟩))
    (hxi : ¬ Commute x (l.get ⟨i, hi⟩)) :
    ¬ Commute x l.prod := by
  induction l generalizing i with
  | nil =>
      exact (Nat.not_lt_zero i hi).elim
  | cons a t ih =>
      cases i with
      | zero =>
          intro h
          rw [List.prod_cons] at h
          have ht : Commute x t.prod :=
            commute_list t x (fun j hj => by simpa using hx j.succ (by simp [hj]) (Nat.succ_ne_zero j))
          have ha : Commute x a := commute_cancel_right x a t.prod ht h
          exact hxi (by simpa using ha)
      | succ j =>
          intro h
          rw [List.prod_cons] at h
          have ha : Commute x a := by simpa using hx 0 (by simp) (Ne.symm (Nat.succ_ne_zero j))
          have ht : Commute x t.prod := commute_cancel_left x a t.prod ha h
          have ht' : ¬ Commute x t.prod :=
            ih j (by simpa using hi)
              (fun k hk hkj => by
                simpa using hx k.succ (by simp [hk]) (by
                  intro hsucc
                  omega))
              (by simpa using hxi)
          exact ht' ht

lemma not_commute_prod (n : ℕ) (b : Fin n → G) (x : G) (i : Fin n)
    (hx : ∀ j : Fin n, j ≠ i → Commute x (b j)) (hxi : ¬ Commute x (b i)) :
    ¬ Commute x (List.ofFn b).prod := by
  exact not_commute_list (List.ofFn b) x i.1 (by simpa [List.length_ofFn] using i.2)
    (by
      intro j hj hji
      have hj' : j < n := by simpa [List.length_ofFn] using hj
      have hget : (List.ofFn b).get ⟨j, hj⟩ = b ⟨j, hj'⟩ := by
        simp [List.get_ofFn, List.length_ofFn]
      rw [hget]
      apply hx ⟨j, hj'⟩
      intro heq
      exact hji (congrArg Fin.val heq))
    (by
      intro hc
      apply hxi
      simpa [List.get_ofFn, List.length_ofFn] using hc)

-- ============ 3. A = C_G({a_i} ∪ {b_i}) ============
def A_of (n : ℕ) (a b : Fin n → G) : Subgroup G :=
  ⨅ i : Fin n ⊕ Fin n, (match i with
    | Sum.inl j => Subgroup.centralizer ({a j} : Set G)
    | Sum.inr j => Subgroup.centralizer ({b j} : Set G))

lemma A_finiteIndex (n : ℕ) (a b : Fin n → G)
    (hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex) :
    (A_of n a b).FiniteIndex := by
  unfold A_of
  exact Subgroup.finiteIndex_iInf (fun i => by
    cases i with
    | inl j => exact hFC (a j)
    | inr j => exact hFC (b j))

-- ============ 4. Corollary 3 ============
lemma cor3 (hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex)
    (hnotFIZ : ¬ (Subgroup.center G).FiniteIndex)
    (A : Subgroup G) (hAfin : A.FiniteIndex) :
    ¬ (∀ x y : G, x ∈ A → y ∈ A → Commute x y) := by
  intro hAbel
  exact hnotFIZ (rl2 hFC A hAfin hAbel)

lemma cor3_exists (hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex)
    (hnotFIZ : ¬ (Subgroup.center G).FiniteIndex)
    (A : Subgroup G) (hAfin : A.FiniteIndex) :
    ∃ x y : G, x ∈ A ∧ y ∈ A ∧ ¬ Commute x y := by
  by_contra h
  apply cor3 hFC hnotFIZ A hAfin
  intro x y hx hy
  by_contra hnc
  exact h ⟨x, y, hx, hy, hnc⟩

-- ============ 5. x ∈ A 的交换事实 ============
lemma memA_commutes (n : ℕ) (a b : Fin n → G) (x : G) (hxA : x ∈ A_of n a b) :
    (∀ i : Fin n, Commute (a i) x) ∧ (∀ i : Fin n, Commute x (b i)) := by
  constructor
  · intro i
    have hxCi : x ∈ Subgroup.centralizer ({a i} : Set G) := (Subgroup.mem_iInf.mp hxA (Sum.inl i))
    exact (Subgroup.mem_centralizer_iff.mp hxCi) (a i) (by simp)
  · intro i
    have hxCi : x ∈ Subgroup.centralizer ({b i} : Set G) := (Subgroup.mem_iInf.mp hxA (Sum.inr i))
    have hbix : Commute (b i) x := (Subgroup.mem_centralizer_iff.mp hxCi) (b i) (by simp)
    exact hbix.symm

-- ============ 6. 延拓元素性质 (i')-(iv') ============
lemma ext_props (n : ℕ) (a b : Fin n → G)
    (hiib : ∀ ⦃i j : Fin n⦄, i ≠ j → Commute (a i) (b j))
    (hiiib : ∀ i : Fin n, ¬ Commute (a i) (b i))
    (hivb : ∀ i j : Fin n, Commute (b i) (b j))
    (x y : G) (hxA : x ∈ A_of n a b) (hyA : y ∈ A_of n a b)
    (hxy : ¬ Commute x y) :
    (∀ i : Fin n, ¬ Commute (a i) (x * (List.ofFn b).prod)) ∧
    (∀ j : Fin n, Commute (x * (List.ofFn b).prod) (b j)) ∧
    (¬ Commute (x * (List.ofFn b).prod) y) ∧
    (∀ i : Fin n, Commute (a i) y) := by
  have hxa1 : ∀ i : Fin n, Commute (a i) x := (memA_commutes n a b x hxA).1
  have hxa2 : ∀ i : Fin n, Commute x (b i) := (memA_commutes n a b x hxA).2
  have hya1 : ∀ i : Fin n, Commute (a i) y := (memA_commutes n a b y hyA).1
  have hya2 : ∀ i : Fin n, Commute y (b i) := (memA_commutes n a b y hyA).2
  constructor
  · intro i h
    have hB : Commute (a i) (List.ofFn b).prod := commute_cancel_left (a i) x (List.ofFn b).prod (hxa1 i) h
    exact (not_commute_prod n b (a i) i (fun j hji => hiib (Ne.symm hji)) (hiiib i)) hB
  constructor
  · intro j
    have hPj : Commute (List.ofFn b).prod (b j) :=
      (commute_prod n b (b j) (fun k => hivb j k)).symm
    exact Commute.mul_left (hxa2 j) hPj
  constructor
  · intro hc
    have hPy : Commute (List.ofFn b).prod y := (commute_prod n b y hya2).symm
    exact hxy (commute_cancel_mul_right x y (List.ofFn b).prod hPy hc)
  · exact hya1

-- ============ 8. RL3 正式组装：Lemma 4 延拓（Fin.snoc） ============

/-- Lemma 4 不变量 (i)-(iv) -/
def imm (n : ℕ) (a b : Fin n → G) : Prop :=
  (∀ ⦃i j : Fin n⦄, i ≠ j → ¬ Commute (a i) (a j)) ∧
  (∀ ⦃i j : Fin n⦄, i ≠ j → Commute (a i) (b j)) ∧
  (∀ i : Fin n, ¬ Commute (a i) (b i)) ∧
  (∀ i j : Fin n, Commute (b i) (b j))

/-- Lemma 4：一步延拓。aₙ₊₁ = x·(b₁⋯bₙ)，bₙ₊₁ = y，(x,y) 为 A 中不交换对。 -/
lemma extend (n : ℕ) (a b : Fin n → G) (h : imm n a b)
    (hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex)
    (hnotFIZ : ¬ (Subgroup.center G).FiniteIndex) :
    ∃ a' b' : Fin (n + 1) → G,
      imm (n + 1) a' b' ∧
      (∀ i : Fin n, a' i.castSucc = a i) ∧ (∀ i : Fin n, b' i.castSucc = b i) := by
  let A : Subgroup G := A_of n a b
  have hAfin : A.FiniteIndex := A_finiteIndex n a b hFC
  rcases cor3_exists hFC hnotFIZ A hAfin with ⟨x, y, hxA, hyA, hxy⟩
  let aB : G := (List.ofFn b).prod
  let a' : Fin (n + 1) → G := Fin.snoc a (x * aB)
  let b' : Fin (n + 1) → G := Fin.snoc b y
  have hext := ext_props n a b h.2.1 h.2.2.1 h.2.2.2 x y hxA hyA hxy
  have hxa : ∀ i : Fin n, a' i.castSucc = a i := by
    intro i
    simp [a', aB]
  have hxb : ∀ i : Fin n, b' i.castSucc = b i := by
    intro i
    simp [b']
  have hylast : a' (Fin.last n) = x * aB := by
    simp [a']
  have hzlast : b' (Fin.last n) = y := by
    simp [b']
  refine ⟨a', b', ?_, hxa, hxb⟩
  constructor
  · rintro i j hij
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => exact (hij rfl).elim
        | cast k =>
            intro hc
            exact hext.1 k (by simpa [hylast, hxa] using hc)
    | cast k =>
        cases i using Fin.lastCases with
        | last =>
            intro hc
            exact hext.1 k (by simpa [hylast, hxa] using hc.symm)
        | cast l =>
            have : ¬ Commute (a l) (a k) := h.1 (by intro hlk; exact hij (congrArg Fin.castSucc hlk))
            simpa [hxa] using this
  constructor
  · rintro i j hij
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => exact (hij rfl).elim
        | cast k =>
            simpa [hxa, hzlast] using hext.2.2.2 k
    | cast k =>
        cases i using Fin.lastCases with
        | last =>
            simpa [hylast, hxb] using hext.2.1 k
        | cast l =>
            have : Commute (a l) (b k) := h.2.1 (by intro hlk; exact hij (congrArg Fin.castSucc hlk))
            simpa [hxa, hxb] using this
  constructor
  · intro i
    cases i using Fin.lastCases with
    | last =>
        intro hc
        exact hext.2.2.1 (by simpa [hylast, hzlast] using hc)
    | cast k =>
        simpa [hxa, hxb] using h.2.2.1 k
  · intro i j
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last => simpa [hzlast]
        | cast k =>
            simpa [hzlast, hxb] using ((memA_commutes n a b y hyA).2 k).symm
    | cast k =>
        cases i using Fin.lastCases with
        | last =>
            simpa [hzlast, hxb] using (memA_commutes n a b y hyA).2 k
        | cast l => simpa [hxb] using h.2.2.2 l k

-- ============ 9. Corollary 5：任意长度两两不交换序列 ============

/-- 从空序列 Nat.rec 构造任意长度满足 (i)-(iv) 的双序列 -/
private noncomputable def seqrec (hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex)
    (hnotFIZ : ¬ (Subgroup.center G).FiniteIndex) (n : ℕ) :
    {q : (Fin n → G) × (Fin n → G) // imm n q.1 q.2} := by
  let base : {q : (Fin 0 → G) × (Fin 0 → G) // imm 0 q.1 q.2} := by
    refine ⟨(Fin.elim0, Fin.elim0), ?_⟩
    have h1 : ∀ ⦃i j : Fin 0⦄, i ≠ j → ¬ Commute (Fin.elim0 i : G) (Fin.elim0 j) := by
      intro i j hij
      exact Fin.elim0 i
    have h2 : ∀ ⦃i j : Fin 0⦄, i ≠ j → Commute (Fin.elim0 i : G) (Fin.elim0 j) := by
      intro i j hij
      exact Fin.elim0 i
    have h3 : ∀ i : Fin 0, ¬ Commute (Fin.elim0 i : G) (Fin.elim0 i) := by
      intro i
      exact Fin.elim0 i
    have h4 : ∀ i j : Fin 0, Commute (Fin.elim0 i : G) (Fin.elim0 j) := by
      intro i j
      exact Fin.elim0 i
    exact ⟨h1, h2, h3, h4⟩
  let step : ∀ n : ℕ,
      {q : (Fin n → G) × (Fin n → G) // imm n q.1 q.2} →
      {q : (Fin (n + 1) → G) × (Fin (n + 1) → G) // imm (n + 1) q.1 q.2} := by
    intro n p
    rcases p with ⟨⟨a, b⟩, h⟩
    choose a' b' h' hxa hxb using extend n a b h hFC hnotFIZ
    exact ⟨(a', b'), h'⟩
  exact Nat.rec base step n

/-- Corollary 5（RL3 结论）：FC − FIZ ⟹ 任意长度 n 的两两不交换序列存在 -/
lemma fc_not_fiz_pairwise_any (hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex)
    (hnotFIZ : ¬ (Subgroup.center G).FiniteIndex) (n : ℕ) :
    ∃ a : Fin n → G, ∀ i j : Fin n, i ≠ j → ¬ Commute (a i) (a j) := by
  refine ⟨(seqrec hFC hnotFIZ n).1.1, ?_⟩
  exact (seqrec hFC hnotFIZ n).2.1

end Jsp125
