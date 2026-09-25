import Mathlib.Data.Set.Finite.Basic

/-!
# 2-色无限 Ramsey（自证）
mathlib v4.34 无无限 Ramsey 模块 → 为 RL1（Neumann Lemma 1：PE ⟹ FC）自证。
定理：无限集上任意二元染色（两个颜色，无对称要求），存在无限单色子集。
-/

namespace Jsp125Ramsey

open Set

universe u
variable {α : Type u}

/-- 无限集 A 中取 a，A\{a} 必无限。 -/
lemma infinite_of_difference {A : Set α} (a : α) (hA : A.Infinite) :
    (A \ {a}).Infinite := by
  by_contra h
  have h' : (A \ {a}).Finite := Classical.not_not.mp h
  have hfin : ((A \ {a}) ∪ ({a} : Set α)).Finite := h'.union (finite_singleton a)
  have hsub : A ⊆ (A \ {a}) ∪ {a} := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inr (by simp [hxa])
    · exact Or.inl ⟨hx, hxa⟩
  exact hA (hfin.subset hsub)

/-- 无限集 A 中取 a：A\{a} 按"是否与 a 成 c 关系"分成两半，必有一半无限。 -/
lemma infinite_partition (c : α → α → Prop) {A : Set α} (a : α) (hA : A.Infinite) :
    (∃ B : Set α, B.Infinite ∧ B ⊆ A \ {a} ∧ ∀ y ∈ B, ¬ c a y) ∨
    (∃ B : Set α, B.Infinite ∧ B ⊆ A \ {a} ∧ ∀ y ∈ B, c a y) := by
  classical
  let B0 : Set α := {y ∈ A \ {a} | ¬ c a y}
  let B1 : Set α := {y ∈ A \ {a} | c a y}
  have hcov : B0 ∪ B1 = A \ {a} := by
    ext y
    constructor
    · intro hy
      rcases hy with hy | hy
      · exact hy.1
      · exact hy.1
    · intro hy
      by_cases h : c a y
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl ⟨hy, h⟩
  have hinf : (A \ {a}).Infinite := infinite_of_difference a hA
  by_cases h0 : B0.Finite
  · by_cases h1 : B1.Finite
    · exfalso
      have hfin : (B0 ∪ B1).Finite := h0.union h1
      exact hinf (by simpa [hcov] using hfin)
    · exact Or.inr ⟨B1, h1, (by intro y hy; exact hy.1), (by intro y hy; exact hy.2)⟩
  · exact Or.inl ⟨B0, h0, (by intro y hy; exact hy.1), (by intro y hy; exact hy.2)⟩

/-- 递归状态：元素 a 与其所在无限集 B。 -/
structure RS (α : Type u) where
  a : α
  B : Set α
  hmem : a ∈ B
  hinf : B.Infinite

/-- 一步的存在性：存在无限子集 B' ⊆ s.B \ {s.a}、元素 a' ∈ B'、颜色 col，
使 s.a 到 B' 全体元素的颜色统一为 col。 -/
lemma exists_rst_step (c : α → α → Prop) (s : RS α) :
    ∃ t : RS α × Prop, t.1.B ⊆ s.B \ {s.a} ∧ ∀ y ∈ t.1.B, c s.a y ↔ t.2 := by
  classical
  rcases infinite_partition c s.a s.hinf with ⟨B, hBinf, hBsub, hBcol⟩ | ⟨B, hBinf, hBsub, hBcol⟩
  · let b : α := Classical.choose hBinf.nonempty
    refine ⟨⟨⟨b, B, (Classical.choose_spec hBinf.nonempty), hBinf⟩, False⟩, ?_⟩
    constructor
    · exact hBsub
    · intro y hy
      constructor
      · intro hc; exact hBcol y hy hc
      · intro hf; exact False.elim hf
  · let b : α := Classical.choose hBinf.nonempty
    refine ⟨⟨⟨b, B, (Classical.choose_spec hBinf.nonempty), hBinf⟩, True⟩, ?_⟩
    constructor
    · exact hBsub
    · intro y hy
      constructor
      · intro _; trivial
      · intro _; exact hBcol y hy

/-- 一步（经典选择）。 -/
noncomputable def rst (c : α → α → Prop) (s : RS α) : RS α × Prop :=
  Classical.choose (exists_rst_step c s)

/-- 沿 rst 迭代的序列：F n = (状态 n, 颜色 n)。 -/
noncomputable def Fchain (c : α → α → Prop) (A : Set α) (hA : A.Infinite) :
    ℕ → RS α × Prop
  | 0 => ((⟨Classical.choose hA.nonempty, A, (Classical.choose_spec hA.nonempty), hA⟩ : RS α), True)
  | n + 1 => rst c (Fchain c A hA n).1

/-- 状态步进性质：B_{n+1} ⊆ B_n \ {aₙ}。 -/
lemma Fchain_step_sub (c : α → α → Prop) (A : Set α) (hA : A.Infinite) (n : ℕ) :
    (Fchain c A hA (n + 1)).1.B ⊆ (Fchain c A hA n).1.B \ {(Fchain c A hA n).1.a} := by
  simpa [Fchain, rst] using (Classical.choose_spec (exists_rst_step c (Fchain c A hA n).1)).1

/-- 嵌套性：B_{n+1} ⊆ B_n。 -/
lemma Fchain_nested (c : α → α → Prop) (A : Set α) (hA : A.Infinite) (n : ℕ) :
    (Fchain c A hA (n + 1)).1.B ⊆ (Fchain c A hA n).1.B := by
  exact (Fchain_step_sub c A hA n).trans (by intro y hy; exact hy.1)

/-- 链式嵌套：n < m ⟹ B_m ⊆ B_n。 -/
lemma Fchain_B_sub (c : α → α → Prop) (A : Set α) (hA : A.Infinite) :
    ∀ {n m : ℕ}, n < m → (Fchain c A hA m).1.B ⊆ (Fchain c A hA n).1.B := by
  intro n m hnm
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases h : n < m
      · exact (Fchain_nested c A hA m).trans (ih h)
      · have hEq : n = m := by omega
        subst m
        exact Fchain_nested c A hA n

/-- 颜色一致性：∀ y ∈ B_{n+1} : c aₙ y ↔ colₙ（colₙ = F (n+1) 的第二分量）。 -/
lemma Fchain_color (c : α → α → Prop) (A : Set α) (hA : A.Infinite) (n : ℕ) :
    ∀ y ∈ (Fchain c A hA (n + 1)).1.B, c (Fchain c A hA n).1.a y ↔ (Fchain c A hA (n + 1)).2 := by
  intro y hy
  simpa [Fchain, rst] using (Classical.choose_spec (exists_rst_step c (Fchain c A hA n).1)).2 y hy

/-- 元素在 A 中：aₙ ∈ A ∀ n。 -/
lemma Fchain_mem_A (c : α → α → Prop) (A : Set α) (hA : A.Infinite) : ∀ n : ℕ,
    (Fchain c A hA n).1.a ∈ A := by
  intro n
  by_cases h : n = 0
  · subst n
    simpa [Fchain] using (Classical.choose_spec hA.nonempty)
  · have hlt : 0 < n := Nat.pos_of_ne_zero h
    have hB : (Fchain c A hA n).1.B ⊆ (Fchain c A hA 0).1.B := Fchain_B_sub c A hA hlt
    have : (Fchain c A hA n).1.a ∈ (Fchain c A hA 0).1.B := hB (Fchain c A hA n).1.hmem
    simpa [Fchain] using this

/-- 元素互异：n < m ⟹ aₙ ≠ aₘ。 -/
lemma Fchain_distinct (c : α → α → Prop) (A : Set α) (hA : A.Infinite) :
    ∀ {n m : ℕ}, n < m → (Fchain c A hA n).1.a ≠ (Fchain c A hA m).1.a := by
  intro n m hnm
  have hmem : (Fchain c A hA m).1.a ∈ (Fchain c A hA (n + 1)).1.B := by
    by_cases h : n + 1 < m
    · exact (Fchain_B_sub c A hA h) (Fchain c A hA m).1.hmem
    · have hEq : n + 1 = m := by omega
      subst m
      exact (Fchain c A hA (n + 1)).1.hmem
  intro hEq
  have hnsub : (Fchain c A hA m).1.a ∈ (Fchain c A hA n).1.B \ {(Fchain c A hA n).1.a} :=
    (Fchain_step_sub c A hA n) hmem
  exact hnsub.2 hEq.symm

/-- 主定理（无限 Ramsey，2 色）：无限集上的**对称**二元染色存在无限单色子集。 -/
theorem exists_infinite_mono (c : α → α → Prop) (hsym : Symmetric c) {A : Set α} (hA : A.Infinite) :
    (∃ S ⊆ A, S.Infinite ∧ ∀ ⦃x y⦄, x ∈ S → y ∈ S → x ≠ y → c x y) ∨
    (∃ S ⊆ A, S.Infinite ∧ ∀ ⦃x y⦄, x ∈ S → y ∈ S → x ≠ y → ¬ c x y) := by
  classical
  let F := Fchain c A hA
  let I : Set ℕ := {n : ℕ | (F (n + 1)).2}
  by_cases hI : I.Infinite
  · let S : Set α := (fun n : ℕ => (F n).1.a) '' I
    refine Or.inl ⟨S, ?_, ?_, ?_⟩
    · intro x hx
      rcases hx with ⟨n, hn, rfl⟩
      exact Fchain_mem_A c A hA n
    · have hInjOn : Set.InjOn (fun n : ℕ => (F n).1.a) I := by
        intro n _ m _ hEq
        by_cases h : n < m
        · exact False.elim (Fchain_distinct c A hA h hEq)
        · by_cases h' : m < n
          · exact False.elim (Fchain_distinct c A hA h' hEq.symm)
          · omega
      exact Set.Infinite.image hInjOn hI
    · intro x y hx hy hne
      rcases hx with ⟨n, hn, rfl⟩
      rcases hy with ⟨m, hm, rfl⟩
      by_cases hnm : n < m
      · have ha_m : (F m).1.a ∈ (F (n + 1)).1.B := by
          by_cases h : n + 1 < m
          · exact (Fchain_B_sub c A hA h) (Fchain c A hA m).1.hmem
          · have hEq : n + 1 = m := by omega
            subst m
            exact (Fchain c A hA (n + 1)).1.hmem
        have hcol : (F (n + 1)).2 := by simpa [I, F] using hn
        exact (Fchain_color c A hA n (F m).1.a ha_m).2 hcol
      · by_cases hmn : m < n
        · have ha_n : (F n).1.a ∈ (F (m + 1)).1.B := by
            by_cases h : m + 1 < n
            · exact (Fchain_B_sub c A hA h) (Fchain c A hA n).1.hmem
            · have hEq : m + 1 = n := by omega
              subst n
              exact (Fchain c A hA (m + 1)).1.hmem
          have hcol : (F (m + 1)).2 := by simpa [I, F] using hm
          exact hsym ((Fchain_color c A hA m (F n).1.a ha_n).2 hcol)
        · have hEq : n = m := by omega
          subst m
          exact False.elim (hne rfl)
  · let J : Set ℕ := {n : ℕ | ¬ (F (n + 1)).2}
    have hIcov : I ∪ J = Set.univ := by
      ext n
      by_cases h : (F (n + 1)).2
      · simp [I, J, h]
      · simp [I, J, h]
    have hJinf : J.Infinite := by
      intro hJfin
      have hIfin : I.Finite := Classical.not_not.mp hI
      have hunivFin : (Set.univ : Set ℕ).Finite := by
        rw [← hIcov]
        exact hIfin.union hJfin
      exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) hunivFin
    let S : Set α := (fun n : ℕ => (F n).1.a) '' J
    refine Or.inr ⟨S, ?_, ?_, ?_⟩
    · intro x hx
      rcases hx with ⟨n, hn, rfl⟩
      exact Fchain_mem_A c A hA n
    · have hInjOn : Set.InjOn (fun n : ℕ => (F n).1.a) J := by
        intro n _ m _ hEq
        by_cases h : n < m
        · exact False.elim (Fchain_distinct c A hA h hEq)
        · by_cases h' : m < n
          · exact False.elim (Fchain_distinct c A hA h' hEq.symm)
          · omega
      exact Set.Infinite.image hInjOn hJinf
    · intro x y hx hy hne
      rcases hx with ⟨n, hn, rfl⟩
      rcases hy with ⟨m, hm, rfl⟩
      by_cases hnm : n < m
      · have ha_m : (F m).1.a ∈ (F (n + 1)).1.B := by
          by_cases h : n + 1 < m
          · exact (Fchain_B_sub c A hA h) (Fchain c A hA m).1.hmem
          · have hEq : n + 1 = m := by omega
            subst m
            exact (Fchain c A hA (n + 1)).1.hmem
        have hcol : ¬ (F (n + 1)).2 := by simpa [J, F] using hn
        have hc : ¬ c (F n).1.a (F m).1.a := by
          intro hcm
          exact hcol ((Fchain_color c A hA n (F m).1.a ha_m).1 hcm)
        exact hc
      · by_cases hmn : m < n
        · have ha_n : (F n).1.a ∈ (F (m + 1)).1.B := by
            by_cases h : m + 1 < n
            · exact (Fchain_B_sub c A hA h) (Fchain c A hA n).1.hmem
            · have hEq : m + 1 = n := by omega
              subst n
              exact (Fchain c A hA (m + 1)).1.hmem
          have hcol : ¬ (F (m + 1)).2 := by simpa [J, F] using hm
          have hc : ¬ c (F m).1.a (F n).1.a := by
            intro hcm
            exact hcol ((Fchain_color c A hA m (F n).1.a ha_n).1 hcm)
          exact fun h => hc (hsym h)
        · have hEq : n = m := by omega
          subst m
          exact False.elim (hne rfl)

end Jsp125Ramsey