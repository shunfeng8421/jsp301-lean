import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Set.Pairwise.Basic

open Set

/-!
# JSP-000125 — 两两不交换子集有界 ⇒ 有限个阿贝尔子群覆盖

数学路线（2026-09-23 R2 修订，对齐 Lecomte 2026 arXiv:2608.20507 Lemma 2.1 结构）：
- L1: 极大两两不交换集 X ⇒ G = ⋃ᵢ C(xᵢ)（中心化子覆盖）            [已证]
- L2: G = ⋃ᵢ C(xᵢ) ⇒ G / Z(G) 有限（Neumann 定理：ω(G) < ∞ ⟹ G/Z(G) 有限，经典）
- L3: G / Z(G) 有限 ⇒ ∃ 有限阿贝尔子群覆盖（每个陪集取 ⟨Z, t⟩，阿贝尔，易）
- 数量界（数学解证据段引用）：Neumann 有限性；Pyber 指数界；Lecomte 2026 锐化 h(n)^{1/n} → √2
-/

namespace Jsp125

variable {G : Type*} [Group G]

/-- 两两不交换子集：任意两个不同元素不交换。 -/
def PairwiseNonComm (X : Set G) : Prop :=
  X.Pairwise (fun a b => ¬ Commute a b)

/-- 阿贝尔子群：子群内任意两元素交换。 -/
def AbelianSubgroup (H : Subgroup G) : Prop :=
  ∀ ⦃a b : G⦄, a ∈ H → b ∈ H → Commute a b

/-- 按包含意义极大的两两不交换集：任意外部元素都至少与 X 中某个元素交换。 -/
def MaximalPairwiseNonComm (X : Set G) : Prop :=
  PairwiseNonComm X ∧ ∀ ⦃g : G⦄, g ∉ X → ∃ x ∈ X, Commute x g

/-- L1: 极大两两不交换集 X ⇒ G = ⋃ᵢ C(xᵢ)（中心化子覆盖）。 -/
lemma centralizer_cover (X : Set G) (hX : MaximalPairwiseNonComm X) :
    ∀ g : G, ∃ x ∈ X, g ∈ Subgroup.centralizer ({x} : Set G) := by
  intro g
  by_cases hg : g ∈ X
  · refine ⟨g, hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [mem_singleton_iff] at hm
    subst m
    rfl
  · rcases hX.2 hg with ⟨x, hxX, hxg⟩
    refine ⟨x, hxX, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [mem_singleton_iff] at hm
    subst m
    exact hxg

/-- L1 的覆盖等价形式（Set.univ 层面）。 -/
lemma centralizer_cover_univ (X : Set G) (hX : MaximalPairwiseNonComm X) :
    (⋃ x ∈ X, (Subgroup.centralizer ({x} : Set G) : Set G)) = univ := by
  rw [Set.eq_univ_iff_forall]
  intro g
  simpa using centralizer_cover X hX g

end Jsp125
