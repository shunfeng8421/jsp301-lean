import Jsp125
import RL4

open Set

/-!
# JSP-000125 主定理（合题）

`∀ G [Group G]`，若 G 中任意两两不交换子集的两两不交换子集 encard 有界（≤ k₀），
则 G 可被有限个阿贝尔子群覆盖。

合题：`bounded_imp_fiz hB`（RL4a，Theorem 6 主方向：ω 有界 ⟹ G/Z(G) 有限）
+ `fiz_imp_abelian_cover`（RL4c/L3：FIZ ⟹ 有限阿贝尔覆盖 ⟨Z(G),r⟩）。
-/

namespace Jsp125

variable {G : Type*} [Group G]

/-- **JSP-000125 主定理**：两两不交换子集有界 ⟹ 有限个阿贝尔子群覆盖。 -/
theorem jsp000125 (hB : ∃ k : ℕ, ∀ X : Set G, PairwiseNonComm X → X.encard ≤ (k : ℕ∞)) :
    ∃ S : Finset (Subgroup G), (∀ H ∈ S, AbelianSubgroup H) ∧ ∀ g : G, ∃ H ∈ S, g ∈ H := by
  exact fiz_imp_abelian_cover (bounded_imp_fiz hB)

end Jsp125