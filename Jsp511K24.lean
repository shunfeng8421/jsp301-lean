import Jsp511M10
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

namespace Jsp511

/-- K_{2,4}：二分完全图，左部 2 顶点、右部 4 顶点，左右部间全连。 -/
abbrev K24 : SimpleGraph (Sum (Fin 2) (Fin 4)) :=
  completeBipartiteGraph (Fin 2) (Fin 4)

/-- 2-列表反例：左部两顶点给 {0,1} / {2,3}；右部四顶点给 2×2 网格的
  全部四种组合 {0,2},{0,3},{1,2},{1,3}（任一 (a,b) ∈ {0,1}×{2,3} 都有一
  个右部顶点列表恰为 {a,b}，从而该顶点无法与两个左部邻点同时异色）。 -/
def K24Lists : Sum (Fin 2) (Fin 4) → Finset (Fin 4)
  | Sum.inl i => if i = 0 then ({0, 1} : Finset (Fin 4)) else ({2, 3} : Finset (Fin 4))
  | Sum.inr j =>
      if j.val = 0 then ({0, 2} : Finset (Fin 4))
      else if j.val = 1 then ({0, 3} : Finset (Fin 4))
      else if j.val = 2 then ({1, 2} : Finset (Fin 4))
      else ({1, 3} : Finset (Fin 4))

theorem K24Lists_card : ∀ v : Sum (Fin 2) (Fin 4), (K24Lists v).card = 2 := by
  intro v
  rcases v with i | j
  · by_cases h : i = 0 <;> simp [K24Lists, h]
  · have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases hj with hj | hj | hj | hj <;> simp [K24Lists, hj]

/-- **K_{2,4} 不是 2-可选择性**（Erdős–Rubin–Taylor 经典反例），
  故 `3` 是平面二分图可选择性常数的最佳值：2 不足以保证可列表染色。 -/
theorem not_two_choosable_K24 : ¬ Choosable K24 2 := by
  intro hch
  rcases hch (α := Fin 4) K24Lists K24Lists_card with ⟨c, hmem, hadj⟩
  have ha : c (Sum.inl 0) = 0 ∨ c (Sum.inl 0) = 1 := by
    have h := hmem (Sum.inl 0)
    simp [K24Lists] at h
    exact h
  have hb : c (Sum.inl 1) = 2 ∨ c (Sum.inl 1) = 3 := by
    have h := hmem (Sum.inl 1)
    simp [K24Lists] at h
    exact h
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · let j : Fin 4 := ⟨0, by decide⟩
      have hcj : c (Sum.inr j) = c (Sum.inl 0) ∨ c (Sum.inr j) = c (Sum.inl 1) := by
        simpa [K24Lists, j, ← ha, ← hb] using hmem (Sum.inr j)
      rcases hcj with hc1 | hc2
      · exact (hadj (by simp [K24, j])) hc1.symm
      · exact (hadj (by simp [K24, j])) hc2.symm
    · let j : Fin 4 := ⟨1, by decide⟩
      have hcj : c (Sum.inr j) = c (Sum.inl 0) ∨ c (Sum.inr j) = c (Sum.inl 1) := by
        simpa [K24Lists, j, ← ha, ← hb] using hmem (Sum.inr j)
      rcases hcj with hc1 | hc2
      · exact (hadj (by simp [K24, j])) hc1.symm
      · exact (hadj (by simp [K24, j])) hc2.symm
  · rcases hb with hb | hb
    · let j : Fin 4 := ⟨2, by decide⟩
      have hcj : c (Sum.inr j) = c (Sum.inl 0) ∨ c (Sum.inr j) = c (Sum.inl 1) := by
        simpa [K24Lists, j, ← ha, ← hb] using hmem (Sum.inr j)
      rcases hcj with hc1 | hc2
      · exact (hadj (by simp [K24, j])) hc1.symm
      · exact (hadj (by simp [K24, j])) hc2.symm
    · let j : Fin 4 := ⟨3, by decide⟩
      have hcj : c (Sum.inr j) = c (Sum.inl 0) ∨ c (Sum.inr j) = c (Sum.inl 1) := by
        simpa [K24Lists, j, ← ha, ← hb] using hmem (Sum.inr j)
      rcases hcj with hc1 | hc2
      · exact (hadj (by simp [K24, j])) hc1.symm
      · exact (hadj (by simp [K24, j])) hc2.symm

end Jsp511
