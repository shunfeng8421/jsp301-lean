import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Center
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Ramsey125
import Jsp125

open Set

universe u

namespace Jsp125

variable {G : Type u} [Group G]

/-- 核心等式 (3a)：s,t 的 g 共轭相等 ⟺ s*t⁻¹ ∈ C(g)。 -/
lemma conj_eq_iff (g s t : G) :
    s⁻¹ * g * s = t⁻¹ * g * t ↔ (s * t⁻¹) ∈ Subgroup.centralizer ({g} : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    simp at hm
    subst m
    have h1 : g * s = s * (t⁻¹ * g * t) := by
      calc g * s = s * (s⁻¹ * g * s) := by group
           _ = s * (t⁻¹ * g * t) := by rw [h]
    calc
      g * (s * t⁻¹) = g * s * t⁻¹ := by group
      _ = (s * (t⁻¹ * g * t)) * t⁻¹ := by rw [h1]
      _ = s * t⁻¹ * g := by group
      _ = (s * t⁻¹) * g := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc
    have h1 : (s * t⁻¹) * g = g * (s * t⁻¹) := by
      exact (hc g (by simp)).symm
    calc
      s⁻¹ * g * s = s⁻¹ * g * (s * t⁻¹) * t := by group
      _ = s⁻¹ * (g * (s * t⁻¹)) * t := by group
      _ = s⁻¹ * ((s * t⁻¹) * g) * t := by rw [← h1]
      _ = (s⁻¹ * (s * t⁻¹)) * g * t := by group
      _ = t⁻¹ * g * t := by group

/-- 核心等式 (3b)：u,v 交换 且 g·u,g·v 交换 ⟹ u⁻¹gu = v⁻¹gv。 -/
lemma conj_eq_of_commute {g u v : G} (huv : Commute u v)
    (hgu : Commute (g * u) (g * v)) : u⁻¹ * g * u = v⁻¹ * g * v := by
  have h1 : u * g * v = v * g * u := by
    calc
      u * g * v = g⁻¹ * ((g * u) * (g * v)) := by group
      _ = g⁻¹ * ((g * v) * (g * u)) := by rw [hgu]
      _ = v * g * u := by group
  have h2 : v⁻¹ * (u * g) = (g * u) * v⁻¹ := by
    calc v⁻¹ * (u * g) = v⁻¹ * (u * g * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * g * u) * v⁻¹ := by rw [h1]
        _ = g * u * v⁻¹ := by group
  have huv1 : v⁻¹ * (u * v) = u := by
    calc v⁻¹ * (u * v) = v⁻¹ * (v * u) := by rw [huv]
        _ = u := by group
  have huv2 : v⁻¹ * u = u * v⁻¹ := by
    calc v⁻¹ * u = v⁻¹ * (u * v) * v⁻¹ := by group
        _ = u * v⁻¹ := by rw [huv1]
  have h3 : (u * v⁻¹) * g = g * (u * v⁻¹) := by
    calc (u * v⁻¹) * g = v⁻¹ * u * g := by rw [← huv2]
        _ = v⁻¹ * (u * g) := by group
        _ = (g * u) * v⁻¹ := h2
        _ = g * (u * v⁻¹) := by group
  calc
    u⁻¹ * g * u = u⁻¹ * (g * (u * v⁻¹)) * v := by group
    _ = u⁻¹ * ((u * v⁻¹) * g) * v := by rw [← h3]
    _ = v⁻¹ * g * v := by group

/-- 横截引理：C(g) 无限指数 ⟹ 无限集 T，其元素 g 共轭两两互异。 -/
lemma infinite_distinct_conjugates (g : G)
    (hfc : ¬ Finite (G ⧸ Subgroup.centralizer ({g} : Set G))) :
    let T : Set G := (fun t : G => t⁻¹) '' Set.range
        (Quotient.out : G ⧸ Subgroup.centralizer ({g} : Set G) → G)
    T.Infinite ∧ ∀ ⦃s t⦄, s ∈ T → t ∈ T → s ≠ t → s⁻¹ * g * s ≠ t⁻¹ * g * t := by
  let H : Subgroup G := Subgroup.centralizer ({g} : Set G)
  intro T
  constructor
  · have hOutInj : Function.Injective (Quotient.out : G ⧸ H → G) := by
      intro q1 q2 h
      rw [← Quotient.out_eq q1, ← Quotient.out_eq q2, h]
    have hInf : Infinite (G ⧸ H) := by
      rcases finite_or_infinite (G ⧸ H) with hfin | hinf
      · exact False.elim (hfc hfin)
      · exact hinf
    haveI : Infinite (G ⧸ H) := hInf
    have hUnivInf : (Set.univ : Set (G ⧸ H)).Infinite := Set.infinite_univ
    have hInjOnOut : Set.InjOn (Quotient.out : G ⧸ H → G) Set.univ := by
      intro a _ b _ h
      exact hOutInj h
    have hROutInf : (Set.range (Quotient.out : G ⧸ H → G)).Infinite := by
      simpa [Set.range] using Set.Infinite.image hInjOnOut hUnivInf
    have hInjOnInv : Set.InjOn (fun t : G => t⁻¹) (Set.range (Quotient.out : G ⧸ H → G)) := by
      intro a _ b _ h
      exact inv_injective h
    simpa [T] using Set.Infinite.image hInjOnInv hROutInf
  · intro s t hs ht hne
    rcases hs with ⟨a, ha, rfl⟩
    rcases ht with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro h
      apply hne
      rw [h]
    intro hconj
    have ha_b : a⁻¹ * b ∈ H := by
      have hs' : (a⁻¹) * (b⁻¹)⁻¹ ∈ Subgroup.centralizer ({g} : Set G) :=
        (conj_eq_iff g (a⁻¹) (b⁻¹)).mp hconj
      simpa [H] using hs'
    have hq : ⟦a⟧ = ⟦b⟧ := Quotient.sound (s := QuotientGroup.leftRel H)
      (QuotientGroup.leftRel_apply.mpr ha_b)
    rcases ha with ⟨q_a, rfl⟩
    rcases hb with ⟨q_b, rfl⟩
    have hq' : q_a = q_b := by
      have h1 : ⟦Quotient.out q_a⟧ = q_b := by
        rw [hq]
        exact Quotient.out_eq q_b
      exact (Quotient.out_eq q_a).symm.trans h1
    exact hab (congrArg (Quotient.out : G ⧸ H → G) hq')

/-- RL1（Neumann Lemma 1）：PE ⟹ FC。PE = 无不限两两不交换集；FC = 每个元素中心化子有限指数。 -/
theorem pe_imp_fc (hPE : ∀ X : Set G, X.Infinite → ¬ PairwiseNonComm X) :
    ∀ g : G, Subgroup.FiniteIndex (Subgroup.centralizer ({g} : Set G)) := by
  intro g
  by_contra hfc
  have hfc' : ¬ Finite (G ⧸ Subgroup.centralizer ({g} : Set G)) := by
    intro hfin
    apply hfc
    exact Subgroup.finiteIndex_iff_finite_quotient.mpr hfin
  let T : Set G := (fun t : G => t⁻¹) '' Set.range
      (Quotient.out : G ⧸ Subgroup.centralizer ({g} : Set G) → G)
  have hT := infinite_distinct_conjugates g hfc'
  rcases hT with ⟨hTinf, hTconj⟩
  rcases Jsp125Ramsey.exists_infinite_mono (c := Commute) (hsym := by
        intro a b h
        exact h.symm) hTinf with
    ⟨S, hSsub, hSinf, hScliq⟩ | ⟨U, hUsub, hUinf, hUind⟩
  · let gS : Set G := (fun x : G => g * x) '' S
    have hInjOn : Set.InjOn (fun x : G => g * x) S := by
      intro x _ y _ h
      exact mul_left_cancel h
    have hgSinf : gS.Infinite := by
      exact Set.Infinite.image hInjOn hSinf
    have hgSnon : PairwiseNonComm gS := by
      intro a ha b hb hne
      rcases ha with ⟨x, hx, rfl⟩
      rcases hb with ⟨y, hy, rfl⟩
      have hxy : x ≠ y := by
        intro h
        apply hne
        rw [h]
      intro hgu
      have hconjxy : x⁻¹ * g * x = y⁻¹ * g * y :=
        conj_eq_of_commute (hScliq hx hy hxy) hgu
      exact (hTconj (hSsub hx) (hSsub hy) hxy) hconjxy
    exact False.elim (hPE gS hgSinf hgSnon)
  · exact False.elim (hPE U hUinf (by
      intro x hx y hy hne
      exact hUind hx hy hne))

end Jsp125
