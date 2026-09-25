import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Center
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

open Set

universe u

namespace Jsp125

variable {G : Type u} [Group G]

/-- 辅助 1：阿贝尔子群 ≤ 其中心化子。 -/
lemma abel_le_centralizer (A : Subgroup G)
    (hAbel : ∀ a b : G, a ∈ A → b ∈ A → a * b = b * a) :
    A ≤ Subgroup.centralizer (A : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hAbel b a hb ha

/-- 辅助 2：⟦r⟧ = ⟦g⟧ ⟺ r⁻¹g ∈ H（商等式 ↔ 左陪集包含）。 -/
lemma mk_eq_mk_iff (H : Subgroup G) (r g : G) :
    (⟦r⟧ : G ⧸ H) = ⟦g⟧ ↔ r⁻¹ * g ∈ H := by
  constructor
  · intro h
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact h)
  · intro h
    exact Quotient.sound (s := QuotientGroup.leftRel H) (QuotientGroup.leftRel_apply.mpr h)

/-- 辅助 3：Quotient.out 的像集有限（A 有限指数 ⟹ 商有限）。 -/
lemma range_out_finite (A : Subgroup G) (hAfin : A.FiniteIndex) :
    (Set.range (Quotient.out : G ⧸ A → G)).Finite := by
  have hAquot : Finite (G ⧸ A) := Subgroup.finiteIndex_iff_finite_quotient.mp hAfin
  haveI : Finite (G ⧸ A) := hAquot
  have huniv : (Set.univ : Set (G ⧸ A)).Finite := Set.finite_univ
  have him : (Set.image (Quotient.out : G ⧸ A → G) Set.univ).Finite :=
    Set.Finite.image (Quotient.out : G ⧸ A → G) huniv
  simpa [Set.range] using him

/-- 辅助 4：陪集分解 ∀ g, ∃ r ∈ 代表集, ∃ a ∈ A, g = r*a。 -/
lemma coset_decompose (A : Subgroup G) (hAfin : A.FiniteIndex) (g : G) :
    ∃ r : G, r ∈ Set.range (Quotient.out : G ⧸ A → G) ∧ ∃ a : G, a ∈ A ∧ g = r * a := by
  let q : G ⧸ A := (⟦g⟧ : G ⧸ A)
  let r : G := Quotient.out q
  refine ⟨r, ⟨q, rfl⟩, ⟨r⁻¹ * g, ?_, ?_⟩⟩
  · have hq : (⟦r⟧ : G ⧸ A) = (⟦g⟧ : G ⧸ A) := by
      change (⟦Quotient.out (⟦g⟧ : G ⧸ A)⟧ : G ⧸ A) = (⟦g⟧ : G ⧸ A)
      exact Quotient.out_eq _
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  · group

/-- 辅助 5：iInf 记法桥（`⨅ r ∈ s, f r` 与 subtype iInf 同集合）。 -/
lemma iInf_mem_eq (s : Finset G) (f : G → Subgroup G) :
    (⨅ r ∈ s, f r) = ⨅ r : {r : G // r ∈ s}, f r.1 := by
  ext x
  simp [Subgroup.mem_iInf]

/-- 辅助 6：Z(G) = C(A) ⊓ ⋂_{r∈S} C(r)，S 为 A 的陪集代表有限集。 -/
lemma center_eq (A : Subgroup G) (hAfin : A.FiniteIndex) :
    Subgroup.center G =
      Subgroup.centralizer (A : Set G) ⊓
        (⨅ r : {r : G // r ∈ (range_out_finite A hAfin).toFinset},
          Subgroup.centralizer ({r.1} : Set G)) := by
  ext x
  constructor
  · intro hx
    constructor
    · exact Subgroup.mem_centralizer_iff.mpr (by
        intro a ha
        exact Subgroup.mem_center_iff.mp hx a)
    · exact Subgroup.mem_iInf.mpr (fun r => by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        simp at ha
        rw [ha]
        exact Subgroup.mem_center_iff.mp hx r.1)
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro g
    rcases coset_decompose A hAfin g with ⟨r, hr, a, ha, rfl⟩
    have hxr0 : x ∈ Subgroup.centralizer ({r} : Set G) := by
      exact (Subgroup.mem_iInf.mp hx.2) ⟨r, (range_out_finite A hAfin).mem_toFinset.mpr hr⟩
    have hxr : r * x = x * r :=
      (Subgroup.mem_centralizer_iff.mp hxr0) r (by simp)
    have hxa : a * x = x * a :=
      (Subgroup.mem_centralizer_iff.mp hx.1) a ha
    calc
      (r * a) * x = r * (a * x) := by group
      _ = r * (x * a) := by rw [hxa]
      _ = (r * x) * a := by group
      _ = (x * r) * a := by rw [hxr]
      _ = x * (r * a) := by group

/-- RL2（Neumann Lemma 2）：FC + 有限指数阿贝尔子群 ⟹ G/Z(G) 有限。 -/
theorem rl2 (hFC : ∀ g : G, Subgroup.FiniteIndex (Subgroup.centralizer ({g} : Set G)))
    (A : Subgroup G) (hAfin : A.FiniteIndex)
    (hAbel : ∀ a b : G, a ∈ A → b ∈ A → a * b = b * a) :
    Subgroup.FiniteIndex (Subgroup.center G) := by
  let S : Finset G := (range_out_finite A hAfin).toFinset
  haveI : A.FiniteIndex := hAfin
  have hCAfin : (Subgroup.centralizer (A : Set G)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (abel_le_centralizer A hAbel)
  have hCSfin : (⨅ r : {r : G // r ∈ S}, Subgroup.centralizer ({r.1} : Set G)).FiniteIndex := by
    exact Subgroup.finiteIndex_iInf (fun r => hFC r.1)
  let ι := Option {r : G // r ∈ S}
  let f : ι → Subgroup G
    | none => Subgroup.centralizer (A : Set G)
    | some r => Subgroup.centralizer ({r.1} : Set G)
  have hfin : (⨅ i : ι, f i).FiniteIndex := by
    exact Subgroup.finiteIndex_iInf (fun i => by
      cases i with
      | none => exact hCAfin
      | some r => exact hFC r.1)
  have hbridge : (⨅ i : ι, f i) = Subgroup.centralizer (A : Set G) ⊓
      (⨅ r : {r : G // r ∈ S}, Subgroup.centralizer ({r.1} : Set G)) := by
    ext x
    constructor
    · intro hx
      have hx' := (Subgroup.mem_iInf.mp hx)
      constructor
      · exact hx' none
      · exact Subgroup.mem_iInf.mpr (fun r => hx' (some r))
    · intro hx
      exact Subgroup.mem_iInf.mpr (fun i => by
        cases i with
        | none => exact hx.1
        | some r => exact (Subgroup.mem_iInf.mp hx.2) r)
  have hcinf : (Subgroup.centralizer (A : Set G) ⊓
      (⨅ r : {r : G // r ∈ S}, Subgroup.centralizer ({r.1} : Set G))).FiniteIndex := by
    rw [← hbridge]
    exact hfin
  rw [center_eq A hAfin]
  exact hcinf

end Jsp125
