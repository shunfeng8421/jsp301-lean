import Mathlib.Data.Set.Card
import Rl1
import Rl3

open Set

universe u

namespace Jsp125

variable {G : Type u} [Group G]

/-- RL4a（Theorem 6 组装，主定理方向）：两两不交换集 encard 有界（≤ k）⟹ FIZ（G/Z(G) 有限）。
反证：¬FIZ 时 RL1+RL3 给出长度 k+1 的两两不交换序列 a，
其像集 (range a) 两两不交换且 encard = k+1，与界 k 矛盾。 -/
lemma bounded_imp_fiz (hB : ∃ k : ℕ, ∀ X : Set G, PairwiseNonComm X → X.encard ≤ (k : ℕ∞)) :
    (Subgroup.center G).FiniteIndex := by
  rcases hB with ⟨k, hk⟩
  by_contra hnotFIZ
  have hPE : ∀ X : Set G, X.Infinite → ¬ PairwiseNonComm X := by
    intro X hinf hnc
    have hle : X.encard ≤ (k : ℕ∞) := hk X hnc
    have htop : X.encard = ⊤ := hinf.encard_eq
    rw [htop] at hle
    exact (by simp : ¬ (⊤ : ℕ∞) ≤ (k : ℕ∞)) hle
  have hFC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).FiniteIndex := pe_imp_fc hPE
  rcases fc_not_fiz_pairwise_any hFC hnotFIZ (k + 1) with ⟨a, ha⟩
  have hainj : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact ha i j hne (by simp [hij] : Commute (a i) (a j))
  have her : (Set.range a).encard = ENat.card (Fin (k + 1)) := hainj.encard_range
  have hcard : ENat.card (Fin (k + 1)) = (k + 1 : ℕ∞) := by
    rw [ENat.card_eq_coe_fintype_card]
    simp
  have hr : (Set.range a).encard = (k + 1 : ℕ∞) := by rw [her, hcard]
  have hpnr : PairwiseNonComm (Set.range a) := by
    change (Set.range a).Pairwise (fun x y => ¬ Commute x y)
    intro x hx y hy hxy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    exact ha i j (by intro hij; exact hxy (congrArg a hij))
  have hle2 : (Set.range a).encard ≤ (k : ℕ∞) := hk (Set.range a) hpnr
  rw [hr] at hle2
  have hle3 : k + 1 ≤ k := ENat.natCast_le_natCast.mp hle2
  exact (Nat.not_succ_le_self k) hle3

/-- RL4b（Theorem 6 反向）：FIZ（G/Z(G) 有限）⟹ PE（不存在无限两两不交换集）。
证明：商映射 G → G/Z(G) 在任意两两不交换集 X 上单射
（xZ = yZ ⟹ x⁻¹y ∈ Z ⟹ Commute x y ⟹ x = y，因 PNC 给出 x ≠ y ⟹ ¬Commute），
故 X 的像是 univ（有限）的子集，有限，与 X 无限矛盾。 -/
lemma fiz_imp_pe (hFIZ : (Subgroup.center G).FiniteIndex) :
    ∀ X : Set G, X.Infinite → ¬ PairwiseNonComm X := by
  intro X hinf hnc
  let φ : G → G ⧸ Subgroup.center G := fun g => ⟦g⟧
  have hinj : Set.InjOn φ X := by
    intro x hx y hy heq
    have hxy : x⁻¹ * y ∈ Subgroup.center G := by
      simpa [QuotientGroup.leftRel_apply] using (Quotient.exact heq)
    have hcomm : Commute x y := by
      rw [Commute]
      have hz : ∀ g : G, g * (x⁻¹ * y) = (x⁻¹ * y) * g := Subgroup.mem_center_iff.mp hxy
      have h1 := hz x
      have hxinv : x * (x⁻¹ * y) = y := by group
      rw [hxinv] at h1
      calc
        x * y = x * ((x⁻¹ * y) * x) := by rw [← h1]
        _ = y * x := by group
    by_contra hne
    exact (hnc hx hy hne) hcomm
  have him : (φ '' X).Infinite := Set.Infinite.image hinj hinf
  have hFinQ : Finite (G ⧸ Subgroup.center G) := Subgroup.finiteIndex_iff_finite_quotient.mp hFIZ
  letI := hFinQ
  have huniv : (Set.univ : Set (G ⧸ Subgroup.center G)).Finite := Set.finite_univ
  have hsub : φ '' X ⊆ Set.univ := by
    intro y hy
    exact Set.mem_univ y
  have hfin : (φ '' X).Finite := huniv.subset hsub
  exact hfin.not_infinite him

/-- 由中心与单个元素生成的阿贝尔子群：⟨Z(G), r⟩ = {z·rⁿ | z ∈ Z(G), n ∈ ℤ}。
Z(G) 元素与 r 交换 ⟹ 元素形如 z·rⁿ 且两两交换。 -/
def Zr (r : G) : Subgroup G where
  carrier := {x : G | ∃ z : G, z ∈ Subgroup.center G ∧ ∃ n : ℤ, x = z * r ^ n}
  one_mem' := ⟨1, Subgroup.one_mem _, 0, by simp⟩
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨zx, hzx, nx, rfl⟩
    rcases hy with ⟨zy, hzy, ny, rfl⟩
    refine ⟨zx * zy, Subgroup.mul_mem _ hzx hzy, nx + ny, ?_⟩
    calc
      (zx * r ^ nx) * (zy * r ^ ny) = zx * (r ^ nx * zy) * r ^ ny := by group
      _ = zx * (zy * r ^ nx) * r ^ ny := by
        rw [(Subgroup.mem_center_iff.mp hzy) (r ^ nx)]
      _ = (zx * zy) * r ^ (nx + ny) := by group
  inv_mem' := by
    intro x hx
    rcases hx with ⟨z, hz, n, rfl⟩
    refine ⟨z⁻¹, Subgroup.inv_mem _ hz, -n, ?_⟩
    calc
      (z * r ^ n)⁻¹ = r ^ (-n) * z⁻¹ := by group
      _ = z⁻¹ * r ^ (-n) := by
        rw [(Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz)) (r ^ (-n))]

/-- Zr r 是阿贝尔子群。 -/
lemma Zr_abelian (r : G) : AbelianSubgroup (Zr r) := by
  intro a b ha hb
  rcases ha with ⟨za, hza, na, rfl⟩
  rcases hb with ⟨zb, hzb, nb, rfl⟩
  rw [Commute]
  calc
    (za * r ^ na) * (zb * r ^ nb) = (za * zb) * r ^ (na + nb) := by
      calc
        (za * r ^ na) * (zb * r ^ nb) = za * (r ^ na * zb) * r ^ nb := by group
        _ = za * (zb * r ^ na) * r ^ nb := by
          rw [(Subgroup.mem_center_iff.mp hzb) (r ^ na)]
        _ = (za * zb) * r ^ (na + nb) := by group
    _ = (zb * za) * r ^ (nb + na) := by
      rw [(Subgroup.mem_center_iff.mp hzb) za]
      rw [Int.add_comm na nb]
    _ = (zb * r ^ nb) * (za * r ^ na) := by
      calc
        (zb * za) * r ^ (nb + na) = (zb * za) * (r ^ nb * r ^ na) := by rw [zpow_add]
        _ = zb * (za * r ^ nb) * r ^ na := by group
        _ = zb * (r ^ nb * za) * r ^ na := by
          rw [(Subgroup.mem_center_iff.mp hza) (r ^ nb)]
        _ = (zb * r ^ nb) * (za * r ^ na) := by group

/-- RL4c（L3/Theorem 6 的覆盖结论）：FIZ ⟹ 有限个阿贝尔子群覆盖 G。
代表集 r ∈ range (Quotient.out)（有限，range_out_finite），
每个代表对应阿贝尔子群 Zr r，陪集分解 g = r·a（a ∈ Z）给出 g ∈ Zr r。 -/
lemma fiz_imp_abelian_cover (hFIZ : (Subgroup.center G).FiniteIndex) :
    ∃ S : Finset (Subgroup G), (∀ H ∈ S, AbelianSubgroup H) ∧ ∀ g : G, ∃ H ∈ S, g ∈ H := by
  classical
  let Z : Subgroup G := Subgroup.center G
  refine ⟨(range_out_finite Z hFIZ).toFinset.image (fun r : G => Zr r), ?_, ?_⟩
  · intro H hH
    rcases (Finset.mem_image.mp hH) with ⟨r, hrS, rfl⟩
    exact Zr_abelian r
  · intro g
    rcases coset_decompose Z hFIZ g with ⟨r, hr, a, ha, rfl⟩
    refine ⟨Zr r, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨r, (range_out_finite Z hFIZ).mem_toFinset.mpr hr, rfl⟩
    · refine ⟨a, ha, 1, ?_⟩
      calc
        r * a = a * r := (Subgroup.mem_center_iff.mp ha) r
        _ = a * r ^ (1 : ℤ) := by rw [zpow_one]

end Jsp125