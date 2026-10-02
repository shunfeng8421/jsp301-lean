import Jsp511AtCore
import Jsp511M8
import Mathlib.Combinatorics.Hall.Basic

/-! ## JSP-000511 M7: sparse graphs admit bounded-outdegree orientations

Alon--Tarsi 1992, Lemma 3.1 (the direction we need):
`G` is `d`-sparse (every edge set of `G` has at most `d * |vertices(H)|` edges)
implies `G` admits an orientation with out-degree at most `d` at every vertex.

We prove this via Hall's theorem (b-matching): match each canonical edge
`e = (u,v)` (with `u < v`) to one of the `2d` slots `(u,i)`, `(v,i)`; the
matched endpoint becomes the **tail** of the oriented edge.  Injectivity of the
matching bounds the out-degree by `d`, and sparsity is exactly Hall's condition
for this b-matching.

Then the M8 assembly: bipartite + `d`-sparse  =>  `(d+1)`-choosable.

(The vertex type is assumed linearly ordered only to pick canonical (u,v), u < v,
representatives of undirected edges; every finite vertex set can be so ordered.)
-/

namespace Jsp511

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The set of vertices incident with an edge set: union of all endpoints. -/
def vertOf (H : Finset (V × V)) : Finset V :=
  H.image Prod.fst ∪ H.image Prod.snd

/-- `G` is `d`-**sparse**: every set of edges of `G` has size at most
  `d` times the size of its incident vertex set. -/
def Sparse (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ H : Finset (V × V), (∀ e ∈ H, G.Adj e.1 e.2) → H.card ≤ d * (vertOf H).card

section M7

variable (G : SimpleGraph V) [DecidableRel G.Adj] [LinearOrder V]

/-- The `2d` vertex-copies of the two endpoints of an ordered pair (the
  b-matching neighborhood of the edge); a copy `(v, i)` means "the `i`-th
  capacity slot of vertex `v`". -/
def copyFinset (d : ℕ) (e : V × V) : Finset (V × Fin d) :=
  (({e.1} : Finset V).product (Finset.univ : Finset (Fin d))) ∪
    (({e.2} : Finset V).product (Finset.univ : Finset (Fin d)))

omit [Fintype V] [LinearOrder V] in
private lemma copyFinset_mem_iff (d : ℕ) (e : V × V) (c : V × Fin d) :
    c ∈ copyFinset d e ↔ c.1 = e.1 ∨ c.1 = e.2 := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Or.inl (by simpa using (Finset.mem_product.mp h).1)
    · exact Or.inr (by simpa using (Finset.mem_product.mp h).1)
  · intro h
    unfold copyFinset
    rcases h with h | h
    · exact Finset.mem_union_left (({e.2} : Finset V).product (Finset.univ : Finset (Fin d)))
        (Finset.mem_product.mpr ⟨by simpa using h, Finset.mem_univ _⟩)
    · exact Finset.mem_union_right (({e.1} : Finset V).product (Finset.univ : Finset (Fin d)))
        (Finset.mem_product.mpr ⟨by simpa using h, Finset.mem_univ _⟩)

/-- The pair contributed by one canonical edge under a Hall matching. -/
def contribution (E : Finset (V × V)) (f : {e : V × V // e ∈ E} → V × Fin d)
    (e : {e : V × V // e ∈ E}) : Finset (V × V) :=
  if (f e).1 = e.1.1 then ({e.1} : Finset (V × V)) else ({e.1.swap} : Finset (V × V))

/-- The orientation produced by a Hall-matching: each canonical edge is directed
  from its matched endpoint (its "tail") toward the other endpoint. -/
def orientationOf (E : Finset (V × V)) (f : {e : V × V // e ∈ E} → V × Fin d) :
    Finset (V × V) :=
  E.attach.biUnion fun e => contribution E f e

omit [Fintype V] [LinearOrder V] in
private lemma contribution_mem (E : Finset (V × V))
    (f : {e : V × V // e ∈ E} → V × Fin d) (e : {e : V × V // e ∈ E}) (p : V × V) :
    p ∈ contribution E f e ↔ p = (if (f e).1 = e.1.1 then e.1 else e.1.swap) := by
  by_cases h : (f e).1 = e.1.1 <;> simp [contribution, h]

/-- Hall's condition for the b-matching, from sparsity. -/
private lemma hall_condition (d : ℕ) (hsp : Sparse G d) :
    let E : Finset (V × V) := Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2 ∧ e.1 < e.2)
    let t : {e : V × V // e ∈ E} → Finset (V × Fin d) := fun e => copyFinset d e.1
    ∀ s : Finset {e : V × V // e ∈ E}, s.card ≤ (s.biUnion t).card := by
  classical
  intro E t s
  let F : Finset (V × V) := s.image (fun e : {e : V × V // e ∈ E} => e.1)
  have hFadj : ∀ e ∈ F, G.Adj e.1 e.2 := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e0, he0, rfl⟩
    exact (Finset.mem_filter.mp e0.2).2.1
  have hspF := hsp F hFadj
  have hcard_s : s.card = F.card := by
    exact (Finset.card_image_of_injective s (fun a b h => Subtype.ext h)).symm
  have hcard_bi : s.biUnion t = (vertOf F).product (Finset.univ : Finset (Fin d)) := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_biUnion.mp hc with ⟨e, he, hce⟩
      have hc' : c.1 = e.1.1 ∨ c.1 = e.1.2 := (copyFinset_mem_iff d e.1 c).mp hce
      rcases hc' with h | h
      · have hf : c.1 ∈ F.image Prod.fst := by
          refine Finset.mem_image.mpr ⟨e.1, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
          · exact h.symm
        refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ c.2⟩
        change c.1 ∈ F.image Prod.fst ∪ F.image Prod.snd
        exact Finset.mem_union_left (F.image Prod.snd) hf
      · have hf : c.1 ∈ F.image Prod.snd := by
          refine Finset.mem_image.mpr ⟨e.1, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
          · exact h.symm
        refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ c.2⟩
        change c.1 ∈ F.image Prod.fst ∪ F.image Prod.snd
        exact Finset.mem_union_right (F.image Prod.fst) hf
    · intro hc
      rcases Finset.mem_product.mp hc with ⟨hcv, _⟩
      change c.1 ∈ F.image Prod.fst ∪ F.image Prod.snd at hcv
      rcases Finset.mem_union.mp hcv with hcv | hcv
      · rcases Finset.mem_image.mp hcv with ⟨e0, he0, hfst⟩
        rcases Finset.mem_image.mp he0 with ⟨e, he, hpair⟩
        refine Finset.mem_biUnion.mpr ⟨e, he, ?_⟩
        have hc1 : c.1 = e.1.1 := by
          calc
            c.1 = Prod.fst e0 := hfst.symm
            _ = Prod.fst e.1 := by rw [← hpair]
            _ = e.1.1 := rfl
        exact (copyFinset_mem_iff d e.1 c).mpr (Or.inl hc1)
      · rcases Finset.mem_image.mp hcv with ⟨e0, he0, hsnd⟩
        rcases Finset.mem_image.mp he0 with ⟨e, he, hpair⟩
        refine Finset.mem_biUnion.mpr ⟨e, he, ?_⟩
        have hc2 : c.1 = e.1.2 := by
          calc
            c.1 = Prod.snd e0 := hsnd.symm
            _ = Prod.snd e.1 := by rw [← hpair]
            _ = e.1.2 := rfl
        exact (copyFinset_mem_iff d e.1 c).mpr (Or.inr hc2)
  have hcard_prod : ((vertOf F).product (Finset.univ : Finset (Fin d))).card =
      (vertOf F).card * d := by
    simp
  calc
    s.card = F.card := hcard_s
    _ ≤ d * (vertOf F).card := hspF
    _ = (vertOf F).card * d := by rw [Nat.mul_comm]
    _ = ((vertOf F).product (Finset.univ : Finset (Fin d))).card := hcard_prod.symm
    _ = (s.biUnion t).card := by rw [hcard_bi]

/-- M7: `d`-sparse graphs have an orientation with out-degree at most `d`. -/
theorem exists_orientation_of_sparse (d : ℕ) (hsp : Sparse G d) :
    ∃ D : Finset (V × V),
      (∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v) ∧
      (∀ ⦃u v⦄, G.Adj u v → ((u, v) ∈ D ↔ (v, u) ∉ D)) ∧
      (∀ v, outdeg D v ≤ d) := by
  classical
  let E : Finset (V × V) := Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2 ∧ e.1 < e.2)
  let ι := {e : V × V // e ∈ E}
  let t : ι → Finset (V × Fin d) := fun e => copyFinset d e.1
  have hhall := Finset.all_card_le_biUnion_card_iff_exists_injective (fun e : ι => t e) |>.mp
    (hall_condition G d hsp)
  obtain ⟨f, hf_inj, hf_mem⟩ := hhall
  set D : Finset (V × V) := orientationOf E f
  have hE_adj : ∀ e : V × V, e ∈ E → G.Adj e.1 e.2 := fun e he =>
    (Finset.mem_filter.mp he).2.1
  have hE_lt : ∀ e : V × V, e ∈ E → e.1 < e.2 := fun e he =>
    (Finset.mem_filter.mp he).2.2
  have hf_head : ∀ e : ι, (f e).1 = e.1.1 ∨ (f e).1 = e.1.2 := by
    intro e
    exact (copyFinset_mem_iff d e.1 (f e)).mp (hf_mem e)
  have hcontrib_first : ∀ (e : ι) (p : V × V), p ∈ contribution E f e → p.1 = (f e).1 := by
    intro e p hp
    by_cases h : (f e).1 = e.1.1
    · have hp' : p = e.1 := by simpa [contribution, h] using hp
      simp [hp', h]
    · have h' : (f e).1 = e.1.2 := by
        rcases hf_head e with hh | hh
        · exact False.elim (h hh)
        · exact hh
      have hp' : p = e.1.swap := by simpa [contribution, h] using hp
      simp [hp', h']
  have hinj_contrib : Function.Injective (fun e : ι => if (f e).1 = e.1.1 then e.1 else e.1.swap) := by
    intro a b h
    have hca : (if (f a).1 = a.1.1 then a.1 else a.1.swap) = a.1 ∨
               (if (f a).1 = a.1.1 then a.1 else a.1.swap) = a.1.swap := by
      by_cases h : (f a).1 = a.1.1 <;> simp [h]
    have hcb : (if (f b).1 = b.1.1 then b.1 else b.1.swap) = b.1 ∨
               (if (f b).1 = b.1.1 then b.1 else b.1.swap) = b.1.swap := by
      by_cases h : (f b).1 = b.1.1 <;> simp [h]
    rcases hca with hca | hca <;> rcases hcb with hcb | hcb
    · apply Subtype.ext
      exact hca.symm.trans (h.trans hcb)
    · apply Subtype.ext
      have hab : a.1 = b.1.swap := hca.symm.trans (h.trans hcb)
      have hlt1 : a.1.1 < a.1.2 := hE_lt a.1 a.2
      have hlt2 : b.1.1 < b.1.2 := hE_lt b.1 b.2
      rcases b with ⟨⟨b1, b2⟩, hbE⟩
      have hab' : a.1 = (b2, b1) := by simpa using hab
      rw [hab'] at hlt1
      exact (lt_asymm hlt2 hlt1).elim
    · apply Subtype.ext
      have hab : a.1.swap = b.1 := hca.symm.trans (h.trans hcb)
      have hlt1 : a.1.1 < a.1.2 := hE_lt a.1 a.2
      have hlt2 : b.1.1 < b.1.2 := hE_lt b.1 b.2
      rcases a with ⟨⟨a1, a2⟩, haE⟩
      have hab' : (a2, a1) = b.1 := by simpa using hab
      rw [← hab'] at hlt2
      exact (lt_asymm hlt1 hlt2).elim
    · apply Subtype.ext
      have hab' : a.1.swap = b.1.swap := hca.symm.trans (h.trans hcb)
      simpa using congrArg Prod.swap hab'
  have hDadj : ∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v := by
    intro u v h
    rcases Finset.mem_biUnion.mp h with ⟨e, he, hee⟩
    by_cases hfst : (f e).1 = e.1.1
    · have hpair : (u, v) = e.1 := by simpa [contribution, hfst] using hee
      have hAdjE : G.Adj e.1.1 e.1.2 := hE_adj e.1 e.2
      simpa [← hpair] using hAdjE
    · have hpair : (u, v) = e.1.swap := by simpa [contribution, hfst] using hee
      have hAdjE : G.Adj e.1.1 e.1.2 := hE_adj e.1 e.2
      have hAdjSw : G.Adj e.1.2 e.1.1 := hAdjE.symm
      have hpair' : e.1 = (v, u) := by simpa using congrArg Prod.swap hpair.symm
      simpa [hpair'] using hAdjSw
  have hD : ∀ ⦃u v⦄, G.Adj u v → ((u, v) ∈ D ↔ (v, u) ∉ D) := by
    intro u v hAdj
    have huv : u ≠ v := by
      intro hsub
      subst hsub
      exact G.loopless.irrefl u hAdj
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · let e : ι := ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ (u, v), ⟨hAdj, hlt⟩⟩⟩
      have h1 : (u, v) ∈ D ↔ (f e).1 = u := by
        constructor
        · intro h
          rcases Finset.mem_biUnion.mp h with ⟨e0, he0, hee⟩
          by_cases hfst : (f e0).1 = e0.1.1
          · have hpair : (u, v) = e0.1 := by simpa [contribution, hfst] using hee
            have he0e : e0 = e := Subtype.ext hpair.symm
            rw [he0e] at hfst
            simpa [e] using hfst
          · have hpair : (u, v) = e0.1.swap := by simpa [contribution, hfst] using hee
            have hlt0 : e0.1.1 < e0.1.2 := hE_lt e0.1 e0.2
            have hvlt : v < u := by
              have hpair' : e0.1 = (v, u) := by simpa using congrArg Prod.swap hpair.symm
              simpa [hpair'] using hlt0
            exact (lt_asymm hlt hvlt).elim
        · intro h
          have hmem : (u, v) ∈ orientationOf E f := by
            refine Finset.mem_biUnion.mpr ⟨e, Finset.mem_attach E e, ?_⟩
            by_cases hfst : (f e).1 = e.1.1
            · simp [contribution, e, hfst]
            · exfalso
              apply hfst
              simpa [e] using h
          simpa [D] using hmem
      have h2 : (v, u) ∈ D ↔ (f e).1 = v := by
        constructor
        · intro h
          rcases Finset.mem_biUnion.mp h with ⟨e0, he0, hee⟩
          by_cases hfst : (f e0).1 = e0.1.1
          · have hpair : (v, u) = e0.1 := by simpa [contribution, hfst] using hee
            have hlt0 : e0.1.1 < e0.1.2 := hE_lt e0.1 e0.2
            have hvlt : v < u := by simpa [hpair.symm] using hlt0
            exact (lt_asymm hlt hvlt).elim
          · have hpair : (v, u) = e0.1.swap := by simpa [contribution, hfst] using hee
            have he0e : e0 = e := by
              apply Subtype.ext
              have hpair' : e0.1 = (u, v) := by simpa using congrArg Prod.swap hpair.symm
              exact hpair'
            have hnot : ¬ (f e).1 = e.1.1 := by
              intro hh
              have hfe0 : ¬ (f e0).1 = e0.1.1 := hfst
              rw [he0e] at hfe0
              exact hfe0 hh
            have hfe : (f e).1 = e.1.2 := by
              rcases hf_head e with hh | hh
              · exact False.elim (hnot hh)
              · exact hh
            simpa [e] using hfe
        · intro h
          have hnot : ¬ (f e).1 = e.1.1 := by
            intro hh
            have hu : u = v := by simpa [e] using hh.symm.trans h
            exact huv hu
          have hmem : (v, u) ∈ orientationOf E f := by
            refine Finset.mem_biUnion.mpr ⟨e, Finset.mem_attach E e, ?_⟩
            by_cases hfst : (f e).1 = e.1.1
            · exfalso
              exact hnot hfst
            · simp [contribution, e, hnot]
          simpa [D] using hmem
      have hmu : (f e).1 = u ∨ (f e).1 = v := by
        rcases hf_head e with hh | hh
        · exact Or.inl (by simpa [e] using hh)
        · exact Or.inr (by simpa [e] using hh)
      constructor
      · intro h1u hv
        have hu : (f e).1 = u := h1.mp h1u
        have hv' : (f e).1 = v := h2.mp hv
        exact huv (hu.symm.trans hv')
      · intro hnotv
        have hnotv' : ¬ (f e).1 = v := by
          intro hv
          exact hnotv (h2.mpr hv)
        have hu : (f e).1 = u := hmu.resolve_right hnotv'
        exact h1.mpr hu
    · let e : ι := ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ (v, u), ⟨hAdj.symm, hgt⟩⟩⟩
      have h1 : (u, v) ∈ D ↔ (f e).1 = u := by
        constructor
        · intro h
          rcases Finset.mem_biUnion.mp h with ⟨e0, he0, hee⟩
          by_cases hfst : (f e0).1 = e0.1.1
          · have hpair : (u, v) = e0.1 := by simpa [contribution, hfst] using hee
            have hlt0 : e0.1.1 < e0.1.2 := hE_lt e0.1 e0.2
            have hvlt : u < v := by simpa [hpair.symm] using hlt0
            exact (lt_asymm hgt hvlt).elim
          · have hpair : (u, v) = e0.1.swap := by simpa [contribution, hfst] using hee
            have he0e : e0 = e := by
              apply Subtype.ext
              have hpair' : e0.1 = (v, u) := by simpa using congrArg Prod.swap hpair.symm
              exact hpair'
            have hnot : ¬ (f e).1 = e.1.1 := by
              intro hh
              have hfe0 : ¬ (f e0).1 = e0.1.1 := hfst
              rw [he0e] at hfe0
              exact hfe0 hh
            have hfe : (f e).1 = e.1.2 := by
              rcases hf_head e with hh | hh
              · exact False.elim (hnot hh)
              · exact hh
            simpa [e] using hfe
        · intro h
          have hnot : ¬ (f e).1 = e.1.1 := by
            intro hh
            have hv : v = u := by simpa [e] using hh.symm.trans h
            exact huv hv.symm
          have hmem : (u, v) ∈ orientationOf E f := by
            refine Finset.mem_biUnion.mpr ⟨e, Finset.mem_attach E e, ?_⟩
            by_cases hfst : (f e).1 = e.1.1
            · exfalso
              exact hnot hfst
            · simp [contribution, e, hnot]
          simpa [D] using hmem
      have h2 : (v, u) ∈ D ↔ (f e).1 = v := by
        constructor
        · intro h
          rcases Finset.mem_biUnion.mp h with ⟨e0, he0, hee⟩
          by_cases hfst : (f e0).1 = e0.1.1
          · have hpair : (v, u) = e0.1 := by simpa [contribution, hfst] using hee
            have he0e : e0 = e := Subtype.ext hpair.symm
            rw [he0e] at hfst
            simpa [e] using hfst
          · have hpair : (v, u) = e0.1.swap := by simpa [contribution, hfst] using hee
            have hlt0 : e0.1.1 < e0.1.2 := hE_lt e0.1 e0.2
            have hvlt : u < v := by
              have hpair' : e0.1 = (u, v) := by simpa using congrArg Prod.swap hpair.symm
              simpa [hpair'] using hlt0
            exact (lt_asymm hgt hvlt).elim
        · intro h
          by_cases hfst : (f e).1 = e.1.1
          · have hmem : (v, u) ∈ orientationOf E f := by
              refine Finset.mem_biUnion.mpr ⟨e, Finset.mem_attach E e, ?_⟩
              simp [contribution, e, hfst]
            simpa [D] using hmem
          · exfalso
            apply hfst
            simpa [e] using h
      have hmu : (f e).1 = v ∨ (f e).1 = u := by
        rcases hf_head e with hh | hh
        · exact Or.inl (by simpa [e] using hh)
        · exact Or.inr (by simpa [e] using hh)
      constructor
      · intro h1u hv
        have hu : (f e).1 = u := h1.mp h1u
        have hv' : (f e).1 = v := h2.mp hv
        exact huv (hu.symm.trans hv')
      · intro hnotv
        have hnotv' : ¬ (f e).1 = v := by
          intro hv
          exact hnotv (h2.mpr hv)
        have hu : (f e).1 = u := hmu.resolve_left hnotv'
        exact h1.mpr hu
  have hout : ∀ v, outdeg D v ≤ d := by
    intro v
    let sA : Finset ι := (E.attach.filter fun e : ι => (f e).1 = v)
    have hfilter : (D.filter fun p : V × V => p.1 = v) =
        sA.image (fun e : ι => if (f e).1 = e.1.1 then e.1 else e.1.swap) := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpD, hpv⟩
        rcases Finset.mem_biUnion.mp hpD with ⟨e, he, hpe⟩
        have hfe : (f e).1 = v := (hcontrib_first e p hpe).symm.trans hpv
        refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨he, hfe⟩
        · by_cases h : (f e).1 = e.1.1
          · have hp' : p = e.1 := by simpa [contribution, h] using hpe
            simp [h, hp']
          · have hp' : p = e.1.swap := by simpa [contribution, h] using hpe
            simp [h, hp']
      · intro hp
        rcases Finset.mem_image.mp hp with ⟨e, he, hpeq⟩
        rcases Finset.mem_filter.mp he with ⟨heA, hfe⟩
        have hp' : p = if (f e).1 = e.1.1 then e.1 else e.1.swap := hpeq.symm
        rw [Finset.mem_filter, hp']
        constructor
        · change (if (f e).1 = e.1.1 then e.1 else e.1.swap) ∈ orientationOf E f
          refine Finset.mem_biUnion.mpr ⟨e, heA, ?_⟩
          by_cases h : (f e).1 = e.1.1 <;> simp [contribution, h]
        · have hv : (if (f e).1 = e.1.1 then e.1 else e.1.swap).1 = (f e).1 := by
            by_cases h : (f e).1 = e.1.1
            · simp [h]
            · have h' : (f e).1 = e.1.2 := by
                rcases hf_head e with hh | hh
                · exact False.elim (h hh)
                · exact hh
              rw [ite_eq_right h, h']
              simp
          exact hv.trans hfe
    have hcard_f : (D.filter fun p : V × V => p.1 = v).card = sA.card := by
      rw [hfilter]
      exact Finset.card_image_of_injective sA hinj_contrib
    have hcard_le : sA.card ≤ d := by
      let g : ι → Fin d := fun e => (f e).2
      have hinjg : Set.InjOn g (↑sA : Set ι) := by
        intro a ha b hb h
        have hfa : (f a).1 = v := (Finset.mem_filter.mp ha).2
        have hfb : (f b).1 = v := (Finset.mem_filter.mp hb).2
        have hfeq : f a = f b := Prod.ext (hfa.trans hfb.symm) h
        exact hf_inj hfeq
      calc
        sA.card = (sA.image g).card := (Finset.card_image_of_injOn hinjg).symm
        _ ≤ (Finset.univ : Finset (Fin d)).card :=
          Finset.card_le_card (by intro x hx; exact Finset.mem_univ x)
        _ = d := by simp
    calc
      outdeg D v = (D.filter fun p : V × V => p.1 = v).card := rfl
      _ = sA.card := hcard_f
      _ ≤ d := hcard_le
  exact ⟨D, hDadj, hD, hout⟩

end M7

end Jsp511