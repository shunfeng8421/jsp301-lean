import Jsp511AtCore
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! M8 : bipartite ⟹ any orientation D of G has EE D ≠ EO D.

Chain: feed `ee_ne_eo_of_all_eulerian_even` with hEven : ∀ H ⊆ D, Eulerian H → Even H.card.
For Eulerian H in a bipartite G: |E(H)| = 2 · (Σ_{v∈P} outdeg_H v) via fiber-sums + crossing.

NOTE: mathlib v4.34.0 uses the new big-operator binder syntax; the Finset sum is
`∑ x ∈ s, f x` (NOT `∑ x in s, f x`, which no longer parses). -/

open Finset
open scoped BigOperators
open scoped Classical

namespace Jsp511

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Filtering `P` for equality with a member `a` gives the singleton `{a}`. -/
lemma card_filter_eq_singleton (P : Finset V) (a : V) (ha : a ∈ P) :
    (P.filter fun v : V => a = v) = {a} := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hvP, hva⟩
    simpa using hva.symm
  · intro hv
    have hva : v = a := by simpa using hv
    rw [Finset.mem_filter]
    constructor
    · rwa [hva]
    · exact hva.symm

omit [Fintype V] in
/-- Filtering `P` for equality with a non-member `a` gives the empty set. -/
lemma card_filter_eq_zero (P : Finset V) (a : V) (ha : a ∉ P) :
    (P.filter fun v : V => a = v) = ∅ := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hvP, hva⟩
    exact False.elim (ha (by simpa [hva.symm] using hvP))
  · intro hv
    simp at hv

omit [Fintype V] in
/-- Σ of outdegrees over a restricted vertex set = edges of H leaving that set. -/
lemma sum_outdeg_restrict_eq_card_filter (P : Finset V) (H : Finset (V × V)) :
    (∑ v ∈ P, outdeg H v) = (H.filter fun e : V × V => e.1 ∈ P).card := by
  classical
  calc
    (∑ v ∈ P, outdeg H v)
        = ∑ v ∈ P, (H.filter fun e : V × V => e.1 = v).card := by
            simp [outdeg]
    _ = ∑ v ∈ P, ∑ e ∈ H, if e.1 = v then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp
    _ = ∑ e ∈ H, ∑ v ∈ P, if e.1 = v then 1 else 0 := by
            rw [Finset.sum_comm (s := P) (t := H)]
    _ = ∑ e ∈ H, if e.1 ∈ P then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases hp : e.1 ∈ P
            · have hf : (P.filter fun v : V => e.1 = v) = {e.1} :=
                card_filter_eq_singleton P e.1 hp
              rw [Finset.sum_boole (p := fun v : V => e.1 = v) (s := P), hf,
                Finset.card_singleton]
              simp [hp]
            · have hf : (P.filter fun v : V => e.1 = v) = ∅ :=
                card_filter_eq_zero P e.1 hp
              rw [Finset.sum_boole (p := fun v : V => e.1 = v) (s := P), hf,
                Finset.card_empty]
              simp [hp]
    _ = (H.filter fun e : V × V => e.1 ∈ P).card := by
            simp

omit [Fintype V] in
/-- Σ of indegrees over a restricted vertex set = edges of H entering that set. -/
lemma sum_indeg_restrict_eq_card_filter (P : Finset V) (H : Finset (V × V)) :
    (∑ v ∈ P, indeg H v) = (H.filter fun e : V × V => e.2 ∈ P).card := by
  classical
  calc
    (∑ v ∈ P, indeg H v)
        = ∑ v ∈ P, (H.filter fun e : V × V => e.2 = v).card := by
            simp [indeg]
    _ = ∑ v ∈ P, ∑ e ∈ H, if e.2 = v then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp
    _ = ∑ e ∈ H, ∑ v ∈ P, if e.2 = v then 1 else 0 := by
            rw [Finset.sum_comm (s := P) (t := H)]
    _ = ∑ e ∈ H, if e.2 ∈ P then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases hp : e.2 ∈ P
            · have hf : (P.filter fun v : V => e.2 = v) = {e.2} :=
                card_filter_eq_singleton P e.2 hp
              rw [Finset.sum_boole (p := fun v : V => e.2 = v) (s := P), hf,
                Finset.card_singleton]
              simp [hp]
            · have hf : (P.filter fun v : V => e.2 = v) = ∅ :=
                card_filter_eq_zero P e.2 hp
              rw [Finset.sum_boole (p := fun v : V => e.2 = v) (s := P), hf,
                Finset.card_empty]
              simp [hp]
    _ = (H.filter fun e : V × V => e.2 ∈ P).card := by
            simp

omit [Fintype V] in
/-- In a digraph whose undirected edges are all in the bipartite graph `G`,
a vertex outside both parts has out-degree 0 in any sub-digraph `H`. -/
lemma outdeg_eq_zero_of_not_mem_union {G : SimpleGraph V} {P Q : Set V}
    (hDund : ∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v) (hPQ : G.IsBipartiteWith P Q)
    {H : Finset (V × V)} (hHsub : H ⊆ D) (v : V) (hv : v ∉ P ∪ Q) :
    outdeg H v = 0 := by
  classical
  unfold outdeg
  have hf : H.filter (fun e : V × V => e.1 = v) = ∅ := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨heH, he1⟩
      have hadj : G.Adj e.1 e.2 := hDund (hHsub heH)
      rcases hPQ.mem_of_adj hadj with ⟨hp, hq⟩ | ⟨hq, hp⟩
      · exact False.elim (hv (by simpa [he1] using Or.inl hp))
      · exact False.elim (hv (by simpa [he1] using Or.inr hq))
    · intro he0
      simp at he0
  simp [hf]

/-- If the undirected edges of the orientation `D` lie in a bipartite graph `G`,
then every Eulerian sub-digraph `H ⊆ D` has an even number of edges. -/
lemma eulerian_subgraph_even_card_of_bipartite {G : SimpleGraph V} {P Q : Set V}
    (hDund : ∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v) (hPQ : G.IsBipartiteWith P Q)
    {H : Finset (V × V)} (hHsub : H ⊆ D) (hEul : Eulerian H) : Even H.card := by
  classical
  have hPout : (∑ v ∈ P.toFinset, outdeg H v) = (H.filter fun e : V × V => e.1 ∈ P.toFinset).card :=
    sum_outdeg_restrict_eq_card_filter P.toFinset H
  have hQin : (∑ v ∈ Q.toFinset, indeg H v) = (H.filter fun e : V × V => e.2 ∈ Q.toFinset).card :=
    sum_indeg_restrict_eq_card_filter Q.toFinset H
  have hcross : (H.filter fun e : V × V => e.1 ∈ P.toFinset) = (H.filter fun e : V × V => e.2 ∈ Q.toFinset) := by
    ext e
    by_cases he : e ∈ H
    · have hadj : G.Adj e.1 e.2 := hDund (hHsub he)
      rcases hPQ.mem_of_adj hadj with h1 | h2
      · simp [he, h1.1, h1.2]
      · constructor
        · intro helem
          rcases Finset.mem_filter.mp helem with ⟨_, hp⟩
          exact False.elim ((Set.disjoint_left.mp hPQ.disjoint (by simpa [Set.mem_toFinset] using hp)) h2.1)
        · intro helem
          rcases Finset.mem_filter.mp helem with ⟨_, hq⟩
          exact False.elim ((Set.disjoint_left.mp hPQ.disjoint.symm (by simpa [Set.mem_toFinset] using hq)) h2.2)
    · simp [he]
  have hEulP : (∑ v ∈ P.toFinset, outdeg H v) = (∑ v ∈ P.toFinset, indeg H v) := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    exact (hEul v).symm
  have hPQeq : (∑ v ∈ P.toFinset, outdeg H v) = (∑ v ∈ Q.toFinset, outdeg H v) := by
    calc
      (∑ v ∈ P.toFinset, outdeg H v)
          = (∑ v ∈ Q.toFinset, indeg H v) := by
              rw [hPout, hcross, ← hQin]
      _ = (∑ v ∈ Q.toFinset, outdeg H v) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              exact hEul v
  have hcard : H.card = 2 * (∑ v ∈ P.toFinset, outdeg H v) := by
    calc
      H.card = (∑ v : V, outdeg H v) := (sum_outdeg_eq_card H).symm
      _ = (∑ v ∈ P.toFinset ∪ Q.toFinset, outdeg H v) := by
              symm
              apply Finset.sum_subset
              · intro v _; exact Finset.mem_univ v
              · intro v hv hpq
                exact outdeg_eq_zero_of_not_mem_union hDund hPQ hHsub v (by
                  simpa [Set.mem_toFinset] using hpq)
      _ = (∑ v ∈ P.toFinset, outdeg H v) + (∑ v ∈ Q.toFinset, outdeg H v) := by
              rw [Finset.sum_union]
              exact Finset.disjoint_left.mpr (by
                intro v hvP hvQ
                exact Set.disjoint_left.mp hPQ.disjoint (by simpa [Set.mem_toFinset] using hvP)
                  (by simpa [Set.mem_toFinset] using hvQ))
      _ = 2 * (∑ v ∈ P.toFinset, outdeg H v) := by
              rw [hPQeq]
              omega
  exact ⟨(∑ v ∈ P.toFinset, outdeg H v), by omega⟩

/-- M8 core: a bipartite graph has no odd Eulerian sub-digraphs in any orientation,
so every orientation of a bipartite graph satisfies the Alon–Tarsi parity condition. -/
lemma ee_ne_eo_of_bipartite {G : SimpleGraph V} (D : Finset (V × V))
    (_hD : ∀ ⦃u v⦄, G.Adj u v → ((u, v) ∈ D ↔ (v, u) ∉ D))
    (hDund : ∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v)
    (hG : G.IsBipartite) : EE D ≠ EO D := by
  classical
  rcases (SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp hG) with ⟨P, Q, hPQ⟩
  apply ee_ne_eo_of_all_eulerian_even
  intro H hHpow hEul
  have hHsub : H ⊆ D := Finset.mem_powerset.mp hHpow
  exact eulerian_subgraph_even_card_of_bipartite hDund hPQ hHsub hEul

end Jsp511