import Jsp511Choosability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# JSP-000511 — M2–M6: Alon–Tarsi orientation criterion (AT92 §1–§2)

* `Jsp511.Eulerian`, `EE`, `EO`, `diff` — Eulerian sub-digraph counting.
* `graphPoly` — the graph polynomial `∏ₑ (xₑ.1 - xₑ.2)`.
* `basicZeroLemma` (AT92 Lemma 2.1) — the "constant-coefficient"
  combinatorial Nullstellensatz over `ℤ`.
* `atCriterion` (AT92 Thm 1.1) — the list-coloring orientation criterion.
* `choosable_of_at_orientation` (AT92 Cor 1.2) — the choosability version
  used by the planar-bipartite main theorem.
* `ee_ne_eo_of_all_eulerian_even` — `EO D = 0` while `EE D ≥ 1`.

Work-in-progress: theorem bodies marked `sorry` are filled by the cron
sessions (see STATE.md R2 plan).  A zero-`sorry` audit runs before the
submission commit.
-/

open Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Jsp511

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Eulerian sub-digraphs of a finite directed edge set -/

/-- Out-degree of `v` in a finite digraph edge set `D`. -/
noncomputable def outdeg (D : Finset (V × V)) (v : V) : ℕ :=
  (D.filter fun e => e.1 = v).card

/-- In-degree of `v` in a finite digraph edge set `D`. -/
noncomputable def indeg (D : Finset (V × V)) (v : V) : ℕ :=
  (D.filter fun e => e.2 = v).card

/-- `D` is **Eulerian**: indegree equals outdegree at every vertex. -/
def Eulerian (D : Finset (V × V)) : Prop :=
  ∀ v, indeg D v = outdeg D v

/-- The empty digraph is Eulerian. -/
lemma Eulerian_empty : Eulerian (∅ : Finset (V × V)) := by
  intro v
  simp [indeg, outdeg]

/-- An Eulerian sub-digraph with an even number of edges. -/
def EvenEulerian (D : Finset (V × V)) : Prop :=
  Eulerian D ∧ Even D.card

/-- An Eulerian sub-digraph with an odd number of edges. -/
def OddEulerian (D : Finset (V × V)) : Prop :=
  Eulerian D ∧ Odd D.card

/-- `EE(D)` : number of even Eulerian sub-digraphs of `D`, as an integer. -/
noncomputable def EE (D : Finset (V × V)) : ℤ := by
  classical
  exact ((D.powerset.filter EvenEulerian).card : ℤ)

/-- `EO(D)` : number of odd Eulerian sub-digraphs of `D`, as an integer. -/
noncomputable def EO (D : Finset (V × V)) : ℤ := by
  classical
  exact ((D.powerset.filter OddEulerian).card : ℤ)

/-- The Alon–Tarsi `diff(D) := |EE(D) - EO(D)|` (the paper counts `EE ≠ EO`). -/
noncomputable def diff (D : Finset (V × V)) : ℕ :=
  Int.natAbs (EE D - EO D)

/-- `diff D ≠ 0` iff `EE D ≠ EO D`. -/
lemma diff_ne_zero_iff (D : Finset (V × V)) : diff D ≠ 0 ↔ EE D ≠ EO D := by
  unfold diff
  rw [Int.natAbs_ne_zero]
  exact sub_ne_zero

/-- The empty sub-digraph is an even Eulerian sub-digraph of every `D`, so
`EE D ≥ 1` always. -/
lemma EE_pos (D : Finset (V × V)) : 0 < EE D := by
  unfold EE
  classical
  have hEven : EvenEulerian (∅ : Finset (V × V)) :=
    ⟨Eulerian_empty, by simp⟩
  have hmem : (∅ : Finset (V × V)) ∈ D.powerset.filter EvenEulerian := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (by simp), hEven⟩
  have hp : 0 < (D.powerset.filter EvenEulerian).card :=
    Finset.card_pos.mpr ⟨∅, hmem⟩
  exact_mod_cast hp

/-- Evenness and oddness are mutually exclusive for natural numbers
(a local replacement for the parity API not imported here). -/
lemma even_not_odd {n : ℕ} : Even n → ¬ Odd n := by
  rintro ⟨k, hk⟩ ⟨l, hl⟩
  omega

/-! ## Graph polynomial (AT92 §2) -/

/-- The graph polynomial of a finite set `E` of oriented edges:
`∏ₑ ∈ E (xₑ.1 - xₑ.2)`.  For an undirected graph `G` we instantiate `E`
with one ordered representative per edge. -/
noncomputable def graphPoly (E : Finset (V × V)) (x : V → ℤ) : ℤ :=
  ∏ e ∈ E, (x e.1 - x e.2)

/-! ## The basic zero lemma (AT92 Lemma 2.1) -/

open MvPolynomial

/-- **Basic zero lemma** (AT92 Lemma 2.1, constant-coefficient
combinatorial Nullstellensatz over `ℤ`): if `p` has `xᵢ`-degree at most
`d i` for every `i`, and `p` vanishes on `∏ᵢ S i` with `|S i| = d i + 1`,
then `p = 0`.  (Proof by induction on `Fintype.card ι`.) -/
theorem basicZeroLemma {ι : Type u} [Fintype ι] (p : MvPolynomial ι ℤ)
    (d : ι → ℕ) (S : ι → Finset ℤ)
    (hdeg : ∀ i, p.degreeOf i ≤ d i)
    (hS : ∀ i, (S i).card = d i + 1)
    (hvan : ∀ c : ι → ℤ, (∀ i, c i ∈ S i) → MvPolynomial.eval c p = 0) :
    p = 0 := by
  sorry

/-! ## The Alon–Tarsi criterion (AT92 Thm 1.1, Cor 1.2) -/

/-- The undirected edge set underlying a digraph `D`. -/
def undirected (D : Finset (V × V)) (u v : V) : Prop :=
  (u, v) ∈ D ∨ (v, u) ∈ D

/-- **Theorem 1.1** (AT92): if `D` is a digraph on `V`, each vertex `v` has
a list `S v` of `outdeg D v + 1` colors, and `EE D ≠ EO D`, then there is a
legal coloring of the underlying undirected graph of `D` from the lists. -/
theorem atCriterion {D : Finset (V × V)} {S : V → Finset ℤ}
    (hS : ∀ v, (S v).card = outdeg D v + 1)
    (hdiff : EE D ≠ EO D) :
    ∃ c : V → ℤ,
      (∀ v, c v ∈ S v) ∧ ∀ ⦃u v⦄, undirected D u v → c u ≠ c v := by
  sorry

/-- **Corollary 1.2** (choosable version, AT92): if `G` has an orientation
`D` (exactly one direction per edge of `G`, no other edges) with maximum
outdegree at most `d` and `EE D ≠ EO D`, then `G` is `(d+1)`-choosable. -/
theorem choosable_of_at_orientation {G : SimpleGraph V} (D : Finset (V × V))
    (d : ℕ)
    (hD : ∀ ⦃u v⦄, G.Adj u v → ((u, v) ∈ D ↔ (v, u) ∉ D))
    (hDund : ∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v)
    (hout : ∀ v, outdeg D v ≤ d)
    (hdiff : EE D ≠ EO D) :
    Choosable G (d + 1) := by
  sorry

/-- If **every** Eulerian sub-digraph of `D` has an even number of edges,
then `EO D = 0` while the empty sub-digraph contributes to `EE D`, hence
`EE D ≠ EO D`.

For a bipartite underlying graph, every directed cycle is even, and every
Eulerian sub-digraph decomposes into directed cycles, so the hypothesis is
satisfied — that implication is formalized in the main-theorem module
(M8). -/
theorem ee_ne_eo_of_all_eulerian_even (D : Finset (V × V))
    (hEven : ∀ H : Finset (V × V), H ∈ D.powerset → Eulerian H → Even H.card) :
    EE D ≠ EO D := by
  have hEO : EO D = 0 := by
    unfold EO
    classical
    have hc : (D.powerset.filter OddEulerian).card = 0 := by
      by_contra hne
      have hnon : (D.powerset.filter OddEulerian).Nonempty :=
        Finset.card_ne_zero.mp hne
      rcases hnon with ⟨H, hH⟩
      rcases Finset.mem_filter.mp hH with ⟨hHmem, hOdd⟩
      rcases hOdd with ⟨hEul, hOddCard⟩
      have hEvenCard := hEven H hHmem hEul
      exact even_not_odd hEvenCard hOddCard
    exact_mod_cast hc
  have hEE : EE D ≠ 0 := by
    intro hz
    have hp := EE_pos D
    omega
  rw [hEO]
  exact hEE

end Jsp511
