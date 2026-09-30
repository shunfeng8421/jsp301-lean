import Jsp511Choosability
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Finsupp.Weight

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
open scoped Classical

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
then `p = 0`.

This is exactly the contrapositive-looking form of mathlib's
`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` (Alon 1999 Thm 1). -/
theorem basicZeroLemma {ι : Type u} [Fintype ι] (p : MvPolynomial ι ℤ)
    (d : ι → ℕ) (S : ι → Finset ℤ)
    (hdeg : ∀ i, p.degreeOf i ≤ d i)
    (hS : ∀ i, (S i).card = d i + 1)
    (hvan : ∀ c : ι → ℤ, (∀ i, c i ∈ S i) → MvPolynomial.eval c p = 0) :
    p = 0 := by
  exact MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p S
    (fun i => lt_of_le_of_lt (hdeg i) (by rw [hS i]; omega)) hvan

/-! ### The graph polynomial as an `MvPolynomial` (AT92 §2) -/

/-- The graph polynomial of a finite oriented edge set `D`, as an
`MvPolynomial` over `ℤ`; each edge `e = (u, v)` contributes `X u - X v`. -/
noncomputable def graphPolyMv (D : Finset (V × V)) : MvPolynomial V ℤ :=
  ∏ e ∈ D, (MvPolynomial.X e.1 - MvPolynomial.X e.2)

/-- Evaluating the polynomial graph polynomial at `c` gives back the integer
graph polynomial. -/
lemma graphPolyMv_eval (D : Finset (V × V)) (c : V → ℤ) :
    MvPolynomial.eval c (graphPolyMv D) = graphPoly D c := by
  simp [graphPolyMv, graphPoly]

/-- The finitely-supported function `v ↦ outdeg D v`. -/
noncomputable def outdegSupp (D : Finset (V × V)) : V →₀ ℕ :=
  ∑ v : V, Finsupp.single v (outdeg D v)

/-- `outdegSupp D` agrees with `outdeg D` pointwise. -/
lemma outdegSupp_apply (D : Finset (V × V)) (v : V) : outdegSupp D v = outdeg D v := by
  unfold outdegSupp
  simp [Finset.sum_apply, Finsupp.single_apply]

/-- The sum of the out-degrees over all vertices equals the number of edges. -/
lemma sum_outdeg_eq_card (D : Finset (V × V)) : (∑ v : V, outdeg D v) = D.card := by
  classical
  calc
    (∑ v : V, outdeg D v)
        = ∑ v : V, (D.filter fun e : V × V => e.1 = v).card := by
            simp [outdeg]
    _ = ∑ v : V, ∑ e ∈ D, if e.1 = v then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact (Finset.sum_boole (p := fun e : V × V => e.1 = v) (s := D)).symm
    _ = ∑ e ∈ D, ∑ v : V, if e.1 = v then 1 else 0 := by
            rw [Finset.sum_comm (s := (Finset.univ : Finset V)) (t := D)]
    _ = ∑ e ∈ D, 1 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            simp [eq_comm]
    _ = D.card := by
            exact (Finset.card_eq_sum_ones D).symm

/-- The total degree of `outdegSupp D` (the number of edges, counted with
out-degree multiplicities) is `D.card`. -/
lemma outdegSupp_degree (D : Finset (V × V)) : (outdegSupp D).degree = D.card := by
  rw [Finsupp.degree_eq_sum]
  calc
    (∑ v : V, outdegSupp D v) = ∑ v : V, outdeg D v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact outdegSupp_apply D v
    _ = D.card := sum_outdeg_eq_card D

/-- Expansion of `∏ e ∈ D, (a e - b e)` over all sub-digraphs `A ⊆ D`:
each `A` selects the negative factors `b e` (`e ∈ A`) and the positive ones
`a e` (`e ∈ D \ A`). -/
lemma prod_sub_eq_powerset_sum {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]
    (D : Finset α) (a b : α → R) :
    (∏ e ∈ D, (a e - b e)) =
      ∑ A ∈ D.powerset, ((-1 : R) ^ A.card) * (∏ e ∈ A, b e) * (∏ e ∈ D \ A, a e) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert e D he ih =>
      rw [Finset.prod_insert he]
      rw [Finset.powerset_insert]
      have hdisj : Disjoint D.powerset (D.powerset.image (insert e)) := by
        rw [Finset.disjoint_left]
        intro A hA hA'
        have heA : e ∉ A := fun heA => he (Finset.mem_powerset.mp hA heA)
        rcases Finset.mem_image.mp hA' with ⟨B, hB, rfl⟩
        exact heA (Finset.mem_insert_self e B)
      rw [Finset.sum_union hdisj]
      have hinj : ∀ x ∈ D.powerset, ∀ y ∈ D.powerset, insert e x = insert e y → x = y := by
        intro x hx y hy hxy
        have hex : e ∉ x := fun h => he (Finset.mem_powerset.mp hx h)
        have hey : e ∉ y := fun h => he (Finset.mem_powerset.mp hy h)
        have hxy' := congrArg (fun s : Finset α => s.erase e) hxy
        simpa [Finset.erase_insert hex, Finset.erase_insert hey] using hxy'
      rw [Finset.sum_image (f := fun A : Finset α =>
        ((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ (insert e D) \ A, a e')) hinj]
      rw [← Finset.sum_add_distrib]
      calc
        (a e - b e) * (∏ e' ∈ D, (a e' - b e'))
            = (a e - b e) * ∑ A ∈ D.powerset,
                ((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ D \ A, a e') := by
                rw [ih]
        _ = ∑ A ∈ D.powerset,
                (a e - b e) * (((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ D \ A, a e')) := by
                rw [Finset.mul_sum]
        _ = ∑ A ∈ D.powerset,
                (((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ (insert e D) \ A, a e')
                  + ((-1 : R) ^ (insert e A).card) * (∏ e' ∈ insert e A, b e') *
                      (∏ e' ∈ (insert e D) \ (insert e A), a e')) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                have heA : e ∉ A := fun heA => he (Finset.mem_powerset.mp hA heA)
                have hsd1 : (insert e D) \ A = insert e (D \ A) := by
                  ext e'
                  by_cases h : e' = e
                  · subst e'
                    simp [he, heA, Finset.mem_sdiff]
                  · simp [h, Finset.mem_sdiff, Finset.mem_insert]
                have hprod1 : (∏ e' ∈ (insert e D) \ A, a e') = a e * (∏ e' ∈ D \ A, a e') := by
                  rw [hsd1]
                  have heDA : e ∉ D \ A := by
                    intro h
                    exact he (Finset.mem_sdiff.mp h).1
                  simpa using (Finset.prod_insert heDA)
                have hsd2 : (insert e D) \ (insert e A) = D \ A := by
                  ext e'
                  by_cases h : e' = e
                  · subst e'
                    simp [he, Finset.mem_sdiff, Finset.mem_insert]
                  · simp [h, Finset.mem_sdiff, Finset.mem_insert]
                have hpb : (∏ e' ∈ insert e A, b e') = b e * (∏ e' ∈ A, b e') := by
                  simpa using (Finset.prod_insert heA)
                have hcard : (insert e A).card = A.card + 1 := Finset.card_insert_of_notMem heA
                have hnegpow : (-1 : R) ^ (A.card + 1) = -((-1 : R) ^ A.card) := by
                  rw [pow_succ, mul_neg_one]
                symm
                calc
                  ((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ (insert e D) \ A, a e')
                      + ((-1 : R) ^ (insert e A).card) * (∏ e' ∈ insert e A, b e') *
                          (∏ e' ∈ (insert e D) \ (insert e A), a e')
                      = ((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ D \ A, a e') * a e
                          + ((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ D \ A, a e') * (-b e) := by
                          rw [hprod1, hcard, hpb, hnegpow, hsd2]
                          ring
                  _ = ((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ D \ A, a e') * (a e - b e) := by
                          ring
                  _ = (a e - b e) * (((-1 : R) ^ A.card) * (∏ e' ∈ A, b e') * (∏ e' ∈ D \ A, a e')) := by
                          ring

/-- `(-1)^n = 1` for even `n`. -/
lemma neg_one_pow_even (n : ℕ) (h : Even n) : (-1 : ℤ) ^ n = 1 := by
  rcases h with ⟨k, rfl⟩
  rw [show k + k = 2 * k by omega]
  rw [pow_mul]
  norm_num

/-- `(-1)^n = -1` for odd `n`. -/
lemma neg_one_pow_odd (n : ℕ) (h : Odd n) : (-1 : ℤ) ^ n = -1 := by
  rcases h with ⟨k, rfl⟩
  rw [pow_succ]
  rw [pow_mul]
  norm_num

/-- The `v`-th coordinate of `∑ e ∈ B, single e.2 1` counts the edges of `B`
ending at `v` (the tail-indexed coordinates). -/
lemma sum_single_T_apply (B : Finset (V × V)) (v : V) :
    (∑ e ∈ B, Finsupp.single e.2 (1 : ℕ)) v = (B.filter fun e : V × V => e.2 = v).card := by
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  exact Finset.sum_boole (p := fun e : V × V => e.2 = v) (s := B)

/-- The `v`-th coordinate of `∑ e ∈ B, single e.1 1` counts the edges of `B`
starting at `v` (the head-indexed coordinates). -/
lemma sum_single_H_apply (B : Finset (V × V)) (v : V) :
    (∑ e ∈ B, Finsupp.single e.1 (1 : ℕ)) v = (B.filter fun e : V × V => e.1 = v).card := by
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  exact Finset.sum_boole (p := fun e : V × V => e.1 = v) (s := B)

/-- The monomial exponent vector selected by `A ⊆ D` equals `outdegSupp D`
exactly when `A` is Eulerian: for every vertex the number of selected
incoming edges matches the number of (un-selected) outgoing edges. -/
lemma exp_eq_outdegSupp_iff (D : Finset (V × V)) (A : Finset (V × V)) (hA : A ⊆ D) :
    (∑ e ∈ A, Finsupp.single e.2 1) + (∑ e ∈ D \ A, Finsupp.single e.1 1) = outdegSupp D
      ↔ Eulerian A := by
  classical
  rw [Finsupp.ext_iff]
  constructor
  · intro h v
    have hv := h v
    rw [Finsupp.add_apply] at hv
    rw [sum_single_T_apply, sum_single_H_apply, outdegSupp_apply] at hv
    have hsplit : (D.filter fun e : V × V => e.1 = v) =
        (A.filter fun e => e.1 = v) ∪ ((D \ A).filter fun e => e.1 = v) := by
      ext e
      by_cases heA : e ∈ A
      · simp [heA, hA heA]
      · simp [heA]
    have hdisj : Disjoint (A.filter fun e => e.1 = v) ((D \ A).filter fun e => e.1 = v) := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he2).1).2 (Finset.mem_filter.mp he1).1
    have hcard : outdeg D v =
        (A.filter fun e => e.1 = v).card + ((D \ A).filter fun e => e.1 = v).card := by
      rw [outdeg, hsplit, Finset.card_union_of_disjoint hdisj]
    rw [hcard] at hv
    rw [indeg, outdeg]
    omega
  · intro h v
    rw [Finsupp.add_apply]
    rw [sum_single_T_apply, sum_single_H_apply, outdegSupp_apply]
    have hsplit : (D.filter fun e : V × V => e.1 = v) =
        (A.filter fun e => e.1 = v) ∪ ((D \ A).filter fun e => e.1 = v) := by
      ext e
      by_cases heA : e ∈ A
      · simp [heA, hA heA]
      · simp [heA]
    have hdisj : Disjoint (A.filter fun e => e.1 = v) ((D \ A).filter fun e => e.1 = v) := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he2).1).2 (Finset.mem_filter.mp he1).1
    have hcard : outdeg D v =
        (A.filter fun e => e.1 = v).card + ((D \ A).filter fun e => e.1 = v).card := by
      rw [outdeg, hsplit, Finset.card_union_of_disjoint hdisj]
    have hba : (A.filter fun e => e.1 = v).card = (A.filter fun e => e.2 = v).card := by
      simpa [indeg, outdeg] using (h v).symm
    rw [← hba, hcard]

/-- Summing the sign `(-1)^|A|` over all Eulerian sub-digraphs of `D` gives
`EE D - EO D`. -/
lemma sum_powerset_eulerian_sign (D : Finset (V × V)) :
    (∑ A ∈ D.powerset, if Eulerian A then (-1 : ℤ) ^ A.card else 0) = EE D - EO D := by
  classical
  have hstep1 : (∑ A ∈ D.powerset, if Eulerian A then (-1 : ℤ) ^ A.card else 0) =
      ∑ A ∈ D.powerset.filter (fun A => Eulerian A), (-1 : ℤ) ^ A.card := by
    rw [Finset.sum_filter]
  calc
    (∑ A ∈ D.powerset, if Eulerian A then (-1 : ℤ) ^ A.card else 0)
        = ∑ A ∈ D.powerset.filter (fun A => Eulerian A), (-1 : ℤ) ^ A.card := hstep1
    _ = (∑ A ∈ D.powerset.filter EvenEulerian, (-1 : ℤ) ^ A.card) +
        (∑ A ∈ D.powerset.filter (fun A => Eulerian A ∧ Odd A.card), (-1 : ℤ) ^ A.card) := by
        have hsplit : D.powerset.filter (fun A : Finset (V × V) => Eulerian A) =
            D.powerset.filter EvenEulerian ∪
              D.powerset.filter (fun A => Eulerian A ∧ Odd A.card) := by
          ext A
          by_cases hE : Eulerian A
          · simp [EvenEulerian, hE]
            have hEO : Even A.card ∨ Odd A.card := Nat.even_or_odd A.card
            tauto
          · simp [EvenEulerian, hE]
        have hdisj : Disjoint (D.powerset.filter EvenEulerian)
            (D.powerset.filter (fun A => Eulerian A ∧ Odd A.card)) := by
          rw [Finset.disjoint_left]
          intro A hA1 hA2
          exact even_not_odd (Finset.mem_filter.mp hA1).2.2 (Finset.mem_filter.mp hA2).2.2
        rw [hsplit, Finset.sum_union hdisj]
    _ = (∑ A ∈ D.powerset.filter EvenEulerian, (1 : ℤ)) +
        (∑ A ∈ D.powerset.filter (fun A => Eulerian A ∧ Odd A.card), (-1 : ℤ)) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro A hA
          exact neg_one_pow_even A.card (Finset.mem_filter.mp hA).2.2
        · refine Finset.sum_congr rfl ?_
          intro A hA
          exact neg_one_pow_odd A.card (Finset.mem_filter.mp hA).2.2
    _ = EE D - EO D := by
        have hodd : D.powerset.filter (fun A : Finset (V × V) => Eulerian A ∧ Odd A.card) =
            D.powerset.filter OddEulerian := by
          apply Finset.filter_congr
          intro A hA
          simp [OddEulerian]
        rw [hodd]
        simp [EE, EO]
        ring

/-- The coefficient of the monomial `∏ₓ X v ^ (outdeg D v)` in the graph
polynomial of `D` is `EE D - EO D` (AT92 Lemma 2.2). -/
lemma graphPoly_coeff_outdeg (D : Finset (V × V)) :
    (graphPolyMv D).coeff (outdegSupp D) = EE D - EO D := by
  classical
  rw [show graphPolyMv D = ∑ A ∈ D.powerset,
        ((-1 : MvPolynomial V ℤ) ^ A.card) * (∏ e ∈ A, MvPolynomial.X e.2) *
          (∏ e ∈ D \ A, MvPolynomial.X e.1) from by
        unfold graphPolyMv
        exact prod_sub_eq_powerset_sum D
          (fun e : V × V => MvPolynomial.X e.1) (fun e : V × V => MvPolynomial.X e.2)]
  rw [MvPolynomial.coeff_sum]
  rw [← sum_powerset_eulerian_sign D]
  refine Finset.sum_congr rfl ?_
  intro A hA
  have hPA : (∏ e ∈ A, MvPolynomial.X e.2) =
      monomial (∑ e ∈ A, Finsupp.single e.2 1) (1 : ℤ) := by
    calc
      (∏ e ∈ A, MvPolynomial.X e.2)
          = ∏ e ∈ A, monomial (Finsupp.single e.2 1) (1 : ℤ) := by
              refine Finset.prod_congr rfl ?_
              intro e he
              simpa using (MvPolynomial.X_pow_eq_monomial (n := e.2) (e := 1))
      _ = monomial (∑ e ∈ A, Finsupp.single e.2 1) (1 : ℤ) := by
              simpa using (MvPolynomial.monomial_sum_prod A
                (fun e : V × V => Finsupp.single e.2 1) (fun _ : V × V => (1 : ℤ))).symm
  have hPD : (∏ e ∈ D \ A, MvPolynomial.X e.1) =
      monomial (∑ e ∈ D \ A, Finsupp.single e.1 1) (1 : ℤ) := by
    calc
      (∏ e ∈ D \ A, MvPolynomial.X e.1)
          = ∏ e ∈ D \ A, monomial (Finsupp.single e.1 1) (1 : ℤ) := by
              refine Finset.prod_congr rfl ?_
              intro e he
              simpa using (MvPolynomial.X_pow_eq_monomial (n := e.1) (e := 1))
      _ = monomial (∑ e ∈ D \ A, Finsupp.single e.1 1) (1 : ℤ) := by
              simpa using (MvPolynomial.monomial_sum_prod (D \ A)
                (fun e : V × V => Finsupp.single e.1 1) (fun _ : V × V => (1 : ℤ))).symm
  have hneg : (C ((-1 : ℤ) ^ A.card) : MvPolynomial V ℤ) = (-1 : MvPolynomial V ℤ) ^ A.card := by
    rw [map_pow]
    simp
  calc
    ((((-1 : MvPolynomial V ℤ) ^ A.card) * (∏ e ∈ A, MvPolynomial.X e.2) *
        (∏ e ∈ D \ A, MvPolynomial.X e.1)).coeff (outdegSupp D))
        = if (∑ e ∈ A, Finsupp.single e.2 1) + (∑ e ∈ D \ A, Finsupp.single e.1 1) = outdegSupp D
          then (-1 : ℤ) ^ A.card else 0 := by
            rw [hPA, hPD]
            rw [← hneg]
            rw [← MvPolynomial.monomial_zero']
            rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
            rw [MvPolynomial.coeff_monomial]
            simp [add_comm]
    _ = if Eulerian A then (-1 : ℤ) ^ A.card else 0 := by
            have hiff : (∑ e ∈ A, Finsupp.single e.2 1) + (∑ e ∈ D \ A, Finsupp.single e.1 1) = outdegSupp D
                ↔ Eulerian A := exp_eq_outdegSupp_iff D A (Finset.mem_powerset.mp hA)
            by_cases hE : Eulerian A <;> simp [hE, hiff]

/-- The total degree of the graph polynomial is at most the number of edges:
each factor `X u - X v` is linear. -/
lemma graphPolyMv_totalDegree_le (D : Finset (V × V)) :
    (graphPolyMv D).totalDegree ≤ D.card := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [graphPolyMv]
  | @insert e D he ih =>
      unfold graphPolyMv
      rw [Finset.prod_insert he]
      calc
        ((MvPolynomial.X e.1 - MvPolynomial.X e.2 : MvPolynomial V ℤ) * graphPolyMv D).totalDegree
            ≤ (MvPolynomial.X e.1 - MvPolynomial.X e.2 : MvPolynomial V ℤ).totalDegree + (graphPolyMv D).totalDegree :=
                totalDegree_mul _ _
        _ ≤ 1 + D.card := by
                refine add_le_add ?_ ih
                have hneg : (-1 : ℤ) • (MvPolynomial.X e.2 : MvPolynomial V ℤ) = -MvPolynomial.X e.2 := by
                  rw [neg_one_smul]
                calc
                  (MvPolynomial.X e.1 - MvPolynomial.X e.2 : MvPolynomial V ℤ).totalDegree
                      = (MvPolynomial.X e.1 + -MvPolynomial.X e.2 : MvPolynomial V ℤ).totalDegree := by simp [sub_eq_add_neg]
                  _ ≤ max (MvPolynomial.X e.1).totalDegree (-MvPolynomial.X e.2).totalDegree :=
                      totalDegree_add (MvPolynomial.X e.1) (-MvPolynomial.X e.2)
                  _ ≤ 1 := by
                      refine max_le ?_ ?_
                      · exact le_of_eq (MvPolynomial.totalDegree_X (R := ℤ) e.1)
                      · calc
                          (-MvPolynomial.X e.2 : MvPolynomial V ℤ).totalDegree
                              ≤ (MvPolynomial.X e.2).totalDegree := by
                                  rw [← hneg]
                                  exact MvPolynomial.totalDegree_smul_le (-1 : ℤ) (MvPolynomial.X e.2)
                          _ = 1 := MvPolynomial.totalDegree_X e.2
        _ ≤ (insert e D).card := by
                rw [Finset.card_insert_of_notMem he]
                omega

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
  classical
  -- Coefficient of the distinguished monomial is non-zero.
  have ht : (graphPolyMv D).coeff (outdegSupp D) ≠ 0 := by
    rw [graphPoly_coeff_outdeg]
    exact sub_ne_zero.mpr hdiff
  -- Total degree matches the exponent-vector degree.
  have htdeg : (graphPolyMv D).totalDegree = (outdegSupp D).degree := by
    apply le_antisymm
    · calc
        (graphPolyMv D).totalDegree ≤ D.card := graphPolyMv_totalDegree_le D
        _ = (outdegSupp D).degree := (outdegSupp_degree D).symm
    · exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr ht)
  -- Grid-size condition of the coefficient-form Nullstellensatz.
  have htS : ∀ v, (outdegSupp D) v < (S v).card := by
    intro v
    rw [outdegSupp_apply, hS v]
    omega
  rcases MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      (f := graphPolyMv D) (t := outdegSupp D) ht htdeg S htS with ⟨c, hc, hcp⟩
  refine ⟨c, hc, ?_⟩
  -- `hcP : eval c (graphPolyMv D) ≠ 0`, rewrite to the integer graph polynomial.
  rw [graphPolyMv_eval] at hcp
  -- A non-zero product of integer factors : every factor is non-zero.
  have hfac : ∀ e ∈ D, c e.1 ≠ c e.2 := by
    intro e he
    have hprod := (Finset.prod_ne_zero_iff (s := D)
      (f := fun e' : V × V => c e'.1 - c e'.2)).mp hcp
    have hsub : c e.1 - c e.2 ≠ 0 := hprod e he
    intro hc
    exact hsub (by rw [hc]; simp)
  intro u v huv
  rcases huv with hu | hv
  · exact hfac (u, v) hu
  · exact (hfac (v, u) hv).symm

/-- **Corollary 1.2** (choosable version, AT92): if `G` has an orientation
`D` (exactly one direction per edge of `G`, no other edges) with maximum
outdegree at most `d` and `EE D ≠ EO D`, then `G` is `(d+1)`-choosable. -/
theorem choosable_of_at_orientation {G : SimpleGraph V} (D : Finset (V × V))
    (d : ℕ)
    (hD : ∀ ⦃u v⦄, G.Adj u v → ((u, v) ∈ D ↔ (v, u) ∉ D))
    (_hDund : ∀ ⦃u v⦄, (u, v) ∈ D → G.Adj u v)
    (hout : ∀ v, outdeg D v ≤ d)
    (hdiff : EE D ≠ EO D) :
    Choosable G (d + 1) := by
  classical
  intro α _ lists hlists
  -- `U` : union of all lists; `emb : α → ℤ` injective on `U`.
  let U : Finset α := Finset.univ.biUnion lists
  let eU : U ≃ Fin U.card := Finset.equivFin U
  let emb : α → ℤ := fun x => if hx : x ∈ U then ((eU ⟨x, hx⟩).val : ℤ) else 0
  -- Each list has at least `outdeg D v + 1` elements.
  have hcard_le : ∀ v, outdeg D v + 1 ≤ (lists v).card := by
    intro v
    calc
      outdeg D v + 1 ≤ d + 1 := Nat.succ_le_succ (hout v)
      _ = (lists v).card := (hlists v).symm
  have hL : ∀ v (i : ℕ), i ∈ Finset.range (outdeg D v + 1) → i < (lists v).card := by
    intro v i hi
    have hi' : i < outdeg D v + 1 := by simpa using hi
    exact lt_of_lt_of_le hi' (hcard_le v)
  -- `T v` : the first `outdeg D v + 1` elements of `lists v` (via equivFin).
  let fT (v : V) (i : {i : ℕ // i ∈ Finset.range (outdeg D v + 1)}) : α :=
    ((Finset.equivFin (lists v)).symm ⟨i.1, hL v i.1 i.2⟩ : {x : α // x ∈ lists v}).1
  let T : V → Finset α := fun v => ((Finset.range (outdeg D v + 1)).attach.image (fT v))
  let S : V → Finset ℤ := fun v => (T v).image emb
  -- `T v ⊆ lists v`
  have hTsub : ∀ v x, x ∈ T v → x ∈ lists v := by
    intro v x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, hxi⟩
    have hmem : fT v i ∈ lists v := by
      exact ((Finset.equivFin (lists v)).symm ⟨i.1, hL v i.1 i.2⟩ : {x : α // x ∈ lists v}).property
    simpa [← hxi] using hmem
  -- `(T v).card = outdeg D v + 1`
  have hTcard : ∀ v, (T v).card = outdeg D v + 1 := by
    intro v
    unfold T
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_attach, Finset.card_range]
    · intro x hx y hy hxy
      apply Subtype.ext
      have hx1 : ((Finset.equivFin (lists v)).symm ⟨x.1, hL v x.1 x.2⟩ :
            {z : α // z ∈ lists v}).1 =
            ((Finset.equivFin (lists v)).symm ⟨y.1, hL v y.1 y.2⟩ :
            {z : α // z ∈ lists v}).1 := by
        change fT v x = fT v y
        exact hxy
      have hst : (Finset.equivFin (lists v)).symm ⟨x.1, hL v x.1 x.2⟩ =
                 (Finset.equivFin (lists v)).symm ⟨y.1, hL v y.1 y.2⟩ := Subtype.ext hx1
      have hinj := (Finset.equivFin (lists v)).symm.injective hst
      exact congrArg Fin.val hinj
  -- `T v ⊆ U`
  have hTsubU : ∀ v x, x ∈ T v → x ∈ U := by
    intro v x hx
    exact (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hTsub v x hx⟩ : x ∈ U)
  -- `(S v).card = outdeg D v + 1` (emb injective on `T v ⊆ U`)
  have hS : ∀ v, (S v).card = outdeg D v + 1 := by
    intro v
    unfold S
    rw [Finset.card_image_of_injOn]
    · exact hTcard v
    · intro x hx y hy hxy
      have hxU : x ∈ U := hTsubU v x hx
      have hyU : y ∈ U := hTsubU v y hy
      have hvalZ : ((eU ⟨x, hxU⟩).val : ℤ) = ((eU ⟨y, hyU⟩).val : ℤ) := by
        simpa [emb, hxU, hyU] using hxy
      have hval : (eU ⟨x, hxU⟩).val = (eU ⟨y, hyU⟩).val := by
        exact_mod_cast hvalZ
      have hfin : eU ⟨x, hxU⟩ = eU ⟨y, hyU⟩ := Fin.ext hval
      have hxy' : (⟨x, hxU⟩ : U) = (⟨y, hyU⟩ : U) := eU.injective hfin
      exact congrArg Subtype.val hxy'
  -- Apply the Alon–Tarsi criterion.
  rcases atCriterion (D := D) (S := S) hS hdiff with ⟨c0, hc0⟩
  have hc0T : ∀ v, ∃ x ∈ T v, emb x = c0 v := by
    intro v
    exact Finset.mem_image.mp (by simpa [S] using hc0.1 v)
  -- Pull colors back through `emb`.
  let c : V → α := fun v => Classical.choose (hc0T v)
  refine ⟨c, ?_, ?_⟩
  · intro v
    have hcT : c v ∈ T v := by simpa [c] using (Classical.choose_spec (hc0T v)).1
    exact hTsub v (c v) hcT
  · intro u v huv
    have hcu : emb (c u) = c0 u := by simpa [c] using (Classical.choose_spec (hc0T u)).2
    have hcv : emb (c v) = c0 v := by simpa [c] using (Classical.choose_spec (hc0T v)).2
    have hc0ne : c0 u ≠ c0 v := hc0.2 (by
      unfold undirected
      by_cases h1 : (u, v) ∈ D
      · exact Or.inl h1
      · right
        by_contra h2
        exact h1 ((hD huv).mpr h2))
    intro hcuv
    apply hc0ne
    rw [← hcu, ← hcv]
    exact congrArg emb hcuv

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
