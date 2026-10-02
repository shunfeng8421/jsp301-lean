import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

/-!
# JSP-000511 — M1: list-coloring / choosability framework

Definitions used by the Alon–Tarsi orientation criterion (M2–M6):

* `ProperListColoring G lists c` — `c` is a proper vertex-coloring of `G`
  choosing each color from the vertex's list.
* `HasProperListColoring G lists` — existence.
* `Choosable G k` — every list-assignment of size `k` admits a proper
  list-coloring, for **every** color type.

Note: mathlib (v4.34.0) has no choosability API; these definitions are
local to the Jsp511 project.
-/

open Finset

namespace Jsp511

universe u v

variable {V : Type u}

/-- A **proper list-coloring** of `G` w.r.t. list assignment `lists`:
each vertex `v` receives a color `c v` inside `lists v`, and adjacent
vertices receive distinct colors. -/
def ProperListColoring (G : SimpleGraph V) {α : Type} [DecidableEq α]
    (lists : V → Finset α) (c : V → α) : Prop :=
  (∀ v, c v ∈ lists v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/-- `G` admits a proper list-coloring from the given lists. -/
def HasProperListColoring (G : SimpleGraph V) {α : Type} [DecidableEq α]
    (lists : V → Finset α) : Prop :=
  ∃ c : V → α, ProperListColoring G lists c

/-- `G` is **`k`-choosable**: for every color type and every list-assignment
of size `k`, a proper list-coloring exists. -/
def Choosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ {α : Type} [DecidableEq α] (lists : V → Finset α),
    (∀ v, (lists v).card = k) → HasProperListColoring G lists

end Jsp511
