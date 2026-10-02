import Jsp511Thm32

namespace Jsp511

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Main theorem** (Alon–Tarsi 1992, Thm 3.2 + Cor 3.4, `d = 2`): every bipartite
  graph `G` whose edge sets satisfy the planar bound `|E(H)| ≤ 2|V(H)| − 4`
  (i.e. `Sparse G 2`; for planar bipartite graphs this bound is Euler's formula)
  is `3`-choosable.

  Proof: `choosable_of_sparse_bipartite` with `d = 2` (M7 Hall orientation +
  M8 parity + M6 Alon–Tarsi criterion). -/
theorem three_choosable_of_bipartite_two_sparse {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder V] (hsp : Sparse G 2) (hG : G.IsBipartite) :
    Choosable G 3 := by
  exact choosable_of_sparse_bipartite (d := 2) hsp hG

end Jsp511
