import Jsp511AtCore
import Jsp511M7
import Jsp511M8

namespace Jsp511

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- **Theorem 3.2** (Alon–Tarsi 1992): a `d`-sparse bipartite graph is `(d+1)`-choosable.

  Proof pipeline:
  - `exists_orientation_of_sparse` (M7, Hall's theorem): `d`-sparse ⟹ an orientation
    `D` of `G` with every outdegree `≤ d` (dual endpoint copies + Hall condition);
  - `ee_ne_eo_of_bipartite` (M8): every orientation of a bipartite graph satisfies
    the Alon–Tarsi parity condition `EE D ≠ EO D` (all Eulerian sub-digraphs have
    even edge count);
  - `choosable_of_at_orientation` (M6, Alon–Tarsi criterion): orientation with
    outdegree `≤ d` and `EE D ≠ EO D` ⟹ `(d+1)`-choosable. -/
theorem choosable_of_sparse_bipartite {G : SimpleGraph V} {d : ℕ}
    [DecidableRel G.Adj] [LinearOrder V] (hsp : Sparse G d) (hG : G.IsBipartite) :
    Choosable G (d + 1) := by
  classical
  rcases exists_orientation_of_sparse G d hsp with ⟨D, hDund, hD, hout⟩
  exact choosable_of_at_orientation D d hD hDund hout
    (ee_ne_eo_of_bipartite D hD hDund hG)

end Jsp511
