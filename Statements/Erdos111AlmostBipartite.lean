import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Ring.Real

open Filter
open Cardinal

/-!
# Erdős problem 111

If `h_G(n)` is the largest, over all `n`-vertex subgraphs of `G`, of the
minimum number of edges that must be deleted to make that subgraph bipartite,
must `h_G(n) / n` tend to infinity whenever `G` has chromatic cardinal `ℵ₁`?
-/

namespace Statements.Erdos111AlmostBipartite

noncomputable def chromaticCardinal {V : Type} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal |
    ∃ (C : Type), #C = κ ∧ Nonempty (G.Coloring C)}

def CanBipartizeByDeletingAtMost {V : Type} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ E : Finset (Sym2 V), E.card ≤ m ∧
    (G.deleteEdges (E : Set (Sym2 V))).IsBipartite

noncomputable def bipartizationNumber {V : Type} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | CanBipartizeByDeletingAtMost G m}

noncomputable def h (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {m : ℕ |
    ∃ A : Finset V, A.card = n ∧
      m = bipartizationNumber (G.induce (A : Set V))}

abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    chromaticCardinal G = ℵ₁ →
      Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop

theorem target : statement := sorry

end Statements.Erdos111AlmostBipartite
