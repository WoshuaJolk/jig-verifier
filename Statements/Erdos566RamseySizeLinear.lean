import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos566RamseySizeLinear

open SimpleGraph

/-- The minimum number of edges in a graph whose every red/blue coloring
contains a red copy of `G` or a blue copy of `H`. -/
noncomputable def sizeRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {m | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.edgeSet.ncard = m ∧
      ∀ (R : SimpleGraph (Fin n)), R ≤ F →
        G.IsContained R ∨ H.IsContained (F \ R)}

/-- Erdős Problem 566: every graph whose induced `k`-vertex subgraphs have
at most `2k-3` edges is Ramsey size linear. -/
abbrev statement : Prop :=
  ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
    (∀ S : Finset (Fin p), 2 ≤ S.card →
      (G.induce S).edgeSet.ncard ≤ 2 * S.card - 3) →
    ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      (∀ v, 0 < H.degree v) →
        (sizeRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

theorem target : statement := sorry

end Statements.Erdos566RamseySizeLinear
