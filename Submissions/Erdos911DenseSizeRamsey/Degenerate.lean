import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Submissions.Erdos911DenseSizeRamsey.Degenerate

structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

def RamseyFor {n : ℕ} (host : FiniteGraph)
    (target : SimpleGraph (Fin n)) : Prop :=
  ∀ red : Fin host.order → Fin host.order → Bool,
    (∀ u v, red u v = red v u) →
    ∃ f : Fin n ↪ Fin host.order,
      (∀ u v, target.Adj u v → host.graph.Adj (f u) (f v)) ∧
      ∃ colour : Bool, ∀ u v, target.Adj u v →
        red (f u) (f v) = colour

open scoped Classical in
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

noncomputable def sizeRamsey {n : ℕ}
    (target : SimpleGraph (Fin n)) : ℕ :=
  sInf {m : ℕ | ∃ host : FiniteGraph,
    edgeCount host.graph = m ∧ RamseyFor host target}

/-- Erdős 911: the size-Ramsey overhead of graphs of average density `C`
grows superlinearly in `C`. -/
abbrev statement : Prop :=
  ∃ f : ℕ → ℝ,
    Tendsto (fun C : ℕ => f C / C) atTop atTop ∧
    ∀ᶠ C : ℕ in atTop, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      C * n ≤ edgeCount G →
        f C * edgeCount G < sizeRamsey G

theorem proof : False → statement := False.elim

end Submissions.Erdos911DenseSizeRamsey.Degenerate
