import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Statements.Erdos911DenseSizeRamseyOverhead

open scoped Classical in
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

/-- `host` is Ramsey for `target`: every two-colouring of the pairs of `host`
contains a monochromatic copy of `target`. -/
def RamseyFor {n : ℕ} (host : Σ k : ℕ, SimpleGraph (Fin k))
    (target : SimpleGraph (Fin n)) : Prop :=
  ∀ red : Fin host.1 → Fin host.1 → Bool,
    (∀ u v, red u v = red v u) →
    ∃ f : Fin n ↪ Fin host.1,
      (∀ u v, target.Adj u v → host.2.Adj (f u) (f v)) ∧
      ∃ colour : Bool, ∀ u v, target.Adj u v → red (f u) (f v) = colour

/-- The size-Ramsey number: the least number of edges of a host that is
Ramsey for `target`. -/
noncomputable def sizeRamsey {n : ℕ} (target : SimpleGraph (Fin n)) : ℕ :=
  sInf {m : ℕ | ∃ host : Σ k : ℕ, SimpleGraph (Fin k),
    edgeCount host.2 = m ∧ RamseyFor host target}

/-- Erdős Problem 911: there is `f` with `f(C)/C → ∞` such that for all large
`C`, every graph on `n ≥ 1` vertices with `e ≥ C n` edges has size-Ramsey
number greater than `f(C) e`. -/
abbrev statement : Prop :=
  ∃ f : ℕ → ℝ,
    Tendsto (fun C : ℕ => f C / C) atTop atTop ∧
    ∀ᶠ C : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      C * n ≤ edgeCount G → f C * edgeCount G < sizeRamsey G

theorem target : statement := sorry

end Statements.Erdos911DenseSizeRamseyOverhead
