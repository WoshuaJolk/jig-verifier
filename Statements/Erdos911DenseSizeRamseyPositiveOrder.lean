import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Statements.Erdos911DenseSizeRamseyPositiveOrder

noncomputable section

/-- Faithful positive-order repair of Erdős 911. Public dependent pairs and
inlined definitions keep the standalone-submission interface inhabitable. -/
abbrev statement : Prop := by
  classical
  exact
    let edgeCount : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ :=
      fun {_n} G => G.edgeFinset.card
    let ramseyFor : ∀ {n : ℕ},
        (Σ k : ℕ, SimpleGraph (Fin k)) → SimpleGraph (Fin n) → Prop :=
      fun {n} host target =>
        ∀ red : Fin host.1 → Fin host.1 → Bool,
          (∀ u v, red u v = red v u) →
          ∃ f : Fin n ↪ Fin host.1,
            (∀ u v, target.Adj u v → host.2.Adj (f u) (f v)) ∧
            ∃ colour : Bool, ∀ u v, target.Adj u v →
              red (f u) (f v) = colour
    let sizeRamsey : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ :=
      fun {_n} target =>
        sInf {m : ℕ | ∃ host : Σ k : ℕ, SimpleGraph (Fin k),
          edgeCount host.2 = m ∧ ramseyFor host target}
    ∃ f : ℕ → ℝ,
      Tendsto (fun C : ℕ => f C / C) atTop atTop ∧
      ∀ᶠ C : ℕ in atTop, ∀ n : ℕ, 1 ≤ n →
        ∀ G : SimpleGraph (Fin n), C * n ≤ edgeCount G →
          f C * edgeCount G < sizeRamsey G

theorem target : statement := sorry

end

end Statements.Erdos911DenseSizeRamseyPositiveOrder
