import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Archimedean

namespace Statements.Erdos51TotientMinRatio

/-- Erdős Problem 51: infinitely many totient values have least preimages
whose ratio to the value tends to infinity. -/
abbrev statement : Prop :=
  ∃ A : Set ℕ, ∃ n : A → ℕ,
    A.Infinite ∧
    (∀ a : A, IsLeast (Nat.totient ⁻¹' {(a : ℕ)}) (n a)) ∧
    Filter.Tendsto (fun a : A ↦ (n a : ℝ) / (a : ℝ))
      Filter.atTop Filter.atTop

theorem target : statement := sorry

end Statements.Erdos51TotientMinRatio
