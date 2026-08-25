import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

open Polynomial

namespace Statements.Erdos1152LagrangeExists

abbrev statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (nodes : Fin n → ℝ), Function.Injective nodes →
      ∀ values : Fin n → ℝ,
        ∃ p : ℝ[X],
          p.natDegree < n ∧
            ∀ i : Fin n, p.eval (nodes i) = values i

theorem target : statement := sorry

end Statements.Erdos1152LagrangeExists
