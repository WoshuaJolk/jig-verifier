import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

open Polynomial

namespace Submissions.Erdos1152LagrangeExists.ExplicitInterpolation

theorem proof :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (nodes : Fin n → ℝ), Function.Injective nodes →
        ∀ values : Fin n → ℝ,
          ∃ p : ℝ[X],
            p.natDegree < n ∧
              ∀ i : Fin n, p.eval (nodes i) = values i := by
  intro n hn nodes hnodes values
  let p : ℝ[X] := Lagrange.interpolate Finset.univ nodes values
  refine ⟨p, ?_, ?_⟩
  · by_cases hp : p = 0
    · simpa [hp] using (lt_of_lt_of_le Nat.zero_lt_one hn)
    · apply (natDegree_lt_iff_degree_lt hp).2
      simpa [p] using
        (Lagrange.degree_interpolate_lt values hnodes.injOn :
          (Lagrange.interpolate Finset.univ nodes values).degree <
            (Finset.univ : Finset (Fin n)).card)
  · intro i
    exact Lagrange.eval_interpolate_at_node values hnodes.injOn (by simp)

end Submissions.Erdos1152LagrangeExists.ExplicitInterpolation
