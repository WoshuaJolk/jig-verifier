import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Submissions.Erdos774DissociatedSingletonCover.Direct

open Finset

theorem proof :
    ∀ A : Set ℕ,
      {U : Finset ℕ | (U : Set ℕ) ⊆ A}.InjOn (fun U => ∑ n ∈ U, n) →
      ∃ T : Set (Set ℕ),
        (∀ S ∈ T,
          {U : Finset ℕ | (U : Set ℕ) ⊆ S}.InjOn (fun U => ∑ n ∈ U, n)) ∧
        T.Finite ∧ A = ⋃₀ T := by
  intro A hA
  refine ⟨{A}, ?_, Set.finite_singleton A, ?_⟩
  · intro S hS
    simp only [Set.mem_singleton_iff] at hS
    subst S
    exact hA
  · simp

end Submissions.Erdos774DissociatedSingletonCover.Direct
