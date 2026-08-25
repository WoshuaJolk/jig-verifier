import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos774DissociatedSingletonCover

open Finset

/-- Every dissociated set already has a one-piece dissociated cover. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ,
    {U : Finset ℕ | (U : Set ℕ) ⊆ A}.InjOn (fun U => ∑ n ∈ U, n) →
    ∃ T : Set (Set ℕ),
      (∀ S ∈ T,
        {U : Finset ℕ | (U : Set ℕ) ⊆ S}.InjOn (fun U => ∑ n ∈ U, n)) ∧
      T.Finite ∧ A = ⋃₀ T

theorem target : statement := sorry

end Statements.Erdos774DissociatedSingletonCover
