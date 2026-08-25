import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos774FiniteDissociatedCover

open Finset

def IsDissociated (A : Set ℕ) : Prop :=
  {S : Finset ℕ | (S : Set ℕ) ⊆ A}.InjOn fun S => ∑ n ∈ S, n

def IsProportionatelyDissociated (A : Set ℕ) : Prop :=
  ∃ c > (0 : ℝ), ∀ B : Finset ℕ, (B : Set ℕ) ⊆ A →
    ∃ S ⊆ B, S.card ≥ c * B.card ∧ IsDissociated (S : Set ℕ)

/-- Erdős problem 774: every infinite proportionately dissociated set is a
finite union of dissociated sets. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsProportionatelyDissociated A →
    ∃ T : Set (Set ℕ),
      (∀ S ∈ T, IsDissociated S) ∧ T.Finite ∧ A = ⋃₀ T

theorem target : statement := sorry

end Statements.Erdos774FiniteDissociatedCover
