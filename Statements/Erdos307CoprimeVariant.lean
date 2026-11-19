import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos307CoprimeVariant

/-- The weakened form of Erdős Problem 307 in which the members of each set are only
required to be pairwise coprime positive integers, each set having at least two members,
has a solution (Cambie): `(1 + 1/5)(1/2 + 1/3) = 1`. -/
abbrev statement : Prop :=
  ∃ P Q : Finset ℕ, (∀ p ∈ P, 0 < p) ∧ (∀ q ∈ Q, 0 < q) ∧ 1 < P.card ∧ 1 < Q.card ∧
    (P : Set ℕ).Pairwise Nat.Coprime ∧ (Q : Set ℕ).Pairwise Nat.Coprime ∧
    (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹) = 1

theorem target : statement := sorry

end Statements.Erdos307CoprimeVariant
