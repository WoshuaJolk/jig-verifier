import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos117CoverNumberMinimaBridge

/-- The least-number bridge at the end of arXiv:2608.20507v1, Lemma 2.1:
mutually cardinality-nonincreasing translations between two nonempty classes
of finite covers identify their least attainable cardinalities. -/
abbrev statement : Prop :=
  ∀ (A B : Set ℕ),
    A.Nonempty →
    B.Nonempty →
    (∀ a ∈ A, ∃ b ∈ B, b ≤ a) →
    (∀ b ∈ B, ∃ a ∈ A, a ≤ b) →
    sInf A = sInf B

theorem target : statement := sorry

end Statements.Erdos117CoverNumberMinimaBridge
