import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card

namespace Statements.Erdos1183SuperpolynomialUnionClosed

def Monochromatic {n : ℕ}
    (color : Finset (Fin n) → Bool)
    (family : Finset (Finset (Fin n))) : Prop :=
  ∃ b : Bool, ∀ A ∈ family, color A = b

def UnionClosed {n : ℕ}
    (family : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ∪ B ∈ family

/-- The still-open superpolynomial half of Erdős Problem 1183:
every fixed polynomial lower bound should eventually be forced in
every two-coloring of the Boolean lattice. -/
abbrev statement : Prop :=
  ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ color : Finset (Fin n) → Bool,
      ∃ family : Finset (Finset (Fin n)),
        Monochromatic color family ∧
          UnionClosed family ∧ n ^ d < family.card

theorem target : statement := sorry

end Statements.Erdos1183SuperpolynomialUnionClosed
