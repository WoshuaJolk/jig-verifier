import Mathlib.Data.Finset.Card

namespace Statements.Erdos788ConcreteIntervals

def InUpperInterval (n : ℕ) (B : Finset ℕ) : Prop :=
  ∀ b ∈ B, 2 * n < b ∧ b < 4 * n

def InLowerInterval (n : ℕ) (C : Finset ℕ) : Prop :=
  ∀ c ∈ C, n < c ∧ c < 2 * n

def AvoidsDistinctSums (B C : Finset ℕ) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B

abbrev statement : Prop :=
  InUpperInterval 1 {3} ∧
    InLowerInterval 3 {4, 5} ∧
      AvoidsDistinctSums {7} {4, 5}

theorem target : statement := sorry

end Statements.Erdos788ConcreteIntervals
