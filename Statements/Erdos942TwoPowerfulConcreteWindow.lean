import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos942TwoPowerfulConcreteWindow

def Powerful (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- Two explicit distinct powerful numbers lie strictly between the consecutive
squares `2909²` and `2910²`. -/
abbrev statement : Prop :=
  ∃ m₁ m₂ : ℕ,
    m₁ ≠ m₂ ∧ Powerful m₁ ∧ Powerful m₂ ∧
    2909 ^ 2 < m₁ ∧ m₁ < 2910 ^ 2 ∧
    2909 ^ 2 < m₂ ∧ m₂ < 2910 ^ 2

theorem target : statement := sorry

end Statements.Erdos942TwoPowerfulConcreteWindow
