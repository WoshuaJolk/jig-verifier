import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos830CompositeMembers

open ArithmeticFunction

abbrev statement : Prop :=
    ∀ a b : ℕ, sigma 1 a = a + b → sigma 1 b = a + b →
      (a = 0 ∧ b = 0) ∨
        (1 < a ∧ 1 < b ∧ ¬ Nat.Prime a ∧ ¬ Nat.Prime b)

end Statements.Erdos830CompositeMembers
