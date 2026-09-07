import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Statements.Erdos830ThabitConstruction

open ArithmeticFunction

abbrev statement : Prop :=
    ∀ k : ℕ, 1 ≤ k →
      let p := 3 * 2^k - 1
      let q := 3 * 2^(k+1) - 1
      let r := 9 * 2^(2*k+1) - 1
      let a := 2^(k+1) * p * q
      let b := 2^(k+1) * r
      Nat.Prime p → Nat.Prime q → Nat.Prime r →
        0 < a ∧ a < b ∧ sigma 1 a = a + b ∧ sigma 1 b = a + b

end Statements.Erdos830ThabitConstruction
