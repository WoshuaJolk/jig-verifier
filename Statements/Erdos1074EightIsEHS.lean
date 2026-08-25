import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos1074EightIsEHS

open scoped Nat

def EHSNumbers : Set ℕ :=
  {m | 1 ≤ m ∧
    ∃ p : ℕ, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m.factorial + 1}

/-- The first EHS number is witnessed by the prime factor 61 of `8!+1`. -/
abbrev statement : Prop :=
  8 ∈ EHSNumbers

theorem target : statement := sorry

end Statements.Erdos1074EightIsEHS
