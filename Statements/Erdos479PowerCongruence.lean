import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos479PowerCongruence

/-- Erdős Problem 479: for every `k > 1`, infinitely many moduli `n`
satisfy `2^n ≡ k (mod n)`. -/
abbrev statement : Prop :=
  ∀ k > 1, {n : ℕ | 2 ^ n ≡ k [MOD n]}.Infinite

theorem target : statement := sorry

end Statements.Erdos479PowerCongruence
