import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos820CoprimePowersInfinitelyOften

/-- The first explicit question in Erdős Problem 820. -/
abbrev statement : Prop :=
  {n : ℕ | Nat.Coprime (2 ^ n - 1) (3 ^ n - 1)}.Infinite

theorem target : statement := sorry

end Statements.Erdos820CoprimePowersInfinitelyOften
