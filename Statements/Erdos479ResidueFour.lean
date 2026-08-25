import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos479ResidueFour

/-- The residue `k=4` case of Erdős 479. -/
abbrev statement : Prop :=
  {n : ℕ | 2 ^ n ≡ 4 [MOD n]}.Infinite

theorem target : statement := sorry

end Statements.Erdos479ResidueFour
