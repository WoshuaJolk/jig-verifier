import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos376CentralBinomCoprime105

/-- Erdős Problem 376. -/
abbrev statement : Prop :=
  Set.Infinite {n : ℕ | n.centralBinom.Coprime 105}

theorem target : statement := sorry

end Statements.Erdos376CentralBinomCoprime105
