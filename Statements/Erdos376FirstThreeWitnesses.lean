import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Insert

namespace Statements.Erdos376FirstThreeWitnesses

/-- The first three known indices all give central binomial coefficients coprime to 105. -/
abbrev statement : Prop :=
  ∀ n ∈ ({0, 1, 10} : Finset ℕ), n.centralBinom.Coprime 105

theorem target : statement := sorry

end Statements.Erdos376FirstThreeWitnesses
