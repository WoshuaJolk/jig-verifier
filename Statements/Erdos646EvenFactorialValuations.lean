import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open scoped Nat

namespace Statements.Erdos646EvenFactorialValuations

abbrev statement : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    {n : ℕ | ∀ p ∈ S, Even (padicValNat p (n !))}.Infinite

theorem target : statement := sorry

end Statements.Erdos646EvenFactorialValuations
