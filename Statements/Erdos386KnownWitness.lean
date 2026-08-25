import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Statements.Erdos386KnownWitness

open Finset Nat
open scoped BigOperators

/-- The classical example `21.choose 2 = 2 * 3 * 5 * 7`. -/
abbrev statement : Prop :=
  Nat.choose 21 2 =
    ∏ i ∈ Ico 0 4, Nat.nth Nat.Prime i

theorem target : statement := sorry

end Statements.Erdos386KnownWitness
