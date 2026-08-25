import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Nth

namespace Submissions.Erdos386KnownWitness.Control

open Finset Nat
open scoped BigOperators

abbrev claimedStatement : Prop :=
  Nat.choose 21 2 =
    ∏ i ∈ Ico 0 4, Nat.nth Nat.Prime i

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos386KnownWitness.Control
