import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos398KnownWitnessesV2

abbrev statement : Prop :=
  (Nat.factorial 4 + 1 = (5 : Nat) ^ 2) ∧
    (Nat.factorial 5 + 1 = (11 : Nat) ^ 2) ∧
      (Nat.factorial 7 + 1 = (71 : Nat) ^ 2)

theorem target : statement := sorry

end Statements.Erdos398KnownWitnessesV2
