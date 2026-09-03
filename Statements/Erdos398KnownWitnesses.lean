import Mathlib

namespace Statements.Erdos398KnownWitnesses

abbrev statement : Prop :=
  (4 ! + 1 = (5 : Nat) ^ 2) ∧
    (5 ! + 1 = (11 : Nat) ^ 2) ∧
      (7 ! + 1 = (71 : Nat) ^ 2)

theorem target : statement := by
  norm_num [Nat.factorial]

end Statements.Erdos398KnownWitnesses
