import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos398KnownWitnessesV2.JohnPhamousKnownWitnesses

theorem proof :
    (Nat.factorial 4 + 1 = (5 : Nat) ^ 2) ∧
      (Nat.factorial 5 + 1 = (11 : Nat) ^ 2) ∧
        (Nat.factorial 7 + 1 = (71 : Nat) ^ 2) := by
  norm_num [Nat.factorial]

end Submissions.Erdos398KnownWitnessesV2.JohnPhamousKnownWitnesses
