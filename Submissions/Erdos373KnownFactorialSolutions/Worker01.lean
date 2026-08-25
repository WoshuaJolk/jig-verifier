import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Submissions.Erdos373KnownFactorialSolutions.Worker01

open scoped Nat

abbrev IsSolution (candidate : ℕ × List ℕ) : Prop :=
  candidate.1 ! = (candidate.2.map Nat.factorial).prod ∧
  candidate.2.Pairwise (· ≥ ·) ∧
  candidate.2.headI < candidate.1 - 1 ∧
  ∀ a ∈ candidate.2, 1 < a

theorem proof :
    IsSolution (10, [7, 6]) ∧ IsSolution (16, [14, 5, 2]) := by
  norm_num [IsSolution, List.pairwise_cons]

end Submissions.Erdos373KnownFactorialSolutions.Worker01
