import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Lattice.Nat

open Nat

namespace Submissions.Erdos1095LeastCandidateBoundary.Worker03SInfMember

def candidates (k : ℕ) : Set ℕ :=
  {n : ℕ | k + 1 < n ∧ k < (n.choose k).minFac}

noncomputable def g (k : ℕ) : ℕ :=
  sInf (candidates k)

theorem proof :
    ∀ k : ℕ, (candidates k).Nonempty →
      k + 1 < g k ∧ k < ((g k).choose k).minFac := by
  intro k h
  exact Nat.sInf_mem h

end Submissions.Erdos1095LeastCandidateBoundary.Worker03SInfMember
