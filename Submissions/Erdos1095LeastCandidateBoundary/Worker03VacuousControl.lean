import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Lattice.Nat

open Nat

namespace Submissions.Erdos1095LeastCandidateBoundary.Worker03VacuousControl

def candidates (k : ℕ) : Set ℕ :=
  {n : ℕ | k + 1 < n ∧ k < (n.choose k).minFac}

noncomputable def g (k : ℕ) : ℕ := sInf (candidates k)

theorem proof (h : False) :
    ∀ k : ℕ, (candidates k).Nonempty →
      k + 1 < g k ∧ k < ((g k).choose k).minFac := h.elim

end Submissions.Erdos1095LeastCandidateBoundary.Worker03VacuousControl
