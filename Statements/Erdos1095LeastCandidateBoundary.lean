import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Lattice.Nat

open Nat

namespace Statements.Erdos1095LeastCandidateBoundary

def candidates (k : ℕ) : Set ℕ :=
  {n : ℕ | k + 1 < n ∧ k < (n.choose k).minFac}

noncomputable def g (k : ℕ) : ℕ :=
  sInf (candidates k)

/-- Whenever the defining candidate set is nonempty, `g k` itself
satisfies both defining inequalities. -/
abbrev statement : Prop :=
  ∀ k : ℕ, (candidates k).Nonempty →
    k + 1 < g k ∧ k < ((g k).choose k).minFac

theorem target : statement := sorry

end Statements.Erdos1095LeastCandidateBoundary
