import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range

namespace Statements.Erdos236RepresentationCountBound

def representationCount (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter
    (fun k => Nat.Prime (n - 2 ^ k))).length

/-- The elementary pointwise bound obtained by counting candidate exponents. -/
abbrev statement : Prop :=
  ∀ n : ℕ, representationCount n ≤ Nat.log2 n + 1

theorem target : statement := sorry

end Statements.Erdos236RepresentationCountBound
