import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Instances.Nat

open Filter

namespace Statements.Erdos855PrimeCountingSubadditivity

/-- Erdős Problem 855 (Segal's conjecture): eventual subadditivity of
the prime-counting function. -/
abbrev statement : Prop :=
  ∀ᶠ x : ℕ in atTop, ∀ᶠ y : ℕ in atTop,
    Nat.primeCounting (x + y) ≤
      Nat.primeCounting x + Nat.primeCounting y

theorem target : statement := sorry

end Statements.Erdos855PrimeCountingSubadditivity
