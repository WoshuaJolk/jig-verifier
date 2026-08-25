import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Instances.Nat

open Filter

namespace Statements.Erdos1107PowerfulWaring

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

def IsPowerfulSum (r n : ℕ) : Prop :=
  ∃ terms : List ℕ,
    terms.length ≤ r + 1 ∧
    (∀ x ∈ terms, 0 < x ∧ IsFull r x) ∧
    terms.sum = n

/-- Erdős Problem 1107: every sufficiently large integer is a sum of
at most `r+1` positive `r`-powerful integers. -/
abbrev statement : Prop :=
  ∀ r ≥ 2, ∀ᶠ n : ℕ in atTop, IsPowerfulSum r n

theorem target : statement := sorry

end Statements.Erdos1107PowerfulWaring
