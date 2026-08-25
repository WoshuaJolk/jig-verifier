import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos1107SmallRepresentations

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

def IsPowerfulSum (r n : ℕ) : Prop :=
  ∃ terms : List ℕ,
    terms.length ≤ r + 1 ∧
    (∀ x ∈ terms, 0 < x ∧ IsFull r x) ∧
    terms.sum = n

/-- Every `n ≤ r + 1` is represented by `n` copies of the
positive `r`-powerful integer one. -/
abbrev statement : Prop :=
  ∀ r n : ℕ, n ≤ r + 1 → IsPowerfulSum r n

theorem target : statement := sorry

end Statements.Erdos1107SmallRepresentations
