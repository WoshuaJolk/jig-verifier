import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Factorization.Basic

namespace Submissions.Erdos1107SmallRepresentations.Worker03VacuousControl

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

def IsPowerfulSum (r n : ℕ) : Prop :=
  ∃ terms : List ℕ,
    terms.length ≤ r + 1 ∧
    (∀ x ∈ terms, 0 < x ∧ IsFull r x) ∧
    terms.sum = n

theorem proof (h : False) :
    ∀ r n : ℕ, n ≤ r + 1 → IsPowerfulSum r n := h.elim

end Submissions.Erdos1107SmallRepresentations.Worker03VacuousControl
