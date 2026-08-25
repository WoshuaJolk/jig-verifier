import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Factorization.Basic

namespace Submissions.Erdos1107SmallRepresentations.Worker03Ones

def IsFull (r n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ r ∣ n

def IsPowerfulSum (r n : ℕ) : Prop :=
  ∃ terms : List ℕ,
    terms.length ≤ r + 1 ∧
    (∀ x ∈ terms, 0 < x ∧ IsFull r x) ∧
    terms.sum = n

theorem proof :
    ∀ r n : ℕ, n ≤ r + 1 → IsPowerfulSum r n := by
  intro r n hn
  refine ⟨List.replicate n 1, ?_, ?_, ?_⟩
  · simpa using hn
  · intro x hx
    simp only [List.mem_replicate] at hx
    have hx1 : x = 1 := hx.2
    subst x
    constructor
    · decide
    · intro p hp
      simp at hp
  · simp

end Submissions.Erdos1107SmallRepresentations.Worker03Ones
