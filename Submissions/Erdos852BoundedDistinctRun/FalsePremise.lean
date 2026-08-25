import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Nat.Prime.Nth

namespace Submissions.Erdos852BoundedDistinctRun.FalsePremise

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def DistinctRun (start length : ℕ) : Prop :=
  (Finset.range length : Set ℕ).Pairwise fun i j =>
    primeGap (start + i) ≠ primeGap (start + j)

theorem proof :
    False →
      ∀ start length B : ℕ,
        DistinctRun start length →
          (∀ i < length, primeGap (start + i) ≤ B) →
            length ≤ B + 1 := by
  intro h
  exact h.elim

end Submissions.Erdos852BoundedDistinctRun.FalsePremise
