import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos681PrimeSuccessorReduction.Worker09Upper

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

theorem proof :
    ∀ n : ℕ, 2 ≤ n →
      (n + 1).Prime ∨
        ∃ k : ℕ, 0 < k ∧ IsComposite (n + k) ∧
          ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p := by
  intro n hn
  by_cases hprime : (n + 1).Prime
  · exact Or.inl hprime
  · right
    refine ⟨1, by omega, ⟨by omega, hprime⟩, ?_⟩
    intro p hp
    have hp2 : 2 ≤ p := hp.1.two_le
    omega

end Submissions.Erdos681PrimeSuccessorReduction.Worker09Upper
