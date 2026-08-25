import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos681ShiftFiveBoundary.Worker09Upper

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

theorem proof :
    ∃ k : ℕ, 0 < k ∧ IsComposite (5 + k) ∧
      ∀ p : ℕ, IsLeastPrimeFactor p (5 + k) → k ^ 2 < p := by
  refine ⟨1, by norm_num, ?_, ?_⟩
  · exact ⟨by decide, by decide⟩
  · intro p hp
    have hp2 : 2 ≤ p := hp.1.two_le
    exact lt_of_lt_of_le (by norm_num) hp2

end Submissions.Erdos681ShiftFiveBoundary.Worker09Upper
