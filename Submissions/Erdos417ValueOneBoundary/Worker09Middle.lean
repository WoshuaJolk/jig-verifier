import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card

namespace Submissions.Erdos417ValueOneBoundary.Worker09Middle

open Set

theorem proof :
    (1 : ℕ) ∈ {k : ℕ | k ∈ Set.range Nat.totient ∧ k ≤ 1} ∧
    (1 : ℕ) ∈ Nat.totient '' Set.Icc 1 1 := by
  exact ⟨⟨⟨1, by simp⟩, by simp⟩, ⟨1, by simp, by simp⟩⟩

end Submissions.Erdos417ValueOneBoundary.Worker09Middle
