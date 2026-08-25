import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18PairMergeFails.Finite

theorem proof :
    let digits : Finset ℕ := {210, 84, 7, 4}
    let replacement : Finset ℕ := {1, 24, 280}
    (∀ a ∈ digits, ∀ b ∈ digits, a < b → ¬(a + b ∣ Nat.factorial 7)) ∧
      replacement ⊆ (Nat.factorial 7).divisors ∧
      replacement.card = 3 ∧
      replacement.sum id = 305 ∧
      digits.sum id = 305 := by
  norm_num [Finset.subset_iff, Nat.mem_divisors]

end Submissions.Erdos18PairMergeFails.Finite
