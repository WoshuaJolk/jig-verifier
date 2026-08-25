import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos676ModFourHalf.Worker04

theorem proof :
    ∀ n : ℕ, 4 ≤ n → n % 4 < 2 →
      ∃ p a b : ℕ,
        p.Prime ∧ 1 ≤ a ∧ b < p ∧ n = a * p ^ 2 + b := by
  intro n hn hrem
  refine ⟨2, n / 4, n % 4, Nat.prime_two, ?_, hrem, ?_⟩
  · omega
  · simpa [mul_comm] using (Nat.div_add_mod n 4).symm

end Submissions.Erdos676ModFourHalf.Worker04
