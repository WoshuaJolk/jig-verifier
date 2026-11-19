import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos699CaseIOne.NoPrime

/-- Degenerate control: the primality demand dropped, so `p = 1` is a witness. Must not be
accepted. -/
theorem proof :
    ∀ n j : ℕ, 1 < j → j ≤ n / 2 →
      ∃ p : ℕ, 1 ≤ p ∧ p ∣ Nat.gcd (n.choose 1) (n.choose j) :=
  fun _ _ _ _ => ⟨1, le_rfl, one_dvd _⟩

end Submissions.Erdos699CaseIOne.NoPrime
