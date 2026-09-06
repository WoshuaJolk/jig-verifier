import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
The prime exclusion is classical; see Chen, Tang and Zhan,
Formalization of Amicable Numbers Theory, arXiv:2601.07444,
and AmicableLib/Amicable.lean, not_isAmicable_prime.
This proof works directly with Jig's sigma equations and explicitly handles
zero and the diagonal, which its canonical definition permits.
-/

namespace Submissions.Erdos830CompositeMembers.CompositeMembers

open ArithmeticFunction

theorem proof :
    ∀ a b : ℕ, sigma 1 a = a + b → sigma 1 b = a + b →
      (a = 0 ∧ b = 0) ∨
        (1 < a ∧ 1 < b ∧ ¬ Nat.Prime a ∧ ¬ Nat.Prime b) := by
  intro a b ha hb
  by_cases ha0 : a = 0
  · left
    subst a
    simpa using ha.symm
  · right
    have hb0 : b ≠ 0 := by
      intro h
      subst b
      simp at hb
      exact ha0 hb.symm
    have ha1 : a ≠ 1 := by
      intro h
      subst a
      have : b = 0 := by simpa using ha.symm
      exact hb0 this
    have hb1 : b ≠ 1 := by
      intro h
      subst b
      have : a = 0 := by simpa using hb.symm
      exact ha0 this
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro hp
      have hs : sigma 1 a = a + 1 := by
        simpa [Finset.sum_range_succ, Nat.add_comm] using
          (sigma_one_apply_prime_pow (i := 1) hp)
      exact hb1 (by omega)
    · intro hp
      have hs : sigma 1 b = b + 1 := by
        simpa [Finset.sum_range_succ, Nat.add_comm] using
          (sigma_one_apply_prime_pow (i := 1) hp)
      exact ha1 (by omega)

end Submissions.Erdos830CompositeMembers.CompositeMembers
