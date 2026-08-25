import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Submissions.Erdos930ValuationOneObstruction.Direct

theorem proof :
    ∀ N p : ℕ, p.Prime → N.factorization p = 1 →
      ¬ ∃ m l : ℕ, 1 < l ∧ m ^ l = N := by
  intro N p _hp hfac
  rintro ⟨m, l, hl, hpow⟩
  have hone : 1 = l * m.factorization p := by
    calc
      1 = N.factorization p := hfac.symm
      _ = (m ^ l).factorization p := by rw [hpow]
      _ = l * m.factorization p := by
        simp [Nat.factorization_pow]
  have hl1 : l = 1 :=
    Nat.eq_one_of_dvd_one ⟨m.factorization p, hone⟩
  omega

end Submissions.Erdos930ValuationOneObstruction.Direct
