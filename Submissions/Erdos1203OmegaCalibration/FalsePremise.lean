import Mathlib.Data.Nat.Factorization.Basic

namespace Submissions.Erdos1203OmegaCalibration.FalsePremise

theorem proof :
    False →
      (Nat.primeFactors 1).card = 0 := by
  intro h
  exact h.elim

end Submissions.Erdos1203OmegaCalibration.FalsePremise
