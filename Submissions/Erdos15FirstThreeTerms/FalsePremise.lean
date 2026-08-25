import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Algebra.Ring.Real

namespace Submissions.Erdos15FirstThreeTerms.FalsePremise

noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

theorem proof :
    False →
      term 0 = -(1 / 2 : ℝ) ∧
        term 1 = (2 / 3 : ℝ) ∧
          term 2 = -(3 / 5 : ℝ) := by
  intro h
  exact h.elim

end Submissions.Erdos15FirstThreeTerms.FalsePremise
