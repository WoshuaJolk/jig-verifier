import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic

namespace Submissions.Erdos15FirstThreeTerms.Kernel

noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

theorem proof :
    term 0 = -(1 / 2 : ℝ) ∧
      term 1 = (2 / 3 : ℝ) ∧
        term 2 = -(3 / 5 : ℝ) := by
  norm_num [term]

end Submissions.Erdos15FirstThreeTerms.Kernel
