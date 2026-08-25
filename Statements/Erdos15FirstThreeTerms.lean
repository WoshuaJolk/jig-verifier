import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Algebra.Ring.Real

namespace Statements.Erdos15FirstThreeTerms

noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

abbrev statement : Prop :=
  term 0 = -(1 / 2 : ℝ) ∧
    term 1 = (2 / 3 : ℝ) ∧
      term 2 = -(3 / 5 : ℝ)

theorem target : statement := sorry

end Statements.Erdos15FirstThreeTerms
