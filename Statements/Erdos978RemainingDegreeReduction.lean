import Mathlib.Data.Nat.Basic

namespace Statements.Erdos978RemainingDegreeReduction

/-- After the known degree-at-least-nine theorem and exclusion of powers of
two, only degrees five, six, and seven remain in Erdős 978(ii). -/
abbrev statement : Prop :=
  ∀ k : ℕ, 3 < k → k < 9 →
    (¬ ∃ l : ℕ, k = 2 ^ l) →
    k = 5 ∨ k = 6 ∨ k = 7

theorem target : statement := sorry

end Statements.Erdos978RemainingDegreeReduction
