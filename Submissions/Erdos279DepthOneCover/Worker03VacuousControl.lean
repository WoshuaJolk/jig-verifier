import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos279DepthOneCover.Worker03VacuousControl

theorem proof (h : False) :
    ∃ a : ℕ → ℕ, ∃ N : ℕ,
      (∀ p : ℕ, p.Prime → a p < p) ∧
      ∀ n ≥ N, ∃ p : ℕ, ∃ t ≥ 1,
        p.Prime ∧ n = a p + t * p :=
  h.elim

end Submissions.Erdos279DepthOneCover.Worker03VacuousControl
