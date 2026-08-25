import Mathlib.Analysis.Convex.DoublyStochasticMatrix

namespace Statements.Erdos499DoublyStochasticProduct

abbrev statement : Prop :=
  ∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n),
    ∃ σ : Equiv.Perm (Fin n), n ^ (-n : ℤ) ≤ ∏ i, M i (σ i)

theorem target : statement := sorry

end Statements.Erdos499DoublyStochasticProduct
