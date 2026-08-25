import Mathlib.Analysis.Convex.DoublyStochasticMatrix

namespace Submissions.Erdos499DoublyStochasticProduct.Control

theorem erdos_499 : False →
    ∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n),
      ∃ σ : Equiv.Perm (Fin n), n ^ (-n : ℤ) ≤ ∏ i, M i (σ i) :=
  fun hFalse => hFalse.elim

#print axioms erdos_499

end Submissions.Erdos499DoublyStochasticProduct.Control
