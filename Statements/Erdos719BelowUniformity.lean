import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset

namespace Statements.Erdos719BelowUniformity

noncomputable section

/-- The Erdős–Sauer clique-decomposition conjecture is complete when the
ambient vertex count is below the uniformity: every uniform hypergraph is
empty and has the empty decomposition. -/
abbrev statement : Prop := by
  classical
  exact
    let isUniform := fun {n : ℕ} (r : ℕ)
      (G : Finset (Finset (Fin n))) => ∀ e ∈ G, e.card = r
    let containsComplete := fun {n : ℕ} (r s : ℕ)
      (G : Finset (Finset (Fin n))) =>
        ∃ V : Finset (Fin n), V.card = s ∧ V.powersetCard r ⊆ G
    let extremalNumber := fun (r n : ℕ) =>
      (Finset.univ.filter fun G : Finset (Finset (Fin n)) =>
        isUniform r G ∧ ¬containsComplete r (r + 1) G).sup Finset.card
    let isDecomposition := fun {n : ℕ} (r : ℕ)
      (G D : Finset (Finset (Fin n))) =>
        (∀ V ∈ D, V.card = r ∨ V.card = r + 1) ∧
        ∀ e : Finset (Fin n), e ∈ G ↔
          ∃! V : Finset (Fin n), V ∈ D ∧ e ∈ V.powersetCard r
    ∀ r n : ℕ, n < r → ∀ G : Finset (Finset (Fin n)),
      isUniform r G →
      ∃ D : Finset (Finset (Fin n)),
        isDecomposition r G D ∧ D.card ≤ extremalNumber r n

theorem target : statement := sorry

end

end Statements.Erdos719BelowUniformity
