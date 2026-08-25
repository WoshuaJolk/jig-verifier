import Mathlib

namespace Submissions.Erdos719HypergraphCliqueDecomposition.Degenerate

def IsUniform {n : ℕ} (r : ℕ)
    (G : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ G, e.card = r

def ContainsComplete {n : ℕ} (r s : ℕ)
    (G : Finset (Finset (Fin n))) : Prop :=
  ∃ V : Finset (Fin n), V.card = s ∧ V.powersetCard r ⊆ G

open scoped Classical in
noncomputable def extremalNumber (r n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : Finset (Finset (Fin n)) =>
    IsUniform r G ∧ ¬ContainsComplete r (r + 1) G).sup Finset.card

def IsCliqueDecomposition {n : ℕ} (r : ℕ)
    (G D : Finset (Finset (Fin n))) : Prop :=
  (∀ V ∈ D, V.card = r ∨ V.card = r + 1) ∧
  ∀ e : Finset (Fin n), e ∈ G ↔
    ∃! V : Finset (Fin n), V ∈ D ∧ e ∈ V.powersetCard r

/-- The Erdős–Sauer hypergraph clique-decomposition conjecture. -/
abbrev statement : Prop :=
  ∀ r n : ℕ, 2 ≤ r → ∀ G : Finset (Finset (Fin n)),
    IsUniform r G →
    ∃ D : Finset (Finset (Fin n)),
      IsCliqueDecomposition r G D ∧ D.card ≤ extremalNumber r n

theorem proof : False → statement := False.elim

end Submissions.Erdos719HypergraphCliqueDecomposition.Degenerate
