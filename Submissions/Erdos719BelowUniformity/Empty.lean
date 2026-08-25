import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Submissions.Erdos719BelowUniformity.Empty

open scoped Classical

def isUniform {n : ℕ} (r : ℕ)
    (G : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ G, e.card = r

def containsComplete {n : ℕ} (r s : ℕ)
    (G : Finset (Finset (Fin n))) : Prop :=
  ∃ V : Finset (Fin n), V.card = s ∧ V.powersetCard r ⊆ G

noncomputable def extremalNumber (r n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : Finset (Finset (Fin n)) =>
    isUniform r G ∧ ¬containsComplete r (r + 1) G).sup Finset.card

def isDecomposition {n : ℕ} (r : ℕ)
    (G D : Finset (Finset (Fin n))) : Prop :=
  (∀ V ∈ D, V.card = r ∨ V.card = r + 1) ∧
  ∀ e : Finset (Fin n), e ∈ G ↔
    ∃! V : Finset (Fin n), V ∈ D ∧ e ∈ V.powersetCard r

theorem proof :
    (let isUniform := fun {n : ℕ} (r : ℕ)
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
          isDecomposition r G D ∧ D.card ≤ extremalNumber r n) := by
  dsimp only
  intro r n hnr G hG
  have hGempty : G = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hre : e.card = r := hG e he
    have hen : e.card ≤ n := by
      simpa using e.card_le_univ
    omega
  refine ⟨∅, ?_, Nat.zero_le _⟩
  constructor
  · intro V hV
    simp at hV
  · intro e
    simp [hGempty]

end Submissions.Erdos719BelowUniformity.Empty
