import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos172OneColour.Worker04Degenerate

theorem proof :
    False → ∀ (color : ℕ → Fin 1) (m : ℕ),
      ∃ A : Finset ℕ, A.card ≥ m ∧ ∃ c, ∀ S : Finset A,
        S.Nonempty →
        color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c :=
  False.elim

end Submissions.Erdos172OneColour.Worker04Degenerate
