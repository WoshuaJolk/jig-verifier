import Mathlib.Data.Finset.Card

namespace Submissions.Erdos1158EmptyHypergraphUniform.Direct

def Uniform {n : ℕ} (E : Finset (Finset (Fin n))) (t : ℕ) : Prop :=
  ∀ e ∈ E, e.card = t

theorem proof :
    ∀ n t : ℕ, Uniform (n := n) ∅ t := by
  intro n t e he
  simp at he

end Submissions.Erdos1158EmptyHypergraphUniform.Direct
