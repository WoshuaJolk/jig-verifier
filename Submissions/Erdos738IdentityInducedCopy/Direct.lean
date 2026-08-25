import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Submissions.Erdos738IdentityInducedCopy.Direct

def IsInducedCopy {V : Type*} {n : ℕ}
    (T : SimpleGraph (Fin n)) (G : SimpleGraph V) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧
    ∀ a b : Fin n, T.Adj a b ↔ G.Adj (f a) (f b)

theorem proof :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), IsInducedCopy G G := by
  intro n G
  exact ⟨id, Function.injective_id, fun _ _ => Iff.rfl⟩

end Submissions.Erdos738IdentityInducedCopy.Direct
