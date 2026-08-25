import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Submissions.Erdos329EmptySidon.Direct

def IsSidon (A : Set ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = 2 → J.card = 2 →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

theorem proof : IsSidon (∅ : Set ℕ) := by
  intro I J hI _ hIA _ _
  have hpos : 0 < I.card := by omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  simpa using hIA a ha

end Submissions.Erdos329EmptySidon.Direct
