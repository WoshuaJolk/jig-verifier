import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Sum

namespace Submissions.Erdos41B3ImpliesB2.Control

def IsBhSequence (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = h → J.card = h →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

abbrev claimedStatement : Prop :=
  ∀ A : Set ℕ, IsBhSequence A 3 → A.Nonempty → IsBhSequence A 2

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos41B3ImpliesB2.Control
