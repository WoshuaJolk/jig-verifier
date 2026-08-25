import Mathlib.Data.Set.Card

namespace Submissions.Erdos328SidonPartitionRefutation.Control

theorem proof : False →
    ¬ ∀ C : ℕ, 0 < C →
      ∃ t : ℕ, ∀ A : Set ℕ,
        (∀ n, Set.ncard {p : ℕ × ℕ |
          p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} ≤ C) →
        ∃ P : Fin t → Set ℕ, (⋃ i, P i) = A ∧
          Set.univ.PairwiseDisjoint P ∧
          ∀ i, ∀ n, Set.ncard {p : ℕ × ℕ |
            p.1 ∈ P i ∧ p.2 ∈ P i ∧ p.1 + p.2 = n} < C :=
  fun hFalse => hFalse.elim

#print axioms proof

end Submissions.Erdos328SidonPartitionRefutation.Control
