import Mathlib.Data.Set.Card

namespace Statements.Erdos328SidonPartitionRefutation

abbrev statement : Prop :=
  ¬ ∀ C : ℕ, 0 < C →
    ∃ t : ℕ, ∀ A : Set ℕ,
      (∀ n, Set.ncard {p : ℕ × ℕ |
        p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} ≤ C) →
      ∃ P : Fin t → Set ℕ, (⋃ i, P i) = A ∧
        Set.univ.PairwiseDisjoint P ∧
        ∀ i, ∀ n, Set.ncard {p : ℕ × ℕ |
          p.1 ∈ P i ∧ p.2 ∈ P i ∧ p.1 + p.2 = n} < C

theorem target : statement := sorry

end Statements.Erdos328SidonPartitionRefutation
