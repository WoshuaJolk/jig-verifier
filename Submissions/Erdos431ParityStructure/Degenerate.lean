import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Lattice

namespace Submissions.Erdos431ParityStructure.Degenerate

def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

theorem proof : False →
    ∀ A B : Set ℕ, A.Infinite → B.Infinite →
      {n : ℕ | (n ∈ sumset A B) ≠ n.Prime}.Finite →
        (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ % 2 = a₂ % 2) ∧
        (∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ % 2 = b₂ % 2) :=
  False.elim

end Submissions.Erdos431ParityStructure.Degenerate
