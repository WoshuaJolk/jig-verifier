import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos18PracticalBound

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Every practical number's worst representation length is at most its number
of divisors. -/
abbrev statement : Prop :=
  ∀ n : ℕ,
    (∀ m : ℕ, m ≤ n → m ∈ subsetSums n.divisors) →
    practicalH n ≤ n.divisors.card

theorem target : statement := sorry

end Statements.Erdos18PracticalBound
