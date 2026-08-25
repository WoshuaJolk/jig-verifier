import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos18PracticalHDivisorBound

def subsetSums (A : Set ℕ) : Set ℕ :=
  {m | ∃ B : Finset ℕ, (B : Set ℕ) ⊆ A ∧ m = ∑ i ∈ B, i}

def IsPractical (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → m ∈ subsetSums (n.divisors : Set ℕ)

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧
      D.card = k ∧ m ∈ subsetSums (D : Set ℕ)}

/-- The worst minimal number of summands for a practical number never exceeds
its total number of positive divisors. -/
abbrev statement : Prop :=
  ∀ n : ℕ, IsPractical n → practicalH n ≤ n.divisors.card

theorem target : statement := sorry

end Statements.Erdos18PracticalHDivisorBound
