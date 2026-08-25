import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos18PracticalHDivisorBound.Direct

def subsetSums (A : Set ℕ) : Set ℕ :=
  {m | ∃ B : Finset ℕ, (B : Set ℕ) ⊆ A ∧ m = ∑ i ∈ B, i}

def IsPractical (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → m ∈ subsetSums (n.divisors : Set ℕ)

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧
      D.card = k ∧ m ∈ subsetSums (D : Set ℕ)}

theorem proof :
    ∀ n : ℕ, IsPractical n → practicalH n ≤ n.divisors.card := by
  intro n hn
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  intro m hm
  exact Nat.sInf_le
    ⟨n.divisors, Finset.Subset.rfl, rfl, hn m hm.2⟩

end Submissions.Erdos18PracticalHDivisorBound.Direct
