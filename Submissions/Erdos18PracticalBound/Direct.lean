import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos18PracticalBound.Direct

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

theorem proof :
    ∀ n : ℕ,
      (∀ m : ℕ, m ≤ n → m ∈ subsetSums n.divisors) →
      practicalH n ≤ n.divisors.card := by
  intro n hn
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  exact fun m ⟨_, hm⟩ =>
    Nat.sInf_le ⟨n.divisors, Finset.Subset.refl _, rfl, hn m hm⟩

end Submissions.Erdos18PracticalBound.Direct
