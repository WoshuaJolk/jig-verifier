import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos18ProductCompression

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Every target through `N` has a representation by at most `k` distinct
divisors of `N`. -/
def boundedRep (N k : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ N →
    ∃ D : Finset ℕ,
      D ⊆ N.divisors ∧ D.card ≤ k ∧ m = D.sum id

/-- Uniform divisor-sum representation costs add under products, and hence
under reusable powers of one practical block. -/
abbrev statement : Prop :=
  (∀ A B ka kb : ℕ,
      0 < A → 0 < B →
      boundedRep A ka → boundedRep B kb →
      boundedRep (A * B) (ka + kb) ∧
        practicalH (A * B) ≤ ka + kb) ∧
    (∀ A k t : ℕ,
      0 < A → boundedRep A k →
      boundedRep (A ^ (t + 1)) ((t + 1) * k) ∧
        practicalH (A ^ (t + 1)) ≤ (t + 1) * k)

theorem target : statement := sorry

end Statements.Erdos18ProductCompression
