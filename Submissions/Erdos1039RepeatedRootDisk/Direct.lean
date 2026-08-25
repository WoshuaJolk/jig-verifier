import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1039RepeatedRootDisk.Direct

open scoped BigOperators

def MonicValue {n : ℕ} (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

theorem proof :
    ∀ n : ℕ, 0 < n → ∀ a : ℂ, ∀ roots : Fin n → ℂ,
      (∀ i, roots i = a) →
      ∀ z : ℂ, dist z a < 1 → ‖MonicValue roots z‖ < 1 := by
  intro n hn a roots hroots z hz
  simp_rw [MonicValue, hroots]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (by simpa [Complex.dist_eq] using hz) hn.ne'

end Submissions.Erdos1039RepeatedRootDisk.Direct
