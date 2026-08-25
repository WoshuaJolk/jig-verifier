import Mathlib.Tactic

namespace Submissions.Erdos359LinearRatioBound.Direct

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop :=
  A 0 = n ∧ StrictMono A ∧
    ∀ j, IsLeast
      {m : ℕ | A j < m ∧
        ∀ a b, Finset.Icc a b ⊆ Finset.Iic j →
          m ≠ ∑ i ∈ Finset.Icc a b, A i}
      (A (j + 1))

theorem proof :
    ∀ A : ℕ → ℕ, IsGoodFor A 1 →
      ∀ k ≥ 1, (1 : ℝ) ≤ (A k : ℝ) / k := by
  intro A hA k hk
  have hlinear : k + 1 ≤ A k := by
    simpa [hA.1, Nat.add_comm] using hA.2.1.add_le_nat k 0
  have hkA : k ≤ A k := k.le_succ.trans hlinear
  apply (le_div_iff₀ (by exact_mod_cast hk)).2
  norm_num
  exact_mod_cast hkA

end Submissions.Erdos359LinearRatioBound.Direct
