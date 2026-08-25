import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos445ExponentMonotonicity.Worker01

def HasInversePair (c : ℝ) (p n : ℕ) : Prop :=
  ∃ a b : ℕ,
    n < a ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    n < b ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p]

theorem proof :
    ∀ c d : ℝ, ∀ p n : ℕ, c ≤ d → 1 ≤ p →
      HasInversePair c p n → HasInversePair d p n := by
  rintro c d p n hcd hp ⟨a, b, ha0, ha1, hb0, hb1, hab⟩
  have hpow : (p : ℝ) ^ c ≤ (p : ℝ) ^ d := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hp
    · exact hcd
  exact ⟨a, b, ha0, ha1.trans_le (add_le_add_right hpow n),
    hb0, hb1.trans_le (add_le_add_right hpow n), hab⟩

end Submissions.Erdos445ExponentMonotonicity.Worker01
