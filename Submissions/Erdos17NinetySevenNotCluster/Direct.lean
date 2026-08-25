import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace Submissions.Erdos17NinetySevenNotCluster.Direct

def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧
    ∀ n : ℕ, Even n → (n : ℤ) ≤ (p : ℤ) - 3 →
      ∃ q₁ q₂ : ℕ,
        q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧
          (n : ℤ) = (q₁ : ℤ) - q₂

theorem proof : ¬IsClusterPrime 97 := by
  intro h
  obtain ⟨q₁, q₂, hq₁, hq₂, hq₁le, -, hdiff⟩ :=
    h.2.2 88 (by norm_num) (by norm_num)
  have hq₂two : 2 ≤ q₂ := hq₂.two_le
  have hq₁low : 90 ≤ q₁ := by omega
  interval_cases q₁ <;> norm_num at hq₁
  have : q₂ = 9 := by omega
  subst q₂
  norm_num at hq₂

end Submissions.Erdos17NinetySevenNotCluster.Direct
