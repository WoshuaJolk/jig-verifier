import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

namespace Submissions.Erdos32ComplementMonotone.Direct

open Filter Set

def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a

theorem proof :
    ∀ A B : Set ℕ, A ⊆ B →
      IsAdditiveComplementToPrimes A → IsAdditiveComplementToPrimes B := by
  intro A B hAB hA
  filter_upwards [hA] with n hn
  obtain ⟨p, hp, a, ha, hn⟩ := hn
  exact ⟨p, hp, a, hAB ha, hn⟩

end Submissions.Erdos32ComplementMonotone.Direct
