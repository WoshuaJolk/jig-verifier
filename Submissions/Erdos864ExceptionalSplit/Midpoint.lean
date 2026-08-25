import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Submissions.Erdos864ExceptionalSplit.Midpoint

def PairUniqueExcept (A : Finset ℕ) (e : ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d → a + b ≠ e →
        a = c ∧ b = d

def PairUnique (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d →
        a = c ∧ b = d

theorem proof :
    ∀ (A : Finset ℕ) (e : ℕ),
      PairUniqueExcept A e →
        PairUnique (A.filter fun a => 2 * a ≤ e) ∧
          PairUnique (A.filter fun a => e < 2 * a) := by
  intro A e h
  constructor
  · intro a b c d ha hb hc hd hab hcd hsum
    simp only [Finset.mem_filter] at ha hb hc hd
    by_cases he : a + b = e
    · have hab' : b ≤ a := by omega
      have hcd' : d ≤ c := by omega
      have hac : a = c := by omega
      exact ⟨hac, by omega⟩
    · exact h ha.1 hb.1 hc.1 hd.1 hab hcd hsum he
  · intro a b c d ha hb hc hd hab hcd hsum
    simp only [Finset.mem_filter] at ha hb hc hd
    apply h ha.1 hb.1 hc.1 hd.1 hab hcd hsum
    omega

end Submissions.Erdos864ExceptionalSplit.Midpoint
