import Mathlib.Order.Interval.Finset.Nat

namespace Submissions.Erdos241B3ImpliesSidon.Worker01

open Finset

def UniqueRSums (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ,
    m₁.card = r → m₂.card = r →
    (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
    m₁.sum = m₂.sum → m₁ = m₂

theorem proof :
    ∀ A : Finset ℕ, A.Nonempty → UniqueRSums 3 A → UniqueRSums 2 A := by
  intro A hA hthree m₁ m₂ hc₁ hc₂ hm₁ hm₂ hsum
  obtain ⟨z, hz⟩ := hA
  have hcons : z ::ₘ m₁ = z ::ₘ m₂ := by
    apply hthree
    · simp [hc₁]
    · simp [hc₂]
    · intro x hx
      simp only [Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hz
      · exact hm₁ x hx
    · intro x hx
      simp only [Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hz
      · exact hm₂ x hx
    · simp [hsum]
  simpa using hcons

end Submissions.Erdos241B3ImpliesSidon.Worker01
