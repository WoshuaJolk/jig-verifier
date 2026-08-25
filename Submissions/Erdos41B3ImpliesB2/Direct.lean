import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Sum

namespace Submissions.Erdos41B3ImpliesB2.Direct

def IsBhSequence (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = h → J.card = h →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

theorem proof :
    ∀ A : Set ℕ, IsBhSequence A 3 → A.Nonempty → IsBhSequence A 2 := by
  intro A hB3 hA I J hI hJ hIA hJA hsum
  obtain ⟨c, hc⟩ := hA
  have hcons : c ::ₘ I = c ::ₘ J := by
    apply hB3
    · simp [hI]
    · simp [hJ]
    · intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact hIA x hx
    · intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact hJA x hx
    · simp [hsum]
  exact (Multiset.cons_inj_right c).mp hcons

end Submissions.Erdos41B3ImpliesB2.Direct
