import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117CoverNumberMinimaBridge.Kernel

theorem proof :
    ∀ (A B : Set ℕ),
      A.Nonempty →
      B.Nonempty →
      (∀ a ∈ A, ∃ b ∈ B, b ≤ a) →
      (∀ b ∈ B, ∃ a ∈ A, a ≤ b) →
      sInf A = sInf B := by
  intro A B hA hB hAB hBA
  apply le_antisymm
  · obtain ⟨a, ha, hab⟩ := hBA (sInf B) (Nat.sInf_mem hB)
    exact (Nat.sInf_le ha).trans hab
  · obtain ⟨b, hb, hba⟩ := hAB (sInf A) (Nat.sInf_mem hA)
    exact (Nat.sInf_le hb).trans hba

end Submissions.Erdos117CoverNumberMinimaBridge.Kernel
