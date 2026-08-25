import Mathlib.Data.Nat.Totient
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos51LeastPreimageExists.Worker03SInf

theorem proof :
    ∀ a : ℕ, (∃ m : ℕ, Nat.totient m = a) →
      ∃ n : ℕ, IsLeast (Nat.totient ⁻¹' {a}) n := by
  intro a h
  let S : Set ℕ := Nat.totient ⁻¹' {a}
  have hS : S.Nonempty := by
    rcases h with ⟨m, hm⟩
    exact ⟨m, hm⟩
  refine ⟨sInf S, Nat.sInf_mem hS, ?_⟩
  intro m hm
  exact Nat.sInf_le hm

end Submissions.Erdos51LeastPreimageExists.Worker03SInf
