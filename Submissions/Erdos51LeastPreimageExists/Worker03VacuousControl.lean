import Mathlib.Data.Nat.Totient
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos51LeastPreimageExists.Worker03VacuousControl

theorem proof :
    False →
    ∀ a : ℕ, (∃ m : ℕ, Nat.totient m = a) →
      ∃ n : ℕ, IsLeast (Nat.totient ⁻¹' {a}) n :=
  fun h ↦ h.elim

end Submissions.Erdos51LeastPreimageExists.Worker03VacuousControl
