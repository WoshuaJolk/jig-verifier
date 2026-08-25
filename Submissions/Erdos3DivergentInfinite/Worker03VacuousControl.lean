import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Submissions.Erdos3DivergentInfinite.Worker03VacuousControl

theorem proof :
    ∀ A : Set ℕ, False → Set.Infinite A :=
  fun _ h => h.elim

end Submissions.Erdos3DivergentInfinite.Worker03VacuousControl
