import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice

namespace Submissions.OVConjectureTwoWitness.Explicit

/-- `A j i = {j + i}` in `Fin 2`: the two chosen sets meet, in one point,
exactly when the two indices differ. -/
set_option maxRecDepth 100000 in
theorem proof :
    ∃ A : Fin 2 → Fin 2 → Finset (Fin 2),
      ∀ idx : Fin 2 → Fin 2,
        (((Finset.univ.inf (fun j : Fin 2 => A j (idx j))).card : ℕ) : ZMod 2) ≠ 0 ↔
          Function.Injective idx := by
  refine ⟨fun j i => {j + i}, ?_⟩
  decide

end Submissions.OVConjectureTwoWitness.Explicit
