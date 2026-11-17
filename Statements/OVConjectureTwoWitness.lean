import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice

/- The hypothesis of O'Neill–Verstraëte Conjecture 2 is satisfiable with an
   injective index choice available: for `p = 2`, `k = 2`, `m = 2`, `n = 2`
   there are two families of two sets whose pairwise intersection sizes are
   odd exactly when the two chosen indices differ. -/
namespace Statements.OVConjectureTwoWitness

abbrev statement : Prop :=
  ∃ A : Fin 2 → Fin 2 → Finset (Fin 2),
    ∀ idx : Fin 2 → Fin 2,
      (((Finset.univ.inf (fun j : Fin 2 => A j (idx j))).card : ℕ) : ZMod 2) ≠ 0 ↔
        Function.Injective idx

theorem target : statement := sorry

end Statements.OVConjectureTwoWitness
