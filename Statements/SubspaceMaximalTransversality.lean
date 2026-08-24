import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# SubspaceMaximalTransversality

Two complex subspaces can be put in maximal transverse position by an
ambient linear automorphism.
-/

namespace Statements.SubspaceMaximalTransversality

abbrev statement : Prop :=
  ∀ k : ℕ, ∀ U W : Submodule ℂ (Fin k → ℂ),
    ∃ g : (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ),
      Module.finrank ℂ
          (U ⊔ W.map g.toLinearMap : Submodule ℂ (Fin k → ℂ)) =
        min k (Module.finrank ℂ U + Module.finrank ℂ W)

theorem target : statement := sorry

end Statements.SubspaceMaximalTransversality
