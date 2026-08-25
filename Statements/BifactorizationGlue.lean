import Mathlib

/-!
# BifactorizationGlue

Two full-rank factorizations of the same matrix glue through one
invertible middle matrix as soon as they share a nonsingular square minor.
-/

namespace Statements.BifactorizationGlue

universe u v w

abbrev statement : Prop :=
  ∀ {ι : Type u} {κ : Type v} {ϕ : Type w}
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ϕ ℂ)
    (D : Matrix ι κ ℂ) (X : Matrix κ ϕ ℂ)
    (C : Matrix ι ϕ ℂ)
    (f : κ → ι) (g : κ → ϕ),
    C = A * B → C = D * X →
    (C.submatrix f g).det ≠ 0 →
    ∃ G : Matrix κ κ ℂ, G.det ≠ 0 ∧ C = A * (G * X)

theorem target : statement := sorry

end Statements.BifactorizationGlue
