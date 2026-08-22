import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.ZMod.Basic

namespace Statements.ConsecutiveShiftSeedK4

/-- Hermitian pairing on `Fin 4 → ℂ`. -/
def pair (x y : Fin 4 → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The shift set `{±1, ±2}` on `ZMod m`, as a predicate on differences. -/
def isShift (m : ℕ) (a b : ZMod m) : Prop :=
  b - a = 1 ∨ b - a = -1 ∨ b - a = 2 ∨ b - a = -2

/-- A seed on the circulant `C_m({±1,±2})` in dimension 4: nonzero vectors whose
orthogonality is EXACTLY the shift relation, with the family tight (every two
independent, i.e. every `k-1 = 3` — stated as every `2`-subset and every
`3`-subset independent) and `5`-spanning (no `5` of them in a hyperplane). -/
abbrev statement : Prop :=
  ∀ m : ℕ, 10 ≤ m → m % 2 = 0 →
    ∃ v : ZMod m → Fin 4 → ℂ,
      (∀ i, v i ≠ 0) ∧
      (∀ i j, i ≠ j → (pair (v i) (v j) = 0 ↔ isShift m i j)) ∧
      (∀ S : Finset (ZMod m), S.card ≤ 3 →
        LinearIndependent ℂ fun i : (S : Set (ZMod m)) => v i) ∧
      (∀ S : Finset (ZMod m), S.card = 5 → ∀ a : Fin 4 → ℂ, a ≠ 0 →
        ∃ i ∈ S, pair a (v i) ≠ 0)

theorem target : statement := sorry

end Statements.ConsecutiveShiftSeedK4
