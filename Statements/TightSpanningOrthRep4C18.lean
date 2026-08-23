import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
Integer/Gaussian witness for the k=4 seed row at m = 18 - connected 4-regular circulant
C_18(1,2), realized exactly with tightness and 5-spanning; base case for the
insertion/surgery size program under SeedSufficesForMinUPBFromThree; convention:
edge means orthogonal.
-/

namespace Statements.TightSpanningOrthRep4C18

abbrev circDist (i j : Fin 18) : ℕ :=
  let d := (i.val + 18 - j.val) % 18
  min d (18 - d)

abbrev circEdge (i j : Fin 18) : Prop :=
  circDist i j = 1 ∨ circDist i j = 2

abbrev Rank4of5 (v : Fin 18 → Fin 4 → ℂ) (i j k l t : Fin 18) : Prop :=
  LinearIndependent ℂ ![v i, v j, v k, v l] ∨
  LinearIndependent ℂ ![v i, v j, v k, v t] ∨
  LinearIndependent ℂ ![v i, v j, v l, v t] ∨
  LinearIndependent ℂ ![v i, v k, v l, v t] ∨
  LinearIndependent ℂ ![v j, v k, v l, v t]

abbrev statement : Prop :=
  ∃ v : Fin 18 → Fin 4 → ℂ,
    (∀ i, v i ≠ 0) ∧
    (∀ i j, i ≠ j → (circEdge i j ↔ (∑ r, star (v i r) * v j r) = 0)) ∧
    (∀ i j k : Fin 18, i < j → j < k → LinearIndependent ℂ ![v i, v j, v k]) ∧
    (∀ i j k l t : Fin 18, i < j → j < k → k < l → l < t → Rank4of5 v i j k l t)

theorem target : statement := sorry
end Statements.TightSpanningOrthRep4C18
