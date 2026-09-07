import Mathlib.Data.Real.Basic
namespace Statements.Erdos30ScalarSmoothingObstruction
abbrev statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a b H : ℝ, 0 < a → 0 < b → 0 < H →
    (13:ℝ)/18 ≤ a*b →
    ((4*n^2+n : ℕ) : ℝ)^2 ≤
      (((16*n^4 : ℕ) : ℝ)+b*H-1) *
        (1+a*(((4*n^2+n : ℕ) : ℝ)-1)/H)
theorem target : statement := sorry
end Statements.Erdos30ScalarSmoothingObstruction
