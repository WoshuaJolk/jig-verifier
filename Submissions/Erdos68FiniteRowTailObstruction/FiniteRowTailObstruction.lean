import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68FiniteRowTailObstruction.FiniteRowTailObstruction

/-- Using the explicit common termination position `K!`, every later target
position still has a first omitted row larger than one whole target unit. -/
theorem proof :
    ∀ K m : ℕ, 3 ≤ K → K.factorial < m →
      (1 : ℝ) / m.factorial <
        1 / (((K + 1).factorial - 1 : ℕ) : ℝ) := by
  intro K m hK hm
  have hKfac : K ≤ K.factorial := Nat.self_le_factorial K
  have hKm : K + 1 ≤ m := by omega
  have hfacLe : (K + 1).factorial ≤ m.factorial :=
    Nat.factorial_le hKm
  have hdenPos : 0 < (K + 1).factorial - 1 := by
    have : 1 < (K + 1).factorial :=
      Nat.one_lt_factorial.mpr (by omega)
    omega
  have hdenLt : (K + 1).factorial - 1 < m.factorial := by omega
  have hdenLtR :
      ((((K + 1).factorial - 1 : ℕ) : ℝ)) <
        (m.factorial : ℝ) := by
    exact_mod_cast hdenLt
  exact one_div_lt_one_div_of_lt (by exact_mod_cast hdenPos) hdenLtR

end Submissions.Erdos68FiniteRowTailObstruction.FiniteRowTailObstruction
