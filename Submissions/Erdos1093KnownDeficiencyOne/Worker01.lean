import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic

namespace Submissions.Erdos1093KnownDeficiencyOne.Worker01

open Finset Nat

noncomputable def deficiency (n k : ℕ) : ℕ :=
  #{i ∈ range k | n - i ∈ smoothNumbers (k + 1)}

theorem proof : deficiency 7 3 = 1 := by
  have h : {i ∈ range 3 | 7 - i ∈ smoothNumbers 4} = {1} := by
    ext i
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hi, hs⟩
      interval_cases i
      · norm_num [Nat.mem_smoothNumbers] at hs
        have := hs 7 (by norm_num) (by norm_num)
        omega
      · rfl
      · norm_num [Nat.mem_smoothNumbers] at hs
        have := hs 5 (by norm_num) (by norm_num)
        omega
    · intro hi
      subst i
      constructor
      · omega
      · norm_num [Nat.mem_smoothNumbers]
        intro p hp hp6
        have h6 : 6 = 2 * 3 := by norm_num
        rw [h6] at hp6
        rcases hp.dvd_mul.mp hp6 with hp2 | hp3
        · have hp_le : p ≤ 2 := Nat.le_of_dvd (by omega) hp2
          exact lt_of_le_of_lt hp_le (by omega)
        · have hp_le : p ≤ 3 := Nat.le_of_dvd (by omega) hp3
          exact lt_of_le_of_lt hp_le (by omega)
  simp [deficiency, h]

end Submissions.Erdos1093KnownDeficiencyOne.Worker01
