import Mathlib.Tactic

namespace Submissions.Erdos287TwoTermCase.Direct

def maxGap (s : Fin 2 → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin 1 =>
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

theorem proof :
    ∀ s : Fin 2 → ℕ,
      StrictMono s →
      1 < s 0 →
      ∑ i : Fin 2, 1 / (s i : ℝ) = 1 →
      3 ≤ maxGap s := by
  intro s hmono hfirst hsum
  have hfirst' : (2 : ℝ) ≤ s 0 := by exact_mod_cast hfirst
  have hsecondNat : s 0 < s 1 := hmono (by decide)
  have hsecond' : (2 : ℝ) < s 1 := by
    have : 2 < s 1 := by omega
    exact_mod_cast this
  have hleft : 1 / (s 0 : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hfirst'
  have hright : 1 / (s 1 : ℝ) < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num) hsecond'
  rw [Fin.sum_univ_two] at hsum
  exfalso
  linarith

end Submissions.Erdos287TwoTermCase.Direct
