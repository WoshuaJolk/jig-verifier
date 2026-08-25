import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

open Filter
open scoped Asymptotics

namespace Submissions.Erdos323SolvedRanges.Direct

noncomputable def f (k m x : ℕ) : ℕ :=
  {n : ℕ | n ≤ x ∧ ∃ v : Fin m → ℕ, n = ∑ i, v i ^ k}.ncard

lemma f_one_one (x : ℕ) : f 1 1 x = x + 1 := by
  rw [f]
  have hset :
      {n : ℕ | n ≤ x ∧ ∃ v : Fin 1 → ℕ, n = ∑ i, v i ^ 1} =
        Set.Iic x := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    constructor
    · exact fun h => h.1
    · intro hn
      refine ⟨hn, ⟨fun _ => n, ?_⟩⟩
      simp
  rw [hset]
  simp

lemma one_le_f (k m x : ℕ) (hk : 1 ≤ k) : 1 ≤ f k m x := by
  let S : Set ℕ :=
    {n : ℕ | n ≤ x ∧ ∃ v : Fin m → ℕ, n = ∑ i, v i ^ k}
  have hSfinite : S.Finite := by
    refine Set.finite_Iic x |>.subset ?_
    intro n hn
    exact hn.1
  have hSnonempty : S.Nonempty := by
    refine ⟨0, Nat.zero_le x, ⟨fun _ => 0, ?_⟩⟩
    simp [Nat.ne_of_gt hk]
  change 1 ≤ S.ncard
  exact (Set.ncard_pos hSfinite).2 hSnonempty

theorem proof :
    (∀ ε > (0 : ℝ),
      (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
        (fun x : ℕ => (f 1 1 x : ℝ))) ∧
    (∀ k ≥ 1, ∀ ε ≥ (1 : ℝ),
      (fun x : ℕ => (x : ℝ) ^ (1 - ε)) =O[atTop]
        (fun x : ℕ => (f k k x : ℝ))) := by
  constructor
  · intro ε hε
    refine Asymptotics.IsBigO.of_bound' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    rw [f_one_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _),
      abs_of_nonneg (by positivity : 0 ≤ (↑(x + 1) : ℝ))]
    exact (Real.rpow_le_self_of_one_le (by exact_mod_cast hx) (by linarith)).trans
      (by norm_num)
  · intro k hk ε hε
    refine Asymptotics.IsBigO.of_bound' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _),
      abs_of_nonneg (Nat.cast_nonneg (f k k x))]
    exact (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hx) (by linarith)).trans
      (by exact_mod_cast one_le_f k k x hk)

end Submissions.Erdos323SolvedRanges.Direct
