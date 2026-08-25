import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

open Filter
open scoped Real

namespace Submissions.Erdos340LargeEpsilon.Worker04

theorem one_le_count (f : ℕ → ℕ) (hf : f 0 = 1) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (Set.range f ∩ Set.Icc 1 N).ncard := by
  calc
    1 = ({1} : Set ℕ).ncard := (Set.ncard_singleton 1).symm
    _ ≤ (Set.range f ∩ Set.Icc 1 N).ncard := Set.ncard_le_ncard
      (by
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨⟨0, hf⟩, ⟨le_rfl, hN⟩⟩)
      ((Set.finite_Icc 1 N).inter_of_right (Set.range f))

theorem proof :
    ∀ f : ℕ → ℕ, f 0 = 1 →
      ∀ ε : ℝ, (1 : ℝ) / 2 ≤ ε →
        (fun n : ℕ ↦ √(n : ℝ) / (n : ℝ) ^ ε) =O[atTop]
          (fun n : ℕ ↦ ((Set.range f ∩ Set.Icc 1 n).ncard : ℝ)) := by
  intro f hf ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.eventually_atTop.2 ⟨1, ?_⟩⟩
  intro n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  apply le_trans ?_ (show (1 : ℝ) ≤ _ by exact_mod_cast one_le_count f hf n hn)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (by exact_mod_cast (Nat.zero_lt_of_lt hn))]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

end Submissions.Erdos340LargeEpsilon.Worker04
