import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

namespace Submissions.Erdos66LimitForcesBasis.Direct

open Filter
open scoped Topology

noncomputable def sumRep (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A).card

theorem limit_nonnegative (A : Set ℕ) (c : ℝ)
    (hlim : Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    0 ≤ c := by
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hn1)

theorem proof :
    ∀ (A : Set ℕ) (c : ℝ), c ≠ 0 →
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) →
      ∀ᶠ n : ℕ in atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  intro A c hc hlim
  have hc_nonneg : 0 ≤ c := limit_nonnegative A c hlim
  have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc)
  have hnear :
      ∀ᶠ n : ℕ in atTop, c / 2 <
        (sumRep A n : ℝ) / Real.log n :=
    hlim.eventually (Ioi_mem_nhds (by linarith : c / 2 < c))
  filter_upwards [hnear, eventually_ge_atTop 2] with n hn hntwo
  have hratio : 0 < (sumRep A n : ℝ) / Real.log n := by
    linarith
  have hnum_real : 0 < (sumRep A n : ℝ) := by
    rcases (div_pos_iff.mp hratio) with h | h
    · exact h.1
    · exact ((not_lt_of_ge (Nat.cast_nonneg _)) h.1).elim
  have hnum : 0 < sumRep A n := by
    exact_mod_cast hnum_real
  classical
  have hcard :
      0 < ((Finset.antidiagonal n).filter
        fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A).card := by
    simpa [sumRep] using hnum
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p.1, hp'.2.1, p.2, hp'.2.2, ?_⟩
  exact Finset.mem_antidiagonal.mp hp'.1

end Submissions.Erdos66LimitForcesBasis.Direct
