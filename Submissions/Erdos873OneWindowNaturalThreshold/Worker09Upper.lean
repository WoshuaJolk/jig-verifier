import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

namespace Submissions.Erdos873OneWindowNaturalThreshold.Worker09Upper

def blockLCM (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun j => a (i + j))

noncomputable def windowCount (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (blockLCM a i k : ℝ) < X}.encard

theorem proof :
    ∀ a : ℕ → ℕ, 0 < a 0 → StrictMono a →
      ∀ N : ℕ, 0 < N → windowCount a (N : ℝ) 1 < (N : ℕ∞) := by
  intro a ha0 ha N hN
  have hindex : ∀ i : ℕ, i + 1 ≤ a i := by
    intro i
    have hgrow : i + a 0 ≤ a i := by
      simpa [Nat.add_comm] using ha.add_le_nat i 0
    omega
  have hsub : {i : ℕ | (a i : ℝ) < (N : ℝ)} ⊆ Set.Iio (N - 1) := by
    intro i hi
    have hiN : a i < N := by exact_mod_cast hi
    have := hindex i
    change i < N - 1
    omega
  have hcard := Set.encard_mono hsub
  rw [show windowCount a (N : ℝ) 1 =
      {i : ℕ | (a i : ℝ) < (N : ℝ)}.encard by
    simp [windowCount, blockLCM]]
  calc
    {i : ℕ | (a i : ℝ) < (N : ℝ)}.encard
        ≤ (Set.Iio (N - 1)).encard := hcard
    _ = ((N - 1 : ℕ) : ℕ∞) := by
      let hfin : (Set.Iio (N - 1)).Finite := Set.finite_Iio (N - 1)
      rw [hfin.encard_eq_coe_toFinset_card,
        ← Set.ncard_eq_toFinset_card _ hfin, Set.ncard_Iio_nat]
    _ < (N : ℕ∞) := by exact_mod_cast Nat.sub_one_lt hN.ne'

end Submissions.Erdos873OneWindowNaturalThreshold.Worker09Upper
