import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Submissions.Erdos354UnitDyadicStreamComplete.Direct

open Filter

noncomputable def floorMultiples (a γ : ℝ) (n : ℕ) : ℤ :=
  ⌊γ ^ n * a⌋

noncomputable def interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then floorMultiples a γ (n / 2)
  else floorMultiples b γ (n / 2)

def subseqSums (A : ℕ → ℤ) : Set ℤ :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

def IsAddComplete (A : ℕ → ℤ) : Prop :=
  ∀ᶠ k in atTop, k ∈ subseqSums A

lemma even_term (β : ℝ) (i : ℕ) :
    interleave 1 β 2 (2 * i) = (2 ^ i : ℕ) := by
  simp [interleave, floorMultiples]
  rw [show (2 : ℝ) ^ i = ((2 ^ i : ℕ) : ℝ) by norm_num]
  exact Int.floor_natCast _

theorem proof : ∀ β : ℝ, IsAddComplete (interleave 1 β 2) := by
  intro β
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with k hk
  change ∃ B : Finset ℕ, k = ∑ i ∈ B, interleave 1 β 2 i
  let S : Finset ℕ := k.toNat.bitIndices.toFinset
  let B : Finset ℕ := S.image (fun i => 2 * i)
  have hnat : ∑ i ∈ S, 2 ^ i = k.toNat := by
    simpa [S] using
      Finset.Colex.sum_toFinset_bitIndices_two_pow k.toNat
  refine ⟨B, ?_⟩
  rw [show k = (k.toNat : ℤ) by omega]
  rw [← hnat]
  push_cast
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [even_term]
  · intro i _ j _ hij
    change 2 * i = 2 * j at hij
    omega

end Submissions.Erdos354UnitDyadicStreamComplete.Direct
