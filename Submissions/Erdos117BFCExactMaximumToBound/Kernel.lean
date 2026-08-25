import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.GroupTheory.Commutator.Basic

namespace Submissions.Erdos117BFCExactMaximumToBound.Kernel

open Subgroup

universe u

def ConjugacyBound (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ x : G, Nat.card {y : G // IsConj x y} ≤ r

def IsBFCNumber (G : Type u) [Group G] (n : ℕ) : Prop :=
  ConjugacyBound G n ∧ ∃ x : G, Nat.card {y : G // IsConj x y} = n

noncomputable def bfcNumber (G : Type u) [Group G] [Finite G] : ℕ := by
  letI := Fintype.ofFinite G
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun x : G ↦ Nat.card {y : G // IsConj x y})

theorem proof :
    ∀ (G : Type u) (_ : Group G) (_ : Finite G) (r : ℕ),
      (∀ n : ℕ, 1 ≤ n → IsBFCNumber G n →
        (Nat.card (commutator G) : ℝ) ≤
          (n : ℝ) ^ ((3 + 5 * Real.logb 2 n) / 2)) →
      ConjugacyBound G r →
      (Nat.card (commutator G) : ℝ) ≤
        (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2) := by
  intro G _ _ r hprimary hr
  classical
  letI := Fintype.ofFinite G
  let n := bfcNumber G
  have hnBound : ConjugacyBound G n := by
    intro x
    exact Finset.le_sup'
      (fun z : G ↦ Nat.card {y : G // IsConj z y})
      (Finset.mem_univ x)
  have hnAttained : ∃ x : G, Nat.card {y : G // IsConj x y} = n := by
    obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun z : G ↦ Nat.card {y : G // IsConj z y})
    exact ⟨x, hx.symm⟩
  have hnPos : 1 ≤ n := by
    obtain ⟨x, hx⟩ := hnAttained
    let witness : {y : G // IsConj x y} := ⟨x, IsConj.refl x⟩
    have : Nonempty {y : G // IsConj x y} := ⟨witness⟩
    rw [← hx]
    exact Finite.card_pos
  have hnr : n ≤ r := by
    obtain ⟨x, hx⟩ := hnAttained
    rw [← hx]
    exact hr x
  have hsource :
      (Nat.card (commutator G) : ℝ) ≤
        (n : ℝ) ^ ((3 + 5 * Real.logb 2 n) / 2) :=
    hprimary n hnPos ⟨hnBound, hnAttained⟩
  apply hsource.trans
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnPos
  have hnrReal : (n : ℝ) ≤ (r : ℝ) := by exact_mod_cast hnr
  have hnLog :
      Real.logb 2 (n : ℝ) ≤ Real.logb 2 (r : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hnrReal
  have hnExponentNonneg :
      0 ≤ (3 + 5 * Real.logb 2 (n : ℝ)) / 2 := by
    have : 0 ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_nonneg (by norm_num) hnReal
    positivity
  have hExponent :
      (3 + 5 * Real.logb 2 (n : ℝ)) / 2 ≤
        (3 + 5 * Real.logb 2 (r : ℝ)) / 2 := by
    linarith
  calc
    (n : ℝ) ^ ((3 + 5 * Real.logb 2 n) / 2) ≤
        (n : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2) :=
      Real.monotone_rpow_of_base_ge_one hnReal hExponent
    _ ≤ (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2) :=
      Real.rpow_le_rpow (by positivity) hnrReal
        (hnExponentNonneg.trans hExponent)

end Submissions.Erdos117BFCExactMaximumToBound.Kernel
