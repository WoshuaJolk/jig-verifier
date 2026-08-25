import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Commutator.Basic

namespace Submissions.Erdos117BFCCompressionTransfer.ThirdWorker

open Subgroup

universe u v

theorem exact_bound
    (G : Type u) (H : Type v) [Group G] [Group H] [Finite G] (N : ℕ)
    (hPyber : ∀ x : G,
      Nat.card {y : G // IsConj x y} ≤ (2 * N + 1) ^ 2)
    (hNVL : ∀ r : ℕ, 1 ≤ r →
      (∀ x : G, Nat.card {y : G // IsConj x y} ≤ r) →
      (Nat.card (commutator G) : ℝ) ≤
        (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2))
    (e : commutator G ≃* commutator H) :
    Real.logb 2 (Nat.card (commutator H)) ≤
      (3 + 10 * Real.logb 2 ((2 * N + 1 : ℕ) : ℝ)) *
        Real.logb 2 ((2 * N + 1 : ℕ) : ℝ) := by
  let r : ℕ := (2 * N + 1) ^ 2
  have hr : 1 ≤ r := by
    dsimp [r]
    exact one_le_pow₀ (by omega)
  have hsource :
      (Nat.card (commutator G) : ℝ) ≤
        (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2) :=
    hNVL r hr hPyber
  letI : Finite (commutator H) :=
    Finite.of_equiv (commutator G) e.toEquiv
  have hcard :
      Nat.card (commutator G) = Nat.card (commutator H) :=
    Nat.card_congr e.toEquiv
  have hGpos : 0 < (Nat.card (commutator G) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := commutator G))
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  calc
    Real.logb 2 (Nat.card (commutator H)) =
        Real.logb 2 (Nat.card (commutator G)) := by rw [hcard]
    _ ≤ Real.logb 2
          ((r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2)) := by
      exact (Real.logb_le_logb (b := 2) (by norm_num) hGpos
        (Real.rpow_pos_of_pos hrpos _)).2 hsource
    _ = ((3 + 5 * Real.logb 2 r) / 2) *
          Real.logb 2 r := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hrpos]
    _ = (3 + 10 * Real.logb 2 ((2 * N + 1 : ℕ) : ℝ)) *
          Real.logb 2 ((2 * N + 1 : ℕ) : ℝ) := by
      have hr_cast :
          (r : ℝ) = ((2 * N + 1 : ℕ) : ℝ) ^ 2 := by
        norm_num [r]
      rw [hr_cast, Real.logb_pow]
      ring

theorem proof :
    ∀ (G : Type u) (H : Type v) (_ : Group G) (_ : Group H)
        (_ : Finite G) (N : ℕ),
      (∀ x : G, Nat.card {y : G // IsConj x y} ≤ (2 * N + 1) ^ 2) →
      (∀ r : ℕ, 1 ≤ r →
        (∀ x : G, Nat.card {y : G // IsConj x y} ≤ r) →
        (Nat.card (commutator G) : ℝ) ≤
          (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2)) →
      (commutator G ≃* commutator H) →
      (Real.logb 2 (Nat.card (commutator H)) ≤
          (3 + 10 * Real.logb 2 ((2 * N + 1 : ℕ) : ℝ)) *
            Real.logb 2 ((2 * N + 1 : ℕ) : ℝ)) ∧
        (Real.logb 2 (Nat.card (commutator H)) ≤
          46 * (Real.logb 2 ((N + 2 : ℕ) : ℝ)) ^ 2) := by
  intro G H _ _ _ N hPyber hNVL e
  have hexact := exact_bound G H N hPyber hNVL e
  let L := Real.logb 2 ((2 * N + 1 : ℕ) : ℝ)
  let M := Real.logb 2 ((N + 2 : ℕ) : ℝ)
  have hApos : 0 < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hAsq :
      ((2 * N + 1 : ℕ) : ℝ) ≤ ((N + 2 : ℕ) : ℝ) ^ 2 := by
    norm_num
    nlinarith [sq_nonneg (N : ℝ)]
  have hLM : L ≤ 2 * M := by
    dsimp [L, M]
    calc
      Real.logb 2 ((2 * N + 1 : ℕ) : ℝ) ≤
          Real.logb 2 (((N + 2 : ℕ) : ℝ) ^ 2) :=
        Real.logb_le_logb_of_le (by norm_num) hApos hAsq
      _ = 2 * Real.logb 2 ((N + 2 : ℕ) : ℝ) := by
        rw [Real.logb_pow]
        norm_num
  have hM : 1 ≤ M := by
    dsimp [M]
    calc
      1 = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 ((N + 2 : ℕ) : ℝ) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        norm_num
  have hL : 0 ≤ L := by
    dsimp [L]
    calc
      0 = Real.logb 2 1 := by simp [Real.logb]
      _ ≤ Real.logb 2 ((2 * N + 1 : ℕ) : ℝ) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        norm_num
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hLsq : L ^ 2 ≤ (2 * M) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLM)
      (add_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hM0) hL)]
  have hMlin : M ≤ M ^ 2 := by
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hM)]
  exact ⟨hexact, hexact.trans (by nlinarith)⟩

end Submissions.Erdos117BFCCompressionTransfer.ThirdWorker
