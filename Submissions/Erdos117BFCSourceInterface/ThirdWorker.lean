import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Index

namespace Submissions.Erdos117BFCSourceInterface.ThirdWorker

open Subgroup

universe u

private theorem class_card_eq_centralizer_index
    (G : Type u) [Group G] (x : G) :
    Nat.card {y : G // IsConj x y} = (centralizer {x}).index := by
  calc
    Nat.card {y : G // IsConj x y} =
        (MulAction.orbit (ConjAct G) x).ncard := by
      rw [← Nat.card_coe_set_eq]
      apply congrArg Set.ncard
      ext y
      rw [ConjAct.mem_orbit_conjAct]
      exact isConj_comm
    _ = (MulAction.stabilizer (ConjAct G) x).index :=
      (MulAction.index_stabilizer (ConjAct G) x).symm
    _ = (Subgroup.comap ConjAct.toConjAct.toMonoidHom
          (MulAction.stabilizer (ConjAct G) x)).index :=
      (Subgroup.index_comap_of_surjective _
        ConjAct.toConjAct.surjective).symm
    _ = (centralizer {x}).index := by
      rw [centralizer_eq_comap_stabilizer]
      rfl

private theorem trivial_breadth
    (G : Type u) [Group G] [Finite G]
    (h : ∀ x : G, Nat.card {y : G // IsConj x y} ≤ 1) :
    IsMulCommutative G ∧ Nat.card (commutator G) = 1 := by
  have hsub : ∀ x : G, Subsingleton {y : G // IsConj x y} :=
    fun x => Finite.card_le_one_iff_subsingleton.mp (h x)
  have hcomm : ∀ x y : G, x * y = y * x := by
    intro x y
    have hc : IsConj x (y * x * y⁻¹) := isConj_iff.mpr ⟨y, rfl⟩
    have heq : (⟨y * x * y⁻¹, hc⟩ : {z : G // IsConj x z}) =
        ⟨x, IsConj.refl x⟩ :=
      @Subsingleton.elim _ (hsub x) _ _
    have hval : y * x * y⁻¹ = x := congr_arg Subtype.val heq
    exact (mul_inv_eq_iff_eq_mul.mp hval).symm
  letI : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  refine ⟨inferInstance, ?_⟩
  rw [commutator_eq_bot]
  exact Nat.card_unique

private theorem abelian_bound
    (G : Type u) [Group G] [Finite G] (r : ℕ) (hr : 1 ≤ r)
    (hcomm : IsMulCommutative G) :
    (Nat.card (commutator G) : ℝ) ≤
      (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2) := by
  letI : IsMulCommutative G := hcomm
  have hcard : Nat.card (commutator G) = 1 := by
    rw [commutator_eq_bot]
    exact Nat.card_unique
  rw [hcard]
  norm_num
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.logb 2 (r : ℝ) := by
    calc
      0 = Real.logb 2 1 := by simp [Real.logb]
      _ ≤ Real.logb 2 (r : ℝ) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        exact_mod_cast hr
  exact Real.one_le_rpow hr1 (by positivity)

theorem proof :
    ∀ (G : Type u) (_ : Group G) (_ : Finite G),
      (∀ x : G,
        Nat.card {y : G // IsConj x y} = (centralizer {x}).index) ∧
      (∀ r : ℕ,
        (∀ x : G, Nat.card {y : G // IsConj x y} ≤ r) ↔
        (∀ x : G, (centralizer {x}).index ≤ r)) ∧
      ((∀ x : G, Nat.card {y : G // IsConj x y} ≤ 1) →
        IsMulCommutative G ∧ Nat.card (commutator G) = 1) ∧
      (∀ r : ℕ, 1 ≤ r → IsMulCommutative G →
        (Nat.card (commutator G) : ℝ) ≤
          (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2)) := by
  intro G _ _
  refine ⟨class_card_eq_centralizer_index G, ?_, trivial_breadth G,
    abelian_bound G⟩
  intro r
  constructor <;> intro h x
  · calc
      (centralizer {x}).index =
          Nat.card {y : G // IsConj x y} :=
        (class_card_eq_centralizer_index G x).symm
      _ ≤ r := h x
  · calc
      Nat.card {y : G // IsConj x y} =
          (centralizer {x}).index :=
        class_card_eq_centralizer_index G x
      _ ≤ r := h x

end Submissions.Erdos117BFCSourceInterface.ThirdWorker
