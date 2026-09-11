import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Finset.Prod
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Ring

namespace Submissions.Erdos530IntegerFreimanModel.Main

/-- A rational linear functional separates any finite set of real numbers.
Finite avoidance of proper hyperplanes is already available in Mathlib. -/
theorem exists_rat_linear_injOn (D : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, Set.InjOn f D := by
  classical
  let X := (D ×ˢ D).filter fun p => p.1 ≠ p.2
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℚ) (fun p : ↥X => p.val.1 - p.val.2)
    (fun p => sub_ne_zero.mpr (Finset.mem_filter.mp p.property).2)
  refine ⟨f, ?_⟩
  intro a ha b hb hab
  by_contra hne
  have hpair : (a, b) ∈ X :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hne⟩
  have hnz := hf ⟨(a, b), hpair⟩
  apply hnz
  change f (a - b) = 0
  rw [map_sub, hab, sub_self]

/-- No loss of points or pair-sum relations is needed to pass from reals to rationals. -/
theorem exists_rat_freiman_model (A : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, Set.InjOn f A ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        f a + f b = f c + f d ↔ a + b = c + d := by
  classical
  let D := A ∪ (A ×ˢ A).image (fun p => p.1 + p.2)
  obtain ⟨f, hf⟩ := exists_rat_linear_injOn D
  have hsum {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A) : a + b ∈ D :=
    Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
  refine ⟨f, fun _ ha _ hb hab => hf (Finset.mem_union_left _ ha)
    (Finset.mem_union_left _ hb) hab, ?_⟩
  intro a ha b hb c hc d hd
  constructor
  · intro h
    exact hf (hsum ha hb) (hsum hc hd) (by simpa only [map_add] using h)
  · intro h
    simpa only [map_add] using congrArg f h

/-- Clear all denominators in a finite rational set with one positive integer.
The total function is only specified on B, and no nonemptiness is required. -/
theorem exists_positive_integer_scaling (B : Finset ℚ) :
    ∃ D : ℤ, 0 < D ∧ ∃ g : ℚ → ℤ, ∀ b ∈ B, (g b : ℚ) = (D : ℚ) * b := by
  classical
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples
    (S := ℚ) (Submonoid.pos ℤ) B id
  let g : ℚ → ℤ := fun b => if hb : b ∈ B then (hD b hb).choose else 0
  refine ⟨(D : ℤ), D.property, g, ?_⟩
  intro b hb
  dsimp only [g]
  rw [dif_pos hb]
  simpa only [Algebra.smul_def, eq_intCast, id_eq] using (hD b hb).choose_spec

/-- Every finite real set has an integer model with exactly the same pair-sum
relations, without deleting points and including all repeated summands. -/
theorem exists_integer_freiman_model (A : Finset ℝ) :
    ∃ f : ℝ → ℤ, Set.InjOn f A ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        f a + f b = f c + f d ↔ a + b = c + d := by
  classical
  obtain ⟨q, hqinj, hqsum⟩ := exists_rat_freiman_model A
  obtain ⟨D, hD, g, hg⟩ := exists_positive_integer_scaling (A.image q)
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hgA (a : ℝ) (ha : a ∈ A) : (g (q a) : ℚ) = (D : ℚ) * q a :=
    hg (q a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hginj {a b : ℝ} (ha : a ∈ A) (hb : b ∈ A)
      (h : g (q a) = g (q b)) : a = b := by
    apply hqinj ha hb
    apply mul_left_cancel₀ hD0
    rw [← hgA a ha, ← hgA b hb, h]
  refine ⟨fun a => g (q a), fun _ ha _ hb h => hginj ha hb h, ?_⟩
  intro a ha b hb c hc d hd
  constructor
  · intro h
    apply (hqsum a ha b hb c hc d hd).mp
    apply mul_left_cancel₀ hD0
    have hr := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hr
    rw [hgA a ha, hgA b hb, hgA c hc, hgA d hd] at hr
    simpa only [mul_add] using hr
  · intro h
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hgA a ha, hgA b hb, hgA c hc, hgA d hd,
      ← mul_add, ← mul_add, (hqsum a ha b hb c hc d hd).mpr h]

abbrev statement : Prop :=
  ∀ A : Finset ℝ, ∃ f : ℝ → ℤ, Set.InjOn f A ∧
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      f a + f b = f c + f d ↔ a + b = c + d

theorem proof : statement := exists_integer_freiman_model

end Submissions.Erdos530IntegerFreimanModel.Main
