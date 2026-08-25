import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace Submissions.Erdos117TransversalCliqueCore.ThirdWorker

open scoped BigOperators

universe u v

noncomputable def lowerSum {V : Type v} [AddCommMonoid V]
    {d : ℕ} (y : Fin d → V) (i : Fin d) : V :=
  ∑ h ∈ Finset.univ.filter (fun h => h < i), y h

noncomputable def point {V : Type v} [AddCommMonoid V]
    {d : ℕ} (x y : Fin d → V) : Option (Fin d) → V
  | none => ∑ h, y h
  | some i => x i + lowerSum y i

theorem y_pair_x {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V]
    {d : ℕ} (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    (x y : Fin d → V)
    (hxy : ∀ i h, B (x i) (y h) = if i = h then 1 else 0)
    (h i : Fin d) :
    B (y h) (x i) = if i = h then -1 else 0 := by
  rw [← hAlt.neg_eq (x i) (y h), hxy]
  split_ifs <;> simp_all

theorem pair_none_some {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V]
    {d : ℕ} (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    (U : Submodule K V) (hU : ∀ u ∈ U, ∀ v ∈ U, B u v = 0)
    (x y : Fin d → V) (hyU : ∀ i, y i ∈ U)
    (hxy : ∀ i h, B (x i) (y h) = if i = h then 1 else 0)
    (i : Fin d) :
    B (point x y none) (point x y (some i)) = -1 := by
  simp only [point, map_add, map_sum, lowerSum]
  have hyx := y_pair_x B hAlt x y hxy
  simp [hyx, hU, hyU]

theorem pair_some_some_of_lt {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V]
    {d : ℕ} (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    (U : Submodule K V) (hU : ∀ u ∈ U, ∀ v ∈ U, B u v = 0)
    (x y : Fin d → V) (hyU : ∀ i, y i ∈ U)
    (hxx : ∀ i r, B (x i) (x r) = 0)
    (hxy : ∀ i h, B (x i) (y h) = if i = h then 1 else 0)
    {i r : Fin d} (hir : i < r) :
    B (point x y (some i)) (point x y (some r)) = 1 := by
  simp only [point, map_add, map_sum, lowerSum]
  have hyx := y_pair_x B hAlt x y hxy
  simp [hxx, hxy, hyx, hU, hyU, hir, hir.le]

theorem pairwise_nonorthogonal {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V]
    {d : ℕ} (B : LinearMap.BilinForm K V) (hAlt : B.IsAlt)
    (U : Submodule K V) (hU : ∀ u ∈ U, ∀ v ∈ U, B u v = 0)
    (x y : Fin d → V) (hyU : ∀ i, y i ∈ U)
    (hxx : ∀ i r, B (x i) (x r) = 0)
    (hxy : ∀ i h, B (x i) (y h) = if i = h then 1 else 0) :
    ∀ q r, q ≠ r → B (point x y q) (point x y r) ≠ 0 := by
  intro q r hqr
  cases q with
  | none =>
      cases r with
      | none => exact (hqr rfl).elim
      | some i =>
          rw [pair_none_some B hAlt U hU x y hyU hxy i]
          exact neg_ne_zero.mpr one_ne_zero
  | some i =>
      cases r with
      | none =>
          have hp : B (point x y (some i)) (point x y none) = (1 : K) := by
            rw [← hAlt.neg_eq,
              pair_none_some B hAlt U hU x y hyU hxy i]
            simp
          rw [hp]
          exact one_ne_zero
      | some r =>
          have hir : i ≠ r := by
            intro e
            exact hqr (congrArg some e)
          rcases lt_or_gt_of_ne hir with hir | hri
          · rw [pair_some_some_of_lt B hAlt U hU x y hyU hxx hxy hir]
            exact one_ne_zero
          · rw [← hAlt.neg_eq,
              pair_some_some_of_lt B hAlt U hU x y hyU hxx hxy hri]
            exact neg_ne_zero.mpr one_ne_zero

theorem distinct_mod_isotropic {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V]
    {d : ℕ} (B : LinearMap.BilinForm K V)
    (U : Submodule K V) (hU : ∀ u ∈ U, ∀ v ∈ U, B u v = 0)
    (x y : Fin d → V) (hyU : ∀ i, y i ∈ U)
    (hxy : ∀ i h, B (x i) (y h) = if i = h then 1 else 0) :
    ∀ q r, q ≠ r → point x y q - point x y r ∉ U := by
  intro q r hqr hmem
  cases q with
  | none =>
      cases r with
      | none => exact hqr rfl
      | some i =>
          have hz := hU _ hmem (y i) (hyU i)
          simp only [point, map_sub, map_sum, lowerSum] at hz
          simp [hU, hyU, hxy] at hz
  | some i =>
      cases r with
      | none =>
          have hz := hU _ hmem (y i) (hyU i)
          simp only [point, map_sub, map_add, map_sum, lowerSum] at hz
          simp [hU, hyU, hxy] at hz
      | some r =>
          have hir : i ≠ r := by
            intro e
            exact hqr (congrArg some e)
          have hz := hU _ hmem (y i) (hyU i)
          simp only [point, map_sub, map_add, map_sum, lowerSum] at hz
          simp [hU, hyU, hxy, hir.symm] at hz

theorem proof :
    ∀ (K : Type u) (V : Type v) (_ : Field K) (_ : AddCommGroup V)
        (_ : Module K V) (d : ℕ) (B : LinearMap.BilinForm K V)
        (U : Submodule K V) (x y : Fin d → V),
      B.IsAlt →
      (∀ u ∈ U, ∀ v ∈ U, B u v = 0) →
      (∀ i, y i ∈ U) →
      (∀ i r, B (x i) (x r) = 0) →
      (∀ i h, B (x i) (y h) = if i = h then 1 else 0) →
      ∃ a : Option (Fin d) → V,
        a none = ∑ h, y h ∧
        (∀ i, a (some i) =
          x i + ∑ h ∈ Finset.univ.filter (fun h => h < i), y h) ∧
        (∀ q r, q ≠ r → B (a q) (a r) ≠ 0) ∧
        (∀ q r, q ≠ r → a q - a r ∉ U) := by
  intro K V _ _ _ d B U x y hAlt hU hyU hxx hxy
  refine ⟨point x y, rfl, fun _ => rfl, ?_, ?_⟩
  · exact pairwise_nonorthogonal B hAlt U hU x y hyU hxx hxy
  · exact distinct_mod_isotropic B U hU x y hyU hxy

end Submissions.Erdos117TransversalCliqueCore.ThirdWorker
