import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace Submissions.Erdos117RestrictedFormRankLoss.Kernel

open Module Submodule

noncomputable def linearRank
    {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V']
    (f : V →ₗ[K] V') : ℕ :=
  finrank K (LinearMap.range f)

noncomputable def formRank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : ℕ :=
  linearRank B

private theorem map_ker_domRestrict
    {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V']
    (f : V →ₗ[K] V') (S : Submodule K V) :
    (LinearMap.ker (f.domRestrict S)).map S.subtype =
      S ⊓ LinearMap.ker f := by
  rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]

private theorem linearRank_domRestrict_add_codim
    {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V']
    (f : V →ₗ[K] V') (S : Submodule K V) :
    linearRank f ≤
      linearRank (f.domRestrict S) + (finrank K V - finrank K S) := by
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hfr := LinearMap.finrank_range_add_finrank_ker (f.domRestrict S)
  have hker :
      finrank K (LinearMap.ker (f.domRestrict S)) =
        finrank K ↥(S ⊓ LinearMap.ker f) := by
    rw [← Submodule.finrank_map_subtype_eq S
      (LinearMap.ker (f.domRestrict S)), map_ker_domRestrict]
  have hlattice :=
    Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker f)
  have hsup : finrank K ↥(S ⊔ LinearMap.ker f) ≤ finrank K V :=
    (S ⊔ LinearMap.ker f).finrank_le
  have hSsup : finrank K S ≤ finrank K ↥(S ⊔ LinearMap.ker f) :=
    Submodule.finrank_mono le_sup_left
  have hS : finrank K S ≤ finrank K V := S.finrank_le
  unfold linearRank
  omega

private theorem linearRank_comp_add_ker
    {K V V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup W'] [Module K W']
    (f : V →ₗ[K] V') (r : V' →ₗ[K] W')
    [FiniteDimensional K (LinearMap.range f)] :
    linearRank f ≤
      linearRank (r.comp f) + finrank K (LinearMap.ker r) := by
  let rr := r.domRestrict (LinearMap.range f)
  have hrr := LinearMap.finrank_range_add_finrank_ker rr
  have hrange :
      LinearMap.range rr = LinearMap.range (r.comp f) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  have hkerMap :
      (LinearMap.ker rr).map (LinearMap.range f).subtype =
        LinearMap.range f ⊓ LinearMap.ker r := by
    exact map_ker_domRestrict r (LinearMap.range f)
  have hker :
      finrank K (LinearMap.ker rr) ≤ finrank K (LinearMap.ker r) := by
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.range f)
      (LinearMap.ker rr), hkerMap]
    exact Submodule.finrank_mono inf_le_right
  unfold linearRank
  rw [← hrange]
  omega

private theorem linearRank_two_sided_restriction
    {K V V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup W'] [Module K W']
    (f : V →ₗ[K] V') (S : Submodule K V) (r : V' →ₗ[K] W') (q : ℕ)
    [FiniteDimensional K (LinearMap.range (f.domRestrict S))]
    (hcodim : finrank K V - finrank K S ≤ q)
    (hker : finrank K (LinearMap.ker r) ≤ q) :
    linearRank f ≤
      linearRank (r.comp (f.domRestrict S)) + 2 * q := by
  have h₁ := linearRank_domRestrict_add_codim f S
  have h₂ := linearRank_comp_add_ker (f.domRestrict S) r
  omega

theorem proof :
    ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
      (S : Submodule K V),
        formRank B ≤
          formRank (B.restrict S) + 2 * (finrank K V - finrank K S) := by
  intro K V _ _ _ _ B S
  let r : Module.Dual K V →ₗ[K] Module.Dual K S :=
    LinearMap.dualMap S.subtype
  have hre :
      r.comp (B.domRestrict S) = B.restrict S := by
    ext x y
    rfl
  have hrange : LinearMap.range S.subtype = S :=
    Submodule.range_subtype S
  have hker :
      finrank K (LinearMap.ker r) = finrank K V - finrank K S := by
    change finrank K (LinearMap.ker (LinearMap.dualMap S.subtype)) =
      finrank K V - finrank K S
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, hrange]
    have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq S
    omega
  have h := linearRank_two_sided_restriction B S r
    (finrank K V - finrank K S) le_rfl hker.le
  simpa only [formRank, hre] using h

end Submissions.Erdos117RestrictedFormRankLoss.Kernel
