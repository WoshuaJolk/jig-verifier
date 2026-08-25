import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open scoped Ordinal

namespace Submissions.Erdos1171OneColor.Direct

noncomputable def omegaOne : Ordinal.{0} := Ordinal.omega 1

noncomputable def domain : Ordinal.{0} := omegaOne ^ (2 : ℕ)

def Symmetric {α : Ordinal} {μ : ℕ}
    (color : α.ToType → α.ToType → Fin μ) : Prop :=
  ∀ x y, color x y = color y x

def Homogeneous {α : Ordinal} {μ : ℕ}
    (color : α.ToType → α.ToType → Fin μ)
    (i : Fin μ) (H : Set α.ToType) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → color x y = i

theorem proof :
    ∀ color : domain.ToType → domain.ToType → Fin 1,
      Symmetric color →
        ∃ H : Set domain.ToType,
          typeLT H = domain ∧ Homogeneous color 0 H := by
  intro color hsymm
  refine ⟨Set.univ, ?_, ?_⟩
  · exact (OrderIso.Set.univ.ordinalType_congr).trans
      (Ordinal.type_toType domain)
  · intro x hx y hy hxy
    exact Fin.eq_zero _

end Submissions.Erdos1171OneColor.Direct
