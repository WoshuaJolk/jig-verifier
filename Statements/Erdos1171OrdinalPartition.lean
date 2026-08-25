import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open scoped Ordinal

namespace Statements.Erdos1171OrdinalPartition

noncomputable def omegaOne : Ordinal.{0} := Ordinal.omega 1

noncomputable def domain : Ordinal.{0} := omegaOne ^ (2 : ℕ)

noncomputable def largeTarget : Ordinal.{0} :=
  omegaOne * Ordinal.omega0

def Symmetric {α : Ordinal} {μ : ℕ}
    (color : α.ToType → α.ToType → Fin μ) : Prop :=
  ∀ x y, color x y = color y x

def Homogeneous {α : Ordinal} {μ : ℕ}
    (color : α.ToType → α.ToType → Fin μ)
    (i : Fin μ) (H : Set α.ToType) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → color x y = i

/-- Erdős Problem 1171. A symmetric binary coloring represents a
coloring of unordered pairs; diagonal values are ignored. Color zero
has target order type `ω₁·ω`, and each of the remaining `k` colors has
target order type three. -/
abbrev statement : Prop :=
  ∀ k : ℕ,
    ∀ color :
      domain.ToType → domain.ToType → Fin (k + 1),
      Symmetric color →
        (∃ H : Set domain.ToType,
          typeLT H = largeTarget ∧
            Homogeneous color 0 H) ∨
        (∃ i : Fin k, ∃ H : Set domain.ToType,
          typeLT H = 3 ∧ Homogeneous color i.succ H)

theorem target : statement := sorry

end Statements.Erdos1171OrdinalPartition
