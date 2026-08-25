import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic

open Cardinal Ordinal

namespace Statements.Erdos1167OneColorBoundary

universe u

def CardinalPartitionRel (μ : Cardinal.{u}) (r : ℕ) (γ : Ordinal.{u})
    (ν : γ.ToType → Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = μ →
    ∀ col : {s : Finset A // s.card = r} → γ.ToType,
      ∃ (i : γ.ToType) (H : Set A), #H = ν i ∧
        ∀ (s : Finset A) (hs : s.card = r),
          (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = i

noncomputable def i0 : (1 : Ordinal.{u}).ToType := default

/-- The one-color boundary of the inlined partition relation is
exactly cardinal comparison. -/
abbrev statement : Prop :=
  ∀ (μ : Cardinal.{u}) (r : ℕ)
      (ν : (1 : Ordinal.{u}).ToType → Cardinal.{u}),
    CardinalPartitionRel μ r 1 ν ↔ μ ≥ ν i0

theorem target : statement := sorry

end Statements.Erdos1167OneColorBoundary
