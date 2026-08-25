import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic

open Cardinal Ordinal

namespace Submissions.Erdos1167OneColorBoundary.Worker03VacuousControl

universe u

def CardinalPartitionRel (μ : Cardinal.{u}) (r : ℕ) (γ : Ordinal.{u})
    (ν : γ.ToType → Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = μ →
    ∀ col : {s : Finset A // s.card = r} → γ.ToType,
      ∃ (i : γ.ToType) (H : Set A), #H = ν i ∧
        ∀ (s : Finset A) (hs : s.card = r),
          (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = i

noncomputable def i0 : (1 : Ordinal.{u}).ToType := default

theorem proof (h : False) :
    ∀ (μ : Cardinal.{u}) (r : ℕ)
        (ν : (1 : Ordinal.{u}).ToType → Cardinal.{u}),
      CardinalPartitionRel μ r 1 ν ↔ μ ≥ ν i0 := h.elim

end Submissions.Erdos1167OneColorBoundary.Worker03VacuousControl
