import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic

open Cardinal Ordinal

namespace Submissions.Erdos1167OneColorBoundary.Worker03CardinalComparison

universe u

def CardinalPartitionRel (μ : Cardinal.{u}) (r : ℕ) (γ : Ordinal.{u})
    (ν : γ.ToType → Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = μ →
    ∀ col : {s : Finset A // s.card = r} → γ.ToType,
      ∃ (i : γ.ToType) (H : Set A), #H = ν i ∧
        ∀ (s : Finset A) (hs : s.card = r),
          (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = i

noncomputable def i0 : (1 : Ordinal.{u}).ToType := default

theorem proof :
    ∀ (μ : Cardinal.{u}) (r : ℕ)
        (ν : (1 : Ordinal.{u}).ToType → Cardinal.{u}),
      CardinalPartitionRel μ r 1 ν ↔ μ ≥ ν i0 := by
  intro μ r ν
  dsimp [CardinalPartitionRel]
  constructor
  · intro h
    have hA : #(μ.out) = μ := Cardinal.mk_out μ
    rcases h μ.out hA (fun _ => i0) with ⟨i, H, hH, _⟩
    have hi : i = i0 := Subsingleton.elim i i0
    subst hi
    have hle : #H ≤ #(μ.out) := Cardinal.mk_set_le H
    rwa [hH, hA] at hle
  · intro h A hA col
    have hle : ν i0 ≤ #A := by rwa [hA]
    rcases Cardinal.le_mk_iff_exists_set.mp hle with ⟨H, hH⟩
    refine ⟨i0, H, hH, ?_⟩
    intro s hs hsH
    exact Subsingleton.elim _ _

end Submissions.Erdos1167OneColorBoundary.Worker03CardinalComparison
