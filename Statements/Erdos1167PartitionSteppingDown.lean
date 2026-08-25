import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic

open Cardinal Ordinal

namespace Statements.Erdos1167PartitionSteppingDown

universe u

/-- The multicolor cardinal partition relation
`μ → (νᵢ)ᵢ<γ ^ r`: every coloring of the `r`-subsets of a set of
cardinality `μ` has a color-`i` homogeneous set of cardinality `ν i`. -/
def CardinalPartitionRel (μ : Cardinal.{u}) (r : ℕ) (γ : Ordinal.{u})
    (ν : γ.ToType → Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = μ →
    ∀ col : {s : Finset A // s.card = r} → γ.ToType,
      ∃ (i : γ.ToType) (H : Set A),
        #H = ν i ∧
        ∀ (s : Finset A) (hs : s.card = r),
          (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = i

/-- Erdős–Hajnal–Rado Problem 1167, including the original
nondegeneracy conditions `γ ≥ 2` and `κᵢ > r`. -/
abbrev statement : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
  ∀ (lam : Cardinal.{u}), ℵ₀ ≤ lam →
  ∀ (γ : Ordinal.{u}), 2 ≤ γ →
  ∀ (κ : γ.ToType → Cardinal.{u}), (∀ i, (r : Cardinal.{u}) < κ i) →
    CardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun i => κ i + 1) →
    CardinalPartitionRel lam r γ κ

theorem target : statement := sorry

end Statements.Erdos1167PartitionSteppingDown
