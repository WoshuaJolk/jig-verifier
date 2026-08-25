import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Count
import Mathlib.Data.Set.Finite.Basic

open Nat Filter
open scoped Asymptotics Classical

namespace Statements.Erdos331BinaryDifferenceRefutation

abbrev statement : Prop :=
  ¬(∀ A B : Set ℕ,
    (fun (n : ℕ) ↦ (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop]
      (fun (n : ℕ) ↦
        (@Nat.count (fun x => x ∈ A) (Classical.decPred _) n : ℝ)) →
    (fun (n : ℕ) ↦ (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop]
      (fun (n : ℕ) ↦
        (@Nat.count (fun x => x ∈ B) (Classical.decPred _) n : ℝ)) →
    { s : ℕ × ℕ × ℕ × ℕ | let ⟨a₁, a₂, b₁, b₂⟩ := s
      a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
      a₁ ≠ a₂ ∧ a₁ + b₂ = a₂ + b₁ }.Infinite)

theorem target : statement := sorry

end Statements.Erdos331BinaryDifferenceRefutation
