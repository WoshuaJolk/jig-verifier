import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos734BalancedBlockSizeMultiplicity

open Filter

abbrev BlockDesign (n : ℕ) := Finset (Finset (Fin n))

def IsPairwiseBalanced {n : ℕ} (B : BlockDesign n) : Prop :=
  ∀ x y : Fin n, x ≠ y →
    ∃! block : Finset (Fin n), block ∈ B ∧ x ∈ block ∧ y ∈ block

def IsNontrivial {n : ℕ} (B : BlockDesign n) : Prop :=
  Finset.univ ∉ B

def HasBoundedSizeMultiplicity (C : ℝ) {n : ℕ} (B : BlockDesign n) : Prop :=
  ∀ t : ℕ,
    ((B.filter fun block => block.card = t).card : ℝ) ≤ C * Real.sqrt n

/-- Erdős Problem 734: for all sufficiently large orders there are
nontrivial pairwise balanced designs with `O(sqrt n)` blocks of each size. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop,
      ∃ B : BlockDesign n,
        IsPairwiseBalanced B ∧ IsNontrivial B ∧
          HasBoundedSizeMultiplicity C B

theorem target : statement := sorry

end Statements.Erdos734BalancedBlockSizeMultiplicity
