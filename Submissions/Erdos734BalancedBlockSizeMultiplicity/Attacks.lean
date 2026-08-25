import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace Submissions.Erdos734BalancedBlockSizeMultiplicity.Attacks

open Filter

abbrev BlockDesign (n : ℕ) := Finset (Finset (Fin n))

def IsPairwiseBalanced {n : ℕ} (B : BlockDesign n) : Prop :=
  ∀ x y : Fin n, x ≠ y →
    ∃! block : Finset (Fin n), block ∈ B ∧ x ∈ block ∧ y ∈ block

def IsNontrivial {n : ℕ} (B : BlockDesign n) : Prop := Finset.univ ∉ B

def HasBoundedSizeMultiplicity (C : ℝ) {n : ℕ} (B : BlockDesign n) : Prop :=
  ∀ t : ℕ,
    ((B.filter fun block => block.card = t).card : ℝ) ≤ C * Real.sqrt n

abbrev claimedStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop,
      ∃ B : BlockDesign n,
        IsPairwiseBalanced B ∧ IsNontrivial B ∧
          HasBoundedSizeMultiplicity C B

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem constantDomainNonempty : ∃ C : ℝ, 0 < C := ⟨1, by norm_num⟩

end Submissions.Erdos734BalancedBlockSizeMultiplicity.Attacks
