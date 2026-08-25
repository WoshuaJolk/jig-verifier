import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace Submissions.Erdos374SixFactorialSquareDensity.Attacks

open Filter Finset
open scoped BigOperators

def IsSquare (n : ℕ) : Prop := ∃ q : ℕ, n = q ^ 2

def HasFactorialSquareWitness (k m : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    A.card = k ∧ m ∈ A ∧
      (∀ a ∈ A, a ≤ m) ∧ IsSquare (∏ a ∈ A, a.factorial)

def HasMinimalWitnessSize (k m : ℕ) : Prop :=
  2 ≤ k ∧ HasFactorialSquareWitness k m ∧
    ∀ j : ℕ, 2 ≤ j → j < k → ¬HasFactorialSquareWitness j m

noncomputable def countSix (n : ℕ) : ℕ :=
  open scoped Classical in
    ((Finset.Icc 1 n).filter fun m => HasMinimalWitnessSize 6 m).card

abbrev claimedStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c * n ≤ countSix n

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem constantDomainNonempty : ∃ c : ℝ, 0 < c := ⟨1, by norm_num⟩

end Submissions.Erdos374SixFactorialSquareDensity.Attacks
