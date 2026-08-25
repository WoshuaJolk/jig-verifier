import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős problem 552

For every fixed positive `c`, are there infinitely many `n` for which
`R(C₄, K₁,ₙ) ≤ n + √n - c`?
-/

namespace Statements.Erdos552C4StarRamsey

noncomputable section

def HasFourCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

def HasBlueStar (n : ℕ) {m : ℕ} (G : SimpleGraph (Fin m)) : Prop :=
  ∃ v : Fin m,
    n ≤ Set.ncard {w : Fin m | w ≠ v ∧ ¬ G.Adj v w}

def RamseyAtMost (n m : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin m), HasFourCycle G ∨ HasBlueStar n G

noncomputable def cutoff (c : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) + Real.sqrt n - c⌋₊

abbrev statement : Prop :=
  ∀ c : ℝ, 0 < c →
    Set.Infinite {n : ℕ | RamseyAtMost n (cutoff c n)}

theorem target : statement := sorry

end

end Statements.Erdos552C4StarRamsey
