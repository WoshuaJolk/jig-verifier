import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter

/-!
# Erdős problem 864

Is the maximal size of a subset of `[1,N]` whose unordered two-term sums are
unique except at possibly one sum asymptotically at most `(2/√3)√N`?
-/

namespace Statements.Erdos864NearSidonBound

def representationCount (A : Finset ℕ) (s : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = s).card

def AlmostSidon (A : Finset ℕ) : Prop :=
  Set.ncard {s : ℕ | 1 < representationCount A s} ≤ 1

noncomputable def nearSidonMax (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ AlmostSidon A ∧ m = A.card}

abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      (nearSidonMax N : ℝ) ≤
        (2 / Real.sqrt 3 + ε) * Real.sqrt N

theorem target : statement := sorry

end Statements.Erdos864NearSidonBound
