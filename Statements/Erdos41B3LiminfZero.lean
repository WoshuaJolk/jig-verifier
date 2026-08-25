import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Order.LiminfLimsup

namespace Statements.Erdos41B3LiminfZero

open Filter Set

def IsB3Sequence (A : Set ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = 3 → J.card = 3 →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

/-- Erdős Problem 41: every infinite B₃ sequence has lower normalized
counting density zero. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, IsB3Sequence A → A.Infinite →
    Filter.liminf
      (fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ))
      Filter.atTop = 0

theorem target : statement := sorry

end Statements.Erdos41B3LiminfZero
