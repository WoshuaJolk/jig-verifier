import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Order.LiminfLimsup

namespace Statements.Erdos329SidonUpperDensityOne

open Filter Set

def IsSidon (A : Set ℕ) : Prop :=
  ∀ I J : Multiset ℕ,
    I.card = 2 → J.card = 2 →
    (∀ a ∈ I, a ∈ A) → (∀ a ∈ J, a ∈ A) →
    I.sum = J.sum → I = J

noncomputable def normalizedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 N).ncard / Real.sqrt N

/-- Erdős Problem 329 (Erdős–Krückeberg conjecture): there is a
Sidon set whose square-root-normalized counting function has limsup one. -/
abbrev statement : Prop :=
  ∃ A : Set ℕ, IsSidon A ∧
    Filter.limsup (normalizedCount A) Filter.atTop = 1

theorem target : statement := sorry

end Statements.Erdos329SidonUpperDensityOne
