import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

namespace Statements.Erdos44AggregateCarryArcs

open Set Finset
open scoped symmDiff

def rot (n c x : ℕ) : ℕ := (x + n - c) % n

abbrev Quad := (((ℕ × ℕ) × ℕ) × ℕ)

abbrev PairCarry (n c x y : ℕ) : Prop :=
  rot n c x + rot n c y < n

abbrev SameCarry (n c : ℕ) (p : Quad) : Prop :=
  PairCarry n c p.1.1.1 p.1.1.2 ↔ PairCarry n c p.2 p.1.2

def CarryCuts (n x y : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun c => PairCarry n c x y

def DisagreementCuts (n : ℕ) (p : Quad) : Finset ℕ :=
  CarryCuts n p.1.1.1 p.1.1.2 ∆ CarryCuts n p.2 p.1.2

def SurvivalCuts (n : ℕ) (p : Quad) : Finset ℕ :=
  (Finset.range n).filter fun c => SameCarry n c p

def CutSurvivors (n c : ℕ) (E : Finset Quad) : Finset Quad :=
  E.filter (SameCarry n c)

/-- Each witness survives on the complement of the symmetric difference of
its two carry arcs; aggregate survivor and disagreement mass is exactly `n|E|`. -/
abbrev statement : Prop :=
  (∀ (n : ℕ) (p : Quad),
    SurvivalCuts n p = Finset.range n \ DisagreementCuts n p) ∧
  (∀ (n : ℕ) (E : Finset Quad),
    (∑ c ∈ Finset.range n, (CutSurvivors n c E).card) +
      (∑ p ∈ E, (DisagreementCuts n p).card) =
        n * E.card)

theorem target : statement := by
  sorry

end Statements.Erdos44AggregateCarryArcs
