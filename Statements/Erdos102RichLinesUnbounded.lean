import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos102RichLinesUnbounded

open Filter

abbrev Point := ℝ × ℝ

def Collinear (a b x : Point) : Prop :=
  (b.1 - a.1) * (x.2 - a.2) =
    (b.2 - a.2) * (x.1 - a.1)

def lineThrough (a b : Point) : Set Point :=
  {x | Collinear a b x}

noncomputable def occupancy (P : Finset Point) (L : Set Point) : ℕ := by
  classical
  exact (P.filter fun x => x ∈ L).card

noncomputable def richLines (P : Finset Point) : Set (Set Point) :=
  {L | ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧
    L = lineThrough a b ∧
    3 < occupancy P L}

/-- Erdős problem 102, unboundedness question: a positive quadratic density
of lines containing at least four selected points forces arbitrarily rich
lines as the number of points tends to infinity. -/
abbrev statement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ K : ℕ,
    ∀ᶠ n : ℕ in atTop,
      ∀ P : Finset Point, P.card = n →
        c * (n : ℝ) ^ 2 ≤ (richLines P).ncard →
        ∃ L ∈ richLines P, K < occupancy P L

theorem target : statement := sorry

end Statements.Erdos102RichLinesUnbounded
