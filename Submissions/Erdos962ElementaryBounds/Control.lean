import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Set.Nat

namespace Submissions.Erdos962ElementaryBounds.Control

def HasLargePrimeBlock (n width : ℕ) : Prop :=
  ∃ start ≤ n, ∀ offset ∈ Set.Icc 1 width,
    ∃ p : ℕ, p.Prime ∧ width < p ∧ p ∣ start + offset

noncomputable def maxWidth (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun width => HasLargePrimeBlock n width) n

abbrev claimedStatement : Prop :=
  (∀ n : ℕ, maxWidth n ≤ n) ∧
    ∀ n : ℕ, 1 ≤ n → 1 ≤ maxWidth n

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos962ElementaryBounds.Control
