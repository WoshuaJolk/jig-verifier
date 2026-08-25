import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos385CompositeWitnessLowerBound

open scoped Classical

def IsComposite (m : ℕ) : Prop :=
  1 < m ∧ ¬m.Prime

noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.range n).filter IsComposite).sup (fun m ↦ m + m.minFac)

/-- Any individual admissible composite gives a lower bound for `F`; in
particular, a composite sufficiently close to `n` proves overshoot. -/
abbrev statement : Prop :=
  ∀ n m : ℕ, m < n → IsComposite m →
    m + m.minFac ≤ F n ∧ (n < m + m.minFac → n < F n)

theorem target : statement := sorry

end Statements.Erdos385CompositeWitnessLowerBound
