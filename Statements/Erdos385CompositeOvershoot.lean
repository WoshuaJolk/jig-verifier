import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos385CompositeOvershoot

open Filter

def IsComposite (m : ℕ) : Prop :=
  1 < m ∧ ¬m.Prime

noncomputable def F (n : ℕ) : ℕ :=
  open scoped Classical in
  ((Finset.range n).filter IsComposite).sup (fun m ↦ m + m.minFac)

/-- Erdős Problem 385(i): eventually a composite below `n`, augmented by
its least prime factor, overshoots `n`. -/
abbrev statement : Prop :=
  ∀ᶠ n : ℕ in atTop, n < F n

theorem target : statement := sorry

end Statements.Erdos385CompositeOvershoot
