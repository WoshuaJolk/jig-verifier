import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

namespace Statements.Erdos1062TwoThirdsLowerBound

def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

noncomputable def extremal (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest
    (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

/-- The upper two-thirds interval is fork-free. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ⌈(2 * n / 3 : ℝ)⌉₊ ≤ extremal n

theorem target : statement := sorry

end Statements.Erdos1062TwoThirdsLowerBound
