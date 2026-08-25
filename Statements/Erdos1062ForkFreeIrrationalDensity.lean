import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Irrational

namespace Statements.Erdos1062ForkFreeIrrationalDensity

open Filter
open scoped Topology

def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

noncomputable def extremal (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest
    (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

/-- Erdős problem 1062: the limiting density of the largest fork-free
subset exists and is irrational. -/
abbrev statement : Prop :=
  ∃ l : ℝ,
    Tendsto (fun n : ℕ => (extremal n : ℝ) / n) atTop (𝓝 l) ∧
      Irrational l

theorem target : statement := sorry

end Statements.Erdos1062ForkFreeIrrationalDensity
