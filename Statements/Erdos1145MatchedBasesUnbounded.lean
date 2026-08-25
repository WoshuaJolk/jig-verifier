import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Statements.Erdos1145MatchedBasesUnbounded

/-- Number of ordered representations `n = a + b` with `a ∈ A`, `b ∈ B`. -/
noncomputable def repCount (A B : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ B).card

/-- Erdős–Sárközy: asymptotically matched additive complements have unbounded
representation function. -/
abbrev statement : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → 0 ∉ A → 0 ∉ B →
    Filter.Tendsto
      (fun n => (Nat.nth (· ∈ A) n : ℝ) / (Nat.nth (· ∈ B) n : ℝ))
      Filter.atTop (nhds 1) →
    (∀ᶠ n : ℕ in Filter.atTop,
      ∃ a ∈ A, ∃ b ∈ B, a + b = n) →
    ∀ K : ℕ, ∃ n : ℕ, K < repCount A B n

theorem target : statement := sorry

end Statements.Erdos1145MatchedBasesUnbounded
