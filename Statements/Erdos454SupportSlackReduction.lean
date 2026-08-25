import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Instances.ENat

open Filter

namespace Statements.Erdos454SupportSlackReduction

noncomputable local instance : ConditionallyCompleteLattice ℕ∞ :=
  WithTop.conditionallyCompleteLattice

noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    ⨅ i : {i : Fin n // 0 < (i : ℕ)},
      (n + i).nth Nat.Prime + (n - i).nth Nat.Prime

/-- It suffices to find arbitrarily late prime-graph vertices with arbitrarily large support-line slack simultaneously at every symmetric offset. -/
abbrev statement : Prop :=
  (∀ B : ℕ, ∃ᶠ n in atTop,
    1 < n ∧
      ∀ i : {i : Fin n // 0 < (i : ℕ)},
        2 * n.nth Nat.Prime + B ≤
          (n + i).nth Nat.Prime + (n - i).nth Nat.Prime) →
  limsup
    (fun n ↦ (f n - 2 * n.nth Nat.Prime : ℕ∞))
    atTop = ⊤

theorem target : statement := sorry

end Statements.Erdos454SupportSlackReduction
