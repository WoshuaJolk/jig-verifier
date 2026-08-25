import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Lattice.Nat

open Filter Finset
open scoped Asymptotics Topology

namespace Statements.Erdos1204AdmissibleDiameter

def IsAdmissible (s : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ a ∈ s, a % p ≠ r

noncomputable def minimumDiameter (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (s : Finset ℕ) (hs : s.Nonempty),
    s.card = k ∧ IsAdmissible s ∧ m = s.max' hs}

/-- The explicit asymptotic conjecture in Erdős Problem 1204. -/
abbrev statement : Prop :=
  (fun k : ℕ => (minimumDiameter k : ℝ)) ~[atTop]
    (fun k : ℕ => (k : ℝ) * Real.log k)

theorem target : statement := sorry

end Statements.Erdos1204AdmissibleDiameter
