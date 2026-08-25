import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Sequences

namespace Submissions.Erdos5LimitPointsNonnegative.Control

open Filter Real Set
open scoped Topology

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

noncomputable def normalizedGap (n : ℕ) : ℝ :=
  primeGap n / Real.log n

def limitPointSet : Set ℝ :=
  {x : ℝ | MapClusterPt x atTop normalizedGap}

abbrev claimedStatement : Prop := limitPointSet ⊆ Set.Ici 0

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos5LimitPointsNonnegative.Control
