import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat

namespace Statements.Erdos950PrimeReciprocalLiminf

open Filter

noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime,
    (1 : ℝ) / (n - p : ℝ)

/-- Erdős Problem 950(i): the lower limit of the reciprocal distance
sum from `n` to earlier primes equals one. -/
abbrev statement : Prop :=
  liminf (fun n : ℕ => (f n : EReal)) atTop = 1

theorem target : statement := sorry

end Statements.Erdos950PrimeReciprocalLiminf
