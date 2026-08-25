import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Count
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Topology.Instances.Nat

/-!
# Erdős problem 456(i)

Compare the least prime `p(n) = 1 mod n` with the least positive integer
whose Euler totient is divisible by `n`.
-/

open Nat Filter
open scoped Topology

namespace Statements.Erdos456AlmostAllTotientMinimum

noncomputable def p (n : ℕ) : ℕ :=
  sInf {q | q.Prime ∧ q ≡ 1 [MOD n]}

noncomputable def m (n : ℕ) : ℕ :=
  sInf {q | 0 < q ∧ n ∣ totient q}

abbrev statement : Prop :=
  Tendsto (fun N => (count (fun n => m n < p n) N : ℝ) / (N : ℝ))
    atTop (𝓝 1)

theorem target : statement := sorry

end Statements.Erdos456AlmostAllTotientMinimum
