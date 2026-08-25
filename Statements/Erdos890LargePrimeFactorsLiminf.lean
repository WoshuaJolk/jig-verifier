import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat

namespace Statements.Erdos890LargePrimeFactorsLiminf

open Filter Finset

/-- Number of distinct prime factors of `n` strictly greater than `k`. -/
def omegaGt (k n : ℕ) : ℕ :=
  (n.primeFactors.filter (· > k)).card

/-- Erdős Problem 890(a): every length-`k` block has lower-limit total
large-prime-factor count at most `k`. -/
abbrev statement : Prop :=
  ∀ k ≥ 1,
    liminf
      (fun n : ℕ => (∑ i ∈ range k, (omegaGt k (n + i) : EReal)))
      atTop ≤ k

theorem target : statement := sorry

end Statements.Erdos890LargePrimeFactorsLiminf
