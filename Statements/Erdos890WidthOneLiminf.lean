import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat

namespace Statements.Erdos890WidthOneLiminf

open Filter Finset

def omegaGt (k n : ℕ) : ℕ :=
  (n.primeFactors.filter (· > k)).card

/-- The complete width-one case of Erdős Problem 890(a). -/
abbrev statement : Prop :=
  liminf
    (fun n : ℕ => (∑ i ∈ range 1, (omegaGt 1 (n + i) : EReal)))
    atTop ≤ 1

theorem target : statement := sorry

end Statements.Erdos890WidthOneLiminf
