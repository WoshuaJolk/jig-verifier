import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat

namespace Submissions.Erdos890WidthOneLiminf.Control

open Filter Finset

def omegaGt (k n : ℕ) : ℕ :=
  (n.primeFactors.filter (· > k)).card

abbrev claimedStatement : Prop :=
  liminf
    (fun n : ℕ => (∑ i ∈ range 1, (omegaGt 1 (n + i) : EReal)))
    atTop ≤ 1

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos890WidthOneLiminf.Control
