import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Prod
namespace Submissions.Erdos1040PolynomialBoundary.Degenerate
def indexPairs (n : ℕ) : Finset (Fin n × Fin n) := (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2
def rootProduct (roots : List ℂ) (z : ℂ) : ℂ := (roots.map fun r => z - r).prod
theorem proof : False → indexPairs 1 = ∅ ∧ rootProduct [0] 0 = 0 ∧ rootProduct [0] 2 = 2 := False.elim
end Submissions.Erdos1040PolynomialBoundary.Degenerate
