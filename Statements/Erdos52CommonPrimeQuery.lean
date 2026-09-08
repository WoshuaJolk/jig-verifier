import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.Rat

/- The finite common-prime query charge, stated independently of its proof.
The full integer sum-product conjecture is not asserted here. -/
namespace Statements.Erdos52CommonPrimeQuery

/-- Remove the complete prime-power factor of a rational number. -/
def unitPart (p : ℕ) (x : ℚ) : ℚ := x / (p : ℚ) ^ padicValRat p x

/-- All normalized cofactors that occur at an endpoint of the selected graph. -/
def cofactorSet (p : ℕ) (R : Finset (ℚ × ℚ)) : Finset ℚ :=
  R.image (fun z => unitPart p z.1) ∪
    R.image (fun z => unitPart p z.2)

def statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (H : ℕ) (hH : 2 ≤ H)
    (R : Finset (ℚ × ℚ)) (M : ℕ)
    (hnz : ∀ z ∈ R, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hcap : ∀ u : ℚ,
      ((R.image (fun z => (unitPart p z.1, unitPart p z.2))).filter
        (fun c => c.1 * c.2 = u)).card ≤ M),
    R.card ≤
      2 * ((H + 1) * Nat.clog 2 (cofactorSet p R).card + 1) *
        (2 * Nat.clog H (cofactorSet p R).card).choose (Nat.clog H (cofactorSet p R).card) *
        (R.image (fun z => z.1 + z.2)).card +
      M * ((H + 1) * Nat.clog 2 (cofactorSet p R).card + 1) ^ 2 *
        (R.image (fun z => z.1 * z.2)).card

end Statements.Erdos52CommonPrimeQuery
