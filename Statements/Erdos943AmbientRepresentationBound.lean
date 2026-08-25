import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.PrimeFin

namespace Statements.Erdos943AmbientRepresentationBound

def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

noncomputable def sumRep (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    (fun pair : ℕ × ℕ => Powerful pair.1 ∧ Powerful pair.2)).card

/-- The powerful-sum representations form a subset of the full
additive antidiagonal. -/
abbrev statement : Prop :=
  ∀ n : ℕ, sumRep n ≤ n + 1

theorem target : statement := sorry

end Statements.Erdos943AmbientRepresentationBound
