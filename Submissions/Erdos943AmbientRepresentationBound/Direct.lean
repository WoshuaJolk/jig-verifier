import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos943AmbientRepresentationBound.Direct

def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

noncomputable def sumRep (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    (fun pair : ℕ × ℕ => Powerful pair.1 ∧ Powerful pair.2)).card

theorem proof : ∀ n : ℕ, sumRep n ≤ n + 1 := by
  intro n
  classical
  unfold sumRep
  exact (Finset.card_filter_le
    (Finset.antidiagonal n)
    (fun pair : ℕ × ℕ => Powerful pair.1 ∧ Powerful pair.2)).trans_eq
      (Finset.Nat.card_antidiagonal n)

end Submissions.Erdos943AmbientRepresentationBound.Direct
