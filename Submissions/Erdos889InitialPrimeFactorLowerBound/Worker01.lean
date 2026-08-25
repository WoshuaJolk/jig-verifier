import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PrimeFin

namespace Submissions.Erdos889InitialPrimeFactorLowerBound.Worker01

def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter fun p ↦
    ∀ i ∈ Finset.range k, ¬p ∣ n + i).card

noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)

theorem proof :
    ∀ n : ℕ, v n 0 = n.primeFactors.card ∧
      (n.primeFactors.card : ℕ∞) ≤ v₀ n := by
  intro n
  have hv : v n 0 = n.primeFactors.card := by
    simp [v]
  refine ⟨hv, ?_⟩
  have hterm : (v n 0 : ℕ∞) ≤ v₀ n := by
    exact le_iSup (fun k : ℕ ↦ (v n k : ℕ∞)) 0
  simpa only [hv] using hterm

end Submissions.Erdos889InitialPrimeFactorLowerBound.Worker01
