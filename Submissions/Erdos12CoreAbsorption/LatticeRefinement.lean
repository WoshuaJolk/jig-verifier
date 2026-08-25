import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Submissions.Erdos12CoreAbsorption.LatticeRefinement

/-- In normalized affine moduli `r + L*q` with `gcd(L,r)=1`, any common
factor `c` is coprime to the slope and forces all relevant quotients into one
class modulo `c`.  Passing to `q=q₀+c*k` refines the lattice and divides the
common factor out of every modulus exactly. -/
theorem proof :
    ∀ L r c q₀ : ℕ,
      Nat.Coprime L r →
      0 < c →
      c ∣ r + L * q₀ →
      Nat.Coprime c L ∧
        (∀ q, q₀ ≤ q → c ∣ r + L * q → c ∣ q - q₀) ∧
        ∃ d,
          r + L * q₀ = c * d ∧
          Nat.gcd (L * c) (r + L * q₀) = c ∧
          ∀ k, r + L * (q₀ + c * k) = c * (d + L * k) := by
  intro L r c q₀ hLr hc0 hcbase
  have hbaseL : Nat.Coprime (r + L * q₀) L := by
    exact (Nat.coprime_add_mul_left_left r L q₀).2 hLr.symm
  have hcL : Nat.Coprime c L := hbaseL.of_dvd_left hcbase
  refine ⟨hcL, ?_, ?_⟩
  · intro q hq hcq
    have hsub :
        (r + L * q) - (r + L * q₀) = L * (q - q₀) := by
      rw [Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    have hcprod : c ∣ L * (q - q₀) := by
      rw [← hsub]
      exact Nat.dvd_sub hcq hcbase
    apply (hcL.dvd_mul_right).mp
    simpa [Nat.mul_comm] using hcprod
  · obtain ⟨d, hd⟩ := hcbase
    have hddiv : d ∣ r + L * q₀ := by
      refine ⟨c, ?_⟩
      rw [hd]
      exact Nat.mul_comm c d
    have hLd : Nat.Coprime L d := hbaseL.symm.of_dvd_right hddiv
    refine ⟨d, hd, ?_, ?_⟩
    · calc
        Nat.gcd (L * c) (r + L * q₀) =
            Nat.gcd (c * L) (c * d) := by rw [hd, Nat.mul_comm L c]
        _ = c * Nat.gcd L d := Nat.gcd_mul_left c L d
        _ = c := by rw [hLd.gcd_eq_one]; simp
    · intro k
      calc
        r + L * (q₀ + c * k) = (r + L * q₀) + L * (c * k) := by ring
        _ = c * d + L * (c * k) := by rw [hd]
        _ = c * (d + L * k) := by ring

end Submissions.Erdos12CoreAbsorption.LatticeRefinement
