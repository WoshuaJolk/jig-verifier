import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Submissions.Erdos730ExplicitPrimeSupportPairs.KernelCheck

abbrev S : Set (ℕ × ℕ) :=
  {(n, m) : ℕ × ℕ | n < m ∧
    n.centralBinom.primeFactors = m.centralBinom.primeFactors}

theorem proof :
    ({(87, 88), (607, 608)} : Set (ℕ × ℕ)) ⊆ S := by
  have h87a : Nat.centralBinom 87 ∣ Nat.centralBinom 88 ^ 6 := by
    norm_num [Nat.centralBinom, Nat.choose_eq_descFactorial_div_factorial]
  have h87b : Nat.centralBinom 88 ∣ Nat.centralBinom 87 ^ 6 := by
    norm_num [Nat.centralBinom, Nat.choose_eq_descFactorial_div_factorial]
  have h607a : Nat.centralBinom 607 ∣ Nat.centralBinom 608 ^ 6 := by
    norm_num [Nat.centralBinom, Nat.choose_eq_descFactorial_div_factorial]
  have h607b : Nat.centralBinom 608 ∣ Nat.centralBinom 607 ^ 6 := by
    norm_num [Nat.centralBinom, Nat.choose_eq_descFactorial_div_factorial]
  rintro _ (rfl | rfl)
  · refine ⟨by decide, Finset.ext ?_⟩
    intro p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hp.dvd_of_dvd_pow (hd.1.trans h87a),
        Nat.centralBinom_ne_zero _⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hp.dvd_of_dvd_pow (hd.1.trans h87b),
        Nat.centralBinom_ne_zero _⟩
  · refine ⟨by decide, Finset.ext ?_⟩
    intro p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hp.dvd_of_dvd_pow (hd.1.trans h607a),
        Nat.centralBinom_ne_zero _⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hp.dvd_of_dvd_pow (hd.1.trans h607b),
        Nat.centralBinom_ne_zero _⟩

end Submissions.Erdos730ExplicitPrimeSupportPairs.KernelCheck
