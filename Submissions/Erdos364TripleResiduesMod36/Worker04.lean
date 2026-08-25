import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Submissions.Erdos364TripleResiduesMod36.Worker04

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop :=
  Full 2 n

theorem prime_sq_dvd_of_powerful {m p : ℕ} (hm : Powerful m)
    (hp : p.Prime) (hd : p ∣ m) : p ^ 2 ∣ m := by
  by_cases hm0 : m = 0
  · subst m
    exact dvd_zero _
  apply hm p
  exact Nat.mem_primeFactors.mpr ⟨hp, hd, hm0⟩

theorem proof :
    ∀ n : ℕ, Powerful n → Powerful (n + 1) → Powerful (n + 2) →
      n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  intro n hn hn1 hn2
  have h4 (m : ℕ) (hm : Powerful m) : m % 2 = 0 → m % 4 = 0 := by
    intro h
    exact Nat.dvd_iff_mod_eq_zero.mp
      (prime_sq_dvd_of_powerful hm Nat.prime_two (Nat.dvd_iff_mod_eq_zero.mpr h))
  have h9 (m : ℕ) (hm : Powerful m) : m % 3 = 0 → m % 9 = 0 := by
    intro h
    exact Nat.dvd_iff_mod_eq_zero.mp
      (prime_sq_dvd_of_powerful hm Nat.prime_three (Nat.dvd_iff_mod_eq_zero.mpr h))
  have hn4 := h4 n hn
  have hn14 := h4 (n + 1) hn1
  have hn24 := h4 (n + 2) hn2
  have hn9 := h9 n hn
  have hn19 := h9 (n + 1) hn1
  have hn29 := h9 (n + 2) hn2
  omega

end Submissions.Erdos364TripleResiduesMod36.Worker04
