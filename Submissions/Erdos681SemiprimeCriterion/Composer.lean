import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos681SemiprimeCriterion.Composer

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

def Witness (n k : ℕ) : Prop :=
  0 < k ∧ IsComposite (n + k) ∧
    ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

def SemiprimeCore : Prop :=
  ∀ᶠ n : ℕ in atTop, (n + 1).Prime →
    ∃ k p q : ℕ, 0 < k ∧ p.Prime ∧ q.Prime ∧ p ≤ q ∧
      n + k = p * q ∧ k ^ 2 < p

private theorem necessary_quartic
    (n k : ℕ) (hcomp : IsComposite (n + k))
    (hrough : ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p) :
    (k ^ 2) ^ 2 < n + k := by
  let m := n + k
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hcomp.1
  have hm1 : m ≠ 1 := ne_of_gt hcomp.1
  have hmin : IsLeastPrimeFactor m.minFac m := by
    refine ⟨Nat.minFac_prime hm1, Nat.minFac_dvd m, ?_⟩
    intro q hq
    exact Nat.minFac_le_of_dvd hq.1.two_le hq.2
  have hkmin : k ^ 2 < m.minFac := hrough m.minFac hmin
  have hsquares : (k ^ 2) ^ 2 < m.minFac ^ 2 :=
    Nat.pow_lt_pow_left hkmin (by decide)
  exact hsquares.trans_le (Nat.minFac_sq_le_self hm0 hcomp.2)

theorem proof :
    SemiprimeCore →
      ∀ᶠ n : ℕ in atTop, (n + 1).Prime →
        ∃ k : ℕ, Witness n k ∧ (k ^ 2) ^ 2 < n + k := by
  intro h
  filter_upwards [h] with n hn
  intro hprime
  obtain ⟨k, p, q, hk, hp, hq, hpq, hprod, hkp⟩ := hn hprime
  have hcomp : IsComposite (n + k) := by
    rw [hprod]
    exact ⟨by nlinarith [hp.two_le, hq.two_le],
      Nat.not_prime_mul hp.ne_one hq.ne_one⟩
  have hrough :
      ∀ r : ℕ, IsLeastPrimeFactor r (n + k) → k ^ 2 < r := by
    intro r hr
    have hrdiv : r ∣ p * q := by
      rw [← hprod]
      exact hr.2.1
    rcases (hr.1.dvd_mul.mp hrdiv) with hrp | hrq
    · have hr_eq : r = p :=
        ((Nat.dvd_prime hp).mp hrp).resolve_left hr.1.ne_one
      simpa [hr_eq] using hkp
    · have hr_eq : r = q :=
        ((Nat.dvd_prime hq).mp hrq).resolve_left hr.1.ne_one
      exact hkp.trans_le (by simpa [hr_eq] using hpq)
  exact ⟨k, ⟨hk, hcomp, hrough⟩, necessary_quartic n k hcomp hrough⟩

end Submissions.Erdos681SemiprimeCriterion.Composer
