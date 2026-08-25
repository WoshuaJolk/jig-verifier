import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1212ShortCompositeAnchor.PrimeFactorGap

def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧
    (¬ p.1.Prime ∨ ¬ p.2.Prime)

private theorem coprime_of_short_leg {a s : ℕ} (hs : a < s)
    (h : ∀ p, p.Prime → p ∣ a → s < a + p) : Nat.gcd a s = 1 := by
  by_contra hg
  obtain ⟨p, hp, hpd⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.gcd a s) (by
      intro h1
      exact hg h1)
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a s)
  have hps : p ∣ s := hpd.trans (Nat.gcd_dvd_right a s)
  have hlt : s < a + p := h p hp hpa
  obtain ⟨k, hk⟩ := hpa
  obtain ⟨l, hl⟩ := hps
  have hkl : k < l := by
    have : p * k < p * l := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hstep : p * (k + 1) ≤ p * l := Nat.mul_le_mul_left p hkl
  have heq : p * (k + 1) = a + p := by rw [hk]; ring
  omega

theorem proof :
    ∀ {a b c : ℕ},
      (1 < a ∧ ¬ a.Prime) →
        a < b →
          (∀ p, p.Prime → p ∣ a → c < a + p) →
            ∀ s, b ≤ s → s ≤ c → Valid (a, s) := by
  intro a b c ha hab hrough s hbs hsc
  have has : a < s := hab.trans_le hbs
  refine ⟨ha.1, by omega, coprime_of_short_leg has ?_, Or.inl ha.2⟩
  intro p hp hpa
  exact hsc.trans_lt (hrough p hp hpa)

end Submissions.Erdos1212ShortCompositeAnchor.PrimeFactorGap
