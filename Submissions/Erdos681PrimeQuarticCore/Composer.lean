import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

open Filter

namespace Submissions.Erdos681PrimeQuarticCore.Composer

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

def Witness (n k : ℕ) : Prop :=
  0 < k ∧ IsComposite (n + k) ∧
    ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

private theorem necessary_quartic
    (n k : ℕ) (_hk : 0 < k) (hcomp : IsComposite (n + k))
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
    (∀ᶠ n : ℕ in atTop, ∃ k : ℕ, Witness n k) ↔
      ∀ᶠ n : ℕ in atTop, (n + 1).Prime →
        ∃ k : ℕ, Witness n k ∧ (k ^ 2) ^ 2 < n + k := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    intro _
    obtain ⟨k, hk, hcomp, hrough⟩ := hn
    exact ⟨k, ⟨hk, hcomp, hrough⟩,
      necessary_quartic n k hk hcomp hrough⟩
  · intro h
    filter_upwards [h, eventually_ge_atTop 2] with n hn h2
    by_cases hp : (n + 1).Prime
    · obtain ⟨k, hw, _⟩ := hn hp
      exact ⟨k, hw⟩
    · refine ⟨1, by omega, ⟨by omega, hp⟩, ?_⟩
      intro p hleast
      have hp2 : 2 ≤ p := hleast.1.two_le
      omega

end Submissions.Erdos681PrimeQuarticCore.Composer
