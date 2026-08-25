import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos681NecessaryQuarticWindow.Worker09Upper

def IsLeastPrimeFactor (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime ∧ q ∣ m → p ≤ q

def IsComposite (m : ℕ) : Prop := 1 < m ∧ ¬m.Prime

theorem proof :
    ∀ n k : ℕ, 0 < k → IsComposite (n + k) →
      (∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p) →
        (k ^ 2) ^ 2 < n + k := by
  intro n k _ hcomp hrough
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

end Submissions.Erdos681NecessaryQuarticWindow.Worker09Upper
