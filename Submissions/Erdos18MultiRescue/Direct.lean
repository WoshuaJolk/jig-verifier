import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos18MultiRescue.Direct

def threeRep (N m : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    D ⊆ N.factorial.divisors ∧
    D.card ≤ 3 ∧
    m = D.sum id

theorem factorial_split {n : ℕ} (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Nat.factorial_succ]
  congr 1
  omega

theorem multiRescue :
    ∀ k q v y r s t w z : ℕ,
      6 ≤ k →
      q = k * v + y →
      q + v = w + t →
      y + r + k * t = s + z →
      0 < w →
      0 < s →
      0 < z →
      r < k + 1 →
      w ∣ (k - 1).factorial →
      s ∣ (k + 1).factorial →
      z ∣ (k + 1).factorial →
      s ≠ k * w →
      s ≠ z →
      k * w ≠ z →
      threeRep (k + 1) ((k + 1) * q + r) := by
  intro k q v y r s t w z hk hq hwt hsz hw hs hz hr hwdiv hsdiv hzdiv
    hskw hszne hkwz
  have hkpos : 0 < k := by omega
  have hkwdiv : k * w ∣ k.factorial := by
    rw [factorial_split hkpos]
    simpa using Nat.mul_dvd_mul_left k hwdiv
  have hkwdiv' : k * w ∣ (k + 1).factorial :=
    hkwdiv.trans (Nat.factorial_dvd_factorial (by omega))
  have hsum : (k + 1) * q + r = s + k * w + z := by
    have hqmul := congrArg (fun a : ℕ => (k + 1) * a) hq
    have hwtmul := congrArg (fun a : ℕ => k * a) hwt
    nlinarith
  refine ⟨{s, k * w, z}, ?_,
    by simp [hskw, hszne, hkwz], ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr
        ⟨hsdiv, Nat.factorial_ne_zero (k + 1)⟩
    · exact Nat.mem_divisors.mpr
        ⟨hkwdiv', Nat.factorial_ne_zero (k + 1)⟩
    · exact Nat.mem_divisors.mpr
        ⟨hzdiv, Nat.factorial_ne_zero (k + 1)⟩
  · simpa [Nat.add_assoc, hskw, hszne, hkwz] using hsum

theorem largePrimeObstructsAtMostOne :
    ∀ p A h s t : ℕ,
      p.Prime →
      h < p →
      0 < s →
      s < t →
      t ≤ h →
      h < A →
      ¬(p ∣ A - s ∧ p ∣ A - t) := by
  intro p A h s t hp hhp hs hst hth hhA
  rintro ⟨hps, hpt⟩
  have htA : t ≤ A := by omega
  have hsum : A - s = (A - t) + (t - s) := by omega
  have hpdiff : p ∣ t - s := by
    apply (Nat.dvd_add_iff_right hpt).2
    rw [← hsum]
    exact hps
  have hdiffpos : 0 < t - s := by omega
  have hple : p ≤ t - s := Nat.le_of_dvd hdiffpos hpdiff
  omega

def smallS : ℕ → ℕ
  | 1 => 2
  | 4 => 2
  | 5 => 3
  | 7 => 2
  | 9 => 2
  | 11 => 2
  | 16 => 2
  | 20 => 2
  | 21 => 3
  | 22 => 29
  | 25 => 2
  | 27 => 2
  | _ => 1

def modelV (r : ℕ) : ℕ := if r = 22 then 647 else 649
def modelY (r : ℕ) : ℕ := if r = 22 then 75 else 19
def modelT (r : ℕ) : ℕ := if r = 22 then 1 else 3
def modelZ (r : ℕ) : ℕ :=
  if r = 22 then 96 else 103 + r - smallS r

theorem model29 :
    ∀ r : ℕ, r < 29 →
      threeRep 29 (29 * 18191 + r) := by
  intro r hr
  apply multiRescue 28 18191 (modelV r) (modelY r) r
    (smallS r) (modelT r) 18837 (modelZ r)
  all_goals interval_cases r <;>
    norm_num [smallS, modelV, modelY, modelT, modelZ, Nat.factorial]

theorem proof :
    (∀ k q v y r s t w z : ℕ,
      6 ≤ k →
      q = k * v + y →
      q + v = w + t →
      y + r + k * t = s + z →
      0 < w →
      0 < s →
      0 < z →
      r < k + 1 →
      w ∣ (k - 1).factorial →
      s ∣ (k + 1).factorial →
      z ∣ (k + 1).factorial →
      s ≠ k * w →
      s ≠ z →
      k * w ≠ z →
      threeRep (k + 1) ((k + 1) * q + r)) ∧
    (∀ p A h s t : ℕ,
      p.Prime →
      h < p →
      0 < s →
      s < t →
      t ≤ h →
      h < A →
      ¬(p ∣ A - s ∧ p ∣ A - t)) ∧
    (∀ r : ℕ, r < 29 →
      threeRep 29 (29 * 18191 + r)) ∧
    (Nat.Prime 31 ∧ 31 ∣ 124 ∧
      Nat.Prime 41 ∧ 41 ∣ 123 ∧
      Nat.Prime 61 ∧ 61 ∣ 122 ∧
      96 ∣ Nat.factorial 29) := by
  exact ⟨multiRescue, largePrimeObstructsAtMostOne, model29,
    by norm_num [Nat.factorial]⟩

end Submissions.Erdos18MultiRescue.Direct
