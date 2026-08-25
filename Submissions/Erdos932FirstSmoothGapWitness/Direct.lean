import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos932FirstSmoothGapWitness.Direct

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

theorem proof :
    2 ≤ ((Finset.Ioo ((3 : ℕ).nth Nat.Prime) ((4 : ℕ).nth Nat.Prime)).filter
      (fun m => maxPrimeFac m <
        (4 : ℕ).nth Nat.Prime - (3 : ℕ).nth Nat.Prime)).card := by
  have h7 : (3 : ℕ).nth Nat.Prime = 7 := by
    have h := Nat.nth_count (show Nat.Prime 7 by norm_num)
    norm_num [Nat.count] at h ⊢
  have h11 : (4 : ℕ).nth Nat.Prime = 11 := by
    have h := Nat.nth_count (show Nat.Prime 11 by norm_num)
    norm_num [Nat.count] at h ⊢
  rw [h7, h11]
  decide +kernel

end Submissions.Erdos932FirstSmoothGapWitness.Direct
