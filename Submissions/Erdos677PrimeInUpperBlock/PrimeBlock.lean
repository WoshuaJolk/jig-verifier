import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos677PrimeInUpperBlock.PrimeBlock

def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

theorem proof :
    ∀ n m k p : ℕ, n + k ≤ m → p.Prime → m < p → p ≤ m + k →
      lcmInterval m k ≠ lcmInterval n k := by
  intro n m k p hnm hp hmp hpk heq
  have hmem : p ∈ Finset.Ioc m (m + k) := Finset.mem_Ioc.2 ⟨hmp, hpk⟩
  have h1 : p ∣ lcmInterval m k := Finset.dvd_lcm hmem
  rw [heq] at h1
  have h2 : lcmInterval n k ∣ ∏ x ∈ Finset.Ioc n (n + k), x :=
    Finset.lcm_dvd (fun b hb => Finset.dvd_prod_of_mem id hb)
  have h3 : p ∣ ∏ x ∈ Finset.Ioc n (n + k), x := h1.trans h2
  obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finset_prod_iff id).1 h3
  rw [Finset.mem_Ioc] at hx
  have hxpos : 0 < x := lt_of_le_of_lt (Nat.zero_le n) hx.1
  have : p ≤ x := Nat.le_of_dvd hxpos hpx
  omega

end Submissions.Erdos677PrimeInUpperBlock.PrimeBlock
