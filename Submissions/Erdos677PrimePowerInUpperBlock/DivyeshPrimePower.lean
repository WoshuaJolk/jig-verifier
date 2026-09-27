import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Submissions.Erdos677PrimePowerInUpperBlock.DivyeshPrimePower

def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

theorem proof :
    ∀ n m k p a : ℕ, n + k ≤ m → p.Prime → 0 < a →
      m < p ^ a → p ^ a ≤ m + k →
      lcmInterval m k ≠ lcmInterval n k := by
  intro n m k p a hnm hp ha hmp hpk heq
  have hmem : p ^ a ∈ Finset.Ioc m (m + k) := Finset.mem_Ioc.2 ⟨hmp, hpk⟩
  have hdiv : p ^ a ∣ lcmInterval m k := Finset.dvd_lcm hmem
  rw [heq] at hdiv
  have hnonzero : lcmInterval n k ≠ 0 := by
    unfold lcmInterval
    exact Finset.lcm_ne_zero_iff.mpr (by
      intro x hx
      have := (Finset.mem_Ioc.mp hx).1
      omega)
  have hfact : a ≤ (lcmInterval n k).factorization p :=
    (hp.pow_dvd_iff_le_factorization hnonzero).mp hdiv
  have hsup := Finset.factorization_lcm (s := Finset.Ioc n (n + k))
    (f := id) (by
      intro x hx
      have := (Finset.mem_Ioc.mp hx).1
      omega) p
  unfold lcmInterval at hfact
  rw [hsup] at hfact
  have hall : ∀ x ∈ Finset.Ioc n (n + k), x.factorization p ≤ a - 1 := by
    intro x hx
    have hxpos : x ≠ 0 := by have := (Finset.mem_Ioc.mp hx).1; omega
    have hnot : ¬ p ^ a ∣ x := by
      intro hd
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hxpos) hd
      have := (Finset.mem_Ioc.mp hx).2
      omega
    have hlt : x.factorization p < a := Nat.lt_of_not_ge
      (fun h => hnot ((hp.pow_dvd_iff_le_factorization hxpos).mpr h))
    omega
  have hbound : (Finset.Ioc n (n + k)).sup (fun x => x.factorization p) ≤ a - 1 :=
    Finset.sup_le hall
  omega

end Submissions.Erdos677PrimePowerInUpperBlock.DivyeshPrimePower
