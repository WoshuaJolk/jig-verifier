import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

open Nat Finset

namespace Submissions.Erdos394PrimeExact.PrimePair

noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i)}

lemma t_eq_of {n k v : ℕ} (hv : 0 < v)
    (hdvd : n ∣ ∏ i ∈ range k, (v + i))
    (hlt : ∀ m ∈ range v, 0 < m →
      ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    t k n = v := by
  refine le_antisymm (Nat.sInf_le ⟨hv, hdvd⟩) ?_
  by_contra! hc
  have hne :
      {m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i)}.Nonempty :=
    ⟨v, hv, hdvd⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  exact hlt _ (mem_range.mpr hc) hpos hd

theorem proof : ∀ p : ℕ, p.Prime → t 2 p = p - 1 := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  apply t_eq_of
  · omega
  · simp only [prod_range_succ, prod_range_zero, one_mul, add_zero]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
    exact dvd_mul_left p (p - 1)
  · intro m hm hpos hdvd
    have hm_lt : m < p - 1 := mem_range.mp hm
    simp only [prod_range_succ, prod_range_zero, one_mul, add_zero] at hdvd
    rcases hp.dvd_mul.mp hdvd with hpm | hpm1
    · have := Nat.le_of_dvd hpos hpm
      omega
    · have hm1pos : 0 < m + 1 := by omega
      have := Nat.le_of_dvd hm1pos hpm1
      omega

end Submissions.Erdos394PrimeExact.PrimePair
