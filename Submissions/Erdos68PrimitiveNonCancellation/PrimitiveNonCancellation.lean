import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68PrimitiveNonCancellation.PrimitiveNonCancellation

private theorem primitive_factor_survives
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℕ)
    (k : ι) (p : ℕ) (hk : k ∈ s) (hp : p.Prime)
    (hpk : p ∣ d k)
    (hprimitive : ∀ i ∈ s, i ≠ k → ¬p ∣ d i) :
    ¬p ∣ ∑ i ∈ s, ∏ j ∈ s.erase i, d j := by
  have hlast : ¬p ∣ ∏ j ∈ s.erase k, d j := by
    apply hp.prime.not_dvd_finsetProd
    intro j hj
    exact hprimitive j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  have hrest :
      p ∣ ∑ i ∈ s.erase k, ∏ j ∈ s.erase i, d j := by
    apply Finset.dvd_sum
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hki : k ∈ s.erase i := Finset.mem_erase.mpr ⟨hik.symm, hk⟩
    exact hpk.trans (Finset.dvd_prod_of_mem d hki)
  intro htotal
  have hsum :
      p ∣ (∑ i ∈ s.erase k, ∏ j ∈ s.erase i, d j) +
        ∏ j ∈ s.erase k, d j := by
    rwa [Finset.sum_erase_add s (fun i => ∏ j ∈ s.erase i, d j) hk]
  exact hlast ((Nat.dvd_add_iff_right hrest).mpr hsum)

/-- A prime that first appears in `N! - 1` cannot cancel from the canonical
common numerator of the finite reciprocal sum from `2` through `N`. -/
theorem proof :
    ∀ N p : ℕ, 2 ≤ N → p.Prime → p ∣ N.factorial - 1 →
      (∀ n : ℕ, 2 ≤ n → n < N → ¬p ∣ n.factorial - 1) →
      ¬p ∣
        ∑ n ∈ Finset.Icc 2 N,
          ∏ m ∈ (Finset.Icc 2 N).erase n, (m.factorial - 1) := by
  intro N p hN hp hpN hprimitive
  apply primitive_factor_survives (Finset.Icc 2 N)
      (fun n => n.factorial - 1) N p
  · exact Finset.mem_Icc.mpr ⟨hN, le_rfl⟩
  · exact hp
  · exact hpN
  · intro n hn hnN
    exact hprimitive n (Finset.mem_Icc.mp hn).1 (lt_of_le_of_ne (Finset.mem_Icc.mp hn).2 hnN)

end Submissions.Erdos68PrimitiveNonCancellation.PrimitiveNonCancellation
