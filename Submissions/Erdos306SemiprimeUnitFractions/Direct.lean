import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

namespace Submissions.Erdos306SemiprimeUnitFractions.Direct

open ArithmeticFunction
open scoped omega Omega BigOperators

theorem proof :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ,
        n 0 = 1 ∧ StrictMono n ∧
        (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
        (1 : ℚ) / (p * q) =
          ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / n i := by
  intro p q hp hq hpq
  let n : Fin 2 → ℕ := fun i => if (i : ℕ) = 0 then 1 else p * q
  have hpq_gt : 1 < p * q := by
    have hp2 : 2 ≤ p := hp.two_le
    have hq2 : 2 ≤ q := hq.two_le
    nlinarith
  have hnmono : StrictMono n := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [n]
  have hcop : p.Coprime q := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hp1 | hpq'
    · exact hp.ne_one hp1
    · exact hpq hpq'
  have homega : ω (p * q) = 2 := by
    rw [cardDistinctFactors_mul hcop]
    simp [hp, hq]
  have hOmega : Ω (p * q) = 2 := by
    rw [cardFactors_mul hp.ne_zero hq.ne_zero]
    simp [hp, hq]
  refine ⟨1, n, by simp [n], hnmono, ?_, ?_⟩
  · intro i hi
    fin_cases i
    · simp at hi
    · simpa [n] using And.intro homega hOmega
  · simp [n]

end Submissions.Erdos306SemiprimeUnitFractions.Direct
