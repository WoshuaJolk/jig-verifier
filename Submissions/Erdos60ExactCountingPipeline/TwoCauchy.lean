import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos60ExactCountingPipeline.TwoCauchy

private theorem falling_factorial_cauchy
    {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (∑ i, f i) ^ 2 ≤
      Fintype.card ι *
        ((∑ i, f i * (f i - 1)) + ∑ i, f i) := by
  classical
  have hs :
      (∑ i, f i ^ 2) =
        (∑ i, f i * (f i - 1)) + ∑ i, f i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases h : f i with
    | zero => simp [h]
    | succ k => simp [h, pow_two, Nat.succ_mul, Nat.mul_succ]
  simpa [hs] using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ι)) (f := f))

private abbrev DistinctPairs (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≠ p.2}

private theorem two_stage_cauchy (n : ℕ)
    (degree : Fin n → ℕ) (codegree : DistinctPairs n → ℕ) :
    ((∑ v, degree v) ^ 2 ≤
      n * ((∑ v, degree v * (degree v - 1)) + ∑ v, degree v)) ∧
    ((∑ p, codegree p) ^ 2 ≤
      (n * (n - 1)) *
        ((∑ p, codegree p * (codegree p - 1)) +
          ∑ p, codegree p)) := by
  constructor
  · simpa using falling_factorial_cauchy degree
  · have hcard : Fintype.card (DistinctPairs n) = n * (n - 1) := by
      classical
      calc
        _ = Fintype.card
            ↥((Finset.univ : Finset (Fin n)).offDiag) := by
          apply Fintype.card_congr
          exact
            { toFun := fun p => ⟨p.1, by
                simpa only [Finset.mem_offDiag, Finset.mem_univ,
                  true_and] using p.2⟩
              invFun := fun p => ⟨p.1, by
                simpa only [Finset.mem_offDiag, Finset.mem_univ,
                  true_and] using p.2⟩
              left_inv := fun p => Subtype.ext rfl
              right_inv := fun p => Subtype.ext rfl }
        _ = ((Finset.univ : Finset (Fin n)).offDiag).card :=
          Fintype.card_coe _
        _ = n * (n - 1) := by
          rw [Finset.offDiag_card]
          simp [pow_two, Nat.mul_sub_left_distrib]
    simpa [hcard] using falling_factorial_cauchy codegree

theorem proof :
    ∀ (n m C : ℕ)
      (degree : Fin n → ℕ) (codegree : DistinctPairs n → ℕ),
      (∑ v, degree v) = 2 * m →
      (∑ v, degree v * (degree v - 1)) =
        ∑ p, codegree p →
      (∑ p, codegree p * (codegree p - 1)) = 8 * C →
      ((2 * m) ^ 2 ≤
        n * ((∑ p, codegree p) + 2 * m)) ∧
      ((∑ p, codegree p) ^ 2 ≤
        (n * (n - 1)) * (8 * C + ∑ p, codegree p)) := by
  intro n m C degree codegree hDegreeSum hIncidence hCycle
  have h := two_stage_cauchy n degree codegree
  constructor
  · simpa [hDegreeSum, hIncidence] using h.1
  · simpa [hCycle] using h.2

end Submissions.Erdos60ExactCountingPipeline.TwoCauchy
