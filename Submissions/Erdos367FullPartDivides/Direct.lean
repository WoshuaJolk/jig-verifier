import Mathlib.Data.Nat.Factorization.Basic

namespace Submissions.Erdos367FullPartDivides.Direct

private def fullPart (r n : ℕ) : ℕ :=
  ∏ p ∈ n.factorization.support with r ≤ n.factorization p,
    p ^ n.factorization p

theorem proof : ∀ r n : ℕ, fullPart r n ∣ n := by
  intro r n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fullPart]
  calc
    fullPart r n ∣ n.factorization.prod (· ^ ·) := by
      unfold fullPart
      rw [Finsupp.prod]
      exact Finset.prod_dvd_prod_of_subset
        (n.factorization.support.filter fun p => r ≤ n.factorization p)
        n.factorization.support
        (fun p => p ^ n.factorization p)
        (Finset.filter_subset _ _)
    _ = n := Nat.prod_factorization_pow_eq_self hn

end Submissions.Erdos367FullPartDivides.Direct
