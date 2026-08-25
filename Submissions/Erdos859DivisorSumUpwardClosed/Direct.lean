import Mathlib.NumberTheory.Divisors

namespace Submissions.Erdos859DivisorSumUpwardClosed.Direct

private def DivisorSumSet (t : ℕ) : Set ℕ :=
  {n : ℕ | ∃ s ⊆ Nat.divisors n, t = ∑ i ∈ s, i}

theorem proof :
    ∀ t n m : ℕ, n ≠ 0 → m ≠ 0 → n ∣ m →
      n ∈ DivisorSumSet t → m ∈ DivisorSumSet t := by
  intro t n m _ hm hnm
  rintro ⟨s, hs, hsum⟩
  refine ⟨s, ?_, hsum⟩
  intro d hd
  have hdn : d ∈ Nat.divisors n := hs hd
  exact Nat.mem_divisors.mpr
    ⟨(Nat.dvd_of_mem_divisors hdn).trans hnm, hm⟩

end Submissions.Erdos859DivisorSumUpwardClosed.Direct
