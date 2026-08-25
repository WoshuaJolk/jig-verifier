import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

namespace Submissions.Erdos962ElementaryBounds.Direct

def HasLargePrimeBlock (n width : ℕ) : Prop :=
  ∃ start ≤ n, ∀ offset ∈ Set.Icc 1 width,
    ∃ p : ℕ, p.Prime ∧ width < p ∧ p ∣ start + offset

noncomputable def maxWidth (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun width => HasLargePrimeBlock n width) n

theorem proof :
    (∀ n : ℕ, maxWidth n ≤ n) ∧
      ∀ n : ℕ, 1 ≤ n → 1 ≤ maxWidth n := by
  constructor
  · intro n
    classical
    exact Nat.findGreatest_le n
  · intro n hn
    classical
    apply Nat.le_findGreatest hn
    refine ⟨1, hn, ?_⟩
    intro offset hoffset
    have hoffset' : offset = 1 := by
      simp only [Set.mem_Icc] at hoffset
      omega
    subst offset
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩

end Submissions.Erdos962ElementaryBounds.Direct
