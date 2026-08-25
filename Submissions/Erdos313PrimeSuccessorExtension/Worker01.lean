import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Submissions.Erdos313PrimeSuccessorExtension.Worker01

open Finset

def IsSolution (m : ℕ) (P : Finset ℕ) : Prop :=
  2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧
    ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m

theorem proof :
    ∀ m P, IsSolution m P → (m + 1).Prime → m + 1 ∉ P →
      IsSolution (m * (m + 1)) (insert (m + 1) P) := by
  rintro m P ⟨hm, hP, hprimes, hsum⟩ hnext hfresh
  refine ⟨?_, Finset.insert_nonempty _ _, ?_, ?_⟩
  · nlinarith
  · intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hnext
    · exact hprimes p hp
  · rw [Finset.sum_insert hfresh, hsum]
    have hm0 : (m : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm))
    have hsucc0 : (m + 1 : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end Submissions.Erdos313PrimeSuccessorExtension.Worker01
