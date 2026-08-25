import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos172SizeOne.Worker04

theorem proof :
    ∀ (n : ℕ) (color : ℕ → Fin n),
      ∃ A : Finset ℕ, A.card ≥ 1 ∧ ∃ c, ∀ S : Finset A,
        S.Nonempty →
        color (∑ x ∈ S, x) = c ∧ color (∏ x ∈ S, x) = c := by
  intro n color
  refine ⟨{1}, by simp, color 1, ?_⟩
  intro S hS
  obtain ⟨x, hx⟩ := hS
  have hxval : (x : ℕ) = 1 := Finset.mem_singleton.mp x.property
  have hSx : S = {x} := by
    ext y
    constructor
    · intro hy
      have hyval : (y : ℕ) = 1 := Finset.mem_singleton.mp y.property
      have hyx : y = x := Subtype.ext (hyval.trans hxval.symm)
      simpa [hyx]
    · intro hy
      have hyx : y = x := Finset.mem_singleton.mp hy
      simpa [hyx] using hx
  subst S
  simp [hxval]

end Submissions.Erdos172SizeOne.Worker04
