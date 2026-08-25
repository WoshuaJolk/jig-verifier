import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Submissions.Erdos304NumeratorOne.Worker04

def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ,
    s.card = k ∧ (∀ n ∈ s, n > 1) ∧
      (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

noncomputable def smallestCollection (a b : ℕ) : ℕ :=
  sInf (unitFractionExpressible a b)

theorem proof : ∀ b : ℕ, 1 < b → smallestCollection 1 b = 1 := by
  intro b hb
  have h : 1 ∈ unitFractionExpressible 1 b := ⟨{b}, by simpa⟩
  have hle : smallestCollection 1 b ≤ 1 := Nat.sInf_le h
  have hzero : 0 ∉ unitFractionExpressible 1 b := by
    simp [unitFractionExpressible]
    omega
  have hne : smallestCollection 1 b ≠ 0 :=
    ne_of_mem_of_not_mem (Nat.sInf_mem ⟨_, h⟩) hzero
  omega

end Submissions.Erdos304NumeratorOne.Worker04
