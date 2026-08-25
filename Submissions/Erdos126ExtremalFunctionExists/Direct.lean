import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos126ExtremalFunctionExists.Direct

open scoped BigOperators

def addFactorsCard (A : Finset ℕ) : ℕ :=
  (∏ p ∈ A.offDiag, (p.1 + p.2)).primeFactors.card

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n,
    IsGreatest
      {m | ∀ (A : Finset ℕ), A.card = n → m ≤ addFactorsCard A}
      (f n)

theorem proof : ∃ f : ℕ → ℕ, IsMaximalAddFactorsCard f := by
  let values : ℕ → Set ℕ :=
    fun n => {k | ∃ A : Finset ℕ, A.card = n ∧ addFactorsCard A = k}
  let f : ℕ → ℕ := fun n => sInf (values n)
  refine ⟨f, fun n => ?_⟩
  have hvalues : (values n).Nonempty := by
    refine ⟨addFactorsCard (Finset.range n), Finset.range n, ?_, rfl⟩
    simp
  constructor
  · intro A hA
    apply Nat.sInf_le
    exact ⟨A, hA, rfl⟩
  · intro m hm
    obtain ⟨A, hA, hvalue⟩ := Nat.sInf_mem hvalues
    have hle := hm A hA
    simpa [f] using hvalue ▸ hle

end Submissions.Erdos126ExtremalFunctionExists.Direct
