import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

namespace Submissions.Erdos883SixVertexTriangle.Direct

def HasCoprimeCycle {n : ℕ} (A : Finset (Fin n)) (ℓ : ℕ) : Prop :=
  ∃ cycle : Fin ℓ → Fin n,
    Function.Injective cycle ∧
    (∀ i, cycle i ∈ A) ∧
    ∀ i j : Fin ℓ, j.val = (i.val + 1) % ℓ →
      Nat.Coprime ((cycle i : ℕ) + 1)
        ((cycle j : ℕ) + 1)

def triangleCycle (i : Fin 3) : Fin 6 :=
  ⟨i.val, by omega⟩

theorem proof :
    6 / 2 + 6 / 3 - 6 / 6 <
        (Finset.univ : Finset (Fin 6)).card ∧
      HasCoprimeCycle (Finset.univ : Finset (Fin 6)) 3 := by
  constructor
  · norm_num
  · refine ⟨triangleCycle, ?_, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact Fin.mk.inj hij
    · intro i
      simp
    · intro i j hnext
      fin_cases i <;> fin_cases j
      all_goals norm_num [triangleCycle] at hnext
      all_goals norm_num [triangleCycle]

end Submissions.Erdos883SixVertexTriangle.Direct
