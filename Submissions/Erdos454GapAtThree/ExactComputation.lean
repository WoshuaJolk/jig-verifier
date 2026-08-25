import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos454GapAtThree.ExactComputation

noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else
    ⨅ i : {i : Fin n // 0 < (i : ℕ)},
      (n + i).nth Nat.Prime + (n - i).nth Nat.Prime

theorem proof : f 3 - 2 * Nat.nth Nat.Prime 3 = 2 := by
  have hp5 : Nat.nth Nat.Prime 5 = 13 :=
    by
      rw [← show Nat.count Nat.Prime 13 = 5 by decide]
      exact Nat.nth_count (by norm_num)
  have hf : f 3 = 16 := by
    rw [f, if_neg (by omega)]
    let i : {i : Fin 3 // 0 < (i : ℕ)} :=
      ⟨⟨1, by decide⟩, by decide⟩
    letI : Nonempty {i : Fin 3 // 0 < (i : ℕ)} := ⟨i⟩
    apply le_antisymm
    · simpa [i] using
        (ciInf_le (OrderBot.bddBelow
          (Set.range fun j : {j : Fin 3 // 0 < (j : ℕ)} ↦
            (3 + (j : ℕ)).nth Nat.Prime +
              (3 - (j : ℕ)).nth Nat.Prime)) i)
    · apply le_ciInf
      rintro ⟨i, hi⟩
      fin_cases i
      · norm_num at hi
      · norm_num
      · simp [hp5]
  simp [hf]

end Submissions.Erdos454GapAtThree.ExactComputation
