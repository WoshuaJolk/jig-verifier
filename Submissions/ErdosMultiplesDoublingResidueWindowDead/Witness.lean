import Mathlib.Order.Interval.Finset.Nat

/-!
Witness: `A = 17 · {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59}`,
`n = 1946`, residues `1, …, 16, 0` in increasing order of the generators.
`M(1946) = 100`; the seventeen residue classes are pairwise disjoint (their residues are pairwise
distinct modulo `17`) and together hold `201` elements of `[1, 1946]`.
-/

namespace Submissions.ErdosMultiplesDoublingResidueWindowDead.Witness

/-- The residue assigned to each generator. -/
def r (a : ℕ) : ℕ :=
  if a = 34 then 1 else if a = 51 then 2 else if a = 85 then 3 else if a = 119 then 4 else
  if a = 187 then 5 else if a = 221 then 6 else if a = 289 then 7 else if a = 323 then 8 else
  if a = 391 then 9 else if a = 493 then 10 else if a = 527 then 11 else if a = 629 then 12 else
  if a = 697 then 13 else if a = 731 then 14 else if a = 799 then 15 else if a = 901 then 16 else 0

set_option maxRecDepth 200000 in
theorem proof :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      (∀ b ∈ A, ∀ c ∈ A, b ∣ c → b = c) ∧
      ∃ r : ℕ → ℕ, ∃ n : ℕ, (∀ a ∈ A, a ≤ n) ∧
        2 * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
          ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, k % a = r a)).card :=
  ⟨{34, 51, 85, 119, 187, 221, 289, 323, 391, 493, 527, 629, 697, 731, 799, 901, 1003},
    by decide, by decide, by decide, r, 1946, by decide, by decide⟩

end Submissions.ErdosMultiplesDoublingResidueWindowDead.Witness
