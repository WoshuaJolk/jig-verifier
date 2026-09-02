import Mathlib.Order.Interval.Finset.Nat

/-!
Witness: `A = {2, 3, 5, 7}`, `a = 7`, `n = 48`, `m = 91`.
`E_7(48) = #{7} = 1`, `E_7(91) = #{7, 49, 77, 91} = 4`, so `2·91·1 = 182 < 192 = 48·4`,
while `M(48) = 36`, `M(91) = 70` and `48·70 = 3360 < 6552 = 2·91·36`.
Every conjunct is a finite computation, closed by `decide`.
-/

namespace Submissions.ErdosMultiplesDoublingMaxGenDead.Witness

theorem proof :
    ∃ A : Finset ℕ, A.Nonempty ∧ 0 ∉ A ∧
      (∀ b ∈ A, ∀ c ∈ A, b ∣ c → b = c) ∧
      ∃ a ∈ A, (∀ b ∈ A, b ≤ a) ∧
      ∃ n m : ℕ, (∀ b ∈ A, b ≤ n) ∧ n < m ∧
        n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ A, b ∣ k)).card <
          2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ A, b ∣ k)).card ∧
        2 * m * ((Finset.Icc 1 n).filter
                (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card <
          n * ((Finset.Icc 1 m).filter
                (fun k => a ∣ k ∧ ∀ b ∈ A.erase a, ¬ b ∣ k)).card :=
  ⟨{2, 3, 5, 7}, by decide, by decide, by decide, 7, by decide, by decide, 48, 91,
    by decide, by decide, by decide, by decide⟩

end Submissions.ErdosMultiplesDoublingMaxGenDead.Witness
