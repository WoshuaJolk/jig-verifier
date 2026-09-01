import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
Expected-RED control: a restatement attack. The theorem below adds the hypothesis `a = 1`,
under which both cardinalities are just `m` and `n` and the claim is `n * m < 2 * m * n`.
It is true and compiles; it is not the statement asked for.
-/

namespace Submissions.ErdosMultiplesDoublingSingleton.MalloryWeakened

theorem proof : ∀ a : ℕ, 0 < a → a = 1 → ∀ n m : ℕ, a ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card := by
  intro a ha h1 n m han hnm
  subst h1
  have hm : ((Finset.Icc 1 m).filter (fun k => ∃ b ∈ ({1} : Finset ℕ), b ∣ k)) = Finset.Icc 1 m := by
    ext k; simp
  have hn : ((Finset.Icc 1 n).filter (fun k => ∃ b ∈ ({1} : Finset ℕ), b ∣ k)) = Finset.Icc 1 n := by
    ext k; simp
  rw [hm, hn, Nat.card_Icc, Nat.card_Icc]
  have hn0 : 0 < n := han
  have : n * (m + 1 - 1) = n * m := by simp
  rw [this]
  have : 2 * m * (n + 1 - 1) = 2 * m * n := by simp
  rw [this]
  calc n * m = m * n := Nat.mul_comm n m
    _ < 2 * m * n := by
        have : 0 < m * n := Nat.mul_pos (lt_trans hn0 hnm) hn0
        linarith [this]

end Submissions.ErdosMultiplesDoublingSingleton.MalloryWeakened
