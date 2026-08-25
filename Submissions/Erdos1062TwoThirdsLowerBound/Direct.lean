import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Submissions.Erdos1062TwoThirdsLowerBound.Direct

def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

noncomputable def extremal (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest
    (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

theorem proof :
    ∀ n : ℕ, ⌈(2 * n / 3 : ℝ)⌉₊ ≤ extremal n := by
  intro n
  classical
  set b : ℕ := n / 3 with hb
  let A : Finset ℕ := .Icc (b + 1) n
  calc
    ⌈(2 * n / 3 : ℝ)⌉₊
        ≤ n - b := by
      grw [Nat.ceil_le, Nat.cast_sub (by omega), le_sub_iff_add_le,
        hb, Nat.cast_div_le]
      apply le_of_eq
      ring
    _ ≤ extremal n := Nat.le_findGreatest (by omega)
      ⟨A, by
        simp only [Finset.coe_Icc, A]
        gcongr
        omega, ?_, by
          simp [A, -Finset.coe_Icc]⟩
  simp only [ForkFree, Finset.coe_Icc, Set.mem_Icc, Set.mem_sdiff,
    Set.mem_singleton_iff, and_assoc, and_imp, A]
  rintro a ha -
  refine Set.subsingleton_of_forall_eq (a * 2) ?_
  simp only [Set.mem_ofPred_eq, and_imp]
  rintro _ _ hk _ ⟨k, rfl⟩
  match k with
  | 0 | 1 | 2 => simp_all
  | k + 3 =>
      grw [← le_add_self] at hk
      omega

end Submissions.Erdos1062TwoThirdsLowerBound.Direct
