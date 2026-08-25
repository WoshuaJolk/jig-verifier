import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68FiniteScaledResidueFormula.FiniteScaledResidueFormula

private lemma denominator_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < n.factorial - 1 := by
  have : 1 < n.factorial := Nat.one_lt_factorial.mpr (by omega)
  omega

private lemma div_mod_decomposition (M D : ℕ) (hD : 0 < D) :
    (M : ℝ) / D =
      (M / D : ℕ) + (M % D : ℕ) / (D : ℝ) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  field_simp [hDR]
  exact_mod_cast (Nat.div_add_mod M D).symm

/-- Scaling the finite sum by `m!` splits it into an explicit integer quotient
sum and a finite sum of normalized modular residues. Consequently its floor is
the quotient sum plus the floor of the residue sum; the newest residue is 1. -/
theorem proof :
    ∀ m : ℕ, 3 ≤ m →
      let A : ℕ :=
        ∑ n ∈ Finset.Icc 2 m,
          m.factorial / (n.factorial - 1)
      let R : ℝ :=
        ∑ n ∈ Finset.Icc 2 m,
          (m.factorial % (n.factorial - 1) : ℕ) /
            ((n.factorial - 1 : ℕ) : ℝ)
      (m.factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 m,
            (1 : ℝ) / (n.factorial - 1 : ℕ) =
        A + R ∧
      ⌊(m.factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 m,
            (1 : ℝ) / (n.factorial - 1 : ℕ)⌋ =
        (A : ℤ) + ⌊R⌋ ∧
      m.factorial % (m.factorial - 1) = 1 := by
  intro m hm
  dsimp
  have heq :
      (m.factorial : ℝ) *
          ∑ n ∈ Finset.Icc 2 m,
            (1 : ℝ) / (n.factorial - 1 : ℕ) =
        (∑ n ∈ Finset.Icc 2 m,
          m.factorial / (n.factorial - 1) : ℕ) +
        ∑ n ∈ Finset.Icc 2 m,
          (m.factorial % (n.factorial - 1) : ℕ) /
            ((n.factorial - 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    calc
      (m.factorial : ℝ) *
          ((1 : ℝ) / (n.factorial - 1 : ℕ)) =
          (m.factorial : ℝ) / (n.factorial - 1 : ℕ) := by ring
      _ = (m.factorial / (n.factorial - 1) : ℕ) +
          (m.factorial % (n.factorial - 1) : ℕ) /
            ((n.factorial - 1 : ℕ) : ℝ) :=
        div_mod_decomposition _ _ (denominator_pos hn2)
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    rw [Int.floor_natCast_add]
  · have hfac : 1 < m.factorial :=
      Nat.one_lt_factorial.mpr (by omega)
    have hden : 1 < m.factorial - 1 := by
      have hmono := Nat.factorial_le hm
      norm_num at hmono
      omega
    conv_lhs =>
      rw [show m.factorial = (m.factorial - 1) + 1 by omega]
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hden]

end Submissions.Erdos68FiniteScaledResidueFormula.FiniteScaledResidueFormula
