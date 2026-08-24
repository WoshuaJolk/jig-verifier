import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# MixedMinUPBAtMostTrivialPlusOne

Corrected scope of the P14 root. The original root excluded bipartite systems
with a qubit factor but accidentally retained the separately classified
all-qubit systems. Johnston's theorem gives `f(8 qubits)=11`, while the old
root demanded at most `10`.

This replacement asks the Chen–Johnston outlook question only in the genuinely
mixed-dimensional region: neither bipartite-with-a-qubit nor all-qubit.
-/

namespace Statements.MixedMinUPBAtMostTrivialPlusOne

abbrev statement : Prop :=
  ∀ p : ℕ, 2 ≤ p → ∀ d : Fin p → ℕ, (∀ j, 2 ≤ d j) →
    ¬ (p = 2 ∧ ∃ j, d j = 2) →
    ¬ (∀ j, d j = 2) →
    ∃ m : ℕ, m ≤ 2 + ∑ j, (d j - 1) ∧
      ∃ v : Fin m → (j : Fin p) → Fin (d j) → ℂ,
        (∀ i j, v i j ≠ 0) ∧
        (∀ i i', i ≠ i' →
          ∃ j, (∑ r, star (v i j r) * v i' j r) = 0) ∧
        (∀ a : (j : Fin p) → Fin (d j) → ℂ,
          (∀ j, a j ≠ 0) →
          ∃ i, ∀ j, (∑ r, star (v i j r) * a j r) ≠ 0)

theorem target : statement := sorry

end Statements.MixedMinUPBAtMostTrivialPlusOne
