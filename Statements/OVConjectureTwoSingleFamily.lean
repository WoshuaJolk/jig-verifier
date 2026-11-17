import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice

/- Source: O'Neill–Verstraëte, A note on k-wise oddtown problems,
   Graphs and Combinatorics 38:101 (2022), Conjecture 2 (arXiv:2011.09402),
   specialised to one family `A_1 = ... = A_k = F`: the single-family k-wise
   variant of the oddtown problem modulo `p`. -/
namespace Statements.OVConjectureTwoSingleFamily

abbrev statement : Prop :=
  ∀ (p k : ℕ), p.Prime → 2 ≤ k →
    ∀ n m : ℕ, 1 ≤ n →
      ∀ F : Fin m → Finset (Fin n),
        (∀ idx : Fin k → Fin m,
          (((Finset.univ.inf (fun j : Fin k => F (idx j))).card : ℕ) : ZMod p) ≠ 0 ↔
            Function.Injective idx) →
        m ^ (k / 2) ≤ (2 * (k / 2) * p) ^ (k / 2) * n ^ (p - 1)

theorem target : statement := sorry

end Statements.OVConjectureTwoSingleFamily
