import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Matrix.ColumnRowPartitioned

/- Source: O'Neill–Verstraëte, A note on k-wise oddtown problems,
   Graphs and Combinatorics 38:101 (2022), Conjecture 2 (arXiv:2011.09402).

   Families `A j = {A j i : i < m}` of subsets of an `n`-element set, for
   `j < k`. Hypothesis: for every choice of one index per family, the size of
   the `k`-wise intersection is ZERO modulo `p` exactly when the chosen
   indices are all distinct. This is the complementary reading of the
   conjecture's hypothesis, matching the convention of the paper's Theorem 2. Conclusion `m = O(n ^ ((p - 1) / ⌊k / 2⌋))`,
   written without real exponents as `m ^ ⌊k / 2⌋ ≤ C * n ^ (p - 1)` with a
   constant `C` depending only on `p` and `k`, for every `n ≥ 1`. -/
namespace Statements.OVConjectureTwoZeroReading

abbrev statement : Prop :=
  ∀ (p k : ℕ), p.Prime → 2 ≤ k →
    ∃ C : ℕ, ∀ n m : ℕ, 1 ≤ n →
      ∀ A : Fin k → Fin m → Finset (Fin n),
        (∀ idx : Fin k → Fin m,
          (((Finset.univ.inf (fun j : Fin k => A j (idx j))).card : ℕ) : ZMod p) = 0 ↔
            Function.Injective idx) →
        m ^ (k / 2) ≤ C * n ^ (p - 1)

theorem target : statement := sorry

end Statements.OVConjectureTwoZeroReading
