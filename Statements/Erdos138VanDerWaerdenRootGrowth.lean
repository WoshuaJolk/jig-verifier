import Mathlib.Algebra.Module.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos138VanDerWaerdenRootGrowth

open Filter

/-- Exact finite arithmetic-progression vocabulary inlined from
`formal-conjectures`. -/
def IsAPOfLengthWith (s : Set ℕ) (l : ℕ∞) (a d : ℕ) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def IsAPOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
  ∃ a d : ℕ, IsAPOfLengthWith s l a d

def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set ℕ}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, IsAPOfLength ((·.1) '' ap) k ∧
    ∀ m ∈ ap, coloring m = c

def monoAPGuaranteeSet (r k : ℕ) : Set ℕ :=
  {N | ∀ coloring : Finset.Icc 1 N → Fin r,
    ContainsMonoAPofLength coloring k}

noncomputable def monoAPNumber (r k : ℕ) : ℕ :=
  sInf (monoAPGuaranteeSet r k)

noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

/-- Erdős problem 138: two-color van der Waerden numbers grow faster than
every fixed exponential. -/
abbrev statement : Prop :=
  Tendsto (fun k : ℕ => (W k : ℝ) ^ (1 / (k : ℝ))) atTop atTop

theorem target : statement := sorry

end Statements.Erdos138VanDerWaerdenRootGrowth
