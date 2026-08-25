import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter
open scoped Topology

namespace Nat

def maxPrimeFac (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactorsList.getLastI

end Nat

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β]
    [LocallyFiniteOrderBot β] (S : Set β) (A : Set β := Set.univ)
    (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun b : β => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Statements.Erdos371LargestPrimeFactorDensity

/-- Erdős Problem 371: the largest prime factor rises from `n` to `n+1`
with asymptotic density one half. -/
abbrev statement : Prop :=
  {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2)

theorem target : statement := sorry

end Statements.Erdos371LargestPrimeFactorDensity
