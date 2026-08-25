import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.ENat

namespace Statements.Erdos889NewPrimeFactorsUnbounded

open Filter Topology

def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter fun p ↦
    ∀ i ∈ Finset.range k, ¬p ∣ n + i).card

noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)

/-- Erdős Problem 889: the maximum number of prime factors first appearing at
one member of a consecutive-integer prefix tends to infinity. -/
abbrev statement : Prop :=
  Tendsto v₀ atTop (𝓝 ⊤)

theorem target : statement := sorry

end Statements.Erdos889NewPrimeFactorsUnbounded
