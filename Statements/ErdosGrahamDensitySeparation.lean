import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.RealVectorSpace

open Filter Finset
open scoped Topology

namespace Statements.ErdosGrahamDensitySeparation

noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (fun x => x ∈ A)).card

noncomputable def density (A : Set ℕ) (N : ℕ) : ℝ := count A N / (N : ℝ)

def tripleFree (A : Set ℕ) : Prop :=
  ∀ x : ℕ, 0 < x → ¬(x ∈ A ∧ 2*x ∈ A ∧ 3*x ∈ A)

def positive (A : Set ℕ) : Prop := ∀ x ∈ A, 0 < x

abbrev statement : Prop :=
  ∃ B : Set ℕ, positive B ∧ B.Infinite ∧ tripleFree B ∧
    ∀ (A : Set ℕ) (d : ℝ), positive A → tripleFree A →
      Tendsto (density A) atTop (nhds d) →
      d < limsup (density B) atTop

end Statements.ErdosGrahamDensitySeparation
