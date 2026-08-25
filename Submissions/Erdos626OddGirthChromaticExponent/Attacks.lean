import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace Submissions.Erdos626OddGirthChromaticExponent.Attacks

open Filter

def cycle (length : ℕ) : SimpleGraph (Fin length) :=
  SimpleGraph.fromRel fun i j =>
    (i.val + 1) % length = j.val ∨ (j.val + 1) % length = i.val

def ContainsCycleOfLength {V : Type*} (G : SimpleGraph V) (length : ℕ) : Prop :=
  ∃ f : Fin length ↪ V,
    ∀ ⦃i j⦄, (cycle length).Adj i j → G.Adj (f i) (f j)

def HasGirthGreaterThan {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ length : ℕ, 3 ≤ length → length ≤ m → ¬ContainsCycleOfLength G length

noncomputable def chromatic {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | G.Colorable k}

noncomputable def maximalChromatic (m n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : SimpleGraph (Fin n) =>
      if HasGirthGreaterThan G m then chromatic G else 0

abbrev claimedStatement : Prop :=
  ∀ m : ℕ, 3 ≤ m → Odd m →
    Tendsto
      (fun n => Real.log (maximalChromatic m n) / Real.log n)
      atTop (nhds (2 / (m + 1 : ℝ)))

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem oddParameterDomain : ∃ m : ℕ, 3 ≤ m ∧ Odd m := ⟨3, by omega, by decide⟩

end Submissions.Erdos626OddGirthChromaticExponent.Attacks
