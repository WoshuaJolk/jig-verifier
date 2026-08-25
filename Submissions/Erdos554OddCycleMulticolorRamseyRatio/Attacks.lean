import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace Submissions.Erdos554OddCycleMulticolorRamseyRatio.Attacks

open Filter

def MonochromaticCopy {v : ℕ} (H : SimpleGraph (Fin v))
    (k m : ℕ) (color : Fin m → Fin m → Fin k) : Prop :=
  ∃ f : Fin v ↪ Fin m, ∃ c : Fin k,
    ∀ ⦃i j⦄, H.Adj i j → color (f i) (f j) = c

def RamseyProperty {v : ℕ} (H : SimpleGraph (Fin v)) (k m : ℕ) : Prop :=
  ∀ color : Fin m → Fin m → Fin k,
    (∀ i j, color i j = color j i) →
      MonochromaticCopy H k m color

noncomputable def ramseyNumber {v : ℕ} (H : SimpleGraph (Fin v)) (k : ℕ) : ℕ :=
  sInf {m : ℕ | RamseyProperty H k m}

def cycle (length : ℕ) : SimpleGraph (Fin length) :=
  SimpleGraph.fromRel fun i j =>
    (i.val + 1) % length = j.val ∨ (j.val + 1) % length = i.val

def triangle : SimpleGraph (Fin 3) := ⊤

abbrev claimedStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    Tendsto
      (fun k => (ramseyNumber (cycle (2 * n + 1)) k : ℝ) /
        ramseyNumber triangle k)
      atTop (nhds 0)

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem parameterDomainNonempty : ∃ n : ℕ, 2 ≤ n := ⟨2, by omega⟩

end Submissions.Erdos554OddCycleMulticolorRamseyRatio.Attacks
