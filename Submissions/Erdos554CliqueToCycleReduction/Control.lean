import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Submissions.Erdos554CliqueToCycleReduction.Control

def MonochromaticCopy {v : ℕ} (H : SimpleGraph (Fin v))
    (k m : ℕ) (color : Fin m → Fin m → Fin k) : Prop :=
  ∃ f : Fin v ↪ Fin m, ∃ c : Fin k,
    ∀ ⦃i j⦄, H.Adj i j → color (f i) (f j) = c

def RamseyProperty {v : ℕ} (H : SimpleGraph (Fin v)) (k m : ℕ) : Prop :=
  ∀ color : Fin m → Fin m → Fin k,
    (∀ i j, color i j = color j i) →
      MonochromaticCopy H k m color

def cycle (length : ℕ) : SimpleGraph (Fin length) :=
  SimpleGraph.fromRel fun i j =>
    (i.val + 1) % length = j.val ∨ (j.val + 1) % length = i.val

abbrev claimedStatement : Prop :=
  ∀ length k m : ℕ,
    RamseyProperty (⊤ : SimpleGraph (Fin length)) k m →
      RamseyProperty (cycle length) k m

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos554CliqueToCycleReduction.Control
