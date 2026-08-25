import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

namespace Submissions.Erdos653LocalSpectrumUpper.Direct

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def localCount (X : Finset Point) (p : Point) : ℕ :=
  (X.image fun x => dist x p).card

theorem proof :
    ∀ X : Finset Point, (X.image (localCount X)).card ≤ X.card := by
  intro X
  exact Finset.card_image_le

end Submissions.Erdos653LocalSpectrumUpper.Direct
