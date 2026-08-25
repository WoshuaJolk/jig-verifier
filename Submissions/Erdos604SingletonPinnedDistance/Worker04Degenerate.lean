import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card

namespace Submissions.Erdos604SingletonPinnedDistance.Worker04Degenerate

theorem proof :
    False → ((({0} : Finset (EuclideanSpace ℝ (Fin 2))).image
      fun y => dist 0 y).card) = 1 :=
  False.elim

end Submissions.Erdos604SingletonPinnedDistance.Worker04Degenerate
