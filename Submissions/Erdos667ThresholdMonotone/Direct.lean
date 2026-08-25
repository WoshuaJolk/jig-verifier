import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Card

namespace Submissions.Erdos667ThresholdMonotone.Direct

open SimpleGraph
open scoped Classical

def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p →
    q ≤ (G.induce s).edgeSet.ncard

noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n),
      LocallyDense p q G → ¬G.CliqueFree m) n

theorem proof :
    ∀ p q r n : ℕ, q ≤ r → H p q n ≤ H p r n := by
  classical
  intro p q r n hqr
  apply Nat.findGreatest_mono_left _ n
  intro m hm G hr
  apply hm G
  intro s hs
  exact hqr.trans (hr s hs)

end Submissions.Erdos667ThresholdMonotone.Direct
