import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Exact rooted codegree-to-C4 identity

Fix distinct vertices `u` and `v`.  A labelled copy of `C₄` that maps the
opposite vertices `0` and `2` to `u` and `v` is uniquely determined by an
ordered pair of distinct common neighbors of `u` and `v`.  Hence the number
of such rooted labelled copies is exactly `d(u,v) * (d(u,v) - 1)`.
-/

open SimpleGraph

namespace Statements.Erdos60RootedCodegreeIdentity

abbrev RootedC4Copies {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :=
  {f : (cycleGraph 4).Copy G //
    f (0 : Fin 4) = u ∧ f (2 : Fin 4) = v}

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n), u ≠ v →
    Nat.card (RootedC4Copies G u v) =
      (G.commonNeighbors u v).ncard *
        ((G.commonNeighbors u v).ncard - 1)

theorem target : statement := sorry

end Statements.Erdos60RootedCodegreeIdentity
