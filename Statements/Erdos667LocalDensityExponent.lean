import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.LiminfLimsup

namespace Statements.Erdos667LocalDensityExponent

open SimpleGraph Filter
open scoped Classical

def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p →
    q ≤ (G.induce s).edgeSet.ncard

noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n),
      LocallyDense p q G → ¬G.CliqueFree m) n

noncomputable def c (p q : ℕ) : ℝ :=
  liminf
    (fun n : ℕ => Real.log (H p q n) / Real.log n)
    atTop

/-- Erdős Problem 667: the locally-dense guaranteed-clique exponent is
strictly increasing in q throughout the stated finite interval. -/
abbrev statement : Prop :=
  ∀ p : ℕ,
    StrictMonoOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1))

theorem target : statement := sorry

end Statements.Erdos667LocalDensityExponent
