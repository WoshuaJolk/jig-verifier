import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Find

namespace Statements.Erdos667BoundaryBehavior

open SimpleGraph
open scoped Classical

def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p →
    q ≤ (G.induce s).edgeSet.ncard

noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n),
      LocallyDense p q G → ¬G.CliqueFree m) n

/-- The maximum local edge threshold for a given p is Nat.choose (p-1) 2 + 1.
At this maximum threshold, a locally-dense graph must have a clique of size
greater than what the minimum threshold requires, indicating genuine separation. --/
abbrev statement : Prop :=
  ∀ p n : ℕ,
    p ≥ 2 →
    n ≥ 2 →
    H p 1 n < H p (Nat.choose (p - 1) 2 + 1) n

theorem target : statement := sorry

end Statements.Erdos667BoundaryBehavior
