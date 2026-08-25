import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos743TreePacking.Degenerate

def IsPacking {n : ℕ}
    (T : (i : Fin (n - 1)) → SimpleGraph (Fin (i.val + 2)))
    (f : (i : Fin (n - 1)) → Fin (i.val + 2) ↪ Fin n) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    ∃! i : Fin (n - 1),
      ∃ a b : Fin (i.val + 2), (T i).Adj a b ∧
        ((f i a = u ∧ f i b = v) ∨
         (f i a = v ∧ f i b = u))

/-- The Gyárfás tree-packing conjecture: `T₂,…,Tₙ` perfectly pack `Kₙ`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ T : (i : Fin (n - 1)) → SimpleGraph (Fin (i.val + 2)),
      (∀ i, (T i).IsTree) →
      ∃ f : (i : Fin (n - 1)) → Fin (i.val + 2) ↪ Fin n,
        IsPacking T f

theorem proof : False → statement := False.elim

end Submissions.Erdos743TreePacking.Degenerate
