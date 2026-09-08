import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic

namespace Statements.Erdos743Stars

def IsPacking {n : ℕ}
    (T : (i : Fin (n - 1)) → SimpleGraph (Fin (i.val + 2)))
    (f : (i : Fin (n - 1)) → Fin (i.val + 2) ↪ Fin n) : Prop :=
  ∀ u v : Fin n, u ≠ v →
    ∃! i : Fin (n - 1),
      ∃ a b : Fin (i.val + 2), (T i).Adj a b ∧
        ((f i a = u ∧ f i b = v) ∨ (f i a = v ∧ f i b = u))

abbrev statement : Prop := ∀ n : ℕ, 2 ≤ n →
    ∀ T : (i : Fin (n - 1)) → SimpleGraph (Fin (i.val + 2)),
      (∀ i, ∃ c, T i = SimpleGraph.starGraph c) →
      ∃ f : (i : Fin (n - 1)) → Fin (i.val + 2) ↪ Fin n, IsPacking T f

theorem target : statement := by sorry

end Statements.Erdos743Stars
