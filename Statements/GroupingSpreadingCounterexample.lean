import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
An exact eight-vertex counterexample to the universal one-factorization assertion
GroupingSpreadingCrossFirst. The following definitions and originalStatement are
copied unchanged from that canonical statement, except for its local name.
No claim is made against the existential grouping statement.
-/
namespace Statements.GroupingSpreadingCounterexample

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The circulant on `ZMod m` with symmetric connection set `S`. -/
def circulant (m : ℕ) (S : Finset (ZMod m)) : SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w => (w - v) ∈ S

/-- Connection set of the connected `k`-regular seed. -/
def degSet (m k : ℕ) : Finset (ZMod m) :=
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (i : ZMod m)) ∪
  (Finset.Icc 1 (k / 2)).image (fun i : ℕ => (-(i : ZMod m))) ∪
  (if k % 2 = 1 then {((m / 2 : ℕ) : ZMod m)} else ∅)

/-- A one-factor as an involution on `ZMod m` with no fixed points (perfect matching). -/
abbrev IsOneFactor {m : ℕ} (F : ZMod m → ZMod m) : Prop :=
  (∀ v, F (F v) = v) ∧ (∀ v, F v ≠ v)

/-- Class complement: the seed together with every factor not assigned to class `j`. -/
def classCompl {m n : ℕ} (k : ℕ) (F : Fin n → ZMod m → ZMod m) (g : Fin n → ℕ) (j : ℕ) :
    SimpleGraph (ZMod m) :=
  SimpleGraph.fromRel fun v w =>
    (circulant m (degSet m k)).Adj v w ∨ ∃ t : Fin n, g t ≠ j ∧ F t v = w

/-- The canonical proposition.

For even `m`, `2 ≤ k`, `2 * k < m`, and class degrees `e j ≥ 1` summing to `m - 1 - k` with no
class taking every factor, every 1-factorization of the seed complement admits an assignment of its
factors to the classes — the cross-first spreading assignment — such that each class complement
stays connected after deleting fewer than `m - 1 - e j` vertices. -/
abbrev originalStatement : Prop :=
  ∀ m k q : ℕ, 2 ≤ k → 2 * k < m → m % 2 = 0 → ∀ e : Fin q → ℕ,
    (∀ j, 1 ≤ e j) →
    (∑ j, e j) + 1 + k = m →
    (∀ j, e j + 1 < m - k) →
    ∀ n : ℕ, n = m - 1 - k →
    ∀ F : Fin n → ZMod m → ZMod m,
      (∀ t, IsOneFactor (F t)) →
      (∀ t v, ¬ (circulant m (degSet m k)).Adj v (F t v)) →
      (∀ v w, v ≠ w → ¬ (circulant m (degSet m k)).Adj v w → ∃! t, F t v = w) →
      ∃ g : Fin n → ℕ,
        (∀ j : Fin q, (Finset.univ.filter fun t => g t = (j : ℕ)).card = e j) ∧
        (∀ j : Fin q, ∀ X : Finset (ZMod m),
          X.card + 1 + e j < m →
          ((classCompl k F g (j : ℕ)).induce {v : ZMod m | v ∉ X}).Connected)


abbrev statement : Prop := ¬ originalStatement

theorem target : statement := sorry

end Statements.GroupingSpreadingCounterexample
