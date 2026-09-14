import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.J4P399IndependentDetours
namespace IndependentDetours
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def Compatible {u v : V} (p : G.Walk u v) (eligible : G.Dart → Bool)
    (tip : G.Dart → V) : Prop :=
  (∀ d ∈ p.darts, eligible d = true → G.Adj d.fst (tip d) ∧ G.Adj (tip d) d.snd) ∧
  (∀ d ∈ p.darts, eligible d = true → tip d ∉ p.support) ∧
  (∀ d ∈ p.darts, eligible d = true → ∀ e ∈ p.darts, eligible e = true →
    tip d = tip e → d = e)

def Within {u v x y : V} (p : G.Walk u v) (q : G.Walk x y)
    (eligible : G.Dart → Bool) (tip : G.Dart → V) : Prop :=
  ∀ z ∈ q.support, z ∈ p.support ∨ ∃ d ∈ p.darts, eligible d = true ∧ tip d = z

end IndependentDetours

open SimpleGraph IndependentDetours

abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (u v : V) (p : G.Walk u v),
    p.IsPath → G.Adj v u → 1 < p.length →
    ∀ (eligible : G.Dart → Bool) (tip : G.Dart → V),
    Compatible p eligible tip → ∀ k : Nat,
    k ≤ (p.darts.filter eligible).length →
    ∃ c : G.Walk v v, c.IsCycle ∧ c.length = p.length + 1 + k ∧
      Within p c eligible tip

end Statements.J4P399IndependentDetours
