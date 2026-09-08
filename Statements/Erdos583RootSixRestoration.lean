import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Multiset.AddSub

namespace Statements.Erdos583RootSixRestoration

universe u

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V,
    p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b →
    ∃! p : List V, p ∈ paths ∧ PathUses p a b

def edgeBag {V : Type u} (p : List V) : Multiset (Sym2 V) :=
  List.rec (motive := fun _ => Multiset (Sym2 V)) 0
    (fun a tail acc => List.casesOn tail 0 (fun b _ => {s(a, b)} + acc)) p

def totalBag {V : Type} (ps : List (List V)) : Multiset (Sym2 V) :=
  ps.foldr (fun p acc => edgeBag p + acc) 0

def restoredEdges {V : Type} (rest : List (List V))
    (a h b c d e f t : V) (p q r : List V) : Multiset (Sym2 V) :=
  totalBag rest + (edgeBag ((b :: p) ++ [c]) + edgeBag ((d :: q) ++ [e]) +
    edgeBag ((f :: r) ++ [t]) + {s(a, h)} +
    {s(a, b)} + {s(a, c)} + {s(a, d)} + {s(a, e)} + {s(a, f)})

abbrev statement : Prop :=
  ∀ {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (rest : List (List V))
    (a h b c d e f t : V) (p q r : List V)
    (roles : ([a, h, b, c, d, e, f, t] : List V).Nodup)
    (hp : ((b :: p) ++ [c]).Nodup)
    (hq : ((d :: q) ++ [e]).Nodup)
    (ht : ((f :: r) ++ [t]).Nodup)
    (haP : a ∉ (b :: p) ++ [c])
    (haQ : a ∉ (d :: q) ++ [e])
    (haT : a ∉ (f :: r) ++ [t])
    (hrest : ∀ path ∈ rest, path.Nodup)
    (hedges : (restoredEdges rest a h b c d e f t p q r).Nodup)
    (hgraph : ∀ x y, s(x, y) ∈ restoredEdges rest a h b c d e f t p q r ↔ G.Adj x y),
    ∃ paths : Finset (List V), paths.card ≤ rest.length + 4 ∧
      IsPathDecomposition G paths

theorem target : statement := sorry

end Statements.Erdos583RootSixRestoration
