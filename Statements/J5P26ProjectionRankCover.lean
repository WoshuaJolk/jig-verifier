import Init

namespace Statements.J5P26ProjectionRankCover

universe u

def drop {V : Type u} [Zero V] (i row col : Fin 4) (x : V) : V :=
  if row=i ∨ col=i then x else 0

abbrev statement : Prop :=
  (∀ {V : Type u} [Lean.Grind.IntModule V]
    (rho : V -> Nat) (e1 e2 e3 : V -> V) (q : V)
    (s1 : forall x y, e1 (x-y)=e1 x-e1 y)
    (s2 : forall x y, e2 (x-y)=e2 x-e2 y)
    (radd : forall x y, rho (x+y)<=rho x+rho y)
    (rsub : forall x y, rho (x-y)<=rho x+rho y)
    (r1 : forall x, rho (e1 x)<=rho x)
    (r2 : forall x, rho (e2 x)<=rho x)
    (hz : (q-e3 q)-e2 (q-e3 q)-e1 ((q-e3 q)-e2 (q-e3 q))=0)
    (a b c : Nat) (ha : rho (e1 q)<=a) (hb : rho (e2 q)<=b)
    (hc : rho (e3 q)<=c), rho q<=a+2*b+4*c) ∧
  (∀ {V : Type u} [Zero V] (row col : Fin 4) (x : V), drop 1 row col (drop 2 row col (drop 3 row col x))=0)

end Statements.J5P26ProjectionRankCover
