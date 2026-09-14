import Init

namespace Statements.J4P41WeakSidonGeometry


namespace P41QuadrilateralTransfer

def WeakSidon (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a≠b → c≠d →
    a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

end P41QuadrilateralTransfer


namespace P41WeakSingerRepair

def WeakSidon (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a≠b → c≠d →
    a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

end P41WeakSingerRepair

abbrev statement : Prop :=
  (∀ (A : Int → Prop) (hw : P41QuadrilateralTransfer.WeakSidon A)
    (x w y z : Int) (hxw : x≠w) (hyz : y≠z)
    (h1 : A (y-x)) (h2 : A (z-x)) (h3 : A (y-w)) (h4 : A (z-w)),
    (y-x=z-w ∧ (z-x)+(y-w)=2*(y-x) ∧ z-x≠y-w) ∨
    (z-x=y-w ∧ (y-x)+(z-w)=2*(z-x) ∧ y-x≠z-w)) ∧
  (∀ (a b c x t : Int)
    (hab : a<b) (hbc : b<c) (he : a+c=2*b)
    (h : (x=t ∧ x+c=t+b) ∨ (x=t ∧ x+c=t+c) ∨
         (x=t+(b-a) ∧ x+c=t+b) ∨ (x=t+(b-a) ∧ x+c=t+c)),
    x=t) ∧
  (∀ (N d fa fb fc : Int)
    (hshort : 2*d≤N) (hcover : N-d≤fa+2*fb+fc),
    N≤8*fa ∨ N≤8*fb ∨ N≤8*fc) ∧
  (∀ (A : Int → Prop) (hw : P41WeakSingerRepair.WeakSidon A)
    (p q V : Int) (hpq : p<q) (hq : q<p+V)
    (h1 : A p) (h2 : A (p+V)) (h3 : A q) (h4 : A (q+V)),
    False) ∧
  (∀ (k E T U J r j : Int)
    (hcount : k-24*E-12 ≤ 5*T)
    (hsplit : T=2*U+J) (hdoubled : J≤j) (hcover : U≤2*r),
    k-24*E-12-5*j ≤ 20*r)

theorem target : statement := sorry

end Statements.J4P41WeakSidonGeometry
