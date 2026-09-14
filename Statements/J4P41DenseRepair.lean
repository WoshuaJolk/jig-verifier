import Init

namespace Statements.J4P41DenseRepair


namespace P41DenseDefects

def WeakSidon (S : Int → Prop) : Prop :=
  ∀ a b c d, S a → S b → S c → S d → a<b → c<d →
    a+b=c+d → a=c ∧ b=d

def NoAP (S : Int → Prop) : Prop :=
  ∀ a b c, S a → S b → S c → a<b → b<c → a+c≠2*b

end P41DenseDefects

abbrev statement : Prop :=
  (∀ (T : Nat → Prop) (x : Nat → Int)
    (rho : Nat → Nat → Int) (anchor : Nat)
    (pos : ∀ i j, T i → T j → i<j → 0<rho i j)
    (unique : ∀ i j l m, T i → T j → T l → T m → i<j → l<m →
      rho i j=rho l m → i=l ∧ j=m)
    (ha : ∀ i, T i → rho anchor i=x i-x anchor)
    (hc : ∀ i j, T i → T j → i<j →
      rho anchor j-rho anchor i=rho i j)
    (a b c d : Nat) (hta : T a) (htb : T b) (htc : T c) (htd : T d)
    (hsum : x a+x b=x c+x d),
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)) ∧
  (∀ (S : Int → Prop) (hw : P41DenseDefects.WeakSidon S) (hn : P41DenseDefects.NoAP S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hs : a+b=c+d),
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)) ∧
  (∀ (S : Int → Prop) (hw : P41DenseDefects.WeakSidon S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hab : a<b) (hcd : c<d) (hac : a<c) (he : b-a=d-c),
    b=c) ∧
  (∀ (k r sq agree changes edits : Int)
    (hclass : sq≤k*(k-r)) (hagree : 2*agree=sq-k)
    (hcompare : k*(k-1)≤2*(agree+changes+edits)),
    k*r≤2*(changes+edits))

theorem target : statement := sorry

end Statements.J4P41DenseRepair
