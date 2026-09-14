import Init

namespace Statements.J5P26CornerTransfer

abbrev member31 (n : Nat) : Bool :=
  n%31 == 4 || n%31 == 5 || n%31 == 8 || n%31 == 9 || n%31 == 10

abbrev lift31 (x y : Nat) : Bool :=
  member31 (x+y) && member31 (x+2*y)

abbrev midpoint31 (x y : Nat) : Nat :=
  if member31 (21*(2*x+y)) && member31 (21*(x+2*y)) then 1 else 0

abbrev statement : Prop :=
  (∀ (x d a b c : Int)
    (h0 : x=a ∨ x=b ∨ x=c)
    (h1 : x+d=a ∨ x+d=b ∨ x+d=c)
    (h2 : x+2*d=a ∨ x+2*d=b ∨ x+2*d=c)
    (h3 : x+3*d=a ∨ x+3*d=b ∨ x+3*d=c), d=0) ∧
  (∀ (a b c x y d : Int) (hd : d ≠ 0)
    (h0 : a*x+b*y+c=0)
    (h1 : a*(x+d)+b*y+c=0)
    (h2 : a*x+b*(y+d)+c=0), a=0 ∧ b=0) ∧
  (∀ (a b : Int)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    (hz : a=0 ∨ b=0), a+b-2 < 0) ∧
  ((∀ a d : Fin 31, d.val ≠ 0 →
      ¬(member31 a.val=true ∧ member31 (a.val+d.val)=true ∧
        member31 (a.val+2*d.val)=true ∧ member31 (a.val+3*d.val)=true)) ∧
    lift31 0 4=true ∧ lift31 1 4=true ∧ lift31 0 5=true ∧
    ((List.range 31).flatMap (fun x => (List.range 31).filter (fun y => lift31 x y))).length=25 ∧
    midpoint31 3 3=0 ∧ midpoint31 6 6=0 ∧
    midpoint31 3 6=1 ∧ midpoint31 6 3=1)

end Statements.J5P26CornerTransfer
