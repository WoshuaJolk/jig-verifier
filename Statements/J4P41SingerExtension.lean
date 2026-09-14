import Init

namespace Statements.J4P41SingerExtension


namespace P41SingerExtension

def Sidon {G : Type} (op : G → G → G) (D : G → Prop) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → op a b = op c d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

def WeakSidon {G : Type} (op : G → G → G) (D : G → Prop) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → a≠b → c≠d →
    op a b = op c d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

end P41SingerExtension

abbrev statement : Prop :=
  (∀ {G : Type} (op : G → G → G) (D : G → Prop) (z : G)
    (hz : ∀ x, op z x=x) (hs : P41SingerExtension.Sidon op D)
    (hd : ∀ x, D x → D (op x x))
    (a : G) (ha : D a) (hne : a≠z),
    ¬D z) ∧
  (∀ {G : Type} (op : G → G → G) (D : G → Prop)
    (hs : P41SingerExtension.Sidon op D) (hd : ∀ x, D x → ∃ w, D w ∧ op w w=x)
    (a b : G) (ha : D a) (hb : D b) (hne : a≠b),
    ¬D (op a b)) ∧
  (∀ {G : Type} (op : G → G → G) (D : G → Prop) (z : G)
    (hl : ∀ x, op z x=x) (hr : ∀ x, op x z=x)
    (hs : P41SingerExtension.Sidon op D) (hd : ∀ x, D x → ∃ w, D w ∧ op w w=x),
    P41SingerExtension.WeakSidon op (fun x => D x ∨ x=z)) ∧
  (∀ (D : Int → Prop) (z : Int)
    (hs : P41SingerExtension.Sidon (fun a b : Int => a+b) D)
    (a b c : Int) (ha : D a ∨ a=z) (hb : D b ∨ b=z)
    (hc : D c ∨ c=z) (hab : a<b) (he : a+c=2*b),
    a=z ∨ b=z ∨ c=z)

theorem target : statement := sorry

end Statements.J4P41SingerExtension
