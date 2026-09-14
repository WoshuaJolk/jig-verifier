import Init

namespace Statements.J4P26BilinearClosure

def inA (x : Nat) : Bool := [0,1,3,4,6,7,8,11,13,14].contains x

def relation (x d : Fin 31) : Prop :=
  d.val ≠ 0 ∧ inA x.val = true ∧ inA ((x.val+d.val)%31) = true ∧
    inA ((x.val+2*d.val)%31) = true

def horizontal (j : Nat) : Prop := j=0 ∨ j=1 ∨ j=3 ∨ j=6

instance (j : Nat) : Decidable (horizontal j) :=
  inferInstanceAs (Decidable (j=0 ∨ j=1 ∨ j=3 ∨ j=6))

def sub31 (a b : Fin 31) : Fin 31 :=
  ⟨(a.val+31-b.val)%31, Nat.mod_lt _ (by decide)⟩

def HD (R : Fin 31 → Fin 31 → Prop) (x d : Fin 31) : Prop :=
  ∃ u : Fin 31, R u d ∧ R (sub31 u x) d

def VD (R : Fin 31 → Fin 31 → Prop) (x d : Fin 31) : Prop :=
  ∃ u : Fin 31, R x u ∧ R x (sub31 u d)

def stage : Nat → Fin 31 → Fin 31 → Prop
  | 0 => relation
  | n+1 => if horizontal n then HD (stage n) else VD (stage n)


def statement : Prop :=
(∀ x d : Fin 31, stage 7 x d) ∧
(∀ x d : Fin 31, d.val ≠ 0 →
    ¬(inA x.val = true ∧ inA ((x.val+d.val)%31) = true ∧
      inA ((x.val+2*d.val)%31) = true ∧ inA ((x.val+3*d.val)%31) = true))

end Statements.J4P26BilinearClosure
