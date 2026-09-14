import Init

namespace Statements.J5P26SumsetPlateau

def good7 (x : Nat) : Prop := x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4

instance (x : Nat) : Decidable (good7 x) := inferInstanceAs (Decidable (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4))

def digit7 (x : Nat) : Prop := good7 (x % 7)

def digits7 : Nat → Nat → Prop :=
  Nat.rec (motive := fun _ => Nat → Prop)
    (fun _ => True)
    (fun _ ih a => digit7 a ∧ ih (a / 7))

def digitList : List Nat := [0,1,2,4]

def sumList : List Nat := digitList.flatMap fun a => digitList.map fun b => (a+b)%7

def convolution7 (t : Nat) : Nat :=
  ((digitList.flatMap fun a => digitList.map fun b => (a+b+7-t)%7).filter
    fun z => sumList.contains z).length

abbrev statement : Prop :=
  (∀ (a d : Fin 7),
    good7 a.val → good7 ((a.val+d.val)%7) →
    good7 ((a.val+2*d.val)%7) → good7 ((a.val+3*d.val)%7) → d.val = 0) ∧
  (∀ t : Fin 7, ∃ a b : Fin 7,
    good7 a.val ∧ good7 b.val ∧ (a.val+b.val)%7 = t.val) ∧
  (∀ (n a d : Nat), digits7 n a → digits7 n (a+d) → digits7 n (a+2*d) → digits7 n (a+3*d) → 7^n ∣ d) ∧
  (∀ t : Fin 7, convolution7 t.val = 16)

end Statements.J5P26SumsetPlateau
