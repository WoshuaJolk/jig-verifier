import Init

namespace Statements.J4P26QuarticTemplates

def det (z i j k : Fin 4) : Int :=
  (z.val : Int)*((j.val : Int)-(i.val : Int))-((k.val : Int)-(i.val : Int))


def statement : Prop :=
(∀ (p : Nat) (hp : 31 ≤ p) (i j : Fin 4),
(i ≠ j ∧ ∃ k : Fin 4, det 2 i j k % (p : Int) = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨ (i=3 ∧ j=2))) ∧
(∀ (p : Nat) (hp : 31 ≤ p) (i j : Fin 4),
(i ≠ j ∧ ∃ k : Fin 4, det 3 i j k % (p : Int) = 0) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2))) ∧
(∀ (p : Nat) (hp : 31 ≤ p) (i j : Fin 4),
(i ≠ j ∧ (∃ k : Fin 4, det 2 i j k % (p : Int) = 0) ∧
      (∃ k : Fin 4, det 3 i j k % (p : Int) = 0)) ↔
    ((i=0 ∧ j=1) ∨ (i=3 ∧ j=2)))

end Statements.J4P26QuarticTemplates
