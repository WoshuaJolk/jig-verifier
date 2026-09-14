import Init

namespace Statements.J5P41OrderCrossings

def mark : Nat → Int
  | 0 => 0 | 1 => 14 | 2 => 23 | 3 => 51 | 4 => 68 | 5 => 69
  | 6 => 72 | 7 => 84 | 8 => 94 | 9 => 125 | 10 => 132
  | 11 => 159 | 12 => 161 | 13 => 167 | 14 => 172 | 15 => 191
  | 16 => 211 | _ => 0

def curve (i r : Nat) : Int := mark (i + r) - mark i

abbrev statement : Prop :=
  (∀ i j l n : Fin 17,
    mark i.val + mark j.val = mark l.val + mark n.val →
    ((i = l ∧ j = n) ∨ (i = n ∧ j = l))) ∧
  ((∀ i j : Fin 17, i < j → mark i.val < mark j.val) ∧
    (∀ i : Fin 17, 0 ≤ mark i.val ∧ mark i.val < 212) ∧
    (212 : Nat) ≤ 17 * 17) ∧
  (∀ r : Fin 15,
    r.val ∈ ([1, 3, 7, 8, 9, 10, 13] : List Nat) →
    (curve 1 r.val - curve 0 r.val) *
      (curve 1 (r.val + 1) - curve 0 (r.val + 1)) < 0)

end Statements.J5P41OrderCrossings
