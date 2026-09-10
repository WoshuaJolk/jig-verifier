import Mathlib

namespace Statements.E811BStructuralRestrictions

def Balanced {t : Nat}
    (c : Fin (6*t+1) → Fin (6*t+1) → Fin 6) : Prop :=
  ∀ v k, ((Finset.univ.erase v).filter (fun w => c v w = k)).card = t

def Allowed (a b d : Fin 6) : Prop :=
  ({a,b,d} : Finset (Fin 6)) ∈
    ([{0,1,2},{0,1,3},{0,1,4},{0,2,3},{0,2,5},
      {0,4,5},{1,2,4},{1,2,5},{1,3,5},{2,3,4}] : List (Finset (Fin 6)))

def BSupported {N : Nat} (c : Fin N → Fin N → Fin 6) : Prop :=
  ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
    c x y ≠ c x z → c x y ≠ c y z → c x z ≠ c y z →
    Allowed (c x y) (c x z) (c y z)

/-- At the stated size and degree, a closed set is automatically a component:
two components would each have at least t+1 vertices. -/
def ClosedThree {N : Nat} (c : Fin N → Fin N → Fin 6)
    (H : Finset (Fin N)) : Prop :=
  ∀ x ∈ H, ∀ y, y ∉ H → c x y ≠ 3

def Separator {t : Nat}
    (c : Fin (6*t+1) → Fin (6*t+1) → Fin 6)
    (H : Finset (Fin (6*t+1))) : Prop :=
  ∃ A S D : Finset (Fin (6*t+1)),
    A ∪ S ∪ D = H ∧
    Disjoint A S ∧ Disjoint A D ∧ Disjoint S D ∧
    2 ≤ A.card ∧ A.card ≤ t ∧
    1 ≤ S.card ∧ S.card ≤ t ∧
    2 ≤ D.card ∧ D.card ≤ t ∧
    (∀ x ∈ A, ∀ y ∈ D, c x y ≠ 3)

def CliqueThree {N : Nat} (c : Fin N → Fin N → Fin 6)
    (Y : Finset (Fin N)) : Prop :=
  ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → c x y = 3

abbrev statement : Prop :=
  ∀ t : Nat, 2 ≤ t →
  ∀ c : Fin (6*t+1) → Fin (6*t+1) → Fin 6,
    (∀ x y, c x y = c y x) → Balanced c → BSupported c →
    (∀ H : Finset (Fin (6*t+1)), H.card = 2*t+1 →
      ClosedThree c H → Separator c H) ∧
    (∀ Y : Finset (Fin (6*t+1)), Y.card = t+1 →
      CliqueThree c Y → ∀ x, x ∉ Y →
      ∀ k : Fin 6, k = 0 ∨ k = 4 ∨ k = 5 →
      (Y.filter (fun y => c x y = k)).card < t)

-- Proposed statement only; the written proofs are not formalized.
theorem target : statement := sorry

end Statements.E811BStructuralRestrictions
