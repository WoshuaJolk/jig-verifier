import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace Statements.Erdos20ExponentialShiftObstruction

abbrev Word (k : ℕ) := Fin k → Bool

abbrev Vertex (k : ℕ) := (Fin k × Bool) ⊕ Word k

def edge {k : ℕ} (collapsed : Finset (Fin k)) (w : Word k) : Finset (Vertex k) :=
  (Finset.univ.image fun i : Fin k => Sum.inl (i, if i ∈ collapsed then false else w i)) ∪
    {Sum.inr w}

def family (k : ℕ) (collapsed : Finset (Fin k)) : Finset (Finset (Vertex k)) :=
  Finset.univ.image (edge collapsed)

def shiftMember {k : ℕ} (i : Fin k) (F : Finset (Finset (Vertex k)))
    (A : Finset (Vertex k)) : Finset (Vertex k) :=
  if Sum.inl (i,false) ∉ A ∧ Sum.inl (i,true) ∈ A ∧
      insert (Sum.inl (i,false)) (A.erase (Sum.inl (i,true))) ∉ F then
    insert (Sum.inl (i,false)) (A.erase (Sum.inl (i,true)))
  else A

def shift {k : ℕ} (i : Fin k) (F : Finset (Finset (Vertex k))) :
    Finset (Finset (Vertex k)) := F.image (shiftMember i F)

def performShifts {k : ℕ} (L : List (Fin k)) (F : Finset (Finset (Vertex k))) :
    Finset (Finset (Vertex k)) := L.foldr shift F

def IsSunflower {k : ℕ} (F : Finset (Finset (Vertex k))) : Prop :=
  ∃ K : Finset (Vertex k), ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ∩ B = K

def core (k : ℕ) : Finset (Vertex k) :=
  Finset.univ.image (fun i : Fin k => Sum.inl (i,false))

abbrev statement : Prop :=
  ∀ k : ℕ,
    (family k ∅).card = 2 ^ k ∧
    (∀ A ∈ family k ∅, A.card = k + 1) ∧
    (∀ G ⊆ family k ∅, 3 ≤ G.card → ¬ IsSunflower G) ∧
    (List.finRange k).length = k ∧
    (performShifts (List.finRange k) (family k ∅)).card = 2 ^ k ∧
    IsSunflower (performShifts (List.finRange k) (family k ∅))

theorem target : statement := sorry

end Statements.Erdos20ExponentialShiftObstruction
