import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Statements.Erdos44PerfectDifferenceCoverBarrier

open Set Finset

def PerfectDifferences {α : Type*} [AddCommGroup α] [Fintype α] [DecidableEq α]
    (C : Finset α) : Prop :=
  ((Finset.univ.erase 0).filter fun δ =>
    (((C ×ˢ C).filter fun p => p.1 - p.2 = δ).card = 1)) =
      Finset.univ.erase 0

abbrev Triple (α : Type*) := (α × α) × α

def CollisionTriples {α : Type*} [AddCommGroup α] [DecidableEq α]
    (C : Finset α) (d : α) : Finset (Triple α) :=
  ((C ×ˢ C) ×ˢ C).filter fun p => p.1.1 + p.1.2 - p.2 = d

def Covers {α : Type*} [AddCommGroup α] [DecidableEq α]
    (C : Finset α) (d : α) (X : Finset α) : Prop :=
  (CollisionTriples C d).filter
    (fun p => p.1.1 ∈ X ∨ p.1.2 ∈ X ∨ p.2 ∈ X) =
      CollisionTriples C d

/-- Away from the exceptional offsets lying in a perfect difference set, every
vertex cover of its collision triples has linear size. -/
abbrev statement : Prop :=
  ∀ {α : Type*} [AddCommGroup α] [Fintype α] [LinearOrder α]
    (C : Finset α) (d : α), PerfectDifferences C → d ∉ C →
      ∀ X : Finset α, Covers C d X → C.card ≤ 4 * X.card

theorem target : statement := by
  sorry

end Statements.Erdos44PerfectDifferenceCoverBarrier
