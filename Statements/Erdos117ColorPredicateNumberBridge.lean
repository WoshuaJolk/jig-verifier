import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos117ColorPredicateNumberBridge

abbrev CentralCoset (G : Type) [Group G] :=
  G ⧸ Subgroup.center G

def centralCosetMk (G : Type) [Group G] (x : G) : CentralCoset G :=
  QuotientGroup.mk' (Subgroup.center G) x

def CosetsNoncommute (G : Type) [Group G]
    (a b : CentralCoset G) : Prop :=
  ∃ x y : G,
    centralCosetMk G x = a ∧
    centralCosetMk G y = b ∧
    ¬Commute x y

def StrongIndependentColor (G : Type) [Group G]
    (S : Finset (CentralCoset G)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬CosetsNoncommute G a b

def StrongColorCover (G : Type) [Group G]
    (C : Finset (Finset (CentralCoset G))) : Prop :=
  (∀ S ∈ C, StrongIndependentColor G S) ∧
  ∀ q : CentralCoset G, ∃ S ∈ C, q ∈ S

def WeakIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

noncomputable def strongColorNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset (CentralCoset G)),
    C.card = k ∧ StrongColorCover G C}

noncomputable def weakColorNumber (G : Type) [Group G]
    [DecidableEq (CentralCoset G)] : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset (CentralCoset G)),
    C.card = k ∧ WeakIndependentCover (CosetsNoncommute G) C}

/-- The strong color predicate in the group-cover conversions and the
distinct-pair predicate in generic graph transport have the same least
cover cardinality for the central-coset noncommuting relation. -/
abbrev statement : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq (CentralCoset G)],
    strongColorNumber G = weakColorNumber G

theorem target : statement := sorry

end Statements.Erdos117ColorPredicateNumberBridge
