import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Lattice.Nat

namespace Submissions.Erdos117ColorPredicateNumberBridge.Kernel

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

theorem cosetsNoncommute_irrefl
    (G : Type) [Group G] (q : CentralCoset G) :
    ¬ CosetsNoncommute G q q := by
  rintro ⟨x, y, hxq, hyq, hxy⟩
  have hxyCoset : centralCosetMk G x = centralCosetMk G y :=
    hxq.trans hyq.symm
  obtain ⟨z, hzCenter, hxz⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := Subgroup.center G)).mp hxyCoset
  have hxzCommute : Commute x z := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp hzCenter x
  have h : Commute x (x * z) :=
    (Commute.refl x).mul_right hxzCommute
  rw [hxz] at h
  exact hxy h

theorem strongColorCover_iff_weakIndependentCover
    (G : Type) [Group G] [DecidableEq (CentralCoset G)]
    (C : Finset (Finset (CentralCoset G))) :
    StrongColorCover G C ↔
      WeakIndependentCover (CosetsNoncommute G) C := by
  constructor
  · intro h
    exact ⟨h.2, fun S hSC x hx y hy _ ↦ h.1 S hSC x hx y hy⟩
  · intro h
    constructor
    · intro S hSC x hx y hy
      by_cases hxy : x = y
      · subst y
        exact cosetsNoncommute_irrefl G x
      · exact h.2 S hSC x hx y hy hxy
    · exact h.1

/-- The strong color predicate used by the group-cover conversion lemmas and
the distinct-pair independent-cover predicate used by generic graph transport
give the same least cover cardinality for the central-coset relation. -/
theorem proof
    (G : Type) [Group G] [DecidableEq (CentralCoset G)] :
    strongColorNumber G = weakColorNumber G := by
  apply congrArg sInf
  ext k
  constructor
  · rintro ⟨C, hcard, hC⟩
    exact ⟨C, hcard, (strongColorCover_iff_weakIndependentCover G C).mp hC⟩
  · rintro ⟨C, hcard, hC⟩
    exact ⟨C, hcard, (strongColorCover_iff_weakIndependentCover G C).mpr hC⟩

end Submissions.Erdos117ColorPredicateNumberBridge.Kernel
