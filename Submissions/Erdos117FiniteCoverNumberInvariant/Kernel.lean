import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Lattice.Nat


open scoped IsMulCommutative

namespace Erdos117Audit.AbelianColorNumber

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

def IndependentColor (G : Type) [Group G]
    (S : Finset (CentralCoset G)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬CosetsNoncommute G a b

def IsColorCover (G : Type) [Group G]
    (C : Finset (Finset (CentralCoset G))) : Prop :=
  (∀ S ∈ C, IndependentColor G S) ∧
  ∀ q : CentralCoset G, ∃ S ∈ C, q ∈ S

def IsAbelianSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

def IsAbelianCover (G : Type) [Group G]
    (A : Finset (Subgroup G)) : Prop :=
  (∀ H ∈ A, IsAbelianSubgroup H) ∧
  ∀ x : G, ∃ H ∈ A, x ∈ H

noncomputable def abelianCoverNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ A : Finset (Subgroup G),
    A.card = k ∧ IsAbelianCover G A}

noncomputable def colorCoverNumber (G : Type) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset (CentralCoset G)),
    C.card = k ∧ IsColorCover G C}

private def subgroupForColor (G : Type) [Group G]
    (S : Finset (CentralCoset G)) : Subgroup G :=
  Subgroup.closure {x : G | centralCosetMk G x ∈ S}

private theorem colorCover_to_abelianCover
    (G : Type) [Group G] (C : Finset (Finset (CentralCoset G)))
    (hC : IsColorCover G C) :
    ∃ A : Finset (Subgroup G),
      IsAbelianCover G A ∧ A.card ≤ C.card := by
  classical
  refine ⟨C.image (subgroupForColor G), ?_, Finset.card_image_le⟩
  constructor
  · intro H hH
    obtain ⟨S, hSC, rfl⟩ := Finset.mem_image.mp hH
    have hcomm :
        ∀ x ∈ {x : G | centralCosetMk G x ∈ S},
          ∀ y ∈ {y : G | centralCosetMk G y ∈ S},
            x * y = y * x := by
      intro x hx y hy
      by_contra hxy
      exact hC.1 S hSC
        (centralCosetMk G x) hx
        (centralCosetMk G y) hy
        ⟨x, y, rfl, rfl, hxy⟩
    letI : IsMulCommutative (subgroupForColor G S) :=
      Subgroup.isMulCommutative_closure hcomm
    intro x hx y hy
    exact congrArg Subtype.val
      (mul_comm
        (⟨x, hx⟩ : subgroupForColor G S)
        (⟨y, hy⟩ : subgroupForColor G S))
  · intro x
    obtain ⟨S, hSC, hxS⟩ := hC.2 (centralCosetMk G x)
    refine ⟨subgroupForColor G S,
      Finset.mem_image.mpr ⟨S, hSC, rfl⟩, ?_⟩
    exact Subgroup.subset_closure hxS

private noncomputable def colorForSubgroup
    (G : Type) [Group G] [Fintype (CentralCoset G)]
    (H : Subgroup G) : Finset (CentralCoset G) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ h : G, h ∈ H ∧ centralCosetMk G h = q

private theorem commute_left_factors_of_commute_products
    {Q : Type} [Group Q] (a₁ a₂ b₁ b₂ : Q)
    (h₁₂ : Commute b₁ a₂) (h₂₁ : Commute b₂ a₁)
    (hbb : Commute b₁ b₂)
    (hprod : Commute (a₁ * b₁) (a₂ * b₂)) :
    Commute a₁ a₂ := by
  rw [commute_iff_eq]
  apply mul_right_cancel (b := b₁ * b₂)
  calc
    (a₁ * a₂) * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
      simpa only [mul_assoc] using
        (congrArg (fun z : Q => a₁ * z * b₂) h₁₂.eq).symm
    _ = (a₂ * b₂) * (a₁ * b₁) := hprod.eq
    _ = (a₂ * a₁) * (b₂ * b₁) := by
      simpa only [mul_assoc] using
        congrArg (fun z : Q => a₂ * z * b₁) h₂₁.eq
    _ = (a₂ * a₁) * (b₁ * b₂) :=
      congrArg (a₂ * a₁ * ·) hbb.eq.symm

private theorem abelianCover_to_colorCover
    (G : Type) [Group G] [Fintype (CentralCoset G)]
    (A : Finset (Subgroup G)) (hA : IsAbelianCover G A) :
    ∃ C : Finset (Finset (CentralCoset G)),
      IsColorCover G C ∧ C.card ≤ A.card := by
  classical
  refine ⟨A.image (colorForSubgroup G), ?_, Finset.card_image_le⟩
  constructor
  · intro S hS
    obtain ⟨H, hHA, rfl⟩ := Finset.mem_image.mp hS
    intro q hq r hr hn
    rw [colorForSubgroup, Finset.mem_filter] at hq hr
    obtain ⟨h, hhH, hhq⟩ := hq.2
    obtain ⟨h', hh'H, hh'r⟩ := hr.2
    obtain ⟨x, y, hxq, hyr, hxy⟩ := hn
    have hxh :
        QuotientGroup.mk' (Subgroup.center G) x =
          QuotientGroup.mk' (Subgroup.center G) h :=
      hxq.trans hhq.symm
    have hyh' :
        QuotientGroup.mk' (Subgroup.center G) y =
          QuotientGroup.mk' (Subgroup.center G) h' :=
      hyr.trans hh'r.symm
    obtain ⟨z, hzCenter, hxz⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center G)).mp hxh
    obtain ⟨w, hwCenter, hyw⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center G)).mp hyh'
    have hprod : Commute (x * z) (y * w) := by
      rw [hxz, hyw]
      exact hA.1 H hHA h hhH h' hh'H
    have hzy : Commute z y := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hzCenter y).symm
    have hwx : Commute w x := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hwCenter x).symm
    have hzw : Commute z w := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp hzCenter w).symm
    exact hxy
      (commute_left_factors_of_commute_products
        x y z w hzy hwx hzw hprod)
  · intro q
    obtain ⟨x, hxq⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center G) q
    obtain ⟨H, hHA, hxH⟩ := hA.2 x
    refine ⟨colorForSubgroup G H,
      Finset.mem_image.mpr ⟨H, hHA, rfl⟩, ?_⟩
    rw [colorForSubgroup, Finset.mem_filter]
    exact ⟨Finset.mem_univ q, x, hxH, hxq⟩

private theorem cosetsNoncommute_irrefl
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

/-- For a finite central quotient, the least abelian-subgroup-cover
cardinality equals the least independent central-coset color-cover
cardinality. This assembles both directions of arXiv:2608.20507v1,
Lemma 2.1 with the minima bridge. -/
theorem abelianCoverNumber_eq_colorCoverNumber
    (G : Type) [Group G] [Fintype (CentralCoset G)] :
    abelianCoverNumber G = colorCoverNumber G := by
  let A : Set ℕ := {k | ∃ A : Finset (Subgroup G),
    A.card = k ∧ IsAbelianCover G A}
  let C : Set ℕ := {k | ∃ C : Finset (Finset (CentralCoset G)),
    C.card = k ∧ IsColorCover G C}
  have hC : C.Nonempty := by
    classical
    let colors : Finset (Finset (CentralCoset G)) :=
      Finset.univ.image (fun q : CentralCoset G ↦ {q})
    have hcolors : IsColorCover G colors := by
      constructor
      · intro S hS
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hS
        intro a ha b hb
        simp only [Finset.mem_singleton] at ha hb
        subst a
        subst b
        exact cosetsNoncommute_irrefl G q
      · intro q
        exact ⟨{q}, Finset.mem_image.mpr
          ⟨q, Finset.mem_univ q, rfl⟩, Finset.mem_singleton_self q⟩
    exact ⟨colors.card, colors, rfl, hcolors⟩
  have hCA : ∀ c ∈ C, ∃ a ∈ A, a ≤ c := by
    rintro c ⟨colors, rfl, hcolors⟩
    obtain ⟨cover, hcover, hcard⟩ :=
      colorCover_to_abelianCover G colors hcolors
    exact ⟨cover.card, ⟨cover, rfl, hcover⟩, hcard⟩
  have hA : A.Nonempty := by
    obtain ⟨c, hc⟩ := hC
    obtain ⟨a, ha, _⟩ := hCA c hc
    exact ⟨a, ha⟩
  have hAC : ∀ a ∈ A, ∃ c ∈ C, c ≤ a := by
    rintro a ⟨cover, rfl, hcover⟩
    obtain ⟨colors, hcolors, hcard⟩ :=
      abelianCover_to_colorCover G cover hcover
    exact ⟨colors.card, ⟨colors, rfl, hcolors⟩, hcard⟩
  change sInf A = sInf C
  apply le_antisymm
  · obtain ⟨a, ha, hac⟩ := hCA (sInf C) (Nat.sInf_mem hC)
    exact (Nat.sInf_le ha).trans hac
  · obtain ⟨c, hc, hca⟩ := hAC (sInf A) (Nat.sInf_mem hA)
    exact (Nat.sInf_le hc).trans hca

end Erdos117Audit.AbelianColorNumber


namespace Erdos117Audit.ColorCoverNumberInvariant

def IsIndependentCover {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (C : Finset (Finset α)) : Prop :=
  (∀ x : α, ∃ S ∈ C, x ∈ S) ∧
  (∀ S ∈ C, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y)

noncomputable def colorCoverNumber {α : Type*} [DecidableEq α]
    (R : α → α → Prop) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset (Finset α),
    C.card = k ∧ IsIndependentCover R C}

private def transportColors
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : Finset (Finset α)) : Finset (Finset β) :=
  C.image (fun S ↦ S.image e)

private theorem transport
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β)
    (hrel : ∀ x y, R x y ↔ Q (e x) (e y))
    (C : Finset (Finset α)) (hC : IsIndependentCover R C) :
    IsIndependentCover Q (transportColors e C) ∧
      (transportColors e C).card = C.card := by
  constructor
  · constructor
    · intro y
      obtain ⟨S, hSC, hyS⟩ := hC.1 (e.symm y)
      refine ⟨S.image e, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨S, hSC, rfl⟩
      · exact Finset.mem_image.mpr
          ⟨e.symm y, hyS, e.apply_symm_apply y⟩
    · intro T hTC x hxT y hyT hxy
      obtain ⟨S, hSC, rfl⟩ := Finset.mem_image.mp hTC
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hxT
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hyT
      have hxy₀ : x₀ ≠ y₀ := fun h ↦ hxy (congrArg e h)
      intro hQ
      exact hC.2 S hSC x₀ hx₀ y₀ hy₀ hxy₀ ((hrel x₀ y₀).mpr hQ)
  · unfold transportColors
    rw [Finset.card_image_of_injective]
    intro S T hST
    ext x
    have h := congrArg (fun U : Finset β ↦ e x ∈ U) hST
    simpa using h

/-- A relation-preserving equivalence identifies the least cardinalities of
finite independent covers. This composes the color-transport and minima steps
at the end of arXiv:2608.20507v1, Lemma 2.1, TeX lines 107--109. -/
theorem colorCoverNumber_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → α → Prop) (Q : β → β → Prop) (e : α ≃ β)
    (hrel : ∀ x y, R x y ↔ Q (e x) (e y))
    (hex : ∃ C : Finset (Finset α), IsIndependentCover R C) :
    colorCoverNumber R = colorCoverNumber Q := by
  let A : Set ℕ := {k | ∃ C : Finset (Finset α),
    C.card = k ∧ IsIndependentCover R C}
  let B : Set ℕ := {k | ∃ C : Finset (Finset β),
    C.card = k ∧ IsIndependentCover Q C}
  have hA : A.Nonempty := by
    obtain ⟨C, hC⟩ := hex
    exact ⟨C.card, C, rfl, hC⟩
  have hAB : ∀ a ∈ A, ∃ b ∈ B, b ≤ a := by
    rintro a ⟨C, rfl, hC⟩
    obtain ⟨hTC, hcard⟩ := transport R Q e hrel C hC
    exact ⟨(transportColors e C).card,
      ⟨transportColors e C, rfl, hTC⟩, hcard.le⟩
  have hrelSymm :
      ∀ x y, Q x y ↔ R (e.symm x) (e.symm y) := by
    intro x y
    simpa using (hrel (e.symm x) (e.symm y)).symm
  have hB : B.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb, _⟩ := hAB a ha
    exact ⟨b, hb⟩
  have hBA : ∀ b ∈ B, ∃ a ∈ A, a ≤ b := by
    rintro b ⟨C, rfl, hC⟩
    obtain ⟨hTC, hcard⟩ :=
      transport Q R e.symm hrelSymm C hC
    exact ⟨(transportColors e.symm C).card,
      ⟨transportColors e.symm C, rfl, hTC⟩, hcard.le⟩
  change sInf A = sInf B
  apply le_antisymm
  · obtain ⟨a, ha, hab⟩ := hBA (sInf B) (Nat.sInf_mem hB)
    exact (Nat.sInf_le ha).trans hab
  · obtain ⟨b, hb, hba⟩ := hAB (sInf A) (Nat.sInf_mem hA)
    exact (Nat.sInf_le hb).trans hba

end Erdos117Audit.ColorCoverNumberInvariant


namespace Erdos117Audit.ColorPredicateBridge

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
theorem strongColorNumber_eq_weakColorNumber
    (G : Type) [Group G] [DecidableEq (CentralCoset G)] :
    strongColorNumber G = weakColorNumber G := by
  apply congrArg sInf
  ext k
  constructor
  · rintro ⟨C, hcard, hC⟩
    exact ⟨C, hcard, (strongColorCover_iff_weakIndependentCover G C).mp hC⟩
  · rintro ⟨C, hcard, hC⟩
    exact ⟨C, hcard, (strongColorCover_iff_weakIndependentCover G C).mpr hC⟩

end Erdos117Audit.ColorPredicateBridge


namespace Erdos117Audit.FiniteCoverNumberAssembly

/-- Exact finite/combinatorial assembly of the cover-number part of
arXiv:2608.20507v1, Lemma 2.1, after graph invariance has been supplied.
This theorem deliberately leaves the classical construction of the
isoclinism and the finite stem representative outside its hypotheses. -/
theorem abelianCoverNumber_eq_of_centralCoset_graph_equiv
    (G H : Type) [Group G] [Group H]
    [Fintype (AbelianColorNumber.CentralCoset G)]
    [Fintype (AbelianColorNumber.CentralCoset H)]
    (e : AbelianColorNumber.CentralCoset G ≃
      AbelianColorNumber.CentralCoset H)
    (hrel : ∀ a b,
      AbelianColorNumber.CosetsNoncommute G a b ↔
        AbelianColorNumber.CosetsNoncommute H (e a) (e b)) :
    AbelianColorNumber.abelianCoverNumber G =
      AbelianColorNumber.abelianCoverNumber H := by
  classical
  have hex :
      ∃ C : Finset (Finset (AbelianColorNumber.CentralCoset G)),
        ColorCoverNumberInvariant.IsIndependentCover
          (AbelianColorNumber.CosetsNoncommute G) C := by
    let colors :
        Finset (Finset (AbelianColorNumber.CentralCoset G)) :=
      Finset.univ.image
        (fun q : AbelianColorNumber.CentralCoset G ↦ {q})
    refine ⟨colors, ?_⟩
    constructor
    · intro q
      exact ⟨{q}, Finset.mem_image.mpr
        ⟨q, Finset.mem_univ q, rfl⟩, Finset.mem_singleton_self q⟩
    · intro S hS x hx y hy hxy
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hS
      simp only [Finset.mem_singleton] at hx hy
      intro _
      exact hxy (hx.trans hy.symm)
  calc
    AbelianColorNumber.abelianCoverNumber G =
        AbelianColorNumber.colorCoverNumber G :=
      AbelianColorNumber.abelianCoverNumber_eq_colorCoverNumber G
    _ = ColorPredicateBridge.strongColorNumber G := rfl
    _ = ColorPredicateBridge.weakColorNumber G :=
      ColorPredicateBridge.strongColorNumber_eq_weakColorNumber G
    _ = ColorCoverNumberInvariant.colorCoverNumber
        (AbelianColorNumber.CosetsNoncommute G) := rfl
    _ = ColorCoverNumberInvariant.colorCoverNumber
        (AbelianColorNumber.CosetsNoncommute H) :=
      ColorCoverNumberInvariant.colorCoverNumber_eq
        (AbelianColorNumber.CosetsNoncommute G)
        (AbelianColorNumber.CosetsNoncommute H) e hrel hex
    _ = ColorPredicateBridge.weakColorNumber H := rfl
    _ = ColorPredicateBridge.strongColorNumber H :=
      (ColorPredicateBridge.strongColorNumber_eq_weakColorNumber H).symm
    _ = AbelianColorNumber.colorCoverNumber H := rfl
    _ = AbelianColorNumber.abelianCoverNumber H :=
      (AbelianColorNumber.abelianCoverNumber_eq_colorCoverNumber H).symm

end Erdos117Audit.FiniteCoverNumberAssembly

namespace Submissions.Erdos117FiniteCoverNumberInvariant.Kernel

theorem proof :
    ∀ (G H : Type) [Group G] [Group H]
      [Fintype (Erdos117Audit.AbelianColorNumber.CentralCoset G)]
      [Fintype (Erdos117Audit.AbelianColorNumber.CentralCoset H)]
      (e : Erdos117Audit.AbelianColorNumber.CentralCoset G ≃
        Erdos117Audit.AbelianColorNumber.CentralCoset H),
      (∀ a b, Erdos117Audit.AbelianColorNumber.CosetsNoncommute G a b ↔
        Erdos117Audit.AbelianColorNumber.CosetsNoncommute H (e a) (e b)) →
      Erdos117Audit.AbelianColorNumber.abelianCoverNumber G =
        Erdos117Audit.AbelianColorNumber.abelianCoverNumber H :=
  @Erdos117Audit.FiniteCoverNumberAssembly.abelianCoverNumber_eq_of_centralCoset_graph_equiv

end Submissions.Erdos117FiniteCoverNumberInvariant.Kernel
