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

def subgroupForColor (G : Type) [Group G]
    (S : Finset (CentralCoset G)) : Subgroup G :=
  Subgroup.closure {x : G | centralCosetMk G x ∈ S}

theorem colorCover_to_abelianCover
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

noncomputable def colorForSubgroup
    (G : Type) [Group G] [Fintype (CentralCoset G)]
    (H : Subgroup G) : Finset (CentralCoset G) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ h : G, h ∈ H ∧ centralCosetMk G h = q

theorem commute_left_factors_of_commute_products
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

theorem abelianCover_to_colorCover
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


namespace Erdos117Audit.FiniteCoverNumberDirect

namespace ACN

open Erdos117Audit.AbelianColorNumber

noncomputable def transportColors
    {G H : Type} [Group G] [Group H]
    (e : CentralCoset G ≃ CentralCoset H)
    (C : Finset (Finset (CentralCoset G))) :
    Finset (Finset (CentralCoset H)) := by
  classical
  exact C.image (fun S ↦ S.image e)

theorem transportColorCover
    {G H : Type} [Group G] [Group H]
    (e : CentralCoset G ≃ CentralCoset H)
    (hrel : ∀ a b, CosetsNoncommute G a b ↔
      CosetsNoncommute H (e a) (e b))
    (C : Finset (Finset (CentralCoset G)))
    (hC : IsColorCover G C) :
    IsColorCover H (transportColors e C) ∧
      (transportColors e C).card = C.card := by
  classical
  constructor
  · constructor
    · intro T hT x hx y hy
      obtain ⟨S, hSC, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
      exact fun hn ↦ hC.1 S hSC x₀ hx₀ y₀ hy₀ ((hrel x₀ y₀).mpr hn)
    · intro q
      obtain ⟨q₀, rfl⟩ := e.surjective q
      obtain ⟨S, hSC, hqS⟩ := hC.2 q₀
      exact ⟨S.image e, Finset.mem_image.mpr ⟨S, hSC, rfl⟩,
        Finset.mem_image.mpr ⟨q₀, hqS, rfl⟩⟩
  · unfold transportColors
    rw [Finset.card_image_of_injective]
    intro S T hST
    ext x
    have h := congrArg (fun U : Finset (CentralCoset H) ↦ e x ∈ U) hST
    simpa using h

theorem finiteCoverNumberInvariant
    (G H : Type) [Group G] [Group H]
    [Fintype (CentralCoset G)] [Fintype (CentralCoset H)]
    (e : CentralCoset G ≃ CentralCoset H)
    (hrel : ∀ a b, CosetsNoncommute G a b ↔
      CosetsNoncommute H (e a) (e b)) :
    abelianCoverNumber G = abelianCoverNumber H := by
  classical
  let A : Set ℕ := {k | ∃ cover : Finset (Subgroup G),
    cover.card = k ∧ IsAbelianCover G cover}
  let B : Set ℕ := {k | ∃ cover : Finset (Subgroup H),
    cover.card = k ∧ IsAbelianCover H cover}
  have hrelSymm :
      ∀ a b, CosetsNoncommute H a b ↔
        CosetsNoncommute G (e.symm a) (e.symm b) := by
    intro a b
    simpa using (hrel (e.symm a) (e.symm b)).symm
  have hAB : ∀ a ∈ A, ∃ b ∈ B, b ≤ a := by
    rintro a ⟨coverG, rfl, hcoverG⟩
    obtain ⟨colorsG, hcolorsG, hcolorsCard⟩ :=
      abelianCover_to_colorCover G coverG hcoverG
    obtain ⟨hcolorsH, htransportCard⟩ :=
      transportColorCover e hrel colorsG hcolorsG
    obtain ⟨coverH, hcoverH, hcoverCard⟩ :=
      colorCover_to_abelianCover H (transportColors e colorsG) hcolorsH
    exact ⟨coverH.card, ⟨coverH, rfl, hcoverH⟩,
      hcoverCard.trans (htransportCard.le.trans hcolorsCard)⟩
  have hBA : ∀ b ∈ B, ∃ a ∈ A, a ≤ b := by
    rintro b ⟨coverH, rfl, hcoverH⟩
    obtain ⟨colorsH, hcolorsH, hcolorsCard⟩ :=
      abelianCover_to_colorCover H coverH hcoverH
    obtain ⟨hcolorsG, htransportCard⟩ :=
      transportColorCover e.symm hrelSymm colorsH hcolorsH
    obtain ⟨coverG, hcoverG, hcoverCard⟩ :=
      colorCover_to_abelianCover G (transportColors e.symm colorsH) hcolorsG
    exact ⟨coverG.card, ⟨coverG, rfl, hcoverG⟩,
      hcoverCard.trans (htransportCard.le.trans hcolorsCard)⟩
  have hA : A.Nonempty := by
    let colors : Finset (Finset (CentralCoset G)) :=
      Finset.univ.image (fun q : CentralCoset G ↦ {q})
    have hcolors : IsColorCover G colors := by
      constructor
      · intro S hS
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hS
        intro x hx y hy
        simp only [Finset.mem_singleton] at hx hy
        subst x
        subst y
        exact cosetsNoncommute_irrefl G q
      · intro q
        exact ⟨{q}, Finset.mem_image.mpr
          ⟨q, Finset.mem_univ q, rfl⟩, Finset.mem_singleton_self q⟩
    obtain ⟨cover, hcover, _⟩ :=
      colorCover_to_abelianCover G colors hcolors
    exact ⟨cover.card, cover, rfl, hcover⟩
  have hB : B.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb, _⟩ := hAB a ha
    exact ⟨b, hb⟩
  change sInf A = sInf B
  apply le_antisymm
  · obtain ⟨a, ha, hab⟩ := hBA (sInf B) (Nat.sInf_mem hB)
    exact (Nat.sInf_le ha).trans hab
  · obtain ⟨b, hb, hba⟩ := hAB (sInf A) (Nat.sInf_mem hA)
    exact (Nat.sInf_le hb).trans hba

end ACN

end Erdos117Audit.FiniteCoverNumberDirect

namespace Submissions.Erdos117FiniteCoverNumberInvariant.SlimKernel

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
  @Erdos117Audit.FiniteCoverNumberDirect.ACN.finiteCoverNumberInvariant

end Submissions.Erdos117FiniteCoverNumberInvariant.SlimKernel
