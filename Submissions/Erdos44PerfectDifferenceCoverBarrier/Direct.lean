import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos44PerfectDifferenceCoverBarrier.Direct

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

theorem proof :
    ∀ {α : Type*} [AddCommGroup α] [Fintype α] [LinearOrder α]
      (C : Finset α) (d : α), PerfectDifferences C → d ∉ C →
        ∀ X : Finset α, Covers C d X → C.card ≤ 4 * X.card := by
  classical
  intro α _ _ _ C d hperfect hd X hcover
  let H := CollisionTriples C d
  have hcover' :
      ∀ p ∈ CollisionTriples C d,
        p.1.1 ∈ X ∨ p.1.2 ∈ X ∨ p.2 ∈ X := by
    intro p hp
    have hm : p ∈ (CollisionTriples C d).filter
        (fun q => q.1.1 ∈ X ∨ q.1.2 ∈ X ∨ q.2 ∈ X) := by
      rw [hcover]
      exact hp
    exact (Finset.mem_filter.mp hm).2
  have perfect_unique :
      ∀ δ : α, δ ≠ 0 →
        ∃! p : α × α, p ∈ C ×ˢ C ∧ p.1 - p.2 = δ := by
    intro δ hδ
    have hm : δ ∈ (Finset.univ.erase 0).filter (fun e =>
        (((C ×ˢ C).filter fun p => p.1 - p.2 = e).card = 1)) := by
      rw [hperfect]
      simp [hδ]
    have hcard := (Finset.mem_filter.mp hm).2
    rw [Finset.card_eq_one] at hcard
    rcases hcard with ⟨p, hp⟩
    refine ⟨p, ?_, ?_⟩
    · have hpm : p ∈ (C ×ˢ C).filter (fun q => q.1 - q.2 = δ) := by
        rw [hp]
        simp
      exact Finset.mem_filter.mp hpm
    · intro q hq
      have hqm : q ∈ (C ×ˢ C).filter (fun r => r.1 - r.2 = δ) :=
        Finset.mem_filter.mpr hq
      rw [hp] at hqm
      simpa using hqm
  have pair_unique :
      ∀ x ∈ C, ∀ y ∈ C, ∀ u ∈ C, ∀ v ∈ C,
        x + y = u + v →
          (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x hx y hy u hu v hv hsum
    by_cases hxu : x = u
    · left
      exact ⟨hxu, by subst u; exact add_left_cancel hsum⟩
    · right
      have hδ : x - u ≠ 0 := sub_ne_zero.mpr hxu
      have hdiff : x - u = v - y :=
        sub_eq_sub_iff_add_eq_add.mpr (hsum.trans (add_comm u v))
      have hp := (perfect_unique (x - u) hδ).unique
        (show (x, u) ∈ C ×ˢ C ∧ x - u = x - u from
          ⟨Finset.mem_product.mpr ⟨hx, hu⟩, rfl⟩)
        (show (v, y) ∈ C ×ˢ C ∧ v - y = x - u from
          ⟨Finset.mem_product.mpr ⟨hv, hy⟩, hdiff.symm⟩)
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp |>.symm⟩
  have hy_inj : Set.InjOn (fun p : Triple α => p.1.2) H := by
    rintro ⟨⟨x, y⟩, z⟩ hp ⟨⟨u, v⟩, w⟩ hq heq
    change y = v at heq
    subst v
    unfold H CollisionTriples at hp hq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    simp only [Finset.mem_product] at hp' hq'
    rcases hp' with ⟨⟨⟨hx, hy⟩, hz⟩, hpe⟩
    rcases hq' with ⟨⟨⟨hu, -⟩, hw⟩, hqe⟩
    have hdy : d - y ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hd
      simpa [h] using hy
    have hxz : x - z = d - y :=
      sub_eq_sub_iff_add_eq_add.mpr (sub_eq_iff_eq_add.mp hpe)
    have huw : u - w = d - y :=
      sub_eq_sub_iff_add_eq_add.mpr (sub_eq_iff_eq_add.mp hqe)
    have hpairs := (perfect_unique (d - y) hdy).unique
      (show (x, z) ∈ C ×ˢ C ∧ x - z = d - y from
        ⟨Finset.mem_product.mpr ⟨hx, hz⟩, hxz⟩)
      (show (u, w) ∈ C ×ˢ C ∧ u - w = d - y from
        ⟨Finset.mem_product.mpr ⟨hu, hw⟩, huw⟩)
    have hxu : x = u := congrArg Prod.fst hpairs
    have hzw : z = w := congrArg Prod.snd hpairs
    subst u
    subst w
    rfl
  have hy_image : H.image (fun p : Triple α => p.1.2) = C := by
    apply Finset.ext
    intro y
    constructor
    · intro hyi
      rcases Finset.mem_image.mp hyi with ⟨⟨⟨x, v⟩, z⟩, hp, hv⟩
      unfold H CollisionTriples at hp
      have hp' := (Finset.mem_filter.mp hp).1
      simp only [Finset.mem_product] at hp'
      change v = y at hv
      rw [← hv]
      exact hp'.1.2
    · intro hy
      have hdy : d - y ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        apply hd
        simpa [h] using hy
      rcases (perfect_unique (d - y) hdy).exists with ⟨⟨x, z⟩, hxz, hdiff⟩
      have hxz' := Finset.mem_product.mp hxz
      apply Finset.mem_image.mpr
      refine ⟨((x, y), z), ?_, rfl⟩
      unfold H CollisionTriples
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hxz'.1, hy⟩, hxz'.2⟩, ?_⟩
      apply sub_eq_iff_eq_add.mpr
      exact sub_eq_sub_iff_add_eq_add.mp hdiff
  have hHcard : H.card = C.card := by
    rw [← hy_image, Finset.card_image_of_injOn hy_inj]
  let Hx := H.filter fun p => p.1.1 ∈ X
  let Hy := H.filter fun p => p.1.2 ∈ X
  let Hz := H.filter fun p => p.2 ∈ X
  have hcovered : H ⊆ (Hx ∪ Hy) ∪ Hz := by
    intro p hp
    simp only [Finset.mem_union, Hx, Hy, Hz, Finset.mem_filter]
    rcases hcover' p hp with hx | hy | hz
    · exact Or.inl (Or.inl ⟨hp, hx⟩)
    · exact Or.inl (Or.inr ⟨hp, hy⟩)
    · exact Or.inr ⟨hp, hz⟩
  have hx_inj : Set.InjOn (fun p : Triple α => p.1.1) Hx := by
    rintro ⟨⟨x, y⟩, z⟩ hp ⟨⟨u, v⟩, w⟩ hq heq
    change x = u at heq
    subst u
    have hpH := (Finset.mem_filter.mp hp).1
    have hqH := (Finset.mem_filter.mp hq).1
    unfold H CollisionTriples at hpH hqH
    have hp' := Finset.mem_filter.mp hpH
    have hq' := Finset.mem_filter.mp hqH
    simp only [Finset.mem_product] at hp' hq'
    rcases hp' with ⟨⟨⟨hx, hy⟩, hz⟩, hpe⟩
    rcases hq' with ⟨⟨⟨-, hv⟩, hw⟩, hqe⟩
    have hdx : d - x ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hd
      simpa [h] using hx
    have hyz : y - z = d - x :=
      sub_eq_sub_iff_add_eq_add.mpr
        ((add_comm y x).trans (sub_eq_iff_eq_add.mp hpe))
    have hvw : v - w = d - x :=
      sub_eq_sub_iff_add_eq_add.mpr
        ((add_comm v x).trans (sub_eq_iff_eq_add.mp hqe))
    have hpairs := (perfect_unique (d - x) hdx).unique
      (show (y, z) ∈ C ×ˢ C ∧ y - z = d - x from
        ⟨Finset.mem_product.mpr ⟨hy, hz⟩, hyz⟩)
      (show (v, w) ∈ C ×ˢ C ∧ v - w = d - x from
        ⟨Finset.mem_product.mpr ⟨hv, hw⟩, hvw⟩)
    have hyv : y = v := congrArg Prod.fst hpairs
    have hzw : z = w := congrArg Prod.snd hpairs
    subst v
    subst w
    rfl
  have hHx : Hx.card ≤ X.card := by
    rw [← Finset.card_image_of_injOn hx_inj]
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact (Finset.mem_filter.mp hp).2
  have hHy : Hy.card ≤ X.card := by
    have hinj : Set.InjOn (fun p : Triple α => p.1.2) Hy :=
      hy_inj.mono (Finset.filter_subset _ _)
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
    exact (Finset.mem_filter.mp hp).2
  let Hzle := Hz.filter fun p => p.1.1 ≤ p.1.2
  let Hzgt := Hz.filter fun p => p.1.2 < p.1.1
  have hz_split : Hz = Hzle ∪ Hzgt := by
    apply Finset.ext
    intro p
    simp only [Hzle, Hzgt, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases le_or_gt p.1.1 p.1.2 with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
  have hz_order_inj :
      ∀ (K : Finset (Triple α)),
        K ⊆ Hz →
        (∀ p ∈ K, p.1.1 ≤ p.1.2) →
        Set.InjOn (fun p : Triple α => p.2) K := by
    intro K hK hord
    rintro ⟨⟨x, y⟩, z⟩ hp ⟨⟨u, v⟩, w⟩ hq heq
    change z = w at heq
    subst w
    have hpHz := hK hp
    have hqHz := hK hq
    have hpH := (Finset.mem_filter.mp hpHz).1
    have hqH := (Finset.mem_filter.mp hqHz).1
    unfold H CollisionTriples at hpH hqH
    have hp' := Finset.mem_filter.mp hpH
    have hq' := Finset.mem_filter.mp hqH
    simp only [Finset.mem_product] at hp' hq'
    rcases hp' with ⟨⟨⟨hx, hy⟩, hz⟩, hpe⟩
    rcases hq' with ⟨⟨⟨hu, hv⟩, -⟩, hqe⟩
    have hsum : x + y = u + v :=
      (sub_eq_iff_eq_add.mp hpe).trans (sub_eq_iff_eq_add.mp hqe).symm
    rcases pair_unique x hx y hy u hu v hv hsum with h | h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨hxu, hyu⟩
      have hpord := hord _ hp
      have hqord := hord _ hq
      have : x = y := le_antisymm hpord (by simpa [hxu, hyu] using hqord)
      subst y
      simp_all
  have hHzle : Hzle.card ≤ X.card := by
    have hsub : Hzle ⊆ Hz := Finset.filter_subset _ _
    have hord : ∀ p ∈ Hzle, p.1.1 ≤ p.1.2 := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    rw [← Finset.card_image_of_injOn (hz_order_inj Hzle hsub hord)]
    apply Finset.card_le_card
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact (Finset.mem_filter.mp (hsub hp)).2
  have hHzgt : Hzgt.card ≤ X.card := by
    let swap : Triple α → Triple α := fun p => ((p.1.2, p.1.1), p.2)
    have hzinj : Set.InjOn (fun p : Triple α => p.2) Hzgt := by
      intro p hp q hq heq
      have hpord : p.1.2 ≤ p.1.1 :=
        le_of_lt (Finset.mem_filter.mp hp).2
      have hqord : q.1.2 ≤ q.1.1 :=
        le_of_lt (Finset.mem_filter.mp hq).2
      rcases p with ⟨⟨x, y⟩, z⟩
      rcases q with ⟨⟨u, v⟩, w⟩
      have hpHz := (Finset.mem_filter.mp hp).1
      have hqHz := (Finset.mem_filter.mp hq).1
      have hpH := (Finset.mem_filter.mp hpHz).1
      have hqH := (Finset.mem_filter.mp hqHz).1
      unfold H CollisionTriples at hpH hqH
      have hp' := Finset.mem_filter.mp hpH
      have hq' := Finset.mem_filter.mp hqH
      simp only [Finset.mem_product] at hp' hq'
      rcases hp' with ⟨⟨⟨hx, hy⟩, hz⟩, hpe⟩
      rcases hq' with ⟨⟨⟨hu, hv⟩, hw⟩, hqe⟩
      change z = w at heq
      subst w
      have hsum : x + y = u + v :=
        (sub_eq_iff_eq_add.mp hpe).trans (sub_eq_iff_eq_add.mp hqe).symm
      rcases pair_unique x hx y hy u hu v hv hsum with h | h
      · rcases h with ⟨rfl, rfl⟩
        rfl
      · rcases h with ⟨hxu, hyu⟩
        have hxy : x ≤ y := by simpa [hxu, hyu] using hqord
        have : x = y := le_antisymm hxy hpord
        subst y
        simp_all
    rw [← Finset.card_image_of_injOn hzinj]
    apply Finset.card_le_card
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hpHz := (Finset.mem_filter.mp hp).1
    exact (Finset.mem_filter.mp hpHz).2
  have hHz : Hz.card ≤ 2 * X.card := by
    rw [hz_split]
    calc
      (Hzle ∪ Hzgt).card ≤ Hzle.card + Hzgt.card :=
        Finset.card_union_le Hzle Hzgt
      _ ≤ 2 * X.card := by omega
  calc
    C.card = H.card := hHcard.symm
    _ ≤ ((Hx ∪ Hy) ∪ Hz).card := Finset.card_le_card hcovered
    _ ≤ (Hx ∪ Hy).card + Hz.card := Finset.card_union_le (Hx ∪ Hy) Hz
    _ ≤ Hx.card + Hy.card + Hz.card := by
      have := Finset.card_union_le Hx Hy
      omega
    _ ≤ 4 * X.card := by omega

end Submissions.Erdos44PerfectDifferenceCoverBarrier.Direct
