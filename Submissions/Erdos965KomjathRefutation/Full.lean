import Mathlib

universe u v
/-!
Complete Lean 4.33 port of Komjáth’s ZFC anti-Ramsey colouring proof.
Source modules are concatenated in dependency order; only internal import lines
were removed.
-/

/-! ## Upstream module: Countability.lean -/

open Function Set


namespace Erdos965

variable {α : Type u} {β : Type v}

/-- An uncountable set mapped to a countable type has an uncountable fibre. -/
theorem uncountable_fiber_of_countable_range [Countable β]
    (f : α → β) {I : Set α} (hI : ¬ I.Countable) :
    ∃ b, ¬ {x ∈ I | f x = b}.Countable := by
  by_contra! h
  apply hI
  refine (Set.countable_iUnion h).mono ?_
  intro x hx
  exact Set.mem_iUnion.2 ⟨f x, hx, rfl⟩

/-- If all relative fibres of a map are countable, its restriction to an
uncountable set has uncountable range. -/
theorem image_uncountable_of_countable_fibers
    (f : α → β) {I : Set α} (hI : ¬ I.Countable)
    (hfib : ∀ b, {x ∈ I | f x = b}.Countable) :
    ¬ (f '' I).Countable := by
  intro him
  apply hI
  refine (him.biUnion fun b hb ↦ hfib b).mono ?_
  rintro x hx
  refine Set.mem_iUnion.2 ⟨f x, Set.mem_iUnion.2 ⟨⟨x, hx, rfl⟩, hx, rfl⟩⟩

/-- On an uncountable set, every map is constant on an uncountable subset or
injective on an uncountable subset. -/
theorem uncountable_constant_or_injective
    (f : α → β) {I : Set α} (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ((∃ b, ∀ x ∈ J, f x = b) ∨ InjOn f J) := by
  classical
  by_cases hbig : ∃ b, ¬ {x ∈ I | f x = b}.Countable
  · obtain ⟨b, hb⟩ := hbig
    refine ⟨{x ∈ I | f x = b}, fun _ hx ↦ hx.1, hb, Or.inl ⟨b, ?_⟩⟩
    intro x hx
    exact hx.2
  · push Not at hbig
    have himage : ¬ (f '' I).Countable :=
      image_uncountable_of_countable_fibers f hI hbig
    let R := f '' I
    have hsec : ∀ b : R, ∃ x ∈ I, f x = b := by
      rintro ⟨b, x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    choose g hgI hgf using hsec
    let J : Set α := Set.range g
    have hg_inj : Injective g := by
      intro b c hbc
      apply Subtype.ext
      rw [← hgf b, ← hgf c, hbc]
    have hJsub : J ⊆ I := by
      rintro x ⟨b, rfl⟩
      exact hgI b
    have hJunc : ¬ J.Countable := by
      intro hJ
      apply himage
      rw [← Set.countable_coe_iff]
      let _ : Countable J := hJ.to_subtype
      let gj : R → J := fun b ↦ ⟨g b, Set.mem_range_self b⟩
      exact (show Injective gj from fun b c hbc ↦
        hg_inj (congrArg Subtype.val hbc)).countable
    refine ⟨J, hJsub, hJunc, Or.inr ?_⟩
    rintro x ⟨b, rfl⟩ y ⟨c, rfl⟩ hxy
    exact congrArg g (Subtype.ext ((hgf b).symm.trans (hxy.trans (hgf c))))

/-- The union of all countable relative fibres of a map to a countable type is
countable.  Equivalently, after deleting this set, every surviving fibre is
uncountable. -/
theorem countable_union_of_countable_fibers [Countable β]
    (f : α → β) (I : Set α) :
    {x ∈ I | {y ∈ I | f y = f x}.Countable}.Countable := by
  classical
  let C : β → Set α := fun b ↦
    if {x ∈ I | f x = b}.Countable then {x ∈ I | f x = b} else ∅
  have hC : ∀ b, (C b).Countable := by
    intro b
    by_cases h : {x ∈ I | f x = b}.Countable
    · change (if {x ∈ I | f x = b}.Countable then
          {x ∈ I | f x = b} else ∅).Countable
      rw [if_pos h]
      exact h
    · simp [C, h]
  refine (Set.countable_iUnion hC).mono ?_
  intro x hx
  refine Set.mem_iUnion.2 ⟨f x, ?_⟩
  simp [C, hx.2, hx.1]

/-- Removing a countable set from an uncountable set leaves an uncountable
set. -/
theorem uncountable_sdiff_countable {I C : Set α}
    (hI : ¬ I.Countable) (hC : C.Countable) :
    ¬ (I \ C).Countable := by
  intro hdiff
  apply hI
  exact (hdiff.union hC).mono (Set.subset_sdiff_union I C)

/-- A point can be chosen outside any countable exceptional subset of an
uncountable set. -/
theorem exists_mem_not_mem_of_uncountable_of_countable
    {I C : Set α} (hI : ¬ I.Countable) (hC : C.Countable) :
    ∃ x ∈ I, x ∉ C := by
  by_contra! h
  exact hI (hC.mono h)

/-- Delete precisely the points lying in countable relative fibres.  What
remains is uncountable, and every fibre represented there is uncountable. -/
theorem uncountable_after_deleting_countable_fibers [Countable β]
    (f : α → β) {I : Set α} (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ∀ x ∈ J, ¬ {y ∈ I | f y = f x}.Countable := by
  let C : Set α := {x ∈ I | {y ∈ I | f y = f x}.Countable}
  refine ⟨I \ C, fun _ hx ↦ hx.1, ?_, ?_⟩
  · exact uncountable_sdiff_countable hI
      (countable_union_of_countable_fibers f I)
  · intro x hx hxfib
    exact hx.2 ⟨hx.1, hxfib⟩

/-- Lower-countable normalization of an injective map into a well-order.  The
resulting uncountable set has only countably many earlier elements below each
of its members (where earlier is measured after applying `p`). -/
theorem uncountable_lowerNormalized {r : β → β → Prop} [IsWellOrder β r]
    (p : α → β) {I : Set α} (hI : ¬ I.Countable) (hp : InjOn p I) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ∀ x ∈ J, {y ∈ J | r (p y) (p x)}.Countable := by
  classical
  let P : Set β := p '' I
  let Bad : Set β := {x ∈ P | ¬ {y ∈ P | r y x}.Countable}
  by_cases hBad : Bad.Nonempty
  · let wf : WellFounded r := IsWellFounded.wf
    let m : β := wf.min Bad hBad
    have hmBad : m ∈ Bad := wf.min_mem Bad hBad
    have hmmin : ∀ z ∈ Bad, ¬ r z m := fun z hz ↦
      wf.not_lt_min Bad hz
    let J : Set α := {x ∈ I | r (p x) m}
    have hJsub : J ⊆ I := fun _ hx ↦ hx.1
    have hpred_image : {y ∈ P | r y m} ⊆ p '' J := by
      rintro y ⟨⟨x, hxI, rfl⟩, hxm⟩
      exact ⟨x, ⟨hxI, hxm⟩, rfl⟩
    have hJunc : ¬ J.Countable := by
      intro hJ
      apply hmBad.2
      exact (hJ.image p).mono hpred_image
    refine ⟨J, hJsub, hJunc, ?_⟩
    intro x hxJ
    have hpxP : p x ∈ P := ⟨x, hxJ.1, rfl⟩
    have hpxNotBad : p x ∉ Bad := by
      intro hpxBad
      exact hmmin (p x) hpxBad hxJ.2
    have hpredP : {y ∈ P | r y (p x)}.Countable := by
      by_contra hnot
      exact hpxNotBad ⟨hpxP, hnot⟩
    have himage : (p '' {y ∈ J | r (p y) (p x)}).Countable := by
      refine hpredP.mono ?_
      rintro z ⟨y, hy, rfl⟩
      exact ⟨⟨y, hJsub hy.1, rfl⟩, hy.2⟩
    exact Set.countable_of_injective_of_countable_image
      (hp.mono fun _ hy ↦ hJsub hy.1) himage
  ·
    refine ⟨I, Set.Subset.rfl, hI, ?_⟩
    intro x hxI
    have hpxP : p x ∈ P := ⟨x, hxI, rfl⟩
    have hpredP : {y ∈ P | r y (p x)}.Countable := by
      by_contra hnot
      exact hBad ⟨p x, hpxP, hnot⟩
    have himage : (p '' {y ∈ I | r (p y) (p x)}).Countable := by
      refine hpredP.mono ?_
      rintro z ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy.1, rfl⟩, hy.2⟩
    exact Set.countable_of_injective_of_countable_image
      (hp.mono fun _ hy ↦ hy.1) himage

/-- From two uncountable subsets of a lower-normalized set, choose a cross
pair in the forward well-order orientation. -/
theorem exists_cross_forward {r : β → β → Prop} [IsWellOrder β r]
    (p : α → β) {D U V : Set α} (hp : InjOn p D)
    (hlower : ∀ x ∈ D, {y ∈ D | r (p y) (p x)}.Countable)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hU : ¬ U.Countable) (hV : ¬ V.Countable) :
    ∃ u ∈ U, ∃ v ∈ V, r (p u) (p v) := by
  have hUne : U.Nonempty := by
    by_contra hn
    exact hU (Set.not_nonempty_iff_eq_empty.mp hn ▸ Set.countable_empty)
  obtain ⟨u, huU⟩ := hUne
  have hlowerV : {v ∈ V | r (p v) (p u)}.Countable := by
    refine Set.Countable.mono ?_ (hlower u (hUD huU))
    intro v hv
    exact And.intro (hVD hv.1) hv.2
  have hexception : ({v ∈ V | r (p v) (p u)} ∪ {u}).Countable :=
    hlowerV.union (Set.countable_singleton u)
  obtain ⟨v, hvV, hv⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable hV hexception
  refine ⟨u, huU, v, hvV, ?_⟩
  have hnvu : v ≠ u := by
    intro hvu
    apply hv
    exact Or.inr hvu
  have hpne : p u ≠ p v := fun huv ↦
    hnvu (hp (hVD hvV) (hUD huU) huv.symm)
  rcases trichotomous_of r (p u) (p v) with huv | huv | hvu
  · exact huv
  · exact (hpne huv).elim
  · exact (hv (Or.inl ⟨hvV, hvu⟩)).elim

/-- Both well-order orientations occur between any two uncountable subsets
of a lower-normalized set. -/
theorem exists_cross_orientations {r : β → β → Prop} [IsWellOrder β r]
    (p : α → β) {D U V : Set α} (hp : InjOn p D)
    (hlower : ∀ x ∈ D, {y ∈ D | r (p y) (p x)}.Countable)
    (hUD : U ⊆ D) (hVD : V ⊆ D) (hU : ¬ U.Countable) (hV : ¬ V.Countable) :
    (∃ u ∈ U, ∃ v ∈ V, r (p u) (p v)) ∧
      ∃ u ∈ U, ∃ v ∈ V, r (p v) (p u) := by
  constructor
  · exact exists_cross_forward p hp hlower hUD hVD hU hV
  · obtain ⟨v, hv, u, hu, hvu⟩ :=
      exists_cross_forward p hp hlower hVD hUD hV hU
    exact ⟨u, hu, v, hv, hvu⟩

end Erdos965

/-! ## Upstream module: CriticalPair.lean -/

open Function Set

namespace Erdos965

/-! ## Hamel indices and their binary rational-cut codes -/

/-- The index type of Mathlib's chosen Hamel basis of `ℝ` over `ℚ`.
It is definitionally a subtype of `ℝ`, so it inherits the ordinary real order. -/
abbrev HamelIndex := Module.Basis.ofVectorSpaceIndex ℚ ℝ

/-- Mathlib's chosen Hamel basis of `ℝ` over `ℚ`. -/
noncomputable abbrev hamelBasis : Module.Basis HamelIndex ℚ ℝ :=
  Module.Basis.ofVectorSpace ℚ ℝ

/-- A fixed enumeration of the rationals. -/
noncomputable def ratEnum : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

@[simp] theorem ratEnum_apply_eq (q : ℚ) :
    ratEnum ((Denumerable.eqv ℚ) q) = q := by
  simp [ratEnum]

/-- The rational-cut code of a Hamel index.  The `n`th bit records whether
the `n`th rational in the fixed enumeration lies strictly below the index. -/
noncomputable def binaryCode (x : HamelIndex) (n : ℕ) : Bool :=
  decide (((ratEnum n : ℚ) : ℝ) < (x : ℝ))

theorem binaryCode_mono {x y : HamelIndex} (hxy : x ≤ y) (n : ℕ) :
    binaryCode x n ≤ binaryCode y n := by
  by_cases hx : (((ratEnum n : ℚ) : ℝ) < (x : ℝ))
  · have hy : (((ratEnum n : ℚ) : ℝ) < (y : ℝ)) := hx.trans_le hxy
    simp [binaryCode, hx, hy]
  · simp [binaryCode, hx]

/-- A `false`/`true` separation at any coordinate forces the corresponding
ordinary order on the underlying reals. -/
theorem lt_of_binaryCode_eq_false_true {x y : HamelIndex} {n : ℕ}
    (hx : binaryCode x n = false) (hy : binaryCode y n = true) : x < y := by
  have hxq : ¬ (((ratEnum n : ℚ) : ℝ) < (x : ℝ)) := by
    apply of_decide_eq_false
    exact hx
  have hqy : (((ratEnum n : ℚ) : ℝ) < (y : ℝ)) := by
    apply of_decide_eq_true
    exact hy
  exact (le_of_not_gt hxq).trans_lt hqy

/-- Rational cuts separate distinct reals, hence also distinct Hamel indices. -/
theorem binaryCode_injective : Injective binaryCode := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q, hxq, hqy⟩ : ∃ q : ℚ, (x : ℝ) < q ∧ (q : ℝ) < y :=
      exists_rat_btwn hlt
    have hbit := congrFun hxy ((Denumerable.eqv ℚ) q)
    simp [binaryCode, ratEnum, hxq.not_gt, hqy] at hbit
  · obtain ⟨q, hyq, hqx⟩ : ∃ q : ℚ, (y : ℝ) < q ∧ (q : ℝ) < x :=
      exists_rat_btwn hgt
    have hbit := congrFun hxy ((Denumerable.eqv ℚ) q)
    simp [binaryCode, ratEnum, hqx, hyq.not_gt] at hbit

/-- The first position at which the rational-cut codes differ. -/
noncomputable def firstDiff (x y : HamelIndex) : ℕ :=
  PiNat.firstDiff (binaryCode x) (binaryCode y)

theorem binaryCode_ne {x y : HamelIndex} (hxy : x ≠ y) :
    binaryCode x ≠ binaryCode y :=
  binaryCode_injective.ne hxy

theorem binaryCode_apply_firstDiff_ne {x y : HamelIndex} (hxy : x ≠ y) :
    binaryCode x (firstDiff x y) ≠ binaryCode y (firstDiff x y) := by
  exact PiNat.apply_firstDiff_ne (binaryCode_ne hxy)

theorem binaryCode_apply_eq_of_lt_firstDiff {x y : HamelIndex} {n : ℕ}
    (hn : n < firstDiff x y) : binaryCode x n = binaryCode y n := by
  exact PiNat.apply_eq_of_lt_firstDiff hn

theorem firstDiff_comm (x y : HamelIndex) : firstDiff x y = firstDiff y x := by
  exact PiNat.firstDiff_comm _ _

/-- At the first difference, the rational-cut code has the same orientation
as the ordinary order on the underlying reals. -/
theorem binaryCode_firstDiff_of_lt {x y : HamelIndex} (hxy : x < y) :
    binaryCode x (firstDiff x y) = false ∧
      binaryCode y (firstDiff x y) = true := by
  have hne := binaryCode_apply_firstDiff_ne hxy.ne
  have hle := binaryCode_mono hxy.le (firstDiff x y)
  revert hne hle
  generalize binaryCode x (firstDiff x y) = a
  generalize binaryCode y (firstDiff x y) = b
  cases a <;> cases b <;> decide

/-- If two different points lie above the same lower point and split from it
at the same level, then they split from each other strictly later. -/
theorem firstDiff_lt_firstDiff_of_common_lower {x y z : HamelIndex}
    (hxy : x < y) (hxz : x < z) (hyz : y ≠ z)
    (hEq : firstDiff x y = firstDiff x z) :
    firstDiff x y < firstDiff y z := by
  have hyzCode : binaryCode y ≠ binaryCode z := binaryCode_ne hyz
  have hle := PiNat.min_firstDiff_le (binaryCode y) (binaryCode x) (binaryCode z) hyzCode
  change min (firstDiff y x) (firstDiff x z) ≤ firstDiff y z at hle
  rw [firstDiff_comm y x, ← hEq, min_self] at hle
  refine hle.lt_of_ne ?_
  intro heq
  have hdiff := PiNat.apply_firstDiff_ne hyzCode
  have hybit := (binaryCode_firstDiff_of_lt hxy).2
  have hzbit := (binaryCode_firstDiff_of_lt hxz).2
  apply hdiff
  change binaryCode y (firstDiff y z) = binaryCode z (firstDiff y z)
  rw [← heq, hybit, hEq, hzbit]

/-! ## The canonical critical pair -/

/-- An oriented pair `(x,y)` is critical for `s` when it belongs to `s`,
maximizes the first-difference level, and its lower endpoint is least among
all ordered pairs attaining that maximum. -/
def IsCriticalPair (s : Finset HamelIndex) (x y : HamelIndex) : Prop :=
  x ∈ s ∧ y ∈ s ∧ x < y ∧
    (∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b →
      firstDiff a b ≤ firstDiff x y) ∧
    (∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b →
      firstDiff a b = firstDiff x y → x ≤ a)

theorem IsCriticalPair.fst_mem {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) : x ∈ s := h.1

theorem IsCriticalPair.snd_mem {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) : y ∈ s := h.2.1

theorem IsCriticalPair.lt {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) : x < y := h.2.2.1

theorem IsCriticalPair.maximal {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) {a b : HamelIndex}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    firstDiff a b ≤ firstDiff x y :=
  h.2.2.2.1 ha hb hab

theorem IsCriticalPair.le_lower {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) {a b : HamelIndex}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hdiff : firstDiff a b = firstDiff x y) : x ≤ a :=
  h.2.2.2.2 ha hb hab hdiff

/-- The finite set of all ordinarily oriented pairs from `s`. -/
private noncomputable def orientedPairs (s : Finset HamelIndex) :
    Finset (HamelIndex × HamelIndex) :=
  (s ×ˢ s).filter fun p ↦ p.1 < p.2

private theorem mem_orientedPairs {s : Finset HamelIndex} {p : HamelIndex × HamelIndex} :
    p ∈ orientedPairs s ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 := by
  rw [orientedPairs, Finset.mem_filter, Finset.mem_product]
  tauto

private theorem orientedPairs_nonempty {s : Finset HamelIndex} (hs : 2 ≤ s.card) :
    (orientedPairs s).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact ⟨(a, b), mem_orientedPairs.2 ⟨ha, hb, hablt⟩⟩
  · exact ⟨(b, a), mem_orientedPairs.2 ⟨hb, ha, hbalt⟩⟩

/-- Every finite set with at least two members has a critical pair. -/
theorem exists_isCriticalPair (s : Finset HamelIndex) (hs : 2 ≤ s.card) :
    ∃ x y, IsCriticalPair s x y := by
  classical
  let P := orientedPairs s
  have hP : P.Nonempty := orientedPairs_nonempty hs
  let D : Finset ℕ := P.image fun p ↦ firstDiff p.1 p.2
  have hD : D.Nonempty := hP.image _
  let N : ℕ := D.max' hD
  let Q : Finset (HamelIndex × HamelIndex) :=
    P.filter fun p ↦ firstDiff p.1 p.2 = N
  have hQ : Q.Nonempty := by
    have hNmem : N ∈ D := D.max'_mem hD
    obtain ⟨p, hpP, hpN⟩ := Finset.mem_image.mp hNmem
    exact ⟨p, Finset.mem_filter.2 ⟨hpP, hpN⟩⟩
  let L : Finset HamelIndex := Q.image Prod.fst
  have hL : L.Nonempty := hQ.image _
  let x : HamelIndex := L.min' hL
  have hxL : x ∈ L := L.min'_mem hL
  obtain ⟨⟨a, b⟩, hpQ, hax⟩ := Finset.mem_image.mp hxL
  simp only at hax
  subst a
  have hpP : (x, b) ∈ P := (Finset.mem_filter.mp hpQ).1
  have hpN : firstDiff x b = N := (Finset.mem_filter.mp hpQ).2
  refine ⟨x, b, ?_⟩
  have hxy := mem_orientedPairs.mp hpP
  refine ⟨hxy.1, hxy.2.1, hxy.2.2, ?_, ?_⟩
  · intro a ha b hb hab
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · have hpab : (a, b) ∈ P := mem_orientedPairs.2 ⟨ha, hb, hablt⟩
      have hmem : firstDiff a b ∈ D := Finset.mem_image.2 ⟨(a, b), hpab, rfl⟩
      simpa only [hpN] using D.le_max' _ hmem
    · have hpba : (b, a) ∈ P := mem_orientedPairs.2 ⟨hb, ha, hbalt⟩
      have hmem : firstDiff b a ∈ D := Finset.mem_image.2 ⟨(b, a), hpba, rfl⟩
      rw [firstDiff_comm]
      simpa only [hpN] using D.le_max' _ hmem
  · intro a ha b hb hab hdiff
    have hpab : (a, b) ∈ P := mem_orientedPairs.2 ⟨ha, hb, hab⟩
    have habN : firstDiff a b = N := hdiff.trans hpN
    have hpabQ : (a, b) ∈ Q := Finset.mem_filter.2 ⟨hpab, habN⟩
    have haL : a ∈ L := Finset.mem_image.2 ⟨(a, b), hpabQ, rfl⟩
    exact L.min'_le _ haL

/-- Critical pairs are unique.  The key point is that two distinct upper
endpoints above the same lower endpoint would have a later first difference. -/
theorem isCriticalPair_unique {s : Finset HamelIndex} {x y x' y' : HamelIndex}
    (h : IsCriticalPair s x y) (h' : IsCriticalPair s x' y') :
    x = x' ∧ y = y' := by
  have hdiff_le := h.maximal h'.fst_mem h'.snd_mem h'.lt.ne
  have hdiff_ge := h'.maximal h.fst_mem h.snd_mem h.lt.ne
  have hdiff : firstDiff x y = firstDiff x' y' := le_antisymm hdiff_ge hdiff_le
  have hxx' : x ≤ x' := h.le_lower h'.fst_mem h'.snd_mem h'.lt hdiff.symm
  have hx'x : x' ≤ x := h'.le_lower h.fst_mem h.snd_mem h.lt hdiff
  have hx : x = x' := le_antisymm hxx' hx'x
  subst x'
  refine ⟨rfl, ?_⟩
  by_contra hyy'
  have hlate : firstDiff x y < firstDiff y y' :=
    firstDiff_lt_firstDiff_of_common_lower h.lt h'.lt hyy' hdiff
  exact (not_le_of_gt hlate) (h.maximal h.snd_mem h'.snd_mem hyy')

private noncomputable instance : Inhabited HamelIndex :=
  ⟨hamelBasis.index_nonempty.some⟩

/-- The canonical critical pair.  Its value on sets of size at most one is an
irrelevant default; all specifications below assume `2 ≤ s.card`. -/
noncomputable def criticalPair (s : Finset HamelIndex) : HamelIndex × HamelIndex :=
  if hs : 2 ≤ s.card then
    let h := exists_isCriticalPair s hs
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else default

theorem criticalPair_spec {s : Finset HamelIndex} (hs : 2 ≤ s.card) :
    IsCriticalPair s (criticalPair s).1 (criticalPair s).2 := by
  rw [criticalPair, dif_pos hs]
  exact Classical.choose_spec (Classical.choose_spec (exists_isCriticalPair s hs))

/-- Characterization of the canonical pair.  This is the main interface used
to identify it in structured unions. -/
theorem criticalPair_eq_iff_isCriticalPair {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex} :
    criticalPair s = (x, y) ↔ IsCriticalPair s x y := by
  constructor
  · intro hp
    have h := criticalPair_spec hs
    rw [hp] at h
    exact h
  · intro h
    have hu := isCriticalPair_unique (criticalPair_spec hs) h
    exact Prod.ext hu.1 hu.2

/-- A convenient cross-union characterization: to identify a proposed pair,
it suffices to prove membership and ordinary orientation, an upper bound for
every first difference in the union, and leastness of its lower endpoint among
the maximizing pairs. -/
theorem criticalPair_eq_of_maximal_least {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hmax : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b →
      firstDiff a b ≤ firstDiff x y)
    (hleast : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b →
      firstDiff a b = firstDiff x y → x ≤ a) :
    criticalPair s = (x, y) := by
  exact (criticalPair_eq_iff_isCriticalPair hs).2 ⟨hx, hy, hxy, hmax, hleast⟩

/-! ## The support colouring -/

/-- Colour a finite support by comparing the ordinary orientation of its
critical pair with the fixed choice well-order. -/
noncomputable def supportColor (s : Finset HamelIndex) : Fin 2 :=
  by
    classical
    exact if hs : 2 ≤ s.card then
      if WellOrderingRel (criticalPair s).1 (criticalPair s).2 then 0 else 1
    else 0

theorem supportColor_eq_zero_of_criticalPair {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex}
    (hp : criticalPair s = (x, y)) (hxy : WellOrderingRel x y) :
    supportColor s = 0 := by
  classical
  simp [supportColor, hs, hp, hxy]

theorem supportColor_eq_one_of_criticalPair {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex}
    (hp : criticalPair s = (x, y)) (hxy : ¬ WellOrderingRel x y) :
    supportColor s = 1 := by
  classical
  simp [supportColor, hs, hp, hxy]

end Erdos965

/-! ## Upstream module: UniformPrefix.lean -/

open Function Set


namespace Erdos965

noncomputable section

/-! ## Ordered coordinates for fixed-cardinality finite sets -/

variable {ι : Type u} {α : Type v}

/-- The increasing enumeration of a finite set whose cardinality is known. -/
def finsetCoord [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) : Fin n → α :=
  (F i).orderEmbOfFin (hcard i)

theorem finsetCoord_mem [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) (j : Fin n) :
    finsetCoord F hcard i j ∈ F i := by
  exact Finset.orderEmbOfFin_mem _ _ _

theorem finsetCoord_injective [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    Injective (finsetCoord F hcard i) := by
  exact ((F i).orderEmbOfFin (hcard i)).injective

theorem finsetCoord_strictMono [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    StrictMono (finsetCoord F hcard i) := by
  exact ((F i).orderEmbOfFin (hcard i)).strictMono

theorem range_finsetCoord [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    Set.range (finsetCoord F hcard i) = (F i : Set α) := by
  exact Finset.range_orderEmbOfFin _ _

/-! ## A common finite prefix separating one finite set -/

/-- One more than the largest first-difference level occurring among pairs
of elements of `s`.  Restriction to this many bits is injective on `s`. -/
def separationLength (s : Finset HamelIndex) : ℕ :=
  s.sup fun x ↦ s.sup fun y ↦ firstDiff x y + 1

theorem firstDiff_lt_separationLength {s : Finset HamelIndex} {x y : HamelIndex}
    (hx : x ∈ s) (hy : y ∈ s) :
    firstDiff x y < separationLength s := by
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  dsimp [separationLength]
  exact (Finset.le_sup (s := s) (f := fun y ↦ firstDiff x y + 1) hy).trans
    (Finset.le_sup (s := s) (f := fun x ↦
      s.sup fun y ↦ firstDiff x y + 1) hx)

/-- If two finite prefixes differ, the first differing bit occurs inside the
prefix. -/
theorem firstDiff_lt_of_res_ne {x y : HamelIndex} {L : ℕ}
    (hres : PiNat.res (binaryCode x) L ≠ PiNat.res (binaryCode y) L) :
    firstDiff x y < L := by
  by_contra h
  apply hres
  rw [PiNat.res_eq_res]
  intro m hm
  exact binaryCode_apply_eq_of_lt_firstDiff
    (hm.trans_le (le_of_not_gt h))

/-- A first difference inside the restriction length makes the restrictions
different. -/
theorem res_ne_of_firstDiff_lt {x y : HamelIndex} {L : ℕ}
    (hxy : x ≠ y) (hfd : firstDiff x y < L) :
    PiNat.res (binaryCode x) L ≠ PiNat.res (binaryCode y) L := by
  intro hres
  have heq := PiNat.res_eq_res.mp hres hfd
  exact binaryCode_apply_firstDiff_ne hxy heq

theorem res_separation_injOn (s : Finset HamelIndex) :
    Set.InjOn (fun x ↦ PiNat.res (binaryCode x) (separationLength s))
      (s : Set HamelIndex) := by
  intro x hx y hy hres
  by_contra hxy
  exact res_ne_of_firstDiff_lt hxy
    (firstDiff_lt_separationLength (by simpa using hx) (by simpa using hy)) hres

/-! ## Uniform-prefix thinning -/

/-- The common data retained when thinning a fixed-size family: a restriction
length, followed by one finite binary prefix for each ordered coordinate. -/
abbrev PrefixRecord (n : ℕ) := ℕ × (Fin n → List Bool)

instance prefixRecord_countable (n : ℕ) : Countable (PrefixRecord n) :=
  inferInstance

def prefixRecord {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (i : ι) : PrefixRecord n :=
  let L := separationLength (F i)
  (L, fun j ↦ PiNat.res (binaryCode (finsetCoord F hcard i j)) L)

/-- An uncountable subfamily on which the separating restriction length and
all coordinate prefixes are constant. -/
structure UniformPrefixWitness {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) where
  carrier : Set ι
  uncountable : ¬ carrier.Countable
  L : ℕ
  prefixes : Fin n → List Bool
  prefixes_injective : Injective prefixes
  prefix_eq : ∀ i ∈ carrier, ∀ j,
    PiNat.res (binaryCode (finsetCoord F hcard i j)) L = prefixes j

/-- Thin an uncountable fixed-cardinality family to a uniform-prefix witness. -/
theorem exists_uniformPrefixWitness {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ W : UniformPrefixWitness F hcard, W.carrier ⊆ I := by
  let recordOf : ι → PrefixRecord n := prefixRecord F hcard
  obtain ⟨r, hr⟩ := uncountable_fiber_of_countable_range recordOf hI
  let J : Set ι := {i ∈ I | recordOf i = r}
  have hJ : ¬ J.Countable := hr
  have hJne : J.Nonempty := by
    by_contra hn
    exact hJ (Set.not_nonempty_iff_eq_empty.mp hn ▸ Set.countable_empty)
  obtain ⟨i₀, hi₀J⟩ := hJne
  let L := r.1
  let p : Fin n → List Bool := r.2
  have hrecord₀ : recordOf i₀ = r := hi₀J.2
  have hL : separationLength (F i₀) = L := congrArg Prod.fst hrecord₀
  have hp : ∀ j, PiNat.res (binaryCode (finsetCoord F hcard i₀ j)) L = p j := by
    intro j
    have h := congrFun (congrArg Prod.snd hrecord₀) j
    simpa [recordOf, prefixRecord, L, p, hL] using h
  have hpinj : Injective p := by
    intro j k hjk
    apply finsetCoord_injective F hcard i₀
    apply res_separation_injOn (F i₀)
    · exact finsetCoord_mem F hcard i₀ j
    · exact finsetCoord_mem F hcard i₀ k
    change PiNat.res (binaryCode (finsetCoord F hcard i₀ j))
        (separationLength (F i₀)) =
      PiNat.res (binaryCode (finsetCoord F hcard i₀ k))
        (separationLength (F i₀))
    rw [hL, hp j, hp k, hjk]
  refine ⟨{
    carrier := J
    uncountable := hJ
    L := L
    prefixes := p
    prefixes_injective := hpinj
    prefix_eq := ?_ }, fun _ hi ↦ hi.1⟩
  intro i hi j
  have hrecord : recordOf i = r := hi.2
  have hLi : separationLength (F i) = L := congrArg Prod.fst hrecord
  have h := congrFun (congrArg Prod.snd hrecord) j
  simpa [recordOf, prefixRecord, L, p, hLi] using h

/-- Distinct ordered coordinates, even in two different members of the
uniform family, split before the common restriction length. -/
theorem UniformPrefixWitness.crossCoordinate_firstDiff_lt {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) {i k : ι} (hi : i ∈ W.carrier)
    (hk : k ∈ W.carrier) {j l : Fin n} (hjl : j ≠ l) :
    firstDiff (finsetCoord F hcard i j) (finsetCoord F hcard k l) < W.L := by
  apply firstDiff_lt_of_res_ne
  rw [W.prefix_eq i hi j, W.prefix_eq k hk l]
  exact W.prefixes_injective.ne hjl

end

end Erdos965

/-! ## Upstream module: CoordinateNormalize.lean -/

open Function Set


namespace Erdos965
namespace FiniteColoring

variable {ι : Type u}

/-! ## Simultaneous normalization of finitely many coordinates -/

/-- A coordinate is normalized on `J` if it is constant there, or if it is
injective and every one of its strict initial segments (for the fixed
well-order) is countable. -/
def CoordinateNormalized (p : ι → HamelIndex) (J : Set ι) : Prop :=
  (∃ b, ∀ x ∈ J, p x = b) ∨
    InjOn p J ∧ ∀ x ∈ J, {y ∈ J | WellOrderingRel (p y) (p x)}.Countable

namespace CoordinateNormalized

/-- Coordinate normalization is preserved when the index set is thinned. -/
theorem mono {p : ι → HamelIndex} {J K : Set ι}
    (h : CoordinateNormalized p J) (hKJ : K ⊆ J) :
    CoordinateNormalized p K := by
  rcases h with hconst | ⟨hinj, hlower⟩
  · exact Or.inl ⟨hconst.choose, fun x hx ↦ hconst.choose_spec x (hKJ hx)⟩
  · refine Or.inr ⟨hinj.mono hKJ, ?_⟩
    intro x hx
    refine (hlower x (hKJ hx)).mono ?_
    intro y hy
    exact ⟨hKJ hy.1, hy.2⟩

end CoordinateNormalized

/-- Simultaneous coordinate normalization on an uncountable thinning of an
initial index set. -/
structure CoordinateNormalization {n : ℕ} (p : Fin n → ι → HamelIndex)
    (I J : Set ι) : Prop where
  subset : J ⊆ I
  uncountable : ¬ J.Countable
  normalized : ∀ j, CoordinateNormalized (p j) J

namespace CoordinateNormalization

/-- A simultaneous normalization remains valid after any further
uncountable thinning. -/
theorem mono {n : ℕ} {p : Fin n → ι → HamelIndex} {I J K : Set ι}
    (h : CoordinateNormalization p I J) (hKJ : K ⊆ J)
    (hKunc : ¬ K.Countable) : CoordinateNormalization p I K where
  subset := hKJ.trans h.subset
  uncountable := hKunc
  normalized j := (h.normalized j).mono hKJ

end CoordinateNormalization

/-- Normalize the coordinates in a prescribed finite set.  This is the
inductive engine used for all coordinates below. -/
private theorem exists_normalized_on_finset {n : ℕ}
    (p : Fin n → ι → HamelIndex) (s : Finset (Fin n))
    (I : Set ι) (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ∀ j ∈ s, CoordinateNormalized (p j) J := by
  classical
  induction s using Finset.induction_on generalizing I with
  | empty =>
      exact ⟨I, Set.Subset.rfl, hI, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨J, hJI, hJunc, hJnorm⟩ := ih I hI
      obtain ⟨K, hKJ, hKunc, hKcase⟩ :=
        uncountable_constant_or_injective (p a) hJunc
      rcases hKcase with hconst | hinj
      · refine ⟨K, hKJ.trans hJI, hKunc, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Or.inl hconst
        · exact (hJnorm j hj).mono hKJ
      · obtain ⟨L, hLK, hLunc, hlower⟩ :=
          uncountable_lowerNormalized (r := WellOrderingRel) (p a) hKunc hinj
        refine ⟨L, hLK.trans (hKJ.trans hJI), hLunc, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Or.inr ⟨hinj.mono hLK, hlower⟩
        · exact (hJnorm j hj).mono (hLK.trans hKJ)

/-- Any finite family of Hamel-index-valued coordinate maps can be
simultaneously normalized on an uncountable subset. -/
theorem exists_coordinateNormalization {n : ℕ}
    (p : Fin n → ι → HamelIndex) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ J, CoordinateNormalization p I J := by
  obtain ⟨J, hJI, hJunc, hnorm⟩ :=
    exists_normalized_on_finset p Finset.univ I hI
  exact ⟨J, hJI, hJunc, fun j ↦ hnorm j (Finset.mem_univ j)⟩

/-! ## Ordered coordinates of a uniform finite-set family -/

/-- The `j`th member, in ordinary increasing order, of a uniformly
`n`-element family of finite sets. -/
noncomputable def coordinate {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (j : Fin n) (i : ι) : HamelIndex :=
  finsetCoord F hcard i j

theorem coordinate_mem {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (j : Fin n) (i : ι) :
    coordinate F hcard j i ∈ F i := by
  exact finsetCoord_mem F hcard i j

theorem coordinate_strictMono {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    StrictMono (fun j : Fin n ↦ coordinate F hcard j i) := by
  exact finsetCoord_strictMono F hcard i

/-- The ordered coordinate of a family whose cardinality is known only on
`I`.  Its value outside `I` is irrelevant; all normalization conclusions are
on subsets of `I`. -/
noncomputable def coordinateWithin {n : ℕ} (F : ι → Finset HamelIndex)
    (I : Set ι) (hcard : ∀ i ∈ I, (F i).card = n)
    (j : Fin n) (i : ι) : HamelIndex := by
  classical
  exact if hi : i ∈ I then (F i).orderEmbOfFin (hcard i hi) j
    else hamelBasis.index_nonempty.some

theorem coordinateWithin_of_mem {n : ℕ} (F : ι → Finset HamelIndex)
    (I : Set ι) (hcard : ∀ i ∈ I, (F i).card = n)
    (j : Fin n) {i : ι} (hi : i ∈ I) :
    coordinateWithin F I hcard j i = (F i).orderEmbOfFin (hcard i hi) j := by
  simp only [coordinateWithin, dif_pos hi]

theorem coordinateWithin_mem {n : ℕ} (F : ι → Finset HamelIndex)
    (I : Set ι) (hcard : ∀ i ∈ I, (F i).card = n)
    (j : Fin n) {i : ι} (hi : i ∈ I) :
    coordinateWithin F I hcard j i ∈ F i := by
  rw [coordinateWithin_of_mem F I hcard j hi]
  exact Finset.orderEmbOfFin_mem (F i) (hcard i hi) j

/-- A uniform finite-set family admits an uncountable thinning on which
each ordered coordinate is constant or injective and lower-normalized in
`WellOrderingRel`.  This is the main interface for the finite-set colouring
argument. -/
theorem exists_coordinateNormalization_of_uniformCard {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    {I : Set ι} (hI : ¬ I.Countable) :
    ∃ J, CoordinateNormalization
      (fun j i ↦ finsetCoord F hcard i j) I J :=
  exists_coordinateNormalization (fun j i ↦ finsetCoord F hcard i j) hI

/-- Relative-cardinality version of
`exists_coordinateNormalization_of_uniformCard`. -/
theorem exists_coordinateNormalization_of_uniformCardOn {n : ℕ}
    (F : ι → Finset HamelIndex) {I : Set ι}
    (hcard : ∀ i ∈ I, (F i).card = n) (hI : ¬ I.Countable) :
    ∃ J, CoordinateNormalization
      (fun j ↦ coordinateWithin F I hcard j) I J :=
  exists_coordinateNormalization (fun j ↦ coordinateWithin F I hcard j) hI

/-- Normalize all ordered coordinates of a uniform-prefix witness while
remaining inside its carrier.  Thus every prefix identity furnished by `W`
is preserved automatically. -/
theorem exists_coordinateNormalization_of_uniformPrefixWitness {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) :
    ∃ J, CoordinateNormalization
      (fun j i ↦ finsetCoord F hcard i j) W.carrier J :=
  Erdos965.FiniteColoring.exists_coordinateNormalization
    (fun (j : Fin n) (i : ι) ↦ finsetCoord F hcard i j) W.uncountable

end FiniteColoring
end Erdos965

/-! ## Upstream module: CylinderSplit.lean -/

open Function Set


namespace Erdos965

variable {ι : Type u}

/-! ## Countable exceptional prefix fibres -/

/-- The first `n` bits of the rational-cut code of a Hamel index. -/
noncomputable def codePrefix (n : ℕ) (x : HamelIndex) : Fin n → Bool :=
  fun i ↦ binaryCode x i

/-- Points which belong to a countable relative prefix fibre at some finite
depth.  There are only countably many depths and finitely many prefixes at
each depth, so this is a countable exceptional set. -/
def badPrefixPoints (p : ι → HamelIndex) (I : Set ι) : Set ι :=
  {x ∈ I | ∃ n, {y ∈ I | codePrefix n (p y) = codePrefix n (p x)}.Countable}

theorem badPrefixPoints_countable (p : ι → HamelIndex) (I : Set ι) :
    (badPrefixPoints p I).Countable := by
  classical
  refine (Set.countable_iUnion fun n ↦
    countable_union_of_countable_fibers
      (fun x ↦ codePrefix n (p x)) I).mono ?_
  rintro x ⟨hxI, n, hn⟩
  exact Set.mem_iUnion.2 ⟨n, hxI, hn⟩

/-- A point outside `badPrefixPoints` has an uncountable relative prefix
fibre at every finite depth. -/
theorem prefix_fiber_uncountable_of_not_bad (p : ι → HamelIndex) (I : Set ι)
    {x : ι} (hxI : x ∈ I) (hx : x ∉ badPrefixPoints p I) (n : ℕ) :
    ¬ {y ∈ I | codePrefix n (p y) = codePrefix n (p x)}.Countable := by
  intro h
  exact hx ⟨hxI, n, h⟩

/-! ## Prefixes determine the split level and ordinary orientation -/

/-- If `x` and `y` have the same length-`N+1` prefixes as two distinct
points `a` and `b`, where `N` is the first difference of `a` and `b`, then
`N` is also the first difference of `x` and `y`. -/
theorem firstDiff_eq_of_codePrefix_succ_eq {x y a b : HamelIndex}
    (hab : a ≠ b)
    (hx : codePrefix (firstDiff a b + 1) x = codePrefix (firstDiff a b + 1) a)
    (hy : codePrefix (firstDiff a b + 1) y = codePrefix (firstDiff a b + 1) b) :
    firstDiff x y = firstDiff a b := by
  let N := firstDiff a b
  have hxN : binaryCode x N = binaryCode a N :=
    congrFun hx ⟨N, by omega⟩
  have hyN : binaryCode y N = binaryCode b N :=
    congrFun hy ⟨N, by omega⟩
  have habN : binaryCode a N ≠ binaryCode b N := by
    simpa only [N] using binaryCode_apply_firstDiff_ne hab
  have hxyN : binaryCode x N ≠ binaryCode y N := by
    intro h
    exact habN (hxN.symm.trans (h.trans hyN))
  have hcodeNe : binaryCode x ≠ binaryCode y := by
    intro h
    exact hxyN (congrFun h N)
  have hge : N ≤ firstDiff x y := by
    rw [firstDiff]
    refine (PiNat.mem_cylinder_iff_le_firstDiff hcodeNe N).1 ?_
    intro i hi
    have hxi : binaryCode x i = binaryCode a i :=
      congrFun hx ⟨i, by omega⟩
    have hyi : binaryCode y i = binaryCode b i :=
      congrFun hy ⟨i, by omega⟩
    calc
      binaryCode x i = binaryCode a i := hxi
      _ = binaryCode b i := binaryCode_apply_eq_of_lt_firstDiff hi
      _ = binaryCode y i := hyi.symm
  have hle : firstDiff x y ≤ N := by
    by_contra h
    exact hxyN (binaryCode_apply_eq_of_lt_firstDiff (Nat.lt_of_not_ge h))
  exact le_antisymm hle hge

/-- The same prefix hypotheses also preserve ordinary orientation. -/
theorem lt_of_codePrefix_succ_eq_of_lt {x y a b : HamelIndex} (hab : a < b)
    (hx : codePrefix (firstDiff a b + 1) x = codePrefix (firstDiff a b + 1) a)
    (hy : codePrefix (firstDiff a b + 1) y = codePrefix (firstDiff a b + 1) b) :
    x < y := by
  let N := firstDiff a b
  have hxN : binaryCode x N = binaryCode a N :=
    congrFun hx ⟨N, by omega⟩
  have hyN : binaryCode y N = binaryCode b N :=
    congrFun hy ⟨N, by omega⟩
  have habBits : binaryCode a N = false ∧ binaryCode b N = true := by
    simpa only [N] using binaryCode_firstDiff_of_lt hab
  have hxBit : binaryCode x N = false := hxN.trans habBits.1
  have hyBit : binaryCode y N = true := hyN.trans habBits.2
  have hxLe : (x : ℝ) ≤ ((ratEnum N : ℚ) : ℝ) := by
    have : ¬ (((ratEnum N : ℚ) : ℝ) < (x : ℝ)) := by
      change decide (((ratEnum N : ℚ) : ℝ) < (x : ℝ)) = false at hxBit
      exact of_decide_eq_false hxBit
    exact le_of_not_gt this
  have hyLt : (((ratEnum N : ℚ) : ℝ) < (y : ℝ)) := by
    change decide (((ratEnum N : ℚ) : ℝ) < (y : ℝ)) = true at hyBit
    exact of_decide_eq_true hyBit
  exact hxLe.trans_lt hyLt

/-! ## The uncountable binary-cylinder split -/

/-- Two uncountable subfamilies on which `p` is injective can be thinned to
uncountable subfamilies separated by one fixed binary split.  Across the two
subfamilies the first-difference level is constant and the ordinary order has
one fixed orientation.

This is the form needed when identifying the critical pair in a structured
union of finite supports. -/
theorem uncountable_cylinder_split (p : ι → HamelIndex) {D U V : Set ι}
    (hp : InjOn p D) (hUD : U ⊆ D) (hVD : V ⊆ D)
    (hU : ¬ U.Countable) (hV : ¬ V.Countable) :
    ∃ (U' V' : Set ι) (N : ℕ),
      U' ⊆ U ∧ V' ⊆ V ∧ ¬ U'.Countable ∧ ¬ V'.Countable ∧
        (∀ u ∈ U', ∀ v ∈ V', firstDiff (p u) (p v) = N) ∧
        ((∀ u ∈ U', ∀ v ∈ V', p u < p v) ∨
          ∀ u ∈ U', ∀ v ∈ V', p v < p u) := by
  classical
  let BU := badPrefixPoints p U
  let BV := badPrefixPoints p V
  have hBU : BU.Countable := badPrefixPoints_countable p U
  have hBV : BV.Countable := badPrefixPoints_countable p V
  obtain ⟨u₀, hu₀U, hu₀good⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable hU hBU
  obtain ⟨v₀, hv₀V, hv₀good⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable hV
      (hBV.union (Set.countable_singleton u₀))
  have hv₀BV : v₀ ∉ BV := by
    intro hv
    exact hv₀good (Or.inl hv)
  have hv₀ne : v₀ ≠ u₀ := by
    intro h
    exact hv₀good (Or.inr h)
  have hpne : p u₀ ≠ p v₀ := by
    intro h
    exact hv₀ne (hp (hVD hv₀V) (hUD hu₀U) h.symm)
  let N := firstDiff (p u₀) (p v₀)
  let U' : Set ι :=
    {u ∈ U | codePrefix (N + 1) (p u) = codePrefix (N + 1) (p u₀)}
  let V' : Set ι :=
    {v ∈ V | codePrefix (N + 1) (p v) = codePrefix (N + 1) (p v₀)}
  have hU'sub : U' ⊆ U := fun _ h ↦ h.1
  have hV'sub : V' ⊆ V := fun _ h ↦ h.1
  have hU' : ¬ U'.Countable := by
    simpa only [U', N, BU] using
      prefix_fiber_uncountable_of_not_bad p U hu₀U hu₀good (N + 1)
  have hV' : ¬ V'.Countable := by
    simpa only [V', N, BV] using
      prefix_fiber_uncountable_of_not_bad p V hv₀V hv₀BV (N + 1)
  have hdiff : ∀ u ∈ U', ∀ v ∈ V', firstDiff (p u) (p v) = N := by
    intro u hu v hv
    simpa only [N] using
      firstDiff_eq_of_codePrefix_succ_eq hpne hu.2 hv.2
  refine ⟨U', V', N, hU'sub, hV'sub, hU', hV', hdiff, ?_⟩
  rcases lt_or_gt_of_ne hpne with huv | hvu
  · exact Or.inl fun u hu v hv ↦ by
      exact lt_of_codePrefix_succ_eq_of_lt huv hu.2 hv.2
  · exact Or.inr fun u hu v hv ↦ by
      have hvPrefix :
          codePrefix (firstDiff (p v₀) (p u₀) + 1) (p v) =
            codePrefix (firstDiff (p v₀) (p u₀) + 1) (p v₀) := by
        rw [firstDiff_comm (p v₀) (p u₀)]
        simpa only [N] using hv.2
      have huPrefix :
          codePrefix (firstDiff (p v₀) (p u₀) + 1) (p u) =
            codePrefix (firstDiff (p v₀) (p u₀) + 1) (p u₀) := by
        rw [firstDiff_comm (p v₀) (p u₀)]
        simpa only [N] using hu.2
      exact lt_of_codePrefix_succ_eq_of_lt hvu hvPrefix huPrefix

end Erdos965

/-! ## Upstream module: DeltaSystem.lean -/

open Function Set


namespace Erdos965

variable {ι : Type u} {α : Type v}

private lemma exists_uncountable_fiber {β : Type*} [Countable β]
    (f : ι → β) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ b, ¬ {i ∈ I | f i = b}.Countable := by
  by_contra! h
  apply hI
  refine (Set.countable_iUnion h).mono ?_
  intro i hi
  exact Set.mem_iUnion.2 ⟨f i, hi, rfl⟩

private lemma exists_maximal_pairwiseDisjoint [DecidableEq α]
    (F : ι → Finset α) (I : Set ι) :
    ∃ J, Maximal (fun J : Set ι ↦ J ⊆ I ∧ J.Pairwise fun i j ↦ Disjoint (F i) (F j)) J := by
  let P : Set (Set ι) := {J | J ⊆ I ∧ J.Pairwise fun i j ↦ Disjoint (F i) (F j)}
  simpa only [P, Set.mem_ofPred_eq] using
    (zorn_subset P fun c hc hchain ↦ by
      refine ⟨⋃₀ c, ?_, fun J hJ ↦ Set.subset_sUnion_of_mem hJ⟩
      constructor
      · exact Set.sUnion_subset fun J hJ ↦ (hc hJ).1
      · rintro i ⟨Ji, hJi, hiJi⟩ j ⟨Jj, hJj, hjJj⟩ hij
        rcases hchain.total hJi hJj with hsub | hsub
        · exact (hc hJj).2 (hsub hiJi) hjJj hij
        · exact (hc hJi).2 hiJi (hsub hjJj) hij)

/-- If every point-star of a family of nonempty finite sets is countable, then an
uncountable index set has an uncountable pairwise-disjoint subset. -/
private lemma exists_uncountable_pairwiseDisjoint [DecidableEq α]
    (F : ι → Finset α) {I : Set ι} (hI : ¬ I.Countable)
    (hne : ∀ i ∈ I, (F i).Nonempty)
    (hstar : ∀ a : α, {i ∈ I | a ∈ F i}.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧ J.Pairwise fun i j ↦ Disjoint (F i) (F j) := by
  obtain ⟨J, hJmax⟩ := exists_maximal_pairwiseDisjoint F I
  refine ⟨J, hJmax.prop.1, ?_, hJmax.prop.2⟩
  intro hJcount
  let _ : Countable J := hJcount.to_subtype
  let U : Set α := ⋃ j : J, (F j : Set α)
  have hUcount : U.Countable := by
    dsimp [U]
    exact Set.countable_iUnion fun j : J ↦ (F j).countable_toSet
  have hintersects : ∀ i ∈ I, ∃ j ∈ J, ¬ Disjoint (F i) (F j) := by
    intro i hi
    by_contra! hdisj
    have hins : insert i J ⊆ I ∧
        (insert i J).Pairwise fun x y ↦ Disjoint (F x) (F y) := by
      constructor
      · exact Set.insert_subset hi hJmax.prop.1
      · rw [Set.pairwise_insert_of_symm]
        exact ⟨hJmax.prop.2, fun j hj _ ↦ hdisj j hj⟩
    have hiJ : i ∈ J := hJmax.mem_of_prop_insert hins
    exact (hne i hi).ne_empty ((Finset.disjoint_self_iff_empty (F i)).mp (hdisj i hiJ))
  have hsub : I ⊆ ⋃ a : U, {i ∈ I | (a : α) ∈ F i} := by
    intro i hi
    obtain ⟨j, hjJ, hij⟩ := hintersects i hi
    rw [Finset.not_disjoint_iff] at hij
    obtain ⟨a, hai, haj⟩ := hij
    refine Set.mem_iUnion.2 ⟨⟨a, ?_⟩, hi, hai⟩
    exact Set.mem_iUnion.2 ⟨⟨j, hjJ⟩, haj⟩
  apply hI
  let _ : Countable U := hUcount.to_subtype
  refine (Set.countable_iUnion fun a : U ↦ ?_).mono hsub
  exact (hstar a).mono fun i hi ↦ hi

private theorem deltaSystem_uniform [DecidableEq α] : ∀ n : ℕ,
    ∀ (F : ι → Finset α) (I : Set ι),
      (∀ i ∈ I, (F i).card = n) → ¬ I.Countable →
      ∃ J ⊆ I, ¬ J.Countable ∧ ∃ r : Finset α,
        ∀ ⦃i⦄, i ∈ J → ∀ ⦃j⦄, j ∈ J → i ≠ j → F i ∩ F j = r
  | 0, F, I, hcard, hI => by
      refine ⟨I, Set.Subset.rfl, hI, ∅, ?_⟩
      intro i hi j hj hij
      have hFi : F i = ∅ := Finset.card_eq_zero.mp (hcard i hi)
      simp [hFi]
  | n + 1, F, I, hcard, hI => by
      classical
      by_cases hstar : ∃ a : α, ¬ {i ∈ I | a ∈ F i}.Countable
      · obtain ⟨a, ha⟩ := hstar
        let Ia : Set ι := {i ∈ I | a ∈ F i}
        let G : ι → Finset α := fun i ↦ (F i).erase a
        have hGcard : ∀ i ∈ Ia, (G i).card = n := by
          intro i hi
          simp only [Ia, Set.mem_ofPred_eq] at hi
          dsimp [G]
          have herase := Finset.card_erase_add_one hi.2
          rw [hcard i hi.1] at herase
          omega
        obtain ⟨J, hJIa, hJunc, r, hr⟩ :=
          deltaSystem_uniform n G Ia hGcard ha
        refine ⟨J, hJIa.trans fun i hi ↦ hi.1, hJunc, insert a r, ?_⟩
        intro i hi j hj hij
        have hai : a ∈ F i := (hJIa hi).2
        have haj : a ∈ F j := (hJIa hj).2
        have hcore : G i ∩ G j = r := hr hi hj hij
        rw [← Finset.insert_erase hai, ← Finset.insert_erase haj]
        rw [← Finset.insert_inter_distrib]
        exact congrArg (insert a) hcore
      · push Not at hstar
        have hne : ∀ i ∈ I, (F i).Nonempty := by
          intro i hi
          apply Finset.card_pos.mp
          rw [hcard i hi]
          omega
        obtain ⟨J, hJI, hJunc, hJdisj⟩ :=
          exists_uncountable_pairwiseDisjoint F hI hne hstar
        refine ⟨J, hJI, hJunc, ∅, ?_⟩
        intro i hi j hj hij
        exact Finset.disjoint_iff_inter_eq_empty.mp (hJdisj hi hj hij)

/-- Every uncountably indexed family of finite sets has an uncountable
Δ-subsystem. The family need not be injective. -/
theorem exists_uncountable_deltaSystem [DecidableEq α]
    (F : ι → Finset α) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧ ∃ r : Finset α,
      ∀ ⦃i⦄, i ∈ J → ∀ ⦃j⦄, j ∈ J → i ≠ j → F i ∩ F j = r := by
  obtain ⟨n, hn⟩ := exists_uncountable_fiber (fun i ↦ (F i).card) hI
  let In : Set ι := {i ∈ I | (F i).card = n}
  obtain ⟨J, hJIn, hJunc, r, hr⟩ :=
    deltaSystem_uniform n F In (fun _ hi ↦ hi.2) hn
  exact ⟨J, hJIn.trans fun _ hi ↦ hi.1, hJunc, r, hr⟩

/-- Set-of-finsets formulation of the uncountable Δ-system lemma. -/
theorem exists_uncountable_deltaSystem_set [DecidableEq α]
    {S : Set (Finset α)} (hS : ¬ S.Countable) :
    ∃ T ⊆ S, ¬ T.Countable ∧ ∃ r : Finset α,
      T.Pairwise fun s t ↦ s ∩ t = r := by
  obtain ⟨T, hTS, hTunc, r, hr⟩ :=
    exists_uncountable_deltaSystem (fun s : Finset α ↦ s) hS
  refine ⟨T, hTS, hTunc, r, ?_⟩
  intro s hs t ht hst
  exact hr hs ht hst

end Erdos965

/-! ## Upstream module: FiniteColoring.lean -/

open Function Set


namespace Erdos965

noncomputable section

/-! ## Simultaneous splitting of the varying coordinates -/

structure FiniteSplitWitness {ι : Type u} {n : ℕ}
    (p : Fin n → ι → HamelIndex) (D : Set ι) (M : Finset (Fin n)) where
  left : Set ι
  right : Set ι
  left_subset : left ⊆ D
  right_subset : right ⊆ D
  left_uncountable : ¬ left.Countable
  right_uncountable : ¬ right.Countable
  level : Fin n → ℕ
  split : ∀ j ∈ M,
    (∀ a ∈ left, ∀ b ∈ right, firstDiff (p j a) (p j b) = level j) ∧
      ((∀ a ∈ left, ∀ b ∈ right, p j a < p j b) ∨
        ∀ a ∈ left, ∀ b ∈ right, p j b < p j a)

theorem exists_finiteSplitWitness {ι : Type u} {n : ℕ}
    (p : Fin n → ι → HamelIndex) (D : Set ι) (M : Finset (Fin n))
    (hD : ¬ D.Countable) (hinj : ∀ j ∈ M, InjOn (p j) D) :
    Nonempty (FiniteSplitWitness p D M) := by
  classical
  induction M using Finset.induction_on with
  | empty =>
      exact ⟨{
        left := D
        right := D
        left_subset := Set.Subset.rfl
        right_subset := Set.Subset.rfl
        left_uncountable := hD
        right_uncountable := hD
        level := fun _ ↦ 0
        split := by simp }⟩
  | @insert j M hjM ih =>
      have hinjM : ∀ k ∈ M, InjOn (p k) D := by
        intro k hk
        exact hinj k (Finset.mem_insert_of_mem hk)
      obtain ⟨W⟩ := ih hinjM
      obtain ⟨U, V, N, hUW, hVW, hUunc, hVunc, hdiff, hord⟩ :=
        uncountable_cylinder_split (p j) (hinj j (Finset.mem_insert_self j M))
          W.left_subset W.right_subset W.left_uncountable W.right_uncountable
      refine ⟨{
        left := U
        right := V
        left_subset := hUW.trans W.left_subset
        right_subset := hVW.trans W.right_subset
        left_uncountable := hUunc
        right_uncountable := hVunc
        level := Function.update W.level j N
        split := ?_ }⟩
      intro k hk
      rw [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · simpa using And.intro hdiff hord
      · obtain ⟨hkdiff, hkord⟩ := W.split k hk
        have hkj : k ≠ j := fun h ↦ hjM (h ▸ hk)
        constructor
        · simpa [Function.update, hkj] using
            (fun a ha b hb ↦ hkdiff a (hUW ha) b (hVW hb))
        · rcases hkord with hkord | hkord
          · exact Or.inl fun a ha b hb ↦ hkord a (hUW ha) b (hVW hb)
          · exact Or.inr fun a ha b hb ↦ hkord a (hUW ha) b (hVW hb)

/-! ## Structural lemmas for one uniform family -/

private theorem commonPrefix_crossCoordinate_lt {ι : Type u} {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) {a b : ι}
    (ha : a ∈ W.carrier) (hb : b ∈ W.carrier) {j k : Fin n} (hjk : j < k) :
    finsetCoord F hcard a j < finsetCoord F hcard b k := by
  let x := finsetCoord F hcard a j
  let y := finsetCoord F hcard a k
  let x' := finsetCoord F hcard a j
  let y' := finsetCoord F hcard b k
  have hxy : x < y := finsetCoord_strictMono F hcard a hjk
  have hN : firstDiff x y < W.L :=
    W.crossCoordinate_firstDiff_lt F hcard ha ha hjk.ne
  have hbits := binaryCode_firstDiff_of_lt hxy
  have hy' : binaryCode y' (firstDiff x y) = binaryCode y (firstDiff x y) := by
    apply PiNat.res_eq_res.mp
      ((W.prefix_eq b hb k).trans (W.prefix_eq a ha k).symm)
    exact hN
  exact lt_of_binaryCode_eq_false_true hbits.1 (hy'.trans hbits.2)

theorem finset_eq_of_all_coords_eq {ι : Type u} {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n) {a b : ι}
    (h : ∀ j, finsetCoord F hcard a j = finsetCoord F hcard b j) :
    F a = F b := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (F a : Set HamelIndex) := hx
    rw [← range_finsetCoord F hcard a] at hx'
    obtain ⟨j, rfl⟩ := hx'
    rw [h j]
    exact finsetCoord_mem F hcard b j
  · intro hx
    have hx' : x ∈ (F b : Set HamelIndex) := hx
    rw [← range_finsetCoord F hcard b] at hx'
    obtain ⟨j, rfl⟩ := hx'
    rw [← h j]
    exact finsetCoord_mem F hcard a j

theorem criticalPair_crossUnion {ι : Type u} {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) {D : Set ι} {M : Finset (Fin n)}
    (hDW : D ⊆ W.carrier)
    (hconst : ∀ j ∉ M, ∃ c, ∀ i ∈ D, finsetCoord F hcard i j = c)
    (S : FiniteSplitWitness (fun j i ↦ finsetCoord F hcard i j) D M)
    {jstar : Fin n} (hjstarM : jstar ∈ M)
    (hlevel_le : ∀ j ∈ M, S.level j ≤ S.level jstar)
    (hlevel_ge : ∀ j ∈ M, W.L ≤ S.level j)
    (hjstarleast : ∀ j ∈ M, S.level j = S.level jstar → jstar ≤ j)
    {a b : ι} (ha : a ∈ S.left) (hb : b ∈ S.right) :
    criticalPair (F a ∪ F b) =
      (min (finsetCoord F hcard a jstar) (finsetCoord F hcard b jstar),
        max (finsetCoord F hcard a jstar) (finsetCoord F hcard b jstar)) := by
  classical
  let p : Fin n → ι → HamelIndex := fun j i ↦ finsetCoord F hcard i j
  let m := S.level jstar
  have haD : a ∈ D := S.left_subset ha
  have hbD : b ∈ D := S.right_subset hb
  have haW : a ∈ W.carrier := hDW haD
  have hbW : b ∈ W.carrier := hDW hbD
  have hLm : W.L ≤ m := hlevel_ge jstar hjstarM
  have hjstarsplit := S.split jstar hjstarM
  have hjstardiff : firstDiff (p jstar a) (p jstar b) = m :=
    hjstarsplit.1 a ha b hb
  have hcoord : ∀ {z}, z ∈ F a ∪ F b →
      ∃ j, z = p j a ∨ z = p j b := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · have hz' : z ∈ (F a : Set HamelIndex) := hz
      rw [← range_finsetCoord F hcard a] at hz'
      obtain ⟨j, rfl⟩ := hz'
      exact ⟨j, Or.inl rfl⟩
    · have hz' : z ∈ (F b : Set HamelIndex) := hz
      rw [← range_finsetCoord F hcard b] at hz'
      obtain ⟨j, rfl⟩ := hz'
      exact ⟨j, Or.inr rfl⟩
  have hcross_lt : ∀ {r s : ι}, r ∈ D → s ∈ D →
      ∀ {j k : Fin n}, j ≠ k → firstDiff (p j r) (p k s) < W.L := by
    intro r s hr hs j k hjk
    exact W.crossCoordinate_firstDiff_lt F hcard (hDW hr) (hDW hs) hjk
  have hbound : ∀ {z}, z ∈ F a ∪ F b → ∀ {w}, w ∈ F a ∪ F b → z ≠ w →
      firstDiff z w ≤ m := by
    intro z hz w hw hzw
    obtain ⟨j, hzj⟩ := hcoord hz
    obtain ⟨k, hwk⟩ := hcoord hw
    rcases hzj with rfl | rfl <;> rcases hwk with rfl | rfl
    · by_cases hjk : j = k
      · subst k
        exact (hzw rfl).elim
      · exact (hcross_lt haD haD hjk).le.trans hLm
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · exact (S.split j hjM).1 a ha b hb ▸ hlevel_le j hjM
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw ((hc a haD).trans (hc b hbD).symm)).elim
      · exact (hcross_lt haD hbD hjk).le.trans hLm
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · rw [firstDiff_comm]
          exact (S.split j hjM).1 a ha b hb ▸ hlevel_le j hjM
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw ((hc b hbD).trans (hc a haD).symm)).elim
      · exact (hcross_lt hbD haD hjk).le.trans hLm
    · by_cases hjk : j = k
      · subst k
        exact (hzw rfl).elim
      · exact (hcross_lt hbD hbD hjk).le.trans hLm
  have hlo_le_of_max : ∀ {z}, z ∈ F a ∪ F b → ∀ {w}, w ∈ F a ∪ F b →
      z < w → firstDiff z w = m →
      min (p jstar a) (p jstar b) ≤ z := by
    intro z hz w hw hzw hzwm
    obtain ⟨j, hzj⟩ := hcoord hz
    obtain ⟨k, hwk⟩ := hcoord hw
    have hcoord_le_a {j : Fin n} (hjM : j ∈ M) (hjm : S.level j = m) :
        min (p jstar a) (p jstar b) ≤ p j a := by
      have hjstarj : jstar ≤ j := hjstarleast j hjM hjm
      rcases hjstarj.eq_or_lt with hEq | hlt
      · subst j
        exact min_le_left _ _
      · exact (min_le_left _ _).trans
          (by simpa only [p] using
            (commonPrefix_crossCoordinate_lt F hcard W haW haW hlt).le)
    have hcoord_le_b {j : Fin n} (hjM : j ∈ M) (hjm : S.level j = m) :
        min (p jstar a) (p jstar b) ≤ p j b := by
      have hjstarj : jstar ≤ j := hjstarleast j hjM hjm
      rcases hjstarj.eq_or_lt with hEq | hlt
      · subst j
        exact min_le_right _ _
      · exact (min_le_left _ _).trans
          (by simpa only [p] using
            (commonPrefix_crossCoordinate_lt F hcard W haW hbW hlt).le)
    rcases hzj with rfl | rfl <;> rcases hwk with rfl | rfl
    · by_cases hjk : j = k
      · subst k
        exact (hzw.false).elim
      · have hlt := hcross_lt haD haD hjk
        omega
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · have hjm : S.level j = m := by
            exact ((S.split j hjM).1 a ha b hb).symm.trans hzwm
          exact hcoord_le_a hjM hjm
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw.ne ((hc a haD).trans (hc b hbD).symm)).elim
      · have hlt := hcross_lt haD hbD hjk
        omega
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · have hjm : S.level j = m := by
            have hforward : firstDiff (p j a) (p j b) = m := by
              rw [firstDiff_comm]
              exact hzwm
            exact ((S.split j hjM).1 a ha b hb).symm.trans hforward
          exact hcoord_le_b hjM hjm
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw.ne ((hc b hbD).trans (hc a haD).symm)).elim
      · have hlt := hcross_lt hbD haD hjk
        omega
    · by_cases hjk : j = k
      · subst k
        exact (hzw.false).elim
      · have hlt := hcross_lt hbD hbD hjk
        omega
  rcases hjstarsplit.2 with hord | hord
  · have hs : 2 ≤ (F a ∪ F b).card := by
      have hcard' : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          (hord a ha b hb).ne⟩
      omega
    have hp := criticalPair_eq_of_maximal_least hs
      (Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar))
      (Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar))
      (hord a ha b hb)
      (by
        intro z hz w hw hzw
        exact (hbound hz hw hzw).trans_eq hjstardiff.symm)
      (by
        intro z hz w hw hzw hdiff
        have hlo := hlo_le_of_max hz hw hzw (hdiff.trans hjstardiff)
        rw [min_eq_left (hord a ha b hb).le] at hlo
        exact hlo)
    simpa [min_eq_left (hord a ha b hb).le, max_eq_right (hord a ha b hb).le] using hp
  · have hs : 2 ≤ (F a ∪ F b).card := by
      have hcard' : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          (hord a ha b hb).ne⟩
      omega
    have hreverseDiff : firstDiff (p jstar b) (p jstar a) = m := by
      rw [firstDiff_comm]
      exact hjstardiff
    have hp := criticalPair_eq_of_maximal_least hs
      (Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar))
      (Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar))
      (hord a ha b hb)
      (by
        intro z hz w hw hzw
        exact (hbound hz hw hzw).trans_eq hreverseDiff.symm)
      (by
        intro z hz w hw hzw hdiff
        have hlo := hlo_le_of_max hz hw hzw (hdiff.trans hreverseDiff)
        rw [min_eq_right (hord a ha b hb).le] at hlo
        exact hlo)
    simpa [min_eq_right (hord a ha b hb).le, max_eq_left (hord a ha b hb).le] using hp

end

end Erdos965

/-! ## Upstream module: HamelTransfer.lean -/

open Function Set Module

namespace Erdos965

/-- The finite support of a real in the chosen Hamel basis. -/
noncomputable def hamelSupport (x : ℝ) : Finset HamelIndex :=
  (hamelBasis.repr x).support

/-- Coordinates on a fixed finite support determine the real uniquely. -/
noncomputable def fixedSupportCode (s : Finset HamelIndex)
    (x : {x : ℝ // hamelSupport x = s}) : s → ℚ :=
  fun i ↦ hamelBasis.repr x.1 i.1

theorem fixedSupportCode_injective (s : Finset HamelIndex) :
    Injective (fixedSupportCode s) := by
  intro x y hxy
  apply Subtype.ext
  apply hamelBasis.repr.injective
  ext i
  by_cases hi : i ∈ s
  · exact congrFun hxy ⟨i, hi⟩
  · have hix : i ∉ hamelSupport x.1 := by simpa [x.2]
    have hiy : i ∉ hamelSupport y.1 := by simpa [y.2]
    rw [Finsupp.notMem_support_iff.mp hix, Finsupp.notMem_support_iff.mp hiy]

/-- Only countably many reals have any specified finite Hamel support. -/
theorem fixedSupport_countable (s : Finset HamelIndex) :
    ({x : ℝ | hamelSupport x = s} : Set ℝ).Countable := by
  rw [← Set.countable_coe_iff]
  exact (fixedSupportCode_injective s).countable

/-- An uncountable set of reals has uncountably many Hamel supports. -/
theorem hamelSupport_image_uncountable {A : Set ℝ} (hA : ¬ A.Countable) :
    ¬ (hamelSupport '' A).Countable := by
  apply image_uncountable_of_countable_fibers hamelSupport hA
  intro s
  exact (fixedSupport_countable s).mono fun _ hx ↦ hx.2

/-- The tuple of Hamel coefficients on a finite root. -/
noncomputable def rootCoeff (root : Finset HamelIndex) (x : ℝ) : root → ℚ :=
  fun i ↦ hamelBasis.repr x i.1

/-- On an uncountable subset, the coefficient tuple on a fixed finite root
can be made constant. -/
theorem exists_uncountable_subset_rootCoeff_eq (root : Finset HamelIndex)
    {A : Set ℝ} (hA : ¬ A.Countable) :
    ∃ (q : root → ℚ) (A' : Set ℝ),
      A' ⊆ A ∧ ¬ A'.Countable ∧
        ∀ x ∈ A', ∀ i : root, hamelBasis.repr x i.1 = q i := by
  obtain ⟨q, hq⟩ := uncountable_fiber_of_countable_range (rootCoeff root) hA
  let A' : Set ℝ := {x ∈ A | rootCoeff root x = q}
  refine ⟨q, A', ?_, hq, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx i
    exact congrFun hx.2 i

theorem hamelSupport_add_subset (x y : ℝ) :
    hamelSupport (x + y) ⊆ hamelSupport x ∪ hamelSupport y := by
  change (hamelBasis.repr (x + y)).support ⊆
    (hamelBasis.repr x).support ∪ (hamelBasis.repr y).support
  rw [map_add]
  exact Finsupp.support_add

/-- If every common nonzero coordinate survives addition, support of a sum
is exactly the union of the supports. -/
theorem hamelSupport_add_eq_union_of_nocancel (x y : ℝ)
    (h : ∀ i, i ∈ hamelSupport x → i ∈ hamelSupport y →
      hamelBasis.repr x i + hamelBasis.repr y i ≠ 0) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply Finset.Subset.antisymm (hamelSupport_add_subset x y)
  intro i hi
  rw [Finset.mem_union] at hi
  rw [hamelSupport, map_add, Finsupp.mem_support_iff, Finsupp.add_apply]
  rcases hi with hix | hiy
  · by_cases hiy : i ∈ hamelSupport y
    · exact h i hix hiy
    · rw [Finsupp.notMem_support_iff.mp hiy]
      simpa using Finsupp.mem_support_iff.mp hix
  · by_cases hix : i ∈ hamelSupport x
    · exact h i hix hiy
    · rw [Finsupp.notMem_support_iff.mp hix, zero_add]
      exact Finsupp.mem_support_iff.mp hiy

/-- Equal nonzero coefficients on an intersection cannot cancel in
characteristic zero. -/
theorem hamelSupport_add_eq_union_of_eq_on_inter (x y : ℝ)
    (hEq : ∀ i, i ∈ hamelSupport x → i ∈ hamelSupport y →
      hamelBasis.repr x i = hamelBasis.repr y i) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply hamelSupport_add_eq_union_of_nocancel x y
  intro i hix hiy
  have hiy0 : hamelBasis.repr y i ≠ 0 := Finsupp.mem_support_iff.mp hiy
  rw [hEq i hix hiy]
  simpa [← two_mul] using mul_ne_zero (two_ne_zero' ℚ) hiy0

/-- Support addition on one pair from a Δ-system, after coefficients on its
root have been made equal. -/
theorem hamelSupport_add_eq_union_of_delta_root (root : Finset HamelIndex)
    (x y : ℝ) (hDelta : hamelSupport x ∩ hamelSupport y = root)
    (hCoeff : ∀ i ∈ root, hamelBasis.repr x i = hamelBasis.repr y i) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply hamelSupport_add_eq_union_of_eq_on_inter x y
  intro i hix hiy
  apply hCoeff i
  rw [← hDelta]
  exact Finset.mem_inter.mpr ⟨hix, hiy⟩

/-- Uniform support addition on a root-coefficient-thinned Δ-system. -/
theorem hamelSupport_add_eq_union_on_thinned_deltaSystem (root : Finset HamelIndex)
    {A : Set ℝ}
    (hDelta : ∀ {x}, x ∈ A → ∀ {y}, y ∈ A → x ≠ y →
      hamelSupport x ∩ hamelSupport y = root)
    (q : root → ℚ)
    (hCoeff : ∀ x ∈ A, ∀ i : root, hamelBasis.repr x i.1 = q i)
    {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply hamelSupport_add_eq_union_of_delta_root root x y (hDelta hx hy hxy)
  intro i hi
  exact (hCoeff x hx ⟨i, hi⟩).trans (hCoeff y hy ⟨i, hi⟩).symm

/-- Abstract finite-support anti-Ramsey property needed by the Hamel transfer. -/
def finset_pair_antiramsey (color : Finset HamelIndex → Fin 2) : Prop :=
  ∀ S : Set (Finset HamelIndex), ¬ S.Countable →
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
      a ≠ b ∧ c ≠ d ∧ color (a ∪ b) ≠ color (c ∪ d)

/-- A real coloring witnessing the negative solution to Erdős 965. -/
def exists_bad_real_coloring : Prop :=
  ∃ color : ℝ → Fin 2, ∀ A : Set ℝ, ¬ A.Countable →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
      a ≠ b ∧ c ≠ d ∧ color (a + b) ≠ color (c + d)

/-- An anti-Ramsey coloring of finite Hamel supports transfers to an
anti-Ramsey coloring of the reals. -/
theorem hamel_transfer_finset_pair_antiramsey
    (color : Finset HamelIndex → Fin 2) (hcolor : finset_pair_antiramsey color) :
    exists_bad_real_coloring := by
  let realColor : ℝ → Fin 2 := fun x ↦ color (hamelSupport x)
  refine ⟨realColor, ?_⟩
  intro A hA
  obtain ⟨J, hJA, hJunc, root, hDelta⟩ :=
    exists_uncountable_deltaSystem hamelSupport hA
  obtain ⟨q, K, hKJ, hKunc, hCoeff⟩ :=
    exists_uncountable_subset_rootCoeff_eq root hJunc
  have hSuppK : ¬ (hamelSupport '' K).Countable := hamelSupport_image_uncountable hKunc
  obtain ⟨sa, hsa, sb, hsb, sc, hsc, sd, hsd, hsab, hscd, hcolors⟩ :=
    hcolor (hamelSupport '' K) hSuppK
  obtain ⟨a, haK, rfl⟩ := hsa
  obtain ⟨b, hbK, rfl⟩ := hsb
  obtain ⟨c, hcK, rfl⟩ := hsc
  obtain ⟨d, hdK, rfl⟩ := hsd
  have hab : a ≠ b := fun hab ↦ hsab (congrArg hamelSupport hab)
  have hcd : c ≠ d := fun hcd ↦ hscd (congrArg hamelSupport hcd)
  have hsum_ab : hamelSupport (a + b) = hamelSupport a ∪ hamelSupport b :=
    hamelSupport_add_eq_union_on_thinned_deltaSystem root
      (fun {x} hxK {y} hyK hxy ↦ hDelta (hKJ hxK) (hKJ hyK) hxy)
      q hCoeff haK hbK hab
  have hsum_cd : hamelSupport (c + d) = hamelSupport c ∪ hamelSupport d :=
    hamelSupport_add_eq_union_on_thinned_deltaSystem root
      (fun {x} hxK {y} hyK hxy ↦ hDelta (hKJ hxK) (hKJ hyK) hxy)
      q hCoeff hcK hdK hcd
  refine ⟨a, hJA (hKJ haK), b, hJA (hKJ hbK), c, hJA (hKJ hcK),
    d, hJA (hKJ hdK), hab, hcd, ?_⟩
  simpa [realColor, hsum_ab, hsum_cd] using hcolors

/-- Specialization of the Hamel transfer to the canonical finite-support
coloring. -/
theorem exists_bad_real_coloring_of_finset_pair_antiramsey
    (hcolor : finset_pair_antiramsey supportColor) : exists_bad_real_coloring :=
  hamel_transfer_finset_pair_antiramsey supportColor hcolor

end Erdos965

/-! ## Upstream module: FiniteMain.lean -/

open Function Set

namespace Erdos965

noncomputable section

/-! The finite-support form of Komjáth's anti-Ramsey coloring. -/

theorem supportColor_finset_pair_antiramsey :
    finset_pair_antiramsey supportColor := by
  classical
  intro T hT
  obtain ⟨n, hI⟩ :=
    uncountable_fiber_of_countable_range (fun s : Finset HamelIndex ↦ s.card) hT
  let I : Set (Finset HamelIndex) := {s ∈ T | s.card = n}
  let ι := I
  let F : ι → Finset HamelIndex := fun s ↦ s.1
  have hcard : ∀ s : ι, (F s).card = n := fun s ↦ s.2.2
  have hι : ¬ (Set.univ : Set ι).Countable := by
    intro hu
    apply hI
    rw [← Set.countable_coe_iff]
    exact Set.countable_univ_iff.mp hu
  obtain ⟨W, hWuniv⟩ :=
    exists_uniformPrefixWitness F hcard hι
  obtain ⟨D, ND⟩ :=
    FiniteColoring.exists_coordinateNormalization_of_uniformPrefixWitness F hcard W
  let p : Fin n → ι → HamelIndex := fun j s ↦ finsetCoord F hcard s j
  let M : Finset (Fin n) := Finset.univ.filter fun j ↦ InjOn (p j) D
  have hM_inj : ∀ j ∈ M, InjOn (p j) D := by
    intro j hj
    simpa [M] using (Finset.mem_filter.mp hj).2
  have hconst : ∀ j ∉ M, ∃ c, ∀ s ∈ D, p j s = c := by
    intro j hj
    have hjnot : ¬ InjOn (p j) D := by
      intro hinj
      apply hj
      simp [M, hinj]
    rcases ND.normalized j with hconst | hinj
    · exact hconst
    · exact (hjnot hinj.1).elim
  have hMne : M.Nonempty := by
    by_contra hMempty
    have hMempty' : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hMempty
    have hDne : D.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact ND.uncountable (h ▸ Set.countable_empty)
    obtain ⟨s₀, hs₀⟩ := hDne
    apply ND.uncountable
    refine (Set.countable_singleton s₀).mono ?_
    intro s hs
    have hFs : F s = F s₀ :=
      finset_eq_of_all_coords_eq F hcard fun j ↦ by
        obtain ⟨c, hc⟩ := hconst j (by simp [hMempty'])
        exact (hc s hs).trans (hc s₀ hs₀).symm
    have : s = s₀ := Subtype.ext hFs
    exact Set.mem_singleton_iff.mpr this
  obtain ⟨S⟩ := exists_finiteSplitWitness p D M ND.uncountable hM_inj
  have hleftD : S.left ⊆ D := S.left_subset
  have hrightD : S.right ⊆ D := S.right_subset
  have hleftW : S.left ⊆ W.carrier :=
    S.left_subset.trans ND.subset
  have hrightW : S.right ⊆ W.carrier :=
    S.right_subset.trans ND.subset
  have hleftne : S.left.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact S.left_uncountable (h ▸ Set.countable_empty)
  have hrightne : S.right.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact S.right_uncountable (h ▸ Set.countable_empty)
  let aBase : ι := hleftne.choose
  have haBase : aBase ∈ S.left := hleftne.choose_spec
  let bBase : ι := hrightne.choose
  have hbBase : bBase ∈ S.right := hrightne.choose_spec
  have hlevel_ge : ∀ j ∈ M, W.L ≤ S.level j := by
    intro j hj
    have hpneq : p j aBase ≠ p j bBase := by
      rcases (S.split j hj).2 with hord | hord
      · exact (hord aBase haBase bBase hbBase).ne
      · exact (hord aBase haBase bBase hbBase).ne.symm
    have hprefix :
        PiNat.res (binaryCode (p j aBase)) W.L =
          PiNat.res (binaryCode (p j bBase)) W.L := by
      exact (W.prefix_eq aBase (hleftW haBase) j).trans
        (W.prefix_eq bBase (hrightW hbBase) j).symm
    have hle : W.L ≤ firstDiff (p j aBase) (p j bBase) := by
      apply (PiNat.mem_cylinder_iff_le_firstDiff (binaryCode_ne hpneq) W.L).1
      exact PiNat.res_eq_res.mp hprefix
    rw [(S.split j hj).1 aBase haBase bBase hbBase] at hle
    exact hle
  let levels : Finset ℕ := M.image S.level
  have hlevels : levels.Nonempty := hMne.image _
  let m : ℕ := levels.max' hlevels
  have hmlevels : m ∈ levels := Finset.max'_mem levels hlevels
  obtain ⟨j₀, hj₀M, hj₀m⟩ := Finset.mem_image.mp hmlevels
  let C : Finset (Fin n) := M.filter fun j ↦ S.level j = m
  have hC : C.Nonempty := by
    refine ⟨j₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨hj₀M, hj₀m⟩
  let jstar : Fin n := C.min' hC
  have hjstarC : jstar ∈ C := Finset.min'_mem C hC
  have hjstarM : jstar ∈ M := (Finset.mem_filter.mp hjstarC).1
  have hjstarm : S.level jstar = m := (Finset.mem_filter.mp hjstarC).2
  have hlevel_le : ∀ j ∈ M, S.level j ≤ S.level jstar := by
    intro j hj
    rw [hjstarm]
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hjstarleast :
      ∀ j ∈ M, S.level j = S.level jstar → jstar ≤ j := by
    intro j hjM hjlevel
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨hjM, hjlevel.trans hjstarm⟩
  have hcrit : ∀ {a b : ι}, a ∈ S.left → b ∈ S.right →
      criticalPair (F a ∪ F b) =
        (min (p jstar a) (p jstar b), max (p jstar a) (p jstar b)) := by
    intro a b ha hb
    exact criticalPair_crossUnion F hcard W ND.subset hconst S hjstarM
      hlevel_le hlevel_ge hjstarleast ha hb
  have hjstarLower :
      ∀ x ∈ D, {y ∈ D | WellOrderingRel (p jstar y) (p jstar x)}.Countable := by
    rcases ND.normalized jstar with hc | hi
    · have hinj := hM_inj jstar hjstarM
      obtain ⟨c, hc⟩ := hc
      obtain ⟨x₀, hx₀⟩ := hleftne
      exfalso
      apply ND.uncountable
      refine (Set.countable_singleton x₀).mono ?_
      intro x hx
      have hpx : p jstar x = p jstar x₀ :=
        (hc x hx).trans (hc x₀ (hleftD hx₀)).symm
      exact Set.mem_singleton_iff.mpr (hinj hx (hleftD hx₀) hpx)
    · exact hi.2
  have hjstarInj : InjOn (p jstar) D := hM_inj jstar hjstarM
  obtain ⟨a₀, ha₀⟩ := hleftne
  obtain ⟨b₀, hb₀, hb₀not⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable S.right_uncountable
      (hjstarLower a₀ (hleftD ha₀))
  have hp₀ne : p jstar a₀ ≠ p jstar b₀ := by
    rcases (S.split jstar hjstarM).2 with hord | hord
    · exact (hord a₀ ha₀ b₀ hb₀).ne
    · exact (hord a₀ ha₀ b₀ hb₀).ne.symm
  have hW₀ : WellOrderingRel (p jstar a₀) (p jstar b₀) := by
    rcases trichotomous_of WellOrderingRel (p jstar a₀) (p jstar b₀) with h | h | h
    · exact h
    · exact (hp₀ne h).elim
    · exact (hb₀not ⟨hrightD hb₀, h⟩).elim
  obtain ⟨b₁, hb₁⟩ := hrightne
  obtain ⟨a₁, ha₁, ha₁not⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable S.left_uncountable
      (hjstarLower b₁ (hrightD hb₁))
  have hp₁ne : p jstar a₁ ≠ p jstar b₁ := by
    rcases (S.split jstar hjstarM).2 with hord | hord
    · exact (hord a₁ ha₁ b₁ hb₁).ne
    · exact (hord a₁ ha₁ b₁ hb₁).ne.symm
  have hW₁ : WellOrderingRel (p jstar b₁) (p jstar a₁) := by
    rcases trichotomous_of WellOrderingRel (p jstar b₁) (p jstar a₁) with h | h | h
    · exact h
    · exact (hp₁ne h.symm).elim
    · exact (ha₁not ⟨hleftD ha₁, h⟩).elim
  have hcard_union : ∀ {a b : ι}, a ∈ S.left → b ∈ S.right →
      2 ≤ (F a ∪ F b).card := by
    intro a b ha hb
    rcases (S.split jstar hjstarM).2 with hord | hord
    · have h : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          (hord a ha b hb).ne⟩
      omega
    · have h : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          (hord a ha b hb).ne⟩
      omega
  have ha₀T : F a₀ ∈ T := a₀.2.1
  have hb₀T : F b₀ ∈ T := b₀.2.1
  have ha₁T : F a₁ ∈ T := a₁.2.1
  have hb₁T : F b₁ ∈ T := b₁.2.1
  refine ⟨F a₀, ha₀T, F b₀, hb₀T, F a₁, ha₁T, F b₁, hb₁T, ?_, ?_, ?_⟩
  · intro hab
    exact hp₀ne (congrArg (fun s ↦ finsetCoord (fun t : ι ↦ t.1) hcard s jstar)
      (Subtype.ext hab))
  · intro hab
    exact hp₁ne (congrArg (fun s ↦ finsetCoord (fun t : ι ↦ t.1) hcard s jstar)
      (Subtype.ext hab))
  · rcases (S.split jstar hjstarM).2 with hord | hord
    · have hord₀ := hord a₀ ha₀ b₀ hb₀
      have hord₁ := hord a₁ ha₁ b₁ hb₁
      have hc₀ : supportColor (F a₀ ∪ F b₀) = 0 :=
        supportColor_eq_zero_of_criticalPair (hcard_union ha₀ hb₀)
          (by simpa [min_eq_left hord₀.le, max_eq_right hord₀.le] using hcrit ha₀ hb₀) hW₀
      have hc₁ : supportColor (F a₁ ∪ F b₁) = 1 :=
        supportColor_eq_one_of_criticalPair (hcard_union ha₁ hb₁)
          (by simpa [min_eq_left hord₁.le, max_eq_right hord₁.le] using hcrit ha₁ hb₁)
          (fun h ↦
            (show WellFounded WellOrderingRel from IsWellFounded.wf).asymmetric
              _ _ h hW₁)
      simp [hc₀, hc₁]
    · have hord₀ := hord a₀ ha₀ b₀ hb₀
      have hord₁ := hord a₁ ha₁ b₁ hb₁
      have hc₀ : supportColor (F a₀ ∪ F b₀) = 1 :=
        supportColor_eq_one_of_criticalPair (hcard_union ha₀ hb₀)
          (by simpa [min_eq_right hord₀.le, max_eq_left hord₀.le] using hcrit ha₀ hb₀)
          (fun h ↦
            (show WellFounded WellOrderingRel from IsWellFounded.wf).asymmetric
              _ _ h hW₀)
      have hc₁ : supportColor (F a₁ ∪ F b₁) = 0 :=
        supportColor_eq_zero_of_criticalPair (hcard_union ha₁ hb₁)
          (by simpa [min_eq_right hord₁.le, max_eq_left hord₁.le] using hcrit ha₁ hb₁) hW₁
      simp [hc₀, hc₁]

end

end Erdos965

namespace Erdos965

theorem not_erdos_965 :
    ¬ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d →
        f (a + b) = f (c + d) := by
  intro hhom
  obtain ⟨color, hcolor⟩ :=
    exists_bad_real_coloring_of_finset_pair_antiramsey
      supportColor_finset_pair_antiramsey
  obtain ⟨A, hA, hmono⟩ := hhom color
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hne⟩ := hcolor A hA
  exact hne (hmono a ha b hb c hc d hd hab hcd)

end Erdos965

namespace Submissions.Erdos965KomjathRefutation.Full

theorem proof :
    ¬ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d →
        f (a + b) = f (c + d) :=
  Erdos965.not_erdos_965

end Submissions.Erdos965KomjathRefutation.Full
