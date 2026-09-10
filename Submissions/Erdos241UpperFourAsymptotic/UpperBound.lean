import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Submissions.Erdos241UpperFourAsymptotic.UpperBound

open Finset

def UniqueTripleSums (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ,
    m₁.card = 3 → m₂.card = 3 →
    (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
    m₁.sum = m₂.sum → m₁ = m₂

theorem reduced_eq {A : Finset ℕ} (hA : UniqueTripleSums A)
    {c d : ℕ} {m n : Multiset ℕ}
    (hc : c ∈ A) (hd : d ∈ A) (hm : m.card = 2) (hn : n.card = 2)
    (hmA : ∀ x ∈ m, x ∈ A) (hnA : ∀ x ∈ n, x ∈ A)
    (hcm : c ∉ m)
    (heq : (m.sum : ℤ) - c = (n.sum : ℤ) - d) : c = d ∧ m = n := by
  have hs : m.sum + d = n.sum + c := by omega
  have he := hA (d ::ₘ m) (c ::ₘ n) (by simp [hm]) (by simp [hn])
    (by intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx; exact hd; exact hmA x hx)
    (by intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx; exact hc; exact hnA x hx)
    (by simpa [add_comm] using hs)
  have hcd : c = d := by
    have hx : c ∈ d ::ₘ m := he.symm ▸ Multiset.mem_cons_self c n
    exact (Multiset.mem_cons.mp hx).resolve_right hcm
  subst d
  exact ⟨rfl, by simpa using he⟩


/-- Ordered four-term representations, including repeated summands. -/
def quadValue (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  (q.1.1 : ℤ) + q.1.2 - q.2.1 - q.2.2

noncomputable def quadFiber (A : Finset ℕ) (t : ℤ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun q => quadValue q = t)

/-- The first positive summand and the ordering of the negative pair suffice. -/
def fiberCode (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × Bool :=
  (q.1.1, decide (q.2.1 ≤ q.2.2))

theorem fiberCode_injective {A : Finset ℕ} (hA : UniqueTripleSums A)
    {t : ℤ} (ht : ∀ x ∈ A, ∀ y ∈ A, (x : ℤ) - y ≠ t) :
    Set.InjOn fiberCode (quadFiber A t) := by
  classical
  rintro ⟨⟨a, b⟩, c, d⟩ hx ⟨⟨a', b'⟩, c', d'⟩ hy he
  obtain ⟨hmem, hv⟩ := mem_filter.mp hx
  obtain ⟨hmem', hv'⟩ := mem_filter.mp hy
  obtain ⟨hab, hcd⟩ := mem_product.mp hmem
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  obtain ⟨hc, hd⟩ := mem_product.mp hcd
  obtain ⟨hab', hcd'⟩ := mem_product.mp hmem'
  obtain ⟨ha', hb'⟩ := mem_product.mp hab'
  obtain ⟨hc', hd'⟩ := mem_product.mp hcd'
  have haa : a = a' := congrArg Prod.fst he
  subst a'
  have hdir : decide (c ≤ d) = decide (c' ≤ d') := congrArg Prod.snd he
  change (a : ℤ) + b - c - d = t at hv
  change (a : ℤ) + b' - c' - d' = t at hv'
  have hbc : b ∉ ({c, d} : Multiset ℕ) := by
    intro hh
    simp at hh
    rcases hh with rfl | rfl
    · exact ht a ha d hd (by omega)
    · exact ht a ha c hc (by omega)
  have hr := reduced_eq hA hb hb'
    (show ({c,d} : Multiset ℕ).card = 2 by simp)
    (show ({c',d'} : Multiset ℕ).card = 2 by simp)
    (by intro x hh; simp at hh; rcases hh with rfl | rfl <;> assumption)
    (by intro x hh; simp at hh; rcases hh with rfl | rfl <;> assumption)
    hbc (by simp; omega)
  obtain ⟨hbb, hpair⟩ := hr
  change b = b' at hbb
  subst b'
  have hsum : c + d = c' + d' := by
    simpa using congrArg Multiset.sum hpair
  have hm : c ∈ ({c', d'} : Multiset ℕ) :=
    hpair ▸ (by simp : c ∈ ({c, d} : Multiset ℕ))
  have hcmem : c = c' ∨ c = d' := by simpa using hm
  have horder : (c ≤ d ↔ c' ≤ d') := by
    by_cases h : c ≤ d <;> by_cases h' : c' ≤ d' <;> simp_all <;> omega
  have hcc : c = c' := by omega
  have hdd : d = d' := by omega
  simp [hcc, hdd]

/-- Outside A-A, the ordered four-term correlation is at most twice the size. -/
theorem quadFiber_card_le {A : Finset ℕ} (hA : UniqueTripleSums A)
    {t : ℤ} (ht : ∀ x ∈ A, ∀ y ∈ A, (x : ℤ) - y ≠ t) :
    (quadFiber A t).card ≤ 2 * A.card := by
  classical
  have hb := card_le_card_of_injOn fiberCode
    (s := quadFiber A t) (t := A ×ˢ (univ : Finset Bool))
    (by
      intro q hq
      have hm := (mem_filter.mp hq).1
      exact mem_product.mpr ⟨(mem_product.mp (mem_product.mp hm).1).1, mem_univ _⟩)
    (fiberCode_injective hA ht)
  simpa [card_product, Nat.mul_comm] using hb


/-- Ordered pairs with a common image, retaining all multiplicity in the domain. -/
noncomputable def equalPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) : Finset (α × α) :=
  (S ×ˢ S).filter (fun q => f q.1 = f q.2)

theorem equalPairs_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (T : Finset β)
    (hT : ∀ x ∈ S, f x ∈ T) :
    (equalPairs S f).card = ∑ z ∈ T, (S.filter (fun x => f x = z)).card ^ 2 := by
  classical
  have hm : Set.MapsTo (fun q : α × α => f q.1) (equalPairs S f) T := by
    intro q hq
    exact hT q.1 (mem_product.mp (mem_filter.mp hq).1).1
  rw [card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  intro z hz
  have he : (equalPairs S f).filter (fun q => f q.1 = z) =
      (S.filter (fun x => f x = z)) ×ˢ (S.filter (fun x => f x = z)) := by
    ext q
    simp only [equalPairs, mem_filter, mem_product]
    aesop
  rw [he, card_product, pow_two]

theorem finite_cauchy_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (T : Finset β)
    (hT : ∀ x ∈ S, f x ∈ T) :
    S.card ^ 2 ≤ T.card * (equalPairs S f).card := by
  classical
  rw [equalPairs_card S f T hT]
  calc
    S.card ^ 2 = (∑ z ∈ T, (S.filter (fun x => f x = z)).card) ^ 2 := by
      rw [card_eq_sum_card_fiberwise (show Set.MapsTo f S T from hT)]
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) T 1
        (fun z => (S.filter (fun x => f x = z)).card)

abbrev Window := (ℕ × ℕ) × ℕ

def windowSet (A : Finset ℕ) (h : ℕ) : Finset Window :=
  (A ×ˢ A) ×ˢ range h

def windowValue (w : Window) : ℤ :=
  (w.1.1 : ℤ) + w.1.2 + w.2

def windowQuad (p : Window × Window) : (ℕ × ℕ) × (ℕ × ℕ) :=
  (p.1.1, p.2.1)

def inDifference (A : Finset ℕ) (t : ℤ) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, (u : ℤ) - v = t

noncomputable def offCollisions (A : Finset ℕ) (h : ℕ) : Finset (Window × Window) := by
  classical
  exact (equalPairs (windowSet A h) windowValue).filter
    (fun p => ¬ inDifference A (quadValue (windowQuad p)))

def offCode (p : Window × Window) : (ℕ × ℕ) × (ℕ × Bool) :=
  ((p.1.2, p.2.2), fiberCode (windowQuad p))

theorem quad_mem_of_windows {A : Finset ℕ} {h : ℕ} {p : Window × Window}
    (hp : p ∈ equalPairs (windowSet A h) windowValue) :
    windowQuad p ∈ (A ×ˢ A) ×ˢ (A ×ˢ A) := by
  have hm := mem_product.mp (mem_filter.mp hp).1
  exact mem_product.mpr ⟨(mem_product.mp hm.1).1, (mem_product.mp hm.2).1⟩

theorem offCode_injective {A : Finset ℕ} (hA : UniqueTripleSums A) (h : ℕ) :
    Set.InjOn offCode (offCollisions A h) := by
  classical
  intro p hp q hq he
  obtain ⟨hpC, hpD⟩ := mem_filter.mp hp
  obtain ⟨hqC, hqD⟩ := mem_filter.mp hq
  have hi : p.1.2 = q.1.2 := congrArg (fun x => x.1.1) he
  have hj : p.2.2 = q.2.2 := congrArg (fun x => x.1.2) he
  have hc : fiberCode (windowQuad p) = fiberCode (windowQuad q) := congrArg Prod.snd he
  have hvp := (mem_filter.mp hpC).2
  have hvq := (mem_filter.mp hqC).2
  have hv : quadValue (windowQuad p) = quadValue (windowQuad q) := by
    dsimp [quadValue, windowQuad, windowValue] at *
    omega
  have ht : ∀ x ∈ A, ∀ y ∈ A, (x : ℤ) - y ≠ quadValue (windowQuad p) := by
    intro x hx y hy heq
    exact hpD ⟨x, hx, y, hy, heq⟩
  have hquad := fiberCode_injective hA ht
    (mem_filter.mpr ⟨quad_mem_of_windows hpC, rfl⟩)
    (mem_filter.mpr ⟨quad_mem_of_windows hqC, hv.symm⟩) hc
  apply Prod.ext
  · exact Prod.ext (congrArg (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.1) hquad) hi
  · exact Prod.ext (congrArg (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.2) hquad) hj

theorem offCollisions_card_le {A : Finset ℕ} (hA : UniqueTripleSums A) (h : ℕ) :
    (offCollisions A h).card ≤ 2 * A.card * h ^ 2 := by
  classical
  let T : Finset ((ℕ × ℕ) × (ℕ × Bool)) :=
    (range h ×ˢ range h) ×ˢ (A ×ˢ (univ : Finset Bool))
  have hm : Set.MapsTo offCode (offCollisions A h) T := by
    intro p hp
    have hw := mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1
    have h1 := mem_product.mp hw.1
    have h2 := mem_product.mp hw.2
    exact mem_product.mpr ⟨mem_product.mpr ⟨h1.2, h2.2⟩,
      mem_product.mpr ⟨(mem_product.mp h1.1).1, mem_univ _⟩⟩
  have hc := card_le_card_of_injOn offCode (t := T) hm (offCode_injective hA h)
  simpa [T, card_product, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc

/-- All ordered exceptional quadruples; the difference is in Z. -/
noncomputable def exceptionalQuads (A : Finset ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun q =>
    ∃ u ∈ A, ∃ v ∈ A, (u : ℤ) - v = quadValue q)

theorem mem_exceptionalQuads {A : Finset ℕ}
    {q : (ℕ × ℕ) × (ℕ × ℕ)} :
    q ∈ exceptionalQuads A ↔
      q ∈ ((A ×ˢ A) ×ˢ (A ×ˢ A)) ∧
      ∃ u ∈ A, ∃ v ∈ A, (u : ℤ) - v = quadValue q := by
  classical
  simp only [exceptionalQuads, mem_filter]

/-- Exceptional differences force a common positive and negative summand. -/
theorem quad_cross_of_difference {A : Finset ℕ} (hA : UniqueTripleSums A)
    {a b c d u v : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hu : u ∈ A) (hv : v ∈ A)
    (he : (a : ℤ) + b - c - d = (u : ℤ) - v) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  classical
  by_cases hbc : b = c
  · exact Or.inr (Or.inr (Or.inl hbc))
  by_cases hbd : b = d
  · exact Or.inr (Or.inr (Or.inr hbd))
  have hbn : b ∉ ({c, d} : Multiset ℕ) := by
    simp [hbc, hbd]
  have hr := reduced_eq hA hb hu
    (show ({c, d} : Multiset ℕ).card = 2 by simp)
    (show ({a, v} : Multiset ℕ).card = 2 by simp)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
    hbn (by simp; omega)
  have hpair : ({c, d} : Multiset ℕ) = ({a, v} : Multiset ℕ) := hr.2
  have ham : a ∈ ({c, d} : Multiset ℕ) :=
    hpair.symm ▸ (by simp : a ∈ ({a, v} : Multiset ℕ))
  have hacd : a = c ∨ a = d := by simpa using ham
  rcases hacd with hac | had
  · exact Or.inl hac
  · exact Or.inr (Or.inl had)

def exceptionalTriples (A : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (A ×ˢ A) ×ˢ A

def quadCross00 (x : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((x.1.1, x.1.2), (x.1.1, x.2))

def quadCross01 (x : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((x.1.1, x.1.2), (x.2, x.1.1))

def quadCross10 (x : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((x.1.1, x.1.2), (x.1.2, x.2))

def quadCross11 (x : (ℕ × ℕ) × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((x.1.1, x.1.2), (x.2, x.1.2))

def exceptionalCover (A : Finset ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((exceptionalTriples A).image quadCross00) ∪
    ((exceptionalTriples A).image quadCross01)) ∪
  (((exceptionalTriples A).image quadCross10) ∪
    ((exceptionalTriples A).image quadCross11))

theorem exceptionalQuads_subset_cover {A : Finset ℕ}
    (hA : UniqueTripleSums A) : exceptionalQuads A ⊆ exceptionalCover A := by
  classical
  rintro ⟨⟨a, b⟩, c, d⟩ hq
  obtain ⟨hm, u, hu, v, hv, he⟩ := mem_exceptionalQuads.mp hq
  obtain ⟨hab, hcd⟩ := mem_product.mp hm
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  obtain ⟨hc, hd⟩ := mem_product.mp hcd
  have he' : (a : ℤ) + b - c - d = (u : ℤ) - v := by
    simpa [quadValue] using he.symm
  have hcross := quad_cross_of_difference hA ha hb hc hd hu hv he'
  change a = c ∨ a = d ∨ b = c ∨ b = d at hcross
  change ((a, b), (c, d)) ∈
    (((exceptionalTriples A).image quadCross00) ∪
      ((exceptionalTriples A).image quadCross01)) ∪
    (((exceptionalTriples A).image quadCross10) ∪
      ((exceptionalTriples A).image quadCross11))
  rcases hcross with hac | had | hbc | hbd
  · apply mem_union.mpr
    left
    apply mem_union.mpr
    left
    exact mem_image.mpr ⟨((a, b), d),
      by simp [exceptionalTriples, ha, hb, hd],
      by simp [quadCross00, hac]⟩
  · apply mem_union.mpr
    left
    apply mem_union.mpr
    right
    exact mem_image.mpr ⟨((a, b), c),
      by simp [exceptionalTriples, ha, hb, hc],
      by simp [quadCross01, had]⟩
  · apply mem_union.mpr
    right
    apply mem_union.mpr
    left
    exact mem_image.mpr ⟨((a, b), d),
      by simp [exceptionalTriples, ha, hb, hd],
      by simp [quadCross10, hbc]⟩
  · apply mem_union.mpr
    right
    apply mem_union.mpr
    right
    exact mem_image.mpr ⟨((a, b), c),
      by simp [exceptionalTriples, ha, hb, hc],
      by simp [quadCross11, hbd]⟩

/-- A sufficient exceptional inventory bound; diagonal overlaps are harmless. -/
theorem exceptionalQuads_card_le {A : Finset ℕ} (hA : UniqueTripleSums A) :
    (exceptionalQuads A).card ≤ 4 * A.card ^ 3 := by
  classical
  have h0 : ((exceptionalTriples A).image quadCross00).card ≤
      (exceptionalTriples A).card := card_image_le
  have h1 : ((exceptionalTriples A).image quadCross01).card ≤
      (exceptionalTriples A).card := card_image_le
  have h2 : ((exceptionalTriples A).image quadCross10).card ≤
      (exceptionalTriples A).card := card_image_le
  have h3 : ((exceptionalTriples A).image quadCross11).card ≤
      (exceptionalTriples A).card := card_image_le
  have h01 := card_union_le ((exceptionalTriples A).image quadCross00)
    ((exceptionalTriples A).image quadCross01)
  have h23 := card_union_le ((exceptionalTriples A).image quadCross10)
    ((exceptionalTriples A).image quadCross11)
  have hall := card_union_le
    (((exceptionalTriples A).image quadCross00) ∪
      ((exceptionalTriples A).image quadCross01))
    (((exceptionalTriples A).image quadCross10) ∪
      ((exceptionalTriples A).image quadCross11))
  have hcover : (exceptionalCover A).card ≤ 4 * (exceptionalTriples A).card := by
    unfold exceptionalCover
    omega
  have htriples : (exceptionalTriples A).card = A.card ^ 3 := by
    simp [exceptionalTriples, card_product, pow_succ, Nat.mul_assoc]
  calc
    (exceptionalQuads A).card ≤ (exceptionalCover A).card :=
      card_le_card (exceptionalQuads_subset_cover hA)
    _ ≤ 4 * (exceptionalTriples A).card := hcover
    _ = 4 * A.card ^ 3 := by rw [htriples]


noncomputable def exceptionalCollisions (A : Finset ℕ) (h : ℕ) :
    Finset (Window × Window) := by
  classical
  exact (equalPairs (windowSet A h) windowValue).filter
    (fun p => inDifference A (quadValue (windowQuad p)))

def exceptionalCode (p : Window × Window) : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (p.1.2, windowQuad p)

theorem exceptionalCode_injective (A : Finset ℕ) (h : ℕ) :
    Set.InjOn exceptionalCode (exceptionalCollisions A h) := by
  classical
  intro p hp q hq he
  have hi : p.1.2 = q.1.2 := congrArg Prod.fst he
  have hquad : windowQuad p = windowQuad q := congrArg Prod.snd he
  have hab : p.1.1 = q.1.1 := congrArg (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.1) hquad
  have hcd : p.2.1 = q.2.1 := congrArg (fun r : (ℕ × ℕ) × (ℕ × ℕ) => r.2) hquad
  have hvp := (mem_filter.mp (mem_filter.mp hp).1).2
  have hvq := (mem_filter.mp (mem_filter.mp hq).1).2
  have hj : p.2.2 = q.2.2 := by
    dsimp [windowValue] at hvp hvq
    rw [hab, hcd, hi] at hvp
    omega
  exact Prod.ext (Prod.ext hab hi) (Prod.ext hcd hj)

theorem exceptionalCollisions_card_le {A : Finset ℕ}
    (hA : UniqueTripleSums A) (h : ℕ) :
    (exceptionalCollisions A h).card ≤ 4 * A.card ^ 3 * h := by
  classical
  let T : Finset (ℕ × ((ℕ × ℕ) × (ℕ × ℕ))) := range h ×ˢ exceptionalQuads A
  have hm : Set.MapsTo exceptionalCode (exceptionalCollisions A h) T := by
    intro p hp
    obtain ⟨hpC, hpD⟩ := mem_filter.mp hp
    have hw := mem_product.mp (mem_filter.mp hpC).1
    exact mem_product.mpr ⟨(mem_product.mp hw.1).2,
      mem_exceptionalQuads.mpr ⟨quad_mem_of_windows hpC, hpD⟩⟩
  have hc := card_le_card_of_injOn exceptionalCode (t := T) hm
    (exceptionalCode_injective A h)
  calc
    (exceptionalCollisions A h).card ≤ h * (exceptionalQuads A).card := by
      simpa [T, card_product] using hc
    _ ≤ h * (4 * A.card ^ 3) := Nat.mul_le_mul_left h (exceptionalQuads_card_le hA)
    _ = _ := by ring

theorem window_collisions_card_le {A : Finset ℕ} (hA : UniqueTripleSums A) (h : ℕ) :
    (equalPairs (windowSet A h) windowValue).card ≤
      2 * A.card * h ^ 2 + 4 * A.card ^ 3 * h := by
  classical
  have he := card_filter_add_card_filter_not
    (s := equalPairs (windowSet A h) windowValue)
    (fun p => inDifference A (quadValue (windowQuad p)))
  change (exceptionalCollisions A h).card + (offCollisions A h).card = _ at he
  have h1 := exceptionalCollisions_card_le hA h
  have h2 := offCollisions_card_le hA h
  omega

theorem windowValue_mem_interval {A : Finset ℕ} {N h : ℕ}
    (hsub : A ⊆ Icc 1 N) {w : Window} (hw : w ∈ windowSet A h) :
    windowValue w ∈ Icc (2 : ℤ) (2 * (N : ℤ) + h - 1) := by
  have hm := mem_product.mp hw
  have hab := mem_product.mp hm.1
  have ha := mem_Icc.mp (hsub hab.1)
  have hb := mem_Icc.mp (hsub hab.2)
  have hi := mem_range.mp hm.2
  apply mem_Icc.mpr
  dsimp [windowValue]
  omega

/-- Unrestricted finite smoothing with a sufficient cubic exceptional inventory. -/
theorem finite_smoothing {A : Finset ℕ} {N h : ℕ}
    (hN : 1 ≤ N) (hh : 1 ≤ h) (hsub : A ⊆ Icc 1 N)
    (hA : UniqueTripleSums A) :
    h * A.card ^ 4 ≤ (2 * N + h - 2) * (2 * A.card * h + 4 * A.card ^ 3) := by
  classical
  have hmap : ∀ w ∈ windowSet A h,
      windowValue w ∈ Icc (2 : ℤ) (2 * (N : ℤ) + h - 1) := by
    intro w hw
    exact windowValue_mem_interval hsub hw
  have hc := finite_cauchy_card (windowSet A h) windowValue
    (Icc (2 : ℤ) (2 * (N : ℤ) + h - 1)) hmap
  have hsize : (Icc (2 : ℤ) (2 * (N : ℤ) + h - 1)).card = 2 * N + h - 2 := by
    rw [Int.card_Icc]
    omega
  rw [hsize] at hc
  have hws : (windowSet A h).card = A.card * A.card * h := by
    simp [windowSet, card_product]
  rw [hws] at hc
  have hfull := hc.trans (Nat.mul_le_mul_left (2 * N + h - 2)
    (window_collisions_card_le hA h))
  have hcancel : h * (h * A.card ^ 4) ≤
      h * ((2 * N + h - 2) * (2 * A.card * h + 4 * A.card ^ 3)) := by
    calc
      _ = (A.card * A.card * h) ^ 2 := by ring
      _ ≤ (2 * N + h - 2) * (2 * A.card * h ^ 2 + 4 * A.card ^ 3 * h) := hfull
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hcancel (by omega)


/-- A natural parameter formulation, avoiding real roots and division. -/
theorem parameter_smoothing {A : Finset ℕ} {N m : ℕ}
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hk : 1 ≤ A.card)
    (hsub : A ⊆ Icc 1 N) (hA : UniqueTripleSums A) :
    m * A.card ^ 3 ≤ (2 * N + A.card ^ 2 * m) * (2 * m + 4) := by
  have hkp : 0 < A.card := by omega
  have hmp : 0 < m := by omega
  have hhp := Nat.mul_pos (pow_pos hkp 2) hmp
  have hh : 1 ≤ A.card ^ 2 * m := by omega
  have hf := finite_smoothing hN hh hsub hA
  have hw := hf.trans (Nat.mul_le_mul_right
    (2 * A.card * (A.card ^ 2 * m) + 4 * A.card ^ 3)
    (Nat.sub_le (2 * N + A.card ^ 2 * m) 2))
  have hc : A.card ^ 3 * (m * A.card ^ 3) ≤
      A.card ^ 3 * ((2 * N + A.card ^ 2 * m) * (2 * m + 4)) := by
    calc
      _ = A.card ^ 2 * m * A.card ^ 4 := by ring
      _ ≤ _ := hw
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hc (pow_pos hkp 3)

/-- A coarse preliminary cubic bound used only to control the window error. -/
theorem coarse_cubic_bound {A : Finset ℕ} {N : ℕ}
    (hN : 1 ≤ N) (hk : 12 ≤ A.card)
    (hsub : A ⊆ Icc 1 N) (hA : UniqueTripleSums A) :
    A.card ^ 3 ≤ 24 * N := by
  have hp := parameter_smoothing hN (m := 1) (by omega) (by omega) hsub hA
  have hs : 12 * A.card ^ 2 ≤ A.card ^ 3 := by
    calc
      _ ≤ A.card * A.card ^ 2 := Nat.mul_le_mul_right _ hk
      _ = _ := by ring
  have hp' : A.card ^ 3 ≤ 12 * N + 6 * A.card ^ 2 := by
    calc
      _ = 1 * A.card ^ 3 := by ring
      _ ≤ _ := hp
      _ = _ := by ring
  omega

/-- Large-cardinality estimate with coefficient approaching four. -/
theorem parameter_cubic_bound {A : Finset ℕ} {N m : ℕ}
    (hN : 1 ≤ N) (hm : 1 ≤ m) (hk : 48 * m * (m + 2) ≤ A.card)
    (hsub : A ⊆ Icc 1 N) (hA : UniqueTripleSums A) :
    m * A.card ^ 3 ≤ (4 * m + 9) * N := by
  have h1 : 1 ≤ m * (m + 2) := by
    calc
      1 = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul hm (by omega)
  have hthreshold : 12 ≤ 48 * m * (m + 2) := by
    calc
      12 ≤ 48 * 1 := by decide
      _ ≤ 48 * (m * (m + 2)) := Nat.mul_le_mul_left 48 h1
      _ = _ := by ring
  have hcoarse := coarse_cubic_bound hN (hthreshold.trans hk) hsub hA
  have hp := parameter_smoothing hN hm (by omega) hsub hA
  have hs : 48 * m * (m + 2) * A.card ^ 2 ≤ A.card ^ 3 := by
    calc
      _ ≤ A.card * A.card ^ 2 := Nat.mul_le_mul_right _ hk
      _ = _ := by ring
  have herr : 2 * m * (m + 2) * A.card ^ 2 ≤ N := by
    have he : 24 * (2 * m * (m + 2) * A.card ^ 2) ≤ 24 * N := by
      calc
        _ = 48 * m * (m + 2) * A.card ^ 2 := by ring
        _ ≤ _ := hs.trans hcoarse
    exact Nat.le_of_mul_le_mul_left he (by decide)
  calc
    _ ≤ _ := hp
    _ = (4 * m + 8) * N + 2 * m * (m + 2) * A.card ^ 2 := by ring
    _ ≤ (4 * m + 8) * N + N := Nat.add_le_add_left herr _
    _ = _ := by ring

/-- Uniform all-N upper-four estimate. The target coefficient one is not proved. -/
theorem uniform_upper_four {A : Finset ℕ} {N m : ℕ}
    (hm : 1 ≤ m) (hN : m * (48 * m * (m + 2)) ^ 3 ≤ N)
    (hsub : A ⊆ Icc 1 N) (hA : UniqueTripleSums A) :
    m * A.card ^ 3 ≤ (4 * m + 9) * N := by
  by_cases hk : 48 * m * (m + 2) ≤ A.card
  · have hmp : 0 < m := by omega
    have htp : 0 < 48 * m * (m + 2) :=
      Nat.mul_pos (Nat.mul_pos (by decide) hmp) (by omega)
    have hpp := Nat.mul_pos hmp (pow_pos htp 3)
    have hpos : 1 ≤ m * (48 * m * (m + 2)) ^ 3 := by omega
    exact parameter_cubic_bound (hpos.trans hN) hm hk hsub hA
  · have hk' : A.card ≤ 48 * m * (m + 2) := by omega
    have hsmall : m * A.card ^ 3 ≤ N :=
      (Nat.mul_le_mul_left m (Nat.pow_le_pow_left hk' 3)).trans hN
    exact hsmall.trans (by
      calc
        N = 1 * N := by ring
        _ ≤ _ := Nat.mul_le_mul_right N (by omega))

/-- The same finite extremal function as the faithful Jig root statement. -/
noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

theorem maxUniqueSums_attained (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ UniqueTripleSums A ∧
      maxUniqueSums N 3 = A.card := by
  classical
  let C := (Icc 1 N).powerset.filter UniqueTripleSums
  have hEmpty : UniqueTripleSums (∅ : Finset ℕ) := by
    intro m n hm hn hmA hnA he
    have hm0 : m = 0 := Multiset.eq_zero_iff_forall_notMem.mpr (by
      intro x hx
      simpa using hmA x hx)
    simp [hm0] at hm
  have hC : C.Nonempty := ⟨∅, by simp [C, hEmpty]⟩
  obtain ⟨A, hAC, he⟩ := C.exists_mem_eq_sup hC card
  obtain ⟨hAP, hA⟩ := mem_filter.mp hAC
  exact ⟨A, mem_powerset.mp hAP, hA, he⟩

theorem max_parameter_bound {N m : ℕ} (hm : 1 ≤ m)
    (hN : m * (48 * m * (m + 2)) ^ 3 ≤ N) :
    m * (maxUniqueSums N 3) ^ 3 ≤ (4 * m + 9) * N := by
  obtain ⟨A, hsub, hA, hcard⟩ := maxUniqueSums_attained N
  rw [hcard]
  exact uniform_upper_four hm hN hsub hA

/-- Classical upper-four bound, only a partial result toward the sharp constant one. -/
theorem upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      (maxUniqueSums N 3 : ℝ) ^ 3 ≤ (4 + ε) * (N : ℝ) := by
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (max (9 / ε) (1 : ℝ))
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmp : (0 : ℝ) < m := lt_trans (by norm_num) hm1
  have hmn : 1 ≤ m := by exact_mod_cast (le_of_lt hm1)
  have hratio : 9 / ε ≤ (m : ℝ) := (le_max_left _ _).trans hm.le
  have h9 : 9 ≤ (m : ℝ) * ε := (div_le_iff₀ hε).mp hratio
  apply Filter.eventually_atTop.2
  refine ⟨m * (48 * m * (m + 2)) ^ 3, ?_⟩
  intro N hN
  have hp := max_parameter_bound hmn hN
  have hpR : (m : ℝ) * (maxUniqueSums N 3 : ℝ) ^ 3 ≤
      (4 * (m : ℝ) + 9) * (N : ℝ) := by exact_mod_cast hp
  have hc : 4 * (m : ℝ) + 9 ≤ (m : ℝ) * (4 + ε) := by
    calc
      _ ≤ 4 * (m : ℝ) + (m : ℝ) * ε := by
        simpa only [add_comm] using add_le_add_left h9 (4 * (m : ℝ))
      _ = _ := by ring
  have hfull : (m : ℝ) * (maxUniqueSums N 3 : ℝ) ^ 3 ≤
      (m : ℝ) * ((4 + ε) * (N : ℝ)) := by
    calc
      _ ≤ _ := hpR
      _ ≤ ((m : ℝ) * (4 + ε)) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)
      _ = _ := by ring
  exact le_of_mul_le_mul_left hfull hmp

#print axioms upper_bound
end Submissions.Erdos241UpperFourAsymptotic.UpperBound
