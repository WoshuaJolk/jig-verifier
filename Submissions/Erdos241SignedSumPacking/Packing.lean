import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

namespace Submissions.Erdos241SignedSumPacking.Packing

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

theorem reduced_not_mem {A : Finset ℕ} (hA : UniqueTripleSums A)
    {c e : ℕ} {m : Multiset ℕ}
    (hc : c ∈ A) (he : e ∈ A) (hm : m.card = 2)
    (hmA : ∀ x ∈ m, x ∈ A) (hcm : c ∉ m) : (m.sum : ℤ) - c ≠ e := by
  intro hs
  have hr := reduced_eq hA hc hc hm (show ({e, c} : Multiset ℕ).card = 2 by simp)
    hmA (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
    hcm (show (m.sum : ℤ) - c = (({e, c} : Multiset ℕ).sum : ℤ) - c by simp at *; omega)
  exact hcm (hr.2.symm ▸ by simp)

def representatives (A : Finset ℕ) : Finset (Σ _ : ℕ, Sym2 ℕ) :=
  A.sigma fun c => (A.erase c).sym2

def signedValue (p : Σ _ : ℕ, Sym2 ℕ) : ℤ :=
  (p.2.toMultiset.sum : ℤ) - p.1

theorem representative_facts {A : Finset ℕ} {p : Σ _ : ℕ, Sym2 ℕ}
    (hp : p ∈ representatives A) :
    p.1 ∈ A ∧ (∀ x ∈ p.2.toMultiset, x ∈ A) ∧ p.1 ∉ p.2.toMultiset := by
  obtain ⟨hc, hm⟩ := mem_sigma.mp hp
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    exact (mem_erase.mp ((mem_sym2_iff.mp hm) x (Sym2.mem_toMultiset.mp hx))).2
  · intro hx
    exact (mem_erase.mp ((mem_sym2_iff.mp hm) p.1 (Sym2.mem_toMultiset.mp hx))).1 rfl

theorem signedValue_injective {A : Finset ℕ} (hA : UniqueTripleSums A) :
    Set.InjOn signedValue (representatives A) := by
  rintro ⟨c, m⟩ hp ⟨d, n⟩ hq he
  obtain ⟨hc, hmA, hcm⟩ := representative_facts hp
  obtain ⟨hd, hnA, _⟩ := representative_facts hq
  obtain ⟨hcd, hmn⟩ := reduced_eq hA hc hd (Sym2.card_toMultiset m)
    (Sym2.card_toMultiset n) hmA hnA hcm he
  change c = d at hcd
  subst d
  have hmn' : m = n := by
    induction m using Sym2.ind with
    | _ a b =>
      induction n using Sym2.ind with
      | _ e f =>
        simp only [Sym2.toMultiset, Sym2.lift_mk] at hmn
        simpa [Sym2.eq_iff, List.perm_pair] using hmn
  subst n
  rfl

theorem card_representatives (A : Finset ℕ) :
    (representatives A).card = A.card * A.card.choose 2 := by
  classical
  rw [representatives, card_sigma]
  calc
    ∑ c ∈ A, ((A.erase c).sym2).card = ∑ _c ∈ A, A.card.choose 2 := by
      apply sum_congr rfl
      intro c hc
      rw [card_sym2, card_erase_of_mem hc, Nat.sub_add_cancel (card_pos.mpr ⟨c, hc⟩)]
    _ = _ := by simp

theorem signedValue_mem_interval {N : ℕ} {A : Finset ℕ}
    (hsub : A ⊆ Icc 1 N) {p : Σ _ : ℕ, Sym2 ℕ}
    (hp : p ∈ representatives A) :
    signedValue p ∈ Icc (2 - (N : ℤ)) (2 * N - 1) := by
  rcases p with ⟨c, m⟩
  induction m using Sym2.ind with
  | _ a b =>
    obtain ⟨hc, hm⟩ := mem_sigma.mp hp
    obtain ⟨ha, hb⟩ := mk_mem_sym2_iff.mp hm
    have hcN := mem_Icc.mp (hsub hc)
    change 1 ≤ c ∧ c ≤ N at hcN
    have haN := mem_Icc.mp (hsub (mem_erase.mp ha).2)
    have hbN := mem_Icc.mp (hsub (mem_erase.mp hb).2)
    simp only [signedValue, Sym2.toMultiset, Sym2.lift_mk, Multiset.sum_coe,
      List.sum_cons, List.sum_nil, add_zero, Nat.cast_add, mem_Icc]
    omega

theorem packing_bound (N : ℕ) (A : Finset ℕ) (hN : 1 ≤ N)
    (hsub : A ⊆ Icc 1 N) (hA : UniqueTripleSums A) :
    A.card + A.card * A.card.choose 2 ≤ 3 * N - 2 := by
  classical
  let R := (representatives A).image signedValue
  let B := A.image (Nat.cast : ℕ → ℤ)
  have hdisj : Disjoint B R := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    obtain ⟨p, hp, heq⟩ := mem_image.mp hy
    obtain ⟨hc, hmA, hcm⟩ := representative_facts hp
    exact reduced_not_mem hA hc he (Sym2.card_toMultiset p.2) hmA hcm heq
  have hcardB : B.card = A.card := card_image_of_injective _ Nat.cast_injective
  have hcardR : R.card = A.card * A.card.choose 2 := by
    rw [card_image_of_injOn (signedValue_injective hA), card_representatives]
  have hbound : B ∪ R ⊆ Icc (2 - (N : ℤ)) (2 * N - 1) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      have haN := mem_Icc.mp (hsub ha)
      apply mem_Icc.mpr
      omega
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      exact signedValue_mem_interval hsub hp
  have hcard := card_le_card hbound
  rw [card_union_of_disjoint hdisj, hcardB, hcardR, Int.card_Icc] at hcard
  have hsize : (2 * (N : ℤ) - 1 + 1 - (2 - N)).toNat = 3 * N - 2 := by omega
  simpa only [hsize] using hcard

/-- The exact finite extremum from the root statement. -/
noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

theorem empty_unique : UniqueTripleSums ∅ := by
  intro m n hm _ hmA _ _
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < m.card by omega)
  exact False.elim (notMem_empty x (hmA x hx))

theorem maximum_attained (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ UniqueTripleSums A ∧ maxUniqueSums N 3 = A.card := by
  classical
  let candidates := (Icc 1 N).powerset.filter UniqueTripleSums
  have hn : candidates.Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), empty_unique⟩⟩
  obtain ⟨A, hA, hmax⟩ := exists_mem_eq_sup candidates hn card
  obtain ⟨hsub, huniq⟩ := mem_filter.mp hA
  exact ⟨A, mem_powerset.mp hsub, huniq, hmax⟩

theorem proof (N : ℕ) (hN : 1 ≤ N) :
    maxUniqueSums N 3 + maxUniqueSums N 3 * (maxUniqueSums N 3).choose 2 ≤ 3 * N - 2 := by
  obtain ⟨A, hsub, hA, heq⟩ := maximum_attained N
  rw [heq]
  exact packing_bound N A hN hsub hA

end Submissions.Erdos241SignedSumPacking.Packing
