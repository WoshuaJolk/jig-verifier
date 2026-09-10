import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Sym2
open Finset SimpleGraph

namespace Submissions.Erdos81SplitLower.SplitLower

def IsEdgeCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : Prop :=
  (∀ clique ∈ parts, G.IsClique (clique : Set V)) ∧
  ∀ edge ∈ G.edgeFinset,
    ∃! clique : Finset V, clique ∈ parts ∧ edge ∈ clique.sym2

def crossEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (V × V) :=
  (A ×ˢ (univ \ A)).filter fun e => G.Adj e.1 e.2

theorem lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (hind : ∀ x ∉ A, ∀ y ∉ A, ¬ G.Adj x y)
    (parts : Finset (Finset V)) (hp : IsEdgeCliquePartition G parts) :
    2 * (crossEdges G A).card ≤ 2 * parts.card + A.card * (A.card - 1) := by
  classical
  let cross := fun c : Finset V => (c ∩ A) ×ˢ (c \ A)
  let core := fun c : Finset V => (c ∩ A).offDiag
  have unique : ∀ c ∈ parts, ∀ d ∈ parts, ∀ x ∈ c, ∀ y ∈ c,
      x ≠ y → x ∈ d → y ∈ d → c = d := by
    intro c hc d hd x hx y hy hxy hxd hyd
    have he : s(x, y) ∈ G.edgeFinset := by
      exact SimpleGraph.mem_edgeFinset.mpr (hp.1 c hc hx hy hxy)
    obtain ⟨e, he, hu⟩ := hp.2 _ he
    exact (hu c ⟨hc, mk_mem_sym2_iff.mpr ⟨hx, hy⟩⟩).trans
      (hu d ⟨hd, mk_mem_sym2_iff.mpr ⟨hxd, hyd⟩⟩).symm
  have hcross : (parts : Set (Finset V)).PairwiseDisjoint cross := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨⟨hxc, hxA⟩, hyc, hyA⟩ := by
      simpa [cross, mem_product, mem_inter, mem_sdiff] using he
    obtain ⟨⟨hxd, _⟩, hyd, _⟩ := by
      simpa [cross, mem_product, mem_inter, mem_sdiff] using hf
    exact hcd (unique c hc d hd e.1 hxc e.2 hyc
      (fun h => hyA (h ▸ hxA)) hxd hyd)
  have hcore : (parts : Set (Finset V)).PairwiseDisjoint core := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨hx, hy, hxy⟩ := mem_offDiag.mp he
    obtain ⟨hxd, hyd, _⟩ := mem_offDiag.mp hf
    exact hcd (unique c hc d hd e.1 (mem_inter.mp hx).1
      e.2 (mem_inter.mp hy).1 hxy (mem_inter.mp hxd).1 (mem_inter.mp hyd).1)
  have cover : parts.biUnion cross = crossEdges G A := by
    ext e
    simp only [mem_biUnion, crossEdges, mem_filter, mem_product, mem_sdiff,
      mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, he⟩
      obtain ⟨⟨hx, hxA⟩, hy, hyA⟩ := by
        simpa [cross, mem_product, mem_inter, mem_sdiff] using he
      exact ⟨⟨hxA, hyA⟩, hp.1 c hc hx hy (fun h => hyA (h ▸ hxA))⟩
    · rintro ⟨⟨hxA, hyA⟩, he⟩
      obtain ⟨c, ⟨hc, hec⟩, _⟩ := hp.2 s(e.1, e.2) (SimpleGraph.mem_edgeFinset.mpr he)
      obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hec
      exact ⟨c, hc, by simp [cross, hx, hy, hxA, hyA]⟩
  have core_sub : parts.biUnion core ⊆ A.offDiag := by
    intro e he
    obtain ⟨c, _, he⟩ := mem_biUnion.mp he
    obtain ⟨hx, hy, hxy⟩ := mem_offDiag.mp he
    exact mem_offDiag.mpr ⟨(mem_inter.mp hx).2, (mem_inter.mp hy).2, hxy⟩
  have local_bound : ∀ c ∈ parts, 2 * (cross c).card ≤ 2 + (core c).card := by
    intro c hc
    have hb : (c \ A).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      by_contra hxy
      exact hind x (mem_sdiff.mp hx).2 y (mem_sdiff.mp hy).2
        (hp.1 c hc (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hxy)
    have ha : 2 * (c ∩ A).card ≤ 2 + (c ∩ A).card * ((c ∩ A).card - 1) := by
      rcases Nat.eq_zero_or_pos (c ∩ A).card with hz | hz
      · simp [hz]
      · have ht : (c ∩ A).card - 1 + 1 = (c ∩ A).card := Nat.sub_add_cancel hz
        have hs := Nat.zero_le (((c ∩ A).card - 1) * ((c ∩ A).card - 2))
        rcases Nat.eq_zero_or_pos ((c ∩ A).card - 1) with h | h
        · omega
        · have ht2 : (c ∩ A).card - 2 + 1 = (c ∩ A).card - 1 := by omega
          nlinarith
    simpa only [cross, core, card_product, offDiag_card, Nat.mul_sub_left_distrib, mul_one] using
      (calc 2 * ((c ∩ A).card * (c \ A).card) ≤ 2 * (c ∩ A).card := by nlinarith
            _ ≤ 2 + (c ∩ A).card * ((c ∩ A).card - 1) := ha)
  have hsum := sum_le_sum local_bound
  have hc := card_le_card core_sub
  rw [card_biUnion hcore, offDiag_card, ← Nat.mul_sub_one] at hc
  have hx : (crossEdges G A).card = ∑ c ∈ parts, (cross c).card := by
    rw [← cover, card_biUnion hcross]
  rw [sum_add_distrib] at hsum
  simp only [sum_const, smul_eq_mul] at hsum
  simp_rw [two_mul] at hsum
  rw [sum_add_distrib, ← hx] at hsum
  omega

def completeSplit (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := x ≠ y ∧ (x.isLeft ∨ y.isLeft)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance (a b : ℕ) : DecidableRel (completeSplit a b).Adj :=
  inferInstanceAs (DecidableRel fun (x y : Fin a ⊕ Fin b) =>
    x ≠ y ∧ (x.isLeft ∨ y.isLeft))

theorem completeSplit_lower (a b : ℕ) (parts : Finset (Finset (Fin a ⊕ Fin b)))
    (hp : IsEdgeCliquePartition (completeSplit a b) parts) :
    2 * (a * b) ≤ 2 * parts.card + a * (a - 1) := by
  classical
  let A : Finset (Fin a ⊕ Fin b) := univ.image Sum.inl
  have hA : A.card = a := by
    simp [A, card_image_of_injective _ Sum.inl_injective]
  have hB : (univ \ A).card = b := by
    rw [card_sdiff_of_subset (subset_univ A), card_univ, Fintype.card_sum, hA]
    simp
  have hind : ∀ x ∉ A, ∀ y ∉ A, ¬ (completeSplit a b).Adj x y := by
    intro x hx y hy
    cases x <;> cases y <;> simp_all [A, completeSplit]
  have hcross : crossEdges (completeSplit a b) A = A ×ˢ (univ \ A) := by
    ext ⟨x, y⟩
    simp only [crossEdges, mem_filter, mem_product, mem_sdiff, mem_univ, true_and]
    constructor
    · exact fun h => h.1
    · rintro ⟨hx, hy⟩
      refine ⟨⟨hx, hy⟩, ?_⟩
      cases x <;> cases y <;> simp_all [A, completeSplit]
  have h := lower_bound (completeSplit a b) A hind parts hp
  simpa only [hcross, card_product, hA, hB] using h

theorem proof (t : ℕ) (parts : Finset (Finset (Fin t ⊕ Fin (2 * t))))
    (hp : IsEdgeCliquePartition (completeSplit t (2 * t)) parts) :
    3 * t ^ 2 + t ≤ 2 * parts.card := by
  have h := completeSplit_lower t (2 * t) parts hp
  rcases Nat.eq_zero_or_pos t with ht | ht
  · simp [ht]
  · have hs : t - 1 + 1 = t := Nat.sub_add_cancel ht
    nlinarith

end Submissions.Erdos81SplitLower.SplitLower
