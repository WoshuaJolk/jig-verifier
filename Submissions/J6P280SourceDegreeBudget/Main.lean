import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Original-source neighbourhood budget and its weighted Cauchy consequence.
   Finite A must contain every original neighbour of the selected endpoints.
   This file does not assert the missing asymptotic clean-count upper bound. -/
namespace Submissions.J6P280SourceDegreeBudget.Main
open Finset
noncomputable section

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

def neighbors (A : Finset ℕ) (r x : ℕ) : Finset ℕ :=
  A.filter (fun y => y ≤ x+r ∧ x ≤ y+r)

def positiveEdges (A : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun z => z.1 < z.2 ∧ z.2 ≤ z.1+r)

theorem positive_edges_card_le (A : Finset ℕ) (r : ℕ) (hA : IsSidon A) :
    (positiveEdges A r).card ≤ r := by
  have h := Finset.card_le_card_of_injOn
    (fun z : ℕ × ℕ => z.2-z.1-1)
    (s := positiveEdges A r) (t := Finset.range r)
  apply (h ?_ ?_).trans_eq (Finset.card_range r)
  · intro z hz
    have hh := (Finset.mem_filter.mp hz).2
    apply Finset.mem_range.mpr
    change z.2-z.1-1 < r
    omega
  · intro z hz w hw he
    change z.2-z.1-1 = w.2-w.1-1 at he
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have az := Finset.mem_product.mp hz'.1
    have aw := Finset.mem_product.mp hw'.1
    have eq := hA z.1 az.1 w.2 aw.2 w.1 aw.1 z.2 az.2 (by omega)
    rcases eq with eq | eq
    · exact Prod.ext eq.1 eq.2.symm
    · have := hz'.2.1
      omega

theorem degree_sum_le (A C : Finset ℕ) (r : ℕ)
    (hA : IsSidon A) (hC : C ⊆ A) :
    (∑ x ∈ C, (neighbors A r x).card) ≤ C.card + 2*r := by
  let I := (C ×ˢ A).filter (fun z => z.2 ≤ z.1+r ∧ z.1 ≤ z.2+r)
  let E := positiveEdges A r
  let J := C.image (fun x => (x,x))
  have he : E.card ≤ r := positive_edges_card_le A r hA
  have hi : I.card = ∑ x ∈ C, (neighbors A r x).card := by
    simp only [I, neighbors, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product]
  have hsub : I ⊆ (J ∪ E) ∪ E.image Prod.swap := by
    intro z hz
    have hh := Finset.mem_filter.mp hz
    have hzC := (Finset.mem_product.mp hh.1).1
    have hzA := (Finset.mem_product.mp hh.1).2
    rcases lt_trichotomy z.1 z.2 with h | h | h
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hC hzC,hzA⟩,h,hh.2.1⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨z.1,hzC,Prod.ext rfl h⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(z.2,z.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzA,hC hzC⟩,h,hh.2.2⟩
      · exact Prod.ext rfl rfl
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (J ∪ E) (E.image Prod.swap)
  have h3 := Finset.card_union_le J E
  have h4 : J.card ≤ C.card := Finset.card_image_le
  have h5 : (E.image Prod.swap).card ≤ E.card := Finset.card_image_le
  omega

theorem endpoint_degree_sum_le (A T : Finset ℕ) (u v : ℕ → ℕ) (n : ℕ)
    (hA : IsSidon A) (hend : ∀ e ∈ T, u e ∈ A ∧ v e ∈ A) :
    (∑ x ∈ T.image u ∪ T.image v, (neighbors A (2*n) x).card)
      ≤ 2*T.card + 4*n := by
  have hc : T.image u ∪ T.image v ⊆ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
      exact (hend e he).1
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
      exact (hend e he).2
  have h := degree_sum_le A (T.image u ∪ T.image v) (2*n) hA hc
  have h1 := Finset.card_union_le (T.image u) (T.image v)
  have h2 : (T.image u).card ≤ T.card := Finset.card_image_le
  have h3 : (T.image v).card ≤ T.card := Finset.card_image_le
  omega

theorem degree_pos (A : Finset ℕ) (r x : ℕ) (hx : x ∈ A) :
    0 < (neighbors A r x).card := by
  apply Finset.card_pos.mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨hx,by omega,by omega⟩⟩

theorem actual_degree_cauchy (A C : Finset ℕ) (r : ℕ)
    (hA : IsSidon A) (hC : C ⊆ A)
    (M : Finset (ℕ × ℕ)) (hM : M ⊆ C ×ˢ C) (R : ℕ × ℕ → ℝ) :
    (∑ z ∈ M, R z)^2 ≤
      (∑ z ∈ M, (R z)^2 /
        ((neighbors A r z.1).card * (neighbors A r z.2).card : ℝ)) *
      ((C.card : ℝ) + 2*r)^2 := by
  let d := fun x => ((neighbors A r x).card : ℝ)
  let g := fun z : ℕ × ℕ => d z.1 * d z.2
  let H := ∑ z ∈ M, (R z)^2 / g z
  have hd : ∀ x ∈ C, 0 < d x := by
    intro x hx
    change (0 : ℝ) < ((neighbors A r x).card : ℝ)
    exact_mod_cast degree_pos A r x (hC hx)
  have hg : ∀ z ∈ M, 0 < g z := by
    intro z hz
    have h := Finset.mem_product.mp (hM hz)
    exact mul_pos (hd z.1 h.1) (hd z.2 h.2)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun z hz =>
    div_nonneg (sq_nonneg _) (hg z hz).le)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul M
    (r := R) (f := fun z => (R z)^2/g z) (g := g)
    (fun z hz => div_nonneg (sq_nonneg _) (hg z hz).le)
    (fun z hz => (hg z hz).le)
    (fun z hz => le_of_eq (div_mul_cancel₀ ((R z)^2) (hg z hz).ne').symm)
  have hp : (∑ z ∈ M, g z) ≤ (∑ x ∈ C, d x)^2 := by
    calc
      _ ≤ ∑ z ∈ C ×ˢ C, g z :=
        Finset.sum_le_sum_of_subset_of_nonneg hM (fun z hz _ => by
          have h := Finset.mem_product.mp hz
          exact (mul_pos (hd z.1 h.1) (hd z.2 h.2)).le)
      _ = (∑ x ∈ C, d x)^2 := by
        simp only [g, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hdSum : (∑ x ∈ C, d x) ≤ (C.card : ℝ)+2*r := by
    change (∑ x ∈ C, ((neighbors A r x).card : ℝ)) ≤ (C.card : ℝ)+2*r
    exact_mod_cast degree_sum_le A C r hA hC
  have hn : 0 ≤ ∑ x ∈ C, d x :=
    Finset.sum_nonneg (fun x hx => (hd x hx).le)
  have hsq : (∑ x ∈ C, d x)^2 ≤ ((C.card : ℝ)+2*r)^2 := by
    nlinarith
  exact hs.trans (mul_le_mul_of_nonneg_left (hp.trans hsq) hH)


def CanonicalSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a+b=c+d → a=c ∧ b=d

def sourceNeighbors (A : Set ℕ) (r x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (x+r+1)).filter (fun y => y ∈ A ∧ x ≤ y+r)

theorem finite_sidon_of_canonical (A : Set ℕ) (B : Finset ℕ)
    (hA : CanonicalSidon A) (hB : ∀ x ∈ B, x ∈ A) : IsSidon B := by
  intro a ha b hb c hc d hd heq
  have ha' := hB a ha
  have hb' := hB b hb
  have hc' := hB c hc
  have hd' := hB d hd
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · exact Or.inl (hA a ha' b hb' c hc' d hd' hab hcd heq)
    · exact Or.inr (hA a ha' b hb' d hd' c hc' hab (by omega) (by omega))
  · by_cases hcd : c ≤ d
    · have h := hA b hb' a ha' c hc' d hd' (by omega) hcd (by omega)
      exact Or.inr ⟨h.2,h.1⟩
    · have h := hA b hb' a ha' d hd' c hc' (by omega) (by omega) (by omega)
      exact Or.inl ⟨h.2,h.1⟩

theorem source_degree_sum_le (A : Set ℕ) (C : Finset ℕ) (r : ℕ)
    (hA : CanonicalSidon A) (hC : ∀ x ∈ C, x ∈ A) :
    (∑ x ∈ C, (sourceNeighbors A r x).card) ≤ C.card+2*r := by
  classical
  let B := (Finset.range (C.sup id+r+1)).filter (fun x => x ∈ A)
  have hb : ∀ x ∈ B, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).2
  have hc : C ⊆ B := by
    intro x hx
    have hxmax : x ≤ C.sup id := Finset.le_sup (f := id) hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hC x hx⟩
  have hn : ∀ x ∈ C, neighbors B r x = sourceNeighbors A r x := by
    intro x hx
    have hxmax : x ≤ C.sup id := Finset.le_sup (f := id) hx
    ext y
    simp only [neighbors, B, sourceNeighbors, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hyB,hyA⟩,hy,hx'⟩
      exact ⟨by omega,hyA,hx'⟩
    · rintro ⟨hy,hyA,hx'⟩
      exact ⟨⟨by omega,hyA⟩,by omega,hx'⟩
  have h := degree_sum_le B C r (finite_sidon_of_canonical A B hA hb) hc
  simpa only [Finset.sum_congr rfl (fun x hx => congrArg Finset.card (hn x hx))] using h

theorem source_endpoint_degree_sum_le (A : Set ℕ) (T : Finset ℕ)
    (u v : ℕ → ℕ) (n : ℕ) (hA : CanonicalSidon A)
    (hend : ∀ e ∈ T, u e ∈ A ∧ v e ∈ A) :
    (∑ x ∈ T.image u ∪ T.image v, (sourceNeighbors A (2*n) x).card)
      ≤ 2*T.card+4*n := by
  have hc : ∀ x ∈ T.image u ∪ T.image v, x ∈ A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
      exact (hend e he).1
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
      exact (hend e he).2
  have h := source_degree_sum_le A (T.image u ∪ T.image v) (2*n) hA hc
  have h1 := Finset.card_union_le (T.image u) (T.image v)
  have h2 : (T.image u).card ≤ T.card := Finset.card_image_le
  have h3 : (T.image v).card ≤ T.card := Finset.card_image_le
  omega

theorem proof (A : Set ℕ) (C : Finset ℕ) (r : ℕ)
    (hA : CanonicalSidon A) (hC : ∀ x ∈ C, x ∈ A) :
    (∑ x ∈ C, (sourceNeighbors A r x).card) ≤ C.card + 2*r :=
  source_degree_sum_le A C r hA hC

end
end Submissions.J6P280SourceDegreeBudget.Main

