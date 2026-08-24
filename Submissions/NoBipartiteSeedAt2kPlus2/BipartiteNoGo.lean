import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace Submissions.NoBipartiteSeedAt2kPlus2.BipartiteNoGo

noncomputable section

def localSpan {k n : ℕ} (a : Fin n → EuclideanSpace ℂ (Fin k))
    (S : Finset (Fin n)) : Submodule ℂ (EuclideanSpace ℂ (Fin k)) :=
  Submodule.span ℂ (Set.range fun i : (S : Set (Fin n)) => a i.1)

lemma orthogonal_span_proper
    {k n : ℕ} {a : Fin n → EuclideanSpace ℂ (Fin k)}
    {z : EuclideanSpace ℂ (Fin k)} (hz : z ≠ 0)
    {S : Finset (Fin n)}
    (horth : ∀ j ∈ S, inner ℂ z (a j) = 0) :
    localSpan a S ≠ ⊤ := by
  have hle : localSpan a S ≤ (ℂ ∙ z)ᗮ := by
    rw [localSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    apply ((ℂ ∙ z).mem_orthogonal (a j.1)).2
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [inner_smul_left, horth j.1 j.2]
  intro htop
  have hztop : z ∈ localSpan a S := by rw [htop]; exact Submodule.mem_top
  have hzorth := hle hztop
  have hself : inner ℂ z z = 0 :=
    ((ℂ ∙ z).mem_orthogonal z).mp hzorth z
      (Submodule.mem_span_singleton_self z)
  exact hz (inner_self_eq_zero.mp hself)

lemma every_cosingleton_is_polar
    {k : ℕ}
    {a b : Fin (k + 1) → EuclideanSpace ℂ (Fin k)}
    (hb : ∀ i, b i ≠ 0)
    (hrow : ∀ i,
      (Finset.univ.filter fun j => inner ℂ (b i) (a j) = 0).card = k)
    (hcol : ∀ j,
      (Finset.univ.filter fun i => inner ℂ (b i) (a j) = 0).card = k) :
    ∀ r, localSpan a (Finset.univ.erase r) ≠ ⊤ := by
  intro r
  have homit : ∃ i : Fin (k + 1), inner ℂ (b i) (a r) ≠ 0 := by
    by_contra h
    push Not at h
    have hall :
        Finset.univ.filter (fun i => inner ℂ (b i) (a r) = 0) = Finset.univ := by
      apply Finset.filter_eq_self.2
      intro i _
      exact h i
    have hc := hcol r
    rw [hall, Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨i, hir⟩ := homit
  let N := Finset.univ.filter fun j => inner ℂ (b i) (a j) = 0
  have hsub : N ⊆ Finset.univ.erase r := by
    intro j hj
    have hjzero : inner ℂ (b i) (a j) = 0 := (Finset.mem_filter.mp hj).2
    have hjr : j ≠ r := by
      intro h
      subst j
      exact hir hjzero
    exact Finset.mem_erase.mpr ⟨hjr, Finset.mem_univ j⟩
  have hNcard : N.card = k := hrow i
  have herasecard : (Finset.univ.erase r).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hNeq : N = Finset.univ.erase r :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [← hNeq]
  apply orthogonal_span_proper (hb i)
  intro j hj
  exact (Finset.mem_filter.mp hj).2

lemma irredundant_spanning_is_independent
    {k : ℕ} {a : Fin (k + 1) → EuclideanSpace ℂ (Fin k)}
    (hspan : localSpan a Finset.univ = ⊤)
    (hproper : ∀ r, localSpan a (Finset.univ.erase r) ≠ ⊤) :
    LinearIndependent ℂ a := by
  rw [linearIndependent_iff_notMem_span]
  intro r hr
  have hset :
      Set.range (fun i : (Finset.univ.erase r : Set (Fin (k + 1))) => a i.1) =
        a '' (Set.univ \ {r}) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j.1, ?_, rfl⟩
      have hj := (Finset.mem_erase.mp j.2).1
      simp [hj]
    · rintro ⟨j, hj, rfl⟩
      have hjr : j ≠ r := by simpa using hj
      exact ⟨⟨j, Finset.mem_erase.mpr ⟨hjr, Finset.mem_univ j⟩⟩, rfl⟩
  have hr' : a r ∈ localSpan a (Finset.univ.erase r) := by
    rw [localSpan, hset]
    exact hr
  apply hproper r
  apply le_antisymm le_top
  rw [← hspan, localSpan, localSpan, Submodule.span_le]
  intro x hx
  obtain ⟨j, rfl⟩ := hx
  by_cases hj : j.1 = r
  · change a j.1 ∈ localSpan a (Finset.univ.erase r)
    simpa [hj] using hr'
  · apply Submodule.subset_span
    exact ⟨⟨j.1, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩, rfl⟩

theorem proof :
    ∀ k : ℕ, 2 ≤ k →
      ∀ a b : Fin (k + 1) → EuclideanSpace ℂ (Fin k),
        (∀ i, b i ≠ 0) →
        localSpan a Finset.univ = ⊤ →
        (∀ i, (Finset.univ.filter fun j => inner ℂ (b i) (a j) = 0).card = k) →
        (∀ j, (Finset.univ.filter fun i => inner ℂ (b i) (a j) = 0).card = k) →
        False := by
  intro k hk a b hb hspan hrow hcol
  have hproper := every_cosingleton_is_polar hb hrow hcol
  have hli := irredundant_spanning_is_independent hspan hproper
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hcard
  omega

end

end Submissions.NoBipartiteSeedAt2kPlus2.BipartiteNoGo
