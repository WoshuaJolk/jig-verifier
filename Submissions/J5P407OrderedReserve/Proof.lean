import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Submissions.J5P407OrderedReserve.Proof

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

noncomputable def mass (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, w i

noncomputable def upperTail (key : ι → ℝ) (q : ℝ) (s : Finset ι) : Finset ι :=
  s.filter fun i => q ≤ key i

theorem mass_mono {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {s t : Finset ι} (hst : s ⊆ t) : mass w s ≤ mass w t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => hw i)

theorem mass_union_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (s t : Finset ι) : mass w (s ∪ t) ≤ mass w s + mass w t := by
  have h : mass w (s ∪ t) + mass w (s ∩ t) = mass w s + mass w t :=
    Finset.sum_union_inter
  have hn : 0 ≤ mass w (s ∩ t) := Finset.sum_nonneg (fun i _ => hw i)
  change mass w (s ∪ t) + mass w (s ∩ t) = mass w s + mass w t at h
  linarith

theorem reserve_below_cutoff {w key : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {B R C : Finset ι} {q t : ℝ} (hRB : R ⊆ B)
    (horder : ∀ i ∈ C, ∀ j ∈ R \ C, key i ≤ key j)
    (hsupply : t < mass w (R \ C))
    (hsmall : mass w (upperTail key q (B \ C)) ≤ t) :
    ∀ i ∈ C, key i < q := by
  intro i hi
  by_contra hn
  have hqi : q ≤ key i := le_of_not_gt hn
  have hsub : R \ C ⊆ upperTail key q (B \ C) := by
    intro j hj
    have hrj := Finset.mem_sdiff.mp hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hRB hrj.1, hrj.2⟩, hqi.trans (horder i hi j hj)⟩
  exact (not_lt_of_ge ((mass_mono hw hsub).trans hsmall)) hsupply

theorem tail_unchanged {key : ι → ℝ} {B C : Finset ι} {q : ℝ}
    (hbelow : ∀ i ∈ C, key i < q) :
    upperTail key q B = upperTail key q (B \ C) := by
  ext i
  simp only [upperTail, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hi, hq⟩
    exact ⟨⟨hi, fun hic => (not_lt_of_ge hq) (hbelow i hic)⟩, hq⟩
  · rintro ⟨⟨hi, _⟩, hq⟩
    exact ⟨hi, hq⟩

theorem original_tail_cover {w key : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {O I S T H : Finset ι} {q : ℝ}
    (hcover : ∀ i ∈ O, i ∈ I ∨ i ∈ S ∨ i ∈ T ∨ i ∈ H)
    (hlow : ∀ i ∈ H, key i < q) :
    mass w (upperTail key q O) ≤ mass w (upperTail key q I) + mass w S + mass w T := by
  have hsub : upperTail key q O ⊆ (upperTail key q I ∪ S) ∪ T := by
    intro i hi
    have h := Finset.mem_filter.mp hi
    rcases hcover i h.1 with hiI | hiS | hiT | hiH
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hiI, h.2⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hiS)))
    · exact Finset.mem_union.mpr (Or.inr hiT)
    · exact False.elim ((not_lt_of_ge h.2) (hlow i hiH))
  have h1 := mass_mono hw hsub
  have h2 := mass_union_le hw (upperTail key q I ∪ S) T
  have h3 := mass_union_le hw (upperTail key q I) S
  linarith

theorem proof
    {w key : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {O I S T H B R C : Finset ι} {q tau Delta : ℝ}
    (hcover : ∀ i ∈ O, i ∈ I ∨ i ∈ S ∨ i ∈ T ∨ i ∈ H)
    (hlow : ∀ i ∈ H, key i < q)
    (hselected : mass w S < 1) (htop : mass w T < 64 + tau)
    (htau : tau < 1 / 8) (hDelta : Delta < 1 / 8)
    (hRB : R ⊆ B)
    (horder : ∀ i ∈ C, ∀ j ∈ R \ C, key i ≤ key j)
    (hsupply : 1 + Delta < mass w (R \ C))
    (hsmall : mass w (upperTail key q (B \ C)) < 1 + Delta)
    (hbalance : |mass w (upperTail key q B) - mass w (upperTail key q I) / 2| < 1 / 8) :
    mass w (upperTail key q O) < 68 := by
  have hbelow := reserve_below_cutoff hw hRB horder hsupply hsmall.le
  have heq := tail_unchanged hbelow (B := B)
  have hb : mass w (upperTail key q B) < 1 + Delta := by
    rw [heq]
    exact hsmall
  have hbal := (abs_lt.mp hbalance).1
  have hi : mass w (upperTail key q I) < 9 / 4 + 2 * Delta := by linarith
  have hfull := original_tail_cover hw hcover hlow
  linarith

end Submissions.J5P407OrderedReserve.Proof

