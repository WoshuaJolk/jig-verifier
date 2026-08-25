import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos155SubadditiveBound.Direct

def IsSidon (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)

noncomputable def maxSidonSubsetCard (A : Finset ℕ) : ℕ := by
  classical
  exact (A.powerset.filter IsSidon).sup Finset.card

noncomputable abbrev F (N : ℕ) : ℕ :=
  maxSidonSubsetCard (Finset.Icc 1 N)

lemma IsSidon.subset {A B : Finset ℕ} (hB : IsSidon B) (hAB : A ⊆ B) :
    IsSidon A := by
  intro a b c d ha hb hc hd hsum
  exact hB (hAB ha) (hAB hb) (hAB hc) (hAB hd) hsum

theorem proof : ∀ N k : ℕ, F (N + k) ≤ F N + F k := by
  classical
  intro N k
  let big : Finset ℕ := Finset.Icc 1 (N + k)
  let small : Finset ℕ := Finset.Icc 1 N
  have hfamily : (big.powerset.filter IsSidon).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [IsSidon]
  obtain ⟨B, hBmem, hmax⟩ :=
    Finset.exists_mem_eq_sup (big.powerset.filter IsSidon) hfamily Finset.card
  have hBdata := Finset.mem_filter.mp hBmem
  have hBsub : B ⊆ big := Finset.mem_powerset.mp hBdata.1
  have hBsidon : IsSidon B := hBdata.2
  let C : Finset ℕ := B ∩ small
  let E : Finset ℕ := B \ small
  let D : Finset ℕ := E.image fun x => x - N
  have hCmem : C ∈ small.powerset.filter IsSidon := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    exact hBsidon.subset Finset.inter_subset_left
  have hCle : C.card ≤ maxSidonSubsetCard small :=
    Finset.le_sup (f := Finset.card) hCmem
  have hEabove : ∀ x ∈ E, N < x := by
    intro x hx
    have hxmem := Finset.mem_sdiff.mp hx
    have hxbig := Finset.mem_Icc.mp (hBsub hxmem.1)
    by_contra! hxN
    exact hxmem.2 (Finset.mem_Icc.mpr ⟨hxbig.1, hxN⟩)
  have hDsub : D ⊆ Finset.Icc 1 k := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hybig := Finset.mem_Icc.mp (hBsub (Finset.mem_sdiff.mp hy).1)
    have hyabove := hEabove y hy
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hDsidon : IsSidon D := by
    intro a b c d ha hb hc hd hsum
    rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
    rcases Finset.mem_image.mp hc with ⟨c', hc', rfl⟩
    rcases Finset.mem_image.mp hd with ⟨d', hd', rfl⟩
    have haB := (Finset.mem_sdiff.mp ha').1
    have hbB := (Finset.mem_sdiff.mp hb').1
    have hcB := (Finset.mem_sdiff.mp hc').1
    have hdB := (Finset.mem_sdiff.mp hd').1
    have hsum' : a' + b' = c' + d' := by
      have haN := hEabove a' ha'
      have hbN := hEabove b' hb'
      have hcN := hEabove c' hc'
      have hdN := hEabove d' hd'
      omega
    rcases hBsidon haB hbB hcB hdB hsum' with hpair | hswap
    · left
      omega
    · right
      omega
  have hDmem : D ∈ (Finset.Icc 1 k).powerset.filter IsSidon :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hDsub, hDsidon⟩
  have hDle : D.card ≤ maxSidonSubsetCard (Finset.Icc 1 k) :=
    Finset.le_sup (f := Finset.card) hDmem
  have hshift_inj : Set.InjOn (fun x : ℕ => x - N) E := by
    intro x hx y hy hxy
    have hxN := hEabove x hx
    have hyN := hEabove y hy
    change x - N = y - N at hxy
    calc
      x = (x - N) + N := (Nat.sub_add_cancel (Nat.le_of_lt hxN)).symm
      _ = (y - N) + N := by rw [hxy]
      _ = y := Nat.sub_add_cancel (Nat.le_of_lt hyN)
  have hDcard : D.card = E.card := by
    exact Finset.card_image_of_injOn hshift_inj
  have hsplit : C.card + E.card = B.card := by
    exact Finset.card_inter_add_card_sdiff B small
  change maxSidonSubsetCard big ≤
    maxSidonSubsetCard small + maxSidonSubsetCard (Finset.Icc 1 k)
  rw [maxSidonSubsetCard, hmax]
  omega

end Submissions.Erdos155SubadditiveBound.Direct
