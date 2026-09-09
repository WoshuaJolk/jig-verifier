import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# A finite reduction to member-transitive sunflower-free families

For a finite family with M members, use all M! words that place each member
exactly once on M disjoint rows. Row permutations preserve the resulting
family and act transitively on its members. The elementary inequality
M^M ≤ (M!)^2 then transfers a transitive bound with base B to a general bound
with base B^2. This is a reduction, not an exponential sunflower bound.

The two projection lemmas below are copied from the locally audited
`p16/reduction/Tensor.lean`, lines 475–505. That source attributes the standard
uniform product argument to Tang–Zhang, arXiv:2512.20055, footnote to (1.2).
No `Submissions` or `Statements` module is imported here. `IsSunflower` is the
same ordinary pairwise-intersection definition used in that source.
-/

namespace Submissions.Erdos20MemberTransitive.Transitive

def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

def SunflowerFree {α : Type} (r : ℕ) (family : Set (Set α)) : Prop :=
  ¬ ∃ subfamily ⊆ family, subfamily.ncard = r ∧ IsSunflower subfamily

/-- The ambient permutations must preserve the whole family, as well as carry
any specified member to any other member. -/
def MemberTransitive {α : Type} (family : Set (Set α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, ∃ e : Equiv.Perm α,
    (fun S : Set α => e '' S) '' family = family ∧ e '' A = B

def MemberTransitiveBound (r B : ℕ) : Prop :=
  ∀ {α : Type} (w : ℕ) (family : Set (Set α)),
    0 < w → family.Finite →
    (∀ member ∈ family, member.ncard = w) →
    SunflowerFree r family → MemberTransitive family → family.ncard ≤ B ^ w

def UniformBound (r B : ℕ) : Prop :=
  ∀ {α : Type} (w : ℕ) (family : Set (Set α)),
    0 < w → family.Finite →
    (∀ member ∈ family, member.ncard = w) →
    SunflowerFree r family → family.ncard ≤ B ^ w

/-- Copied projection dichotomy: an antichain projection of an indexed
sunflower is injective or constant. -/
theorem projection_injective_or_constant {ι α : Type} {H : Set ι} {f : ι → Set α}
    (hanti : ∀ i ∈ H, ∀ j ∈ H, f i ⊆ f j → f i = f j)
    (hsun : ∃ K, H.Pairwise fun i j => f i ∩ f j = K) :
    Set.InjOn f H ∨ ∃ K, ∀ i ∈ H, f i = K := by
  classical
  by_cases hinj : Set.InjOn f H
  · exact Or.inl hinj
  · right
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨i, hi, j, hj, heq, hne⟩ := hinj
    obtain ⟨K, hK⟩ := hsun
    have hiK : f i = K := by simpa [heq] using hK hi hj hne
    refine ⟨f i, ?_⟩
    intro l hl
    by_cases hli : l = i
    · exact congrArg f hli
    · apply Eq.symm
      apply hanti i hi l hl
      have hil := hK hi hl (Ne.symm hli)
      rw [← hiK] at hil
      exact fun x hx => (show x ∈ f i ∩ f l from hil.symm ▸ hx).2

/-- Copied preservation of sunflowers under point-map preimages. -/
theorem sunflower_preimage_image {α β : Type} {H : Set (Set β)}
    (hsun : IsSunflower H) (f : α → β) :
    IsSunflower ((fun S => f ⁻¹' S) '' H) := by
  obtain ⟨K, hK⟩ := hsun
  refine ⟨f ⁻¹' K, ?_⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
  have hab : A ≠ B := fun h => hne (congrArg (fun S => f ⁻¹' S) h)
  exact congrArg (fun S => f ⁻¹' S) (hK hA hB hab)

def rowSection {ι α : Type} (i : ι) (S : Set (ι × α)) : Set α :=
  (fun x => (i, x)) ⁻¹' S

def permutationWord {α : Type} (F : Set (Set α))
    (σ : Equiv.Perm F) : Set (F × α) :=
  {p | p.2 ∈ (σ p.1 : Set α)}

def permutationFamily {α : Type} (F : Set (Set α)) : Set (Set (F × α)) :=
  Set.range (permutationWord F)

@[simp] theorem rowSection_permutationWord {α : Type} (F : Set (Set α))
    (σ : Equiv.Perm F) (i : F) :
    rowSection i (permutationWord F σ) = (σ i : Set α) := rfl

theorem permutationWord_injective {α : Type} (F : Set (Set α)) :
    Function.Injective (permutationWord F) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  apply Subtype.ext
  simpa only [rowSection_permutationWord] using congrArg (rowSection i) h

theorem permutationFamily_finite {α : Type} {F : Set (Set α)} (hF : F.Finite) :
    (permutationFamily F).Finite := by
  classical
  let : Fintype F := hF.fintype
  simpa only [Set.image_univ, permutationFamily] using
    (Set.finite_univ.image (permutationWord F))

theorem permutationFamily_ncard {α : Type} {F : Set (Set α)} (hF : F.Finite) :
    (permutationFamily F).ncard = F.ncard.factorial := by
  classical
  let : Fintype F := hF.fintype
  rw [permutationFamily, Set.ncard_range_of_injective (permutationWord_injective F),
    Nat.card_eq_fintype_card, Fintype.card_perm, Set.fintypeCard_eq_ncard]

theorem permutationWord_ncard {α : Type} {F : Set (Set α)} {w : ℕ}
    (hF : F.Finite) (hw : 0 < w)
    (hU : ∀ A ∈ F, A.ncard = w) (σ : Equiv.Perm F) :
    (permutationWord F σ).ncard = F.ncard * w := by
  classical
  let : Fintype F := hF.fintype
  let : ∀ i : F, Fintype (σ i : Set α) := fun i =>
    (Set.finite_of_ncard_pos (by rw [hU _ (σ i).property]; exact hw)).fintype
  let e : permutationWord F σ ≃ Σ i : F, (σ i : Set α) :=
    Equiv.setProdEquivSigma (permutationWord F σ)
  let : Fintype (permutationWord F σ) := Fintype.ofEquiv _ e.symm
  calc
    (permutationWord F σ).ncard = Fintype.card (permutationWord F σ) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ = Fintype.card (Σ i : F, (σ i : Set α)) := Fintype.card_congr e
    _ = ∑ i : F, Fintype.card (σ i : Set α) := Fintype.card_sigma
    _ = ∑ _i : F, w := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Set.fintypeCard_eq_ncard, hU _ (σ i).property]
    _ = F.ncard * w := by simp [Set.fintypeCard_eq_ncard]

theorem permutationFamily_uniform {α : Type} {F : Set (Set α)} {w : ℕ}
    (hF : F.Finite) (hw : 0 < w) (hU : ∀ A ∈ F, A.ncard = w) :
    ∀ S ∈ permutationFamily F, S.ncard = F.ncard * w := by
  rintro S ⟨σ, rfl⟩
  exact permutationWord_ncard hF hw hU σ

theorem rowPermutation_image_word {α : Type} (F : Set (Set α))
    (ρ σ : Equiv.Perm F) :
    (Equiv.prodCongr ρ (Equiv.refl α)) '' permutationWord F σ =
      permutationWord F (ρ.symm.trans σ) := by
  rw [Equiv.image_eq_preimage_symm]
  rfl

theorem rowPermutation_preserves_family {α : Type} (F : Set (Set α))
    (ρ : Equiv.Perm F) :
    (fun S : Set (F × α) => (Equiv.prodCongr ρ (Equiv.refl α)) '' S) ''
      permutationFamily F = permutationFamily F := by
  apply Set.Subset.antisymm
  · rintro S ⟨A, ⟨σ, rfl⟩, rfl⟩
    change (Equiv.prodCongr ρ (Equiv.refl α)) '' permutationWord F σ ∈
      permutationFamily F
    rw [rowPermutation_image_word]
    exact ⟨ρ.symm.trans σ, rfl⟩
  · rintro S ⟨τ, rfl⟩
    refine ⟨permutationWord F (ρ.trans τ), ⟨ρ.trans τ, rfl⟩, ?_⟩
    change (Equiv.prodCongr ρ (Equiv.refl α)) '' permutationWord F (ρ.trans τ) =
      permutationWord F τ
    rw [rowPermutation_image_word]
    apply congrArg (permutationWord F)
    ext i
    simp

theorem permutationFamily_memberTransitive {α : Type} (F : Set (Set α)) :
    MemberTransitive (permutationFamily F) := by
  intro A hA B hB
  obtain ⟨σ, rfl⟩ := hA
  obtain ⟨τ, rfl⟩ := hB
  let ρ : Equiv.Perm F := σ.trans τ.symm
  refine ⟨Equiv.prodCongr ρ (Equiv.refl α), rowPermutation_preserves_family F ρ, ?_⟩
  rw [rowPermutation_image_word]
  apply congrArg (permutationWord F)
  ext i
  simp [ρ]

/-- The row argument handles every petal count r > 1; no reduction from three
petals to all petal counts is used. -/
theorem permutationFamily_sunflowerFree {α : Type} {F : Set (Set α)} {w r : ℕ}
    (hw : 0 < w) (hr : 1 < r) (hU : ∀ A ∈ F, A.ncard = w)
    (hfree : SunflowerFree r F) : SunflowerFree r (permutationFamily F) := by
  rintro ⟨H, hH, hcard, hsun⟩
  have hHfin : H.Finite := Set.finite_of_ncard_pos (by
    rw [hcard]
    exact Nat.zero_lt_of_lt hr)
  have hrow : ∀ i : F, ∀ S ∈ H, rowSection i S ∈ F := by
    intro i S hS
    obtain ⟨σ, rfl⟩ := hH hS
    simpa only [rowSection_permutationWord] using (σ i).property
  have hconstant : ∀ i : F, ∃ K : Set α, ∀ S ∈ H, rowSection i S = K := by
    intro i
    have hanti : ∀ S ∈ H, ∀ T ∈ H,
        rowSection i S ⊆ rowSection i T → rowSection i S = rowSection i T := by
      intro S hS T hT hsub
      exact Set.eq_of_subset_of_ncard_le hsub
        (by rw [hU _ (hrow i S hS), hU _ (hrow i T hT)])
        (Set.finite_of_ncard_pos (by rw [hU _ (hrow i T hT)]; exact hw))
    have hproj : ∃ K, H.Pairwise fun S T =>
        rowSection i S ∩ rowSection i T = K := by
      obtain ⟨K, hK⟩ := hsun
      refine ⟨rowSection i K, ?_⟩
      intro S hS T hT hne
      exact congrArg (rowSection i) (hK hS hT hne)
    rcases projection_injective_or_constant hanti hproj with hinj | hconst
    · exfalso
      apply hfree
      refine ⟨rowSection i '' H, ?_, hinj.ncard_image.trans hcard, ?_⟩
      · rintro S ⟨T, hT, rfl⟩
        exact hrow i T hT
      · exact sunflower_preimage_image hsun (fun x => (i, x))
    · exact hconst
  have hsmall : H.ncard ≤ 1 := (Set.ncard_le_one hHfin).2 (by
    intro S hS T hT
    apply Set.ext
    rintro ⟨i, x⟩
    obtain ⟨K, hK⟩ := hconstant i
    have heq : rowSection i S = rowSection i T :=
      (hK S hS).trans (hK T hT).symm
    exact Set.ext_iff.mp heq x)
  rw [hcard] at hsmall
  exact (Nat.not_le_of_gt hr) hsmall

/-- Pair the increasing and decreasing factors in a factorial. -/
theorem pow_le_factorial_sq (M : ℕ) : M ^ M ≤ M.factorial ^ 2 := by
  have hpoint : ∀ i ∈ Finset.range M, M ≤ (i + 1) * (M - i) := by
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hpos : 0 < M - i := Nat.sub_pos_of_lt hiM
    calc
      M = (M - i) + i := (Nat.sub_add_cancel (Nat.le_of_lt hiM)).symm
      _ ≤ (M - i) + i * (M - i) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right i hpos) _
      _ = (i + 1) * (M - i) := by simp [Nat.add_mul, Nat.add_comm]
  calc
    M ^ M = ∏ _i ∈ Finset.range M, M := by simp
    _ ≤ ∏ i ∈ Finset.range M, (i + 1) * (M - i) := Finset.prod_le_prod' hpoint
    _ = (∏ i ∈ Finset.range M, (i + 1)) * (∏ i ∈ Finset.range M, (M - i)) :=
      Finset.prod_mul_distrib
    _ = M.factorial * M.factorial := by
      rw [Finset.prod_range_add_one_eq_factorial,
        ← Nat.descFactorial_eq_prod_range M M, Nat.descFactorial_self]
    _ = M.factorial ^ 2 := (pow_two _).symm

/-- A member-transitive exponential bound with natural base B implies a bound
with base B^2 for every finite positive-width uniform family, for each fixed
petal count r ≥ 3. Empty families are included. -/
theorem proves (r B : ℕ) (hr : 3 ≤ r)
    (hB : MemberTransitiveBound r B) : UniformBound r (B ^ 2) := by
  intro α w F hw hF hU hfree
  by_cases hM : F.ncard = 0
  · rw [hM]
    exact Nat.zero_le _
  have hMpos : 0 < F.ncard := Nat.pos_of_ne_zero hM
  have hr' : 1 < r := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hr
  have hword : (permutationFamily F).ncard ≤ B ^ (F.ncard * w) :=
    hB (F.ncard * w) (permutationFamily F) (Nat.mul_pos hMpos hw)
      (permutationFamily_finite hF) (permutationFamily_uniform hF hw hU)
      (permutationFamily_sunflowerFree hw hr' hU hfree)
      (permutationFamily_memberTransitive F)
  rw [permutationFamily_ncard hF] at hword
  have hp : F.ncard ^ F.ncard ≤ ((B ^ 2) ^ w) ^ F.ncard := by
    calc
      F.ncard ^ F.ncard ≤ F.ncard.factorial ^ 2 := pow_le_factorial_sq _
      _ ≤ (B ^ (F.ncard * w)) ^ 2 := Nat.pow_le_pow_left hword 2
      _ = ((B ^ 2) ^ w) ^ F.ncard := by
        simp only [← pow_mul]
        congr 1
        ac_rfl
  exact (Nat.pow_le_pow_iff_left hM).mp hp

end Submissions.Erdos20MemberTransitive.Transitive
