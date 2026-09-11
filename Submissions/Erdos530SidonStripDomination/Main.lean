import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Linarith

namespace Submissions.Erdos530SidonStripDomination.Main

def IsSidon {α : Type*} [Add α] (S : Finset α) : Prop :=
  ∀ ⦃a b c d : α⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- An injective Freiman map pulls Sidon subsets back without changing their size. -/
theorem pullback_sidon {α β : Type*} [Add α] [Add β] [DecidableEq β]
    (A : Finset α) (f : α → β) (hinj : Set.InjOn f A)
    (hfreiman : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → f a + f b = f c + f d)
    (T : Finset β) (hT : T ⊆ A.image f) (hSidon : IsSidon T) :
    ∃ S : Finset α, S ⊆ A ∧ IsSidon S ∧ S.card = T.card := by
  classical
  obtain ⟨S, hSA, hST⟩ := Finset.subset_image_iff.mp hT
  refine ⟨S, hSA, ?_, ?_⟩
  · intro a b c d ha hb hc hd hsum
    have himage {x : α} (hx : x ∈ S) : f x ∈ T := by
      rw [← hST]
      exact Finset.mem_image_of_mem f hx
    have h := hSidon (himage ha) (himage hb) (himage hc) (himage hd)
      (hfreiman a (hSA ha) b (hSA hb) c (hSA hc) d (hSA hd) hsum)
    rcases h with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact Or.inl ⟨hinj (hSA ha) (hSA hc) hac, hinj (hSA hb) (hSA hd) hbd⟩
    · exact Or.inr ⟨hinj (hSA ha) (hSA hd) had, hinj (hSA hb) (hSA hc) hbc⟩
  · rw [← hST, Finset.card_image_of_injOn (hinj.mono hSA)]


/-- A Sidon alphabet times an integer interval admits an injective forward
Freiman map onto an interval with exactly the same cardinality. -/
theorem sidon_product_interval_model {α : Type*} [Add α]
    (A : Finset α) (hA : IsSidon A) (L : ℕ) :
    ∃ f : α × ℤ → ℤ,
      Set.InjOn f (↑(A ×ˢ Finset.Ico 0 (L : ℤ)) : Set (α × ℤ)) ∧
      (A ×ˢ Finset.Ico 0 (L : ℤ)).image f = Finset.Ico 0 ((A.card * L : ℕ) : ℤ) ∧
      ∀ a ∈ A ×ˢ Finset.Ico 0 (L : ℤ), ∀ b ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
      ∀ c ∈ A ×ˢ Finset.Ico 0 (L : ℤ), ∀ d ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
        a + b = c + d → f a + f b = f c + f d := by
  classical
  let e : ↥A ≃ ↥(Finset.Ico (0 : ℤ) (A.card : ℤ)) :=
    Finset.equivOfCardEq (by simp)
  let r : α → ℤ := fun a => if h : a ∈ A then (e ⟨a, h⟩).val else 0
  have hr (a : α) (ha : a ∈ A) : r a = (e ⟨a, ha⟩).val := by simp [r, ha]
  have hb (a : α) (ha : a ∈ A) : 0 ≤ r a ∧ r a < A.card := by
    rw [hr a ha]
    exact Finset.mem_Ico.mp (e ⟨a, ha⟩).property
  have hi : Set.InjOn r A := by
    intro a ha b hb hab
    rw [hr a ha, hr b hb] at hab
    exact congrArg Subtype.val (e.injective (Subtype.ext hab))
  let f : α × ℤ → ℤ := fun a => r a.1 * L + a.2
  have hf : Set.InjOn f (↑(A ×ˢ Finset.Ico 0 (L : ℤ)) : Set (α × ℤ)) := by
    intro a ha b hb hab
    obtain ⟨haA, haI⟩ := Finset.mem_product.mp ha
    obtain ⟨hbA, hbI⟩ := Finset.mem_product.mp hb
    obtain ⟨ha0, haL⟩ := Finset.mem_Ico.mp haI
    obtain ⟨hb0, hbL⟩ := Finset.mem_Ico.mp hbI
    change r a.1 * L + a.2 = r b.1 * L + b.2 at hab
    have hrab : r a.1 = r b.1 := by
      by_contra hne
      have h : r a.1 + 1 ≤ r b.1 ∨ r b.1 + 1 ≤ r a.1 := by omega
      rcases h with h | h <;> nlinarith
    exact Prod.ext (hi haA hbA hrab) (by nlinarith)
  have himage : (A ×ˢ Finset.Ico 0 (L : ℤ)).image f =
      Finset.Ico 0 ((A.card * L : ℕ) : ℤ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨haA, haI⟩ := Finset.mem_product.mp ha
      obtain ⟨ha0, haL⟩ := Finset.mem_Ico.mp haI
      obtain ⟨hr0, hrN⟩ := hb a.1 haA
      have hrN' : r a.1 + 1 ≤ A.card := by omega
      apply Finset.mem_Ico.mpr
      dsimp only [f]
      push_cast
      constructor <;> nlinarith
    · rw [Finset.card_image_of_injOn hf, Finset.card_product]
      simp
  refine ⟨f, hf, himage, ?_⟩
  intro a ha b hb c hc d hd hsum
  have hfirst := congrArg Prod.fst hsum
  have hsecond := congrArg Prod.snd hsum
  change a.1 + b.1 = c.1 + d.1 at hfirst
  change a.2 + b.2 = c.2 + d.2 at hsecond
  rcases hA (Finset.mem_product.mp ha).1 (Finset.mem_product.mp hb).1
    (Finset.mem_product.mp hc).1 (Finset.mem_product.mp hd).1 hfirst with
    ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · dsimp only [f]
    rw [hac, hbd]
    linarith
  · dsimp only [f]
    rw [had, hbc]
    linarith

/-- Every Sidon subset of the equal-size interval pulls back to the product. -/
theorem sidon_product_interval_domination {α : Type*} [Add α]
    (A : Finset α) (hA : IsSidon A) (L : ℕ)
    (T : Finset ℤ) (hT : T ⊆ Finset.Ico 0 ((A.card * L : ℕ) : ℤ))
    (hSidon : IsSidon T) :
    ∃ S : Finset (α × ℤ), S ⊆ A ×ˢ Finset.Ico 0 (L : ℤ) ∧
      IsSidon S ∧ S.card = T.card := by
  obtain ⟨f, hf, himage, hsum⟩ := sidon_product_interval_model A hA L
  exact pullback_sidon _ f hf hsum T (by simpa only [himage] using hT) hSidon

/-- A gap of twice the interval length prevents every carry in pair sums. -/
theorem integer_strip_encoding (A : Finset ℤ) (L : ℕ) (M : ℤ) (hM : 2 * L ≤ M) :
    Set.InjOn (fun a : ℤ × ℤ => M * a.1 + a.2)
      (↑(A ×ˢ Finset.Ico 0 (L : ℤ)) : Set (ℤ × ℤ)) ∧
    ∀ a ∈ A ×ˢ Finset.Ico 0 (L : ℤ), ∀ b ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
    ∀ c ∈ A ×ˢ Finset.Ico 0 (L : ℤ), ∀ d ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
      (M * a.1 + a.2) + (M * b.1 + b.2) =
        (M * c.1 + c.2) + (M * d.1 + d.2) → a + b = c + d := by
  have hreflect : ∀ a ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
      ∀ b ∈ A ×ˢ Finset.Ico 0 (L : ℤ), ∀ c ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
      ∀ d ∈ A ×ˢ Finset.Ico 0 (L : ℤ),
      (M * a.1 + a.2) + (M * b.1 + b.2) =
        (M * c.1 + c.2) + (M * d.1 + d.2) → a + b = c + d := by
    intro a ha b hb c hc d hd h
    obtain ⟨ha0, haL⟩ := Finset.mem_Ico.mp (Finset.mem_product.mp ha).2
    obtain ⟨hb0, hbL⟩ := Finset.mem_Ico.mp (Finset.mem_product.mp hb).2
    obtain ⟨hc0, hcL⟩ := Finset.mem_Ico.mp (Finset.mem_product.mp hc).2
    obtain ⟨hd0, hdL⟩ := Finset.mem_Ico.mp (Finset.mem_product.mp hd).2
    have hfirst : a.1 + b.1 = c.1 + d.1 := by
      by_contra hne
      have hh : a.1 + b.1 + 1 ≤ c.1 + d.1 ∨ c.1 + d.1 + 1 ≤ a.1 + b.1 := by omega
      rcases hh with hh | hh <;> nlinarith
    exact Prod.ext hfirst (by dsimp; nlinarith)
  refine ⟨?_, hreflect⟩
  intro a ha b hb h
  have hh := hreflect a ha a ha b hb b hb (by linarith)
  have hfirst := congrArg Prod.fst hh
  have hsecond := congrArg Prod.snd hh
  exact Prod.ext (by dsimp at hfirst; omega) (by dsimp at hsecond; omega)

/-- Integer strips with a Sidon alphabet have the same-cardinality interval's
Sidon subsets available, with no asymptotic or size loss. -/
theorem integer_sidon_strip_domination (A : Finset ℤ) (hA : IsSidon A)
    (L : ℕ) (M : ℤ) (hM : 2 * L ≤ M) :
    ((A ×ˢ Finset.Ico 0 (L : ℤ)).image (fun a => M * a.1 + a.2)).card = A.card * L ∧
    ∀ T : Finset ℤ, T ⊆ Finset.Ico 0 ((A.card * L : ℕ) : ℤ) → IsSidon T →
      ∃ S : Finset ℤ,
        S ⊆ (A ×ˢ Finset.Ico 0 (L : ℤ)).image (fun a => M * a.1 + a.2) ∧
        IsSidon S ∧ S.card = T.card := by
  obtain ⟨hinj, hreflect⟩ := integer_strip_encoding A L M hM
  constructor
  · rw [Finset.card_image_of_injOn hinj, Finset.card_product]
    simp
  · intro T hT hSidon
    obtain ⟨S, hSA, hS, hcard⟩ := sidon_product_interval_domination A hA L T hT hSidon
    refine ⟨S.image (fun a => M * a.1 + a.2), Finset.image_subset_image hSA, ?_, ?_⟩
    · intro a b c d ha hb hc hd hsum
      obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨d, hdS, rfl⟩ := Finset.mem_image.mp hd
      rcases hS haS hbS hcS hdS
        (hreflect a (hSA haS) b (hSA hbS) c (hSA hcS) d (hSA hdS) hsum) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rw [Finset.card_image_of_injOn (hinj.mono hSA), hcard]

abbrev statement : Prop :=
  ∀ A : Finset ℤ, IsSidon A → ∀ (L : ℕ) (M : ℤ), 2 * L ≤ M →
    ((A ×ˢ Finset.Ico 0 (L : ℤ)).image (fun a => M * a.1 + a.2)).card = A.card * L ∧
    ∀ T : Finset ℤ, T ⊆ Finset.Ico 0 ((A.card * L : ℕ) : ℤ) → IsSidon T →
      ∃ S : Finset ℤ,
        S ⊆ (A ×ˢ Finset.Ico 0 (L : ℤ)).image (fun a => M * a.1 + a.2) ∧
        IsSidon S ∧ S.card = T.card

theorem proof : statement := integer_sidon_strip_domination

end Submissions.Erdos530SidonStripDomination.Main
