import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Submissions.J4P280SidonBlockEnergy.Proof

/- Finite shared short-difference packing. The analytic power-range estimate
   and the canonical asymptotic application are separate paper arguments. -/
namespace SidonBlockEnergy

open Finset

noncomputable section

def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

def UniquePositiveDifferences (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a < b → c < d → b - a = d - c → a = c ∧ b = d

/- Standard bridge, adapted from the already checked SidonDifferences module. -/
theorem sidon_iff_uniquePositiveDifferences (A : Set ℕ) :
    IsSidon A ↔ UniquePositiveDifferences A := by
  constructor
  · intro h a b c d ha hb hc hd hab hcd heq
    by_cases had : a ≤ d
    · by_cases hcb : c ≤ b
      · have h' := h ha hd hc hb had hcb (by omega)
        exact ⟨h'.1, h'.2.symm⟩
      · have h' := h ha hd hb hc had (by omega) (by omega)
        omega
    · have h' := h hd ha hc hb (by omega) (by omega) (by omega)
      omega
  · intro h a b c d ha hb hc hd hab hcd heq
    by_cases hac : a < c
    · have h' := h ha hc hd hb hac (by omega) (by omega)
      omega
    · by_cases hca : c < a
      · have h' := h hc ha hb hd hca (by omega) (by omega)
        omega
      · exact ⟨by omega, by omega⟩

def increasingPairs (F : Finset ℕ) : Finset (ℕ × ℕ) :=
  (F ×ˢ F).filter (fun p => p.1 < p.2)

theorem mem_increasingPairs (F : Finset ℕ) (p : ℕ × ℕ) :
    p ∈ increasingPairs F ↔ p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 < p.2 := by
  simp [increasingPairs, and_assoc]

theorem increasingPairs_card (F : Finset ℕ) :
    (increasingPairs F).card = F.card.choose 2 := by
  exact Finset.card_product_filter_lt

theorem shared_pair_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H : ℕ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hwidth : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b - a < H) :
    ∑ i ∈ I, (F i).card.choose 2 ≤ H - 1 := by
  classical
  let U := I.biUnion (fun i => increasingPairs (F i))
  have hd : (I : Set ι).PairwiseDisjoint (fun i => increasingPairs (F i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_increasingPairs _ _).mp hp
    have hq' := (mem_increasingPairs _ _).mp hq
    exact Finset.disjoint_left.mp (hdis hi hj hij) hp'.1 hq'.1
  have hcard : U.card = ∑ i ∈ I, (F i).card.choose 2 := by
    dsimp [U]
    rw [Finset.card_biUnion hd]
    apply Finset.sum_congr rfl
    intro i hi
    exact increasingPairs_card _
  have hu : ∀ p ∈ U, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ p.2 - p.1 < H := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := Finset.mem_biUnion.mp hp
    have hh := (mem_increasingPairs _ _).mp hip
    exact ⟨hsub i hi p.1 hh.1, hsub i hi p.2 hh.2.1,
      hh.2.2, hwidth i hi p.1 hh.1 p.2 hh.2.1 hh.2.2⟩
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1 - 1) U (Finset.range (H-1)) := by
    intro p hp
    have hh := hu p hp
    apply Finset.mem_range.mpr
    change p.2 - p.1 - 1 < H - 1
    omega
  have hinj : (U : Set (ℕ × ℕ)).InjOn (fun p => p.2 - p.1 - 1) := by
    intro p hp q hq heq
    have hp' := hu p hp
    have hq' := hu q hq
    change p.2 - p.1 - 1 = q.2 - q.1 - 1 at heq
    have he := hA hp'.1 hp'.2.1 hq'.1 hq'.2.1 hp'.2.2.1 hq'.2.2.1 (by omega)
    exact Prod.ext he.1 he.2
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2-p.1-1) hmaps hinj
  rw [hcard] at hc
  simpa using hc

theorem square_choose (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n+1).choose 2 = n + n.choose 2 := by
      simpa using (Nat.choose_succ_succ n 1)
    rw [hc]
    nlinarith [ih]

theorem real_square_choose (n : ℕ) :
    (n : ℝ)^2 = 2 * (n.choose 2 : ℝ) + n := by
  exact_mod_cast (square_choose n).symm

theorem weighted_block_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H : ℕ) (w : ι → ℝ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hwidth : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b - a < H) :
    (∑ i ∈ I, ((F i).card : ℝ) * w i)^2 ≤
      (2 * ((H-1 : ℕ) : ℝ) + ∑ i ∈ I, ((F i).card : ℝ)) *
        ∑ i ∈ I, (w i)^2 := by
  have hp := shared_pair_budget I F A H hA hsub hdis hwidth
  have hpr : (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) ≤ ((H-1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have he : (∑ i ∈ I, ((F i).card : ℝ)^2) =
      2 * (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) + ∑ i ∈ I, ((F i).card : ℝ) := by
    simp_rw [real_square_choose]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have henergy : (∑ i ∈ I, ((F i).card : ℝ)^2) ≤
      2 * ((H-1 : ℕ) : ℝ) + ∑ i ∈ I, ((F i).card : ℝ) := by
    rw [he]
    linarith
  exact (Finset.sum_mul_sq_le_sq_mul_sq I (fun i => ((F i).card : ℝ)) w).trans
    (mul_le_mul_of_nonneg_right henergy (Finset.sum_nonneg (fun i hi => sq_nonneg _)))

theorem sidon_weighted_block_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H : ℕ) (w : ι → ℝ)
    (hA : IsSidon A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hwidth : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b - a < H) :
    (∑ i ∈ I, ((F i).card : ℝ) * w i)^2 ≤
      (2 * ((H-1 : ℕ) : ℝ) + ∑ i ∈ I, ((F i).card : ℝ)) *
        ∑ i ∈ I, (w i)^2 := by
  exact weighted_block_budget I F A H w
    ((sidon_iff_uniquePositiveDifferences A).mp hA) hsub hdis hwidth

end
end SidonBlockEnergy


open Finset SidonBlockEnergy

theorem proof :
  ∀ (ι : Type) [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset Nat) (A : Set Nat) (H : Nat) (w : ι → ℝ),
    IsSidon A → (∀ i ∈ I, ∀ a ∈ F i, a ∈ A) →
    (I : Set ι).PairwiseDisjoint F →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b - a < H) →
    (∑ i ∈ I, ((F i).card : ℝ) * w i) ^ 2 ≤
      (2 * ((H - 1 : Nat) : ℝ) + ∑ i ∈ I, ((F i).card : ℝ)) *
        ∑ i ∈ I, (w i) ^ 2 := by
  exact @SidonBlockEnergy.sidon_weighted_block_budget

end Submissions.J4P280SidonBlockEnergy.Proof
