import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.J5P280ResidueCapacity.Proof

/- Finite shared short-difference packing. The analytic power-range estimate
   and the canonical asymptotic application are separate paper arguments. -/
namespace DifferenceCarrierCapacity

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

theorem shared_difference_carrier_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (D : Finset ℕ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hdiff : ∀ i ∈ I, ∀ p ∈ increasingPairs (F i), p.2 - p.1 ∈ D) :
    ∑ i ∈ I, (F i).card.choose 2 ≤ D.card := by
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
  have hu : ∀ p ∈ U, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ p.2 - p.1 ∈ D := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := Finset.mem_biUnion.mp hp
    have hh := (mem_increasingPairs _ _).mp hip
    exact ⟨hsub i hi p.1 hh.1, hsub i hi p.2 hh.2.1, hh.2.2, hdiff i hi p hip⟩
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) U D := by
    intro p hp
    exact (hu p hp).2.2.2
  have hinj : (U : Set (ℕ × ℕ)).InjOn (fun p => p.2 - p.1) := by
    intro p hp r hr heq
    have hp' := hu p hp
    have hr' := hu r hr
    have he := hA hp'.1 hp'.2.1 hr'.1 hr'.2.1 hp'.2.2.1 hr'.2.2.1 heq
    exact Prod.ext he.1 he.2
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1) hmaps hinj
  rw [hcard] at hc
  exact hc

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

theorem fiber_carrier_square_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (D : Finset ℕ)
    (hA : IsSidon A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hdiff : ∀ i ∈ I, ∀ p ∈ increasingPairs (F i), p.2 - p.1 ∈ D) :
    (∑ i ∈ I, ((F i).card : ℝ)) ^ 2 ≤
      (I.card : ℝ) * (∑ i ∈ I, ((F i).card : ℝ) + 2 * (D.card : ℝ)) := by
  have hp := shared_difference_carrier_budget I F A D
    ((sidon_iff_uniquePositiveDifferences A).mp hA) hsub hdis hdiff
  have hpr : (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) ≤ (D.card : ℝ) := by
    exact_mod_cast hp
  have he : (∑ i ∈ I, ((F i).card : ℝ)^2) =
      2 * (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) + ∑ i ∈ I, ((F i).card : ℝ) := by
    simp_rw [real_square_choose]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have henergy : (∑ i ∈ I, ((F i).card : ℝ)^2) ≤
      (∑ i ∈ I, ((F i).card : ℝ)) + 2 * (D.card : ℝ) := by
    rw [he]
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => ((F i).card : ℝ)) (fun _ => (1 : ℝ))
  have hn : (∑ i ∈ I, ((F i).card : ℝ))^2 ≤
      (∑ i ∈ I, ((F i).card : ℝ)^2) * (I.card : ℝ) := by
    simpa using hcs
  have hb := mul_le_mul_of_nonneg_right henergy (Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card)
  nlinarith [hn, hb]


theorem partition_carrier_square_budget {ι : Type*} [DecidableEq ι]
    (F : Finset ℕ) (key : ℕ → ι) (D : Finset ℕ)
    (hA : IsSidon (F : Set ℕ))
    (hdiff : ∀ a ∈ F, ∀ b ∈ F, a < b → key a = key b → b - a ∈ D) :
    (F.card : ℝ)^2 ≤ ((F.image key).card : ℝ) * ((F.card : ℝ) + 2 * (D.card : ℝ)) := by
  classical
  let I := F.image key
  let parts := fun r => F.filter (fun a => key a = r)
  have hsub : ∀ r ∈ I, ∀ a ∈ parts r, a ∈ (F : Set ℕ) := by
    intro r hr a ha
    exact (Finset.mem_filter.mp ha).1
  have hdis : (I : Set ι).PairwiseDisjoint parts := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    exact hij ((Finset.mem_filter.mp hai).2.symm.trans (Finset.mem_filter.mp haj).2)
  have hunion : I.biUnion parts = F := by
    ext a
    constructor
    · intro ha
      obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp har).1
    · intro ha
      apply Finset.mem_biUnion.mpr
      refine ⟨key a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  have hsum : ∑ r ∈ I, (parts r).card = F.card := by
    rw [← Finset.card_biUnion hdis, hunion]
  have hsumr : (∑ r ∈ I, ((parts r).card : ℝ)) = (F.card : ℝ) := by
    exact_mod_cast hsum
  have hd : ∀ r ∈ I, ∀ p ∈ increasingPairs (parts r), p.2 - p.1 ∈ D := by
    intro r hr p hp
    have h := (mem_increasingPairs _ _).mp hp
    have ha := Finset.mem_filter.mp h.1
    have hb := Finset.mem_filter.mp h.2.1
    exact hdiff p.1 ha.1 p.2 hb.1 h.2.2 (ha.2.trans hb.2.symm)
  have bound := fiber_carrier_square_budget I parts (F : Set ℕ) D hA hsub hdis hd
  rw [hsumr] at bound
  exact bound

end
end DifferenceCarrierCapacity



/- Finite shared short-difference packing. The analytic power-range estimate
   and the canonical asymptotic application are separate paper arguments. -/
namespace ModularResidueCapacity

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

theorem shared_scaled_pair_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (q m : ℕ)
    (label : ℕ × ℕ → ℕ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hscale : ∀ i ∈ I, ∀ p ∈ increasingPairs (F i), p.2 - p.1 = m * label p)
    (hrange : ∀ i ∈ I, ∀ p ∈ increasingPairs (F i), 0 < label p ∧ label p < q) :
    ∑ i ∈ I, (F i).card.choose 2 ≤ q - 1 := by
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
  have hu : ∀ p ∈ U, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧
      p.2 - p.1 = m * label p ∧ 0 < label p ∧ label p < q := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := Finset.mem_biUnion.mp hp
    have hh := (mem_increasingPairs _ _).mp hip
    exact ⟨hsub i hi p.1 hh.1, hsub i hi p.2 hh.2.1,
      hh.2.2, hscale i hi p hip, (hrange i hi p hip).1, (hrange i hi p hip).2⟩
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => label p - 1) U (Finset.range (q-1)) := by
    intro p hp
    have hh := hu p hp
    apply Finset.mem_range.mpr
    change label p - 1 < q - 1
    omega
  have hinj : (U : Set (ℕ × ℕ)).InjOn (fun p => label p - 1) := by
    intro p hp r hr heq
    have hp' := hu p hp
    have hr' := hu r hr
    change label p - 1 = label r - 1 at heq
    have hl : label p = label r := by omega
    have he : p.2 - p.1 = r.2 - r.1 := by
      rw [hp'.2.2.2.1, hr'.2.2.2.1, hl]
    have he' := hA hp'.1 hp'.2.1 hr'.1 hr'.2.1 hp'.2.2.1 hr'.2.2.1 he
    exact Prod.ext he'.1 he'.2
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => label p - 1) hmaps hinj
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

theorem fiber_square_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (q m : ℕ)
    (label : ℕ × ℕ → ℕ)
    (hA : IsSidon A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hscale : ∀ i ∈ I, ∀ p ∈ increasingPairs (F i), p.2 - p.1 = m * label p)
    (hrange : ∀ i ∈ I, ∀ p ∈ increasingPairs (F i), 0 < label p ∧ label p < q) :
    (∑ i ∈ I, ((F i).card : ℝ)) ^ 2 ≤
      (I.card : ℝ) * (∑ i ∈ I, ((F i).card : ℝ) + 2 * ((q-1 : ℕ) : ℝ)) := by
  have hp := shared_scaled_pair_budget I F A q m label
    ((sidon_iff_uniquePositiveDifferences A).mp hA) hsub hdis hscale hrange
  have hpr : (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) ≤ ((q-1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have he : (∑ i ∈ I, ((F i).card : ℝ)^2) =
      2 * (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) + ∑ i ∈ I, ((F i).card : ℝ) := by
    simp_rw [real_square_choose]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have henergy : (∑ i ∈ I, ((F i).card : ℝ)^2) ≤
      (∑ i ∈ I, ((F i).card : ℝ)) + 2 * ((q-1 : ℕ) : ℝ) := by
    rw [he]
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => ((F i).card : ℝ)) (fun _ => (1 : ℝ))
  have hn : (∑ i ∈ I, ((F i).card : ℝ))^2 ≤
      (∑ i ∈ I, ((F i).card : ℝ)^2) * (I.card : ℝ) := by
    simpa using hcs
  have hb := mul_le_mul_of_nonneg_right henergy (Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card)
  nlinarith [hn, hb]


theorem modular_square_budget (F : Finset ℕ) (N m : ℕ)
    (hA : IsSidon (F : Set ℕ)) (hN : ∀ a ∈ F, a ≤ N) :
    (F.card : ℝ)^2 ≤ ((F.image (fun a => a % m)).card : ℝ) *
      ((F.card : ℝ) + 2 * ((N / m : ℕ) : ℝ)) := by
  classical
  let I := F.image (fun a => a % m)
  let parts := fun r => F.filter (fun a => a % m = r)
  let label := fun p : ℕ × ℕ => p.2 / m - p.1 / m
  have hsub : ∀ r ∈ I, ∀ a ∈ parts r, a ∈ (F : Set ℕ) := by
    intro r hr a ha
    exact (Finset.mem_filter.mp ha).1
  have hdis : (I : Set ℕ).PairwiseDisjoint parts := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    exact hij ((Finset.mem_filter.mp hai).2.symm.trans
      (Finset.mem_filter.mp haj).2)
  have hunion : I.biUnion parts = F := by
    ext a
    constructor
    · intro ha
      obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp har).1
    · intro ha
      apply Finset.mem_biUnion.mpr
      refine ⟨a % m, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  have hsum : ∑ r ∈ I, (parts r).card = F.card := by
    rw [← Finset.card_biUnion hdis, hunion]
  have hsumr : (∑ r ∈ I, ((parts r).card : ℝ)) = (F.card : ℝ) := by
    exact_mod_cast hsum
  have hscale : ∀ r ∈ I, ∀ p ∈ increasingPairs (parts r),
      p.2 - p.1 = m * label p := by
    intro r hr p hp
    have h := (mem_increasingPairs _ _).mp hp
    have hm1 := (Finset.mem_filter.mp h.1).2
    have hm2 := (Finset.mem_filter.mp h.2.1).2
    have ha := Nat.mod_add_div p.1 m
    have hb := Nat.mod_add_div p.2 m
    have hquot : p.1 / m ≤ p.2 / m := Nat.div_le_div_right h.2.2.le
    have hdiff := Nat.sub_add_cancel hquot
    have hmul : m * (p.2 / m - p.1 / m) + m * (p.1 / m) = m * (p.2 / m) := by
      rw [← Nat.mul_add, hdiff]
    dsimp [label]
    omega
  have hrange : ∀ r ∈ I, ∀ p ∈ increasingPairs (parts r),
      0 < label p ∧ label p < N / m + 1 := by
    intro r hr p hp
    have h := (mem_increasingPairs _ _).mp hp
    have he := hscale r hr p hp
    have hbN := hN p.2 (Finset.mem_filter.mp h.2.1).1
    have hqN : p.2 / m ≤ N / m := Nat.div_le_div_right hbN
    constructor
    · by_contra hn
      have hz : label p = 0 := by omega
      rw [hz, Nat.mul_zero] at he
      omega
    · change p.2 / m - p.1 / m < N / m + 1
      exact Nat.lt_succ_of_le ((Nat.sub_le _ _).trans hqN)
  have bound := fiber_square_budget I parts (F : Set ℕ) (N / m + 1) m label
    hA hsub hdis hscale hrange
  rw [hsumr] at bound
  simpa only [Nat.add_sub_cancel] using bound

end
end ModularResidueCapacity




namespace ResiduePrefixRigidity

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


theorem quotient_pos {d q : ℕ} (hd : 0 < d) (hq : q ∣ d) : 0 < d / q := by
  have he := Nat.mul_div_cancel' hq
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, Nat.mul_zero] at he
  exact (Nat.ne_of_gt hd) he.symm

theorem divisible_pair_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H q : ℕ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hwidth : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b - a < H)
    (hdiv : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → q ∣ b - a) :
    ∑ i ∈ I, (F i).card.choose 2 ≤ (H - 1) / q := by
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
  have hu : ∀ p ∈ U, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧
      p.2 - p.1 < H ∧ q ∣ p.2 - p.1 := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := Finset.mem_biUnion.mp hp
    have hh := (mem_increasingPairs _ _).mp hip
    exact ⟨hsub i hi p.1 hh.1, hsub i hi p.2 hh.2.1, hh.2.2,
      hwidth i hi p.1 hh.1 p.2 hh.2.1 hh.2.2,
      hdiv i hi p.1 hh.1 p.2 hh.2.1 hh.2.2⟩
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => (p.2 - p.1) / q - 1)
      U (Finset.range ((H-1)/q)) := by
    intro p hp
    have hh := hu p hp
    have hpq := quotient_pos (show 0 < p.2-p.1 by omega) hh.2.2.2.2
    have hle : (p.2-p.1)/q ≤ (H-1)/q := Nat.div_le_div_right (by omega)
    apply Finset.mem_range.mpr
    change (p.2-p.1)/q-1 < (H-1)/q
    omega
  have hinj : (U : Set (ℕ × ℕ)).InjOn (fun p => (p.2-p.1)/q-1) := by
    intro p hp r hr heq
    have hp' := hu p hp
    have hr' := hu r hr
    have hpq := quotient_pos (show 0 < p.2-p.1 by omega) hp'.2.2.2.2
    have hrq := quotient_pos (show 0 < r.2-r.1 by omega) hr'.2.2.2.2
    change (p.2-p.1)/q-1 = (r.2-r.1)/q-1 at heq
    have hquot : (p.2-p.1)/q = (r.2-r.1)/q := by omega
    have he : p.2-p.1 = r.2-r.1 := by
      calc
        p.2-p.1 = q*((p.2-p.1)/q) := (Nat.mul_div_cancel' hp'.2.2.2.2).symm
        _ = q*((r.2-r.1)/q) := by rw [hquot]
        _ = r.2-r.1 := Nat.mul_div_cancel' hr'.2.2.2.2
    have h := hA hp'.1 hp'.2.1 hr'.1 hr'.2.1 hp'.2.2.1 hr'.2.2.1 he
    exact Prod.ext h.1 h.2
  have hc := Finset.card_le_card_of_injOn
    (fun p : ℕ × ℕ => (p.2-p.1)/q-1) hmaps hinj
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


theorem divisible_square_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H q : ℕ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hwidth : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b-a < H)
    (hdiv : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → q ∣ b-a) :
    (∑ i ∈ I, ((F i).card : ℝ)^2) ≤
      2 * (((H-1)/q : ℕ) : ℝ) + ∑ i ∈ I, ((F i).card : ℝ) := by
  have hp := divisible_pair_budget I F A H q hA hsub hdis hwidth hdiv
  have hpr : (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) ≤ (((H-1)/q : ℕ) : ℝ) := by
    exact_mod_cast hp
  have he : (∑ i ∈ I, ((F i).card : ℝ)^2) =
      2 * (∑ i ∈ I, ((F i).card.choose 2 : ℝ)) + ∑ i ∈ I, ((F i).card : ℝ) := by
    simp_rw [real_square_choose]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [he]
  linarith


theorem support_mass_bound (m k D : ℝ) (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hlarge : 2*k ≤ m) (henergy : m^2 ≤ k*(2*D+m)) :
    m^2 ≤ 4*k*D := by
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hlarge)]

theorem overlap_count_budget (P Q R S : Finset ℕ) (hPQ : P ⊆ Q) :
    P.card ≤ (P \ R).card + (Q \ S).card + ((P ∩ R) ∩ S).card := by
  have h1 := Finset.card_sdiff_add_card_inter P R
  have h2 := Finset.card_sdiff_add_card_inter (P ∩ R) S
  have hsub : (P ∩ R) \ S ⊆ Q \ S := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha ⊢
    exact ⟨hPQ ha.1.1, ha.2⟩
  have hc := Finset.card_le_card hsub
  omega

theorem joint_divisible_pair_budget {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H q r : ℕ)
    (hA : UniquePositiveDifferences A)
    (hsub : ∀ i ∈ I, ∀ a ∈ F i, a ∈ A)
    (hdis : (I : Set ι).PairwiseDisjoint F)
    (hwidth : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b-a < H)
    (hq : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → q ∣ b-a)
    (hr : ∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → r ∣ b-a) :
    ∑ i ∈ I, (F i).card.choose 2 ≤ (H-1)/(Nat.lcm q r) := by
  apply divisible_pair_budget I F A H (Nat.lcm q r) hA hsub hdis hwidth
  intro i hi a ha b hb hab
  exact Nat.lcm_dvd (hq i hi a ha b hb hab) (hr i hi a ha b hb hab)

theorem large_prime_power_step {d u v p T k : ℕ} (hp : Nat.Prime p)
    (hpT : T < p) (hu : 0 < u) (hv : 0 < v) (huT : u ≤ T) (hvT : v ≤ T) :
    p^k ∣ d*u ↔ p^k ∣ d*v := by
  have cu : Nat.Coprime (p^k) u :=
    (Nat.coprime_of_lt_prime (by omega) (by omega) hp).pow_left k
  have cv : Nat.Coprime (p^k) v :=
    (Nat.coprime_of_lt_prime (by omega) (by omega) hp).pow_left k
  exact cu.dvd_mul_right.trans cv.dvd_mul_right.symm

theorem prime_power_chain (q : ℕ → ℕ) (T p k : ℕ) (hp : Nat.Prime p)
    (hpT : T < p)
    (hstep : ∀ i, ∃ d u v : ℕ, 0 < u ∧ 0 < v ∧ u ≤ T ∧ v ≤ T ∧
      q i = d*u ∧ q (i+1) = d*v) :
    ∀ n, p^k ∣ q n ↔ p^k ∣ q 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨d,u,v,hu,hv,huT,hvT,hq,hr⟩ := hstep n
    have h := large_prime_power_step hp hpT hu hv huT hvT (d := d) (k := k)
    rw [← hq, ← hr] at h
    exact h.symm.trans ih

end
end ResiduePrefixRigidity

open Finset

theorem solves :
  (∀ {ι : Type*} [DecidableEq ι]
    (F : Finset ℕ) (key : ℕ → ι) (D : Finset ℕ),
    DifferenceCarrierCapacity.IsSidon (F : Set ℕ) →
    (∀ a ∈ F, ∀ b ∈ F, a < b → key a = key b → b - a ∈ D) →
    (F.card : ℝ)^2 ≤ ((F.image key).card : ℝ) * ((F.card : ℝ) + 2 * (D.card : ℝ))) ∧
  (∀ (F : Finset ℕ) (N m : ℕ),
    DifferenceCarrierCapacity.IsSidon (F : Set ℕ) → (∀ a ∈ F, a ≤ N) →
    (F.card : ℝ)^2 ≤ ((F.image (fun a => a % m)).card : ℝ) *
      ((F.card : ℝ) + 2 * ((N / m : ℕ) : ℝ))) ∧
  (∀ {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset ℕ) (A : Set ℕ) (H q r : ℕ),
    ResiduePrefixRigidity.UniquePositiveDifferences A →
    (∀ i ∈ I, ∀ a ∈ F i, a ∈ A) →
    (I : Set ι).PairwiseDisjoint F →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → b-a < H) →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → q ∣ b-a) →
    (∀ i ∈ I, ∀ a ∈ F i, ∀ b ∈ F i, a < b → r ∣ b-a) →
    ∑ i ∈ I, (F i).card.choose 2 ≤ (H-1)/(Nat.lcm q r)) :=
  ⟨@DifferenceCarrierCapacity.partition_carrier_square_budget,
    @ModularResidueCapacity.modular_square_budget,
    @ResiduePrefixRigidity.joint_divisible_pair_budget⟩

end Submissions.J5P280ResidueCapacity.Proof
