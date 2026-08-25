import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Submissions.Erdos1097ThreeAPRefutation.TernaryConstruction

def CommonDifferences (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    b - a = d ∧ c - b = d}

def X_funs (M : ℕ) : Finset (Fin M → ℤ) :=
  Fintype.piFinset (fun _ => ({0, 2} : Finset ℤ))

def Y_funs (M : ℕ) : Finset (Fin M → ℤ) :=
  Fintype.piFinset (fun _ => ({1, 2} : Finset ℤ))

def D_funs (M : ℕ) : Finset (Fin M → ℤ) :=
  Fintype.piFinset (fun _ => ({-1, 0, 1} : Finset ℤ))

def eval_fun (M : ℕ) (f : Fin M → ℤ) : ℤ :=
  ∑ i : Fin M, f i * (3 : ℤ) ^ (i : ℕ)

def X_M (M : ℕ) : Finset ℤ := (X_funs M).image (eval_fun M)
def Y_M (M : ℕ) : Finset ℤ := (Y_funs M).image (eval_fun M)
def A_M (M : ℕ) : Finset ℤ := X_M M ∪ Y_M M

lemma card_A_M (M : ℕ) : (A_M M).card ≤ 2 ^ (M + 1) := by
  unfold A_M
  apply le_trans (Finset.card_union_le _ _)
  have hX : (X_M M).card ≤ 2 ^ M := by
    unfold X_M
    apply le_trans Finset.card_image_le
    unfold X_funs
    rw [Fintype.card_piFinset]
    have h : ({0, 2} : Finset ℤ).card = 2 := rfl
    simp [h]
  have hY : (Y_M M).card ≤ 2 ^ M := by
    unfold Y_M
    apply le_trans Finset.card_image_le
    unfold Y_funs
    rw [Fintype.card_piFinset]
    have h : ({1, 2} : Finset ℤ).card = 2 := rfl
    simp [h]
  have h2 : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by ring
  omega

lemma eval_fun_succ_left (M : ℕ) (f : Fin (M + 1) → ℤ) :
    eval_fun (M + 1) f = f 0 + 3 * eval_fun M (fun i => f i.succ) := by
  unfold eval_fun
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : (3 : ℤ) ^ (i.succ : ℕ) = 3 * 3 ^ (i : ℕ) := by
    rw [show (i.succ : ℕ) = (i : ℕ) + 1 by rfl, pow_add, pow_one, mul_comm]
  rw [h]
  ring

lemma eval_fun_inj_D {M : ℕ} (f g : Fin M → ℤ)
    (hf : ∀ i, f i ∈ ({-1, 0, 1} : Set ℤ))
    (hg : ∀ i, g i ∈ ({-1, 0, 1} : Set ℤ))
    (h : eval_fun M f = eval_fun M g) : f = g := by
  induction M with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ M ih =>
      have h1 := eval_fun_succ_left M f
      have h2 := eval_fun_succ_left M g
      rw [h1, h2] at h
      have hmod :
          (f 0 + 3 * eval_fun M (fun i => f i.succ)) % 3 =
            (g 0 + 3 * eval_fun M (fun i => g i.succ)) % 3 := by
        rw [h]
      have hmodf :
          (f 0 + 3 * eval_fun M (fun i => f i.succ)) % 3 = f 0 % 3 := by
        omega
      have hmodg :
          (g 0 + 3 * eval_fun M (fun i => g i.succ)) % 3 = g 0 % 3 := by
        omega
      rw [hmodf, hmodg] at hmod
      have hf0 := hf 0
      have hg0 := hg 0
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf0 hg0
      have h0 : f 0 = g 0 := by
        rcases hf0 with hf0 | hf0 | hf0 <;>
          rcases hg0 with hg0 | hg0 | hg0 <;>
          (rw [hf0, hg0] at hmod ⊢; try rfl) <;> revert hmod <;> decide
      have hrest :
          eval_fun M (fun i => f i.succ) = eval_fun M (fun i => g i.succ) := by
        omega
      have htail := ih (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hf i.succ) (fun i => hg i.succ) hrest
      ext i
      cases i using Fin.cases with
      | zero => exact h0
      | succ i => exact congr_fun htail i

lemma diffs_exist (M : ℕ) (d : Fin M → ℤ) (hd : d ∈ D_funs M) :
    ∃ a ∈ X_funs M, ∃ b ∈ Y_funs M, ∃ c ∈ X_funs M,
      b - a = d ∧ c - b = d := by
  use fun i => if d i = 1 then 0 else 2
  have ha : (fun i => if d i = 1 then (0 : ℤ) else 2) ∈ X_funs M := by
    unfold X_funs
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs <;> simp
  use ha
  use fun i => if d i = 0 then 2 else 1
  have hb : (fun i => if d i = 0 then (2 : ℤ) else 1) ∈ Y_funs M := by
    unfold Y_funs
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs <;> simp
  use hb
  use fun i => if d i = -1 then 0 else 2
  have hc : (fun i => if d i = -1 then (0 : ℤ) else 2) ∈ X_funs M := by
    unfold X_funs
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs <;> simp
  use hc
  constructor
  · ext i
    simp only [Pi.sub_apply]
    have hdi : d i ∈ ({-1, 0, 1} : Finset ℤ) := by
      exact Fintype.mem_piFinset.mp hd i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdi
    rcases hdi with hdi | hdi | hdi <;> simp [hdi]
  · ext i
    simp only [Pi.sub_apply]
    have hdi : d i ∈ ({-1, 0, 1} : Finset ℤ) := by
      exact Fintype.mem_piFinset.mp hd i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdi
    rcases hdi with hdi | hdi | hdi <;> simp [hdi]

lemma card_diffs_A_M (M : ℕ) :
    3 ^ M - 1 ≤ (CommonDifferences (A_M M)).ncard := by
  let DM := (D_funs M).image (eval_fun M)
  have hsub : (((DM \ {0} : Finset ℤ) : Set ℤ)) ⊆ CommonDifferences (A_M M) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hd
    obtain ⟨hdin, hdne⟩ := hd
    rw [Finset.mem_image] at hdin
    obtain ⟨df, hdf, rfl⟩ := hdin
    refine ⟨hdne, ?_⟩
    obtain ⟨a, ha, b, hb, c, hc, hba, hcb⟩ := diffs_exist M df hdf
    refine ⟨eval_fun M a, ?_, eval_fun M b, ?_, eval_fun M c, ?_, ?_, ?_⟩
    · unfold A_M X_M
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · unfold A_M Y_M
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    · unfold A_M X_M
      rw [Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
    · rw [← hba]
      unfold eval_fun
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext i
      simp only [Pi.sub_apply]
      ring
    · rw [← hcb]
      unfold eval_fun
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext i
      simp only [Pi.sub_apply]
      ring
  have hcardD : (D_funs M).card = 3 ^ M := by
    unfold D_funs
    rw [Fintype.card_piFinset]
    have h : ({-1, 0, 1} : Finset ℤ).card = 3 := rfl
    simp [h]
  have hinj :
      ∀ x ∈ D_funs M, ∀ y ∈ D_funs M, eval_fun M x = eval_fun M y → x = y := by
    intro x hx y hy hxy
    apply eval_fun_inj_D x y
    · intro i
      have hi := Fintype.mem_piFinset.mp hx i
      simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hi
    · intro i
      have hi := Fintype.mem_piFinset.mp hy i
      simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hi
    · exact hxy
  have hcardDM : DM.card = 3 ^ M := by
    rw [← hcardD]
    exact Finset.card_image_of_injOn hinj
  have hcarddiff : 3 ^ M - 1 ≤ (DM \ {0}).card := by
    have hsum := Finset.card_sdiff_add_card_inter DM {0}
    have hinter : (DM ∩ {0}).card ≤ 1 := by
      calc
        (DM ∩ {0}).card ≤ ({0} : Finset ℤ).card :=
          Finset.card_le_card Finset.inter_subset_right
        _ = 1 := Finset.card_singleton 0
    omega
  have hncard :
      (((DM \ {0} : Finset ℤ) : Set ℤ)).ncard = (DM \ {0}).card :=
    Set.ncard_coe_finset _
  have hfin : (CommonDifferences (A_M M)).Finite := by
    apply Set.Finite.subset
      (Finset.image (fun p : ℤ × ℤ => p.2 - p.1) (A_M M ×ˢ A_M M)).finite_toSet
    rintro d ⟨-, a, ha, b, hb, -, -, hba, -⟩
    exact Finset.mem_coe.mpr <| Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hba⟩
  have hle :
      (((DM \ {0} : Finset ℤ) : Set ℤ)).ncard ≤
        (CommonDifferences (A_M M)).ncard :=
    Set.ncard_le_ncard hsub hfin
  rw [hncard] at hle
  omega

theorem proof :
    ¬ ∃ C > (0 : ℝ), ∀ A : Finset ℤ,
      (CommonDifferences A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ) := by
  rintro ⟨C, hC, hbound⟩
  have heventual :
      ∀ᶠ M : ℕ in Filter.atTop,
        0 < ((3 ^ M - 1 : ℕ) : ℝ) -
          C * (2 ^ (M + 1) : ℝ) ^ (3 / 2 : ℝ) := by
    have hr : (2 : ℝ) ^ (3 / 2 : ℝ) / 3 < 1 := by
      rw [div_lt_iff₀ (by norm_num)]
      have h1 : (2 : ℝ) ^ (3 / 2 : ℝ) = ((2 : ℝ) ^ (3 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (3 : ℝ) * (1 / 2 : ℝ) by ring]
        rw [Real.rpow_mul (by norm_num)]
      rw [h1]
      norm_num [← Real.sqrt_eq_rpow, Real.sqrt_lt]
    have ht1 :
        Filter.Tendsto (fun M : ℕ => ((2 : ℝ) ^ (3 / 2 : ℝ) / 3) ^ M)
          Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr
    have ht2 :
        Filter.Tendsto
          (fun M : ℕ =>
            C * (2 : ℝ) ^ (3 / 2 : ℝ) *
              ((2 : ℝ) ^ (3 / 2 : ℝ) / 3) ^ M)
          Filter.atTop (nhds 0) := by
      simpa using ht1.const_mul (C * (2 : ℝ) ^ (3 / 2 : ℝ))
    have ht3 :
        Filter.Tendsto (fun M : ℕ => (1 / 3 : ℝ) ^ M)
          Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have ht4 :
        Filter.Tendsto
          (fun M : ℕ =>
            C * (2 : ℝ) ^ (3 / 2 : ℝ) *
                ((2 : ℝ) ^ (3 / 2 : ℝ) / 3) ^ M +
              (1 / 3 : ℝ) ^ M)
          Filter.atTop (nhds 0) := by
      simpa using ht2.add ht3
    have he :
        ∀ᶠ M : ℕ in Filter.atTop,
          C * (2 : ℝ) ^ (3 / 2 : ℝ) *
                ((2 : ℝ) ^ (3 / 2 : ℝ) / 3) ^ M +
              (1 / 3 : ℝ) ^ M < 1 :=
      (tendsto_order.mp ht4).2 1 (by norm_num)
    filter_upwards [he, Filter.Ici_mem_atTop 1] with M hM hM1
    rw [Set.mem_Ici] at hM1
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ M := by positivity
    have hmul := mul_lt_mul_of_pos_right hM h3pos
    have hdistrib :
        (C * (2 : ℝ) ^ (3 / 2 : ℝ) *
                ((2 : ℝ) ^ (3 / 2 : ℝ) / 3) ^ M +
              (1 / 3 : ℝ) ^ M) *
            (3 : ℝ) ^ M =
          C * (2 : ℝ) ^ (3 / 2 : ℝ) *
              ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ M +
            1 := by
      rw [add_mul]
      congr 1
      · rw [div_pow, mul_assoc, div_mul_cancel₀ _ (ne_of_gt h3pos)]
      · rw [one_div, inv_pow, inv_mul_cancel₀ (ne_of_gt h3pos)]
    rw [hdistrib] at hmul
    have h2M :
        C * (2 : ℝ) ^ (3 / 2 : ℝ) *
              ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ M =
            C * (2 ^ (M + 1) : ℝ) ^ (3 / 2 : ℝ) := by
      have hp1 :
          ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ M =
            (2 : ℝ) ^ ((3 / 2 : ℝ) * M) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [hp1]
      have hp2 :
          (2 : ℝ) ^ (3 / 2 : ℝ) *
              (2 : ℝ) ^ ((3 / 2 : ℝ) * M) =
            (2 : ℝ) ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ) * M) := by
        rw [← Real.rpow_add (by norm_num)]
      have hp3 : (2 ^ (M + 1) : ℝ) = (2 : ℝ) ^ ((M : ℝ) + 1) := by
        norm_cast
      rw [hp3, ← Real.rpow_mul (by positivity), mul_assoc]
      congr 1
      rw [hp2]
      congr 1
      ring
    rw [h2M] at hmul
    have hcast : ((3 ^ M - 1 : ℕ) : ℝ) = (3 : ℝ) ^ M - 1 := by
      have hone : 1 ≤ 3 ^ M := by
        calc
          1 = 3 ^ 0 := by rfl
          _ ≤ 3 ^ M := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.cast_sub hone]
      norm_cast
    rw [hcast]
    linarith
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp heventual
  have hMpos := hM M le_rfl
  have hA := hbound (A_M M)
  have h1 : ((3 ^ M - 1 : ℕ) : ℝ) ≤
      (CommonDifferences (A_M M)).ncard := by
    exact_mod_cast card_diffs_A_M M
  have h2 : (A_M M).card ≤ 2 ^ (M + 1) := card_A_M M
  have h3 : ((A_M M).card : ℝ) ≤ (2 ^ (M + 1) : ℝ) := by
    exact_mod_cast h2
  have h4 :
      ((A_M M).card : ℝ) ^ (3 / 2 : ℝ) ≤
        (2 ^ (M + 1) : ℝ) ^ (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h3 (by norm_num)
  have h5 :
      C * ((A_M M).card : ℝ) ^ (3 / 2 : ℝ) ≤
        C * (2 ^ (M + 1) : ℝ) ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left h4 hC.le
  linarith

end Submissions.Erdos1097ThreeAPRefutation.TernaryConstruction
