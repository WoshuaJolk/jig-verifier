import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- The canonical threshold and obstruction definitions are reproduced verbatim.
The star count is the standard lower construction; no novelty is claimed. -/
namespace Submissions.Erdos643ThresholdLowerBound.Main

def Uniform {V : Type} [DecidableEq V]
    (t : ℕ) (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, A.card = t

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

def IsThreshold (n t m : ℕ) : Prop :=
  (∀ F : Finset (Finset (Fin n)),
      Uniform t F → m ≤ F.card → HasDisjointEqualUnion F) ∧
  ∀ q : ℕ, q < m →
    ∃ F : Finset (Finset (Fin n)),
      Uniform t F ∧ q ≤ F.card ∧ ¬HasDisjointEqualUnion F

theorem uniform_card_le {n t : ℕ} {F : Finset (Finset (Fin n))}
    (hF : Uniform t F) : F.card ≤ Nat.choose n t := by
  calc
    F.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard t).card :=
      Finset.card_le_card (by
        intro A hA
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hF A hA⟩)
    _ = Nat.choose n t := by simp

theorem threshold_exists_unique (n t : ℕ) : ∃! m, IsThreshold n t m := by
  classical
  let P : ℕ → Prop := fun m => ∀ F : Finset (Finset (Fin n)),
    Uniform t F → m ≤ F.card → HasDisjointEqualUnion F
  have hex : ∃ m, P m := by
    refine ⟨Nat.choose n t + 1, ?_⟩
    intro F hF hcard
    have := uniform_card_le hF
    omega
  have hs : IsThreshold n t (Nat.find hex) := by
    refine ⟨Nat.find_spec hex, ?_⟩
    intro q hq
    have hn : ¬ P q := Nat.find_min hex hq
    dsimp [P] at hn
    push Not at hn
    exact hn
  refine ⟨Nat.find hex, hs, ?_⟩
  intro m hm
  apply Nat.le_antisymm
  · by_contra hn
    obtain ⟨F, hF, hcard, hfree⟩ := hm.2 (Nat.find hex) (by omega)
    exact hfree (hs.1 F hF hcard)
  · by_contra hn
    obtain ⟨F, hF, hcard, hfree⟩ := hs.2 m (by omega)
    exact hfree (hm.1 F hF hcard)

theorem threshold_ge_star {n t m : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hm : IsThreshold n t m) : Nat.choose (n - 1) (t - 1) + 1 ≤ m := by
  let v : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩
  let F : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard t).filter ({v} ⊆ ·)
  have hcard : F.card = Nat.choose (n - 1) (t - 1) := by
    simpa [F] using Finset.card_filter_powersetCard_subset
      ({v} : Finset (Fin n)) Finset.univ t (by simp) (by simpa using ht)
  have huniform : Uniform t F := by
    intro A hA
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
  have hcommon : ∀ A ∈ F, v ∈ A := by
    intro A hA
    exact Finset.singleton_subset_iff.mp (Finset.mem_filter.mp hA).2
  have hfree : ¬HasDisjointEqualUnion F := by
    rintro ⟨A, hA, B, hB, C, hC, D, hD,
      hAB, hAC, hAD, hBC, hBD, hCD, hunion, hdAB, hdCD⟩
    exact (Finset.disjoint_left.mp hdAB) (hcommon A hA) (hcommon B hB)
  have hlt : F.card < m :=
    lt_of_not_ge (fun h => hfree (hm.1 F huniform h))
  simpa [hcard] using Nat.succ_le_of_lt hlt

theorem choose_pred_ratio {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (Nat.choose (n - 1) k : ℝ) / (Nat.choose n k : ℝ) =
      1 - (k : ℝ) / (n : ℝ) := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hc0 : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hk))
  have hnat := Nat.choose_mul_succ_eq (n - 1) k
  rw [Nat.sub_add_cancel hn] at hnat
  have hreal : (Nat.choose (n - 1) k : ℝ) * (n : ℝ) =
      (Nat.choose n k : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hk] at hreal
  field_simp [hc0, hn0]
  nlinarith [hreal]

theorem star_ratio_tendsto_one (k : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => (Nat.choose (n - 1) k : ℝ) / (Nat.choose n k : ℝ))
      Filter.atTop (nhds 1) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - (k : ℝ) / (n : ℝ))
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (max 1 k)] with n hn
  exact (choose_pred_ratio ((le_max_left 1 k).trans hn)
    ((le_max_right 1 k).trans hn)).symm

theorem threshold_eventual_lower {t : ℕ} (ht : 1 ≤ t) (f : ℕ → ℕ)
    (hf : ∀ n, IsThreshold n t (f n)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      1 - ε ≤ (f n : ℝ) / (Nat.choose n (t - 1) : ℝ) := by
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, ((t - 1 : ℕ) : ℝ) / (n : ℝ) < ε :=
    (tendsto_const_div_atTop_nhds_zero_nat ((t - 1 : ℕ) : ℝ)).eventually_lt_const hε
  filter_upwards [Filter.eventually_ge_atTop (max 1 (t - 1)), hsmall] with n hn hsmall
  have hn1 : 1 ≤ n := (le_max_left 1 (t - 1)).trans hn
  have hkn : t - 1 ≤ n := (le_max_right 1 (t - 1)).trans hn
  have hstar := threshold_ge_star hn1 ht (hf n)
  have hstar' : (Nat.choose (n - 1) (t - 1) : ℝ) ≤ (f n : ℝ) := by
    exact_mod_cast (Nat.le_succ _).trans hstar
  have hratio := div_le_div_of_nonneg_right hstar'
    (Nat.cast_nonneg (Nat.choose n (t - 1)) : (0 : ℝ) ≤ _)
  rw [choose_pred_ratio hn1 hkn] at hratio
  linarith

abbrev statement : Prop :=
  (∀ n t : ℕ, ∃! m, IsThreshold n t m) ∧
  (∀ n t m : ℕ, 1 ≤ n → 1 ≤ t → IsThreshold n t m →
    Nat.choose (n - 1) (t - 1) + 1 ≤ m) ∧
  (∀ t : ℕ, 1 ≤ t → ∀ f : ℕ → ℕ, (∀ n, IsThreshold n t (f n)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
      1 - ε ≤ (f n : ℝ) / (Nat.choose n (t - 1) : ℝ))

theorem proof : statement := by
  refine ⟨threshold_exists_unique, ?_, ?_⟩
  · intro n t m hn ht hm
    exact threshold_ge_star hn ht hm
  · intro t ht f hf ε hε
    exact threshold_eventual_lower ht f hf ε hε

end Submissions.Erdos643ThresholdLowerBound.Main
