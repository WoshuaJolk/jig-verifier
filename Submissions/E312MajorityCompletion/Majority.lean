import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
Fixed-majority completion comparison for prescribed reciprocal inventories.
This proves a comparison with the full inventory, not an exponential bound
for that inventory and not a solution of Erdős 312.
Source argument: prime_multiplicity_core.md, fixed-majority extension.
-/
namespace Submissions.E312MajorityCompletion.Majority

open scoped BigOperators

noncomputable def value {ι : Type*} [Fintype ι] (n a : ι → ℕ) : ℝ :=
  ∑ i, (a i : ℝ) / n i

def Fits {ι : Type*} (m a : ι → ℕ) : Prop := ∀ i, a i ≤ m i

def Full {ι : Type*} (n a : ι → ℕ) : Prop := ∀ i, a i < n i

def doubled {ι : Type*} (n a : ι → ℕ) : ι → ℕ :=
  fun i => (2 * a i) % n i

theorem value_nonneg {ι : Type*} [Fintype ι] (n a : ι → ℕ) :
    0 ≤ value n a := by
  exact Finset.sum_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem coordinate_le_value {ι : Type*} [Fintype ι] (n a : ι → ℕ) (i : ι) :
    (a i : ℝ) / n i ≤ value n a := by
  unfold value
  exact Finset.single_le_sum (fun j _ => div_nonneg (show (0 : ℝ) ≤ a j from Nat.cast_nonneg _) (Nat.cast_nonneg (n j)))
    (Finset.mem_univ i)

theorem doubled_full {ι : Type*} {n a : ι → ℕ} (hn : ∀ i, 0 < n i) :
    Full n (doubled n a) := by
  intro i
  exact Nat.mod_lt _ (hn i)

theorem doubled_nonzero {n a : ℕ} (hn : Odd n) (ha : 0 < a) (han : a < n) :
    0 < (2 * a) % n := by
  have hcop : Nat.Coprime n 2 := hn.coprime_two_left.symm
  have hnot : ¬ n ∣ 2 * a := by
    intro h
    have hna : n ∣ a := hcop.dvd_of_dvd_mul_left h
    exact (Nat.not_dvd_of_pos_of_lt ha han) hna
  exact Nat.pos_of_ne_zero (fun h => hnot (Nat.dvd_of_mod_eq_zero h))

theorem unique_large {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ι → ℕ} (hs : value n a < 1) {i j : ι}
    (hi : (1 : ℝ) / 2 < (a i : ℝ) / n i)
    (hj : (1 : ℝ) / 2 < (a j : ℝ) / n j) : i = j := by
  by_contra hne
  have hpair : (a i : ℝ) / n i + (a j : ℝ) / n j ≤ value n a := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i,j} : Finset ι) ⊆ Finset.univ from Finset.subset_univ _)
      (fun x _ _ => div_nonneg (show (0 : ℝ) ≤ a x from Nat.cast_nonneg _) (Nat.cast_nonneg (n x)))
    simpa [value, hne] using h
  linarith

theorem doubled_at_pivot {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ι → ℕ} (hn : ∀ i, 0 < n i) (ha : Full n a)
    (hs : value n a < 1) {p : ι}
    (hp : (1 : ℝ) / 2 < (a p : ℝ) / n p) :
    doubled n a p = 2 * a p - n p ∧
      (∀ i, i ≠ p → doubled n a i = 2 * a i) ∧
      value n (doubled n a) = 2 * value n a - 1 := by
  have hpR : (0 : ℝ) < n p := by exact_mod_cast hn p
  have hpa : n p < 2 * a p := by
    have h := (lt_div_iff₀ hpR).mp hp
    exact_mod_cast (show (n p : ℝ) < 2 * (a p : ℝ) by linarith)
  have hmodp : doubled n a p = 2 * a p - n p := by
    dsimp [doubled]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := ha p; omega)]
  have hother : ∀ i, i ≠ p → doubled n a i = 2 * a i := by
    intro i hip
    have hiR : (0 : ℝ) < n i := by exact_mod_cast hn i
    have hi : (a i : ℝ) / n i < 1 / 2 := by
      have hpair : (a i : ℝ) / n i + (a p : ℝ) / n p ≤ value n a := by
        have h := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({i,p} : Finset ι) ⊆ Finset.univ from Finset.subset_univ _)
          (fun x _ _ => div_nonneg (show (0 : ℝ) ≤ a x from Nat.cast_nonneg _) (Nat.cast_nonneg (n x)))
        simpa [value, hip] using h
      linarith
    have hnat : 2 * a i < n i := by
      have h := (div_lt_iff₀ hiR).mp hi
      exact_mod_cast (show 2 * (a i : ℝ) < n i by linarith)
    exact Nat.mod_eq_of_lt hnat
  refine ⟨hmodp, hother, ?_⟩
  have hpoint : ∀ i, (doubled n a i : ℝ) / n i =
      2 * ((a i : ℝ) / n i) - if i = p then 1 else 0 := by
    intro i
    by_cases hip : i = p
    · subst i
      rw [hmodp, Nat.cast_sub (by omega), if_pos rfl]
      push_cast
      field_simp
    · rw [hother i hip, if_neg hip]
      push_cast
      ring
  simp_rw [value, hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem growth_without_wrap (x : ℕ → ℝ) (u t : ℕ)
    (h : ∀ j < t, x (u + j + 1) = 2 * x (u + j)) :
    x (u + t) = (2 : ℝ)^t * x u := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show u + (t + 1) = u + t + 1 by omega, h t (by omega)]
    rw [ih (fun j hj => h j (by omega)), pow_succ]
    ring

/-- At most L coordinates can stay active throughout a long sequence of
single-coordinate wraps with a fixed positive post-wrap lower bound. -/
theorem last_wrap_cardinality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : ℕ → ι → ℝ) (w : ℕ → ι)
    (T L : ℕ) (D ε : ℝ) (hD : 0 < D) (hε : 0 < ε)
    (hT : D ≤ (2 : ℝ)^T) (hL : 1 ≤ ε * (2 : ℝ)^L)
    (hinitial : ∀ i ∈ S, 1 / D ≤ x 0 i)
    (hupper : ∀ i ∈ S, x T i < 1)
    (hwrap : ∀ j < T, ε < x (j + 1) (w j))
    (hdouble : ∀ j < T, ∀ i, i ≠ w j → x (j + 1) i = 2 * x j i) :
    S.card ≤ L := by
  have hcovered : S ⊆ (Finset.Ico (T - L) T).image w := by
    intro i hi
    let W := (Finset.range T).filter (fun j => w j = i)
    have hW : W.Nonempty := by
      by_contra hn
      have hnever : ∀ j < T, i ≠ w j := by
        intro j hj hij
        exact hn ⟨j, by simp [W, hj, hij]⟩
      have hg := growth_without_wrap (fun j => x j i) 0 T
        (fun j hj => by simpa using hdouble j hj i (hnever j hj))
      have hprod := mul_le_mul_of_nonneg_left (hinitial i hi)
        (show 0 ≤ (2 : ℝ)^T by positivity)
      have hdiv : 1 ≤ (2 : ℝ)^T * (1 / D) := by
        rw [mul_one_div, le_div_iff₀ hD]
        simpa using hT
      simp only [zero_add] at hg
      linarith [hupper i hi]
    let j := W.max' hW
    have hjW : j ∈ W := Finset.max'_mem W hW
    have hj : j < T ∧ w j = i := by simpa [W] using hjW
    have hafter : ∀ v, j < v → v < T → i ≠ w v := by
      intro v hjv hv hiv
      have hvW : v ∈ W := by simp [W, hv, hiv]
      have hvj := Finset.le_max' W v hvW
      change v ≤ j at hvj
      omega
    have hrecent : T - L ≤ j := by
      by_contra hbad
      have hlength : L ≤ T - (j + 1) := by omega
      have hg := growth_without_wrap (fun v => x v i) (j + 1) (T - (j + 1))
        (fun v hv => hdouble (j + 1 + v) (by omega) i
          (hafter (j + 1 + v) (by omega) (by omega)))
      have hindex : j + 1 + (T - (j + 1)) = T := by omega
      rw [hindex] at hg
      have hstart : ε < x (j + 1) i := by simpa [hj.2] using hwrap j hj.1
      have hpow : (2 : ℝ)^L ≤ (2 : ℝ)^(T - (j + 1)) :=
        pow_le_pow_right₀ (by norm_num) hlength
      have hbase : 1 ≤ (2 : ℝ)^(T - (j + 1)) * ε := by
        nlinarith [mul_le_mul_of_nonneg_left hpow hε.le]
      have hstrict := mul_lt_mul_of_pos_left hstart
        (show 0 < (2 : ℝ)^(T - (j + 1)) by positivity)
      linarith [hupper i hi]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨hrecent, hj.1⟩, hj.2⟩
  calc S.card ≤ ((Finset.Ico (T - L) T).image w).card := Finset.card_le_card hcovered
    _ ≤ (Finset.Ico (T - L) T).card := Finset.card_image_le
    _ ≤ L := by simp only [Nat.card_Ico]; omega

def orbit {ι : Type*} (n a : ι → ℕ) : ℕ → (ι → ℕ)
  | 0 => a
  | j + 1 => doubled n (orbit n a j)

theorem orbit_full {ι : Type*} {n a : ι → ℕ}
    (hn : ∀ i, 0 < n i) (ha : Full n a) (j : ℕ) : Full n (orbit n a j) := by
  cases j with
  | zero => exact ha
  | succ j => exact doubled_full hn

theorem violation_large {ι : Type*} {n m a : ι → ℕ} {ρ : ℝ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, ρ * n i ≤ m i)
    {i : ι} (hi : m i < a i) : ρ < (a i : ℝ) / n i := by
  apply (lt_div_iff₀ (by exact_mod_cast hn i)).mpr
  exact lt_of_le_of_lt (hm i) (by exact_mod_cast hi)

/-- Assuming every preceding stage violates a cap, doubling gives the exact
advertised deficit, with no rounding error. -/
theorem orbit_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n m a : ι → ℕ} {ρ δ : ℝ} {T : ℕ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, ρ * n i ≤ m i)
    (hρ : 1 / 2 < ρ) (ha : Full n a)
    (hδ : 0 < δ) (hs : value n a = 1 - δ)
    (hbad : ∀ j < T, ¬ Fits m (orbit n a j)) :
    ∀ j ≤ T, value n (orbit n a j) = 1 - (2 : ℝ)^j * δ := by
  intro j hj
  induction j with
  | zero => simpa [orbit] using hs
  | succ j ih =>
    have heq := ih (by omega)
    have hbelow : value n (orbit n a j) < 1 := by
      rw [heq]
      have : 0 < (2 : ℝ)^j * δ := by positivity
      linarith
    obtain ⟨p, hp⟩ : ∃ p, m p < orbit n a j p := by
      have h := hbad j (by omega)
      simpa only [Fits, not_forall, not_le] using h
    have hlarge := violation_large hn hm hp
    have hstep := (doubled_at_pivot hn (orbit_full hn ha j) hbelow
      (lt_trans hρ hlarge)).2.2
    change value n (doubled n (orbit n a j)) = _
    rw [hstep, heq, pow_succ]
    ring

/-- The large-support branch of the majority repair theorem. The bound T is
chosen so that all powers before T are less than D, while 2^T reaches D. -/
theorem repair_large_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n m a : ι → ℕ} {ρ δ D : ℝ} {T L : ℕ}
    (hn : ∀ i, 0 < n i) (hnD : ∀ i, (n i : ℝ) ≤ D)
    (hm : ∀ i, ρ * n i ≤ m i) (hρ : 1 / 2 < ρ)
    (ha : Full n a) (hδ : 0 < δ) (hs : value n a = 1 - δ)
    (hT : D ≤ (2 : ℝ)^T)
    (hbefore : ∀ j < T, (2 : ℝ)^j < D)
    (hL : 1 ≤ (2 * ρ - 1) * (2 : ℝ)^L)
    (hsupport : L < (Finset.univ.filter (fun i => 0 < a i)).card) :
    ∃ b, Fits m b ∧ value n b < 1 ∧ 1 - value n b < D * δ := by
  classical
  let S := Finset.univ.filter (fun i => 0 < a i)
  have hSne : S.Nonempty := Finset.card_pos.mp (by
    change 0 < (Finset.univ.filter (fun i => 0 < a i)).card
    omega)
  obtain ⟨i₀, hi₀⟩ := hSne
  have hD : 0 < D := lt_of_lt_of_le (by exact_mod_cast hn i₀) (hnD i₀)
  have hex : ∃ j < T, Fits m (orbit n a j) := by
    by_contra hnone
    have hbad : ∀ j < T, ¬ Fits m (orbit n a j) := by
      simpa only [not_exists, not_and] using hnone
    have heq := orbit_value hn hm hρ ha hδ hs hbad
    have hbelow : ∀ j ≤ T, value n (orbit n a j) < 1 := by
      intro j hj
      rw [heq j hj]
      have : 0 < (2 : ℝ)^j * δ := by positivity
      linarith
    have hpivot : ∀ j < T, ∃ p, m p < orbit n a j p := by
      intro j hj
      simpa only [Fits, not_forall, not_le] using hbad j hj
    let w : ℕ → ι := fun j => if h : j < T then Classical.choose (hpivot j h) else i₀
    have hw : ∀ j < T, m (w j) < orbit n a j (w j) := by
      intro j hj
      simpa only [w, dif_pos hj] using Classical.choose_spec (hpivot j hj)
    have hbound := last_wrap_cardinality S
      (fun j i => (orbit n a j i : ℝ) / n i) w T L D (2 * ρ - 1)
      hD (by linarith) hT hL
      (by
        intro i hi
        have hai : 0 < a i := (Finset.mem_filter.mp hi).2
        have hni : (0 : ℝ) < n i := by exact_mod_cast hn i
        change 1 / D ≤ (a i : ℝ) / n i
        apply (div_le_div_iff₀ hD hni).mpr
        have haone : (1 : ℝ) ≤ a i := by exact_mod_cast hai
        nlinarith [hnD i])
      (by
        intro i _
        exact lt_of_le_of_lt (coordinate_le_value n (orbit n a T) i) (hbelow T le_rfl))
      (by
        intro j hj
        have hlarge := violation_large hn hm (hw j hj)
        have hp := (doubled_at_pivot hn (orbit_full hn ha j) (hbelow j (by omega))
          (lt_trans hρ hlarge)).1
        have hnle : n (w j) ≤ 2 * orbit n a j (w j) := by
          have hnpos : (0 : ℝ) < n (w j) := by exact_mod_cast hn (w j)
          have hc := (lt_div_iff₀ hnpos).mp (lt_trans hρ hlarge)
          exact_mod_cast (show (n (w j) : ℝ) ≤ 2 * (orbit n a j (w j) : ℝ) by linarith)
        change 2 * ρ - 1 < (doubled n (orbit n a j) (w j) : ℝ) / n (w j)
        rw [hp, Nat.cast_sub hnle]
        push_cast
        have hnpos : (0 : ℝ) < n (w j) := by exact_mod_cast hn (w j)
        apply (lt_div_iff₀ hnpos).mpr
        have hc := (lt_div_iff₀ hnpos).mp hlarge
        nlinarith)
      (by
        intro j hj i hip
        have hlarge := violation_large hn hm (hw j hj)
        have hp := (doubled_at_pivot hn (orbit_full hn ha j) (hbelow j (by omega))
          (lt_trans hρ hlarge)).2.1 i hip
        change (doubled n (orbit n a j) i : ℝ) / n i = _
        rw [hp]
        push_cast
        ring)
    change S.card ≤ L at hbound
    change L < S.card at hsupport
    omega
  let j₀ := Nat.find hex
  have hj₀ : j₀ < T ∧ Fits m (orbit n a j₀) := Nat.find_spec hex
  have hbad : ∀ v < j₀, ¬ Fits m (orbit n a v) := by
    intro v hv hfitv
    have hmin := Nat.find_min hex hv
    exact hmin ⟨by omega, hfitv⟩
  have heq := orbit_value hn hm hρ ha hδ hs hbad j₀ le_rfl
  refine ⟨orbit n a j₀, hj₀.2, ?_, ?_⟩
  · rw [heq]
    have : 0 < (2 : ℝ)^j₀ * δ := by positivity
    linarith
  · rw [heq]
    have := mul_lt_mul_of_pos_right (hbefore j₀ hj₀.1) hδ
    linarith

/-- A positive deficit lies on the grid of the product of active denominators. -/
theorem support_grid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ι → ℕ} (hn : ∀ i, 0 < n i) {δ : ℝ}
    (hδ : 0 < δ) (hs : value n a = 1 - δ) :
    1 ≤ (∏ i ∈ Finset.univ.filter (fun i => 0 < a i), (n i : ℝ)) * δ := by
  classical
  let S := Finset.univ.filter (fun i => 0 < a i)
  let Q : ℕ := ∏ i ∈ S, n i
  let C : ℕ := ∑ i ∈ S, a i * (Q / n i)
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => hn i)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hdiv : ∀ i ∈ S, n i ∣ Q := fun i hi => Finset.dvd_prod_of_mem n hi
  have hsum : value n a = ∑ i ∈ S, (a i : ℝ) / n i := by
    unfold value
    apply Eq.symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    have hai : a i = 0 := by
      have : ¬ 0 < a i := by simpa [S] using hi
      omega
    simp [hai]
  have hnum : (Q : ℝ) * value n a = C := by
    rw [hsum, Finset.mul_sum]
    simp only [C, Nat.cast_sum, Nat.cast_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hid : (n i : ℝ) * (Q / n i : ℕ) = Q := by
      exact_mod_cast Nat.mul_div_cancel' (hdiv i hi)
    have hni : (n i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hn i))
    field_simp
    nlinarith
  have hCQ : C < Q := by
    have : (C : ℝ) < Q := by rw [← hnum, hs]; nlinarith
    exact_mod_cast this
  have hgap : (C : ℝ) + 1 ≤ Q := by exact_mod_cast hCQ
  have hcast : (Q : ℝ) = ∏ i ∈ S, (n i : ℝ) := by simp [Q]
  change 1 ≤ (∏ i ∈ S, (n i : ℝ)) * δ
  rw [← hcast]
  rw [hs] at hnum
  nlinarith

theorem sparse_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ι → ℕ} {D δ : ℝ} {L : ℕ}
    (hn : ∀ i, 0 < n i) (hnD : ∀ i, (n i : ℝ) ≤ D)
    (hD : 1 ≤ D) (hδ : 0 < δ) (hs : value n a = 1 - δ)
    (hcard : (Finset.univ.filter (fun i => 0 < a i)).card ≤ L) :
    1 ≤ D^L * δ := by
  have hg := support_grid hn hδ hs
  have hp : (∏ i ∈ Finset.univ.filter (fun i => 0 < a i), (n i : ℝ)) ≤ D^L := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.filter (fun i => 0 < a i), D :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hnD i)
      _ = D ^ (Finset.univ.filter (fun i => 0 < a i)).card := by simp
      _ ≤ D^L := pow_le_pow_right₀ hD hcard
  exact le_trans hg (mul_le_mul_of_nonneg_right hp hδ.le)

/-- Two available majority columns fill one with error less than the finer step. -/
theorem two_column_fill {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n m : ι → ℕ} {ρ : ℝ} {i j : ι}
    (hij : i ≠ j) (hni : 2 ≤ n i) (hnj : 0 < n j)
    (hm : ∀ k, ρ * n k ≤ m k) (hρ : 1 / 2 < ρ) :
    ∃ b, Fits m b ∧ value n b ≤ 1 ∧ 1 - value n b < 1 / n j := by
  classical
  let c := (n i + 1) / 2
  have hc : n i ≤ 2*c ∧ 2*c ≤ n i + 1 := by dsimp [c]; omega
  have hclt : c < n i := by omega
  have hcfit : c ≤ m i := by
    have hpos : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
    have hmi : (n i : ℝ) < 2 * m i := by nlinarith [hm i]
    have : n i < 2 * m i := by exact_mod_cast hmi
    omega
  have hnip : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by omega)
  have hnjp : (0 : ℝ) < n j := by exact_mod_cast hnj
  let r : ℝ := 1 - (c : ℝ) / n i
  have hr : 0 < r ∧ r ≤ 1/2 := by
    dsimp [r]
    have hh : (c : ℝ) / n i < 1 := (div_lt_one hnip).mpr (by exact_mod_cast hclt)
    have hl : (1 : ℝ)/2 ≤ (c : ℝ)/n i := by
      apply (le_div_iff₀ hnip).mpr
      have : (n i : ℝ) ≤ 2*c := by exact_mod_cast hc.1
      linarith
    constructor <;> linarith
  let d := ⌊(n j : ℝ)*r⌋₊
  have hd : (d : ℝ) ≤ (n j : ℝ)*r := Nat.floor_le (mul_nonneg hnjp.le hr.1.le)
  have hdr : (n j : ℝ)*r < (d : ℝ)+1 := Nat.lt_floor_add_one _
  have hdfit : d ≤ m j := by
    have : (d : ℝ) ≤ m j := by nlinarith [hm j]
    exact_mod_cast this
  let b : ι → ℕ := fun k => if k = i then c else if k = j then d else 0
  have hb : value n b = (c : ℝ)/n i + (d : ℝ)/n j := by
    unfold value
    have he : (fun k => (b k : ℝ)/n k) =
        (fun k => (if k = i then (c : ℝ)/n i else 0) +
          (if k = j then (d : ℝ)/n j else 0)) := by
      funext k
      by_cases hki : k = i
      · subst k; simp [b, hij]
      · by_cases hkj : k = j
        · subst k; simp [b, hki]
        · simp [b, hki, hkj]
    rw [he, Finset.sum_add_distrib]
    simp
  refine ⟨b, ?_, ?_, ?_⟩
  · intro k
    dsimp [b]
    split_ifs with hki hkj
    · simpa [hki] using hcfit
    · simpa [hkj] using hdfit
    · exact Nat.zero_le _
  · rw [hb]
    have : (d : ℝ)/n j ≤ r := (div_le_iff₀ hnjp).mpr (by nlinarith)
    dsimp [r] at this
    linarith
  · rw [hb]
    apply (lt_div_iff₀ hnjp).mpr
    have hcancel : (d : ℝ)/n j * n j = d := div_mul_cancel₀ _ (ne_of_gt hnjp)
    dsimp [r] at hdr
    nlinarith

def Optimal {ι : Type*} [Fintype ι] (n m u : ι → ℕ) : Prop :=
  Fits m u ∧ value n u ≤ 1 ∧ ∀ b, Fits m b → value n b ≤ 1 → value n b ≤ value n u

/-- The comparison before specializing the full profile to a prime-box optimum. -/
theorem majority_profile_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n m u a : ι → ℕ} {ρ δ : ℝ} {L B : ℕ} {i j : ι}
    (hn : ∀ k, 2 ≤ n k) (hj : ∀ k, n k ≤ n j) (hij : i ≠ j)
    (hm : ∀ k, ρ * n k ≤ m k) (hρ : 1/2 < ρ)
    (hu : Optimal n m u) (ha : Full n a) (hδ : 0 < δ)
    (hs : value n a = 1 - δ) (hL : 1 ≤ (2*ρ-1)*(2:ℝ)^L)
    (hLB : L ≤ B) (hB : 2 ≤ B) : (1 - value n u)^B < δ := by
  let D : ℝ := n j
  let E : ℝ := 1 - value n u
  have hnpos : ∀ k, 0 < n k := fun k => lt_of_lt_of_le (by omega) (hn k)
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ n j by have := hn j; omega)
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hnD : ∀ k, (n k : ℝ) ≤ D := fun k => by dsimp [D]; exact_mod_cast hj k
  have hE : 0 ≤ E := sub_nonneg.mpr hu.2.1
  obtain ⟨b, hb, hb1, hbgap⟩ := two_column_fill hij (hn i) (hnpos j) hm hρ
  have hED : E < 1/D := by
    have hmax := hu.2.2 b hb hb1
    dsimp [E, D]
    linarith
  have hEDmul : E*D < 1 := (lt_div_iff₀ hDp).mp hED
  have hElt : E < 1 := lt_of_lt_of_le hED (by simpa using one_div_le_one_div_of_le zero_lt_one hD)
  by_cases hsmall : (Finset.univ.filter (fun k => 0 < a k)).card ≤ L
  · have hgrid := sparse_gap hnpos hnD hD hδ hs (le_trans hsmall hLB)
    have hpow : (E*D)^B < 1 := pow_lt_one₀ (mul_nonneg hE hDp.le) hEDmul (by omega)
    rw [mul_pow] at hpow
    have hDB : 0 < D^B := pow_pos hDp _
    change E^B < δ
    nlinarith
  · have hex : ∃ T : ℕ, D ≤ (2:ℝ)^T := by
      obtain ⟨T, _, hT⟩ := exists_nat_pow_near hD (by norm_num : (1:ℝ)<2)
      exact ⟨T + 1, hT.le⟩
    let T := Nat.find hex
    have hT : D ≤ (2:ℝ)^T := Nat.find_spec hex
    have hbefore : ∀ v < T, (2:ℝ)^v < D := by
      intro v hv
      exact lt_of_not_ge (Nat.find_min hex hv)
    obtain ⟨b, hb, hb1, hbg⟩ := repair_large_support hnpos hnD hm hρ ha hδ hs
      hT hbefore hL (by omega)
    have hEδ : E < D*δ := by
      have hmax := hu.2.2 b hb hb1.le
      dsimp [E]
      linarith
    have hsq : E^2 < δ := by
      have h1 := mul_le_mul_of_nonneg_left hEδ.le hE
      have h2 := mul_lt_mul_of_pos_right hEDmul hδ
      nlinarith
    change E^B < δ
    exact lt_of_le_of_lt (pow_le_pow_of_le_one hE hElt.le hB) hsq

theorem exists_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] (n m : ι → ℕ) :
    ∃ u, Optimal n m u := by
  classical
  let S := (Fintype.piFinset (fun i => Finset.range (m i + 1))).filter (fun a => value n a ≤ 1)
  have hmem : ∀ a, a ∈ S ↔ Fits m a ∧ value n a ≤ 1 := by
    intro a
    simp [S, Fits]
  have hzero : (fun _ => 0) ∈ S := by
    rw [hmem]
    exact ⟨fun _ => Nat.zero_le _, by simp [value]⟩
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image S (value n) ⟨_, hzero⟩
  refine ⟨u, (hmem u).mp hu |>.1, (hmem u).mp hu |>.2, ?_⟩
  intro b hb hb1
  exact hmax b ((hmem b).mpr ⟨hb, hb1⟩)

/-- Clearing denominators in the whole count vector. -/
theorem cleared_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ι → ℕ} (hn : ∀ i, 0 < n i) :
    (∏ i, (n i : ℝ)) * value n a =
      ∑ i, (a i : ℝ) * ∏ k ∈ Finset.univ.erase i, (n k : ℝ) := by
  unfold value
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hp := Finset.prod_erase_mul Finset.univ (fun k => (n k : ℝ)) (Finset.mem_univ i)
  rw [← hp]
  have hni : (n i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hn i))
  field_simp

/-- Pairwise coprime denominators below their capacities cannot sum to one. -/
theorem full_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n a : ι → ℕ} (hn : ∀ i, 0 < n i)
    (hcop : Pairwise (fun i j => Nat.Coprime (n i) (n j)))
    (ha : Full n a) : value n a ≠ 1 := by
  intro hs
  have heq := cleared_value (a := a) hn
  rw [hs, mul_one] at heq
  have heqN : (∏ i, n i) = ∑ i, a i * ∏ k ∈ Finset.univ.erase i, n k := by
    exact_mod_cast heq
  have hazero : ∀ i, a i = 0 := by
    intro i
    let f : ι → ℕ := fun j => a j * ∏ k ∈ Finset.univ.erase j, n k
    have hdivsum : n i ∣ ∑ j ∈ Finset.univ.erase i, f j := by
      apply Finset.dvd_sum
      intro j hj
      apply dvd_mul_of_dvd_right
      apply Finset.dvd_prod_of_mem
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
      exact Ne.symm hj
    have hdivall : n i ∣ ∑ j, f j := by
      change n i ∣ ∑ j, a j * ∏ k ∈ Finset.univ.erase j, n k
      rw [← heqN]
      exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    have hterm : n i ∣ f i := by
      rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)] at hdivall
      exact (Nat.dvd_add_iff_right hdivsum).mpr hdivall
    have hcopprod : Nat.Coprime (n i) (∏ k ∈ Finset.univ.erase i, n k) := by
      apply Nat.Coprime.prod_right
      intro k hk
      exact hcop (Ne.symm (Finset.mem_erase.mp hk).1)
    have hai : n i ∣ a i := hcopprod.dvd_of_dvd_mul_right hterm
    exact Nat.eq_zero_of_dvd_of_lt hai (ha i)
  have : value n a = 0 := by simp [value, hazero]
  linarith

noncomputable def deficit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n m : ι → ℕ) : ℝ :=
  1 - sSup {x : ℝ | ∃ a, Fits m a ∧ value n a ≤ 1 ∧ x = value n a}

theorem deficit_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n m u : ι → ℕ} (hu : Optimal n m u) : deficit n m = 1-value n u := by
  have hg : IsGreatest {x : ℝ | ∃ a, Fits m a ∧ value n a ≤ 1 ∧ x = value n a} (value n u) := by
    refine ⟨⟨u, hu.1, hu.2.1, rfl⟩, ?_⟩
    rintro x ⟨a, ha, ha1, rfl⟩
    exact hu.2.2 a ha ha1
  unfold deficit
  rw [hg.csSup_eq]

noncomputable def majorityExponent (ρ : ℝ) : ℕ :=
  max 2 ⌈Real.logb 2 (1 / (2*ρ-1))⌉₊

theorem majority_threshold {ρ : ℝ} (hρ : 1/2 < ρ) :
    1 ≤ (2*ρ-1)*(2:ℝ)^⌈Real.logb 2 (1/(2*ρ-1))⌉₊ := by
  have hε : 0 < 2*ρ-1 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (Nat.le_ceil (Real.logb 2 (1/(2*ρ-1))))
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast] at hpow
  have := (div_le_iff₀ hε).mp hpow
  nlinarith

/-- Fixed-majority completion, for pairwise coprime denominator inventories. -/
theorem majority_completion_coprime {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {n m : ι → ℕ} {ρ : ℝ}
    (hn : ∀ i, 2 ≤ n i) (hcop : Pairwise (fun i j => Nat.Coprime (n i) (n j)))
    (hm : ∀ i, ρ * n i ≤ m i) (hmn : ∀ i, m i < n i)
    (hρ : 1/2 < ρ) :
    deficit n m < (deficit n (fun i => n i - 1)) ^ (1 / (majorityExponent ρ : ℝ)) := by
  classical
  let u := Classical.choose (exists_optimal n m)
  let a := Classical.choose (exists_optimal n (fun i => n i-1))
  have hu : Optimal n m u := Classical.choose_spec (exists_optimal n m)
  have haopt : Optimal n (fun i => n i-1) a := Classical.choose_spec (exists_optimal n (fun i => n i-1))
  have ha : Full n a := by
    intro i
    have hai := haopt.1 i
    dsimp at hai
    have hni := hn i
    omega
  have hnpos : ∀ i, 0 < n i := fun i => lt_of_lt_of_le (by omega) (hn i)
  have huFull : Full n u := fun i => lt_of_le_of_lt (hu.1 i) (hmn i)
  have huPos : 0 < 1-value n u :=
    sub_pos.mpr (lt_of_le_of_ne hu.2.1 (full_ne_one hnpos hcop huFull))
  have hδ : 0 < 1 - value n a := sub_pos.mpr (lt_of_le_of_ne haopt.2.1 (full_ne_one hnpos hcop ha))
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ n Finset.univ_nonempty
  obtain ⟨i, hij⟩ := exists_ne j
  have hp := majority_profile_power hn (fun k => hj k (Finset.mem_univ k)) hij hm hρ hu ha hδ
    (by ring) (majority_threshold hρ)
    (show ⌈Real.logb 2 (1/(2*ρ-1))⌉₊ ≤ majorityExponent ρ from le_max_right _ _)
    (show 2 ≤ majorityExponent ρ from le_max_left _ _)
  have hB : majorityExponent ρ ≠ 0 := by have := le_max_left 2 ⌈Real.logb 2 (1/(2*ρ-1))⌉₊; unfold majorityExponent; omega
  have hroot : ((1-value n a) ^ (1 / (majorityExponent ρ : ℝ))) ^ majorityExponent ρ = 1-value n a := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hδ.le hB
  rw [deficit_eq hu, deficit_eq haopt]
  by_contra hno
  have hle := pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) (le_of_not_gt hno) (majorityExponent ρ)
  rw [hroot] at hle
  have hnonneg : 0 ≤ (1-value n u)^majorityExponent ρ := pow_nonneg huPos.le _
  linarith

/-- The advertised prime-box theorem. Counts are the prescribed original inventory. -/
theorem majority_completion {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {p m : ι → ℕ} {ρ : ℝ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hm : ∀ i, ⌈ρ * p i⌉₊ ≤ m i) (hmp : ∀ i, m i < p i)
    (hρ : 1/2 < ρ) :
    deficit p m < (deficit p (fun i => p i - 1)) ^ (1 / (majorityExponent ρ : ℝ)) := by
  apply majority_completion_coprime (fun i => (hp i).two_le) ?_ ?_ hmp hρ
  · intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  · intro i
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hm i)

def inventory {ι : Type*} [Fintype ι] (n m : ι → ℕ) : Multiset ℕ :=
  ∑ i, Multiset.replicate (m i) (n i)

noncomputable def mass (A : Multiset ℕ) : ℝ :=
  (A.map (fun n : ℕ => (n : ℝ)⁻¹)).sum

theorem inventory_lift {ι : Type*} [Fintype ι] {n m a : ι → ℕ}
    (ha : Fits m a) : inventory n a ≤ inventory n m := by
  apply Finset.sum_le_sum
  intro i _
  exact (Multiset.replicate_le_replicate (n i)).mpr (ha i)

theorem inventory_mass {ι : Type*} [Fintype ι] (n a : ι → ℕ) :
    mass (inventory n a) = value n a := by
  classical
  have hsum : ∀ S : Finset ι, mass (∑ i ∈ S, Multiset.replicate (a i) (n i)) =
      ∑ i ∈ S, (a i : ℝ)/n i := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [mass]
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hadd : ∀ A B, mass (A+B) = mass A + mass B := by
        intro A B; simp [mass, Multiset.map_add, Multiset.sum_add]
      rw [hadd, ih]
      simp [mass, div_eq_mul_inv]
  exact hsum Finset.univ

/-- A count optimum is attained by a genuine submultiset of the inventory. -/
theorem deficit_attained {ι : Type*} [Fintype ι] [DecidableEq ι] (n m : ι → ℕ) :
    ∃ S ≤ inventory n m, mass S ≤ 1 ∧ 1-mass S = deficit n m := by
  obtain ⟨u, hu⟩ := exists_optimal n m
  refine ⟨inventory n u, inventory_lift hu.1, ?_, ?_⟩
  · simpa [inventory_mass] using hu.2.1
  · rw [inventory_mass, deficit_eq hu]

theorem inventory_count {ι : Type*} [Fintype ι] (n m : ι → ℕ) (q : ℕ) :
    (inventory n m).count q = ∑ i, if n i = q then m i else 0 := by
  classical
  have hsum : ∀ S : Finset ι, (∑ i ∈ S, Multiset.replicate (m i) (n i)).count q =
      ∑ i ∈ S, if n i = q then m i else 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi, Multiset.count_add, ih]
      by_cases h : n i = q
      · simp [h]
      · simp [Multiset.count_replicate, h]
  exact hsum Finset.univ

theorem inventory_count_at {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n m : ι → ℕ) (hinj : Function.Injective n) (i : ι) :
    (inventory n m).count (n i) = m i := by
  rw [inventory_count]
  have he : ∀ j, n j = n i ↔ j = i := fun j => ⟨fun h => hinj h, congrArg n⟩
  simp [he]

theorem submultiset_profile {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n m : ι → ℕ} (hinj : Function.Injective n) {S : Multiset ℕ}
    (hS : S ≤ inventory n m) :
    ∃ a, Fits m a ∧ S = inventory n a := by
  let a : ι → ℕ := fun i => S.count (n i)
  have hfit : Fits m a := by
    intro i
    have hc := (Multiset.le_iff_count.mp hS) (n i)
    rwa [inventory_count_at n m hinj i] at hc
  refine ⟨a, hfit, ?_⟩
  apply Multiset.ext.mpr
  intro q
  by_cases hq : ∃ i, n i = q
  · obtain ⟨i, rfl⟩ := hq
    rw [inventory_count_at n a hinj i]
  · have hnone : ∀ i, n i ≠ q := by simpa using hq
    have hc := (Multiset.le_iff_count.mp hS) q
    rw [inventory_count] at hc ⊢
    simp [hnone] at hc ⊢
    exact hc

/-- The profile deficit equals the optimum over actual submultisets. -/
theorem deficit_multiset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n m : ι → ℕ) (hinj : Function.Injective n) :
    deficit n m = 1 - sSup {x : ℝ | ∃ S ≤ inventory n m, mass S ≤ 1 ∧ x = mass S} := by
  unfold deficit
  congr 2
  ext x
  constructor
  · rintro ⟨a, ha, ha1, rfl⟩
    exact ⟨inventory n a, inventory_lift ha, by simpa [inventory_mass] using ha1,
      (inventory_mass n a).symm⟩
  · rintro ⟨S, hS, hS1, rfl⟩
    obtain ⟨a, ha, rfl⟩ := submultiset_profile hinj hS
    exact ⟨a, ha, by simpa [inventory_mass] using hS1, inventory_mass n a⟩

end Submissions.E312MajorityCompletion.Majority
