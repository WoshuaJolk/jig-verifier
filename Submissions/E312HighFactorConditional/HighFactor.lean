import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
Conditional high-factor exponential approximation theorem for Erdős 312.
The analytic assumptions are fixed separately from the target and remain assumptions.
proof proves the exact implication; it does not solve full E312.
-/
namespace Submissions.E312HighFactorConditional.HighFactor

noncomputable def mass (A : Multiset ℕ) : ℝ :=
  (A.map fun n : ℕ => (n : ℝ)⁻¹).sum

def positive (A : Multiset ℕ) : Prop := ∀ n ∈ A, 0 < n

def stable (A : Multiset ℕ) : Prop :=
  (∀ n ∈ A, 2 ≤ n) ∧ ∀ n ∈ A, A.count n < n.minFac

def factorCount (n : ℕ) : ℕ := n.primeFactorsList.length

theorem factorCount_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    factorCount (a * b) = factorCount a + factorCount b := by
  simpa [factorCount] using (Nat.perm_primeFactorsList_mul ha hb).length_eq

theorem factorCount_prime_mul {p n : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0) :
    factorCount (p * n) = 1 + factorCount n := by
  rw [factorCount_mul hp.ne_zero hn]
  simp [factorCount, Nat.primeFactorsList_prime hp]

def selectedFactorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∈ P)).length

theorem squarefree_factorCount {n : ℕ} (hn : Squarefree n) :
    n.primeFactorsList.toFinset.card = factorCount n := by
  exact List.toFinset_card_of_nodup hn.nodup_primeFactorsList

theorem squarefree_selectedFactorCount (P : Finset ℕ) {n : ℕ}
    (hn : Squarefree n) :
    (P ∩ n.primeFactorsList.toFinset).card = selectedFactorCount P n := by
  have h := List.toFinset_card_of_nodup
    (hn.nodup_primeFactorsList.filter (fun p => p ∈ P))
  simpa [selectedFactorCount, List.toFinset_filter, Finset.filter_mem_eq_inter,
    Finset.inter_comm] using h

theorem selectedFactorCount_mul (P : Finset ℕ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    selectedFactorCount P (a * b) =
      selectedFactorCount P a + selectedFactorCount P b := by
  have h := (Nat.perm_primeFactorsList_mul ha hb).filter (fun p => p ∈ P)
  simpa [selectedFactorCount, List.filter_append] using h.length_eq

theorem selectedFactorCount_prime_mul (P : Finset ℕ) {p n : ℕ}
    (hp : Nat.Prime p) (hpP : p ∈ P) (hn : n ≠ 0) :
    selectedFactorCount P (p * n) = 1 + selectedFactorCount P n := by
  rw [selectedFactorCount_mul P hp.ne_zero hn]
  simp [selectedFactorCount, Nat.primeFactorsList_prime hp, hpP]

noncomputable def approximates (A : Multiset ℕ) (δ : ℝ) : Prop :=
  ∃ B : Multiset ℕ, B ≤ A ∧ 1 - δ ≤ mass B ∧ mass B ≤ 1

noncomputable def generalEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
    ∀ A : Multiset ℕ, positive A → R₀ ≤ mass A →
      approximates A (Real.exp (-c * Real.sqrt (mass A * Real.log (mass A))))

noncomputable def primeEstimate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
    ∀ (A : Multiset ℕ) (a : ℝ),
      (∀ p ∈ A, Nat.Prime p) → 0 < a → a < 1 →
      (∀ p ∈ A, (A.count p : ℝ) / p ≤ a) → R₀ ≤ mass A →
      approximates A (Real.exp (-c * min (mass A)
        (Real.sqrt (mass A * Real.log (mass A) / a))))

noncomputable def highFactorConclusion : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
    ∀ A : Multiset ℕ, stable A → R₀ ≤ mass A →
      (∀ n ∈ A, C * (Real.log (mass A)) ^ 2 ≤ (factorCount n : ℝ)) →
      approximates A (Real.exp (-c * mass A))

/-- The exact conditional theorem type, proved by proof below. -/
noncomputable def conditionalTarget : Prop :=
  generalEstimate → primeEstimate → highFactorConclusion

/-- Index zero is the general stretched-exponential rate. -/
noncomputable def recursiveRate (k : ℕ) (L R : ℝ) : ℝ :=
  min R (Real.sqrt (R * Real.log R * L ^ k))

theorem recursiveRate_amplifies (k : ℕ) {L R S : ℝ}
    (hL : 1 ≤ L) (hR : 1 ≤ R) (hS : 16 * R * L ≤ S) :
    4 * recursiveRate (k + 1) L R ≤ recursiveRate k L S := by
  have hR0 : 0 ≤ R := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hRL : R ≤ R * L := by nlinarith
  have hRS : R ≤ S := by nlinarith
  have hS0 : 0 ≤ S := hR0.trans hRS
  have hlog : Real.log R ≤ Real.log S :=
    Real.log_le_log (by linarith) hRS
  have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlogS0 : 0 ≤ Real.log S := hlog0.trans hlog
  have hp : 0 ≤ L ^ k := pow_nonneg hL0 k
  have hprod : 16 * (R * Real.log R * L ^ (k + 1)) ≤
      S * Real.log S * L ^ k := by
    have h₁ := mul_le_mul_of_nonneg_right hS hlog0
    have h₂ := mul_le_mul_of_nonneg_left hlog hS0
    have h₃ := mul_le_mul_of_nonneg_right (h₁.trans h₂) hp
    rw [pow_succ]
    nlinarith only [h₃]
  have hroot : 4 * Real.sqrt (R * Real.log R * L ^ (k + 1)) ≤
      Real.sqrt (S * Real.log S * L ^ k) := by
    have h₁ := Real.sq_sqrt (show 0 ≤ R * Real.log R * L ^ (k + 1) by positivity)
    have h₂ := Real.sq_sqrt (show 0 ≤ S * Real.log S * L ^ k by positivity)
    have h₃ := Real.sqrt_nonneg (S * Real.log S * L ^ k)
    have h₄ := Real.sqrt_nonneg (R * Real.log R * L ^ (k + 1))
    nlinarith
  unfold recursiveRate
  apply le_min
  · have := min_le_left R (Real.sqrt (R * Real.log R * L ^ (k + 1)))
    nlinarith
  · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans hroot

@[simp] theorem mass_zero : mass 0 = 0 := by simp [mass]

@[simp] theorem mass_cons (n : ℕ) (A : Multiset ℕ) :
    mass (n ::ₘ A) = (n : ℝ)⁻¹ + mass A := by simp [mass]

@[simp] theorem mass_add (A B : Multiset ℕ) :
    mass (A + B) = mass A + mass B := by simp [mass]

theorem mass_nonneg (A : Multiset ℕ) : 0 ≤ mass A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons n A ih =>
    rw [mass_cons]
    exact add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) ih

theorem approximates_mono {A B : Multiset ℕ} {δ : ℝ}
    (hAB : A ≤ B) (h : approximates A δ) : approximates B δ := by
  obtain ⟨S, hS, hlo, hhi⟩ := h
  exact ⟨S, hS.trans hAB, hlo, hhi⟩

theorem approximates_error_mono {A : Multiset ℕ} {δ ε : ℝ}
    (hδε : δ ≤ ε) (h : approximates A δ) : approximates A ε := by
  obtain ⟨S, hS, hlo, hhi⟩ := h
  exact ⟨S, hS, le_trans (sub_le_sub_left hδε 1) hlo, hhi⟩

theorem stable_positive {A : Multiset ℕ} (h : stable A) : positive A := by
  intro n hn
  have := h.1 n hn
  omega

theorem stable_submultiset {A B : Multiset ℕ} (h : stable A) (hBA : B ≤ A) :
    stable B := by
  constructor
  · intro n hn
    exact h.1 n (Multiset.mem_of_le hBA hn)
  · intro n hn
    exact lt_of_le_of_lt (Multiset.count_le_of_le n hBA)
      (h.2 n (Multiset.mem_of_le hBA hn))

theorem mass_sub {A B : Multiset ℕ} (hBA : B ≤ A) :
    mass (A - B) = mass A - mass B := by
  have h := congrArg mass (Multiset.sub_add_cancel hBA)
  rw [mass_add] at h
  linarith

theorem mass_mono {A B : Multiset ℕ} (hAB : A ≤ B) : mass A ≤ mass B := by
  have h := mass_nonneg (B - A)
  rw [mass_sub hAB] at h
  linarith

/-- An optimizer is over actual submultisets, not fractional coefficients. -/
noncomputable def optimal (A S : Multiset ℕ) : Prop :=
  S ≤ A ∧ mass S ≤ 1 ∧
    ∀ T : Multiset ℕ, T ≤ A → mass T ≤ 1 → mass T ≤ mass S

theorem exists_optimal (A : Multiset ℕ) : ∃ S, optimal A S := by
  classical
  let candidates := A.powerset.toFinset.filter (fun S => mass S ≤ 1)
  have hz : (0 : Multiset ℕ) ∈ candidates := by simp [candidates]
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image mass ⟨0, hz⟩
  have hS' : S ≤ A ∧ mass S ≤ 1 := by
    simpa [candidates] using hS
  refine ⟨S, hS'.1, hS'.2, ?_⟩
  intro T hTA hT
  apply hmax T
  simpa [candidates] using And.intro hTA hT

theorem optimal_unused_reciprocal {A S : Multiset ℕ} {n : ℕ}
    (h : optimal A S) (hn : 0 < n) (havailable : n ::ₘ S ≤ A) :
    1 - mass S < (n : ℝ)⁻¹ := by
  by_contra hbad
  have hsmall : (n : ℝ)⁻¹ ≤ 1 - mass S := le_of_not_gt hbad
  have hfits : mass (n ::ₘ S) ≤ 1 := by rw [mass_cons]; linarith
  have hmax := h.2.2 (n ::ₘ S) havailable hfits
  rw [mass_cons] at hmax
  have hp : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  linarith

theorem optimal_complement_mass {A S : Multiset ℕ} (h : optimal A S)
    (hstrict : mass S < 1) : mass A - 1 < mass (A - S) := by
  rw [mass_sub h.1]
  linarith

theorem optimal_complement_stable {A S : Multiset ℕ} (hA : stable A) :
    stable (A - S) :=
  stable_submultiset hA (Multiset.sub_le_self A S)

theorem optimal_complement_denominator {A S : Multiset ℕ}
    (h : optimal A S) (hpos : positive A) (hstrict : mass S < 1)
    {n : ℕ} (hn : n ∈ A - S) :
    (n : ℝ) < (1 - mass S)⁻¹ := by
  have hnpos := hpos n (Multiset.mem_of_le (Multiset.sub_le_self A S) hn)
  have havailable : n ::ₘ S ≤ A := by
    have hs : ({n} : Multiset ℕ) ≤ A - S := Multiset.singleton_le.mpr hn
    have ha : ({n} : Multiset ℕ) + S ≤ A - S + S :=
      Multiset.add_le_add_right hs
    simpa only [Multiset.singleton_add, Multiset.sub_add_cancel h.1] using ha
  have hrec := optimal_unused_reciprocal h hnpos havailable
  have hgap : 0 < 1 - mass S := by linarith
  exact lt_inv_of_lt_inv₀ hgap hrec

/-- Cofactor scaling is exact on the original multiset, including repeats. -/
theorem mass_scale (q : ℕ) (A : Multiset ℕ) :
    mass (A.map (fun n => q * n)) = (q : ℝ)⁻¹ * mass A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons n A ih => simp [ih, Nat.cast_mul, mul_inv_rev, mul_add, mul_comm]

/-- Removing a common factor preserves stability provided no cofactor is one.
This avoids treating repeated occurrences as a set in a prime block. -/
theorem stable_cofactors (q : ℕ) (A : Multiset ℕ) (hq : 0 < q)
    (hlarge : ∀ n ∈ A, 2 ≤ n)
    (hstable : stable (A.map (fun n => q * n))) : stable A := by
  refine ⟨hlarge, ?_⟩
  intro n hn
  have hinj : Function.Injective (fun n : ℕ => q * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  have hmem : q * n ∈ A.map (fun n => q * n) :=
    Multiset.mem_map.mpr ⟨n, hn, rfl⟩
  have hc := hstable.2 (q * n) hmem
  rw [Multiset.count_map_eq_count' _ _ hinj] at hc
  have hnlarge := hlarge n hn
  have hp : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
  have hd : n.minFac ∣ q * n := (Nat.minFac_dvd n).trans (dvd_mul_left n q)
  exact hc.trans_le (Nat.minFac_le_of_dvd hp.two_le hd)

theorem mass_join (B : Multiset (Multiset ℕ)) :
    mass B.join = (B.map mass).sum := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons S B ih => simp [ih]

/-- Repeated extraction consumes original occurrences at most once. The oracle
is an internal interface, to be supplied by the recursive approximation bound. -/
theorem extract_bundles (A : Multiset ℕ) (k : ℕ) (δ : ℝ)
    (oracle : ∀ B : Multiset ℕ, B ≤ A →
      mass A - (k : ℝ) ≤ mass B → approximates B δ) :
    ∃ bundles : Multiset (Multiset ℕ),
      bundles.card = k ∧ bundles.join ≤ A ∧
      (∀ S ∈ bundles, 1 - δ ≤ mass S ∧ mass S ≤ 1) ∧
      mass bundles.join ≤ (k : ℝ) := by
  induction k with
  | zero => exact ⟨0, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    have smaller : ∀ B : Multiset ℕ, B ≤ A →
        mass A - (k : ℝ) ≤ mass B → approximates B δ := by
      intro B hBA hmass
      apply oracle B hBA
      push_cast
      linarith
    obtain ⟨bundles, hcard, hjoin, hgood, hmass⟩ := ih smaller
    have hremaining : mass A - ((k + 1 : ℕ) : ℝ) ≤
        mass (A - bundles.join) := by
      rw [mass_sub hjoin]
      push_cast
      linarith
    obtain ⟨S, hS, hlo, hhi⟩ :=
      oracle (A - bundles.join) (Multiset.sub_le_self _ _) hremaining
    refine ⟨S ::ₘ bundles, by simp [hcard], ?_, ?_, ?_⟩
    · rw [Multiset.join_cons]
      have h : S + bundles.join ≤ A - bundles.join + bundles.join :=
        Multiset.add_le_add_right hS
      simpa only [Multiset.sub_add_cancel hjoin] using h
    · intro T hT
      rcases Multiset.mem_cons.mp hT with rfl | hT
      · exact ⟨hlo, hhi⟩
      · exact hgood T hT
    · rw [Multiset.join_cons, mass_add]
      push_cast
      linarith

/-- Extracting at most half the initial mass keeps each recursive call above
the half-mass threshold, with stability inherited by every residual. -/
theorem extract_stable_half (A : Multiset ℕ) (k : ℕ) (δ : ℝ)
    (hstable : stable A) (hk : (k : ℝ) ≤ mass A / 2)
    (oracle : ∀ B : Multiset ℕ, B ≤ A → stable B →
      mass A / 2 ≤ mass B → approximates B δ) :
    ∃ bundles : Multiset (Multiset ℕ),
      bundles.card = k ∧ bundles.join ≤ A ∧
      (∀ S ∈ bundles, 1 - δ ≤ mass S ∧ mass S ≤ 1) ∧
      mass bundles.join ≤ (k : ℝ) := by
  apply extract_bundles
  intro B hBA hmass
  exact oracle B hBA (stable_submultiset hstable hBA) (by linarith)

/-- Lifting error is proportional to selected ideal mass, not bundle count. -/
theorem weighted_lifting {ι : Type*} (I : Finset ι) (actual ideal : ι → ℝ)
    {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hlow : ∀ i ∈ I, (1 - δ) * ideal i ≤ actual i)
    (hhigh : ∀ i ∈ I, actual i ≤ ideal i)
    (hnear : 1 - ε ≤ ∑ i ∈ I, ideal i)
    (hcap : (∑ i ∈ I, ideal i) ≤ 1) :
    1 - ε - δ ≤ ∑ i ∈ I, actual i ∧ (∑ i ∈ I, actual i) ≤ 1 := by
  have hlo := Finset.sum_le_sum hlow
  have hhi := Finset.sum_le_sum hhigh
  rw [← Finset.mul_sum] at hlo
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hcap hδ]
  · exact hhi.trans hcap

/-- Finite probabilistic method with two simultaneous normalized budgets.
Zero-probability outcomes are excluded from the witness. -/
theorem finite_joint_selection {ι : Type*} (I : Finset ι)
    (w f g : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hf : ∀ i ∈ I, 0 ≤ f i) (hg : ∀ i ∈ I, 0 ≤ g i)
    (hnorm : (∑ i ∈ I, w i) = 1)
    (hbudget : (∑ i ∈ I, w i * (f i + g i)) < 1) :
    ∃ i ∈ I, 0 < w i ∧ f i < 1 ∧ g i < 1 := by
  by_contra h
  have hterm : ∀ i ∈ I, w i ≤ w i * (f i + g i) := by
    intro i hi
    by_cases hwi : 0 < w i
    · have hbad : ¬ (f i < 1 ∧ g i < 1) := by
        intro hgood
        exact h ⟨i, hi, hwi, hgood⟩
      have hscore : 1 ≤ f i + g i := by
        have := hf i hi
        have := hg i hi
        push Not at hbad
        by_cases hfi : f i < 1
        · have := hbad hfi
          linarith
        · have := le_of_not_gt hfi
          linarith
      nlinarith
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hwi) (hw i hi)
      simp [hz]
  have := Finset.sum_le_sum hterm
  rw [hnorm] at this
  linarith

/-- Exact finite law of independent prime selection. -/
noncomputable def selectionWeight (U P : Finset ℕ) (θ : ℝ) : ℝ :=
  (∏ _p ∈ P, θ) * ∏ _p ∈ U \ P, (1 - θ)

theorem selectionWeight_nonneg (U P : Finset ℕ) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 ≤ selectionWeight U P θ := by
  unfold selectionWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun _ _ => hθ)
  · exact Finset.prod_nonneg (fun _ _ => sub_nonneg.mpr hθ1)

theorem selectionWeight_sum (U : Finset ℕ) (θ : ℝ) :
    (∑ P ∈ U.powerset, selectionWeight U P θ) = 1 := by
  unfold selectionWeight
  rw [← Finset.prod_add]
  simp

/-- The generating function is proved directly over the powerset, so it
does not require measure-theoretic independence assumptions. -/
theorem selectionWeight_generating (U : Finset ℕ) (θ : ℝ) (z : ℕ → ℝ) :
    (∑ P ∈ U.powerset, selectionWeight U P θ * ∏ p ∈ P, z p) =
      ∏ p ∈ U, (θ * z p + (1 - θ)) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro P hP
  unfold selectionWeight
  rw [Finset.prod_mul_distrib]
  ring

theorem selectionWeight_missing (U : Finset ℕ) (θ : ℝ) {a : ℕ}
    (ha : a ∈ U) :
    (∑ P ∈ U.powerset, if a ∈ P then 0 else selectionWeight U P θ) = 1 - θ := by
  have h := selectionWeight_generating U θ (fun p => if p = a then 0 else 1)
  have hfactor : ∀ p : ℕ,
      θ * (if p = a then 0 else 1) + (1 - θ) =
        (if p = a then 1 - θ else 1) := by
    intro p
    split_ifs <;> ring
  simp_rw [hfactor, Finset.prod_ite_eq'] at h
  simpa [ha, mul_ite] using h

theorem selectionWeight_inclusion (U : Finset ℕ) (θ : ℝ) {a : ℕ}
    (ha : a ∈ U) :
    (∑ P ∈ U.powerset, if a ∈ P then selectionWeight U P θ else 0) = θ := by
  have hmissing := selectionWeight_missing U θ ha
  have htotal := selectionWeight_sum U θ
  have hsplit :
      (∑ P ∈ U.powerset, if a ∈ P then selectionWeight U P θ else 0) +
      (∑ P ∈ U.powerset, if a ∈ P then 0 else selectionWeight U P θ) =
      ∑ P ∈ U.powerset, selectionWeight U P θ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    split_ifs <;> simp
  linarith

theorem selectionWeight_mean_sum (U : Finset ℕ) (θ : ℝ) (z : ℕ → ℝ) :
    (∑ P ∈ U.powerset, selectionWeight U P θ * ∑ p ∈ P, z p) =
      θ * ∑ p ∈ U, z p := by
  have hext : ∀ P ∈ U.powerset,
      (∑ p ∈ P, z p) = ∑ p ∈ U, if p ∈ P then z p else 0 := by
    intro P hP
    have hsub := Finset.mem_powerset.mp hP
    have h := Finset.sum_subset hsub
      (f := fun p => if p ∈ P then z p else (0 : ℝ))
      (by intro p hp hpP; simp [hpP])
    simpa using h
  calc
    _ = ∑ P ∈ U.powerset, ∑ p ∈ U,
        (if p ∈ P then selectionWeight U P θ else 0) * z p := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [hext P hP, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ = ∑ p ∈ U, ∑ P ∈ U.powerset,
        (if p ∈ P then selectionWeight U P θ else 0) * z p :=
      Finset.sum_comm
    _ = ∑ p ∈ U, θ * z p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_mul, selectionWeight_inclusion U θ hp]
    _ = _ := (Finset.mul_sum U z θ).symm

theorem selectionWeight_count_generating (U V : Finset ℕ) (hVU : V ⊆ U)
    (θ t : ℝ) :
    (∑ P ∈ U.powerset, selectionWeight U P θ * t ^ (P ∩ V).card) =
      (θ * t + (1 - θ)) ^ V.card := by
  have h := selectionWeight_generating U θ (fun p => if p ∈ V then t else 1)
  have hfactor : ∀ p : ℕ,
      θ * (if p ∈ V then t else 1) + (1 - θ) =
        (if p ∈ V then θ * t + (1 - θ) else 1) := by
    intro p
    split_ifs <;> ring
  simp_rw [hfactor, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, Finset.filter_mem_eq_inter] at h
  simpa [Finset.inter_eq_right.mpr hVU] using h

theorem selectionWeight_lower_tail (U V : Finset ℕ) (hVU : V ⊆ U)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (T : ℕ) :
    (∑ P ∈ U.powerset,
      if (P ∩ V).card < T then selectionWeight U P θ else 0) *
      (1 / 2 : ℝ) ^ T ≤ (1 - θ / 2) ^ V.card := by
  have hterm : ∀ P ∈ U.powerset,
      (if (P ∩ V).card < T then selectionWeight U P θ else 0) *
        (1 / 2 : ℝ) ^ T ≤
      selectionWeight U P θ * (1 / 2 : ℝ) ^ (P ∩ V).card := by
    intro P hP
    have hw := selectionWeight_nonneg U P hθ hθ1
    split_ifs with hcount
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount.le) hw
    · simp only [zero_mul]
      positivity
  have h := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, selectionWeight_count_generating U V hVU] at h
  convert h using 1
  congr 1
  ring

theorem selectionWeight_chernoff (U V : Finset ℕ) (hVU : V ⊆ U)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ θ * V.card / 2) :
    (∑ P ∈ U.powerset,
      if (P ∩ V).card < T then selectionWeight U P θ else 0) ≤
      Real.exp (-θ * V.card / 8) := by
  have htail := selectionWeight_lower_tail U V hVU hθ hθ1 T
  have hbase : 1 - θ / 2 ≤ Real.exp (-θ / 2) := by
    linarith [Real.add_one_le_exp (-θ / 2)]
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 - θ / 2 by linarith) hbase V.card
  rw [← Real.exp_nat_mul] at hp
  have hhalf : (1 / 2 : ℝ) ^ T = Real.exp (-(T : ℝ) * Real.log 2) := by
    rw [show -(T : ℝ) * Real.log 2 = (T : ℝ) * (-Real.log 2) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  have hlog : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hexponent : (V.card : ℝ) * (-θ / 2) ≤
      -θ * V.card / 8 + (-(T : ℝ) * Real.log 2) := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  have hexp := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_add, ← hhalf] at hexp
  exact (mul_le_mul_iff_left₀ (show (0 : ℝ) < (1 / 2 : ℝ) ^ T by positivity)).mp
    (htail.trans (hp.trans hexp))

/-- Linearity of discarded mass over actual occurrences, not distinct values. -/
theorem expected_discarded_mass {ι : Type*} (I : Finset ι) (w : ι → ℝ)
    (bad : ι → ℕ → Prop) [∀ i, DecidablePred (bad i)]
    (A : Multiset ℕ) {δ : ℝ}
    (hbad : ∀ n ∈ A, (∑ i ∈ I, if bad i n then w i else 0) ≤ δ) :
    (∑ i ∈ I, w i * mass (A.filter (bad i))) ≤ δ * mass A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons n A ih =>
    have hn := hbad n (Multiset.mem_cons_self n A)
    have hA := ih (fun m hm => hbad m (Multiset.mem_cons_of_mem hm))
    have heq : (∑ i ∈ I, w i * mass ((n ::ₘ A).filter (bad i))) =
        (∑ i ∈ I, if bad i n then w i else 0) * (n : ℝ)⁻¹ +
        ∑ i ∈ I, w i * mass (A.filter (bad i)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : bad i n
      · simp [Multiset.filter_cons_of_pos _ h, h, mass_cons, mul_add]
      · simp [Multiset.filter_cons_of_neg _ h, h]
    rw [heq, mass_cons, mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hn (by positivity)) hA

theorem finite_joint_budgets {ι : Type*} (I : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (hf : ∀ i ∈ I, 0 ≤ f i) (hg : ∀ i ∈ I, 0 ≤ g i)
    (hnorm : (∑ i ∈ I, w i) = 1)
    {a b F G : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hF : (∑ i ∈ I, w i * f i) ≤ F)
    (hG : (∑ i ∈ I, w i * g i) ≤ G)
    (hbudget : F / a + G / b < 1) :
    ∃ i ∈ I, 0 < w i ∧ f i < a ∧ g i < b := by
  have hmean : (∑ i ∈ I, w i * (f i / a + g i / b)) < 1 := by
    simp_rw [mul_add, ← mul_div_assoc]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    exact lt_of_le_of_lt
      (add_le_add (div_le_div_of_nonneg_right hF ha.le)
        (div_le_div_of_nonneg_right hG hb.le)) hbudget
  obtain ⟨i, hi, hwi, hfi, hgi⟩ := finite_joint_selection I w
    (fun i => f i / a) (fun i => g i / b) hw
    (fun i hi => div_nonneg (hf i hi) ha.le)
    (fun i hi => div_nonneg (hg i hi) hb.le) hnorm hmean
  exact ⟨i, hi, hwi, (div_lt_one ha).mp hfi, (div_lt_one hb).mp hgi⟩

/-- The complete finite selection step: simultaneously small reciprocal prime
mass and small discarded denominator mass, with arbitrary multiplicities. -/
theorem finite_prime_selection (U : Finset ℕ) (A : Multiset ℕ)
    (V : ℕ → Finset ℕ) (T : ℕ) {θ μ a b : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hVU : ∀ n ∈ A, V n ⊆ U)
    (hμ : ∀ n ∈ A, μ ≤ θ * (V n).card)
    (hT : (T : ℝ) ≤ μ / 2)
    (hbudget : (θ * ∑ p ∈ U, (p : ℝ)⁻¹) / a +
      (Real.exp (-μ / 8) * mass A) / b < 1) :
    ∃ P : Finset ℕ, P ⊆ U ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) < a ∧
      mass (A.filter (fun n => (P ∩ V n).card < T)) < b := by
  have hbad : ∀ n ∈ A,
      (∑ P ∈ U.powerset,
        if (P ∩ V n).card < T then selectionWeight U P θ else 0) ≤
      Real.exp (-μ / 8) := by
    intro n hn
    have hμn := hμ n hn
    exact (selectionWeight_chernoff U (V n) (hVU n hn) hθ hθ1 T
      (by linarith)).trans (Real.exp_le_exp.mpr (by linarith))
  have hmass := expected_discarded_mass U.powerset
    (fun P => selectionWeight U P θ)
    (fun P n => (P ∩ V n).card < T) A hbad
  obtain ⟨P, hP, _hw, hsmall, hdiscard⟩ := finite_joint_budgets U.powerset
    (fun P => selectionWeight U P θ)
    (fun P => ∑ p ∈ P, (p : ℝ)⁻¹)
    (fun P => mass (A.filter (fun n => (P ∩ V n).card < T)))
    (fun P _ => selectionWeight_nonneg U P hθ hθ1)
    (fun P _ => Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)))
    (fun P _ => mass_nonneg _)
    (selectionWeight_sum U θ) ha hb
    (selectionWeight_mean_sum U θ (fun p => (p : ℝ)⁻¹)).le hmass hbudget
  exact ⟨P, Finset.mem_powerset.mp hP, hsmall, hdiscard⟩

theorem squarefree_prime_selection (U : Finset ℕ) (A : Multiset ℕ)
    (T : ℕ) {θ μ a b : ℝ}
    (hstable : stable A) (hsquare : ∀ n ∈ A, Squarefree n)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hU : ∀ n ∈ A, n.primeFactorsList.toFinset ⊆ U)
    (hμ : ∀ n ∈ A, μ ≤ θ * factorCount n)
    (hT : (T : ℝ) ≤ μ / 2)
    (hbudget : (θ * ∑ p ∈ U, (p : ℝ)⁻¹) / a +
      (Real.exp (-μ / 8) * mass A) / b < 1) :
    ∃ (P : Finset ℕ) (B : Multiset ℕ), P ⊆ U ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) < a ∧ B ≤ A ∧ stable B ∧
      mass A - b < mass B ∧
      (∀ n ∈ B, Squarefree n ∧ T ≤ selectedFactorCount P n) := by
  obtain ⟨P, hPU, hsmall, hdiscard⟩ := finite_prime_selection U A
    (fun n => n.primeFactorsList.toFinset) T hθ hθ1 ha hb hU
    (fun n hn => by
      rw [squarefree_factorCount (hsquare n hn)]
      exact hμ n hn)
    hT hbudget
  let B := A.filter (fun n => ¬ (P ∩ n.primeFactorsList.toFinset).card < T)
  have hBA : B ≤ A := Multiset.filter_le _ _
  have hpartition := congrArg mass
    (Multiset.filter_add_not (fun n => (P ∩ n.primeFactorsList.toFinset).card < T) A)
  rw [mass_add] at hpartition
  refine ⟨P, B, hPU, hsmall, hBA, stable_submultiset hstable hBA, ?_, ?_⟩
  · change mass A - b < mass (A.filter
      (fun n => ¬ (P ∩ n.primeFactorsList.toFinset).card < T))
    linarith
  · intro n hn
    have hn' := Multiset.mem_filter.mp hn
    have hs := hsquare n hn'.1
    refine ⟨hs, ?_⟩
    rw [← squarefree_selectedFactorCount P hs]
    exact Nat.le_of_not_lt hn'.2

noncomputable def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [Nat.cast_mul, mul_inv_rev, mul_comm]

theorem reciprocalHom_prime_norm {p : ℕ} (hp : Nat.Prime p) :
    ‖reciprocalHom p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem reciprocal_factored_hasSum (P : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers P => (n.val : ℝ)⁻¹)
      (∏ p ∈ P with Nat.Prime p, (1 - (p : ℝ)⁻¹)⁻¹) := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun hp => reciprocalHom_prime_norm hp) P).2

/-- Every finite distinct inventory supported on P is bounded by its Euler
product. This is an arithmetic sum, not a statement about multiplicities. -/
theorem reciprocal_sum_le_eulerProduct (P S : Finset ℕ)
    (hS : ∀ n ∈ S, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      ∏ p ∈ P with Nat.Prime p, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have h := sum_le_hasSum (S.subtype (· ∈ Nat.factoredNumbers P))
    (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.val)) (reciprocal_factored_hasSum P)
  rw [Finset.sum_subtype_of_mem (fun n : ℕ => (n : ℝ)⁻¹) hS] at h
  exact h

noncomputable def eulerProduct (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹

theorem reciprocal_sum_le_primeProduct (P S : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : ∀ n ∈ S, n ∈ Nat.factoredNumbers P) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ eulerProduct P := by
  have h := reciprocal_sum_le_eulerProduct P S hS
  simpa only [Finset.filter_eq_self.mpr hP, eulerProduct] using h

theorem log_le_eulerProduct (N : ℕ) :
    Real.log (N + 1 : ℕ) ≤ eulerProduct (N + 1).primesBelow := by
  have h := reciprocal_sum_le_primeProduct (N + 1).primesBelow (Finset.Icc 1 N)
    (fun p hp => Nat.prime_of_mem_primesBelow hp) (by
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      refine Nat.mem_factoredNumbers.mpr ⟨by omega, ?_⟩
      intro p hp
      have hp' := Nat.mem_primeFactorsList'.mp hp
      have hpn := Nat.le_of_dvd (by omega : 0 < n) hp'.2.1
      exact Nat.mem_primesBelow.mpr ⟨by omega, hp'.1⟩)
  have hlog := log_add_one_le_harmonic N
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlog
  exact hlog.trans h

theorem eulerProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    0 < eulerProduct P := by
  apply Finset.prod_pos
  intro p hp
  apply inv_pos.mpr
  have hi : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (hP p hp).one_lt)
  linarith

theorem eulerProduct_sdiff (P Q : Finset ℕ) (hQP : Q ⊆ P) :
    eulerProduct (P \ Q) * eulerProduct Q = eulerProduct P := by
  exact Finset.prod_sdiff hQP

/-- Rough harmonic sums reduce to a full Euler-product upper bound; the
small-prime denominator contributes a genuine logarithmic saving. -/
theorem rough_reciprocal_sum_le (D r : ℕ) (hr : 2 ≤ r) (hrD : r ≤ D + 1)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ D ∧
      ∀ p ∈ n.primeFactorsList, r ≤ p) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ eulerProduct (D + 1).primesBelow / Real.log r := by
  let P := (D + 1).primesBelow
  let Q := r.primesBelow
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hQ : ∀ p ∈ Q, Nat.Prime p := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hQP : Q ⊆ P := by
    intro p hp
    have hp' := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨lt_of_lt_of_le hp'.1 hrD, hp'.2⟩
  have hsupport : ∀ n ∈ S, n ∈ Nat.factoredNumbers (P \ Q) := by
    intro n hn
    obtain ⟨hn0, hnD, hnrough⟩ := hS n hn
    refine Nat.mem_factoredNumbers.mpr ⟨by omega, ?_⟩
    intro p hp
    have hp' := Nat.mem_primeFactorsList'.mp hp
    have hpn := Nat.le_of_dvd hn0 hp'.2.1
    have hrp := hnrough p hp
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Nat.mem_primesBelow.mpr ⟨by omega, hp'.1⟩
    · intro hpQ
      have := Nat.lt_of_mem_primesBelow hpQ
      omega
  have hsum := reciprocal_sum_le_primeProduct (P \ Q) S
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1) hsupport
  have hlog : Real.log r ≤ eulerProduct Q := by
    have h := log_le_eulerProduct (r - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using h
  have hlog0 : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hprod0 : 0 ≤ eulerProduct (P \ Q) :=
    (eulerProduct_pos _ (fun p hp => hP p (Finset.mem_sdiff.mp hp).1)).le
  apply (le_div_iff₀ hlog0).mpr
  calc
    _ ≤ eulerProduct (P \ Q) * Real.log r := mul_le_mul_of_nonneg_right hsum hlog0.le
    _ ≤ eulerProduct (P \ Q) * eulerProduct Q := mul_le_mul_of_nonneg_left hlog hprod0
    _ = _ := eulerProduct_sdiff P Q hQP

/-- Discrete partial summation with a retained boundary deficit. -/
theorem weighted_prefix_bound_aux (a : ℕ → ℝ) (C : ℝ)
    (hprefix : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ C * n) (n : ℕ) :
    (∑ k ∈ Finset.range n, a k / (k + 1 : ℕ)) +
      (C * n - ∑ k ∈ Finset.range n, a k) / (n + 1 : ℕ) ≤
      C * ∑ k ∈ Finset.range n, (k + 1 : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : 0 ≤ C * (n + 1 : ℕ) - ∑ k ∈ Finset.range (n + 1), a k :=
      sub_nonneg.mpr (hprefix (n + 1))
    have hdiv := div_le_div_of_nonneg_left hd
      (show (0 : ℝ) < (n + 1 : ℕ) by positivity)
      (show ((n + 1 : ℕ) : ℝ) ≤ (n + 2 : ℕ) by exact_mod_cast Nat.le_succ (n + 1))
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hdiv ⊢
    simp only [Nat.cast_add, Nat.cast_one] at ih
    have hrel : a n / ((n : ℝ) + 1) +
        (C * ((n : ℝ) + 1) - ((∑ k ∈ Finset.range n, a k) + a n)) / ((n : ℝ) + 1) =
        C / ((n : ℝ) + 1) +
        (C * (n : ℝ) - ∑ k ∈ Finset.range n, a k) / ((n : ℝ) + 1) := by
      field_simp
      ring
    simp only [div_eq_mul_inv] at hrel hdiv ih ⊢
    simp only [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    nlinarith only [hrel, hdiv, ih]

theorem weighted_prefix_bound (a : ℕ → ℝ) (C : ℝ)
    (hprefix : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ C * n) (n : ℕ) :
    (∑ k ∈ Finset.range n, a k / (k + 1 : ℕ)) ≤
      C * ∑ k ∈ Finset.range n, (k + 1 : ℝ)⁻¹ := by
  have h := weighted_prefix_bound_aux a C hprefix n
  have hd : 0 ≤ (C * n - ∑ k ∈ Finset.range n, a k) / (n + 1 : ℕ) :=
    div_nonneg (sub_nonneg.mpr (hprefix n)) (by positivity)
  linarith

theorem sum_primesLE_eq_range_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ N.primesLE, f p) =
      ∑ k ∈ Finset.range N, if Nat.Prime (k + 1) then f (k + 1) else 0 := by
  rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter,
    ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
  simp [Nat.not_prime_zero]

theorem prime_log_div_sum_le (N : ℕ) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log 4 * (1 + Real.log N) := by
  let a : ℕ → ℝ := fun k => if Nat.Prime (k + 1) then Real.log (k + 1 : ℕ) else 0
  have hpref : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ Real.log 4 * n := by
    intro n
    have h := Chebyshev.theta_le_log4_mul_x (x := n) (Nat.cast_nonneg n)
    rw [Chebyshev.theta_eq_sum_primesLE_log, sum_primesLE_eq_range_shift] at h
    exact h
  have h := weighted_prefix_bound a (Real.log 4) hpref N
  have heq : (∑ p ∈ N.primesLE, Real.log p / p) =
      ∑ k ∈ Finset.range N, a k / (k + 1 : ℕ) := by
    rw [sum_primesLE_eq_range_shift]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [a, ite_div, zero_div]
  rw [heq]
  apply h.trans
  have hh := harmonic_le_one_add_log N
  have hH : (∑ k ∈ Finset.range N, (k + 1 : ℝ)⁻¹) = (harmonic N : ℝ) := by
    simp [harmonic]
  rw [hH]
  exact mul_le_mul_of_nonneg_left hh (Real.log_nonneg (by norm_num))

/-- A single Euler factor can be shifted to a convergent exponent at
controlled cost. No asymptotic estimate is assumed here. -/
theorem euler_factor_shift {a u : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hu : 0 ≤ u) :
    (1 - a)⁻¹ ≤ Real.exp (2 * a * u) * (1 - a * Real.exp (-u))⁻¹ := by
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hden : 0 < 1 - a := by linarith
  have hden' : 0 < 1 - a * Real.exp (-u) := by
    have := mul_le_mul_of_nonneg_left he ha
    linarith
  have hsmall := Real.add_one_le_exp (-u)
  have hbig := Real.add_one_le_exp (2 * a * u)
  have hsmall' := mul_le_mul_of_nonneg_left hsmall ha
  have hbig' := mul_le_mul_of_nonneg_left hbig hden.le
  have hrem := mul_nonneg (show 0 ≤ 1 - 2 * a by linarith) (mul_nonneg ha hu)
  have hcross : 1 - a * Real.exp (-u) ≤ Real.exp (2 * a * u) * (1 - a) := by
    nlinarith
  have hquot : 1 / (1 - a) ≤ Real.exp (2 * a * u) / (1 - a * Real.exp (-u)) :=
    (div_le_div_iff₀ hden hden').mpr (by simpa using hcross)
  simpa only [div_eq_mul_inv, one_mul] using hquot

theorem eulerProduct_shift (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    {ε : ℝ} (hε : 0 ≤ ε) :
    eulerProduct P ≤
      Real.exp (2 * ε * ∑ p ∈ P, Real.log p / p) *
        ∏ p ∈ P, (1 - (p : ℝ)⁻¹ * Real.exp (- (ε * Real.log p)))⁻¹ := by
  have hlocal (p : ℕ) (hp : p ∈ P) := hP p hp
  have h := Finset.prod_le_prod (s := P)
    (fun (p : ℕ) hp => show 0 ≤ (1 - (p : ℝ)⁻¹)⁻¹ from by
      have hi : (p : ℝ)⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀ (by exact_mod_cast (hlocal p hp).one_lt)
      exact inv_nonneg.mpr (by linarith))
    (fun p hp => euler_factor_shift
      (show 0 ≤ (p : ℝ)⁻¹ by positivity)
      (show (p : ℝ)⁻¹ ≤ 1 / 2 from by
        have htwo : (2 : ℝ) ≤ p := by exact_mod_cast (hlocal p hp).two_le
        simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) htwo)
      (show 0 ≤ ε * Real.log p from mul_nonneg hε
        (Real.log_nonneg (by exact_mod_cast (hlocal p hp).one_lt.le))))
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at h
  have hexp : (∑ p ∈ P, 2 * (p : ℝ)⁻¹ * (ε * Real.log p)) =
      2 * ε * ∑ p ∈ P, Real.log p / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [div_eq_mul_inv]
    ring
  rw [hexp] at h
  exact h

theorem shifted_reciprocal_series_bound {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - ε)) ≤ 1 + 1 / ε := by
  have hexp : -1 - ε < -1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-1 - ε)) (Set.Ici 1) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) hxy (by linarith)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-1 - ε)) 1
    (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (by have := Set.mem_Ioi.mp hx; norm_num at this; linarith) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num)] at ht
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - ε)) :=
    Real.summable_nat_rpow.mpr hexp
  have hs' : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-1 - ε)) := by
    simpa only [Function.comp_def] using hs.comp_injective
      (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  rw [hs'.tsum_eq_zero_add]
  norm_num only [Nat.zero_add, Nat.cast_one, Real.one_rpow]
  have htail : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-1 - ε)) ≤ 1 / ε := by
    simpa only [Nat.cast_one, Real.one_rpow,
      show (-1 - ε + 1 : ℝ) = -ε by ring, neg_div_neg_eq] using ht
  linarith only [htail]

noncomputable def realPowerHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ s
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

theorem shifted_primeProduct_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    {ε : ℝ} (hε : 0 < ε) :
    (∏ p ∈ P, (1 - (p : ℝ) ^ (-1 - ε))⁻¹) ≤ 1 + 1 / ε := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hlocal : ∀ {p : ℕ}, Nat.Prime p → ‖realPowerHom (-1 - ε) p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ (-1 - ε)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hprod := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := realPowerHom (-1 - ε)) hlocal P).2.tsum_eq
  simp only [Finset.filter_eq_self.mpr hP] at hprod
  have hsub : (∑' n : Nat.factoredNumbers P, (n.val : ℝ) ^ (-1 - ε)) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-1 - ε) :=
    Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-1 - ε))
      (Nat.factoredNumbers P) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hs
  have hall : (∑' n : ℕ, (n : ℝ) ^ (-1 - ε)) ≤ 1 + 1 / ε := by
    rw [hs.tsum_eq_zero_add]
    simpa [Real.zero_rpow (show (-1 - ε : ℝ) ≠ 0 by linarith)] using
      shifted_reciprocal_series_bound hε
  have heq : (∏ p ∈ P, (1 - (p : ℝ) ^ (-1 - ε))⁻¹) =
      ∑' n : Nat.factoredNumbers P, (n.val : ℝ) ^ (-1 - ε) := hprod.symm
  rw [heq]
  exact hsub.trans hall

theorem shifted_power_identity {x : ℝ} (hx : 0 < x) (ε : ℝ) :
    x ^ (-1 - ε) = x⁻¹ * Real.exp (-(ε * Real.log x)) := by
  rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_neg_one, Real.rpow_def_of_pos hx]
  congr 2
  ring

theorem eulerProduct_upper (N : ℕ) (hN : 1 ≤ N) :
    eulerProduct N.primesLE ≤ 16 * (2 + Real.log N) := by
  let ε : ℝ := (1 + Real.log N)⁻¹
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hden : 0 < 1 + Real.log N := by linarith
  have hε : 0 < ε := inv_pos.mpr hden
  have hP : ∀ p ∈ N.primesLE, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hshift := eulerProduct_shift N.primesLE hP hε.le
  have hid : ∀ p ∈ N.primesLE,
      (p : ℝ)⁻¹ * Real.exp (-(ε * Real.log p)) = (p : ℝ) ^ (-1 - ε) := by
    intro p hp
    exact (shifted_power_identity (by exact_mod_cast (hP p hp).pos) ε).symm
  have hprodEq :
      (∏ p ∈ N.primesLE, (1 - (p : ℝ)⁻¹ * Real.exp (-(ε * Real.log p)))⁻¹) =
      ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-1 - ε))⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [hid p hp]
  rw [hprodEq] at hshift
  have hprod := shifted_primeProduct_bound N.primesLE hP hε
  have hcost : Real.exp (2 * ε * ∑ p ∈ N.primesLE, Real.log p / p) ≤ 16 := by
    have hbound := mul_le_mul_of_nonneg_left (prime_log_div_sum_le N)
      (show 0 ≤ 2 * ε by positivity)
    have hcancel : 2 * ε * (Real.log 4 * (1 + Real.log N)) = 2 * Real.log 4 := by
      dsimp [ε]
      field_simp
    rw [hcancel] at hbound
    have he := Real.exp_le_exp.mpr hbound
    have hexact : Real.exp (2 * Real.log 4) = (16 : ℝ) := by
      rw [show (2 : ℝ) * Real.log 4 = Real.log 4 + Real.log 4 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    rwa [hexact] at he
  have hprod0 : 0 ≤ ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-1 - ε))⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    apply inv_nonneg.mpr
    have hr := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (hP p hp).one_lt : (1 : ℝ) < p)
      (show -1 - ε < 0 by linarith)
    linarith
  have h := hshift.trans (mul_le_mul hcost hprod hprod0 (by norm_num : (0 : ℝ) ≤ 16))
  simp only [ε, one_div, inv_inv] at h
  linarith

theorem rough_harmonic_bound (D r : ℕ) (hD : 1 ≤ D) (hr : 2 ≤ r)
    (hrD : r ≤ D + 1) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ D ∧ ∀ p ∈ n.primeFactorsList, r ≤ p) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 16 * (2 + Real.log D) / Real.log r := by
  have h := rough_reciprocal_sum_le D r hr hrD S hS
  apply h.trans
  exact div_le_div_of_nonneg_right (eulerProduct_upper D hD)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega)))

theorem prime_reciprocal_sum_le_log (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, (p : ℝ)⁻¹) ≤ Real.log (16 * (2 + Real.log N)) := by
  have hterm : ∀ p ∈ N.primesLE,
      Real.exp ((p : ℝ)⁻¹) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hi : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast hprime.one_lt)
    have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
    have he : 1 - (p : ℝ)⁻¹ ≤ Real.exp (-(p : ℝ)⁻¹) := by
      linarith [Real.add_one_le_exp (-(p : ℝ)⁻¹)]
    have h := inv_anti₀ hden he
    simpa only [Real.exp_neg, inv_inv] using h
  have hprod := Finset.prod_le_prod (s := N.primesLE)
    (fun (p : ℕ) _hp => (Real.exp_pos ((p : ℝ)⁻¹)).le) hterm
  rw [← Real.exp_sum] at hprod
  have hbound := hprod.trans (eulerProduct_upper N hN)
  have hlog := Real.log_le_log (Real.exp_pos _) hbound
  simpa only [Real.log_exp] using hlog

/-- Removing the least prime from a nonsquarefree integer leaves either
another copy of that prime or a square of a strictly larger prime. -/
theorem nonsquarefree_cofactor_cases {r k : ℕ} (hr : Nat.Prime r)
    (hmin : ∀ p : ℕ, Nat.Prime p → p ∣ r * k → r ≤ p)
    (hns : ¬ Squarefree (r * k)) :
    r ∣ k ∨ ∃ p : ℕ, Nat.Prime p ∧ r < p ∧ p * p ∣ k := by
  have hsq := Nat.squarefree_iff_prime_squarefree (n := r * k)
  have hex : ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ r * k := by
    by_contra h
    apply hns
    apply hsq.mpr
    intro p hp hdiv
    exact h ⟨p, hp, hdiv⟩
  obtain ⟨p, hp, hdiv⟩ := hex
  by_cases hpr : p = r
  · subst p
    left
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨t, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hr.pos
    simpa only [Nat.mul_assoc] using ht
  · right
    have hpd : p ∣ r * k := (dvd_mul_right p p).trans hdiv
    have hle := hmin p hp hpd
    have hc : Nat.Coprime (p * p) r := by
      simpa only [pow_two] using ((Nat.coprime_primes hp hr).mpr hpr).pow_left 2
    exact ⟨p, hp, lt_of_le_of_ne hle (Ne.symm hpr), hc.dvd_of_dvd_mul_left hdiv⟩

/-- Discrete Abel domination for any nonnegative decreasing weight. -/
theorem antitone_weighted_prefix_aux (a w : ℕ → ℝ) (C : ℝ)
    (hprefix : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ C * n)
    (hw : Antitone w) (n : ℕ) :
    (∑ k ∈ Finset.range n, a k * w k) +
      (C * n - ∑ k ∈ Finset.range n, a k) * w n ≤
      C * ∑ k ∈ Finset.range n, w k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : 0 ≤ C * (n + 1 : ℕ) - ∑ k ∈ Finset.range (n + 1), a k :=
      sub_nonneg.mpr (hprefix (n + 1))
    have hm := mul_le_mul_of_nonneg_left (hw (Nat.le_succ n)) hd
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at hm ⊢
    nlinarith only [ih, hm]

theorem antitone_weighted_prefix (a w : ℕ → ℝ) (C : ℝ)
    (hprefix : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ C * n)
    (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) (n : ℕ) :
    (∑ k ∈ Finset.range n, a k * w k) ≤ C * ∑ k ∈ Finset.range n, w k := by
  have h := antitone_weighted_prefix_aux a w C hprefix hw n
  have hd := mul_nonneg (sub_nonneg.mpr (hprefix n)) (hw0 n)
  linarith

noncomputable def massHom : Multiset ℕ →+ ℝ where
  toFun := mass
  map_zero' := mass_zero
  map_add' := mass_add

theorem mass_eq_sum_counts (A : Multiset ℕ) :
    mass A = ∑ n ∈ A.toFinset, (A.count n : ℝ) / n := by
  have h := congrArg massHom (Multiset.toFinset_sum_count_nsmul_eq A)
  simp only [map_sum, map_nsmul, nsmul_eq_mul] at h
  change (∑ n ∈ A.toFinset, (A.count n : ℝ) * mass {n}) = mass A at h
  simpa [mass, div_eq_mul_inv] using h.symm

/-- Stability provides the pointwise multiplicity budget used by the
least-prime decomposition. No occurrence is discarded in this bound. -/
theorem stable_mass_le_minFac_sum (A : Multiset ℕ) (hA : stable A) :
    mass A ≤ ∑ n ∈ A.toFinset, (n.minFac : ℝ) / n := by
  rw [mass_eq_sum_counts]
  apply Finset.sum_le_sum
  intro n hn
  have hc := (hA.2 n (Multiset.mem_toFinset.mp hn)).le
  apply div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg n)

noncomputable def logWeight (x : ℝ) : ℝ :=
  (max 2 x)⁻¹ / (Real.log (max 2 x)) ^ 2

theorem logWeight_nonneg (x : ℝ) : 0 ≤ logWeight x := by
  unfold logWeight
  positivity

theorem logWeight_antitone : Antitone logWeight := by
  intro x y hxy
  have hx : (0 : ℝ) < max 2 x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm : max 2 x ≤ max 2 y := max_le_max_left 2 hxy
  have hl : Real.log (max 2 x) ≤ Real.log (max 2 y) := Real.log_le_log hx hm
  have hl0 : 0 < Real.log (max 2 x) := Real.log_pos (by linarith [le_max_left (2 : ℝ) x])
  have hsq : (Real.log (max 2 x)) ^ 2 ≤ (Real.log (max 2 y)) ^ 2 := by nlinarith
  unfold logWeight
  simp only [div_eq_mul_inv]
  exact mul_le_mul (inv_anti₀ hx hm) (inv_anti₀ (sq_pos_of_pos hl0) hsq)
    (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr hx.le)

theorem logWeight_summable : Summable (fun n : ℕ => logWeight n) := by
  have hi : MeasureTheory.IntegrableOn logWeight (Set.Ioi (2 : ℝ)) := by
    apply (integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 2)).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp only [logWeight, max_eq_right (Set.mem_Ioi.mp hx).le]
  exact AntitoneOn.summable_of_integrableOn_Ioi (N := 2)
    (by simpa using logWeight_antitone.antitoneOn (s := Set.Ici (2 : ℝ)))
    (by simpa using hi) (fun x _ => logWeight_nonneg x)

theorem prime_log_reciprocal_sum_bound (N : ℕ) :
    (∑ p ∈ N.primesLE, 1 / ((p : ℝ) * Real.log p)) ≤
      Real.log 4 * ∑' n : ℕ, logWeight n := by
  let a : ℕ → ℝ := fun n => if Nat.Prime n then Real.log n else 0
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · rfl
  have hpref : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ Real.log 4 * n := by
    intro n
    have hc := Chebyshev.theta_le_log4_mul_x (x := n) (Nat.cast_nonneg n)
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter,
      ← Nat.range_succ_eq_Icc_zero] at hc
    have hsub : (∑ k ∈ Finset.range n, a k) ≤ ∑ k ∈ Finset.range (n + 1), a k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
        (fun k _ _ => ha k)
    exact hsub.trans hc
  have hw : Antitone (fun n : ℕ => logWeight n) := by
    intro m n hmn
    exact logWeight_antitone (by exact_mod_cast hmn)
  have h := antitone_weighted_prefix a (fun n => logWeight n) (Real.log 4)
    hpref hw (fun n => logWeight_nonneg n) (N + 1)
  have heq : (∑ p ∈ N.primesLE, 1 / ((p : ℝ) * Real.log p)) =
      ∑ k ∈ Finset.range (N + 1), a k * logWeight k := by
    rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter,
      ← Nat.range_succ_eq_Icc_zero]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : Nat.Prime p
    · have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
      have hlog0 : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hprime.one_lt))
      simp only [a, hprime, if_pos, logWeight, max_eq_right htwo]
      field_simp
    · simp [a, hprime]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_left
    (logWeight_summable.sum_le_tsum (Finset.range (N + 1)) (fun n _ => logWeight_nonneg n))
    (Real.log_nonneg (by norm_num)))

theorem reciprocal_square_tail (r : ℕ) (hr : 0 < r) :
    (∑' n : ℕ, ((n + r + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) ≤ (r : ℝ)⁻¹ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ha : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ici (r : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hrR.trans_le hx) hxy (by norm_num)
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-2 : ℝ)) r ha
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hrR)
    (fun x hx => Real.rpow_nonneg (hrR.trans (Set.mem_Ioi.mp hx)).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hrR] at h
  norm_num at h
  simpa [Real.rpow_neg_one] using h

theorem finite_reciprocal_square_tail (r : ℕ) (hr : 0 < r) (S : Finset ℕ)
    (hS : ∀ n ∈ S, r < n) :
    (∑ n ∈ S, (n : ℝ)⁻¹ ^ 2) ≤ (r : ℝ)⁻¹ := by
  let g : ℕ → ℕ := fun n => n - (r + 1)
  have hrestore : ∀ n ∈ S, g n + r + 1 = n := by
    intro n hn
    have := hS n hn
    dsimp [g]
    omega
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    have := hrestore a ha
    have := hrestore b hb
    omega
  have hs : Summable (fun n : ℕ => ((n + r + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    have hbase := Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    simpa only [Function.comp_def] using hbase.comp_injective
      (show Function.Injective (fun n : ℕ => n + r + 1) by
        intro a b h
        change a + r + 1 = b + r + 1 at h
        omega)
  have hfinite := hs.sum_le_tsum (S.image g)
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Finset.sum_image hinj] at hfinite
  have heq : (∑ n ∈ S, ((g n + r + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) =
      ∑ n ∈ S, (n : ℝ)⁻¹ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hrestore n hn]
    simp [inv_pow]
  rw [heq] at hfinite
  exact hfinite.trans (reciprocal_square_tail r hr)

theorem reciprocal_sum_divisible (a : ℕ) (S : Finset ℕ)
    (hdiv : ∀ n ∈ S, a ∣ n) :
    (∑ n ∈ S, (n : ℝ)⁻¹) =
      (a : ℝ)⁻¹ * ∑ k ∈ S.image (fun n => n / a), (k : ℝ)⁻¹ := by
  have hinj : Set.InjOn (fun n => n / a) S := by
    intro m hm n hn heq
    have hm' := Nat.mul_div_cancel' (hdiv m hm)
    have hn' := Nat.mul_div_cancel' (hdiv n hn)
    calc
      m = a * (m / a) := hm'.symm
      _ = a * (n / a) := congrArg (fun k => a * k) heq
      _ = n := hn'
  rw [Finset.sum_image hinj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h := congrArg (fun m : ℕ => (m : ℝ)⁻¹) (Nat.mul_div_cancel' (hdiv n hn))
  simpa only [Nat.cast_mul, mul_inv_rev, mul_comm] using h.symm

theorem divisible_rough_harmonic_bound (D r a : ℕ) (hD : 1 ≤ D)
    (hr : 2 ≤ r) (hrD : r ≤ D + 1) (ha : 0 < a) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ D ∧ ∀ p ∈ n.primeFactorsList, r ≤ p)
    (hdiv : ∀ n ∈ S, a ∣ n) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      (a : ℝ)⁻¹ * (16 * (2 + Real.log D) / Real.log r) := by
  rw [reciprocal_sum_divisible a S hdiv]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg a))
  apply rough_harmonic_bound D r hD hr hrD
  intro k hk
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hn0, hnD, hnrough⟩ := hS n hn
  have hd := hdiv n hn
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn0 hd) ha, (Nat.div_le_self n a).trans hnD, ?_⟩
  intro p hp
  have hp' := Nat.mem_primeFactorsList'.mp hp
  have hpn : p ∣ n := hp'.2.1.trans (Nat.div_dvd_of_dvd hd)
  exact hnrough p (Nat.mem_primeFactorsList'.mpr ⟨hp'.1, hpn, by omega⟩)

theorem finite_weighted_cover {ι : Type*} (I : Finset ι) (S : Finset ℕ)
    (f : ℕ → ℝ) (E₀ : ℕ → Prop) (E : ι → ℕ → Prop)
    [DecidablePred E₀] [∀ i, DecidablePred (E i)]
    (hf : ∀ n ∈ S, 0 ≤ f n)
    (hcover : ∀ n ∈ S, E₀ n ∨ ∃ i ∈ I, E i n) :
    (∑ n ∈ S, f n) ≤ (∑ n ∈ S with E₀ n, f n) +
      ∑ i ∈ I, ∑ n ∈ S with E i n, f n := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnon : ∀ i ∈ I, 0 ≤ (if E i n then f n else 0) := by
    intro i hi
    split_ifs <;> first | exact hf n hn | rfl
  have hsum0 := Finset.sum_nonneg hnon
  rcases hcover n hn with h₀ | ⟨i, hi, hE⟩
  · simp only [if_pos h₀]
    linarith
  · have hsingle := Finset.single_le_sum hnon hi
    rw [if_pos hE] at hsingle
    have hfirst : 0 ≤ (if E₀ n then f n else 0) := by
      split_ifs <;> first | exact hf n hn | rfl
    linarith

theorem rough_repeated_prime_union_bound (D r : ℕ) (hD : 1 ≤ D)
    (hr : 2 ≤ r) (hrD : r ≤ D + 1) (S P : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ D ∧ ∀ p ∈ n.primeFactorsList, r ≤ p)
    (hP : ∀ p ∈ P, r < p)
    (hcover : ∀ n ∈ S, r ∣ n ∨ ∃ p ∈ P, p * p ∣ n) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      2 * (r : ℝ)⁻¹ * (16 * (2 + Real.log D) / Real.log r) := by
  let H := 16 * (2 + Real.log D) / Real.log r
  have hH : 0 ≤ H := by
    have hdlog := Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD)
    have hrlog := Real.log_nonneg (show (1 : ℝ) ≤ r by exact_mod_cast (show 1 ≤ r by omega))
    dsimp [H]
    positivity
  have hbase := divisible_rough_harmonic_bound D r r hD hr hrD (by omega)
    (S.filter (fun n => r ∣ n))
    (fun n hn => hS n (Finset.mem_filter.mp hn).1)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  have hpieces : ∀ p ∈ P,
      (∑ n ∈ S with p * p ∣ n, (n : ℝ)⁻¹) ≤ (p : ℝ)⁻¹ ^ 2 * H := by
    intro p hp
    have hp0 : 0 < p := by have := hP p hp; omega
    have h := divisible_rough_harmonic_bound D r (p * p) hD hr hrD
      (Nat.mul_pos hp0 hp0) (S.filter (fun n => p * p ∣ n))
      (fun n hn => hS n (Finset.mem_filter.mp hn).1)
      (fun n hn => (Finset.mem_filter.mp hn).2)
    simpa only [Nat.cast_mul, mul_inv_rev, pow_two] using h
  have hc := finite_weighted_cover P S (fun n => (n : ℝ)⁻¹)
    (fun n => r ∣ n) (fun p n => p * p ∣ n) (fun n _ => by positivity) hcover
  have hpSum := Finset.sum_le_sum hpieces
  rw [← Finset.sum_mul] at hpSum
  have htail := finite_reciprocal_square_tail r (by omega) P hP
  have htailH := mul_le_mul_of_nonneg_right htail hH
  change (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 2 * (r : ℝ)⁻¹ * H
  linarith

theorem nonsquarefree_minFac_block_bound (D r : ℕ) (hD : 1 ≤ D)
    (hr : Nat.Prime r) (hrD : r ≤ D) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n ∧ n ≤ D ∧ n.minFac = r ∧ ¬ Squarefree n) :
    (∑ n ∈ S, (r : ℝ) / n) ≤
      2 * (r : ℝ)⁻¹ * (16 * (2 + Real.log D) / Real.log r) := by
  let K := S.image (fun n => n / r)
  let P := D.primesLE.filter (fun p => r < p)
  have hdiv : ∀ n ∈ S, r ∣ n := by
    intro n hn
    rw [← (hS n hn).2.2.1]
    exact Nat.minFac_dvd n
  have hK : ∀ k ∈ K, 0 < k ∧ k ≤ D ∧ ∀ p ∈ k.primeFactorsList, r ≤ p := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hn2, hnD, hnmin, _⟩ := hS n hn
    have hn0 : 0 < n := by omega
    refine ⟨Nat.div_pos (Nat.le_of_dvd hn0 (hdiv n hn)) hr.pos,
      (Nat.div_le_self n r).trans hnD, ?_⟩
    intro p hp
    have hp' := Nat.mem_primeFactorsList'.mp hp
    rw [← hnmin]
    exact Nat.minFac_le_of_dvd hp'.1.two_le
      (hp'.2.1.trans (Nat.div_dvd_of_dvd (hdiv n hn)))
  have hcover : ∀ k ∈ K, r ∣ k ∨ ∃ p ∈ P, p * p ∣ k := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hn2, hnD, hnmin, hnns⟩ := hS n hn
    have heq := Nat.mul_div_cancel' (hdiv n hn)
    have hcases := nonsquarefree_cofactor_cases hr
      (fun p hp hpn => by
        rw [heq] at hpn
        rw [← hnmin]
        exact Nat.minFac_le_of_dvd hp.two_le hpn)
      (by rwa [heq])
    rcases hcases with h | ⟨p, hp, hrp, hpp⟩
    · exact Or.inl h
    · right
      have hk0 : 0 < n / r := Nat.div_pos (Nat.le_of_dvd (by omega) (hdiv n hn)) hr.pos
      have hpk : p ≤ n / r := Nat.le_of_dvd hk0 ((dvd_mul_right p p).trans hpp)
      refine ⟨p, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, hp⟩, hrp⟩, hpp⟩
      exact hpk.trans ((Nat.div_le_self n r).trans hnD)
  have hbound := rough_repeated_prime_union_bound D r hD hr.two_le (by omega) K P hK
    (fun p hp => (Finset.mem_filter.mp hp).2) hcover
  have heq : (∑ n ∈ S, (r : ℝ) / n) = ∑ k ∈ K, (k : ℝ)⁻¹ := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum, reciprocal_sum_divisible r S hdiv, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast hr.ne_zero : (r : ℝ) ≠ 0), one_mul]
  rwa [heq]

theorem nonsquarefree_distinct_budget (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n ∧ n ≤ D ∧ ¬ Squarefree n) :
    (∑ n ∈ S, (n.minFac : ℝ) / n) ≤
      32 * (2 + Real.log D) * (Real.log 4 * ∑' n : ℕ, logWeight n) := by
  have heq : (∑ n ∈ S, (n.minFac : ℝ) / n) =
      ∑ r ∈ D.primesLE, ∑ n ∈ S with n.minFac = r, (r : ℝ) / n := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn2, hnD, _⟩ := hS n hn
    have hmem : n.minFac ∈ D.primesLE := Nat.mem_primesLE.mpr
      ⟨(Nat.minFac_le (by omega)).trans hnD, Nat.minFac_prime (by omega)⟩
    simp only [Finset.sum_ite_eq, if_pos hmem]
  rw [heq]
  have hblocks : ∀ r ∈ D.primesLE,
      (∑ n ∈ S with n.minFac = r, (r : ℝ) / n) ≤
      2 * (r : ℝ)⁻¹ * (16 * (2 + Real.log D) / Real.log r) := by
    intro r hr
    have hr' := Nat.mem_primesLE.mp hr
    apply nonsquarefree_minFac_block_bound D r hD hr'.2 hr'.1
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨hn2, hnD, hnns⟩ := hS n hn'.1
    exact ⟨hn2, hnD, hn'.2, hnns⟩
  have hs := Finset.sum_le_sum hblocks
  have hfactor : (∑ r ∈ D.primesLE,
      2 * (r : ℝ)⁻¹ * (16 * (2 + Real.log D) / Real.log r)) =
      32 * (2 + Real.log D) * ∑ r ∈ D.primesLE, 1 / ((r : ℝ) * Real.log r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hfactor] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left (prime_log_reciprocal_sum_bound D)
  have := Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD)
  positivity

theorem stable_nonsquarefree_mass_bound (A : Multiset ℕ) (hA : stable A)
    (D : ℕ) (hD : 1 ≤ D) (hsupport : ∀ n ∈ A, n ≤ D) :
    mass (A.filter (fun n => ¬ Squarefree n)) ≤
      32 * (2 + Real.log D) * (Real.log 4 * ∑' n : ℕ, logWeight n) := by
  let B := A.filter (fun n => ¬ Squarefree n)
  have hBA : B ≤ A := Multiset.filter_le _ _
  have hB := stable_submultiset hA hBA
  apply (stable_mass_le_minFac_sum B hB).trans
  apply nonsquarefree_distinct_budget D hD
  intro n hn
  have hnB := Multiset.mem_toFinset.mp hn
  have hnA := Multiset.mem_of_le hBA hnB
  exact ⟨hA.1 n hnA, hsupport n hnA, (Multiset.mem_filter.mp hnB).2⟩

theorem selected_prime_exists (P : Finset ℕ) {n : ℕ}
    (hcount : 0 < selectedFactorCount P n) :
    ∃ p ∈ P, Nat.Prime p ∧ p ∣ n := by
  have hn : (n.primeFactorsList.filter (fun p => p ∈ P)).length ≠ 0 :=
    Nat.ne_of_gt hcount
  have hne : n.primeFactorsList.filter (fun p => p ∈ P) ≠ [] := by
    intro h
    simp [h] at hn
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hp' := List.mem_filter.mp hp
  have hfac := Nat.mem_primeFactorsList'.mp hp'.1
  exact ⟨p, of_decide_eq_true hp'.2, hfac.1, hfac.2.1⟩

theorem selectedFactorCount_div_prime (P : Finset ℕ) {p n : ℕ}
    (hp : Nat.Prime p) (hpP : p ∈ P) (hn : 0 < n) (hpn : p ∣ n) :
    selectedFactorCount P n = 1 + selectedFactorCount P (n / p) := by
  have hq : n / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
  have h := selectedFactorCount_prime_mul P hp hpP hq
  rwa [Nat.mul_div_cancel' hpn] at h

theorem selected_cofactor_nontrivial (P : Finset ℕ) {p n : ℕ}
    (hp : Nat.Prime p) (hpP : p ∈ P) (hn : 0 < n) (hpn : p ∣ n)
    (hcount : 2 ≤ selectedFactorCount P n) : 2 ≤ n / p := by
  have hq := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hrec := selectedFactorCount_div_prime P hp hpP hn hpn
  by_contra h
  have heq : n / p = 1 := by omega
  rw [heq, show selectedFactorCount P 1 = 0 by simp [selectedFactorCount]] at hrec
  omega

theorem one_sub_sum_le_product (P : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ p ∈ P, 0 ≤ a p ∧ a p ≤ 1) :
    1 - ∑ p ∈ P, a p ≤ ∏ p ∈ P, (1 - a p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hp' := ha p (Finset.mem_insert_self p P)
    have haP : ∀ q ∈ P, 0 ≤ a q ∧ a q ≤ 1 :=
      fun q hq => ha q (Finset.mem_insert_of_mem hq)
    have hih := ih haP
    have hs := Finset.sum_nonneg (fun q hq => (haP q hq).1)
    have hm := mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hp'.2)
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    nlinarith

theorem eulerProduct_le_geometric (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hσ : (∑ p ∈ P, (p : ℝ)⁻¹) < 1) :
    eulerProduct P ≤ (1 - ∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ := by
  have h := one_sub_sum_le_product P (fun p => (p : ℝ)⁻¹) (by
    intro p hp
    refine ⟨by positivity, ?_⟩
    exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hP p hp).one_lt)).le)
  have hi := inv_anti₀ (show 0 < 1 - ∑ p ∈ P, (p : ℝ)⁻¹ by linarith) h
  simpa only [eulerProduct, Finset.prod_inv_distrib] using hi

/-- Each additional selected-prime factor saves a factor of sigma in a
distinct reciprocal sum. Divisibility covers may overlap. -/
theorem selected_depth_sum_bound (P U : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hU : ∀ p ∈ U, Nat.Prime p)
    (k : ℕ) (S : Finset ℕ)
    (hsupport : ∀ n ∈ S, n ∈ Nat.factoredNumbers U)
    (hcount : ∀ n ∈ S, k ≤ selectedFactorCount P n) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ k * eulerProduct U := by
  induction k generalizing S with
  | zero => simpa using reciprocal_sum_le_primeProduct U S hU hsupport
  | succ k ih =>
    have hcover : ∀ n ∈ S, False ∨ ∃ p ∈ P, p ∣ n := by
      intro n hn
      obtain ⟨p, hp, _, hpn⟩ := selected_prime_exists P (n := n) (by have := hcount n hn; omega)
      exact Or.inr ⟨p, hp, hpn⟩
    have hc := finite_weighted_cover P S (fun n => (n : ℝ)⁻¹)
      (fun _ => False) (fun p n => p ∣ n) (fun n _ => by positivity) hcover
    simp only [Finset.filter_false, Finset.sum_empty, zero_add] at hc
    have hpieces : ∀ p ∈ P,
        (∑ n ∈ S with p ∣ n, (n : ℝ)⁻¹) ≤
        (p : ℝ)⁻¹ * ((∑ q ∈ P, (q : ℝ)⁻¹) ^ k * eulerProduct U) := by
      intro p hp
      let T := S.filter (fun n => p ∣ n)
      have hd : ∀ n ∈ T, p ∣ n := fun n hn => (Finset.mem_filter.mp hn).2
      rw [reciprocal_sum_divisible p T hd]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg p))
      apply ih
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        exact Nat.mem_factoredNumbers_of_dvd (hsupport n (Finset.mem_filter.mp hn).1)
          (Nat.div_dvd_of_dvd (hd n hn))
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have hnS := (Finset.mem_filter.mp hn).1
        have hn0 : 0 < n := Nat.pos_of_ne_zero (Nat.mem_factoredNumbers.mp (hsupport n hnS)).1
        have hrec := selectedFactorCount_div_prime P (hP p hp) hp hn0 (hd n hn)
        have := hcount n hnS
        omega
    have hs := hc.trans (Finset.sum_le_sum hpieces)
    rw [← Finset.sum_mul] at hs
    calc
      _ ≤ (∑ p ∈ P, (p : ℝ)⁻¹) * ((∑ p ∈ P, (p : ℝ)⁻¹) ^ k * eulerProduct U) := hs
      _ = _ := by rw [pow_succ]; ring

theorem selected_background_depth_bound (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (hdisj : Disjoint P Q) (hσ : (∑ p ∈ P, (p : ℝ)⁻¹) < 1)
    (k : ℕ) (S : Finset ℕ)
    (hsupport : ∀ n ∈ S, n ∈ Nat.factoredNumbers (P ∪ Q))
    (hcount : ∀ n ∈ S, k ≤ selectedFactorCount P n) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      eulerProduct Q * (∑ p ∈ P, (p : ℝ)⁻¹) ^ k /
        (1 - ∑ p ∈ P, (p : ℝ)⁻¹) := by
  have hU : ∀ p ∈ P ∪ Q, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hQ p hp
  have h := selected_depth_sum_bound P (P ∪ Q) hP hU k S hsupport hcount
  have hprod : eulerProduct (P ∪ Q) = eulerProduct P * eulerProduct Q :=
    Finset.prod_union hdisj
  rw [hprod] at h
  have hb := mul_le_mul_of_nonneg_right (eulerProduct_le_geometric P hP hσ)
    (eulerProduct_pos Q hQ).le
  have hb' := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (∑ p ∈ P, (p : ℝ)⁻¹) ^ k by positivity)
  apply (h.trans hb').trans_eq
  simp only [div_eq_mul_inv]
  ring

/-- Even a noninjective label map lifts submultisets occurrence-for-occurrence. -/
theorem submultiset_map_lift {α β : Type*} (f : α → β)
    (A : Multiset α) (B : Multiset β) (hB : B ≤ A.map f) :
    ∃ S : Multiset α, S ≤ A ∧ S.map f = B := by
  have hm : B ∈ (A.map f).powersetCard B.card :=
    Multiset.mem_powersetCard.mpr ⟨hB, rfl⟩
  rw [Multiset.powersetCard_map] at hm
  obtain ⟨S, hS, heq⟩ := Multiset.mem_map.mp hm
  exact ⟨S, (Multiset.mem_powersetCard.mp hS).1, heq⟩

theorem join_mono {A B : Multiset (Multiset ℕ)} (hAB : A ≤ B) :
    A.join ≤ B.join := by
  have h := Multiset.sub_add_cancel hAB
  have hj := congrArg Multiset.join h
  rw [Multiset.join_add] at hj
  rw [← hj]
  exact Multiset.le_add_left _ _

theorem labeled_bundle_mass_bounds (B : Multiset (ℕ × Multiset ℕ)) (δ : ℝ)
    (hB : ∀ b ∈ B, (1 - δ) * (b.1 : ℝ)⁻¹ ≤ mass b.2 ∧
      mass b.2 ≤ (b.1 : ℝ)⁻¹) :
    (1 - δ) * mass (B.map Prod.fst) ≤ mass (B.map Prod.snd).join ∧
      mass (B.map Prod.snd).join ≤ mass (B.map Prod.fst) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    have hb := hB b (Multiset.mem_cons_self b B)
    have hi := ih (fun c hc => hB c (Multiset.mem_cons_of_mem hc))
    simp only [Multiset.map_cons, Multiset.join_cons, mass_add, mass_cons]
    constructor <;> nlinarith [hb.1, hb.2, hi.1, hi.2]

/-- Approximation in the ideal prime inventory lifts to a genuine original
submultiset with error epsilon+delta, independent of the number of bundles. -/
theorem lift_labeled_bundles (A : Multiset ℕ) (B : Multiset (ℕ × Multiset ℕ))
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hinventory : (B.map Prod.snd).join ≤ A)
    (hB : ∀ b ∈ B, (1 - δ) * (b.1 : ℝ)⁻¹ ≤ mass b.2 ∧
      mass b.2 ≤ (b.1 : ℝ)⁻¹)
    (happrox : approximates (B.map Prod.fst) ε) : approximates A (ε + δ) := by
  obtain ⟨C, hC, hlo, hhi⟩ := happrox
  obtain ⟨S, hS, hmap⟩ := submultiset_map_lift Prod.fst B C hC
  have hb := labeled_bundle_mass_bounds S δ
    (fun b hb => hB b (Multiset.mem_of_le hS hb))
  rw [hmap] at hb
  refine ⟨(S.map Prod.snd).join,
    (join_mono (Multiset.map_le_map hS)).trans hinventory, ?_, hb.2.trans hhi⟩
  have he := mul_le_mul_of_nonneg_left hhi hδ
  nlinarith [hb.1]

noncomputable def selectedLabel (P : Finset ℕ) (n : ℕ) : ℕ :=
  if h : 0 < selectedFactorCount P n then Classical.choose (selected_prime_exists P h) else 0

theorem selectedLabel_spec (P : Finset ℕ) {n : ℕ} (hn : 0 < selectedFactorCount P n) :
    selectedLabel P n ∈ P ∧ Nat.Prime (selectedLabel P n) ∧ selectedLabel P n ∣ n := by
  simp only [selectedLabel, dif_pos hn]
  exact Classical.choose_spec (selected_prime_exists P hn)

theorem multiset_label_partition (A : Multiset ℕ) (P : Finset ℕ) (label : ℕ → ℕ)
    (hlabel : ∀ n ∈ A, label n ∈ P) :
    (∑ p ∈ P, A.filter (fun n => label n = p)) = A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons n A ih =>
    have hn := hlabel n (Multiset.mem_cons_self n A)
    have hA := ih (fun m hm => hlabel m (Multiset.mem_cons_of_mem hm))
    simp_rw [Multiset.filter_cons]
    rw [Finset.sum_add_distrib, hA, Finset.sum_ite_eq, if_pos hn]
    simp

noncomputable def primeBlock (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ) : Multiset ℕ :=
  A.filter (fun n => selectedLabel P n = q)

theorem primeBlock_partition (P : Finset ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n) :
    (∑ q ∈ P, primeBlock P q A) = A :=
  multiset_label_partition A P (selectedLabel P)
    (fun n hn => (selectedLabel_spec P (hcount n hn)).1)

theorem primeBlock_divisible (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n) :
    ∀ n ∈ primeBlock P q A, q ∣ n := by
  intro n hn
  have hn' := Multiset.mem_filter.mp hn
  have hspec := selectedLabel_spec P (hcount n hn'.1)
  rw [hn'.2] at hspec
  exact hspec.2.2

noncomputable def cofactorBlock (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ) : Multiset ℕ :=
  (primeBlock P q A).map (fun n => n / q)

theorem cofactorBlock_reconstruct (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n) :
    (cofactorBlock P q A).map (fun n => q * n) = primeBlock P q A := by
  unfold cofactorBlock
  rw [Multiset.map_map]
  calc
    _ = (primeBlock P q A).map id := Multiset.map_congr rfl (by
      intro n hn
      exact Nat.mul_div_cancel' (primeBlock_divisible P q A hcount n hn))
    _ = _ := Multiset.map_id _

theorem cofactorBlock_stable (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hq : Nat.Prime q) (hqP : q ∈ P) (hA : stable A)
    (hcount : ∀ n ∈ A, 2 ≤ selectedFactorCount P n) :
    stable (cofactorBlock P q A) := by
  have hc : ∀ n ∈ A, 0 < selectedFactorCount P n := fun n hn => lt_of_lt_of_le (by omega) (hcount n hn)
  apply stable_cofactors q _ hq.pos
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hk
    have hnA := (Multiset.mem_filter.mp hn).1
    exact selected_cofactor_nontrivial P hq hqP (stable_positive hA n hnA)
      (primeBlock_divisible P q A hc n hn) (hcount n hnA)
  · rw [cofactorBlock_reconstruct P q A hc]
    exact stable_submultiset hA (Multiset.filter_le _ _)

theorem cofactorBlock_mass (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n) :
    mass (primeBlock P q A) = (q : ℝ)⁻¹ * mass (cofactorBlock P q A) := by
  rw [← mass_scale, cofactorBlock_reconstruct P q A hcount]

theorem cofactorBlock_count_lt (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hq : Nat.Prime q) (hA : stable A)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n)
    {k : ℕ} (hk : k ∈ cofactorBlock P q A) :
    (cofactorBlock P q A).count k < q := by
  have hinj : Function.Injective (fun n : ℕ => q * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hq.pos hab
  have hs := stable_submultiset hA (Multiset.filter_le (fun n => selectedLabel P n = q) A)
  have hm : q * k ∈ (cofactorBlock P q A).map (fun n => q * n) :=
    Multiset.mem_map.mpr ⟨k, hk, rfl⟩
  rw [cofactorBlock_reconstruct P q A hcount] at hm
  have hc := hs.2 (q * k) hm
  change (primeBlock P q A).count (q * k) < (q * k).minFac at hc
  rw [← cofactorBlock_reconstruct P q A hcount,
    Multiset.count_map_eq_count' _ _ hinj] at hc
  exact hc.trans_le (Nat.minFac_le_of_dvd hq.two_le (dvd_mul_right q k))

theorem cofactorBlock_depth (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hq : Nat.Prime q) (hqP : q ∈ P) (hA : positive A) (t : ℕ)
    (hcount : ∀ n ∈ A, t + 1 ≤ selectedFactorCount P n) :
    ∀ k ∈ cofactorBlock P q A, t ≤ selectedFactorCount P k := by
  intro k hk
  obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hk
  have hnA := (Multiset.mem_filter.mp hn).1
  have hc : ∀ n ∈ A, 0 < selectedFactorCount P n := by
    intro n hn
    have := hcount n hn
    omega
  have hd := primeBlock_divisible P q A hc n hn
  have he := selectedFactorCount_div_prime P hq hqP (hA n hnA) hd
  have := hcount n hnA
  omega

theorem cofactorBlock_support (P U : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n)
    (hsupport : ∀ n ∈ A, n ∈ Nat.factoredNumbers U) :
    ∀ k ∈ cofactorBlock P q A, k ∈ Nat.factoredNumbers U := by
  intro k hk
  obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hk
  exact Nat.mem_factoredNumbers_of_dvd (hsupport n (Multiset.mem_filter.mp hn).1)
    (Nat.div_dvd_of_dvd (primeBlock_divisible P q A hcount n hn))

theorem cofactorBlock_mass_bound (P Q : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hQ : ∀ p ∈ Q, Nat.Prime p)
    (hqP : q ∈ P) (hdisj : Disjoint P Q)
    (hσ : (∑ p ∈ P, (p : ℝ)⁻¹) < 1) (hA : stable A) (t : ℕ)
    (hsupport : ∀ n ∈ A, n ∈ Nat.factoredNumbers (P ∪ Q))
    (hcount : ∀ n ∈ A, t + 1 ≤ selectedFactorCount P n) :
    mass (cofactorBlock P q A) ≤ (q : ℝ) *
      (eulerProduct Q * (∑ p ∈ P, (p : ℝ)⁻¹) ^ t /
        (1 - ∑ p ∈ P, (p : ℝ)⁻¹)) := by
  have hc : ∀ n ∈ A, 0 < selectedFactorCount P n := by
    intro n hn
    have := hcount n hn
    omega
  have hb := selected_background_depth_bound P Q hP hQ hdisj hσ t
    (cofactorBlock P q A).toFinset
    (fun n hn => cofactorBlock_support P (P ∪ Q) q A hc hsupport n
      (Multiset.mem_toFinset.mp hn))
    (fun n hn => cofactorBlock_depth P q A (hP q hqP) hqP
      (stable_positive hA) t hcount n (Multiset.mem_toFinset.mp hn))
  calc
    _ = ∑ n ∈ (cofactorBlock P q A).toFinset,
        ((cofactorBlock P q A).count n : ℝ) / n := mass_eq_sum_counts _
    _ ≤ ∑ n ∈ (cofactorBlock P q A).toFinset, (q : ℝ) * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hlt := cofactorBlock_count_lt P q A (hP q hqP) hA hc
        (Multiset.mem_toFinset.mp hn)
      have hle : ((cofactorBlock P q A).count n : ℝ) ≤ q := by exact_mod_cast hlt.le
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = (q : ℝ) * ∑ n ∈ (cofactorBlock P q A).toFinset, (n : ℝ)⁻¹ :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)

theorem cofactorBlock_capacity (P Q : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hQ : ∀ p ∈ Q, Nat.Prime p)
    (hqP : q ∈ P) (hdisj : Disjoint P Q)
    (hσ : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 / 2) (hA : stable A) (b k : ℕ)
    (hb : eulerProduct Q * (∑ p ∈ P, (p : ℝ)⁻¹) ^ b ≤ 1)
    (hsupport : ∀ n ∈ A, n ∈ Nat.factoredNumbers (P ∪ Q))
    (hcount : ∀ n ∈ A, b + k + 1 ≤ selectedFactorCount P n) :
    mass (cofactorBlock P q A) ≤ 2 * (q : ℝ) *
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ k := by
  let σ : ℝ := ∑ p ∈ P, (p : ℝ)⁻¹
  have hs0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hs1 : σ < 1 := by dsimp [σ]; linarith
  have hd : 0 < 1 - σ := by linarith
  have h := cofactorBlock_mass_bound P Q q A hP hQ hqP hdisj hs1 hA
    (b + k) hsupport hcount
  have hn : eulerProduct Q * σ ^ (b + k) ≤ σ ^ k := by
    rw [pow_add, ← mul_assoc]
    simpa using mul_le_mul_of_nonneg_right hb (pow_nonneg hs0 k)
  have he : eulerProduct Q * σ ^ (b + k) / (1 - σ) ≤ 2 * σ ^ k := by
    apply (div_le_iff₀ hd).mpr
    apply hn.trans
    have hs2 : σ ≤ 1 / 2 := hσ
    nlinarith [pow_nonneg hs0 k]
  exact h.trans (by
    calc
      _ ≤ (q : ℝ) * (2 * σ ^ k) := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg q)
      _ = _ := by ring)

theorem extract_primeBlock_bundles (P : Finset ℕ) (q : ℕ) (A : Multiset ℕ)
    (hq : Nat.Prime q) (hqP : q ∈ P) (hA : stable A)
    (hcount : ∀ n ∈ A, 2 ≤ selectedFactorCount P n)
    (m : ℕ) (δ : ℝ) (hm : (m : ℝ) ≤ mass (cofactorBlock P q A) / 2)
    (oracle : ∀ B : Multiset ℕ, B ≤ cofactorBlock P q A → stable B →
      mass (cofactorBlock P q A) / 2 ≤ mass B → approximates B δ) :
    ∃ bundles : Multiset (Multiset ℕ), bundles.card = m ∧
      bundles.join ≤ primeBlock P q A ∧
      (∀ S ∈ bundles, (1 - δ) * (q : ℝ)⁻¹ ≤ mass S ∧
        mass S ≤ (q : ℝ)⁻¹) := by
  obtain ⟨B, hcard, hjoin, hgood, _⟩ := extract_stable_half _ m δ
    (cofactorBlock_stable P q A hq hqP hA hcount) hm oracle
  refine ⟨B.map (Multiset.map (fun n => q * n)), by simpa, ?_, ?_⟩
  · rw [← Multiset.map_join]
    have h := Multiset.map_le_map (f := fun n => q * n) hjoin
    have hc : ∀ n ∈ A, 0 < selectedFactorCount P n := by
      intro n hn
      have := hcount n hn
      omega
    rwa [cofactorBlock_reconstruct P q A hc] at h
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hS
    rw [mass_scale]
    have ht := hgood T hT
    have hq0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left ht.1 hq0
    · simpa using mul_le_mul_of_nonneg_left ht.2 hq0

/-- Assemble independent blocks while retaining every original occurrence. -/
theorem assemble_labeled_inventory (P : Finset ℕ)
    (blocks : ℕ → Multiset ℕ) (bundles : ℕ → Multiset (Multiset ℕ)) (δ : ℝ)
    (hjoin : ∀ q ∈ P, (bundles q).join ≤ blocks q)
    (hgood : ∀ q ∈ P, ∀ S ∈ bundles q,
      (1 - δ) * (q : ℝ)⁻¹ ≤ mass S ∧ mass S ≤ (q : ℝ)⁻¹) :
    ∃ B : Multiset (ℕ × Multiset ℕ),
      (B.map Prod.snd).join ≤ ∑ q ∈ P, blocks q ∧
      B.map Prod.fst = ∑ q ∈ P, Multiset.replicate (bundles q).card q ∧
      (∀ b ∈ B, (1 - δ) * (b.1 : ℝ)⁻¹ ≤ mass b.2 ∧
        mass b.2 ≤ (b.1 : ℝ)⁻¹) := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | @insert q P hq ih =>
    obtain ⟨B, hBjoin, hBlabels, hBgood⟩ := ih
      (fun p hp => hjoin p (Finset.mem_insert_of_mem hp))
      (fun p hp => hgood p (Finset.mem_insert_of_mem hp))
    let C := (bundles q).map (fun S => (q, S))
    have hCsnd : C.map Prod.snd = bundles q := by simp [C, Multiset.map_map]
    have hCfst : C.map Prod.fst = Multiset.replicate (bundles q).card q := by
      simp [C, Multiset.map_map]
    refine ⟨C + B, ?_, ?_, ?_⟩
    · rw [Multiset.map_add, Multiset.join_add, hCsnd, Finset.sum_insert hq]
      exact add_le_add (hjoin q (Finset.mem_insert_self q P)) hBjoin
    · rw [Multiset.map_add, hCfst, hBlabels, Finset.sum_insert hq]
    · intro b hb
      rcases Multiset.mem_add.mp hb with hb | hb
      · obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp hb
        exact hgood q (Finset.mem_insert_self q P) S hS
      · exact hBgood b hb

def primeInventory (P : Finset ℕ) (m : ℕ → ℕ) : Multiset ℕ :=
  ∑ q ∈ P, Multiset.replicate (m q) q

theorem primeInventory_count (P : Finset ℕ) (m : ℕ → ℕ) (q : ℕ) :
    (primeInventory P m).count q = if q ∈ P then m q else 0 := by
  induction P using Finset.induction_on with
  | empty => simp [primeInventory]
  | @insert p P hp ih =>
    simp only [primeInventory, Finset.sum_insert hp, Multiset.count_add] at *
    by_cases hqp : q = p
    · subst p
      simp [ih, hp]
    · simp [Multiset.count_replicate, hqp, Ne.symm hqp, ih]

theorem primeInventory_mem (P : Finset ℕ) (m : ℕ → ℕ) {q : ℕ}
    (hq : q ∈ primeInventory P m) : q ∈ P := by
  have h := Multiset.count_pos.mpr hq
  rw [primeInventory_count] at h
  split_ifs at h with hp
  · exact hp
  · omega

theorem primeInventory_mass (P : Finset ℕ) (m : ℕ → ℕ) :
    mass (primeInventory P m) = ∑ q ∈ P, (m q : ℝ) / q := by
  induction P using Finset.induction_on with
  | empty => simp [primeInventory]
  | @insert q P hq ih =>
    simp only [primeInventory, Finset.sum_insert hq, mass_add] at *
    rw [ih]
    simp [mass, div_eq_mul_inv]

theorem primeBlock_inventory_lifting (P : Finset ℕ) (A : Multiset ℕ)
    (m : ℕ → ℕ) (δ ε : ℝ) (hδ : 0 ≤ δ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n)
    (hextract : ∀ q ∈ P, ∃ bundles : Multiset (Multiset ℕ),
      bundles.card = m q ∧ bundles.join ≤ primeBlock P q A ∧
      (∀ S ∈ bundles, (1 - δ) * (q : ℝ)⁻¹ ≤ mass S ∧ mass S ≤ (q : ℝ)⁻¹))
    (happrox : approximates (primeInventory P m) ε) :
    approximates A (ε + δ) := by
  have hex : ∀ q : ℕ, ∃ bundles : Multiset (Multiset ℕ), q ∈ P →
      bundles.card = m q ∧ bundles.join ≤ primeBlock P q A ∧
      (∀ S ∈ bundles, (1 - δ) * (q : ℝ)⁻¹ ≤ mass S ∧ mass S ≤ (q : ℝ)⁻¹) := by
    intro q
    by_cases hq : q ∈ P
    · obtain ⟨B, hB⟩ := hextract q hq
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => False.elim (hq h)⟩
  choose bundles hb using hex
  obtain ⟨B, hjoin, hlabels, hgood⟩ := assemble_labeled_inventory P
    (fun q => primeBlock P q A) bundles δ
    (fun q hq => (hb q hq).2.1) (fun q hq => (hb q hq).2.2)
  rw [primeBlock_partition P A hcount] at hjoin
  have hl : B.map Prod.fst = primeInventory P m := by
    rw [hlabels]
    unfold primeInventory
    apply Finset.sum_congr rfl
    intro q hq
    rw [(hb q hq).1]
  apply lift_labeled_bundles A B hδ hjoin hgood
  rwa [hl]

theorem primeBlock_mass_partition (P : Finset ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n) :
    (∑ q ∈ P, (q : ℝ)⁻¹ * mass (cofactorBlock P q A)) = mass A := by
  simp_rw [← cofactorBlock_mass P _ A hcount]
  have h := congrArg massHom (primeBlock_partition P A hcount)
  simpa only [map_sum, massHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using h

theorem primeInventory_concentration (P : Finset ℕ) (m : ℕ → ℕ) (a : ℝ)
    (hbound : ∀ q ∈ P, (m q : ℝ) / q ≤ a) :
    ∀ q ∈ primeInventory P m, ((primeInventory P m).count q : ℝ) / q ≤ a := by
  intro q hq
  have hp := primeInventory_mem P m hq
  rw [primeInventory_count, if_pos hp]
  exact hbound q hp

noncomputable def retainedBundleCount (H h : ℝ) : ℕ :=
  if h ≤ H then ⌊H / 2⌋₊ else 0

theorem retainedBundleCount_bounds (H h : ℝ) (hH : 0 ≤ H) (hh : 4 ≤ h) :
    H / 4 - h / 4 ≤ (retainedBundleCount H h : ℝ) ∧
      (retainedBundleCount H h : ℝ) ≤ H / 2 := by
  unfold retainedBundleCount
  split_ifs with hlarge
  · have hlo := Nat.lt_floor_add_one (H / 2)
    have hhi := Nat.floor_le (show 0 ≤ H / 2 by positivity)
    constructor <;> linarith
  · push_cast
    constructor <;> linarith

theorem retained_inventory_mass_bounds (P : Finset ℕ) (H : ℕ → ℝ) (h R : ℝ)
    (hH : ∀ q ∈ P, 0 ≤ H q) (hh : 4 ≤ h)
    (hR : (∑ q ∈ P, (q : ℝ)⁻¹ * H q) = R) :
    (R - h * ∑ q ∈ P, (q : ℝ)⁻¹) / 4 ≤
        mass (primeInventory P (fun q => retainedBundleCount (H q) h)) ∧
      mass (primeInventory P (fun q => retainedBundleCount (H q) h)) ≤ R / 2 := by
  rw [primeInventory_mass]
  have hlo := Finset.sum_le_sum (s := P) (fun q hq =>
    mul_le_mul_of_nonneg_left (retainedBundleCount_bounds (H q) h (hH q hq) hh).1
      (show 0 ≤ (q : ℝ)⁻¹ by positivity))
  have hhi := Finset.sum_le_sum (s := P) (fun q hq =>
    mul_le_mul_of_nonneg_left (retainedBundleCount_bounds (H q) h (hH q hq) hh).2
      (show 0 ≤ (q : ℝ)⁻¹ by positivity))
  have hlform : (∑ q ∈ P, (q : ℝ)⁻¹ * (H q / 4 - h / 4)) =
      (R - h * ∑ q ∈ P, (q : ℝ)⁻¹) / 4 := by
    simp_rw [mul_sub, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hR, ← Finset.sum_div,
      ← Finset.sum_mul]
    ring
  have hhform : (∑ q ∈ P, (q : ℝ)⁻¹ * (H q / 2)) = R / 2 := by
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hR]
  rw [hlform] at hlo
  rw [hhform] at hhi
  constructor
  · simpa only [div_eq_mul_inv, mul_comm] using hlo
  · simpa only [div_eq_mul_inv, mul_comm] using hhi

theorem retained_primeBlock_lifting (P : Finset ℕ) (A : Multiset ℕ)
    (hP : ∀ q ∈ P, Nat.Prime q) (hA : stable A)
    (hcount : ∀ n ∈ A, 2 ≤ selectedFactorCount P n)
    (h δ ε : ℝ) (hδ : 0 ≤ δ)
    (oracle : ∀ q ∈ P, h ≤ mass (cofactorBlock P q A) →
      ∀ B : Multiset ℕ, B ≤ cofactorBlock P q A → stable B →
        mass (cofactorBlock P q A) / 2 ≤ mass B → approximates B δ)
    (happrox : approximates
      (primeInventory P (fun q => retainedBundleCount (mass (cofactorBlock P q A)) h)) ε) :
    approximates A (ε + δ) := by
  apply primeBlock_inventory_lifting P A _ δ ε hδ _ _ happrox
  · intro n hn
    have := hcount n hn
    omega
  · intro q hq
    by_cases hlarge : h ≤ mass (cofactorBlock P q A)
    · apply extract_primeBlock_bundles P q A (hP q hq) hq hA hcount
      · simp only [retainedBundleCount, if_pos hlarge]
        exact Nat.floor_le (div_nonneg (mass_nonneg _) (by norm_num))
      · exact oracle q hq hlarge
    · refine ⟨0, ?_, by simp, by simp⟩
      simp [retainedBundleCount, hlarge]

noncomputable def blockInventory (P : Finset ℕ) (A : Multiset ℕ) (h : ℝ) : Multiset ℕ :=
  primeInventory P (fun q => retainedBundleCount (mass (cofactorBlock P q A)) h)

theorem blockInventory_mass_bounds (P : Finset ℕ) (A : Multiset ℕ)
    (hcount : ∀ n ∈ A, 0 < selectedFactorCount P n)
    (hσ : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hR : 16 * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ mass A) :
    3 * mass A / 16 ≤ mass (blockInventory P A
        (mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹))) ∧
      mass (blockInventory P A (mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹))) ≤ mass A / 2 := by
  have hd : 0 < 4 * ∑ p ∈ P, (p : ℝ)⁻¹ := by positivity
  have hh : 4 ≤ mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have hb := retained_inventory_mass_bounds P (fun q => mass (cofactorBlock P q A))
    (mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹)) (mass A)
    (fun _ _ => mass_nonneg _) hh (primeBlock_mass_partition P A hcount)
  have he : (mass A - mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹) *
      (∑ p ∈ P, (p : ℝ)⁻¹)) / 4 = 3 * mass A / 16 := by
    field_simp [ne_of_gt hσ]
    ring
  rw [he] at hb
  exact hb

theorem blockInventory_concentration (P : Finset ℕ) (A : Multiset ℕ) (h a : ℝ)
    (hP : ∀ q ∈ P, Nat.Prime q) (hh : 4 ≤ h)
    (hcapacity : ∀ q ∈ P, mass (cofactorBlock P q A) ≤ 2 * (q : ℝ) * a) :
    ∀ q ∈ blockInventory P A h, ((blockInventory P A h).count q : ℝ) / q ≤ a := by
  apply primeInventory_concentration
  intro q hq
  have hm := (retainedBundleCount_bounds (mass (cofactorBlock P q A)) h (mass_nonneg _) hh).2
  have hc := hcapacity q hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (hP q hq).pos
  apply (div_le_iff₀ hq0).mpr
  nlinarith

theorem primeRate_comparison (k : ℕ) (L R M a : ℝ)
    (hL : 1 ≤ L) (hR : 64 ≤ R) (hM : R / 8 ≤ M)
    (ha : 0 < a) (hcap : a * L ^ k ≤ 1) :
    recursiveRate k L R ≤ 8 * min M (Real.sqrt (M * Real.log M / a)) := by
  have hR0 : 0 < R := by linarith
  have hM0 : 0 < M := by linarith
  have hLR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hLM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ L ^ k := pow_nonneg (by linarith) k
  have hsquare : R ≤ M ^ 2 := by
    have hsq := mul_self_le_mul_self (by linarith : 0 ≤ R / 8) hM
    nlinarith
  have hlog := Real.log_le_log hR0 hsquare
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hprod : R * Real.log R / 16 ≤ M * Real.log M := by
    have h := mul_le_mul hM (show Real.log R / 2 ≤ Real.log M by linarith)
      (by positivity : 0 ≤ Real.log R / 2) hM0.le
    nlinarith
  have hrprod : 0 ≤ R * Real.log R := mul_nonneg hR0.le hLR
  have hscaled := mul_le_mul_of_nonneg_left hcap hrprod
  have hrad : R * Real.log R * L ^ k / 16 ≤ M * Real.log M / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hs0 : 0 ≤ R * Real.log R * L ^ k := mul_nonneg hrprod hpow
  have ht0 : 0 ≤ M * Real.log M / a := by positivity
  have hs := Real.sq_sqrt hs0
  have ht := Real.sq_sqrt ht0
  have hsnon := Real.sqrt_nonneg (R * Real.log R * L ^ k)
  have htnon := Real.sqrt_nonneg (M * Real.log M / a)
  have hroot : Real.sqrt (R * Real.log R * L ^ k) ≤
      4 * Real.sqrt (M * Real.log M / a) := by nlinarith
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 8)]
  apply le_min
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

theorem exponential_errors_absorb (x : ℝ) (hx : 1 ≤ x) :
    Real.exp (-2 * x) + Real.exp (-4 * x) ≤ Real.exp (-x) := by
  have hpos := Real.exp_pos (-x)
  have hex := Real.add_one_le_exp x
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hhalf : Real.exp (-x) ≤ 1 / 2 := by nlinarith
  have htwo : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfour : Real.exp (-4 * x) ≤ Real.exp (-2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsq := mul_le_mul_of_nonneg_left hhalf hpos.le
  rw [htwo] at hfour ⊢
  nlinarith

/-- One complete compression step, with the recursive calls isolated as an oracle. -/
theorem prime_compression_step (P : Finset ℕ) (A : Multiset ℕ)
    (k : ℕ) (L a c cp Rp : ℝ)
    (hP : ∀ q ∈ P, Nat.Prime q) (hA : stable A)
    (hcount : ∀ n ∈ A, 2 ≤ selectedFactorCount P n)
    (hσ0 : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hσ : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 / 128)
    (hL : 1 ≤ L) (ha : 0 < a) (ha1 : a < 1) (hacap : a * L ^ k ≤ 1)
    (hc : 0 < c) (hcp : 16 * c ≤ cp)
    (hR : 64 ≤ mass A) (hRp : Rp ≤ 3 * mass A / 16)
    (herror : 1 ≤ c * recursiveRate k L (mass A))
    (hcapacity : ∀ q ∈ P, mass (cofactorBlock P q A) ≤ 2 * (q : ℝ) * a)
    (oracle : ∀ q ∈ P, mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹) ≤
        mass (cofactorBlock P q A) →
      ∀ B : Multiset ℕ, B ≤ cofactorBlock P q A → stable B →
        mass (cofactorBlock P q A) / 2 ≤ mass B →
        approximates B (Real.exp (-4 * (c * recursiveRate k L (mass A)))))
    (primeOracle : ∀ (I : Multiset ℕ) (a : ℝ),
      (∀ p ∈ I, Nat.Prime p) → 0 < a → a < 1 →
      (∀ p ∈ I, (I.count p : ℝ) / p ≤ a) → Rp ≤ mass I →
      approximates I (Real.exp (-cp * min (mass I)
        (Real.sqrt (mass I * Real.log (mass I) / a))))) :
    approximates A (Real.exp (-c * recursiveRate k L (mass A))) := by
  let h := mass A / (4 * ∑ p ∈ P, (p : ℝ)⁻¹)
  let I := blockInventory P A h
  let F := recursiveRate k L (mass A)
  have hcpos : ∀ n ∈ A, 0 < selectedFactorCount P n := by
    intro n hn
    have := hcount n hn
    omega
  have hsmall : 16 * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ mass A := by linarith
  have hmass := blockInventory_mass_bounds P A hcpos hσ0 hsmall
  change 3 * mass A / 16 ≤ mass I ∧ mass I ≤ mass A / 2 at hmass
  have hh : 4 ≤ h := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * ∑ p ∈ P, (p : ℝ)⁻¹)).mpr
    linarith
  have hiprime : ∀ p ∈ I, Nat.Prime p := by
    intro p hp
    exact hP p (primeInventory_mem P _ hp)
  have hi := primeOracle I a hiprime ha ha1
    (blockInventory_concentration P A h a hP hh hcapacity) (hRp.trans hmass.1)
  have hrate := primeRate_comparison k L (mass A) (mass I) a hL hR
    (by linarith [hmass.1]) ha hacap
  let G := min (mass I) (Real.sqrt (mass I * Real.log (mass I) / a))
  have hg : 0 ≤ G := le_min (mass_nonneg I) (Real.sqrt_nonneg _)
  have he : 2 * (c * F) ≤ cp * G := by
    have h1 := mul_le_mul_of_nonneg_left hrate hc.le
    have h2 := mul_le_mul_of_nonneg_right hcp hg
    change c * F ≤ c * (8 * G) at h1
    nlinarith
  have hi' : approximates I (Real.exp (-2 * (c * F))) :=
    approximates_error_mono (Real.exp_le_exp.mpr (by linarith)) hi
  have hlift := retained_primeBlock_lifting P A hP hA hcount h
    (Real.exp (-4 * (c * F))) (Real.exp (-2 * (c * F)))
    (Real.exp_pos _).le oracle hi'
  apply approximates_error_mono _ hlift
  simpa [F, neg_mul] using exponential_errors_absorb (c * F) herror

theorem recursiveRate_lower (k : ℕ) (L R : ℝ)
    (hL : 1 ≤ L) (hR : 1 ≤ R) (hlog : 1 ≤ Real.log R) :
    Real.sqrt R ≤ recursiveRate k L R := by
  have hR0 : 0 ≤ R := by linarith
  have hp : 1 ≤ L ^ k := one_le_pow₀ hL
  have hs := Real.sq_sqrt hR0
  have hn := Real.sqrt_nonneg R
  apply le_min
  · nlinarith
  · apply Real.sqrt_le_sqrt
    have h1 : R ≤ R * Real.log R := by nlinarith
    nlinarith

theorem cofactor_threshold_amplifies (σ L R H S : ℝ)
    (hσ : 0 < σ) (hidentity : 128 * σ * L = 1)
    (hH : R / (4 * σ) ≤ H) (hS : H / 2 ≤ S) :
    16 * R * L ≤ S := by
  have he : R / (4 * σ) = 32 * R * L := by
    apply (div_eq_iff (by positivity : 4 * σ ≠ 0)).mpr
    have h := congrArg (fun x : ℝ => R * x) hidentity
    nlinarith
  rw [he] at hH
  linarith

/-- Uniform recursion with constants fixed before the depth and inventories. -/
theorem uniform_recursive_bound (cg cp Rg Rp c R₀ : ℝ)
    (hc : 0 < c) (hcg : c ≤ cg) (hcp : 16 * c ≤ cp)
    (hR₀ : 64 ≤ R₀) (hRg : Rg ≤ R₀) (hRp : Rp ≤ 3 * R₀ / 16)
    (hlog : 1 ≤ Real.log R₀) (herror : 1 ≤ c * Real.sqrt R₀)
    (generalOracle : ∀ A : Multiset ℕ, positive A → Rg ≤ mass A →
      approximates A (Real.exp (-cg * Real.sqrt (mass A * Real.log (mass A)))))
    (primeOracle : ∀ (I : Multiset ℕ) (a : ℝ),
      (∀ p ∈ I, Nat.Prime p) → 0 < a → a < 1 →
      (∀ p ∈ I, (I.count p : ℝ) / p ≤ a) → Rp ≤ mass I →
      approximates I (Real.exp (-cp * min (mass I)
        (Real.sqrt (mass I * Real.log (mass I) / a)))))
    (P Q : Finset ℕ) (b : ℕ) (L : ℝ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (hdisj : Disjoint P Q)
    (hσ0 : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hσ : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 / 128)
    (hL : 1 ≤ L) (hidentity : 128 * (∑ p ∈ P, (p : ℝ)⁻¹) * L = 1)
    (hb : eulerProduct Q * (∑ p ∈ P, (p : ℝ)⁻¹) ^ b ≤ 1)
    (k : ℕ) (A : Multiset ℕ) (hA : stable A) (hmass : R₀ ≤ mass A)
    (hsupport : ∀ n ∈ A, n ∈ Nat.factoredNumbers (P ∪ Q))
    (hcount : ∀ n ∈ A, b + k + 1 ≤ selectedFactorCount P n) :
    approximates A (Real.exp (-c * recursiveRate k L (mass A))) := by
  induction k generalizing A with
  | zero =>
    have hi := generalOracle A (stable_positive hA) (hRg.trans hmass)
    apply approximates_error_mono _ hi
    apply Real.exp_le_exp.mpr
    have hf : recursiveRate 0 L (mass A) ≤ Real.sqrt (mass A * Real.log (mass A)) := by
      simp only [recursiveRate, pow_zero, mul_one]
      exact min_le_right _ _
    have h1 := mul_le_mul_of_nonneg_left hf hc.le
    have h2 := mul_le_mul_of_nonneg_right hcg (Real.sqrt_nonneg (mass A * Real.log (mass A)))
    linarith
  | succ k ih =>
    let σ : ℝ := ∑ p ∈ P, (p : ℝ)⁻¹
    have hs0 : 0 < σ := hσ0
    have hs1 : σ < 1 := by dsimp [σ]; linarith
    have hacap : σ ^ (k + 1) * L ^ (k + 1) ≤ 1 := by
      rw [← mul_pow]
      apply pow_le_one₀ (mul_nonneg hs0.le (by linarith))
      change 128 * σ * L = 1 at hidentity
      nlinarith
    have herr : 1 ≤ c * recursiveRate (k + 1) L (mass A) := by
      have hl : 1 ≤ Real.log (mass A) := hlog.trans
        (Real.log_le_log (by linarith : 0 < R₀) hmass)
      have hr := recursiveRate_lower (k + 1) L (mass A) hL (by linarith) hl
      have hroot := Real.sqrt_le_sqrt hmass
      have hmul := mul_le_mul_of_nonneg_left (hroot.trans hr) hc.le
      exact herror.trans hmul
    apply prime_compression_step P A (k + 1) L (σ ^ (k + 1)) c cp Rp hP hA
      (by intro n hn; have := hcount n hn; omega) hσ0 hσ hL
      (pow_pos hs0 _) (pow_lt_one₀ hs0.le hs1 (by omega)) hacap hc hcp
      (by linarith) (by linarith) herr
    · intro q hq
      exact cofactorBlock_capacity P Q q A hP hQ hq hdisj (by linarith) hA b (k + 1)
        hb hsupport hcount
    · intro q hq hlarge B hBA hBstable hhalf
      have hamp := cofactor_threshold_amplifies σ L (mass A)
        (mass (cofactorBlock P q A)) (mass B) hs0 hidentity hlarge hhalf
      have hBmass : R₀ ≤ mass B := by
        have hR0 : 0 ≤ mass A := mass_nonneg A
        nlinarith
      have hposcount : ∀ n ∈ A, 0 < selectedFactorCount P n := by
        intro n hn
        have := hcount n hn
        omega
      have hBsupport : ∀ n ∈ B, n ∈ Nat.factoredNumbers (P ∪ Q) := by
        intro n hn
        exact cofactorBlock_support P (P ∪ Q) q A hposcount hsupport n
          (Multiset.mem_of_le hBA hn)
      have hBcount : ∀ n ∈ B, b + k + 1 ≤ selectedFactorCount P n := by
        intro n hn
        apply cofactorBlock_depth P q A (hP q hq) hq (stable_positive hA)
          (b + k + 1) _ n (Multiset.mem_of_le hBA hn)
        intro n hn
        have := hcount n hn
        omega
      have hi := ih B hBstable hBmass hBsupport hBcount
      apply approximates_error_mono _ hi
      apply Real.exp_le_exp.mpr
      have hr := recursiveRate_amplifies k hL (by linarith : 1 ≤ mass A) hamp
      have hm := mul_le_mul_of_nonneg_left hr hc.le
      nlinarith
    · exact primeOracle

theorem uniform_recursion (hg : generalEstimate) (hp : primeEstimate) :
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
      ∀ (P Q : Finset ℕ) (b k : ℕ) (A : Multiset ℕ),
        (∀ p ∈ P, Nat.Prime p) → (∀ q ∈ Q, Nat.Prime q) → Disjoint P Q →
        0 < (∑ p ∈ P, (p : ℝ)⁻¹) → (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 / 128 →
        eulerProduct Q * (∑ p ∈ P, (p : ℝ)⁻¹) ^ b ≤ 1 →
        stable A → R₀ ≤ mass A →
        (∀ n ∈ A, n ∈ Nat.factoredNumbers (P ∪ Q)) →
        (∀ n ∈ A, b + k + 1 ≤ selectedFactorCount P n) →
        approximates A (Real.exp (-c * recursiveRate k
          (1 / (128 * ∑ p ∈ P, (p : ℝ)⁻¹)) (mass A))) := by
  obtain ⟨cg, hcg0, Rg, hRg0, generalOracle⟩ := hg
  obtain ⟨cp, hcp0, Rp, hRp0, primeOracle⟩ := hp
  let c := min cg (cp / 16)
  have hc : 0 < c := lt_min hcg0 (by positivity)
  have hcg : c ≤ cg := min_le_left _ _
  have hcp : 16 * c ≤ cp := by have := min_le_right cg (cp / 16); dsimp [c]; linarith
  let R₀ := 64 + Rg + 16 * Rp + Real.exp 1 + (1 / c) ^ 2
  have hsq : 0 ≤ (1 / c) ^ 2 := sq_nonneg _
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hR₀ : 64 ≤ R₀ := by dsimp [R₀]; linarith
  have hRg : Rg ≤ R₀ := by dsimp [R₀]; linarith
  have hRp : Rp ≤ 3 * R₀ / 16 := by dsimp [R₀]; linarith
  have hexp : Real.exp 1 ≤ R₀ := by dsimp [R₀]; linarith
  have hlog : 1 ≤ Real.log R₀ := by
    have h := Real.log_le_log he hexp
    simpa only [Real.log_exp] using h
  have herror : 1 ≤ c * Real.sqrt R₀ := by
    have hbound : (1 / c) ^ 2 ≤ R₀ := by dsimp [R₀]; linarith
    have hr := Real.sqrt_le_sqrt hbound
    rw [Real.sqrt_sq (by positivity : 0 ≤ 1 / c)] at hr
    have hm := mul_le_mul_of_nonneg_left hr hc.le
    have heq : c * (1 / c) = 1 := by field_simp
    rwa [heq] at hm
  refine ⟨c, hc, R₀, by linarith, ?_⟩
  intro P Q b k A hP hQ hdisj hσ0 hσ hb hA hmass hsupport hcount
  have hL : 1 ≤ 1 / (128 * ∑ p ∈ P, (p : ℝ)⁻¹) := by
    apply (le_div_iff₀ (by positivity : 0 < 128 * ∑ p ∈ P, (p : ℝ)⁻¹)).mpr
    linarith
  have hid : 128 * (∑ p ∈ P, (p : ℝ)⁻¹) *
      (1 / (128 * ∑ p ∈ P, (p : ℝ)⁻¹)) = 1 := by
    field_simp [ne_of_gt hσ0]
  exact uniform_recursive_bound cg cp Rg Rp c R₀ hc hcg hcp hR₀ hRg hRp hlog herror
    generalOracle primeOracle P Q b _ hP hQ hdisj hσ0 hσ hL hid hb
    k A hA hmass hsupport hcount

noncomputable def selectionDepth (R : ℝ) : ℕ := ⌈2 * Real.log R⌉₊

theorem selectionDepth_bounds (R : ℝ) (hlog : 1 ≤ Real.log R) :
    0 < selectionDepth R ∧ (3 * selectionDepth R + 1 : ℕ) ≤ 10 * Real.log R := by
  have hlo := Nat.le_ceil (2 * Real.log R)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log R by linarith)
  change 2 * Real.log R ≤ (selectionDepth R : ℝ) at hlo
  change (selectionDepth R : ℝ) < 2 * Real.log R + 1 at hhi
  constructor
  · have hr : 0 < (selectionDepth R : ℝ) := by linarith
    exact_mod_cast hr
  · push_cast
    linarith

theorem selectionDepth_power (R : ℝ) (hR : 0 < R) :
    R ≤ (2 : ℝ) ^ selectionDepth R := by
  have hlo := Nat.le_ceil (2 * Real.log R)
  change 2 * Real.log R ≤ (selectionDepth R : ℝ) at hlo
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (selectionDepth R))
  have hx : Real.log R ≤ (selectionDepth R : ℝ) * Real.log 2 := by linarith
  have h := Real.exp_le_exp.mpr hx
  simpa only [Real.exp_log hR, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h

theorem eulerProduct_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q)
    (hQ : ∀ q ∈ Q, Nat.Prime q) : eulerProduct P ≤ eulerProduct Q := by
  have hf : ∀ q ∈ Q, 1 ≤ (1 - (q : ℝ)⁻¹)⁻¹ := by
    intro q hq
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).two_le
    have hi : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr (by linarith)
    apply (one_le_inv₀ (by linarith : 0 < 1 - (q : ℝ)⁻¹)).mpr
    have hnon : 0 ≤ (q : ℝ)⁻¹ := by positivity
    linarith
  exact Finset.prod_le_prod_of_subset_of_one_le hPQ
    (fun q hq => (by norm_num : (0 : ℝ) ≤ 1).trans (hf q (hPQ hq)))
    (fun q hq _ => hf q hq)

theorem selected_background_budget (R σ Z : ℝ) (hR : 0 < R)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 2) (hZ : Z ≤ R ^ 2) :
    Z * σ ^ (2 * selectionDepth R) ≤ 1 := by
  have hr := selectionDepth_power R hR
  have hp := pow_le_pow_left₀ hσ0 hσ (selectionDepth R)
  have hpow : (0 : ℝ) < 2 ^ selectionDepth R := by positivity
  have hmul : R * σ ^ selectionDepth R ≤ 1 := by
    have h := mul_le_mul hr hp (pow_nonneg hσ0 _) hpow.le
    have he : (2 : ℝ) ^ selectionDepth R * (1 / 2 : ℝ) ^ selectionDepth R = 1 := by
      rw [← mul_pow]
      norm_num
    exact h.trans_eq he
  have hnon : 0 ≤ R * σ ^ selectionDepth R := mul_nonneg hR.le (pow_nonneg hσ0 _)
  have hs : (R * σ ^ selectionDepth R) ^ 2 ≤ 1 := by nlinarith
  have hz := mul_le_mul_of_nonneg_right hZ (pow_nonneg hσ0 (2 * selectionDepth R))
  apply hz.trans
  calc
    R ^ 2 * σ ^ (2 * selectionDepth R) = (R * σ ^ selectionDepth R) ^ 2 := by
      rw [Nat.mul_comm 2 (selectionDepth R), pow_mul, mul_pow]
    _ ≤ 1 := hs

theorem selected_depth_saturates (R M L : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hMR : M ≤ R) (hlog : 1 ≤ Real.log M) (hL : 2 ≤ L) :
    recursiveRate (selectionDepth R) L M = M := by
  have hp := (selectionDepth_power R hR).trans
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL (selectionDepth R))
  have hpow : 0 ≤ L ^ selectionDepth R := by positivity
  have hprod : M ≤ Real.log M * L ^ selectionDepth R := by nlinarith
  have hsq : M ^ 2 ≤ M * Real.log M * L ^ selectionDepth R := by
    have h := mul_le_mul_of_nonneg_left hprod hM
    nlinarith
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hM] at hs
  exact min_eq_left hs

theorem localized_prime_universe (D : ℕ) (R : ℝ) (hD : 1 ≤ D)
    (hR : 64 ≤ R) (hlogD : Real.log D ≤ R) :
    eulerProduct D.primesLE ≤ R ^ 2 ∧
      (∑ p ∈ D.primesLE, (p : ℝ)⁻¹) ≤ 2 * Real.log R := by
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hpoly : 16 * (2 + Real.log D) ≤ R ^ 2 := by nlinarith
  constructor
  · exact (eulerProduct_upper D hD).trans hpoly
  · have hl := Real.log_le_log (by positivity : 0 < 16 * (2 + Real.log D)) hpoly
    rw [Real.log_pow] at hl
    norm_num at hl
    exact (prime_reciprocal_sum_le_log D hD).trans hl

/-- A fixed bad-mass probability already suffices for simultaneous selection. -/
theorem selection_tail_budget (R : ℝ) (hlog : 1 ≤ Real.log R) :
    Real.exp (-(64 * Real.log R) / 8) ≤ 1 / 9 := by
  have hx : 8 ≤ (64 * Real.log R) / 8 := by linarith
  have he := Real.add_one_le_exp ((64 * Real.log R) / 8)
  have hp := Real.exp_pos (-(64 * Real.log R) / 8)
  have hcancel : Real.exp ((64 * Real.log R) / 8) *
      Real.exp (-(64 * Real.log R) / 8) = 1 := by
    rw [← Real.exp_add]
    have hz : (64 * Real.log R) / 8 + -(64 * Real.log R) / 8 = 0 := by ring
    rw [hz, Real.exp_zero]
  nlinarith

theorem calibrated_squarefree_selection (U : Finset ℕ) (A : Multiset ℕ) (R : ℝ)
    (hR : 0 < R) (hlog : 1 ≤ Real.log R)
    (hA : stable A) (hsquare : ∀ n ∈ A, Squarefree n)
    (hmasslo : R / 2 ≤ mass A) (hmasshi : mass A ≤ R)
    (hU : ∀ n ∈ A, n.primeFactorsList.toFinset ⊆ U)
    (hweight : (∑ p ∈ U, (p : ℝ)⁻¹) ≤ 2 * Real.log R)
    (hfactor : ∀ n ∈ A, 524288 * (Real.log R) ^ 2 ≤ (factorCount n : ℝ)) :
    ∃ (P : Finset ℕ) (B : Multiset ℕ), P ⊆ U ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) < 1 / 256 ∧ B ≤ A ∧ stable B ∧ R / 4 < mass B ∧
      (∀ n ∈ B, Squarefree n ∧ 3 * selectionDepth R + 1 ≤ selectedFactorCount P n) := by
  let θ := 1 / (8192 * Real.log R)
  have hd : 0 < 8192 * Real.log R := by linarith
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hμ : ∀ n ∈ A, 64 * Real.log R ≤ θ * (factorCount n : ℝ) := by
    intro n hn
    change 64 * Real.log R ≤ (1 / (8192 * Real.log R)) * (factorCount n : ℝ)
    rw [one_div, mul_comm ((8192 * Real.log R)⁻¹), ← div_eq_mul_inv]
    apply (le_div_iff₀ hd).mpr
    have := hfactor n hn
    nlinarith
  have hT : ((3 * selectionDepth R + 1 : ℕ) : ℝ) ≤ (64 * Real.log R) / 2 := by
    have := (selectionDepth_bounds R hlog).2
    linarith
  have hbudget : (θ * ∑ p ∈ U, (p : ℝ)⁻¹) / (1 / 256) +
      (Real.exp (-(64 * Real.log R) / 8) * mass A) / (R / 4) < 1 := by
    have h1 : (θ * ∑ p ∈ U, (p : ℝ)⁻¹) / (1 / 256) ≤ 1 / 16 := by
      have hw := mul_le_mul_of_nonneg_left hweight hθ0
      have heq : θ * (2 * Real.log R) = 1 / 4096 := by
        dsimp [θ]
        field_simp
        ring
      rw [heq] at hw
      norm_num at hw ⊢
      linarith
    have h2 : (Real.exp (-(64 * Real.log R) / 8) * mass A) / (R / 4) ≤ 4 / 9 := by
      apply (div_le_iff₀ (by positivity : 0 < R / 4)).mpr
      have ht := mul_le_mul (selection_tail_budget R hlog) hmasshi
        (mass_nonneg A) (by norm_num : (0 : ℝ) ≤ 1 / 9)
      nlinarith
    linarith
  obtain ⟨P, B, hPU, hsmall, hBA, hBstable, hBmass, hgood⟩ :=
    squarefree_prime_selection U A (3 * selectionDepth R + 1) hA hsquare hθ0 hθ1
      (by norm_num : (0 : ℝ) < 1 / 256) (by positivity : 0 < R / 4) hU hμ hT hbudget
  exact ⟨P, B, hPU, hsmall, hBA, hBstable, by linarith, hgood⟩

theorem localized_squarefree_exponential (hg : generalEstimate) (hp : primeEstimate) :
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ, 1 < R₀ ∧
      ∀ (D : ℕ) (R : ℝ) (A : Multiset ℕ), 1 ≤ D → R₀ ≤ R → Real.log D ≤ R →
        stable A → (∀ n ∈ A, Squarefree n) → R / 2 ≤ mass A → mass A ≤ R →
        (∀ n ∈ A, n ≤ D) →
        (∀ n ∈ A, 524288 * (Real.log R) ^ 2 ≤ (factorCount n : ℝ)) →
        approximates A (Real.exp (-c * R)) := by
  obtain ⟨c, hc, Ru, hRu, hu⟩ := uniform_recursion hg hp
  let R₀ := 64 + 4 * Ru + 4 * Real.exp 1
  have he : 0 < Real.exp 1 := Real.exp_pos _
  refine ⟨c / 4, by positivity, R₀, by dsimp [R₀]; linarith, ?_⟩
  intro D R A hD hR hlogD hA hsquare hmasslo hmasshi hden hfactor
  have hR64 : 64 ≤ R := by dsimp [R₀] at hR; linarith
  have hRpos : 0 < R := by linarith
  have hRexp : Real.exp 1 ≤ R / 4 := by dsimp [R₀] at hR; linarith
  have hRlog : 1 ≤ Real.log R := by
    have h := Real.log_le_log he (show Real.exp 1 ≤ R by linarith)
    simpa only [Real.log_exp] using h
  have hU : ∀ n ∈ A, n.primeFactorsList.toFinset ⊆ D.primesLE := by
    intro n hn p hp
    have hp' := Nat.mem_primeFactorsList'.mp (List.mem_toFinset.mp hp)
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd (stable_positive hA n hn) hp'.2.1).trans (hden n hn), hp'.1⟩
  have hUbounds := localized_prime_universe D R hD hR64 hlogD
  obtain ⟨P, B, hPU, hσ, hBA, hBstable, hBmass, hBcount⟩ :=
    calibrated_squarefree_selection D.primesLE A R hRpos hRlog hA hsquare
      hmasslo hmasshi hU hUbounds.2 hfactor
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (hPU hp)).2
  have hQ : ∀ q ∈ D.primesLE \ P, Nat.Prime q := fun q hq =>
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hq).1).2
  have hBne : B ≠ 0 := by
    intro hz
    rw [hz, mass_zero] at hBmass
    linarith
  obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hBne
  have hcnt : 0 < selectedFactorCount P n := by have := (hBcount n hn).2; omega
  obtain ⟨p, hpP, hpprime, _⟩ := selected_prime_exists P hcnt
  have hσ0 : 0 < ∑ p ∈ P, (p : ℝ)⁻¹ := by
    have hp0 : 0 < (p : ℝ)⁻¹ := by exact_mod_cast inv_pos.mpr (show 0 < (p : ℝ) by exact_mod_cast hpprime.pos)
    exact hp0.trans_le (Finset.single_le_sum (f := fun q : ℕ => (q : ℝ)⁻¹)
      (fun q _ => by positivity) hpP)
  have hbackground : eulerProduct (D.primesLE \ P) *
      (∑ p ∈ P, (p : ℝ)⁻¹) ^ (2 * selectionDepth R) ≤ 1 := by
    apply selected_background_budget R _ _ hRpos hσ0.le (by linarith)
    exact (eulerProduct_mono Finset.sdiff_subset
      (fun p hp => (Nat.mem_primesLE.mp hp).2)).trans hUbounds.1
  have hBsupport : ∀ n ∈ B, n ∈ Nat.factoredNumbers (P ∪ (D.primesLE \ P)) := by
    intro n hn
    have hnA := Multiset.mem_of_le hBA hn
    refine Nat.mem_factoredNumbers.mpr ⟨ne_of_gt (stable_positive hA n hnA), ?_⟩
    intro p hp
    have hpU := hU n hnA (List.mem_toFinset.mpr hp)
    by_cases hpP : p ∈ P
    · exact Finset.mem_union_left _ hpP
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hpU, hpP⟩)
  have hBthreshold : Ru ≤ mass B := by dsimp [R₀] at hR; linarith
  have hdepth : ∀ n ∈ B, 2 * selectionDepth R + selectionDepth R + 1 ≤
      selectedFactorCount P n := by
    intro n hn
    have := (hBcount n hn).2
    omega
  have hi := hu P (D.primesLE \ P) (2 * selectionDepth R) (selectionDepth R) B
    hP hQ (Finset.disjoint_left.mpr (fun q hq hq' => (Finset.mem_sdiff.mp hq').2 hq))
    hσ0 (by linarith) hbackground
    hBstable hBthreshold hBsupport hdepth
  have hBhi : mass B ≤ R := (mass_mono hBA).trans hmasshi
  have hBlog : 1 ≤ Real.log (mass B) := by
    have h := Real.log_le_log he (hRexp.trans hBmass.le)
    simpa only [Real.log_exp] using h
  have hL : 2 ≤ 1 / (128 * ∑ p ∈ P, (p : ℝ)⁻¹) := by
    apply (le_div_iff₀ (by positivity : 0 < 128 * ∑ p ∈ P, (p : ℝ)⁻¹)).mpr
    linarith
  rw [selected_depth_saturates R (mass B) _ hRpos (mass_nonneg B) hBhi hBlog hL] at hi
  apply approximates_mono hBA
  apply approximates_error_mono _ hi
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The exact advertised conditional theorem, with no extra analytic premises. -/
theorem proof : conditionalTarget := by
  intro hg hp
  obtain ⟨cl, hcl, Rl, hRl, hlocal⟩ := localized_squarefree_exponential hg hp
  let G : ℝ := Real.log 4 * ∑' n : ℕ, logWeight n
  have hG : 0 ≤ G := mul_nonneg (Real.log_nonneg (by norm_num))
    (tsum_nonneg (fun n => logWeight_nonneg n))
  let K : ℝ := 1 + 32 * G
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hKpos : 0 < K := by linarith
  let c := min cl (1 / (8 * K))
  have hc : 0 < c := lt_min hcl (by positivity)
  let R₀ := Rl + 16 * K + 64
  refine ⟨524288, by norm_num, c, hc, R₀, by dsimp [R₀]; linarith, ?_⟩
  intro A hA hR hfactor
  have hR64 : 64 ≤ mass A := by dsimp [R₀] at hR; linarith
  have hRK : 16 * K ≤ mass A := by dsimp [R₀] at hR; linarith
  have hRlocal : Rl ≤ mass A := by dsimp [R₀] at hR; linarith
  obtain ⟨S, hS⟩ := exists_optimal A
  by_cases hexact : mass S = 1
  · refine ⟨S, hS.1, ?_, hS.2.1⟩
    rw [hexact]
    have := (Real.exp_pos (-c * mass A)).le
    linarith
  have hstrict : mass S < 1 := lt_of_le_of_ne hS.2.1 hexact
  let E := 1 - mass S
  have hE : 0 < E := by dsimp [E]; linarith
  have hE1 : E ≤ 1 := by dsimp [E]; have := mass_nonneg S; linarith
  let x := Real.log E⁻¹
  have heq : Real.exp (-x) = E := by
    dsimp [x]
    rw [Real.log_inv, neg_neg, Real.exp_log hE]
  by_cases hx : mass A / (8 * K) ≤ x
  · have hcx : c * mass A ≤ x := by
      calc
        _ ≤ (1 / (8 * K)) * mass A :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (mass_nonneg A)
        _ = mass A / (8 * K) := by ring
        _ ≤ x := hx
    have hgap : E ≤ Real.exp (-c * mass A) := by
      rw [← heq]
      exact Real.exp_le_exp.mpr (by linarith)
    refine ⟨S, hS.1, ?_, hS.2.1⟩
    dsimp [E] at hgap
    linarith
  have hxsmall : x < mass A / (8 * K) := lt_of_not_ge hx
  let B := A - S
  have hBA : B ≤ A := Multiset.sub_le_self _ _
  have hBstable : stable B := stable_submultiset hA hBA
  have hBmass : mass A - 1 < mass B := optimal_complement_mass hS hstrict
  let D := ⌊E⁻¹⌋₊
  have hInv : 1 ≤ E⁻¹ := (one_le_inv₀ hE).mpr hE1
  have hD : 1 ≤ D := (Nat.one_le_floor_iff _).mpr hInv
  have hden : ∀ n ∈ B, n ≤ D := by
    intro n hn
    exact Nat.le_floor (optimal_complement_denominator hS (stable_positive hA) hstrict hn).le
  have hlogD : Real.log D ≤ x := Real.log_le_log
    (by exact_mod_cast (show 0 < D by omega)) (Nat.floor_le (inv_nonneg.mpr hE.le))
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hxR : x ≤ mass A := by
    have hd : 0 < 8 * K := by positivity
    have h := (lt_div_iff₀ hd).mp hxsmall
    have hx0 : 0 ≤ x := hlogD0.trans hlogD
    nlinarith
  have hns := stable_nonsquarefree_mass_bound B hBstable D hD hden
  have hnsbound : mass (B.filter (fun n => ¬ Squarefree n)) ≤ mass A / 4 := by
    have hcoef : 32 * G ≤ K := by dsimp [K]; linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2 + Real.log D by linarith)
    have hxmul := (lt_div_iff₀ (by positivity : 0 < 8 * K)).mp hxsmall
    change mass (B.filter (fun n => ¬ Squarefree n)) ≤ 32 * (2 + Real.log D) * G at hns
    have hlogmul := mul_le_mul_of_nonneg_left hlogD hKpos.le
    nlinarith
  let T := B.filter (fun n => Squarefree n)
  have hTB : T ≤ B := Multiset.filter_le _ _
  have hTA : T ≤ A := hTB.trans hBA
  have hTstable := stable_submultiset hA hTA
  have hpartition := congrArg mass (Multiset.filter_add_not (fun n => Squarefree n) B)
  rw [mass_add] at hpartition
  have hTmass : mass A / 2 ≤ mass T := by change mass T + _ = mass B at hpartition; linarith
  have hi := hlocal D (mass A) T hD hRlocal (hlogD.trans hxR) hTstable
    (fun n hn => (Multiset.mem_filter.mp hn).2) hTmass (mass_mono hTA)
    (fun n hn => hden n (Multiset.mem_of_le hTB hn))
    (fun n hn => hfactor n (Multiset.mem_of_le hTA hn))
  apply approximates_mono hTA
  apply approximates_error_mono _ hi
  apply Real.exp_le_exp.mpr
  have hcc : c ≤ cl := min_le_left _ _
  have hm := mul_le_mul_of_nonneg_right hcc (mass_nonneg A)
  linarith
























































































end Submissions.E312HighFactorConditional.HighFactor
