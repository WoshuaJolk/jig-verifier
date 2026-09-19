import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Multiset.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith

namespace Submissions.J5P407NormalForm.Proof

noncomputable def mass (A : Multiset ℕ) : ℝ :=
  (A.map fun n : ℕ => (n : ℝ)⁻¹).sum

def Threshold (c : ℝ) : Prop :=
  ∀ K : ℝ, 1 < K → ∃ N₀ : ℕ,
    ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → N₀ ≤ A.card → K < mass A →
      ∃ S : Multiset ℕ, S ≤ A ∧
        1 - Real.exp (-(c * K)) < mass S ∧ mass S ≤ 1

def Unconditional (c : ℝ) : Prop :=
  ∀ K : ℝ, 1 < K → ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → K < mass A →
    ∃ S : Multiset ℕ, S ≤ A ∧
      1 - Real.exp (-(c * K)) < mass S ∧ mass S ≤ 1

-- Exact root syntax, with the same local mass definition; no canonical import.
def canonicalStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, 1 < K → ∃ N₀ : ℕ,
    ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → N₀ ≤ A.card → K < mass A →
      ∃ S : Multiset ℕ, S ≤ A ∧
        1 - Real.exp (-(c * K)) < mass S ∧ mass S ≤ 1

theorem mass_nonneg (A : Multiset ℕ) : 0 ≤ mass A := by
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨n, _, rfl⟩ := Multiset.mem_map.mp hx
  exact inv_nonneg.mpr (Nat.cast_nonneg n)

theorem mass_add (A B : Multiset ℕ) : mass (A + B) = mass A + mass B := by
  simp [mass]

theorem mass_mono {A B : Multiset ℕ} (h : A ≤ B) : mass A ≤ mass B := by
  obtain ⟨D, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [mass_add]
  exact le_add_of_nonneg_right (mass_nonneg D)

theorem mass_replicate (t L : ℕ) :
    mass (Multiset.replicate t L) = (t : ℝ) * (L : ℝ)⁻¹ := by
  simp [mass, nsmul_eq_mul]

theorem split_submultiset {U A B : Multiset ℕ} (h : U ≤ A + B) :
    ∃ S T : Multiset ℕ, S ≤ A ∧ T ≤ B ∧ U = S + T := by
  refine ⟨U ∩ A, U - A, Multiset.inter_le_right, ?_, ?_⟩
  · exact Multiset.sub_le_iff_le_add'.mpr h
  · simpa only [add_comm] using (Multiset.sub_add_inter U A).symm

theorem unconditional_of_threshold {c : ℝ} (hc : 0 < c)
    (h : Threshold c) : Unconditional c := by
  intro K hK A hA hKA
  let K' : ℝ := (K + mass A) / 2
  have hKK' : K < K' := by dsimp [K']; linarith
  have hK'A : K' < mass A := by dsimp [K']; linarith
  have hK' : 1 < K' := hK.trans hKK'
  obtain ⟨N₀, hN⟩ := h K' hK'
  let t : ℕ := N₀ + 1
  have ht : 0 < (t : ℝ) := by
    dsimp [t]
    exact_mod_cast Nat.succ_pos N₀
  let ε : ℝ := Real.exp (-(c * K)) - Real.exp (-(c * K'))
  have hε : 0 < ε := by
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith
  obtain ⟨L, hL, hLsmall⟩ := Real.exists_nat_pos_inv_lt (div_pos hε ht)
  have hpad : mass (Multiset.replicate t L) < ε := by
    rw [mass_replicate]
    have := (lt_div_iff₀ ht).mp hLsmall
    simpa only [mul_comm] using this
  let B : Multiset ℕ := Multiset.replicate t L
  have hpos : ∀ n ∈ A + B, 0 < n := by
    intro n hn
    rcases Multiset.mem_add.mp hn with hn | hn
    · exact hA n hn
    · have hnL : n = L := (Multiset.mem_replicate.mp hn).2
      simpa only [hnL] using hL
  have hcard : N₀ ≤ (A + B).card := by
    simp only [Multiset.card_add, B, Multiset.card_replicate]
    exact (Nat.le_succ N₀).trans (Nat.le_add_left t A.card)
  have hmass : K' < mass (A + B) := by
    rw [mass_add]
    exact hK'A.trans_le (le_add_of_nonneg_right (mass_nonneg B))
  obtain ⟨U, hU, hlower, hupper⟩ := hN (A + B) hpos hcard hmass
  obtain ⟨S, T, hSA, hTB, heq⟩ := split_submultiset hU
  have hm : mass U = mass S + mass T := by rw [heq, mass_add]
  have hT : mass T < ε := (mass_mono hTB).trans_lt hpad
  have hT0 := mass_nonneg T
  refine ⟨S, hSA, ?_, ?_⟩
  · dsimp [ε] at hT
    linarith
  · linarith

theorem threshold_of_unconditional {c : ℝ} (h : Unconditional c) : Threshold c := by
  intro K hK
  refine ⟨0, ?_⟩
  intro A hA _ hKA
  exact h K hK A hA hKA

theorem threshold_iff_unconditional {c : ℝ} (hc : 0 < c) :
    Threshold c ↔ Unconditional c :=
  ⟨unconditional_of_threshold hc, threshold_of_unconditional⟩

theorem canonical_iff_unconditional :
    canonicalStatement ↔ ∃ c : ℝ, 0 < c ∧ Unconditional c := by
  change (∃ c : ℝ, 0 < c ∧ Threshold c) ↔ _
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, unconditional_of_threshold hc h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, threshold_of_unconditional h⟩

-- The finite maximum is attained over actual submultisets, with repetitions retained.
def Optimal (A S : Multiset ℕ) : Prop :=
  S ≤ A ∧ mass S ≤ 1 ∧ ∀ T : Multiset ℕ, T ≤ A → mass T ≤ 1 → mass T ≤ mass S

theorem exists_optimal (A : Multiset ℕ) : ∃ S, Optimal A S := by
  classical
  let F := A.powerset.toFinset.filter (fun S => mass S ≤ 1)
  have hmem (S : Multiset ℕ) : S ∈ F ↔ S ≤ A ∧ mass S ≤ 1 := by
    simp [F]
  have hzero : (0 : Multiset ℕ) ∈ F := by
    apply (hmem 0).mpr
    simp [mass]
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image F mass ⟨0, hzero⟩
  have hSS := (hmem S).mp hS
  refine ⟨S, hSS.1, hSS.2, ?_⟩
  intro T hTA hT
  exact hmax T ((hmem T).mpr ⟨hTA, hT⟩)

def Endpoint (c : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → 1 < mass A →
    ∀ S : Multiset ℕ, Optimal A S → 1 - Real.exp (-(c * mass A)) ≤ mass S

theorem endpoint_of_unconditional {c : ℝ} (hc : 0 < c)
    (h : Unconditional c) : Endpoint c := by
  intro A hA hR S hS
  by_contra hn
  have hdexp : Real.exp (-(c * mass A)) < 1 - mass S := by
    have := lt_of_not_ge hn
    linarith
  have hd : 0 < 1 - mass S := (Real.exp_pos _).trans hdexp
  have hlog : -(c * mass A) < Real.log (1 - mass S) :=
    (Real.lt_log_iff_exp_lt hd).mpr hdexp
  let k : ℝ := -Real.log (1 - mass S) / c
  have hkR : k < mass A := by
    apply (div_lt_iff₀ hc).mpr
    linarith
  let K : ℝ := (max 1 k + mass A) / 2
  have hm : max 1 k < mass A := max_lt hR hkR
  have hmK : max 1 k < K := by dsimp [K]; linarith
  have hKR : K < mass A := by dsimp [K]; linarith
  have hK : 1 < K := (le_max_left 1 k).trans_lt hmK
  have hkK : k < K := (le_max_right 1 k).trans_lt hmK
  have hprod : -Real.log (1 - mass S) < K * c := (div_lt_iff₀ hc).mp hkK
  have hexp : Real.exp (-(c * K)) < 1 - mass S := by
    apply (Real.lt_log_iff_exp_lt hd).mp
    nlinarith
  obtain ⟨T, hTA, hTlow, hThi⟩ := h K hK A hA hKR
  have hTS := hS.2.2 T hTA hThi
  linarith

theorem unconditional_of_endpoint {c : ℝ} (hc : 0 < c)
    (h : Endpoint c) : Unconditional c := by
  intro K hK A hA hKR
  obtain ⟨S, hS⟩ := exists_optimal A
  have hb := h A hA (hK.trans hKR) S hS
  have he : Real.exp (-(c * mass A)) < Real.exp (-(c * K)) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact ⟨S, hS.1, by linarith, hS.2.1⟩

theorem unconditional_iff_endpoint {c : ℝ} (hc : 0 < c) :
    Unconditional c ↔ Endpoint c :=
  ⟨endpoint_of_unconditional hc, unconditional_of_endpoint hc⟩

def LogBound (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → ∀ S : Multiset ℕ,
    Optimal A S → 0 < 1 - mass S → mass A ≤ C * (-Real.log (1 - mass S))

theorem logBound_of_endpoint {c : ℝ} (hc : 0 < c) (h : Endpoint c) :
    LogBound (max 1 c⁻¹) := by
  intro A hA S hS hd
  have hsimple := Real.log_le_sub_one_of_pos hd
  have hSnonneg := mass_nonneg S
  have hL : 0 ≤ -Real.log (1 - mass S) := by linarith
  by_cases hR : 1 < mass A
  · have hb := h A hA hR S hS
    have hdexp : 1 - mass S ≤ Real.exp (-(c * mass A)) := by linarith
    have hl := (Real.log_le_iff_le_exp hd).mpr hdexp
    have hmul : mass A * c ≤ -Real.log (1 - mass S) := by nlinarith
    have hdiv : mass A ≤ -Real.log (1 - mass S) / c := (le_div_iff₀ hc).mpr hmul
    have hi : mass A ≤ c⁻¹ * (-Real.log (1 - mass S)) := by
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
    exact hi.trans (mul_le_mul_of_nonneg_right (le_max_right 1 c⁻¹) hL)
  · have hRA : mass A ≤ 1 := le_of_not_gt hR
    have heq : mass S = mass A := le_antisymm (mass_mono hS.1) (hS.2.2 A le_rfl hRA)
    have hbase : mass A ≤ -Real.log (1 - mass S) := by rw [heq] at hsimple ⊢; linarith
    have hscale := mul_le_mul_of_nonneg_right (le_max_left 1 c⁻¹) hL
    exact hbase.trans (by simpa only [one_mul] using hscale)

theorem endpoint_of_logBound {C : ℝ} (hC : 0 < C) (h : LogBound C) :
    Endpoint C⁻¹ := by
  intro A hA _ S hS
  have hd0 : 0 ≤ 1 - mass S := by linarith [hS.2.1]
  rcases eq_or_lt_of_le hd0 with hd | hd
  · have he := Real.exp_pos (-(C⁻¹ * mass A))
    linarith
  · have hb := h A hA S hS hd
    have hdiv : mass A / C ≤ -Real.log (1 - mass S) :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hb)
    have hl : Real.log (1 - mass S) ≤ -(C⁻¹ * mass A) := by
      rw [div_eq_mul_inv] at hdiv
      nlinarith
    have he := (Real.log_le_iff_le_exp hd).mp hl
    linarith

theorem canonical_iff_logBound :
    canonicalStatement ↔ ∃ C : ℝ, 0 < C ∧ LogBound C := by
  rw [canonical_iff_unconditional]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨max 1 c⁻¹, lt_of_lt_of_le zero_lt_one (le_max_left 1 c⁻¹),
      logBound_of_endpoint hc (endpoint_of_unconditional hc h)⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C⁻¹, inv_pos.mpr hC,
      unconditional_of_endpoint (inv_pos.mpr hC) (endpoint_of_logBound hC h)⟩

theorem mass_cons (n : ℕ) (A : Multiset ℕ) :
    mass (n ::ₘ A) = (n : ℝ)⁻¹ + mass A := by simp [mass]

theorem mass_erase {n : ℕ} {A : Multiset ℕ} (hn : n ∈ A) :
    mass (A.erase n) = mass A - (n : ℝ)⁻¹ := by
  have h := congrArg mass (Multiset.cons_erase hn)
  rw [mass_cons] at h
  linarith

theorem small_reciprocal_mem_optimum {A S : Multiset ℕ} {n : ℕ}
    (hS : Optimal A S) (hn : n ∈ A) (hnpos : 0 < n)
    (hsmall : (n : ℝ)⁻¹ ≤ 1 - mass S) : n ∈ S := by
  by_contra hnS
  have hSA : S ≤ A.erase n := by
    have h := Multiset.erase_le_erase n hS.1
    simpa only [Multiset.erase_of_notMem hnS] using h
  have hcons : n ::ₘ S ≤ A := by
    simpa only [Multiset.cons_erase hn] using Multiset.cons_le_cons n hSA
  have hup : mass (n ::ₘ S) ≤ 1 := by rw [mass_cons]; linarith
  have hmax := hS.2.2 (n ::ₘ S) hcons hup
  have hw : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hnpos)
  rw [mass_cons] at hmax
  linarith

theorem optimal_erase_small {A S : Multiset ℕ} {n : ℕ}
    (hS : Optimal A S) (hn : n ∈ A) (hnpos : 0 < n)
    (hsmall : (n : ℝ)⁻¹ ≤ 1 - mass S) :
    Optimal (A.erase n) (S.erase n) ∧
      1 - mass (S.erase n) = (1 - mass S) + (n : ℝ)⁻¹ := by
  have hnS := small_reciprocal_mem_optimum hS hn hnpos hsmall
  have hm := mass_erase hnS
  have hw : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  refine ⟨⟨Multiset.erase_le_erase n hS.1, ?_, ?_⟩, by linarith⟩
  · linarith [hS.2.1]
  · intro T hTA hT
    have hTA' : T ≤ A := hTA.trans (Multiset.erase_le n A)
    have hTS := hS.2.2 T hTA' hT
    have hcons : n ::ₘ T ≤ A := by
      simpa only [Multiset.cons_erase hn] using Multiset.cons_le_cons n hTA
    have hup : mass (n ::ₘ T) ≤ 1 := by rw [mass_cons]; linarith
    have hmax := hS.2.2 (n ::ₘ T) hcons hup
    rw [mass_cons] at hmax
    linarith

theorem logarithmic_deletion_gain {d e : ℝ} (hd : 0 < d)
    (hde : d ≤ e) (he : e ≤ 1) : e - d ≤ Real.log e - Real.log d := by
  have hepos : 0 < e := hd.trans_le hde
  have h := Real.log_le_sub_one_of_pos (div_pos hd hepos)
  rw [Real.log_div hd.ne' hepos.ne'] at h
  have hdiv : Real.log d - Real.log e + 1 ≤ d / e := by linarith
  have hmul := (le_div_iff₀ hepos).mp hdiv
  have hmono : 0 ≤ Real.log e - Real.log d := sub_nonneg.mpr (Real.log_le_log hd hde)
  have hscale := mul_le_mul_of_nonneg_left he hmono
  nlinarith

def TerminalLogBound (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → ∀ S : Multiset ℕ,
    Optimal A S → 0 < 1 - mass S →
    (∀ n ∈ A, 1 - mass S < (n : ℝ)⁻¹) →
    mass A ≤ C * (-Real.log (1 - mass S))

theorem logBound_of_terminal {C : ℝ} (hC : 1 ≤ C)
    (h : TerminalLogBound C) : LogBound C := by
  intro A
  induction A using Multiset.strongInductionOn with
  | ih A ih =>
    intro hA S hS hd
    classical
    by_cases hex : ∃ n ∈ A, (n : ℝ)⁻¹ ≤ 1 - mass S
    · obtain ⟨n, hn, hsmall⟩ := hex
      have hnpos := hA n hn
      have hw : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hnpos)
      obtain ⟨hS', hdef⟩ := optimal_erase_small hS hn hnpos hsmall
      have hd' : 0 < 1 - mass (S.erase n) := by rw [hdef]; linarith
      have hA' : ∀ k ∈ A.erase n, 0 < k := by
        intro k hk
        exact hA k (Multiset.mem_of_mem_erase hk)
      have hb := ih (A.erase n) (Multiset.erase_lt.mpr hn) hA' (S.erase n) hS' hd'
      have hgain : (n : ℝ)⁻¹ ≤
          Real.log (1 - mass (S.erase n)) - Real.log (1 - mass S) := by
        have hg := logarithmic_deletion_gain hd
          (show 1 - mass S ≤ 1 - mass (S.erase n) by rw [hdef]; linarith)
          (show 1 - mass (S.erase n) ≤ 1 by linarith [mass_nonneg (S.erase n)])
        rw [hdef] at hg ⊢
        linarith
      have hC0 : 0 ≤ C := le_trans zero_le_one hC
      have hscaled := mul_le_mul_of_nonneg_left hgain hC0
      have hpaid := mul_le_mul_of_nonneg_right hC hw.le
      have hm := mass_erase hn
      nlinarith
    · apply h A hA S hS hd
      intro n hn
      apply lt_of_not_ge
      intro hnsmall
      exact hex ⟨n, hn, hnsmall⟩

theorem logBound_iff_terminal {C : ℝ} (hC : 1 ≤ C) :
    LogBound C ↔ TerminalLogBound C := by
  constructor
  · intro h A hA S hS hd _
    exact h A hA S hS hd
  · exact logBound_of_terminal hC

theorem canonical_iff_terminalLogBound :
    canonicalStatement ↔ ∃ C : ℝ, 1 ≤ C ∧ TerminalLogBound C := by
  constructor
  · intro hroot
    obtain ⟨c, hc, h⟩ := canonical_iff_unconditional.mp hroot
    refine ⟨max 1 c⁻¹, le_max_left 1 c⁻¹, ?_⟩
    exact (logBound_iff_terminal (le_max_left 1 c⁻¹)).mp
      (logBound_of_endpoint hc (endpoint_of_unconditional hc h))
  · rintro ⟨C, hC, h⟩
    apply canonical_iff_logBound.mpr
    exact ⟨C, lt_of_lt_of_le zero_lt_one hC, logBound_of_terminal hC h⟩

def Lifts (A B : Multiset ℕ) : Prop :=
  ∀ T : Multiset ℕ, T ≤ B → ∃ U : Multiset ℕ, U ≤ A ∧ mass U = mass T

theorem lifts_refl (A : Multiset ℕ) : Lifts A A := by
  intro T hT
  exact ⟨T, hT, rfl⟩

theorem lifts_trans {A B D : Multiset ℕ} (hAB : Lifts A B) (hBD : Lifts B D) :
    Lifts A D := by
  intro T hT
  obtain ⟨V, hVB, hVT⟩ := hBD T hT
  obtain ⟨U, hUA, hUV⟩ := hAB V hVB
  exact ⟨U, hUA, hUV.trans hVT⟩

theorem compression_mass (d m : ℕ) (hd : 0 < d) :
    mass (Multiset.replicate d (d * m)) = (m : ℝ)⁻¹ := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [mass_replicate, Nat.cast_mul, mul_inv_rev,
    mul_comm (m : ℝ)⁻¹ (d : ℝ)⁻¹, mul_inv_cancel_left₀ hdR]

theorem compression_lifts (R : Multiset ℕ) (d m : ℕ) (hd : 0 < d) :
    Lifts (R + Multiset.replicate d (d * m)) (R + {m}) := by
  intro T hT
  obtain ⟨S, V, hSR, hVm, heq⟩ := split_submultiset hT
  rcases Multiset.le_singleton.mp hVm with rfl | rfl
  · refine ⟨S, hSR.trans (le_add_of_nonneg_right (Multiset.zero_le _)), ?_⟩
    simp [heq, mass]
  · refine ⟨S + Multiset.replicate d (d * m), add_le_add hSR le_rfl, ?_⟩
    rw [heq, mass_add, mass_add, compression_mass d m hd]
    simp [mass]

def Stable (A : Multiset ℕ) : Prop :=
  ∀ n ∈ A, 2 ≤ n ∧ A.count n < n.minFac

theorem exists_stable_compression (A : Multiset ℕ) (hA : ∀ n ∈ A, 0 < n) :
    (∃ T : Multiset ℕ, T ≤ A ∧ mass T = 1) ∨
    ∃ B : Multiset ℕ, (∀ n ∈ B, 0 < n) ∧ Stable B ∧ mass B = mass A ∧ Lifts A B := by
  classical
  suffices ∀ k : ℕ, ∀ D : Multiset ℕ, D.card = k → (∀ n ∈ D, 0 < n) →
      (∃ T : Multiset ℕ, T ≤ D ∧ mass T = 1) ∨
      ∃ B : Multiset ℕ, (∀ n ∈ B, 0 < n) ∧ Stable B ∧ mass B = mass D ∧ Lifts D B by
    exact this A.card A rfl hA
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih D hcard hD
  by_cases hone : 1 ∈ D
  · exact Or.inl ⟨{1}, Multiset.singleton_le.mpr hone, by simp [mass]⟩
  have htwo : ∀ n ∈ D, 2 ≤ n := by
    intro n hn
    have hp := hD n hn
    have hne : n ≠ 1 := by intro he; subst n; exact hone hn
    omega
  by_cases hbad : ∃ n ∈ D, n.minFac ≤ D.count n
  · obtain ⟨n, hn, hcount⟩ := hbad
    let d := n.minFac
    have hd : 2 ≤ d := (Nat.minFac_prime (by have := htwo n hn; omega)).two_le
    have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
    obtain ⟨m, hnm⟩ := Nat.minFac_dvd n
    change n = d * m at hnm
    have hmpos : 0 < m := by
      have hp := hD n hn
      nlinarith
    let X := Multiset.replicate d n
    have hXD : X ≤ D := Multiset.le_count_iff_replicate_le.mp hcount
    let R := D - X
    have hdecomp : R + X = D := Multiset.sub_add_cancel hXD
    let B : Multiset ℕ := R + {m}
    have hRD : R ≤ D := Multiset.sub_le_self D X
    have hBpos : ∀ j ∈ B, 0 < j := by
      intro j hj
      rcases Multiset.mem_add.mp hj with hj | hj
      · exact hD j (Multiset.mem_of_le hRD hj)
      · simpa only [Multiset.mem_singleton.mp hj] using hmpos
    have hXm : mass X = (m : ℝ)⁻¹ := by
      dsimp [X]
      rw [hnm]
      exact compression_mass d m hdpos
    have hmass : mass B = mass D := by
      have he := congrArg mass hdecomp
      rw [mass_add, hXm] at he
      simpa [B, mass_add, mass] using he
    have hcomp : Lifts (R + X) B := by
      dsimp [X, B]
      rw [hnm]
      exact compression_lifts R d m hdpos
    have hDB : Lifts D B := hdecomp ▸ hcomp
    have hcards : R.card + d = D.card := by
      have he := congrArg Multiset.card hdecomp
      simpa [X] using he
    have hBc : B.card < k := by
      simp only [B, Multiset.card_add, Multiset.card_singleton]
      omega
    rcases ih B.card hBc B rfl hBpos with ⟨T, hTB, hT⟩ | ⟨F, hFpos, hFstable, hFmass, hBF⟩
    · obtain ⟨U, hUD, hUT⟩ := hDB T hTB
      exact Or.inl ⟨U, hUD, hUT.trans hT⟩
    · exact Or.inr ⟨F, hFpos, hFstable, hFmass.trans hmass, lifts_trans hDB hBF⟩
  · refine Or.inr ⟨D, hD, ?_, rfl, lifts_refl D⟩
    intro n hn
    refine ⟨htwo n hn, lt_of_not_ge ?_⟩
    intro hh
    exact hbad ⟨n, hn, hh⟩

def StableLogBound (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → Stable A → ∀ S : Multiset ℕ,
    Optimal A S → 0 < 1 - mass S → mass A ≤ C * (-Real.log (1 - mass S))

theorem logBound_of_stable {C : ℝ} (hC : 0 ≤ C) (h : StableLogBound C) :
    LogBound C := by
  intro A hA S hS hd
  rcases exists_stable_compression A hA with ⟨T, hTA, hT⟩ | ⟨B, hBpos, hBstable, hmass, hAB⟩
  · have hm := hS.2.2 T hTA (by rw [hT])
    rw [hT] at hm
    linarith
  · obtain ⟨T, hT⟩ := exists_optimal B
    obtain ⟨U, hUA, hUT⟩ := hAB T hT.1
    have hUhi : mass U ≤ 1 := by rw [hUT]; exact hT.2.1
    have hTS : mass T ≤ mass S := by simpa only [hUT] using hS.2.2 U hUA hUhi
    have hdT : 0 < 1 - mass T := by linarith
    have hb := h B hBpos hBstable T hT hdT
    have hlog : Real.log (1 - mass S) ≤ Real.log (1 - mass T) :=
      Real.log_le_log hd (by linarith)
    have hscale := mul_le_mul_of_nonneg_left (neg_le_neg hlog) hC
    rw [hmass] at hb
    exact hb.trans hscale

theorem logBound_iff_stable {C : ℝ} (hC : 0 ≤ C) : LogBound C ↔ StableLogBound C := by
  constructor
  · intro h A hA _ S hS hd
    exact h A hA S hS hd
  · exact logBound_of_stable hC

theorem canonical_iff_stableLogBound :
    canonicalStatement ↔ ∃ C : ℝ, 0 < C ∧ StableLogBound C := by
  rw [canonical_iff_logBound]
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, (logBound_iff_stable hC.le).mp h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, logBound_of_stable hC.le h⟩

theorem stable_of_le {A B : Multiset ℕ} (hA : Stable A) (hBA : B ≤ A) : Stable B := by
  intro n hn
  obtain ⟨hn2, hcount⟩ := hA n (Multiset.mem_of_le hBA hn)
  exact ⟨hn2, (Multiset.count_le_of_le n hBA).trans_lt hcount⟩

def StableTerminalLogBound (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → Stable A → ∀ S : Multiset ℕ,
    Optimal A S → 0 < 1 - mass S →
    (∀ n ∈ A, 1 - mass S < (n : ℝ)⁻¹) →
    mass A ≤ C * (-Real.log (1 - mass S))

theorem stableLogBound_of_stableTerminal {C : ℝ} (hC : 1 ≤ C)
    (h : StableTerminalLogBound C) : StableLogBound C := by
  intro A
  induction A using Multiset.strongInductionOn with
  | ih A ih =>
    intro hA hstable S hS hd
    classical
    by_cases hex : ∃ n ∈ A, (n : ℝ)⁻¹ ≤ 1 - mass S
    · obtain ⟨n, hn, hsmall⟩ := hex
      have hnpos := hA n hn
      have hw : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hnpos)
      obtain ⟨hS', hdef⟩ := optimal_erase_small hS hn hnpos hsmall
      have hd' : 0 < 1 - mass (S.erase n) := by rw [hdef]; linarith
      have hA' : ∀ k ∈ A.erase n, 0 < k := by
        intro k hk
        exact hA k (Multiset.mem_of_mem_erase hk)
      have hstable' := stable_of_le hstable (Multiset.erase_le n A)
      have hb := ih (A.erase n) (Multiset.erase_lt.mpr hn) hA' hstable' (S.erase n) hS' hd'
      have hgain : (n : ℝ)⁻¹ ≤
          Real.log (1 - mass (S.erase n)) - Real.log (1 - mass S) := by
        have hg := logarithmic_deletion_gain hd
          (show 1 - mass S ≤ 1 - mass (S.erase n) by rw [hdef]; linarith)
          (show 1 - mass (S.erase n) ≤ 1 by linarith [mass_nonneg (S.erase n)])
        rw [hdef] at hg ⊢
        linarith
      have hC0 : 0 ≤ C := le_trans zero_le_one hC
      have hscaled := mul_le_mul_of_nonneg_left hgain hC0
      have hpaid := mul_le_mul_of_nonneg_right hC hw.le
      have hm := mass_erase hn
      nlinarith
    · apply h A hA hstable S hS hd
      intro n hn
      apply lt_of_not_ge
      intro hnsmall
      exact hex ⟨n, hn, hnsmall⟩

theorem stableLogBound_iff_stableTerminal {C : ℝ} (hC : 1 ≤ C) :
    StableLogBound C ↔ StableTerminalLogBound C := by
  constructor
  · intro h A hA hstable S hS hd _
    exact h A hA hstable S hS hd
  · exact stableLogBound_of_stableTerminal hC

theorem canonical_iff_stableTerminalLogBound :
    canonicalStatement ↔ ∃ C : ℝ, 1 ≤ C ∧ StableTerminalLogBound C := by
  constructor
  · intro hroot
    obtain ⟨c, hc, h⟩ := canonical_iff_unconditional.mp hroot
    refine ⟨max 1 c⁻¹, le_max_left 1 c⁻¹, ?_⟩
    intro A hA _ S hS hd _
    exact logBound_of_endpoint hc (endpoint_of_unconditional hc h) A hA S hS hd
  · rintro ⟨C, hC, h⟩
    apply canonical_iff_stableLogBound.mpr
    exact ⟨C, lt_of_lt_of_le zero_lt_one hC, stableLogBound_of_stableTerminal hC h⟩

def RestrictedStableLogBound (P : ℕ → Prop) (C : ℝ) : Prop :=
  ∀ A : Multiset ℕ, (∀ n ∈ A, 0 < n) → Stable A → (∀ n ∈ A, P n) →
    ∀ S : Multiset ℕ, Optimal A S → 0 < 1 - mass S →
      mass A ≤ C * (-Real.log (1 - mass S))

theorem restricted_bound_on_subinventory {P : ℕ → Prop} {C : ℝ}
    (hC : 0 ≤ C) (h : RestrictedStableLogBound P C)
    {A B S : Multiset ℕ} (hA : ∀ n ∈ A, 0 < n) (hstable : Stable A)
    (hS : Optimal A S) (hd : 0 < 1 - mass S) (hBA : B ≤ A)
    (hP : ∀ n ∈ B, P n) : mass B ≤ C * (-Real.log (1 - mass S)) := by
  have hBpos : ∀ n ∈ B, 0 < n := fun n hn => hA n (Multiset.mem_of_le hBA hn)
  obtain ⟨T, hT⟩ := exists_optimal B
  have hTS := hS.2.2 T (hT.1.trans hBA) hT.2.1
  have hdT : 0 < 1 - mass T := by linarith
  have hb := h B hBpos (stable_of_le hstable hBA) hP T hT hdT
  have hlog := Real.log_le_log hd (show 1 - mass S ≤ 1 - mass T by linarith)
  exact hb.trans (mul_le_mul_of_nonneg_left (neg_le_neg hlog) hC)

theorem stableLogBound_of_partition (P : ℕ → Prop) [DecidablePred P]
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : RestrictedStableLogBound P C)
    (hnotP : RestrictedStableLogBound (fun n => ¬P n) D) : StableLogBound (C + D) := by
  intro A hA hstable S hS hd
  have hbP := restricted_bound_on_subinventory hC hP hA hstable hS hd
    (Multiset.filter_le P A) (fun n hn => (Multiset.mem_filter.mp hn).2)
  have hbN := restricted_bound_on_subinventory hD hnotP hA hstable hS hd
    (Multiset.filter_le (fun n => ¬P n) A) (fun n hn => (Multiset.mem_filter.mp hn).2)
  have he := congrArg mass (Multiset.filter_add_not P A)
  rw [mass_add] at he
  nlinarith

theorem canonical_iff_prime_composite_bounds :
    canonicalStatement ↔ ∃ Cp Cc : ℝ, 0 < Cp ∧ 0 < Cc ∧
      RestrictedStableLogBound Nat.Prime Cp ∧
      RestrictedStableLogBound (fun n => ¬Nat.Prime n) Cc := by
  constructor
  · intro hroot
    obtain ⟨C, hC, h⟩ := canonical_iff_stableLogBound.mp hroot
    refine ⟨C, C, hC, hC, ?_, ?_⟩
    · intro A hA hstable _ S hS hd
      exact h A hA hstable S hS hd
    · intro A hA hstable _ S hS hd
      exact h A hA hstable S hS hd
  · rintro ⟨Cp, Cc, hCp, hCc, hp, hc⟩
    apply canonical_iff_stableLogBound.mpr
    exact ⟨Cp + Cc, add_pos hCp hCc,
      stableLogBound_of_partition Nat.Prime hCp.le hCc.le hp hc⟩

/- Package the two already-proved reductions; this proves neither analytic estimate. -/
theorem proof :
    (canonicalStatement ↔ ∃ C : ℝ, 1 ≤ C ∧ StableTerminalLogBound C) ∧
  (canonicalStatement ↔ ∃ Cp Cc : ℝ, 0 < Cp ∧ 0 < Cc ∧
    RestrictedStableLogBound Nat.Prime Cp ∧
    RestrictedStableLogBound (fun n => ¬Nat.Prime n) Cc) :=
  ⟨canonical_iff_stableTerminalLogBound, canonical_iff_prime_composite_bounds⟩

end Submissions.J5P407NormalForm.Proof

#print axioms Submissions.J5P407NormalForm.Proof.stable_of_le
#print axioms Submissions.J5P407NormalForm.Proof.stableLogBound_of_stableTerminal
#print axioms Submissions.J5P407NormalForm.Proof.canonical_iff_stableTerminalLogBound
#print axioms Submissions.J5P407NormalForm.Proof.restricted_bound_on_subinventory
#print axioms Submissions.J5P407NormalForm.Proof.stableLogBound_of_partition
#print axioms Submissions.J5P407NormalForm.Proof.canonical_iff_prime_composite_bounds
