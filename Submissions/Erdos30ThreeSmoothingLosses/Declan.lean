import Mathlib.Tactic

/-
Finite-support Sidon convolution energy estimate, following Hou--Zhao,
Vector-valued smoothing for finite Sidon sets, arXiv:2607.01169v2, Lemma2.1.
The proof below directly injects off-diagonal convolution triples into kernel
pairs; no summability or modular embedding assumptions are required.
-/
namespace SidonConvolutionEnergy

/-- Every nonzero ordered difference in A has a unique representation. -/
def IsSidon (A : Finset ℤ) : Prop :=
  Set.InjOn (fun p : ℤ × ℤ => p.1 - p.2) (A.offDiag : Set (ℤ × ℤ))

/-- The difference definition is exactly the usual uniqueness of unordered
two-term sums; it imposes no stronger hidden Sidon hypothesis. -/
theorem isSidon_iff_unique_sums (A : Finset ℤ) :
    IsSidon A ↔
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h a ha b hb c hc d hd he
    by_cases hac : a = c
    · exact Or.inl ⟨hac, by omega⟩
    · have hdb : d ≠ b := by omega
      have hp : (a, c) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨ha, hc, hac⟩
      have hq : (d, b) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨hd, hb, hdb⟩
      have hh : (a, c) = (d, b) := h hp hq (by dsimp; omega)
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      exact Or.inr ⟨h1, h2.symm⟩
  · intro h p hp q hq he
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hc, hd, hcd⟩ := Finset.mem_offDiag.mp hq
    have hs : p.1 + q.2 = q.1 + p.2 := by
      change p.1 - p.2 = q.1 - q.2 at he
      omega
    rcases h p.1 ha q.2 hd q.1 hc p.2 hb hs with hh | hh
    · exact Prod.ext hh.1 hh.2.symm
    · exact (hab hh.1).elim

/-- A weighted injection may ignore source terms of weight zero. -/
theorem sum_le_of_inj_nonzero {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α → ℝ) (g : β → ℝ) (i : α → β)
    (hmaps : ∀ x ∈ s, f x ≠ 0 → i x ∈ t)
    (hinj : Set.InjOn i (s.filter (fun x => f x ≠ 0) : Set α))
    (hweight : ∀ x ∈ s, f x = g (i x))
    (hgnonneg : ∀ y ∈ t, 0 ≤ g y) :
    ∑ x ∈ s, f x ≤ ∑ y ∈ t, g y := by
  classical
  let S := s.filter (fun x => f x ≠ 0)
  calc
    ∑ x ∈ s, f x = ∑ x ∈ S, f x := (Finset.sum_filter_ne_zero s).symm
    _ = ∑ x ∈ S, g (i x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hweight x (Finset.mem_filter.mp hx).1
    _ = ∑ y ∈ S.image i, g y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ t, g y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hmaps x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
      · exact fun y hy _ => hgnonneg y hy

/-- A translated square sum over an arbitrary finite output domain is bounded
by the full finite kernel square sum. -/
theorem translated_square_sum_le (J B : Finset ℤ) (K : ℤ → ℝ)
    (hsupport : ∀ s, s ∉ B → K s = 0) (a : ℤ) :
    ∑ n ∈ J, K (n - a) ^ 2 ≤ ∑ s ∈ B, K s ^ 2 := by
  apply sum_le_of_inj_nonzero J B (fun n => K (n - a) ^ 2)
    (fun s => K s ^ 2) (fun n => n - a)
  · intro n hn hne
    by_contra hnot
    rw [hsupport _ hnot, zero_pow (by omega)] at hne
    exact hne rfl
  · intro x hx y hy he
    change x - a = y - a at he
    omega
  · intro x hx
    rfl
  · intro y hy
    positivity

/-- The Sidon property injects every off-diagonal convolution contribution
into a different ordered off-diagonal pair of kernel positions. -/
theorem off_diagonal_energy_le (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) :
    ∑ p ∈ A.offDiag, ∑ n ∈ J, K (n - p.1) * K (n - p.2) ≤
      ∑ p ∈ B.offDiag, K p.1 * K p.2 := by
  rw [← Finset.sum_product A.offDiag J
    (fun p => K (p.2 - p.1.1) * K (p.2 - p.1.2))]
  apply sum_le_of_inj_nonzero (A.offDiag ×ˢ J) B.offDiag
    (fun p => K (p.2 - p.1.1) * K (p.2 - p.1.2))
    (fun p => K p.1 * K p.2)
    (fun p => (p.2 - p.1.1, p.2 - p.1.2))
  · rintro ⟨⟨a, b⟩, n⟩ hp hne
    have hab := Finset.mem_offDiag.mp (Finset.mem_product.mp hp).1
    have habne : a ≠ b := hab.2.2
    apply Finset.mem_offDiag.mpr
    refine ⟨?_, ?_, ?_⟩
    · by_contra hnot
      simp [hsupport _ hnot] at hne
    · by_contra hnot
      simp [hsupport _ hnot] at hne
    · dsimp
      omega
  · rintro ⟨⟨a, b⟩, n⟩ hp ⟨⟨c, d⟩, m⟩ hq he
    have hpA := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hqA := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have he1 : n - a = m - c := congrArg Prod.fst he
    have he2 : n - b = m - d := congrArg Prod.snd he
    have hab : (a, b) = (c, d) := hA hpA hqA (by dsimp; omega)
    cases hab
    have hnm : n = m := by omega
    subst m
    rfl
  · intro p hp
    rfl
  · intro p hp
    exact mul_nonneg (hK _) (hK _)

/-- Exact diagonal/off-diagonal expansion of the convolution square. -/
theorem energy_split (A J : Finset ℤ) (K : ℤ → ℝ) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) =
      (∑ a ∈ A, ∑ n ∈ J, K (n - a) ^ 2) +
      ∑ p ∈ A.offDiag, ∑ n ∈ J, K (n - p.1) * K (n - p.2) := by
  calc
    _ = ∑ n ∈ J, ∑ p ∈ A ×ˢ A, K (n - p.1) * K (n - p.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
    _ = ∑ p ∈ A ×ˢ A, ∑ n ∈ J, K (n - p.1) * K (n - p.2) := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag A),
        Finset.sum_diag]
      simp only [pow_two]

/-- The off-diagonal mass of a kernel pair is its total squared mass minus
its diagonal square mass. -/
theorem kernel_pair_split (B : Finset ℤ) (K : ℤ → ℝ) :
    (∑ s ∈ B, K s) ^ 2 =
      (∑ s ∈ B, K s ^ 2) + ∑ p ∈ B.offDiag, K p.1 * K p.2 := by
  rw [pow_two, Finset.sum_mul_sum,
    ← Finset.sum_product B B (fun p => K p.1 * K p.2),
    ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag B),
    Finset.sum_diag]
  simp only [pow_two]

/-- Generic finite-support energy bound, including arbitrary finite output
truncations and empty Sidon sets. -/
theorem convolution_energy_le (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) ≤
      (∑ s ∈ B, K s) ^ 2 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K s ^ 2 := by
  rw [energy_split]
  have hdiag : (∑ a ∈ A, ∑ n ∈ J, K (n - a) ^ 2) ≤
      (A.card : ℝ) * ∑ s ∈ B, K s ^ 2 := by
    calc
      _ ≤ ∑ _a ∈ A, ∑ s ∈ B, K s ^ 2 :=
        Finset.sum_le_sum fun a ha => translated_square_sum_le J B K hsupport a
      _ = _ := by simp [nsmul_eq_mul]
  have hoff := off_diagonal_energy_le A J B K hA hK hsupport
  have hsplit := kernel_pair_split B K
  nlinarith

/-- Hou--Zhao's unit-mass scalar energy estimate (their Eq.5 before mixing). -/
theorem probability_kernel_energy_le (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) (hmass : ∑ s ∈ B, K s = 1) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) ≤
      1 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K s ^ 2 := by
  simpa [hmass] using convolution_energy_le A J B K hA hK hsupport

/-- Averaging preserves the sharp diagonal correction; no individual kernel
needs its own boundary covering inequality. -/
theorem weighted_probability_kernel_energy_le {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K : R → ℤ → ℝ) (lam : R → ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ J, (∑ a ∈ A, K r (n - a)) ^ 2) ≤
      1 + ((A.card : ℝ) - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2 := by
  calc
    _ ≤ ∑ r, lam r *
        (1 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K r s ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (probability_kernel_energy_le A J B (K r) hA (hK r)
          (hsupport r) (hmass r)) (hlam r)
    _ = _ := by
      simp_rw [mul_add, mul_one]
      rw [Finset.sum_add_distrib, hlammass]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

#print axioms probability_kernel_energy_le
#print axioms weighted_probability_kernel_energy_le
end SidonConvolutionEnergy


/-
The finite Hilbert-space step of Hou--Zhao, arXiv:2607.01169v2, Lemma2.1.
All analytic objects are finite sums. Concrete boundary interpolation and
kernel block-mass identities are supplied separately.
-/
namespace SidonFiniteSmoothing
open SidonConvolutionEnergy

/-- Weighted Cauchy--Schwarz on a finite direct sum, allowing signed weights Q
but requiring nonnegative mixing coefficients. -/
theorem weighted_cauchy_schwarz {R : Type*} [Fintype R]
    (J : Finset ℤ) (lam : R → ℝ) (Q u : R → ℤ → ℝ)
    (hlam : ∀ r, 0 ≤ lam r) :
    (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) ^ 2 ≤
      (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) *
      (∑ r, lam r * ∑ n ∈ J, u r n ^ 2) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ J)
    (fun p : R × ℤ => Real.sqrt (lam p.1) * Q p.1 p.2)
    (fun p : R × ℤ => Real.sqrt (lam p.1) * u p.1 p.2)
  have hp (r : R) (n : ℤ) :
      (Real.sqrt (lam r) * Q r n) * (Real.sqrt (lam r) * u r n) =
      lam r * (Q r n * u r n) := by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hlam r)]
  have hs (r : R) : Real.sqrt (lam r) ^ 2 = lam r := Real.sq_sqrt (hlam r)
  simp only [Finset.sum_product] at hcs
  simp_rw [hp, mul_pow, hs, ← Finset.mul_sum] at hcs
  exact hcs

/-- Summing the pointwise cover over A gives the weighted convolution pairing. -/
theorem cardinal_le_pairing {R : Type*} [Fintype R]
    (A J : Finset ℤ) (lam : R → ℝ) (Q K : R → ℤ → ℝ)
    (hcover : ∀ x ∈ A,
      1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x)) :
    (A.card : ℝ) ≤
      ∑ r, lam r * ∑ n ∈ J, Q r n * (∑ x ∈ A, K r (n - x)) := by
  calc
    (A.card : ℝ) = ∑ _x ∈ A, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ A, ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x) :=
      Finset.sum_le_sum fun x hx => hcover x hx
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]

/-- The exact finite smoothing inequality. Interval placement of A and the
boundary construction are needed only to establish the explicit cover/norm
hypotheses; this statement does not conceal either of those obligations. -/
theorem finite_smoothing_bound {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K Q : R → ℤ → ℝ) (lam : R → ℝ)
    (N a b H : ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1)
    (hcover : ∀ x ∈ A,
      1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x))
    (hQnorm : (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) = N + b * H - 1)
    (hKnorm : (∑ r, lam r * ∑ s ∈ B, K r s ^ 2) = a / H) :
    (A.card : ℝ) ^ 2 ≤
      (N + b * H - 1) * (1 + a * ((A.card : ℝ) - 1) / H) := by
  let u : R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
  have hpair := cardinal_le_pairing A J lam Q K hcover
  have hcard : 0 ≤ (A.card : ℝ) := by positivity
  have hsquare : (A.card : ℝ) ^ 2 ≤
      (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) ^ 2 := by
    have hp : 0 ≤
        ((∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - (A.card : ℝ)) *
        ((∑ r, lam r * ∑ n ∈ J, Q r n * u r n) + (A.card : ℝ)) := by
      apply mul_nonneg <;> dsimp [u] <;> linarith
    nlinarith
  have hcs := weighted_cauchy_schwarz J lam Q u hlam
  have henergy := weighted_probability_kernel_energy_le A J B K lam
    hA hK hsupport hmass hlam hlammass
  rw [hKnorm] at henergy
  have hnormpos : 0 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 := by
    apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hlam r) (Finset.sum_nonneg fun n hn => sq_nonneg _)
  calc
    (A.card : ℝ) ^ 2 ≤
        (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) *
        (∑ r, lam r * ∑ n ∈ J, u r n ^ 2) := hsquare.trans hcs
    _ ≤ (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) *
        (1 + ((A.card : ℝ) - 1) * (a / H)) :=
      mul_le_mul_of_nonneg_left henergy hnormpos
    _ = _ := by rw [hQnorm]; ring

#print axioms finite_smoothing_bound
end SidonFiniteSmoothing

/-!
Retain missing-difference energy and distance from the Cauchy--Schwarz extremizer.
All quantities are finite sums. No asymptotic inference is built into the result.
-/
namespace SidonDefectStability
open SidonConvolutionEnergy SidonFiniteSmoothing

noncomputable def differences (A : Finset ℤ) : Finset ℤ :=
  A.offDiag.image (fun p => p.1 - p.2)

noncomputable def missingPairs (A B : Finset ℤ) : Finset (ℤ × ℤ) :=
  B.offDiag.filter (fun p => p.2 - p.1 ∉ differences A)

noncomputable def missingEnergy (A B : Finset ℤ) (K : ℤ → ℝ) : ℝ :=
  ∑ p ∈ missingPairs A B, K p.1 * K p.2

theorem missingEnergy_nonneg (A B : Finset ℤ) (K : ℤ → ℝ)
    (hK : ∀ s, 0 ≤ K s) : 0 ≤ missingEnergy A B K := by
  exact Finset.sum_nonneg fun p hp => mul_nonneg (hK _) (hK _)

/-- A missing difference excludes an entire autocorrelation fibre. -/
theorem off_diagonal_energy_with_defect (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) :
    (∑ p ∈ A.offDiag, ∑ n ∈ J, K (n - p.1) * K (n - p.2)) +
      missingEnergy A B K ≤ ∑ p ∈ B.offDiag, K p.1 * K p.2 := by
  classical
  have hoff : (∑ p ∈ A.offDiag, ∑ n ∈ J, K (n - p.1) * K (n - p.2)) ≤
      ∑ p ∈ B.offDiag \ missingPairs A B, K p.1 * K p.2 := by
    rw [← Finset.sum_product A.offDiag J
      (fun p => K (p.2 - p.1.1) * K (p.2 - p.1.2))]
    apply sum_le_of_inj_nonzero (A.offDiag ×ˢ J) (B.offDiag \ missingPairs A B)
      (fun p => K (p.2 - p.1.1) * K (p.2 - p.1.2))
      (fun p => K p.1 * K p.2)
      (fun p => (p.2 - p.1.1, p.2 - p.1.2))
    · rintro ⟨⟨a, b⟩, n⟩ hp hne
      have hpA := (Finset.mem_product.mp hp).1
      have hab := Finset.mem_offDiag.mp hpA
      have habne : a ≠ b := hab.2.2
      apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_offDiag.mpr
        refine ⟨?_, ?_, ?_⟩
        · by_contra hnot
          simp [hsupport _ hnot] at hne
        · by_contra hnot
          simp [hsupport _ hnot] at hne
        · dsimp
          omega
      · intro hm
        have hmissing := (Finset.mem_filter.mp hm).2
        apply hmissing
        apply Finset.mem_image.mpr
        exact ⟨(a,b), hpA, by dsimp; omega⟩
    · rintro ⟨⟨a, b⟩, n⟩ hp ⟨⟨c, d⟩, m⟩ hq he
      have hpA := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      have hqA := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
      have he1 : n - a = m - c := congrArg Prod.fst he
      have he2 : n - b = m - d := congrArg Prod.snd he
      have hab : (a, b) = (c, d) := hA hpA hqA (by dsimp; omega)
      cases hab
      have hnm : n = m := by omega
      subst m
      rfl
    · intro p hp
      rfl
    · intro p hp
      exact mul_nonneg (hK _) (hK _)
  have hsub : missingPairs A B ⊆ B.offDiag := Finset.filter_subset _ _
  have hsplit := Finset.sum_sdiff hsub (f := fun p : ℤ × ℤ => K p.1 * K p.2)
  dsimp [missingEnergy]
  linarith

/-- Strengthened energy bound, allowing arbitrary output truncation. -/
theorem convolution_energy_with_defect (A J B : Finset ℤ) (K : ℤ → ℝ)
    (hA : IsSidon A) (hK : ∀ s, 0 ≤ K s)
    (hsupport : ∀ s, s ∉ B → K s = 0) :
    (∑ n ∈ J, (∑ a ∈ A, K (n - a)) ^ 2) + missingEnergy A B K ≤
      (∑ s ∈ B, K s) ^ 2 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K s ^ 2 := by
  rw [energy_split]
  have hdiag : (∑ a ∈ A, ∑ n ∈ J, K (n - a) ^ 2) ≤
      (A.card : ℝ) * ∑ s ∈ B, K s ^ 2 := by
    calc
      _ ≤ ∑ _a ∈ A, ∑ s ∈ B, K s ^ 2 :=
        Finset.sum_le_sum fun a ha => translated_square_sum_le J B K hsupport a
      _ = _ := by simp [nsmul_eq_mul]
  have hoff := off_diagonal_energy_with_defect A J B K hA hK hsupport
  have hsplit := kernel_pair_split B K
  nlinarith

theorem weighted_energy_with_defect {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K : R → ℤ → ℝ) (lam : R → ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ J, (∑ a ∈ A, K r (n - a)) ^ 2) +
      (∑ r, lam r * missingEnergy A B (K r)) ≤
      1 + ((A.card : ℝ) - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2 := by
  calc
    _ = ∑ r, lam r * ((∑ n ∈ J, (∑ a ∈ A, K r (n - a)) ^ 2) +
        missingEnergy A B (K r)) := by simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ r, lam r * (1 + ((A.card : ℝ) - 1) * ∑ s ∈ B, K r s ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (hlam r)
      simpa [hmass] using convolution_energy_with_defect A J B (K r) hA (hK r) (hsupport r)
    _ = _ := by
      simp_rw [mul_add, mul_one]
      rw [Finset.sum_add_distrib, hlammass, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Finite square completion, with no sign assumptions on Q or u. -/
theorem weighted_residual_identity {R : Type*} [Fintype R]
    (J : Finset ℤ) (lam : R → ℝ) (Q u : R → ℤ → ℝ) (t : ℝ) :
    (∑ r, lam r * ∑ n ∈ J, (u r n - t * Q r n) ^ 2) =
      (∑ r, lam r * ∑ n ∈ J, u r n ^ 2) -
      2 * t * (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) +
      t ^ 2 * (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2) := by
  have hp (r : R) (n : ℤ) :
      (u r n - t * Q r n) ^ 2 = u r n ^ 2 - 2 * t * (Q r n * u r n) + t ^ 2 * Q r n ^ 2 := by ring
  simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring

/-- Exact deficit budget, retaining Cauchy residual and cover surplus. Uniform
in every finite kernel family, support, truncation, and nonnegative mixture. -/
theorem finite_smoothing_deficit_budget {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K Q : R → ℤ → ℝ) (lam : R → ℝ) (q : ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1)
    (hq : 0 < q) (hQnorm : ∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 = q) :
    let k : ℝ := A.card
    let u : R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
    let D := ∑ r, lam r * missingEnergy A B (K r)
    let V := ∑ r, lam r * ∑ n ∈ J, (u r n - (k / q) * Q r n) ^ 2
    let C := (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - k
    k ^ 2 + q * (D + V) + 2 * k * C ≤
      q * (1 + (k - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2) := by
  dsimp only
  let k : ℝ := A.card
  let u : R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
  have hid := weighted_residual_identity J lam Q u (k / q)
  rw [hQnorm] at hid
  have he := mul_le_mul_of_nonneg_left
    (weighted_energy_with_defect A J B K lam hA hK hsupport hmass hlam hlammass) hq.le
  change k ^ 2 + q * ((∑ r, lam r * missingEnergy A B (K r)) +
    (∑ r, lam r * ∑ n ∈ J, (u r n - k / q * Q r n) ^ 2)) +
    2 * k * ((∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - k) ≤ _
  rw [hid]
  convert he using 1 <;> dsimp [k, u] at * <;> try rfl
  field_simp [ne_of_gt hq]
  ring


/-- The cover makes every retained loss nonnegative. -/
theorem finite_smoothing_with_defect {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K Q : R → ℤ → ℝ) (lam : R → ℝ) (q : ℝ)
    (hA : IsSidon A) (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1)
    (hq : 0 < q) (hQnorm : ∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 = q)
    (hcover : ∀ x ∈ A,
      1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x)) :
    let k : ℝ := A.card
    let u : R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
    let D := ∑ r, lam r * missingEnergy A B (K r)
    let V := ∑ r, lam r * ∑ n ∈ J, (u r n - (k / q) * Q r n) ^ 2
    k ^ 2 + q * (D + V) ≤
      q * (1 + (k - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2) := by
  have hb := finite_smoothing_deficit_budget A J B K Q lam q hA hK
    hsupport hmass hlam hlammass hq hQnorm
  have hp := cardinal_le_pairing A J lam Q K hcover
  have hnonneg : 0 ≤ 2 * (A.card : ℝ) *
      ((∑ r, lam r * ∑ n ∈ J, Q r n * (∑ x ∈ A, K r (n - x))) - A.card) := by
    apply mul_nonneg
    · positivity
    · linarith
  dsimp only at hb ⊢
  linarith

/-- Any local block discrepancy is controlled by the same residual. -/
theorem local_residual_discrepancy (J T : Finset ℤ) (hT : T ⊆ J)
    (f : ℤ → ℝ) :
    (∑ n ∈ T, f n) ^ 2 ≤ (T.card : ℝ) * ∑ n ∈ J, f n ^ 2 := by
  have hcs : (∑ n ∈ T, f n) ^ 2 ≤ (T.card : ℝ) * ∑ n ∈ T, f n ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) f
  have hs : (∑ n ∈ T, f n ^ 2) ≤ ∑ n ∈ J, f n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun n hn _ => sq_nonneg _)
  exact hcs.trans (mul_le_mul_of_nonneg_left hs (by positivity))


/-- Cover surplus bounds the number of actual points on inactive constraints.
The application takes G(x)=Σ_r λ_r Σ_n Q_r(n)K_r(n-x). -/
theorem cover_surplus_subset (A T : Finset ℤ) (hT : T ⊆ A) (G : ℤ → ℝ)
    (delta : ℝ) (hG : ∀ x ∈ A, 1 ≤ G x) (hgap : ∀ x ∈ T, 1 + delta ≤ G x) :
    delta * (T.card : ℝ) ≤ (∑ x ∈ A, G x) - A.card := by
  calc
    _ = ∑ _x ∈ T, delta := by simp [mul_comm]
    _ ≤ ∑ x ∈ T, (G x - 1) := Finset.sum_le_sum fun x hx => by linarith [hgap x hx]
    _ ≤ ∑ x ∈ A, (G x - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun x hx _ => by linarith [hG x hx])
    _ = _ := by simp [Finset.sum_sub_distrib]


/-- Public target: the ordinary unique-sums Sidon hypothesis gives an exact
finite budget for THREE explicitly nonnegative losses. No interval, kernel
shape, asymptotic threshold, or boundary convention is hidden in the premise. -/
theorem sidon_three_nonnegative_losses {R : Type*} [Fintype R]
    (A J B : Finset ℤ) (K Q : R → ℤ → ℝ) (lam : R → ℝ) (q : ℝ)
    (hA : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    (hK : ∀ r s, 0 ≤ K r s)
    (hsupport : ∀ r s, s ∉ B → K r s = 0)
    (hmass : ∀ r, ∑ s ∈ B, K r s = 1)
    (hlam : ∀ r, 0 ≤ lam r) (hlammass : ∑ r, lam r = 1)
    (hq : 0 < q) (hQnorm : ∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 = q)
    (hcover : ∀ x ∈ A,
      1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x)) :
    let k : ℝ := A.card
    let u : R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
    let D := ∑ r, lam r * missingEnergy A B (K r)
    let V := ∑ r, lam r * ∑ n ∈ J, (u r n - (k / q) * Q r n) ^ 2
    let C := (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - k
    0 ≤ D ∧ 0 ≤ V ∧ 0 ≤ C ∧
      k ^ 2 + q * (D + V) + 2 * k * C ≤
        q * (1 + (k - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hlam r) (missingEnergy_nonneg A B (K r) (hK r))
  · apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hlam r) (Finset.sum_nonneg fun n hn => sq_nonneg _)
  · have hp := cardinal_le_pairing A J lam Q K hcover
    linarith
  · exact finite_smoothing_deficit_budget A J B K Q lam q
      ((isSidon_iff_unique_sums A).mpr hA) hK hsupport hmass hlam hlammass hq hQnorm

end SidonDefectStability
#print axioms SidonDefectStability.convolution_energy_with_defect
#print axioms SidonDefectStability.finite_smoothing_deficit_budget

namespace SidonKernelCompatibility
open SidonConvolutionEnergy SidonDefectStability

noncomputable def conv (B : Finset ℤ) (K f : ℤ → ℝ) (n : ℤ) : ℝ :=
  ∑ s ∈ B, K s * f (n - s)

/-- Pointwise Jensen for a finite probability kernel, proved by finite Cauchy. -/
theorem conv_square_le (B : Finset ℤ) (K f : ℤ → ℝ)
    (hK : ∀ s, 0 ≤ K s) (hmass : ∑ s ∈ B, K s = 1) (n : ℤ) :
    conv B K f n ^ 2 ≤ ∑ s ∈ B, K s * f (n - s) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B
    (fun s => Real.sqrt (K s)) (fun s => Real.sqrt (K s) * f (n - s))
  have hp (s : ℤ) : Real.sqrt (K s) * (Real.sqrt (K s) * f (n-s)) = K s * f (n-s) := by
    rw [← mul_assoc, Real.mul_self_sqrt (hK s)]
  simp_rw [hp, mul_pow, Real.sq_sqrt (hK _)] at hcs
  simpa [conv, hmass] using hcs

/-- Finite Young contraction. The output domain T is arbitrary; f only needs
support in J. Consequently an enlarged convolution support is allowed. -/
theorem conv_energy_le (B J T : Finset ℤ) (K f : ℤ → ℝ)
    (hK : ∀ s, 0 ≤ K s) (hmass : ∑ s ∈ B, K s = 1)
    (hf : ∀ n, n ∉ J → f n = 0) :
    (∑ n ∈ T, conv B K f n ^ 2) ≤ ∑ n ∈ J, f n ^ 2 := by
  calc
    _ ≤ ∑ n ∈ T, ∑ s ∈ B, K s * f (n - s) ^ 2 :=
      Finset.sum_le_sum fun n hn => conv_square_le B K f hK hmass n
    _ = ∑ s ∈ B, K s * ∑ n ∈ T, f (n - s) ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ s ∈ B, K s * ∑ n ∈ J, f n ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (translated_square_sum_le T J f hf s) (hK s)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Finite probability-kernel commutativity, obtained without infinite sums. -/
theorem conv_kernel_comm (B : Finset ℤ) (K L : ℤ → ℝ)
    (hK : ∀ s, 0 ≤ K s) (hL : ∀ s, 0 ≤ L s)
    (hKs : ∀ s, s ∉ B → K s = 0) (hLs : ∀ s, s ∉ B → L s = 0)
    (n : ℤ) : conv B K L n = conv B L K n := by
  have hle (K L : ℤ → ℝ) (hK : ∀ s, 0 ≤ K s) (hL : ∀ s, 0 ≤ L s)
      (hLs : ∀ s, s ∉ B → L s = 0) : conv B K L n ≤ conv B L K n := by
    apply sum_le_of_inj_nonzero B B (fun s => K s * L (n-s))
      (fun s => L s * K (n-s)) (fun s => n-s)
    · intro s hs hne
      by_contra hnot
      simp [hLs _ hnot] at hne
    · intro s hs t ht he
      dsimp at he
      omega
    · intro s hs
      have he : n - (n - s) = s := by omega
      rw [he, mul_comm]
    · intro s hs
      exact mul_nonneg (hL s) (hK _)
  exact le_antisymm (hle K L hK hL hLs) (hle L K hL hK hKs)

/-- The two actual smoothed counting functions come from the SAME set A. -/
theorem counting_convolution_comm (A B : Finset ℤ) (K L : ℤ → ℝ)
    (hK : ∀ s, 0 ≤ K s) (hL : ∀ s, 0 ≤ L s)
    (hKs : ∀ s, s ∉ B → K s = 0) (hLs : ∀ s, s ∉ B → L s = 0)
    (n : ℤ) :
    conv B L (fun z => ∑ a ∈ A, K (z-a)) n =
      conv B K (fun z => ∑ a ∈ A, L (z-a)) n := by
  unfold conv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := B) (t := A), Finset.sum_comm (s := B) (t := A)]
  apply Finset.sum_congr rfl
  intro a ha
  have hsub (s : ℤ) : n - s - a = (n-a) - s := by omega
  simp_rw [hsub]
  exact conv_kernel_comm B L K hL hK hLs hKs (n-a)

/-- Basic linearity, used to transfer commutativity to residuals. -/
theorem conv_residual (B : Finset ℤ) (K u Q : ℤ → ℝ) (t : ℝ) (n : ℤ) :
    conv B K (fun z => u z - t * Q z) n = conv B K u n - t * conv B K Q n := by
  unfold conv
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  ring


/-- Sharp two-channel inequality before applying Young contraction. -/
theorem weighted_difference_energy_le (T : Finset ℤ) (f g : ℤ → ℝ)
    (lam eta : ℝ) :
    lam * eta * (∑ n ∈ T, (f n - g n) ^ 2) ≤
      (lam + eta) * (lam * (∑ n ∈ T, f n ^ 2) + eta * (∑ n ∈ T, g n ^ 2)) := by
  have hp (n : ℤ) : lam * eta * (f n - g n) ^ 2 ≤
      (lam + eta) * (lam * f n ^ 2 + eta * g n ^ 2) := by
    nlinarith [sq_nonneg (lam * f n + eta * g n)]
  have hs := Finset.sum_le_sum (fun n hn => hp n : ∀ n ∈ T, _)
  simpa only [Finset.mul_sum, Finset.sum_add_distrib, mul_add] using hs

/-- A precise compatibility lower bound, with no roots or denominators.
For positive lam, eta, divide by lam+eta to obtain the usual sharp coefficient. -/
theorem residual_compatibility_bound (B J T : Finset ℤ) (K L f g : ℤ → ℝ)
    (lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hK : ∀ s, 0 ≤ K s) (hL : ∀ s, 0 ≤ L s)
    (hmK : ∑ s ∈ B, K s = 1) (hmL : ∑ s ∈ B, L s = 1)
    (hf : ∀ n, n ∉ J → f n = 0) (hg : ∀ n, n ∉ J → g n = 0) :
    lam * eta * (∑ n ∈ T, (conv B L f n - conv B K g n) ^ 2) ≤
      (lam + eta) * (lam * (∑ n ∈ J, f n ^ 2) + eta * (∑ n ∈ J, g n ^ 2)) := by
  have hfE := conv_energy_le B J T L f hL hmL hf
  have hgE := conv_energy_le B J T K g hK hmK hg
  exact (weighted_difference_energy_le T (conv B L f) (conv B K g) lam eta).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hfE hlam) (mul_le_mul_of_nonneg_left hgE heta))
      (add_nonneg hlam heta))

/-- Honest support condition for the actual counting convolution. -/
theorem counting_support (A B J : Finset ℤ) (K : ℤ → ℝ)
    (hKs : ∀ s, s ∉ B → K s = 0)
    (hAB : ∀ a ∈ A, ∀ s ∈ B, a + s ∈ J) :
    ∀ n, n ∉ J → (∑ a ∈ A, K (n-a)) = 0 := by
  intro n hn
  apply Finset.sum_eq_zero
  intro a ha
  apply hKs
  intro hb
  have hx := hAB a ha (n-a) hb
  apply hn
  simpa using hx

/-- Quantitative compatibility for actual counting functions of A. No Sidon
hypothesis is needed here; the Sidon constraint enters the deficit budget. -/
theorem actual_counting_compatibility_bound (A B J T : Finset ℤ)
    (K L Q W : ℤ → ℝ) (t lam eta : ℝ) (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hK : ∀ s, 0 ≤ K s) (hL : ∀ s, 0 ≤ L s)
    (hKs : ∀ s, s ∉ B → K s = 0) (hLs : ∀ s, s ∉ B → L s = 0)
    (hmK : ∑ s ∈ B, K s = 1) (hmL : ∑ s ∈ B, L s = 1)
    (hQs : ∀ n, n ∉ J → Q n = 0) (hWs : ∀ n, n ∉ J → W n = 0)
    (hAB : ∀ a ∈ A, ∀ s ∈ B, a + s ∈ J) :
    lam * eta * t ^ 2 * (∑ n ∈ T, (conv B L Q n - conv B K W n) ^ 2) ≤
      (lam + eta) *
        (lam * (∑ n ∈ J, ((∑ a ∈ A, K (n-a)) - t * Q n) ^ 2) +
         eta * (∑ n ∈ J, ((∑ a ∈ A, L (n-a)) - t * W n) ^ 2)) := by
  let f : ℤ → ℝ := fun n => (∑ a ∈ A, K (n-a)) - t * Q n
  let g : ℤ → ℝ := fun n => (∑ a ∈ A, L (n-a)) - t * W n
  have hf : ∀ n, n ∉ J → f n = 0 := by
    intro n hn
    simp [f, counting_support A B J K hKs hAB n hn, hQs n hn]
  have hg : ∀ n, n ∉ J → g n = 0 := by
    intro n hn
    simp [g, counting_support A B J L hLs hAB n hn, hWs n hn]
  have hp (n : ℤ) : (conv B L f n - conv B K g n) ^ 2 =
      t ^ 2 * (conv B L Q n - conv B K W n) ^ 2 := by
    dsimp [f, g]
    rw [conv_residual, conv_residual, counting_convolution_comm A B K L hK hL hKs hLs n]
    ring
  have hb := residual_compatibility_bound B J T K L f g lam eta hlam heta hK hL hmK hmL hf hg
  simp_rw [hp, ← Finset.mul_sum] at hb
  simpa only [f, g, mul_assoc] using hb

/-- Common dual sources automatically pass the compatibility test. This is
why exact KKT-optimal cover profiles cannot yield a commutativity gain. -/
theorem common_source_compatibility (U B : Finset ℤ) (mu K L : ℤ → ℝ)
    (hK : ∀ s, 0 ≤ K s) (hL : ∀ s, 0 ≤ L s)
    (hKs : ∀ s, s ∉ B → K s = 0) (hLs : ∀ s, s ∉ B → L s = 0)
    (n : ℤ) :
    conv B L (fun z => ∑ a ∈ U, mu a * K (z-a)) n =
      conv B K (fun z => ∑ a ∈ U, mu a * L (z-a)) n := by
  unfold conv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := B) (t := U), Finset.sum_comm (s := B) (t := U)]
  apply Finset.sum_congr rfl
  intro a ha
  have hsub (s : ℤ) : n - s - a = (n-a) - s := by omega
  simp_rw [hsub]
  calc
    _ = mu a * conv B L K (n-a) := by
      rw [conv, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = mu a * conv B K L (n-a) := by rw [conv_kernel_comm B L K hL hK hLs hKs]
    _ = _ := by
      rw [conv, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring

end SidonKernelCompatibility
#print axioms SidonKernelCompatibility.conv_energy_le
#print axioms SidonKernelCompatibility.counting_convolution_comm

#print axioms SidonDefectStability.finite_smoothing_with_defect
#print axioms SidonDefectStability.local_residual_discrepancy
#print axioms SidonKernelCompatibility.actual_counting_compatibility_bound
#print axioms SidonKernelCompatibility.common_source_compatibility

#print axioms SidonDefectStability.cover_surplus_subset

#print axioms SidonDefectStability.sidon_three_nonnegative_losses

namespace Submissions.Erdos30ThreeSmoothingLosses.Declan
open Finset
noncomputable def differences (A : Finset ℤ) : Finset ℤ :=
  A.offDiag.image (fun p => p.1 - p.2)
noncomputable def missingPairs (A B : Finset ℤ) : Finset (ℤ × ℤ) :=
  B.offDiag.filter (fun p => p.2 - p.1 ∉ differences A)
noncomputable def missingEnergy (A B : Finset ℤ) (K : ℤ → ℝ) : ℝ :=
  ∑ p ∈ missingPairs A B, K p.1 * K p.2

theorem proof : ∀ (R : ℕ) (A J B : Finset ℤ) (K Q : Fin R → ℤ → ℝ)
    (lam : Fin R → ℝ) (q : ℝ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
    (∀ r s, 0 ≤ K r s) →
    (∀ r s, s ∉ B → K r s = 0) →
    (∀ r, ∑ s ∈ B, K r s = 1) →
    (∀ r, 0 ≤ lam r) → (∑ r, lam r = 1) →
    0 < q → (∑ r, lam r * ∑ n ∈ J, Q r n ^ 2 = q) →
    (∀ x ∈ A, 1 ≤ ∑ r, lam r * ∑ n ∈ J, Q r n * K r (n - x)) →
    let k : ℝ := A.card
    let u : Fin R → ℤ → ℝ := fun r n => ∑ x ∈ A, K r (n - x)
    let D := ∑ r, lam r * missingEnergy A B (K r)
    let V := ∑ r, lam r * ∑ n ∈ J, (u r n - (k / q) * Q r n) ^ 2
    let C := (∑ r, lam r * ∑ n ∈ J, Q r n * u r n) - k
    0 ≤ D ∧ 0 ≤ V ∧ 0 ≤ C ∧
      k ^ 2 + q * (D + V) + 2 * k * C ≤
        q * (1 + (k - 1) * ∑ r, lam r * ∑ s ∈ B, K r s ^ 2) := by
  intro R A J B K Q lam q hA hK hsupport hmass hlam hlammass hq hQnorm hcover
  exact SidonDefectStability.sidon_three_nonnegative_losses A J B K Q lam q
    hA hK hsupport hmass hlam hlammass hq hQnorm hcover
end Submissions.Erdos30ThreeSmoothingLosses.Declan
