import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Interval


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


namespace SidonFiniteSmoothing

/-- Exact finite support reindexing for the convolution pairing. Q may be
signed; no inequality or positivity assumption is used. -/
theorem sum_shift_support (J B : Finset ℤ) (K Q : ℤ → ℝ) (x : ℤ)
    (hsupport : ∀ s, s ∉ B → K s = 0)
    (htranslate : ∀ s ∈ B, x + s ∈ J) :
    (∑ n ∈ J, Q n * K (n - x)) = ∑ s ∈ B, Q (x + s) * K s := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _ _ => n - x)
  · intro n hn hne
    by_contra hnot
    rw [hsupport _ hnot, mul_zero] at hne
    exact hne rfl
  · intro n hn hne m hm hme he
    omega
  · intro s hs hne
    refine ⟨x + s, htranslate s hs, ?_, ?_⟩
    · simpa using hne
    · omega
  · intro n hn hne
    have he : x + (n - x) = n := by omega
    rw [he]

/-- Nat-indexed boundary sums identify exactly with their integer intervals. -/
theorem sum_int_Ico_nat (M : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Finset.Ico (0 : ℤ) (M : ℤ), f z) =
      ∑ n ∈ Finset.range M, f (n : ℤ) := by
  classical
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ico]
    omega
  · intro n hn m hm he
    omega
  · intro z hz
    simp only [Finset.mem_Ico] at hz
    refine ⟨z.toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

#print axioms sum_shift_support
#print axioms sum_int_Ico_nat
end SidonFiniteSmoothing


namespace SidonBoundary

open scoped BigOperators
set_option linter.unusedSimpArgs false

theorem sum_range_blocks (m h : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range (m*h), f s =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range h, f (i*h+j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

theorem div_block (q h t : ℕ) (hh : 0 < h) (ht : t < h) : (q*h+t)/h = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right t q hh, Nat.div_eq_of_lt ht]
  simp

theorem div_shifted_block (q i h t j : ℕ) (hh : 0 < h) :
    (q*h+t+(i*h+j))/h = q+i+(t+j)/h := by
  have heq : q*h+t+(i*h+j) = (t+j)+(q+i)*h := by ring
  rw [heq, Nat.add_mul_div_right _ _ hh]
  omega

theorem block_weight_sum (h t a : ℕ) (hh : 0 < h) (ht : t < h) (w : ℕ → ℝ) :
    (∑ j ∈ Finset.range h, w (a+(t+j)/h)) =
      ((h:ℝ)-t)*w a + (t:ℝ)*w (a+1) := by
  have hleft : ∑ j ∈ Finset.range (h-t), w (a+(t+j)/h) = (h-t:ℕ)*w a := by
    calc
      _ = ∑ _j ∈ Finset.range (h-t), w a := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [Nat.div_eq_of_lt (by omega : t+j<h), Nat.add_zero]
      _ = _ := by simp
  have hright : ∑ j ∈ Finset.range t, w (a+(t+(h-t+j))/h) = (t:ℝ)*w (a+1) := by
    calc
      _ = ∑ _j ∈ Finset.range t, w (a+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have heq : t+(h-t+j) = h+j := by omega
        rw [heq, Nat.add_div_left j hh, Nat.div_eq_of_lt (by omega : j<h)]
      _ = _ := by simp
  calc
    _ = (∑ j ∈ Finset.range (h-t), w (a+(t+j)/h)) +
        ∑ j ∈ Finset.range t, w (a+(t+(h-t+j))/h) := by
      simpa only [Nat.sub_add_cancel ht.le] using
        Finset.sum_range_add (fun j => w (a+(t+j)/h)) (h-t) t
    _ = _ := by rw [hleft, hright, Nat.cast_sub ht.le]

theorem interpolation (m h q t : ℕ) (hh : 0 < h) (ht : t < h) (p w : ℕ → ℝ) :
    (∑ s ∈ Finset.range (m*h), (p (s/h) / h) * w ((q*h+t+s)/h)) =
      (1-(t:ℝ)/h) * (∑ i ∈ Finset.range m, p i*w (q+i)) +
      ((t:ℝ)/h) * (∑ i ∈ Finset.range m, p i*w (q+i+1)) := by
  rw [sum_range_blocks]
  have hR : (h:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  calc
    _ = ∑ i ∈ Finset.range m,
        (p i / h) * (((h:ℝ)-t)*w (q+i) + (t:ℝ)*w (q+i+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ j ∈ Finset.range h, (p i / h) * w (q+i+(t+j)/h) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_block i h j hh (Finset.mem_range.mp hj), div_shifted_block q i h t j hh]
        _ = _ := by rw [← Finset.mul_sum, block_weight_sum h t (q+i) hh ht w]
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp

#print axioms interpolation


variable {R : Type*} [Fintype R]

theorem weighted_interpolation (m h q t : ℕ) (hh : 0 < h) (ht : t < h)
    (lam : R → ℝ) (p w : R → ℕ → ℝ) :
    (∑ r, lam r * ∑ s ∈ Finset.range (m*h), (p r (s/h) / h) * w r ((q*h+t+s)/h)) =
      (1-(t:ℝ)/h) * (∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) +
      ((t:ℝ)/h) * (∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i+1)) := by
  simp_rw [interpolation m h q t hh ht]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;> ring

theorem interpolated_cover (m h M x : ℕ) (hh : 0 < h) (hx : x < M*h)
    (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hc : ∀ q ≤ M, 1 ≤ ∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    1 ≤ ∑ r, lam r * ∑ s ∈ Finset.range (m*h), (p r (s/h) / h)*w r ((x+s)/h) := by
  let q := x/h
  let t := x%h
  have ht : t < h := Nat.mod_lt _ hh
  have hq : q < M := (Nat.div_lt_iff_lt_mul hh).mpr hx
  have hxt : q*h+t = x := by simpa [q, t, Nat.mul_comm] using Nat.div_add_mod x h
  rw [← hxt, weighted_interpolation m h q t hh ht]
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have htR : (t:ℝ) < h := by exact_mod_cast ht
  have hz : 0 ≤ (t:ℝ)/h := by positivity
  have ho : 0 ≤ 1-(t:ℝ)/h := by apply sub_nonneg.mpr; exact (div_le_one hhR).mpr htR.le
  have h1 := mul_le_mul_of_nonneg_left (hc q hq.le) ho
  have h2 := mul_le_mul_of_nonneg_left (hc (q+1) hq) hz
  simp only [Nat.add_right_comm q 1] at h2
  linarith

/-- Reflected boundary weights on positions 0,...,T−1. T≥2D keeps the two
D-point boundary regions disjoint. Values outside this interval are irrelevant. -/
def boundary (T D h : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n < D then w (n/h) else if T-1-n < D then w ((T-1-n)/h) else 1

theorem boundary_reflect (T D h n : ℕ) (hT : 2*D ≤ T) (hn : n < T) (w : ℕ → ℝ) :
    boundary T D h w (T-1-n) = boundary T D h w n := by
  have hinv : T-1-(T-1-n) = n := by omega
  have hd : ¬ (n<D ∧ T-1-n<D) := by omega
  unfold boundary
  rw [hinv]
  split_ifs <;> aesop

theorem boundary_square (T D h n : ℕ) (hT : 2*D ≤ T) (hn : n < T) (w : ℕ → ℝ) :
    (boundary T D h w n)^2 = 1 +
      (if n<D then (w (n/h))^2-1 else 0) +
      (if T-1-n<D then (w ((T-1-n)/h))^2-1 else 0) := by
  have hd : ¬ (n<D ∧ T-1-n<D) := by omega
  unfold boundary
  split_ifs <;> simp_all

theorem truncate_sum (T D : ℕ) (hD : D ≤ T) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range T, if n<D then f n else 0) = ∑ n ∈ Finset.range D, f n := by
  calc
    _ = (∑ n ∈ Finset.range D, if n<D then f n else 0) +
        ∑ n ∈ Finset.range (T-D), if D+n<D then f (D+n) else 0 := by
      simpa only [Nat.add_sub_of_le hD] using
        Finset.sum_range_add (fun n => if n<D then f n else 0) D (T-D)
    _ = _ := by
      have hs : (∑ n ∈ Finset.range (T-D), if D+n<D then f (D+n) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        exact if_neg (by omega)
      rw [hs, add_zero]
      apply Finset.sum_congr rfl
      intro n hn
      exact if_pos (Finset.mem_range.mp hn)

theorem block_sum (M h : ℕ) (hh : 0 < h) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (M*h), f (n/h)) = (h:ℝ)*∑ j ∈ Finset.range M, f j := by
  rw [sum_range_blocks, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ _j ∈ Finset.range h, f i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_block i h j hh (Finset.mem_range.mp hj)]
    _ = _ := by simp

theorem boundary_norm (T M h : ℕ) (hh : 0 < h) (hT : 2*(M*h) ≤ T) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.range T, (boundary T (M*h) h w n)^2) =
      (T:ℝ) + 2*((h:ℝ)*∑ j ∈ Finset.range M, (w j)^2 - M*h) := by
  have hD : M*h ≤ T := by omega
  have hpoint : ∀ n ∈ Finset.range T, (boundary T (M*h) h w n)^2 =
      1 + (if n<M*h then (w (n/h))^2-1 else 0) +
      (if T-1-n<M*h then (w ((T-1-n)/h))^2-1 else 0) := by
    intro n hn
    exact boundary_square T (M*h) h n hT (Finset.mem_range.mp hn) w
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.sum_range_reflect (fun n => if n<M*h then (w (n/h))^2-1 else 0),
    truncate_sum T (M*h) hD, Finset.sum_sub_distrib, block_sum M h hh (fun j => (w j)^2)]
  simp
  ring

#print axioms interpolated_cover
#print axioms boundary_norm


theorem boundary_left (N H M h x s : ℕ) (_hH : 0 < H) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < M*h) (hs : s < H)
    (w : ℕ → ℝ) (hw : ∀ j, M ≤ j → w j = 1) :
    boundary (N+H-1) (M*h) h w (x+s) = w ((x+s)/h) := by
  have hfar : M*h ≤ N+H-1-1-(x+s) := by omega
  unfold boundary
  rw [if_neg (by omega : ¬ N+H-1-1-(x+s)<M*h)]
  split_ifs with hx'
  · rfl
  · symm
    apply hw
    exact (Nat.le_div_iff_mul_le hh).mpr (by omega)

theorem boundary_middle (N H D h x s : ℕ) (_hH : 0 < H)
    (hx : D ≤ x) (hx' : x < N-D) (hs : s < H) (w : ℕ → ℝ) :
    boundary (N+H-1) D h w (x+s) = 1 := by
  unfold boundary
  rw [if_neg (by omega : ¬ x+s<D), if_neg (by omega : ¬ N+H-1-1-(x+s)<D)]

theorem kernel_mass (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ)
    (hp : ∑ i ∈ Finset.range m, p i = 1) :
    (∑ s ∈ Finset.range (m*h), p (s/h)/h) = 1 := by
  rw [block_sum m h hh (fun i => p i / h), ← Finset.sum_div, hp]
  have hR : (h:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  field_simp

theorem kernel_reflect (m h s : ℕ) (hh : 0 < h) (hs : s < m*h) (p : ℕ → ℝ)
    (hp : ∀ i < m, p (m-1-i) = p i) :
    p ((m*h-1-s)/h) / h = p (s/h) / h := by
  have hdiv : (m*h-1-s)/h = m-1-s/h := by
    have heq : m*h-1-s = h*m-(s+1) := by rw [Nat.sub_sub, Nat.mul_comm m h, Nat.add_comm 1 s]
    rw [heq, Nat.mul_sub_div s h m (by simpa [Nat.mul_comm] using hs)]
    omega
  rw [hdiv, hp (s/h) ((Nat.div_lt_iff_lt_mul hh).mpr hs)]

theorem boundary_window_reflect (N H D h x s : ℕ) (hH : 0 < H)
    (hN : 2*D ≤ N) (hx : x < N) (hs : s < H) (w : ℕ → ℝ) :
    boundary (N+H-1) D h w (x+(H-1-s)) =
      boundary (N+H-1) D h w (N-1-x+s) := by
  have hi : N+H-1-1-(x+(H-1-s)) = N-1-x+s := by omega
  have hr := boundary_reflect (N+H-1) D h (x+(H-1-s)) (by omega) (by omega) w
  rw [hi] at hr
  exact hr.symm

theorem convolution_reflect (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < N) (p w : ℕ → ℝ)
    (hp : ∀ i < m, p (m-1-i) = p i) :
    (∑ s ∈ Finset.range (m*h), (p (s/h)/h)*boundary (N+m*h-1) (M*h) h w (x+s)) =
      ∑ s ∈ Finset.range (m*h), (p (s/h)/h)*boundary (N+m*h-1) (M*h) h w (N-1-x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  calc
    _ = ∑ s ∈ Finset.range (m*h), (p ((m*h-1-s)/h)/h)*
        boundary (N+m*h-1) (M*h) h w (x+(m*h-1-s)) := by
      exact (Finset.sum_range_reflect _ (m*h)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := Finset.mem_range.mp hs
      rw [kernel_reflect m h s hh hs' p hp,
        boundary_window_reflect N (m*h) (M*h) h x s hH hN hx hs' w]

theorem actual_boundary_cover (N m h M x : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(M*h) ≤ N) (hx : x < N) (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam : ∑ r, lam r = 1) (hmass : ∀ r, ∑ i ∈ Finset.range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, M ≤ j → w r j = 1)
    (hc : ∀ q ≤ M, 1 ≤ ∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    1 ≤ ∑ r, lam r * ∑ s ∈ Finset.range (m*h),
      (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (x+s) := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  have hleft : ∀ y < M*h, 1 ≤ ∑ r, lam r * ∑ s ∈ Finset.range (m*h),
      (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (y+s) := by
    intro y hy
    have heq : (∑ r, lam r * ∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (y+s)) =
        ∑ r, lam r * ∑ s ∈ Finset.range (m*h), (p r (s/h)/h)*w r ((y+s)/h) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [boundary_left N (m*h) M h y s hH hh hN hy (Finset.mem_range.mp hs) (w r) (hw r)]
    rw [heq]
    exact interpolated_cover m h M y hh hy lam p w hc
  by_cases hxl : x < M*h
  · exact hleft x hxl
  by_cases hxr : N-M*h ≤ x
  · have hy : N-1-x < M*h := by omega
    have heq : (∑ r, lam r * ∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (x+s)) =
        ∑ r, lam r * ∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (N-1-x+s) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [convolution_reflect N m h M x hm hh hN hx (p r) (w r) (hsym r)]
    rw [heq]
    exact hleft _ hy
  · have hone : ∀ r, (∑ s ∈ Finset.range (m*h),
        (p r (s/h)/h)*boundary (N+m*h-1) (M*h) h (w r) (x+s)) = 1 := by
      intro r
      calc
        _ = ∑ s ∈ Finset.range (m*h), p r (s/h)/h := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [boundary_middle N (m*h) (M*h) h x s hH (by omega) (by omega)
            (Finset.mem_range.mp hs) (w r), mul_one]
        _ = 1 := kernel_mass m h hh (p r) (hmass r)
    simp_rw [hone, mul_one]
    rw [hlam]

#print axioms actual_boundary_cover


theorem weighted_boundary_norm (T M h : ℕ) (hh : 0 < h) (hT : 2*(M*h) ≤ T)
    (lam : R → ℝ) (w : R → ℕ → ℝ) (hlam : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ Finset.range T, (boundary T (M*h) h (w r) n)^2) =
      (T:ℝ) + 2*((h:ℝ)*(∑ r, lam r * ∑ j ∈ Finset.range M, (w r j)^2) - M*h) := by
  simp_rw [boundary_norm T M h hh hT]
  have heq : ∀ r, lam r * ((T:ℝ)+2*((h:ℝ)*(∑ j ∈ Finset.range M, (w r j)^2)-M*h)) =
      (T:ℝ)*lam r + (2*(h:ℝ))*(lam r*∑ j ∈ Finset.range M, (w r j)^2) -
        (2*(M:ℝ)*h)*lam r := by intro r; ring
  simp_rw [heq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hlam]
  ring

theorem weighted_boundary_norm_sidon (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (lam : R → ℝ) (w : R → ℕ → ℝ)
    (hlam : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ Finset.range (N+m*h-1),
      (boundary (N+m*h-1) (L*m*h) h (w r) n)^2) =
      (N:ℝ) + (1+2*((∑ r, lam r * ∑ j ∈ Finset.range (L*m), (w r j)^2)/(m:ℝ)-L)) *
        ((m:ℝ)*h)-1 := by
  have hH : 0 < m*h := Nat.mul_pos hm hh
  rw [weighted_boundary_norm (N+m*h-1) (L*m) h hh (by omega) lam w hlam]
  rw [Nat.cast_sub (by omega : 1 ≤ N+m*h), Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_mul]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp
  ring

#print axioms weighted_boundary_norm_sidon

end SidonBoundary


namespace SidonConcrete
open SidonConvolutionEnergy SidonFiniteSmoothing SidonBoundary

variable {R : Type*} [Fintype R]

noncomputable def blockKernel (m h : ℕ) (p : ℕ → ℝ) (s : ℤ) : ℝ :=
  if 0 ≤ s ∧ s < (m*h : ℕ) then p (s.toNat/h)/(h:ℝ) else 0

def blockWeight (N m h L : ℕ) (w : ℕ → ℝ) (z : ℤ) : ℝ :=
  boundary (N+m*h-1) (L*m*h) h w z.toNat

def aValue (m : ℕ) (lam : R → ℝ) (p : R → ℕ → ℝ) : ℝ :=
  (m:ℝ) * ∑ r, lam r * ∑ i ∈ Finset.range m, p r i ^ 2

noncomputable def bValue (m L : ℕ) (lam : R → ℝ) (w : R → ℕ → ℝ) : ℝ :=
  1 + 2 * ((∑ r, lam r * ∑ j ∈ Finset.range (L*m), w r j ^ 2)/(m:ℝ) - L)

theorem blockKernel_nat (m h s : ℕ) (p : ℕ → ℝ) (hs : s < m*h) :
    blockKernel m h p (s:ℤ) = p (s/h)/(h:ℝ) := by
  unfold blockKernel
  rw [if_pos (by omega)]
  simp

theorem blockKernel_support (m h : ℕ) (p : ℕ → ℝ) :
    ∀ s, s ∉ Finset.Ico (0:ℤ) (m*h:ℕ) → blockKernel m h p s = 0 := by
  intro s hs
  exact if_neg (by simpa only [Finset.mem_Ico] using hs)

theorem blockKernel_nonneg (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ)
    (hp : ∀ i < m, 0 ≤ p i) : ∀ s, 0 ≤ blockKernel m h p s := by
  intro s
  unfold blockKernel
  split_ifs with hs
  · apply div_nonneg
    · apply hp
      apply (Nat.div_lt_iff_lt_mul hh).mpr
      omega
    · positivity
  · rfl

theorem blockKernel_mass (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ)
    (hp : ∑ i ∈ Finset.range m, p i = 1) :
    (∑ s ∈ Finset.Ico (0:ℤ) (m*h:ℕ), blockKernel m h p s) = 1 := by
  rw [sum_int_Ico_nat]
  calc
    _ = ∑ s ∈ Finset.range (m*h), p (s/h)/(h:ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact blockKernel_nat m h s p (Finset.mem_range.mp hs)
    _ = 1 := kernel_mass m h hh p hp

theorem blockKernel_square_mass (m h : ℕ) (hh : 0 < h) (p : ℕ → ℝ) :
    (∑ s ∈ Finset.Ico (0:ℤ) (m*h:ℕ), blockKernel m h p s ^ 2) =
      (∑ i ∈ Finset.range m, p i ^ 2)/(h:ℝ) := by
  rw [sum_int_Ico_nat]
  have hhR : (h:ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ s ∈ Finset.range (m*h), (p (s/h)/(h:ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [blockKernel_nat m h s p (Finset.mem_range.mp hs)]
    _ = _ := by
      rw [block_sum m h hh (fun i => (p i/(h:ℝ)) ^ 2)]
      simp_rw [div_pow]
      rw [← Finset.sum_div]
      field_simp

theorem weighted_kernel_square_mass (m h : ℕ) (hm : 0 < m) (hh : 0 < h)
    (lam : R → ℝ) (p : R → ℕ → ℝ) :
    (∑ r, lam r * ∑ s ∈ Finset.Ico (0:ℤ) (m*h:ℕ), blockKernel m h (p r) s ^ 2) =
      aValue m lam p / ((m:ℝ)*h) := by
  simp_rw [blockKernel_square_mass m h hh, ← mul_div_assoc]
  rw [← Finset.sum_div]
  unfold aValue
  have hmR : (m:ℝ) ≠ 0 := by positivity
  have hhR : (h:ℝ) ≠ 0 := by positivity
  field_simp

/-- Translation from the Nat interval convolution used in interpolation to
its actual finite integer pairing. -/
theorem block_pairing (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (p w : ℕ → ℝ) (x : ℤ) (hx : x ∈ Finset.Ico (0:ℤ) (N:ℤ)) :
    (∑ n ∈ Finset.Ico (0:ℤ) (N+m*h-1:ℕ),
      blockWeight N m h L w n * blockKernel m h p (n-x)) =
    ∑ s ∈ Finset.range (m*h), (p (s/h)/(h:ℝ)) *
      boundary (N+m*h-1) (L*m*h) h w (x.toNat+s) := by
  have hx0 := (Finset.mem_Ico.mp hx).1
  have hxN := (Finset.mem_Ico.mp hx).2
  have hH : 0 < m*h := Nat.mul_pos hm hh
  rw [sum_shift_support _ (Finset.Ico (0:ℤ) (m*h:ℕ)) _ _ x
    (blockKernel_support m h p)]
  · rw [sum_int_Ico_nat]
    apply Finset.sum_congr rfl
    intro s hs
    rw [blockKernel_nat m h s p (Finset.mem_range.mp hs)]
    unfold blockWeight
    have he : (x + (s:ℤ)).toNat = x.toNat + s := by omega
    rw [he, mul_comm]
  · intro s hs
    have hs0 := (Finset.mem_Ico.mp hs).1
    have hsH := (Finset.mem_Ico.mp hs).2
    apply Finset.mem_Ico.mpr
    constructor <;> omega

theorem block_cover (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam : ∑ r, lam r = 1) (hmass : ∀ r, ∑ i ∈ Finset.range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i)) :
    ∀ x ∈ Finset.Ico (0:ℤ) (N:ℤ),
      1 ≤ ∑ r, lam r * ∑ n ∈ Finset.Ico (0:ℤ) (N+m*h-1:ℕ),
        blockWeight N m h L (w r) n * blockKernel m h (p r) (n-x) := by
  intro x hx
  simp_rw [block_pairing N m h L hm hh _ _ x hx]
  apply actual_boundary_cover N m h (L*m) x.toNat hm hh hN
    (by have hx' := Finset.mem_Ico.mp hx; omega) lam p w hlam hmass hsym hw hc

theorem block_weight_norm (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (lam : R → ℝ) (w : R → ℕ → ℝ)
    (hlam : ∑ r, lam r = 1) :
    (∑ r, lam r * ∑ n ∈ Finset.Ico (0:ℤ) (N+m*h-1:ℕ),
      blockWeight N m h L (w r) n ^ 2) =
      (N:ℝ) + bValue m L lam w * ((m:ℝ)*h) - 1 := by
  simp_rw [sum_int_Ico_nat]
  simp only [blockWeight, Int.toNat_natCast]
  exact weighted_boundary_norm_sidon N m h L hm hh hN lam w hlam

/-- Complete exact finite inequality from the finite certificate constraints.
All interval coverage and norm calculations are discharged by actual kernels
and reflected boundary weights, rather than left as analytic assumptions. -/
theorem finite_bound_from_certificate (N m h L : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hN : 2*(L*m*h) ≤ N) (lam : R → ℝ) (p w : R → ℕ → ℝ)
    (hlam_nonneg : ∀ r, 0 ≤ lam r) (hlam : ∑ r, lam r = 1)
    (hp_nonneg : ∀ r i, i < m → 0 ≤ p r i)
    (hmass : ∀ r, ∑ i ∈ Finset.range m, p r i = 1)
    (hsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hc : ∀ q ≤ L*m, 1 ≤ ∑ r, lam r * ∑ i ∈ Finset.range m, p r i*w r (q+i))
    (A : Finset ℤ) (hA : IsSidon A)
    (hAN : A ⊆ Finset.Ico (0:ℤ) (N:ℤ)) :
    (A.card : ℝ) ^ 2 ≤
      ((N:ℝ) + bValue m L lam w * ((m:ℝ)*h) - 1) *
      (1 + aValue m lam p * ((A.card : ℝ)-1) / ((m:ℝ)*h)) := by
  apply finite_smoothing_bound A
    (Finset.Ico (0:ℤ) (N+m*h-1:ℕ)) (Finset.Ico (0:ℤ) (m*h:ℕ))
    (fun r => blockKernel m h (p r)) (fun r => blockWeight N m h L (w r))
    lam (N:ℝ) (aValue m lam p) (bValue m L lam w) ((m:ℝ)*h)
    hA
  · exact fun r => blockKernel_nonneg m h hh (p r) (hp_nonneg r)
  · exact fun r => blockKernel_support m h (p r)
  · exact fun r => blockKernel_mass m h hh (p r) (hmass r)
  · exact hlam_nonneg
  · exact hlam
  · intro x hx
    exact block_cover N m h L hm hh hN lam p w hlam hmass hsym hw hc x (hAN hx)
  · exact block_weight_norm N m h L hm hh hN lam w hlam
  · exact weighted_kernel_square_mass m h hm hh lam p

#print axioms finite_bound_from_certificate
end SidonConcrete


namespace SidonAlgebraicTransfer

lemma quadratic_bound {u v d w k : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ d) (hw : 0 ≤ w)
    (_hk : 0 ≤ k)
    (h : k ^ 2 ≤ u ^ 2 + v * u + w + (v + d) * k) :
    k ≤ u + v + d + w + 1 := by
  by_contra hc
  have hgt : u + v + d + w + 1 < k := lt_of_not_ge hc
  have hp : 0 < (k - (u + v + d + w + 1)) * (k + u + w + 1) :=
    mul_pos (by linarith) (by linarith)
  have hdu : 0 ≤ d * u := mul_nonneg hd hu
  have hwu : 0 ≤ w * u := mul_nonneg hw hu
  have hwv : 0 ≤ w * v := mul_nonneg hw hv
  have hdw : 0 ≤ d * w := mul_nonneg hd hw
  nlinarith [sq_nonneg w]

/-- Explicit algebraic inversion of the finite smoothing inequality.  Here
`x` is the fourth root of the interval length and `H` is any admissible
kernel length between `t*x^3` and `t*x^3+m`. -/
theorem finite_smoothing_bound {a b c t m x H k : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (_ht : 0 < t)
    (hm : 0 ≤ m) (hx : 1 ≤ x) (hH : 0 < H) (hk : 0 ≤ k)
    (hat : a = c * t) (hbt : b * t = c)
    (hlo : t * x ^ 3 ≤ H) (hhi : H ≤ t * x ^ 3 + m)
    (hfinite : k ^ 2 ≤ (x ^ 4 + b * H - 1) * (1 + a * (k - 1) / H))
    (hfactor : 0 ≤ x ^ 4 + b * H - 1) :
    k ≤ x ^ 2 + c * x + a * b + b * m + 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hB : 0 ≤ x ^ 4 + b * H := by positivity
  have hD : 0 ≤ 1 + a * k / H := by positivity
  have hrelax : k ^ 2 ≤ (x ^ 4 + b * H) * (1 + a * k / H) := by
    calc
      k ^ 2 ≤ (x ^ 4 + b * H - 1) * (1 + a * (k - 1) / H) := hfinite
      _ ≤ (x ^ 4 + b * H - 1) * (1 + a * k / H) := by
        gcongr
        linarith
      _ ≤ (x ^ 4 + b * H) * (1 + a * k / H) := by gcongr; linarith
  have hratio : a * x ^ 4 / H ≤ c * x := by
    apply (div_le_iff₀ hH).2
    calc
      a * x ^ 4 = (c * x) * (t * x ^ 3) := by rw [hat]; ring
      _ ≤ (c * x) * H := mul_le_mul_of_nonneg_left hlo (mul_nonneg hc hx0)
  have hboundary : b * H ≤ c * x ^ 3 + b * m := by
    calc
      b * H ≤ b * (t * x ^ 3 + m) := mul_le_mul_of_nonneg_left hhi hb
      _ = c * x ^ 3 + b * m := by rw [mul_add, ← mul_assoc, hbt]
  have hrewrite :
      (x ^ 4 + b * H) * (1 + a * k / H) =
        x ^ 4 + b * H + (a * x ^ 4 / H + a * b) * k := by
    field_simp
  rw [hrewrite] at hrelax
  have hineq : k ^ 2 ≤ (x ^ 2) ^ 2 + (c * x) * x ^ 2 + b * m +
      (c * x + a * b) * k := by
    have hmulk := mul_le_mul_of_nonneg_right hratio hk
    nlinarith
  exact quadratic_bound (sq_nonneg x) (mul_nonneg hc hx0)
    (mul_nonneg ha hb) (mul_nonneg hb hm) hk hineq

#print axioms finite_smoothing_bound

/-- The admissible kernel length can be selected without rounding errors in
the leading coefficient. -/
theorem admissible_length {t x : ℝ} (m : ℕ) (hm : 0 < m)
    (ht : 0 < t) (hx : 0 < x) :
    ∃ h : ℕ, 0 < h ∧
      t * x ^ 3 ≤ (m : ℝ) * h ∧
      (m : ℝ) * h ≤ t * x ^ 3 + m := by
  let z : ℝ := t * x ^ 3 / m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : 0 < z := by dsimp [z]; positivity
  refine ⟨⌈z⌉₊, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.mpr hz
  · have h := Nat.le_ceil z
    have h' := mul_le_mul_of_nonneg_left h hmR.le
    dsimp [z] at h'
    have he : (m : ℝ) * (t * x ^ 3 / m) = t * x ^ 3 := by field_simp
    rwa [he] at h'
  · have h : (⌈z⌉₊ : ℝ) ≤ z + 1 := by
      have hc := Nat.ceil_lt_add_one hz.le
      exact hc.le
    have h' := mul_le_mul_of_nonneg_left h hmR.le
    dsimp [z] at h'
    have he : (m : ℝ) * (t * x ^ 3 / m + 1) = t * x ^ 3 + m := by field_simp
    rwa [he] at h'

#print axioms admissible_length

lemma separation_condition {L t m x H : ℝ}
    (hL : 0 ≤ L) (hx : 1 ≤ x)
    (hxt : 4 * L * t ≤ x) (hxm : 4 * L * m ≤ x)
    (hH : H ≤ t * x ^ 3 + m) : 2 * L * H ≤ x ^ 4 := by
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  have hx4x : x ≤ x ^ 4 := by
    have := mul_le_mul_of_nonneg_left hx3 hx0
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hxt (pow_nonneg hx0 3)
  have hmulH := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 2 * L)
  nlinarith

/-- A finite smoothing inequality for each admissible multiple of `m` implies
an eventual bound with an explicit additive constant.  The hypothesis is the
finite combinatorial inequality, rather than an asymptotic assumption. -/
theorem eventual_bound (m L : ℕ) (hm : 0 < m)
    {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ht : 0 < t) (hat : a = c * t) (hbt : b * t = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℝ, 0 ≤ k →
      (∀ h : ℕ, 0 < h → 2 * (L : ℝ) * ((m : ℝ) * h) ≤ N →
        k ^ 2 ≤ ((N : ℝ) + b * ((m : ℝ) * h) - 1) *
          (1 + a * (k - 1) / ((m : ℝ) * h))) →
      k ≤ Real.sqrt N + c * Real.sqrt (Real.sqrt N) + a * b + b * m + 1 := by
  let T : ℝ := max 1 (4 * (L : ℝ) * (t + m))
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := by linarith
  refine ⟨⌈T ^ 4⌉₊, ?_⟩
  intro N hN k hk hf
  let x : ℝ := Real.sqrt (Real.sqrt N)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : x ^ 4 = N := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (Real.sqrt N) ^ 2 := by rw [hx2]
      _ = N := Real.sq_sqrt (by positivity)
  have hTN : T ^ 4 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hTx : T ≤ x := (pow_le_pow_iff_left₀ hT0 hx0 (by decide : 4 ≠ 0)).mp
    (by rwa [hx4])
  have hx1 : 1 ≤ x := hT1.trans hTx
  have hTsum : 4 * (L : ℝ) * (t + m) ≤ x := (le_max_right _ _).trans hTx
  have hxt : 4 * (L : ℝ) * t ≤ x := by
    have : 0 ≤ 4 * (L : ℝ) * m := by positivity
    nlinarith
  have hxm : 4 * (L : ℝ) * m ≤ x := by
    have : 0 ≤ 4 * (L : ℝ) * t := by positivity
    nlinarith
  obtain ⟨h, hh, hlo, hhi⟩ := admissible_length m hm ht (by linarith : 0 < x)
  have hsep : 2 * (L : ℝ) * ((m : ℝ) * h) ≤ N := by
    rw [← hx4]
    exact separation_condition (by positivity) hx1 hxt hxm hhi
  have hH : (0 : ℝ) < (m : ℝ) * h := by positivity
  have hfactor : 0 ≤ x ^ 4 + b * ((m : ℝ) * h) - 1 := by
    have hpow : 1 ≤ x ^ 4 := one_le_pow₀ hx1
    have hpos : 0 ≤ b * ((m : ℝ) * h) := by positivity
    linarith
  have hfinite := hf h hh hsep
  rw [← hx4] at hfinite
  have hbound := finite_smoothing_bound ha hb hc ht (by positivity : (0 : ℝ) ≤ m)
    hx1 hH hk hat hbt hlo hhi hfinite hfactor
  simpa [hx2, x] using hbound

#print axioms eventual_bound

/-- The leading coefficient from any positive certificate can be replaced
by an explicitly certified rational upper bound on its square root. -/
theorem eventual_bound_of_coefficient (m L : ℕ) (hm : 0 < m)
    {a b γ : ℝ} (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ)
    (hab : a * b < γ ^ 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℝ, 0 ≤ k →
      (∀ h : ℕ, 0 < h → 2 * (L : ℝ) * ((m : ℝ) * h) ≤ N →
        k ^ 2 ≤ ((N : ℝ) + b * ((m : ℝ) * h) - 1) *
          (1 + a * (k - 1) / ((m : ℝ) * h))) →
      k ≤ Real.sqrt N + γ * Real.sqrt (Real.sqrt N) + a * b + b * m + 1 := by
  let c := Real.sqrt (a * b)
  let t := c / b
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos ha hb)
  have hcsq : c ^ 2 = a * b := Real.sq_sqrt (mul_pos ha hb).le
  have ht : 0 < t := div_pos hc hb
  have hat : a = c * t := by
    dsimp [t]
    field_simp
    nlinarith [hcsq]
  have hbt : b * t = c := by dsimp [t]; field_simp
  obtain ⟨N₀, hN₀⟩ := eventual_bound m L hm ha.le hb.le hc.le ht hat hbt
  refine ⟨N₀, ?_⟩
  intro N hN k hk hf
  have hbound := hN₀ N hN k hk hf
  have hcγ : c ≤ γ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcγ (Real.sqrt_nonneg (Real.sqrt N))
  linarith

#print axioms eventual_bound_of_coefficient

end SidonAlgebraicTransfer


/- Exact finite certificate using Hou–Zhao arXiv:2607.01169v2 hypotheses.
Numerical data optimized in this campaign; rational checks use the Lean kernel.
This supplies finite hypotheses of the smoothing lemma, not its asymptotic conclusion. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

namespace Submissions.Erdos30VectorSmoothingCertificate942838.Declan

open scoped BigOperators

def extendedWeight (w : Fin 8 → Fin 512 → ℚ) (r : Fin 8) (j : ℕ) : ℚ :=
  if hj : j < 512 then w r ⟨j, hj⟩ else 1

def energyA (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) : ℚ :=
  128 * ∑ r, mix r * ∑ i, (p r i)^2

def energyB (mix : Fin 8 → ℚ) (w : Fin 8 → Fin 512 → ℚ) : ℚ :=
  1 + 2 * ((∑ r, mix r * ∑ j, (w r j)^2) / 128 - 4)

def ValidCertificate (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ)
    (w : Fin 8 → Fin 512 → ℚ) : Prop :=
  (∀ r, 0 ≤ mix r) ∧ (∑ r, mix r) = 1 ∧
  (∀ r i, 0 ≤ p r i) ∧ (∀ r, (∑ i, p r i) = 1) ∧
  (∀ r i, p r i = p r i.rev) ∧
  (∀ q : Fin 513, 1 ≤ ∑ r, mix r * ∑ i, p r i * extendedWeight w r (q.val + i.val)) ∧
  0 < energyA mix p ∧ 0 < energyB mix w ∧
  energyA mix p * energyB mix w < (942838 / 1000000 : ℚ)^2

abbrev statement : Prop :=
  ∃ (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) (w : Fin 8 → Fin 512 → ℚ),
    ValidCertificate mix p w

def mixInts : List ℕ := [422972356839, 56455640755, 2342754306, 221227015251, 143927345853, 20182087393, 58064372370, 74828427233]
def kernelInts : List (List ℕ) := [
  [1213946189, 1264471874, 958096528, 944113919, 1691464608, 1658228109, 2537899164, 2520256063, 3667606505, 3628506270, 3979393375, 4136945299, 2685484155, 2867040651, 4114616174, 4356846463, 3361765321, 3422299798, 4738031554, 4908964028, 4280772014, 4122434641, 3517282627, 3715300378, 3827319721, 3687591123, 3660801632, 3804014839, 4520538308, 4212689218, 5404187492, 5566599031, 7093299360, 6956083638, 7300110453, 7349715322, 7847752247, 7440254016, 7273749009, 7861500229, 8296171988, 7858144782, 9064942585, 9190462594, 10714109779, 10098790295, 10586837430, 10821286167, 11405381501, 11203183157, 11304081444, 11789585071, 14175250935, 13773040979, 14327610188, 15115265827, 17791489387, 18008709837, 20316871393, 20924925057, 20010577143, 19122744352, 17841042225, 18161524539, 18161524539, 17841042225, 19122744352, 20010577143, 20924925057, 20316871393, 18008709837, 17791489387, 15115265827, 14327610188, 13773040979, 14175250935, 11789585071, 11304081444, 11203183157, 11405381501, 10821286167, 10586837430, 10098790295, 10714109779, 9190462594, 9064942585, 7858144782, 8296171988, 7861500229, 7273749009, 7440254016, 7847752247, 7349715322, 7300110453, 6956083638, 7093299360, 5566599031, 5404187492, 4212689218, 4520538308, 3804014839, 3660801632, 3687591123, 3827319721, 3715300378, 3517282627, 4122434641, 4280772014, 4908964028, 4738031554, 3422299798, 3361765321, 4356846463, 4114616174, 2867040651, 2685484155, 4136945299, 3979393375, 3628506270, 3667606505, 2520256063, 2537899164, 1658228109, 1691464608, 944113919, 958096528, 1264471874, 1213946189],
  [4054327818, 3910475081, 9195395534, 9324827876, 10357972635, 9932570276, 12977369683, 13195319136, 6146601105, 6088878450, 9863176390, 10403914439, 7911175189, 6909943164, 4740203902, 5113563432, 7397185681, 7057041426, 7923071897, 8030890400, 5963986776, 5644746368, 5184373373, 5206788967, 7562616872, 7220634562, 9527405310, 8554671740, 10589827446, 11375412561, 10713798509, 9643124078, 10214022245, 10281399024, 9535281481, 9595880394, 7025249227, 7588064882, 5592466746, 5346870060, 7540100389, 7626830507, 7730955997, 7746660828, 5732307006, 5717204358, 5200637670, 5349081018, 6566692965, 6881599295, 4072607685, 4407916941, 9503622675, 9992632869, 9755806586, 9229672920, 6647226630, 6839748762, 8990400669, 8756853780, 6513143607, 6353722015, 10375858948, 9568191745, 9568191745, 10375858948, 6353722015, 6513143607, 8756853780, 8990400669, 6839748762, 6647226630, 9229672920, 9755806586, 9992632869, 9503622675, 4407916941, 4072607685, 6881599295, 6566692965, 5349081018, 5200637670, 5717204358, 5732307006, 7746660828, 7730955997, 7626830507, 7540100389, 5346870060, 5592466746, 7588064882, 7025249227, 9595880394, 9535281481, 10281399024, 10214022245, 9643124078, 10713798509, 11375412561, 10589827446, 8554671740, 9527405310, 7220634562, 7562616872, 5206788967, 5184373373, 5644746368, 5963986776, 8030890400, 7923071897, 7057041426, 7397185681, 5113563432, 4740203902, 6909943164, 7911175189, 10403914439, 9863176390, 6088878450, 6146601105, 13195319136, 12977369683, 9932570276, 10357972635, 9324827876, 9195395534, 3910475081, 4054327818],
  [1573702116, 1594328772, 2147952778, 2196683400, 5872632731, 5573536725, 6304759188, 6178177291, 2123364736, 2127531967, 3451373953, 3387514914, 8978922441, 8955675944, 6669998900, 6961050764, 11288345256, 11496766337, 5204232613, 5241878607, 9388853421, 9796059550, 6624235554, 6518873027, 10802977847, 10959386357, 7154269126, 6847292497, 7539984476, 7853096918, 4907510138, 5097115120, 13930766084, 13642534570, 10574259919, 10990414706, 15090397682, 15004391696, 16180626980, 16815072664, 12673427498, 12833927431, 9400527993, 9496885736, 9682790711, 9570213201, 9120384455, 9394868980, 12108505367, 11485670682, 5106144732, 5725058398, 6086480823, 5871199324, 6768126813, 7227455033, 5648988921, 5718868145, 6187923301, 6231283759, 5622871781, 5534723129, 4654545529, 4802580493, 4802580493, 4654545529, 5534723129, 5622871781, 6231283759, 6187923301, 5718868145, 5648988921, 7227455033, 6768126813, 5871199324, 6086480823, 5725058398, 5106144732, 11485670682, 12108505367, 9394868980, 9120384455, 9570213201, 9682790711, 9496885736, 9400527993, 12833927431, 12673427498, 16815072664, 16180626980, 15004391696, 15090397682, 10990414706, 10574259919, 13642534570, 13930766084, 5097115120, 4907510138, 7853096918, 7539984476, 6847292497, 7154269126, 10959386357, 10802977847, 6518873027, 6624235554, 9796059550, 9388853421, 5241878607, 5204232613, 11496766337, 11288345256, 6961050764, 6669998900, 8955675944, 8978922441, 3387514914, 3451373953, 2127531967, 2123364736, 6178177291, 6304759188, 5573536725, 5872632731, 2196683400, 2147952778, 1594328772, 1573702116],
  [227067071, 218955465, 322563287, 320829881, 708749414, 747488571, 660810019, 638546593, 1881942179, 1957695065, 2753596429, 2524764489, 5345739345, 5614813405, 6960127558, 6789008295, 8010204934, 8081572309, 10200007968, 9999977352, 10451436366, 10174129510, 13116654993, 13175810672, 13868049755, 13631399394, 13731839922, 14022932027, 13203703108, 12895168784, 9213009047, 9274892828, 6324920612, 6315838298, 8647961030, 8680771893, 8761541608, 9026859754, 9175271325, 9110893230, 7315214903, 7328505293, 13229475003, 12905131994, 11790597128, 12172441555, 7141129803, 6353421301, 6591737402, 6746263270, 6829642540, 6602913876, 7135270787, 7084199222, 9295016772, 9472839304, 9478876166, 9333183481, 8785925861, 8508644302, 10379304723, 10408319131, 9190843644, 9153558754, 9153558754, 9190843644, 10408319131, 10379304723, 8508644302, 8785925861, 9333183481, 9478876166, 9472839304, 9295016772, 7084199222, 7135270787, 6602913876, 6829642540, 6746263270, 6591737402, 6353421301, 7141129803, 12172441555, 11790597128, 12905131994, 13229475003, 7328505293, 7315214903, 9110893230, 9175271325, 9026859754, 8761541608, 8680771893, 8647961030, 6315838298, 6324920612, 9274892828, 9213009047, 12895168784, 13203703108, 14022932027, 13731839922, 13631399394, 13868049755, 13175810672, 13116654993, 10174129510, 10451436366, 9999977352, 10200007968, 8081572309, 8010204934, 6789008295, 6960127558, 5614813405, 5345739345, 2524764489, 2753596429, 1957695065, 1881942179, 638546593, 660810019, 747488571, 708749414, 320829881, 322563287, 218955465, 227067071],
  [2280844296, 2040073091, 3666252552, 4018562469, 4131861125, 3985983240, 5001301633, 5505037673, 7576142179, 6591217739, 8356160638, 9236830607, 13619835641, 12291586341, 11179364931, 12152367691, 8543742260, 7733658019, 10595389364, 11755129401, 10051870602, 9419616782, 8762768153, 9579456988, 6773241315, 6620675964, 8047435185, 8135137612, 7143154798, 6672154016, 5149077732, 5596702111, 5425721594, 5468073553, 5065221278, 5274946987, 5658236327, 5454732483, 7895216580, 8299903919, 10902340216, 10708066037, 12530957013, 13018681635, 13273717236, 11716106515, 11344973002, 12340613067, 11011759340, 10660272565, 6218654530, 6525276126, 6048533709, 5625839255, 5730491976, 5629367354, 6896857684, 6278173124, 6729739915, 6175547170, 6746579206, 7159927532, 7966295962, 8006544962, 8006544962, 7966295962, 7159927532, 6746579206, 6175547170, 6729739915, 6278173124, 6896857684, 5629367354, 5730491976, 5625839255, 6048533709, 6525276126, 6218654530, 10660272565, 11011759340, 12340613067, 11344973002, 11716106515, 13273717236, 13018681635, 12530957013, 10708066037, 10902340216, 8299903919, 7895216580, 5454732483, 5658236327, 5274946987, 5065221278, 5468073553, 5425721594, 5596702111, 5149077732, 6672154016, 7143154798, 8135137612, 8047435185, 6620675964, 6773241315, 9579456988, 8762768153, 9419616782, 10051870602, 11755129401, 10595389364, 7733658019, 8543742260, 12152367691, 11179364931, 12291586341, 13619835641, 9236830607, 8356160638, 6591217739, 7576142179, 5505037673, 5001301633, 3985983240, 4131861125, 4018562469, 3666252552, 2040073091, 2280844296],
  [3910777853, 3913096039, 3382944260, 3319051999, 3822821760, 3941171685, 5185339550, 5636082328, 6106432131, 6385132698, 8116998541, 7642647409, 2840863125, 2839434124, 5884085344, 5901140434, 4788226571, 4468898218, 5767287678, 5859822313, 7847804491, 7528891452, 9477386544, 10018807981, 10333274146, 9931406960, 8713026456, 8892316680, 13285662864, 13003154450, 7285005457, 7486475415, 8396819484, 7638579297, 9944246991, 9538023187, 7343358953, 7137136964, 13756080122, 14151626895, 10382172284, 11974331104, 13244828141, 12496850179, 7001645065, 7698800138, 6571825011, 6976566140, 8185890238, 8081792607, 10973969627, 10588653277, 6569054924, 6677106078, 8735314047, 8745709724, 7853913015, 7359689653, 10745451850, 10983219310, 5260340654, 5085958756, 8094312473, 8291266856, 8291266856, 8094312473, 5085958756, 5260340654, 10983219310, 10745451850, 7359689653, 7853913015, 8745709724, 8735314047, 6677106078, 6569054924, 10588653277, 10973969627, 8081792607, 8185890238, 6976566140, 6571825011, 7698800138, 7001645065, 12496850179, 13244828141, 11974331104, 10382172284, 14151626895, 13756080122, 7137136964, 7343358953, 9538023187, 9944246991, 7638579297, 8396819484, 7486475415, 7285005457, 13003154450, 13285662864, 8892316680, 8713026456, 9931406960, 10333274146, 10018807981, 9477386544, 7528891452, 7847804491, 5859822313, 5767287678, 4468898218, 4788226571, 5901140434, 5884085344, 2839434124, 2840863125, 7642647409, 8116998541, 6385132698, 6106432131, 5636082328, 5185339550, 3941171685, 3822821760, 3319051999, 3382944260, 3913096039, 3910777853],
  [3453840319, 3848999088, 5848584706, 5516519903, 4224115756, 4558050599, 5007555039, 4603803032, 7890675415, 8265318750, 10783540791, 9986908295, 9410170589, 10369543207, 14821195943, 13389427483, 12799433018, 13610929209, 12847943005, 12218716153, 8128478059, 8499837376, 6606330874, 6741251994, 5630297339, 5789621533, 7975031278, 8453296192, 4944155949, 5141307339, 7754151293, 8040906666, 8924668573, 8154404246, 9151003670, 9015635011, 7885744023, 8071771675, 5924937911, 5992628582, 7432884442, 7339268695, 6542629845, 6873875077, 6698639483, 7046962914, 7726908024, 7346268698, 7811623429, 7493029813, 8521576124, 8575780564, 6849552525, 6995412102, 6499772181, 6985331250, 5613120735, 5455788459, 9450076519, 9015687118, 5971858376, 5730244463, 10672116348, 11070862933, 11070862933, 10672116348, 5730244463, 5971858376, 9015687118, 9450076519, 5455788459, 5613120735, 6985331250, 6499772181, 6995412102, 6849552525, 8575780564, 8521576124, 7493029813, 7811623429, 7346268698, 7726908024, 7046962914, 6698639483, 6873875077, 6542629845, 7339268695, 7432884442, 5992628582, 5924937911, 8071771675, 7885744023, 9015635011, 9151003670, 8154404246, 8924668573, 8040906666, 7754151293, 5141307339, 4944155949, 8453296192, 7975031278, 5789621533, 5630297339, 6741251994, 6606330874, 8499837376, 8128478059, 12218716153, 12847943005, 13610929209, 12799433018, 13389427483, 14821195943, 10369543207, 9410170589, 9986908295, 10783540791, 8265318750, 7890675415, 4603803032, 5007555039, 4558050599, 4224115756, 5516519903, 5848584706, 3848999088, 3453840319],
  [2209813120, 2291992270, 1419270661, 1406175978, 2589939036, 2688916416, 2973918020, 2758257225, 3031248700, 3127114167, 4434882776, 4596367909, 4273578564, 4251819687, 3941214450, 3745117691, 5936903380, 6140477148, 7101849976, 7299325410, 7259839553, 7198286840, 6125926079, 5952377921, 9019108149, 8796406183, 8319318093, 8363333654, 4923736824, 5020458635, 6362061624, 6499703042, 8691889053, 8551907859, 11595780431, 12384516668, 20976397176, 20083861304, 21748852979, 22057689324, 11218192053, 11252766026, 9579541354, 9969849644, 12555276074, 11356404923, 10641713759, 10965963866, 9482128396, 9158231810, 7923351873, 8115137618, 7501990324, 7336001645, 7358584971, 7750371176, 10372437015, 10428478251, 7458847473, 7365129172, 7889075997, 7456224649, 5352598226, 5362069730, 5362069730, 5352598226, 7456224649, 7889075997, 7365129172, 7458847473, 10428478251, 10372437015, 7750371176, 7358584971, 7336001645, 7501990324, 8115137618, 7923351873, 9158231810, 9482128396, 10965963866, 10641713759, 11356404923, 12555276074, 9969849644, 9579541354, 11252766026, 11218192053, 22057689324, 21748852979, 20083861304, 20976397176, 12384516668, 11595780431, 8551907859, 8691889053, 6499703042, 6362061624, 5020458635, 4923736824, 8363333654, 8319318093, 8796406183, 9019108149, 5952377921, 6125926079, 7198286840, 7259839553, 7299325410, 7101849976, 6140477148, 5936903380, 3745117691, 3941214450, 4251819687, 4273578564, 4596367909, 4434882776, 3127114167, 3031248700, 2758257225, 2973918020, 2688916416, 2589939036, 1406175978, 1419270661, 2291992270, 2209813120]
]
def weightInts : List (List ℕ) := [
  [78904189846105, 82188263104105, 63507445559105, 62649921178105, 112167339279105, 110044947245105, 168936611049105, 167794590059105, 245005261192105, 242450727036105, 269099127263105, 279286689667105, 189202373722105, 201109389938105, 285049456102105, 301086217330105, 240569372666105, 245047053975105, 333783376344105, 345506382221105, 309277701702105, 299782171814105, 264485100756105, 278003622382105, 288769213513105, 280546241354105, 282458216916105, 292497231505105, 342753164686105, 323630601320105, 405544106102105, 416689225736105, 521670246081105, 513514212689105, 543263585641105, 547123483618105, 587348266197105, 561557446271105, 559216689925105, 597712128475105, 634410189008105, 606833613817105, 694291469370105, 702913720588105, 812333083433105, 772936889462105, 816753569820105, 831975162441105, 882719739039105, 869797558658105, 889928404181105, 921503284399105, 1090454370799105, 1064823374642105, 1117396325983105, 1168703940145105, 1360002061706105, 1375034259031105, 1545397142607105, 1586068019343105, 1549636664087105, 1493713254422105, 1432834095093105, 1454575281316105, 1476053738186105, 1456472962352105, 1561594851498105, 1620246660764105, 1703133251559105, 1665473028823105, 1540197649395105, 1527351094579105, 1376195265022105, 1326071241210105, 1310456105190105, 1336887802255105, 1202012273823105, 1171157135326105, 1182679077509105, 1196041500875105, 1176336290957105, 1161526607015105, 1147755986464105, 1187948093566105, 1106649983448105, 1099318683912105, 1037344345455105, 1066526624024105, 1053772478653105, 1016736235092105, 1042856657322105, 1069931917907105, 1053267874663105, 1051055040072105, 1044140080940105, 1054035686408105, 970141460646105, 960717388786105, 897298326403105, 918292993786105, 884756928003105, 876759939035105, 891013780121105, 901283081023105, 906738085659105, 895216333688105, 947368942192105, 958828366869105, 1013296020611105, 1003531460950105, 932497240533105, 929757050009105, 1007811269475105, 993220187949105, 926725370964105, 915848188267105, 1023748039084105, 1014260710558105, 1006696771873105, 1009841799683105, 950391864841105, 952195435023105, 909212558616105, 912055142510105, 877002994735105, 878639412426105, 911528215272105, 908999315240105, 843582641506105, 844295306558105, 855532219189105, 856205199852105, 867906556120105, 868604330168105, 879710972797105, 880456257602105, 890817650348105, 891587540932105, 900909130302105, 901725805089105, 910781500363105, 911459159833105, 922055254782105, 922553779700105, 932009421050105, 932270084009105, 942812968018105, 943002768306105, 952328913476105, 952337127653105, 962375263956105, 962534972300105, 973281723692105, 973229329079105, 983977916032105, 984057361319105, 994937086835105, 994861786420105, 1005125632677105, 1005348390811105, 1014491260109105, 1014535859286105, 1022188277154105, 1022366218257105, 1029671735761105, 1029789284699105, 1036587952359105, 1037108269501105, 1044041917570105, 1043972444958105, 1050440235881105, 1050803364864105, 1056000632514105, 1056232044326105, 1059811313690105, 1060654655426105, 1063604351287105, 1064223936304105, 1066430871510105, 1067271173925105, 1069186390686105, 1069540495410105, 1068855280605105, 1069614617068105, 1068084155300105, 1068057671973105, 1063521873133105, 1063250298969105, 1055989845941105, 1055082634385105, 1048283880609105, 1048234707977105, 1042268761086105, 1041887224466105, 1035491841332105, 1035406271710105, 1027267862673105, 1026258776864105, 1016711611459105, 1016273960428105, 1008531350791105, 1008297216615105, 1002793780903105, 1003330666956105, 997985492497105, 998126948895105, 994800039090105, 995422009668105, 991862692994105, 992286021997105, 988982165697105, 989638836542105, 986500655387105, 986542370841105, 984624594050105, 984785938119105, 983799304558105, 983509165756105, 982708173781105, 982987825076105, 981767288496105, 981629407988105, 980650193470105, 980543316194105, 979660533702105, 979395617477105, 979810631425105, 979691135068105, 981098849456105, 980653091091105, 982605621656105, 982276018830105, 984034922543105, 983542366790105, 985243428381105, 984919355100105, 985832942871105, 985322832456105, 985404680647105, 985045994467105, 986231947011105, 985903797778105, 985893662835105, 985796676737105, 986817302732105, 986883732666105, 986242525240105, 986455089145105, 985924544882105, 986091831224105, 986480243276105, 986623037711105, 987687418810105, 987791557289105, 989418216370105, 989493065770105, 990636013169105, 990755344277105, 992933810137105, 993043936559105, 995081001238105, 995181965571105, 997068287349105, 997159880730105, 998902271623105, 998983456752105, 1000591403453105, 1000661804275105, 1002149263800105, 1002207986574105, 1003577177103105, 1003626115557105, 1004851289259105, 1004893157261105, 1005989724352105, 1006028032413105, 1006977194307105, 1007013108088105, 1007831261480105, 1007867610031105, 1008541674684105, 1008576109764105, 1009092735740105, 1009128569918105, 1009485221500105, 1009520388545105, 1009712594565105, 1009749419476105, 1009784201554105, 1009818075081105, 1009710506678105, 1009744300110105, 1009515271287105, 1009546814192105, 1009199902819105, 1009230155559105, 1008771323578105, 1008794044348105, 1008219562409105, 1008243738400105, 1007559162525105, 1007578039868105, 1006801491822105, 1006816999399105, 1005972183946105, 1005974988098105, 1005070507471105, 1005063852899105, 1004110569503105, 1004090671126105, 1003092662573105, 1003066924425105, 1002063786108105, 1002025783863105, 1001031005025105, 1000992729520105, 1000053074962105, 1000018607560105, 999177600672105, 999156702288105, 998408632649105, 998388229364105, 997721705450105, 997706792786105, 997130370578105, 997116491478105, 996658504247105, 996660205243105, 996344182458105, 996352803899105, 996152714928105, 996165088977105, 996048200887105, 996052579924105, 996017981667105, 996020218272105, 996037466398105, 996029944883105, 996103209190105, 996088883782105, 996214955112105, 996190251557105, 996367184504105, 996341536164105, 996551103042105, 996522505563105, 996751202431105, 996726521638105, 996971676143105, 996942328290105, 997210541085105, 997182835671105, 997470258785105, 997443879131105, 997749365921105, 997726700212105, 998030513003105, 998009511251105, 998296385677105, 998282035249105, 998543275596105, 998533891644105, 998771883178105, 998769813093105, 998984871153105, 998987843081105, 999191524217105, 999202495016105, 999408113382105, 999424831869105, 999615595126105, 999637675008105, 999831624886105, 999855394251105, 1000037096535105, 1000060194283105, 1000255069724105, 1000275298626105, 1000480982820105, 1000498884254105, 1000702076762105, 1000718126382105, 1000906836352105, 1000921544063105, 1001091565720105, 1001105427740105, 1001260881319105, 1001273237728105, 1001393160450105, 1001403488231105, 1001495239775105, 1001504520170105, 1001564059543105, 1001571436109105, 1001612173489105, 1001619239264105, 1001628314274105, 1001633531906105, 1001620013121105, 1001624412847105, 1001592158423105, 1001595400429105, 1001539532136105, 1001541848721105, 1001474727948105, 1001476712377105, 1001380806356105, 1001381727639105, 1001278290088105, 1001280838452105, 1001164978026105, 1001165808818105, 1001039529222105, 1001040191044105, 1000904136515105, 1000903404248105, 1000757023373105, 1000756528226105, 1000608524179105, 1000609593488105, 1000454806060105, 1000454277526105, 1000304192001105, 1000303539613105, 1000156394834105, 1000156006640105, 1000015138903105, 1000012546085105, 999881794056105, 999878988680105, 999751297009105, 999746101805105, 999629314751105, 999628828869105, 999515158927105, 999513422567105, 999425018090105, 999423020515105, 999355240256105, 999347557620105, 999278996602105, 999273528493105, 999229840726105, 999224149147105, 999179180278105, 999180028430105, 999164334053105, 999156252517105, 999154884014105, 999152535038105, 999162391071105, 999156882804105, 999209121787105, 999210438962105, 999253778144105, 999250373624105, 999293701601105, 999293042808105, 999336032793105, 999336567932105, 999410313984105, 999418194900105, 999513851761105, 999517616806105, 999596156823105, 999591818762105, 999655204674105, 999651130390105, 999710400819105, 999712937070105, 999764367908105, 999766783778105, 999817729389105, 999819579184105, 999894769627105, 999889701063105, 999959134222105, 999967565410105, 1000022342868105, 1000023016224105, 1000046065232105, 1000054029131105, 1000082861537105, 1000080138057105, 1000123309987105, 1000133120297105, 1000185346527105, 1000192347345105, 1000246077516105, 1000248930169105, 1000282260235105, 1000276031799105, 1000291200248105, 1000291299619105, 1000279653713105, 1000279812238105, 1000300112732105, 1000305482092105, 1000344124655105, 1000342581987105, 1000355522266105, 1000355799010105, 1000397434927105, 1000401560908105, 1000426396906105, 1000435446591105, 1000406293744105, 1000404475700105, 1000429062867105, 1000437049389105, 1000366230972105, 1000373738813105],
  [263523585097105, 254173431213105, 601801144679105, 610067890210105, 686770375181105, 659103106290105, 867757361007105, 881474402383105, 437329500169105, 433342718829105, 685732668310105, 720582447344105, 569570853283105, 504740025382105, 372364198651105, 395866172703105, 550879954384105, 528373542589105, 593669617809105, 599928562851105, 475609703370105, 454207559149105, 432367247574105, 432838108494105, 593706369257105, 570497593732105, 730688684318105, 666122090536105, 811162374631105, 859873595042105, 831895088769105, 760714189268105, 812408847048105, 814087375307105, 780985325994105, 782249992805105, 630042765022105, 663969556537105, 546757241582105, 528671066160105, 681894160134105, 685124986080105, 704953911037105, 703618733410105, 586061200767105, 582700772107105, 560661574424105, 567878346333105, 658213501364105, 676363448089105, 506386209036105, 526147429476105, 867306647036105, 897364609503105, 897247565691105, 861796775247105, 709217154538105, 719921605063105, 872599714945105, 855779017222105, 725218239004105, 712952009998105, 987618783030105, 933026241926105, 950554069700105, 1000102697508105, 756472433628105, 764660924823105, 924491200247105, 937623844592105, 814328786632105, 799975790622105, 982394975782105, 1014525581300105, 1047336474281105, 1013986084568105, 700706826008105, 676825056663105, 872436141566105, 849514669002105, 786458805194105, 773996313625105, 822675923769105, 820648543186105, 967439926488105, 963378212510105, 974769535435105, 966025917490105, 841808767250105, 854527527155105, 1000635484406105, 961010769533105, 1146776038867105, 1139171017091105, 1209249239320105, 1201093500026105, 1186655839463105, 1252344915034105, 1317798544321105, 1263853311908105, 1155043546334105, 1214549707615105, 1086386019923105, 1105818029901105, 972465527318105, 968510172014105, 1016122841517105, 1034320545280105, 1187088742469105, 1177818757909105, 1142346448624105, 1162038379316105, 1033869025453105, 1007499557090105, 1166791781834105, 1229350168486105, 1412120853276105, 1375439433133105, 1153724265661105, 1155355901086105, 1633649829160105, 1617393599561105, 1447102962375105, 1472409612183105, 1430212745928105, 1419853363936105, 1100637776637105, 1107885151654105, 863654683068105, 861666590951105, 873020465456105, 871148058154105, 877258773887105, 875227272348105, 880243248865105, 878568434284105, 880429026860105, 878565179349105, 887356740861105, 885508160504105, 890515159519105, 888086465884105, 895530610498105, 894089560839105, 903699379948105, 901864117246105, 909212615484105, 907692787015105, 914146639817105, 912507690969105, 920998422333105, 919676774000105, 928626865171105, 927284120948105, 933857054949105, 932851191396105, 937037581613105, 937008154716105, 938993199373105, 938220618432105, 940672394196105, 940988185603105, 942682359950105, 942969656520105, 945212462481105, 945485436079105, 950132827244105, 949895178362105, 956431869594105, 956473505435105, 960727024359105, 960701856036105, 964722342876105, 964726845669105, 970637824344105, 970703377092105, 977045201108105, 976984336018105, 982024168316105, 981697589562105, 989455845893105, 988795683931105, 991361221803105, 990221809015105, 992832429369105, 992245756129105, 997268662170105, 996485532717105, 999205544930105, 998704459358105, 1003485739175105, 1003145893200105, 1003741087806105, 1004237567502105, 1004574306559105, 1004319563602105, 1008448582239105, 1008051477972105, 1009752999094105, 1009165523897105, 1012809248699105, 1012422353777105, 1013286479353105, 1012371836087105, 1012750032716105, 1012382481118105, 1017632533120105, 1017608151103105, 1019906873983105, 1020238144237105, 1023545604463105, 1024090980124105, 1026681604192105, 1027260828163105, 1027610622656105, 1028251351511105, 1028437241104105, 1029235438427105, 1031342726238105, 1031966175550105, 1031827476878105, 1033066720620105, 1030031288523105, 1031404292689105, 1027232063118105, 1028750093713105, 1024727120906105, 1025253331630105, 1020161970539105, 1021528498336105, 1018056589861105, 1018519680535105, 1016992257328105, 1017160709330105, 1017681308824105, 1017927969243105, 1017709883732105, 1017657513248105, 1015066638102105, 1015148555648105, 1013067998043105, 1012866808679105, 1012745215785105, 1012949095613105, 1010336325540105, 1009554445186105, 1004054898983105, 1003867476243105, 1001714617955105, 1001465252153105, 991842497721105, 991850272502105, 984733084231105, 984334594760105, 977780221805105, 977540554426105, 975861215585105, 975518856785105, 977614710087105, 977296777229105, 979249461144105, 978954244698105, 980842774606105, 980574431410105, 982414020527105, 982168174146105, 984006850282105, 983785882251105, 985516547818105, 985320959565105, 987000210908105, 986839570290105, 988428747844105, 988288029123105, 989751966591105, 989637608980105, 991009622033105, 990917434550105, 992209949180105, 992142028741105, 993321874722105, 993273575926105, 994332345228105, 994304040298105, 995277130969105, 995263901241105, 996186714015105, 996173851030105, 997079825501105, 997078647166105, 997960311214105, 997954154490105, 998823126682105, 998812575708105, 999660136378105, 999645230640105, 1000433652513105, 1000422092030105, 1001120967726105, 1001108301817105, 1001751961297105, 1001739812886105, 1002330124389105, 1002317678738105, 1002824947948105, 1002811174530105, 1003227707914105, 1003214746504105, 1003558721712105, 1003550362858105, 1003778772892105, 1003780702742105, 1003971901564105, 1003991697040105, 1004144608842105, 1004173672061105, 1004250701846105, 1004292699367105, 1004328440695105, 1004378598066105, 1004342138521105, 1004398441505105, 1004351834553105, 1004401490434105, 1004348473757105, 1004402764114105, 1004284583152105, 1004346466607105, 1004200365500105, 1004272065819105, 1004068440631105, 1004147478683105, 1003927129844105, 1004021947303105, 1003792353843105, 1003894237921105, 1003579545962105, 1003683221243105, 1003326729523105, 1003427043220105, 1003012774249105, 1003105735631105, 1002645434011105, 1002730750670105, 1002257742026105, 1002334514335105, 1001851058529105, 1001916452381105, 1001391820075105, 1001448250016105, 1000918040249105, 1000956129808105, 1000465340544105, 1000482490454105, 1000048786455105, 1000042674426105, 999665422224105, 999650695783105, 999347643711105, 999311206172105, 999056358067105, 999012010893105, 998775619072105, 998727923495105, 998478368223105, 998425705003105, 998176451706105, 998123907832105, 997910481157105, 997856877802105, 997672641461105, 997621478326105, 997434921864105, 997380066187105, 997229093581105, 997185778444105, 997118042870105, 997076581687105, 997041978663105, 997003825202105, 997122920678105, 997083629843105, 997315705210105, 997282158688105, 997610919394105, 997580354704105, 997952682355105, 997928243332105, 998261161537105, 998241050410105, 998553057222105, 998537761827105, 998817662109105, 998806752030105, 999056970766105, 999048871767105, 999312150521105, 999308572344105, 999520918023105, 999513632635105, 999719309032105, 999720655336105, 999888417939105, 999887018888105, 1000043829720105, 1000053072222105, 1000194696281105, 1000199603174105, 1000316184571105, 1000322568387105, 1000437447470105, 1000442512528105, 1000543386091105, 1000551526329105, 1000615255702105, 1000625198050105, 1000665432953105, 1000673189763105, 1000701222034105, 1000713789325105, 1000752121482105, 1000762845782105, 1000800402583105, 1000807562139105, 1000833151041105, 1000842851276105, 1000840787662105, 1000849955119105, 1000853002748105, 1000868602790105, 1000815096759105, 1000827882669105, 1000797109613105, 1000809146378105, 1000790084075105, 1000793445258105, 1000727809210105, 1000738951613105, 1000689638682105, 1000692597816105, 1000595548614105, 1000604167991105, 1000512415606105, 1000522540162105, 1000465161047105, 1000474598253105, 1000400968471105, 1000422953130105, 1000450030109105, 1000460185964105, 1000379545898105, 1000393753351105, 1000307044575105, 1000316733669105, 1000252048373105, 1000280053034105, 1000242510611105, 1000251326591105, 1000278639763105, 1000294963181105, 1000233852770105, 1000231576956105, 1000195925647105, 1000210109811105, 1000173651223105, 1000160450347105, 1000057635932105, 1000058444624105, 999976579435105, 999956889165105, 999962630575105, 999955962507105, 999921585562105, 999912470321105, 999886389837105, 999870653998105, 999792270522105, 999786686621105, 999785760061105, 999790376287105, 999795823982105, 999784132233105, 999754920806105, 999755869263105, 999774199502105, 999752205574105, 999808153553105, 999785938960105, 999726991689105, 999707989035105, 999644911348105, 999628681864105, 999559134719105, 999539234601105, 999605981178105, 999602574549105, 999596803634105, 999624769584105, 999668686566105, 999685999911105, 999628062691105, 999640427486105, 999520033606105, 999526677811105, 999535743324105, 999543272011105, 999577852032105, 999580605556105, 999870494967105, 999851741907105, 999885775588105, 999886320208105],
  [102287639818105, 103628333137105, 141211236725105, 144399584690105, 385514932414105, 366145034271105, 419626365124105, 411166868337105, 154400710438105, 154307470439105, 243130799073105, 238614558388105, 606209897802105, 604262813583105, 465607071317105, 484058374864105, 773065867457105, 786434950430105, 389690075297105, 392167781288105, 667770632068105, 694308422085105, 498509742976105, 492145623344105, 777911076567105, 788461234392105, 552905948166105, 533502904583105, 586615537777105, 607215165344105, 424676568434105, 437568553200105, 1017805376345105, 999841939516105, 815545048748105, 843082211835105, 1121827225862105, 1117158003099105, 1210219551359105, 1252304396865105, 1001167501103105, 1013106192667105, 804080340278105, 812033689120105, 834988764563105, 829487586170105, 811483399834105, 831051379043105, 1018380425980105, 979936529850105, 579157927121105, 620819466256105, 651924476111105, 640019328883105, 706418331477105, 738171635921105, 644713823206105, 651651271600105, 689819589903105, 695140320534105, 663866714486105, 660728677618105, 611306458305105, 623462876384105, 630473485180105, 623584378216105, 687918243737105, 696265005856105, 743938750534105, 743874360699105, 722260172714105, 720468422901105, 831598079705105, 804469319621105, 756442856524105, 772729721367105, 758758766111105, 721085415493105, 1145048749353105, 1187490485877105, 1027037387409105, 1011829063023105, 1054486865959105, 1064192171327105, 1066194627206105, 1062477218271105, 1299758931809105, 1291803894043105, 1578831042568105, 1539954972644105, 1485815257943105, 1493155357060105, 1248127275586105, 1222949550553105, 1440014688799105, 1460219121340105, 907075721659105, 896545463555105, 1100385734734105, 1081652372870105, 1052203001686105, 1073492723650105, 1335924064505105, 1327423557346105, 1068173696595105, 1076554876925105, 1297875590191105, 1273065473305105, 1022139291216105, 1020970545571105, 1444663771979105, 1432378180865105, 1172434076383105, 1154578601831105, 1320393168324105, 1322694190961105, 979107394564105, 984084072545105, 912507140898105, 913135278618105, 1190057972968105, 1199182549718105, 1169338964252105, 1189837240396105, 968136658446105, 966333518930105, 944096510629105, 944117813052105, 855234155889105, 856566442841105, 866976177078105, 868338283712105, 878330512539105, 879635540801105, 886026433550105, 887652225626105, 893323107980105, 895115371726105, 904849853659105, 906699716734105, 915200492017105, 917099165486105, 920008243755105, 922013815353105, 927123909629105, 928829066332105, 929527192356105, 931090993358105, 937971607820105, 939481556797105, 942177570317105, 943335303987105, 949119677060105, 950356405947105, 951791748224105, 952901991708105, 958031459355105, 959445727275105, 963818921046105, 964987907289105, 972252829176105, 973180071179105, 971530812280105, 972787936748105, 973963503174105, 974793319041105, 971655915172105, 972564686425105, 967934292887105, 968202339916105, 967415435466105, 967511481324105, 969967501960105, 969934080197105, 972072019183105, 972140907237105, 974588073044105, 974315726317105, 973907469842105, 974264024349105, 980072427663105, 979778318671105, 985200523383105, 985081756881105, 989551249654105, 988944274846105, 994945968037105, 994211350629105, 999712990188105, 998881479838105, 1004962389739105, 1004173292901105, 1011105035642105, 1010119570871105, 1017060998284105, 1016151567941105, 1022192691448105, 1021145506058105, 1026541795303105, 1025492905325105, 1031298013409105, 1030252334328105, 1034431527969105, 1033774824674105, 1038748352668105, 1037867929675105, 1043136335913105, 1042780949997105, 1041533760509105, 1040536673959105, 1041772116424105, 1040979727112105, 1041555062670105, 1040629708064105, 1041172822359105, 1040281474695105, 1037124270931105, 1036337267956105, 1028670845335105, 1028458540297105, 1021519937574105, 1021223438049105, 1017998036107105, 1018038237118105, 1011395696846105, 1011172597147105, 1013026966379105, 1012947756082105, 1011660742820105, 1011881493010105, 1011026878178105, 1010895707814105, 1005949948560105, 1005976700987105, 1004980979985105, 1004857203576105, 1000403543947105, 1000691171545105, 1000061896217105, 1000338095209105, 993110429494105, 993612023528105, 990318815086105, 991077681900105, 985166033863105, 985914865133105, 985254171556105, 985958037776105, 986391617298105, 987077205180105, 983213676377105, 983757773250105, 980305768301105, 980551451907105, 980498211938105, 980772211932105, 981068201698105, 981350292733105, 983034130332105, 983299919449105, 984847693823105, 985095667743105, 986511812353105, 986743312867105, 988081521009105, 988291573264105, 989561477252105, 989746681546105, 990884659271105, 991043504745105, 992066634636105, 992198501640105, 993192190681105, 993294463427105, 994223837586105, 994301258790105, 995233688746105, 995287581315105, 996127489255105, 996158907312105, 996969684625105, 996983249199105, 997716721006105, 997711381486105, 998433401224105, 998410753532105, 999063675789105, 999018971101105, 999613768018105, 999549352125105, 1000040608245105, 999961037192105, 1000485360966105, 1000384549933105, 1000899540860105, 1000784056060105, 1001355932797105, 1001224606224105, 1001877725699105, 1001740101661105, 1002415706119105, 1002274350355105, 1002922089463105, 1002779036795105, 1003403797486105, 1003256987829105, 1003854063101105, 1003709590033105, 1004321552721105, 1004169049251105, 1004700303507105, 1004549925574105, 1005004234691105, 1004853389786105, 1005245693546105, 1005101820618105, 1005406590528105, 1005271813837105, 1005495178686105, 1005371440044105, 1005503236863105, 1005389996171105, 1005415562555105, 1005315817407105, 1005232625584105, 1005145559671105, 1004967205754105, 1004895238611105, 1004629645245105, 1004572916260105, 1004214142636105, 1004173031951105, 1003742805612105, 1003711727497105, 1003196998561105, 1003178701788105, 1002573713985105, 1002561288208105, 1001966494005105, 1001969301046105, 1001346106952105, 1001361910326105, 1000720478458105, 1000750317336105, 1000090127522105, 1000134196850105, 999513136300105, 999569896201105, 999058760940105, 999120174812105, 998709653585105, 998776276493105, 998411012301105, 998478722468105, 998210195401105, 998282340937105, 997981107028105, 998055756921105, 997769185645105, 997841315946105, 997564267976105, 997639984028105, 997435606437105, 997512209467105, 997321048197105, 997401181550105, 997275171559105, 997351597353105, 997234022907105, 997307703141105, 997299877352105, 997366679450105, 997410826635105, 997467343748105, 997601275818105, 997647050887105, 997792946828105, 997827811816105, 997966539401105, 997991174224105, 998197802138105, 998214650643105, 998474956436105, 998488499969105, 998752926558105, 998762128452105, 999022998249105, 999028516343105, 999265326864105, 999266069158105, 999490256685105, 999487239736105, 999686586571105, 999679618835105, 999848796959105, 999839025407105, 1000011895680105, 999997451826105, 1000147574104105, 1000130308698105, 1000275480451105, 1000255902738105, 1000375373767105, 1000353332897105, 1000448188372105, 1000425389454105, 1000542604791105, 1000521891358105, 1000610854535105, 1000581983177105, 1000680446953105, 1000655675797105, 1000714774721105, 1000682805823105, 1000746534990105, 1000723727880105, 1000775312244105, 1000746467365105, 1000801867862105, 1000778765504105, 1000797895340105, 1000770487211105, 1000826402185105, 1000803519024105, 1000812453031105, 1000791583971105, 1000812233627105, 1000793291859105, 1000797109111105, 1000774405936105, 1000759655627105, 1000745744526105, 1000738447605105, 1000717571634105, 1000731381807105, 1000718011418105, 1000654802480105, 1000644103062105, 1000612649914105, 1000606941977105, 1000511545189105, 1000505935095105, 1000484570613105, 1000481181227105, 1000415453028105, 1000402985593105, 1000315480863105, 1000321014076105, 1000245353099105, 1000251808306105, 1000159467294105, 1000166418845105, 1000034435807105, 1000031254336105, 999981613984105, 999985617322105, 999894872797105, 999918708634105, 999937923072105, 999953283740105, 999856386145105, 999877919726105, 999792862145105, 999797609605105, 999731366321105, 999752172585105, 999725791963105, 999729224829105, 999707423033105, 999738637449105, 999735196557105, 999716334954105, 999651205364105, 999681262512105, 999647198460105, 999637127652105, 999623651089105, 999656757736105, 999672893753105, 999672005172105, 999763858807105, 999784267334105, 999741112851105, 999749210103105, 999783530811105, 999806152762105, 999782036430105, 999769751218105, 999832377580105, 999856682211105, 999886568674105, 999900913016105, 999984506515105, 1000013744838105, 999962515997105, 999954771163105, 1000012781026105, 1000021175188105, 999984952678105, 999994659516105, 1000071755577105, 1000088750715105, 999941112566105, 999940949954105, 999941006086105, 999924830821105, 999760352823105, 999756610375105, 1000135519852105, 1000143457385105, 999958537615105, 999978565348105],
  [14758927079105, 14231688140105, 21196629547105, 21075722592105, 46629215050105, 49137058404105, 44241866013105, 42823847378105, 124304439170105, 129235133999105, 182902665190105, 168112973333105, 354245072137105, 371587212603105, 464712601262105, 453714005887105, 540227129709105, 544817905917105, 691001403151105, 678023494856105, 718141033906105, 699937619735105, 902596496497105, 905977913272105, 965539026210105, 949746783931105, 971772898395105, 990036101577105, 952628744954105, 932203113443105, 708126728293105, 711458150265105, 531470764436105, 530241589280105, 690767968447105, 692242873217105, 708944367896105, 725554852559105, 746913419895105, 742354322848105, 637684201932105, 638102071933105, 1032064093992105, 1010542699624105, 954666018072105, 978709553662105, 667377271334105, 615777557059105, 642095115739105, 650933080473105, 667590421448105, 651786824503105, 697887379028105, 693253523374105, 849171952650105, 859342913496105, 874391892749105, 863693764870105, 843013218398105, 823596118884105, 959752972455105, 959939929439105, 897502603193105, 893382297704105, 909103018830105, 909764910794105, 1004864278720105, 1001228180560105, 897091339716105, 913306357573105, 964700741981105, 972617922048105, 988853028726105, 975865753794105, 849047398438105, 850735015488105, 831030321762105, 844162249772105, 853333114038105, 841889712886105, 841133317183105, 890754253779105, 1232501011036105, 1206879049219105, 1299385364594105, 1319260597643105, 957217095470105, 955460045610105, 1088025352005105, 1091290148195105, 1099564371496105, 1081451939883105, 1094251214335105, 1090966414837105, 957633079185105, 957020103607105, 1164929642136105, 1159694476129105, 1418441842311105, 1437201747027105, 1513911010015105, 1493986846560105, 1512116834347105, 1526187933452105, 1506131581909105, 1501192987514105, 1334562602337105, 1351416100788105, 1344095851769105, 1356189517532105, 1240405061081105, 1235048053189105, 1175774655630105, 1186094658161105, 1117823863810105, 1099696648791105, 934442369163105, 948391551274105, 912183136422105, 906557463978105, 840693216862105, 841352195072105, 860915294035105, 857611854482105, 846634629155105, 845908640204105, 853240060997105, 852921595270105, 852340207635105, 851486598216105, 865429701665105, 864569743843105, 878613381994105, 877753445326105, 891619365603105, 890700322263105, 904859015457105, 903944482467105, 917051483828105, 916054323984105, 928520534565105, 927729706962105, 937495636873105, 936411549017105, 944874662177105, 943954962923105, 951192611946105, 950183860492105, 955253167226105, 954450431286105, 958963902602105, 958416759389105, 959841009138105, 959229387418105, 959752287836105, 959377242283105, 959567888089105, 958898318858105, 959683943815105, 959315808527105, 963609275665105, 963203838080105, 970356106091105, 969962896209105, 974730375083105, 974299363214105, 978885547060105, 978183955431105, 982501690859105, 981890726687105, 987890862197105, 987230687680105, 987206148675105, 986862629269105, 987708983360105, 987010929087105, 992720021966105, 992809970285105, 998197869453105, 998153275693105, 1003359743777105, 1003569710478105, 1008136630564105, 1008403409066105, 1010620665248105, 1010730037276105, 1012740011926105, 1013035949860105, 1015394472160105, 1015985852587105, 1016263931398105, 1016864168487105, 1018118479554105, 1018798671406105, 1019818543137105, 1020496691275105, 1020059130663105, 1020805268807105, 1021979821292105, 1022478818264105, 1022874650871105, 1023245302950105, 1023399961628105, 1023998698288105, 1026130215132105, 1026706448635105, 1029177489871105, 1029553507393105, 1031916595448105, 1032498346330105, 1034891555623105, 1034699886397105, 1031816078478105, 1031991164855105, 1027633065450105, 1027526148850105, 1028729233884105, 1028642986428105, 1027802292439105, 1027663828902105, 1026686515386105, 1026818500418105, 1025628036723105, 1025832103402105, 1026684304171105, 1026904306290105, 1024523035767105, 1024815529741105, 1018363220718105, 1018369440101105, 1010622614333105, 1010936201785105, 1002787670218105, 1002883172682105, 994925845878105, 995107892458105, 989620987799105, 989537816046105, 984083371394105, 983814041280105, 980081016028105, 979890336575105, 977025937565105, 976667286175105, 974829951192105, 974754061894105, 975462103401105, 975166378300105, 976452048630105, 976243006619105, 978573781962105, 978349400831105, 980412840646105, 980237025213105, 982503495404105, 982335816119105, 984523320074105, 984358664230105, 986588652042105, 986434644344105, 988481579636105, 988338629064105, 990198146654105, 990066241670105, 991738127878105, 991618533148105, 993095260335105, 992988147369105, 994283039750105, 994189734803105, 995310126477105, 995227853095105, 996212875396105, 996146451801105, 997014477463105, 996961462305105, 997729909244105, 997691852382105, 998393082131105, 998366615353105, 999008554565105, 998990101024105, 999619840885105, 999610605393105, 1000242081126105, 1000238484354105, 1000876815969105, 1000883666001105, 1001519440682105, 1001532323485105, 1002110951870105, 1002130349674105, 1002606617365105, 1002632237023105, 1003041733521105, 1003074502207105, 1003418582486105, 1003462989982105, 1003744836550105, 1003798981036105, 1003992118117105, 1004057566472105, 1004253880717105, 1004326109203105, 1004512084842105, 1004596216609105, 1004695854745105, 1004779973548105, 1004796963686105, 1004883166970105, 1004819218799105, 1004903335564105, 1004767044037105, 1004848472661105, 1004675024846105, 1004756224182105, 1004548789636105, 1004626500680105, 1004379301193105, 1004449103673105, 1004193389610105, 1004254906279105, 1003975452474105, 1004027078868105, 1003727246806105, 1003768958085105, 1003471018428105, 1003501589533105, 1003180805019105, 1003203993715105, 1002871952434105, 1002889999712105, 1002550547656105, 1002559533295105, 1002181354781105, 1002181398641105, 1001759170333105, 1001753593820105, 1001288718196105, 1001273723578105, 1000765090182105, 1000752790002105, 1000281671319105, 1000266869488105, 999856651635105, 999843358672105, 999408208001105, 999396101307105, 998967793772105, 998957579018105, 998537770251105, 998525769524105, 998118369896105, 998102822963105, 997676269265105, 997656742688105, 997260420645105, 997235818135105, 996934052589105, 996908910600105, 996723488044105, 996692913040105, 996631581771105, 996599063914105, 996660222120105, 996624058796105, 996771706398105, 996736231772105, 996971471184105, 996939690785105, 997236646682105, 997207341763105, 997552843309105, 997528635512105, 997907707174105, 997884314766105, 998257768521105, 998238657594105, 998597367254105, 998581200559105, 998908239053105, 998895517126105, 999194924946105, 999184941879105, 999453007458105, 999445680903105, 999682083872105, 999677389891105, 999883510079105, 999881482388105, 1000057777246105, 1000057855180105, 1000208512502105, 1000211281019105, 1000337677380105, 1000341903889105, 1000443561964105, 1000448892967105, 1000537464022105, 1000545199302105, 1000608880469105, 1000616323374105, 1000672547851105, 1000683128086105, 1000723413626105, 1000732558580105, 1000762412037105, 1000773841608105, 1000798708355105, 1000810096124105, 1000817214119105, 1000828565695105, 1000834539109105, 1000848241776105, 1000843002901105, 1000853489120105, 1000835421899105, 1000848157261105, 1000835190231105, 1000845369703105, 1000823984858105, 1000834983604105, 1000807155534105, 1000818990682105, 1000768526123105, 1000780510689105, 1000712174546105, 1000724233318105, 1000678463220105, 1000691782323105, 1000629508965105, 1000642882225105, 1000578153262105, 1000587648355105, 1000513730402105, 1000524232382105, 1000451903612105, 1000462013435105, 1000390789940105, 1000400693958105, 1000319392097105, 1000324708629105, 1000235638132105, 1000240375722105, 1000175611112105, 1000181325431105, 1000125618374105, 1000126940374105, 1000044593865105, 1000044916857105, 999968154475105, 999961643729105, 999884011792105, 999877143720105, 999804429932105, 999798703489105, 999748309907105, 999741032130105, 999689578908105, 999682200107105, 999662067080105, 999661998609105, 999613241057105, 999604750945105, 999603153614105, 999600279956105, 999625678561105, 999628958242105, 999639708662105, 999642807196105, 999658342191105, 999661227605105, 999690046696105, 999689526969105, 999706994175105, 999702900205105, 999750455866105, 999736237384105, 999763506505105, 999767968628105, 999832434559105, 999821057494105, 999876741651105, 999867529561105, 999874407077105, 999857536227105, 999893009064105, 999893646654105, 999942850250105, 999931804965105, 999965261464105, 999962535308105, 999966037076105, 999952786383105, 999990535739105, 999984787866105, 1000042496773105, 1000049790720105, 1000079396877105, 1000080144923105, 1000071746365105, 1000065551221105, 1000078083601105, 1000078789334105, 1000082038573105, 1000083333803105, 1000080917297105, 1000082268621105, 1000045814565105, 1000059579732105, 1000042159124105, 1000056555826105],
  [148250534432105, 132600864764105, 240616069011105, 263270992917105, 274639663263105, 265267352845105, 335442972886105, 368147887525105, 508044176320105, 444500013199105, 566682370914105, 623405357751105, 917665997550105, 831699742319105, 773379335059105, 835646877519105, 614152863278105, 561496511670105, 757101791770105, 831657453987105, 733604677475105, 692848657625105, 661278128771105, 714064091784105, 542295228190105, 532906704254105, 633588992604105, 639670670179105, 584711606962105, 554574510650105, 464237871230105, 493337266857105, 489473420537105, 492685668851105, 473688448848105, 487831129319105, 519635380674105, 507140080635105, 673154119216105, 699994683282105, 879130352928105, 867458908404105, 998724118739105, 1031198666707105, 1062607814470105, 962647558504105, 953846438474105, 1018280271109105, 947093007332105, 924973267930105, 650348330640105, 670658361395105, 649453450947105, 622675481193105, 638928132705105, 632633835539105, 724723798801105, 684691430319105, 725186082302105, 688718705418105, 737612724486105, 763464986658105, 828416003808105, 830421081079105, 843977938454105, 840781853979105, 802135538183105, 774640391657105, 750687221548105, 785650441079105, 769086695570105, 808787829058105, 738932997516105, 745615718954105, 750248978341105, 777936571526105, 820435197605105, 801150974351105, 1102020435148105, 1125213468165105, 1228460384683105, 1164454236936105, 1207064387914105, 1308011096058105, 1310590941288105, 1280171839847105, 1180882279024105, 1194318473116105, 1042810222175105, 1017523394076105, 874171363494105, 888024837380105, 876146082319105, 863354944832105, 902386952097105, 900274716844105, 924849602794105, 896363903595105, 1009203278435105, 1039980995216105, 1120066974686105, 1115005430151105, 1039128404427105, 1049610294708105, 1247680342728105, 1195324609624105, 1256785335989105, 1297792142272105, 1428228303462105, 1353398648654105, 1189156687928105, 1241193703449105, 1494947032129105, 1431895173091105, 1527353526399105, 1612897336406105, 1352663186562105, 1295971006891105, 1201841515632105, 1265520377836105, 1150020361085105, 1117931481196105, 1069254225632105, 1078890360296105, 1088077372965105, 1065484812122105, 976486596753105, 992086638142105, 859136859176105, 859328140790105, 870244227264105, 870677197580105, 880076600253105, 880177705258105, 889541905035105, 889784528188105, 898188044237105, 897929823910105, 904281790516105, 905019865140105, 909553601762105, 909400125650105, 909438642580105, 910608936052105, 911554711510105, 911797772018105, 916205186351105, 917258025523105, 918688831049105, 918599796825105, 921586525297105, 922125261204105, 925650121888105, 925392189207105, 931645541961105, 931518153322105, 936304338939105, 936076341983105, 941797740828105, 942041508020105, 949259843392105, 949050267110105, 956444705719105, 956181288561105, 963984890354105, 963500574740105, 970921756378105, 970627981443105, 975570913661105, 974855286134105, 977079062795105, 976527115317105, 976732046957105, 975672572433105, 975398328724105, 975873808337105, 975737948054105, 975207791197105, 976192025992105, 976005404177105, 981280736133105, 980776062284105, 986464841936105, 986374485375105, 991892252317105, 991899168695105, 996067535586105, 996694276331105, 1000296991520105, 1001507170138105, 1004398564332105, 1005229481695105, 1007152910067105, 1007960143205105, 1009704664930105, 1010569136874105, 1012949545504105, 1014253228816105, 1017046742882105, 1017824544302105, 1020923068939105, 1021090632953105, 1025322717379105, 1025399170965105, 1029613316978105, 1029272160768105, 1032881327845105, 1032822698897105, 1031796644286105, 1031373035218105, 1028725781967105, 1029295402311105, 1025938347612105, 1024932628978105, 1021495713284105, 1020948235692105, 1019005006487105, 1018238524901105, 1018633101322105, 1018263615122105, 1020893473433105, 1020298156087105, 1023157712751105, 1022749258924105, 1025038791267105, 1024662936467105, 1026607786667105, 1026667934158105, 1026879150285105, 1026450996563105, 1025422186188105, 1025075327284105, 1025198854729105, 1024683789459105, 1021727338007105, 1022022028934105, 1018053119129105, 1017700893941105, 1011645115024105, 1012474821267105, 1008862859449105, 1008887696291105, 1001278039708105, 1002264480058105, 993053617040105, 992738262488105, 987444314795105, 988002963725105, 984091868240105, 983671475166105, 981500684768105, 981577365902105, 980130599672105, 980053220011105, 978449194439105, 978719251772105, 978479391650105, 978518895157105, 980343986503105, 980380730087105, 982064252197105, 982094385581105, 983657438664105, 983686326058105, 985127460892105, 985152947463105, 986485377386105, 986515189523105, 987769436771105, 987787732056105, 988991196459105, 989012096852105, 990233394557105, 990236552604105, 991462009527105, 991461186901105, 992637145006105, 992619879361105, 993792001846105, 993775715334105, 994919582980105, 994894750385105, 996001265050105, 995979746343105, 997006174731105, 996986364312105, 997953993427105, 997937521297105, 998830841252105, 998810354553105, 999604808285105, 999587362133105, 1000278547795105, 1000265087033105, 1000845213160105, 1000839104446105, 1001312444714105, 1001310800131105, 1001714146721105, 1001723517528105, 1002098485063105, 1002116685532105, 1002494566568105, 1002529317400105, 1002917546761105, 1002945524749105, 1003341966970105, 1003378740931105, 1003765680785105, 1003806170031105, 1004116514644105, 1004165484083105, 1004391763219105, 1004442854849105, 1004586667583105, 1004638308795105, 1004719299964105, 1004762032037105, 1004787974086105, 1004812290738105, 1004793563846105, 1004805182441105, 1004756392613105, 1004755314183105, 1004678419440105, 1004663873216105, 1004548662670105, 1004513619977105, 1004353565670105, 1004306188333105, 1004095244843105, 1004044711843105, 1003764723601105, 1003712218503105, 1003362086221105, 1003313998102105, 1002903463245105, 1002855567059105, 1002455586926105, 1002413493829105, 1002048849291105, 1001996978272105, 1001679172667105, 1001642317043105, 1001373044713105, 1001344159331105, 1001100800691105, 1001083525993105, 1000829614059105, 1000817399847105, 1000518043610105, 1000515056355105, 1000166077363105, 1000169505261105, 999778728124105, 999788026234105, 999360273519105, 999368904595105, 998931358060105, 998947100849105, 998518512257105, 998540062806105, 998102150787105, 998132236356105, 997732834188105, 997758725851105, 997415146332105, 997447439732105, 997192610030105, 997212035313105, 997009636778105, 997029252307105, 996941994619105, 996946601328105, 997000697590105, 997010397314105, 997148425523105, 997149153449105, 997350506724105, 997358189267105, 997596495765105, 997602809827105, 997865806773105, 997873924333105, 998163168459105, 998165495428105, 998466880934105, 998469799351105, 998747371094105, 998748850213105, 999000341090105, 999002670862105, 999233316342105, 999232922198105, 999446609972105, 999445872860105, 999645982291105, 999646057915105, 999835109345105, 999832048627105, 999983942561105, 999985365152105, 1000132937005105, 1000129060144105, 1000267625355105, 1000268168782105, 1000396436506105, 1000390801143105, 1000503150731105, 1000503373430105, 1000583174199105, 1000578987651105, 1000662058529105, 1000665529137105, 1000722542754105, 1000722386360105, 1000767778801105, 1000770196106105, 1000801822934105, 1000800951729105, 1000815844498105, 1000818433446105, 1000836468092105, 1000835478927105, 1000832368700105, 1000836657563105, 1000807473456105, 1000814003802105, 1000789641581105, 1000799208858105, 1000778376711105, 1000777887508105, 1000753344861105, 1000762880612105, 1000733427379105, 1000729499896105, 1000685043021105, 1000693906792105, 1000634471782105, 1000627694688105, 1000574854648105, 1000571799262105, 1000521214654105, 1000513570198105, 1000453065171105, 1000453939441105, 1000385028487105, 1000375123850105, 1000308056020105, 1000310280178105, 1000255966851105, 1000239282669105, 1000164261671105, 1000163026942105, 1000108284850105, 1000098522774105, 1000082293140105, 1000092668732105, 1000047517115105, 1000041146273105, 1000013710461105, 1000008318516105, 999953075154105, 999962597636105, 999987030511105, 999995550083105, 1000001267241105, 1000005105761105, 999978611775105, 999972497239105, 999940960094105, 999948085292105, 999917360926105, 999913692348105, 999883687490105, 999881725758105, 999835056276105, 999812235617105, 999771101116105, 999782227216105, 999757027159105, 999755205448105, 999711155462105, 999714267160105, 999681586312105, 999686789393105, 999706247546105, 999719248198105, 999721026439105, 999724659781105, 999692123478105, 999707551449105, 999673080527105, 999677384894105, 999705840908105, 999728674690105, 999733199541105, 999727901323105, 999737294197105, 999769865222105, 999768430831105, 999762803276105, 999734558720105, 999749028257105, 999815541563105, 999789073928105, 999831825534105, 999860182545105, 999885430501105, 999876142008105, 999795956557105, 999830067099105],
  [254193110786105, 254343788452105, 223857081407105, 219706560709105, 255946275487105, 263576291547105, 348506405767105, 377860556084105, 413821417269105, 432451857361105, 550970402931105, 520945017435105, 216641082280105, 216885503337105, 417829593320105, 419279264680105, 353128659565105, 332737515370105, 422284648318105, 428344289214105, 564112212653105, 543523461670105, 678846989859105, 713856652181105, 745085140398105, 719330029799105, 651414195971105, 663031156170105, 958806136476105, 940587485719105, 583755864072105, 596711373724105, 665143138111105, 615921556056105, 776115383096105, 749005462445105, 619190267072105, 604656856479105, 1045679180482105, 1070032771519105, 842722517006105, 945232983519105, 1041957115152105, 993965381681105, 652442034012105, 697631861263105, 634701205079105, 661588966808105, 749527637011105, 743763676209105, 942459743858105, 918326461891105, 670875905770105, 678433616523105, 822158991200105, 823490110278105, 777718637104105, 746267948768105, 977814376998105, 993452148071105, 636572110001105, 625664088246105, 830721018819105, 843779176867105, 856503055276105, 844161848971105, 661546215278105, 673149599796105, 1055196188817105, 1040189335453105, 836159857681105, 868499260931105, 939315387985105, 939358605774105, 819535747724105, 813234982590105, 1086586240248105, 1112253360894105, 940622140943105, 948412547564105, 883485228116105, 858320127296105, 944229143758105, 899668767323105, 1270850192343105, 1319521675333105, 1256743780700105, 1154075633609105, 1417904303108105, 1391405101540105, 984128370820105, 996330923442105, 1155559377131105, 1180951574940105, 1050153988194105, 1098826129317105, 1056679593969105, 1043729422467105, 1431761053886105, 1450072302690105, 1186939127344105, 1175515219963105, 1273023584721105, 1299195381548105, 1298594032065105, 1263865395646105, 1157047340451105, 1177696754080105, 1066643388308105, 1060862299372105, 992899643408105, 1013804797707105, 1101502297858105, 1100876332554105, 919713299971105, 920274654663105, 1246282891245105, 1277594002210105, 1184021013069105, 1166874020261105, 1153834874478105, 1125233830733105, 1061704329181105, 1054256668340105, 1037851458486105, 1042135273856105, 1092675976251105, 1092734161590105, 855403229336105, 855602403348105, 864796603777105, 865000619732105, 874807196972105, 875081458250105, 884479672200105, 884638875664105, 892853219256105, 892554646812105, 900344762131105, 899725244099105, 905797178540105, 905670206545105, 916569081994105, 916414908295105, 924355640312105, 924188944614105, 933282259691105, 933433079895105, 941255515894105, 941327825064105, 947166854827105, 947523560616105, 951340972026105, 951186783785105, 954570561112105, 954814451899105, 959309705937105, 959341127946105, 959319294126105, 959655132251105, 965172453423105, 965336759896105, 969874657702105, 970783775214105, 972893733141105, 974274436968105, 978421598075105, 980006518378105, 977369693420105, 978619198537105, 979475903768105, 979123318769105, 978508935690105, 978909969179105, 983594368870105, 983309702094105, 989046689329105, 988339816894105, 992784105158105, 992142397969105, 993577107357105, 993310465994105, 998609917742105, 998230589130105, 1001377760901105, 1000962289451105, 1004871806822105, 1004914139188105, 1005290103063105, 1005125072645105, 1011049297474105, 1011041497435105, 1013874455372105, 1013644724353105, 1016318917219105, 1016322433242105, 1021867331387105, 1021654573699105, 1021352406200105, 1021379048650105, 1024246259855105, 1023756659475105, 1025562190454105, 1025088300073105, 1028786433140105, 1028372392442105, 1027887024267105, 1027072355438105, 1029242674718105, 1028312591931105, 1031518031775105, 1030974896258105, 1032883249995105, 1033006149003105, 1029155319044105, 1028540398912105, 1025608838061105, 1026549445483105, 1019479027242105, 1020878682079105, 1020036793277105, 1021243151988105, 1017913845337105, 1018757410334105, 1017405208738105, 1017520862135105, 1016794658543105, 1017081092996105, 1010308839733105, 1010334426003105, 1007548252982105, 1007752145844105, 1003403477106105, 1003192737064105, 998796839983105, 999119375713105, 996319658198105, 996336525879105, 995226379483105, 995335202176105, 995263979603105, 995035284849105, 993599081256105, 993400588872105, 994752575070105, 994523380748105, 990822756706105, 990108077196105, 987806700141105, 987344868746105, 985213072403105, 985193881901105, 984017913152105, 984117865653105, 983181301579105, 983200587561105, 981471780668105, 981503903903105, 983441491591105, 983471210393105, 985295690375105, 985321523337105, 987021940383105, 987043783873105, 988623810897105, 988643325449105, 990119924238105, 990144326737105, 991522169387105, 991556997887105, 992861031098105, 992898203456105, 994052475914105, 994092822831105, 995140821734105, 995184401638105, 996106866683105, 996148810280105, 996963568575105, 997004502907105, 997740840673105, 997777293307105, 998465351168105, 998504586284105, 999150596768105, 999186380850105, 999772380846105, 999808818501105, 1000403588081105, 1000435343320105, 1000953685234105, 1000983170703105, 1001438548871105, 1001454202944105, 1001884050707105, 1001877836708105, 1002250223713105, 1002219379971105, 1002638383174105, 1002587469584105, 1003000068695105, 1002954010002105, 1003382005704105, 1003329189132105, 1003691152321105, 1003641765763105, 1003919660961105, 1003880447984105, 1004093287890105, 1004063418135105, 1004257110602105, 1004230957926105, 1004344568799105, 1004323683229105, 1004390076189105, 1004375141789105, 1004381909695105, 1004366773883105, 1004367380042105, 1004354216218105, 1004262853357105, 1004249696045105, 1004111877684105, 1004102401950105, 1003921196479105, 1003911329974105, 1003640953081105, 1003634267351105, 1003364481112105, 1003357172453105, 1003038289347105, 1003038777552105, 1002687079910105, 1002694796155105, 1002280441629105, 1002295264983105, 1001881276104105, 1001909435790105, 1001455244452105, 1001498033492105, 1000986869842105, 1001038735903105, 1000490225967105, 1000540841146105, 1000044104012105, 1000104842082105, 999646093253105, 999693420840105, 999337896829105, 999363890584105, 999015994012105, 999023912169105, 998723136769105, 998717845793105, 998434057849105, 998426719036105, 998150216581105, 998138314373105, 997962961973105, 997950446858105, 997815370193105, 997799019765105, 997728967618105, 997715512270105, 997713519511105, 997694960610105, 997736558247105, 997717757697105, 997777668356105, 997756688552105, 997818032524105, 997800849702105, 997882747116105, 997868332088105, 997931172431105, 997920431212105, 998042330775105, 998042410892105, 998201567901105, 998208789938105, 998404511982105, 998411614544105, 998623261767105, 998628872097105, 998861805400105, 998867720227105, 999135743773105, 999141563151105, 999370581455105, 999375864171105, 999588222432105, 999593868740105, 999771058746105, 999776192223105, 999950052592105, 999955483872105, 1000100377184105, 1000102657419105, 1000220645708105, 1000223222324105, 1000337155455105, 1000340568858105, 1000426748565105, 1000429700104105, 1000522359278105, 1000524914044105, 1000580285467105, 1000578762896105, 1000634730261105, 1000638328459105, 1000678043082105, 1000678031623105, 1000708149482105, 1000707224254105, 1000737403123105, 1000734281681105, 1000734624071105, 1000732601956105, 1000761066769105, 1000758113219105, 1000742201837105, 1000735788310105, 1000737677593105, 1000732075057105, 1000725973758105, 1000726692812105, 1000691680390105, 1000690760200105, 1000685107996105, 1000682397582105, 1000633360891105, 1000629189322105, 1000619669961105, 1000616959347105, 1000560130687105, 1000556795006105, 1000490984206105, 1000490773459105, 1000442822570105, 1000438084878105, 1000346919341105, 1000350167148105, 1000291239643105, 1000286513680105, 1000247671547105, 1000257671834105, 1000187047778105, 1000187705206105, 1000141701308105, 1000145076748105, 1000036895287105, 1000045152868105, 1000016507562105, 1000032336774105, 999962135293105, 999966812354105, 999923305955105, 999918681674105, 999857741052105, 999866125480105, 999840155453105, 999842396310105, 999827849692105, 999846086317105, 999788943762105, 999790476019105, 999773581778105, 999768784077105, 999745578712105, 999750939366105, 999745009934105, 999742334916105, 999728969929105, 999732740855105, 999719188901105, 999712106041105, 999728756742105, 999733189281105, 999741260079105, 999737135296105, 999801617717105, 999789264377105, 999840984591105, 999851660018105, 999883087765105, 999869436787105, 999889169746105, 999895765419105, 999885834692105, 999862519763105, 999838643097105, 999830902964105, 999907017082105, 999896117300105, 999931524054105, 999957382342105, 1000018968062105, 1000004145798105, 1000002499375105, 1000026740758105, 999881142567105, 999893795626105, 999959231747105, 999974957328105, 1000023684289105, 1000023008534105, 1000009403732105, 1000003820892105, 1000079993637105, 1000051854098105, 999711791802105, 999718824920105],
  [224493041516105, 250177608765105, 383654905448105, 362472685673105, 284062606020105, 305838079713105, 339423072632105, 313590551389105, 532123931987105, 556482001529105, 728469479309105, 677077411581105, 650585926568105, 712527879064105, 1012458116537105, 919948291436105, 896866946480105, 948720174644105, 914034096759105, 873053025498105, 621560155242105, 644974391468105, 532335474583105, 540747745900105, 477211830996105, 487342657719105, 637072103734105, 668091686703105, 450025916415105, 463257697309105, 639701544054105, 658965369075105, 725779085117105, 676638512862105, 751831038566105, 743190437340105, 681339405169105, 693453338866105, 564536830238105, 569149589276105, 671371205704105, 665570821429105, 623995844724105, 645720929972105, 643887962708105, 667060617533105, 720783095308105, 696939221225105, 737553195473105, 717368335638105, 795222868844105, 798954263573105, 698971095050105, 708716182591105, 687157419511105, 719135613297105, 640264368463105, 630954141483105, 899662885148105, 872199858355105, 687644381269105, 672280956610105, 1003894989215105, 1029917806774105, 1045500161306105, 1020091282622105, 714706496507105, 730524553419105, 939420591217105, 968016425279105, 722712914964105, 733747610024105, 833424920690105, 802841684540105, 847099803726105, 838122301470105, 963059837196105, 959896056835105, 907728578253105, 928752225446105, 912375291195105, 937757194389105, 907178064309105, 885573583844105, 910101065889105, 889270517656105, 954571835716105, 961033197282105, 881960747533105, 878033152685105, 1030879446257105, 1019203398284105, 1108336451487105, 1117368962168105, 1069676942467105, 1120117217364105, 1079015254423105, 1061535274573105, 907406590737105, 895482149415105, 1136859446164105, 1106472818707105, 981490454390105, 971357864926105, 1058679715931105, 1049978067474105, 1189522034731105, 1165320738909105, 1449832255229105, 1490285092341105, 1562978235592105, 1510419978851105, 1573000541063105, 1665432665113105, 1401297487153105, 1339747985082105, 1398320646051105, 1449946901139105, 1308269634195105, 1284564049432105, 1090714725585105, 1117244758605105, 1104787813808105, 1083782108858105, 1184349127599105, 1206304723158105, 1094469206037105, 1069502880659105, 861384454814105, 861717045577105, 871341257062105, 871257509230105, 878961611234105, 879208094691105, 888250898022105, 888170772473105, 896819716638105, 897146890820105, 902517346825105, 902460871109105, 905233682512105, 905997384905105, 909208250358105, 909000271745105, 907598617832105, 908829672728105, 907769183503105, 908204054470105, 907680204417105, 908760111682105, 912151956629105, 912881457205105, 918078729648105, 918710308077105, 924973258374105, 925434257975105, 929469160675105, 929471224664105, 936961434865105, 936749715249105, 941596402099105, 941091348310105, 944978825659105, 945212871183105, 947996447583105, 948370541454105, 952160492079105, 952361145828105, 958212922399105, 958344669232105, 962699822298105, 962922471375105, 967990769358105, 967880507577105, 973052201472105, 972578355090105, 976995420804105, 976886036147105, 980737115839105, 980932655321105, 983639184319105, 983775455933105, 988082711503105, 988076579158105, 992782045363105, 992293503101105, 998292115510105, 997916629153105, 999826472699105, 999905483181105, 1004706970641105, 1005004227071105, 1004723383647105, 1004599652962105, 1004085444154105, 1004381722654105, 1008607219165105, 1008643080604105, 1009687447072105, 1009293774487105, 1014168670913105, 1013597088503105, 1016989868556105, 1016893039308105, 1019647298388105, 1019675839943105, 1020531332795105, 1020612768584105, 1022299892129105, 1022044135131105, 1024009785511105, 1023362626459105, 1025835744377105, 1025517120100105, 1027640690686105, 1027642223778105, 1028785141932105, 1028689790830105, 1031073104251105, 1031037317533105, 1031079019908105, 1031220867792105, 1029875767589105, 1029876052299105, 1029259637987105, 1028460177078105, 1028474455829105, 1027957999543105, 1030365365833105, 1030010949972105, 1028703312344105, 1028828571856105, 1029441862787105, 1029727004865105, 1028978382270105, 1029410634510105, 1026466246182105, 1027277688820105, 1019849070479105, 1020040323188105, 1011372809813105, 1012363789162105, 1002586709400105, 1002176980673105, 996363764765105, 996898176097105, 990087950645105, 989821942866105, 985119666246105, 985227284425105, 983464187133105, 983168352356105, 981572806895105, 981586563802105, 978407174045105, 978075315936105, 976595784918105, 976659735726105, 978395956545105, 978455091842105, 980068609190105, 980129278411105, 981647759509105, 981705777047105, 983106425003105, 983166534470105, 984454168957105, 984510021076105, 985733998176105, 985791516683105, 986991302895105, 987037369901105, 988206097085105, 988255936934105, 989464812324105, 989496174475105, 990740689010105, 990765657310105, 992037542413105, 992046239878105, 993284898550105, 993282430464105, 994459439978105, 994446888039105, 995544713017105, 995524907413105, 996576536338105, 996556202561105, 997507292089105, 997489966907105, 998380466451105, 998370449169105, 999214484738105, 999200791883105, 1000014275573105, 999994666720105, 1000761580713105, 1000738472635105, 1001425975458105, 1001400487073105, 1002030482948105, 1002001052721105, 1002561756126105, 1002533592857105, 1003022523488105, 1003001218484105, 1003428829191105, 1003408973887105, 1003783248179105, 1003759976712105, 1004097601835105, 1004072182991105, 1004347509311105, 1004321749214105, 1004527734068105, 1004508780911105, 1004624589166105, 1004611509382105, 1004699252168105, 1004684141985105, 1004698980911105, 1004678949167105, 1004697489082105, 1004679347787105, 1004706149553105, 1004683015784105, 1004644971946105, 1004621273348105, 1004566960300105, 1004548962732105, 1004418322291105, 1004409032969105, 1004223664147105, 1004215591338105, 1003985204169105, 1003976743002105, 1003729525634105, 1003719605615105, 1003441862510105, 1003435988189105, 1003124042020105, 1003128189328105, 1002773312277105, 1002782454767105, 1002388962309105, 1002398102725105, 1001979949130105, 1001990493099105, 1001528247959105, 1001539502504105, 1001069539503105, 1001078521694105, 1000621484222105, 1000630759773105, 1000175362474105, 1000197412201105, 999734207801105, 999764745711105, 999256887958105, 999293790616105, 998797061370105, 998832899828105, 998318208396105, 998349958402105, 997838601516105, 997864160244105, 997391252699105, 997404273082105, 997039478383105, 997049762554105, 996813589594105, 996808991956105, 996720166592105, 996721600880105, 996720928258105, 996713934894105, 996820279722105, 996817972450105, 997000825459105, 996996643629105, 997210042712105, 997210787568105, 997449457396105, 997449346086105, 997740309853105, 997746554118105, 998071398665105, 998075921911105, 998372258235105, 998375952646105, 998649743983105, 998651801725105, 998904959823105, 998905828244105, 999156017571105, 999156198803105, 999385213036105, 999383972678105, 999587464219105, 999585813806105, 999776685110105, 999771201449105, 999947534375105, 999948147394105, 1000121702003105, 1000115327843105, 1000261273813105, 1000257905433105, 1000394775058105, 1000386571723105, 1000518591327105, 1000512281549105, 1000625490564105, 1000618599577105, 1000689853019105, 1000683535836105, 1000749362574105, 1000745744116105, 1000804045860105, 1000799675483105, 1000858401911105, 1000856237873105, 1000877331231105, 1000874923512105, 1000893024050105, 1000889745729105, 1000890413326105, 1000891234633105, 1000874374668105, 1000871455419105, 1000856671147105, 1000857543539105, 1000842275439105, 1000841850425105, 1000810078063105, 1000814024233105, 1000779517763105, 1000776804920105, 1000728782367105, 1000729074535105, 1000669668062105, 1000666162122105, 1000599089436105, 1000590238566105, 1000538393125105, 1000541032328105, 1000474163494105, 1000472205374105, 1000428695829105, 1000424158914105, 1000300973324105, 1000302215361105, 1000245864141105, 1000245992642105, 1000220785649105, 1000231026064105, 1000216013609105, 1000215144720105, 1000184898951105, 1000196165628105, 1000141274346105, 1000147458686105, 1000133032869105, 1000145455168105, 1000094940499105, 1000097412816105, 1000028290777105, 1000030088357105, 1000036298306105, 1000038724952105, 1000029758725105, 1000030968703105, 999991582345105, 999986161381105, 999908187360105, 999905514965105, 999839932664105, 999843485224105, 999823769304105, 999818631716105, 999753525032105, 999757683822105, 999702233633105, 999693789247105, 999667856308105, 999675722844105, 999683170649105, 999693086859105, 999629229383105, 999644631662105, 999616419187105, 999607704191105, 999600270861105, 999610748062105, 999646940987105, 999643794618105, 999627615663105, 999640953717105, 999609223661105, 999619027868105, 999555333896105, 999547480050105, 999498408791105, 999492963681105, 999577892929105, 999614191765105, 999750906773105, 999742251911105, 999781811766105, 999822724246105, 999654569159105, 999612175678105],
  [143633643335105, 148975131505105, 94494380540105, 93726719861105, 172062150236105, 178566962010105, 199708527112105, 185864096680105, 206555587858105, 212743434807105, 301016466876105, 311566151114105, 295235729998105, 294039790579105, 278245897804105, 265699603287105, 412309041697105, 425544948359105, 494471575811105, 507517324492105, 512466657201105, 508880326952105, 446772113472105, 435850113283105, 641804300771105, 627516826675105, 606347608002105, 609173091260105, 395115873362105, 401411296908105, 494778123996105, 503831385962105, 653942737481105, 645093455555105, 852908915874105, 904285712167105, 1475958406011105, 1418858821549105, 1549230206920105, 1569324974030105, 888964050607105, 891547105856105, 796344635202105, 822089409795105, 1002204390748105, 925057558544105, 893486724185105, 914134650638105, 832076314729105, 810919818151105, 743761364915105, 755791648102105, 727993061624105, 716958941298105, 730047991203105, 755094131072105, 937352738174105, 940964799577105, 762620331636105, 756556627562105, 802499085985105, 774300044164105, 650172758089105, 650281473882105, 660946979748105, 659826828759105, 807391640043105, 835002133595105, 814086518220105, 820087690625105, 1025917966292105, 1022279981212105, 867876617571105, 842360066879105, 854506057154105, 864841504611105, 918499345784105, 905741685984105, 1000651449484105, 1021211360276105, 1133785408646105, 1112539941608105, 1176879873275105, 1254302504034105, 1105145669717105, 1080487724239105, 1205800408456105, 1203876228746105, 1926942666640105, 1907160201403105, 1828756372668105, 1886755544012105, 1356888699254105, 1306515016331105, 1128978915759105, 1138180039286105, 1013229463520105, 1004531870896105, 932910483658105, 926736089552105, 1164771706606105, 1161923693746105, 1211119491952105, 1225569550900105, 1045186741338105, 1056668912552105, 1142502265145105, 1146876316456105, 1166923496488105, 1154527942466105, 1109830164846105, 1096849115156105, 971480037130105, 984275074166105, 1019589334238105, 1021264562939105, 1057919247155105, 1047700370279105, 978953927509105, 972827055190105, 970273417678105, 984307898654105, 980926169677105, 974733712047105, 912884613431105, 913870878560105, 984717633771105, 979540581878105, 851124070078105, 851200646674105, 862179927505105, 862175084493105, 874179868789105, 874182680685105, 885148547333105, 885055361438105, 895859504988105, 895976435222105, 906630769967105, 906642293476105, 916085150278105, 915940610658105, 925777913897105, 925664528341105, 935901935890105, 935971998678105, 944088510282105, 943947808937105, 951109575890105, 950768835198105, 957960803441105, 957681819866105, 965952563826105, 965809881809105, 971015638639105, 971088937775105, 976711028261105, 976769096875105, 985802087305105, 985762862322105, 993473283608105, 993282424523105, 998759479577105, 998727380528105, 1001027628491105, 1000176831994105, 993622665578105, 993614183048105, 984950098079105, 984653120911105, 986446611604105, 986115722323105, 989410007038105, 988664189316105, 989218236308105, 989656468192105, 990715045155105, 990843386835105, 993195388154105, 993665128402105, 997089097421105, 997379878900105, 1001296354626105, 1001760308891105, 1005528605087105, 1005603203350105, 1006595526905105, 1006624684969105, 1010418414376105, 1010517058202105, 1013665001259105, 1014220378048105, 1019333486773105, 1019909485587105, 1024933660580105, 1025526263678105, 1028333121005105, 1028508333450105, 1031678947548105, 1031752377072105, 1031770357198105, 1031913405325105, 1034338658304105, 1034878393703105, 1037145901091105, 1037523842854105, 1038989731985105, 1039574207879105, 1039580615450105, 1039859401148105, 1038122041021105, 1038720404886105, 1035946327326105, 1035367882134105, 1034850872247105, 1034680735597105, 1032177883285105, 1031987247462105, 1018209290545105, 1018297167516105, 1005540438001105, 1004759365301105, 1000061856618105, 1000050956199105, 998049792264105, 997893944633105, 997806831030105, 997802677000105, 998819008034105, 998902951512105, 996232052537105, 996346184923105, 992872384060105, 992777792466105, 992053700178105, 991775329929105, 989702688494105, 989351008183105, 986938285890105, 986767909990105, 985018252287105, 985057488704105, 985229276935105, 985068455961105, 984692951445105, 984499394406105, 983550197533105, 983517381464105, 983624529095105, 983684544613105, 983832726308105, 983673348125105, 983878016754105, 983819654586105, 984989637646105, 984904464336105, 984995211039105, 984996579575105, 987087005542105, 987087390939105, 989038979959105, 989038847299105, 990833592208105, 990833380386105, 992484722363105, 992485864321105, 993994269441105, 993993550981105, 995359010202105, 995358234720105, 996597306607105, 996598748546105, 997703484943105, 997706563179105, 998668653580105, 998670589957105, 999520913925105, 999525067655105, 1000276742432105, 1000286299439105, 1000937249426105, 1000951008775105, 1001483136781105, 1001499613176105, 1001958358523105, 1001974505730105, 1002352113620105, 1002367619412105, 1002610021350105, 1002626185276105, 1002751965333105, 1002771513595105, 1002813998104105, 1002833839358105, 1002841925115105, 1002875020312105, 1002985401626105, 1003019638814105, 1003266235486105, 1003305745683105, 1003528334287105, 1003573451910105, 1003748591243105, 1003805945539105, 1003975392039105, 1004026917591105, 1004182167875105, 1004232454560105, 1004352951833105, 1004396749815105, 1004465847251105, 1004505616980105, 1004514898512105, 1004547983032105, 1004499064621105, 1004531509317105, 1004466024367105, 1004498353516105, 1004372644042105, 1004404293742105, 1004227075509105, 1004250590598105, 1003990132798105, 1004004936299105, 1003661764892105, 1003667579276105, 1003275750036105, 1003278816384105, 1002831859363105, 1002834061528105, 1002379768457105, 1002379654067105, 1001880385893105, 1001872023954105, 1001329278709105, 1001315243232105, 1000741245580105, 1000718133669105, 1000135469977105, 1000107350653105, 999543048985105, 999505458545105, 998975169449105, 998945835093105, 998415237814105, 998387274543105, 997888375079105, 997862672744105, 997571443146105, 997544485039105, 997448241000105, 997433088614105, 997409339122105, 997394437305105, 997401817682105, 997389126863105, 997398335263105, 997385056043105, 997377899590105, 997363090371105, 997397703474105, 997381260520105, 997471672586105, 997456584612105, 997561368978105, 997550313526105, 997688524362105, 997682657211105, 997859604006105, 997856475263105, 998063618126105, 998059765758105, 998266481179105, 998264888415105, 998479929510105, 998481215251105, 998714597944105, 998716167753105, 998949254772105, 998949787607105, 999185428103105, 999188613296105, 999420482427105, 999424398025105, 999646030310105, 999651816951105, 999875672809105, 999882198591105, 1000068789834105, 1000075093543105, 1000239072187105, 1000245376053105, 1000376959030105, 1000381533469105, 1000498114388105, 1000504957111105, 1000596378295105, 1000601884804105, 1000665868513105, 1000671928061105, 1000723766338105, 1000728911382105, 1000766476151105, 1000772634066105, 1000798994711105, 1000807128409105, 1000815529233105, 1000823676246105, 1000812155048105, 1000818115325105, 1000813205864105, 1000820403971105, 1000801104480105, 1000807420142105, 1000783487549105, 1000790861093105, 1000759575389105, 1000762784886105, 1000725795465105, 1000732776938105, 1000695292312105, 1000701226863105, 1000673651139105, 1000678179574105, 1000622641651105, 1000630421432105, 1000569685557105, 1000576527912105, 1000537987903105, 1000541989617105, 1000507739130105, 1000507116659105, 1000474165434105, 1000473566511105, 1000406265613105, 1000405098671105, 1000322201630105, 1000327876557105, 1000268162214105, 1000270413194105, 1000215385146105, 1000216411512105, 1000174413898105, 1000171617013105, 1000088227915105, 1000086466193105, 1000030789614105, 1000024715224105, 999954526467105, 999954650432105, 999845084968105, 999844740618105, 999764637689105, 999763618696105, 999742461508105, 999737952327105, 999714562119105, 999717561557105, 999678691299105, 999671025286105, 999634973981105, 999646032789105, 999598083292105, 999606063967105, 999596221461105, 999592998501105, 999607363820105, 999590105984105, 999618859672105, 999615663141105, 999600783894105, 999590697605105, 999566350093105, 999568619507105, 999588548712105, 999574586762105, 999627782188105, 999624821799105, 999702102650105, 999706264328105, 999791678260105, 999807351242105, 999871786365105, 999860871910105, 999925623645105, 999912348361105, 999895747658105, 999902014481105, 999952667974105, 999967393140105, 1000081359471105, 1000094644965105, 1000238177104105, 1000238269200105, 1000239770292105, 1000236367948105, 1000208576462105, 1000213533118105, 1000264165608105, 1000265818602105, 1000232546842105, 1000226909772105, 1000204925670105, 1000195314753105, 1000233403762105, 1000224748898105, 1000098638926105, 1000091202996105, 1000186463958105, 1000196712220105, 999933244146105, 999927120320105]
]

/- Original list numerators above are retained for independent audit.
The following balanced integer lookup definitions encode exactly the same entries. -/


def kernelRow0LLLLLL (i : ℕ) : ℕ := if i < 1 then 1213946189 else 1264471874
def kernelRow0LLLLLR (i : ℕ) : ℕ := if i < 3 then 958096528 else 944113919
def kernelRow0LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow0LLLLLL i else kernelRow0LLLLLR i
def kernelRow0LLLLRL (i : ℕ) : ℕ := if i < 5 then 1691464608 else 1658228109
def kernelRow0LLLLRR (i : ℕ) : ℕ := if i < 7 then 2537899164 else 2520256063
def kernelRow0LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow0LLLLRL i else kernelRow0LLLLRR i
def kernelRow0LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow0LLLLL i else kernelRow0LLLLR i
def kernelRow0LLLRLL (i : ℕ) : ℕ := if i < 9 then 3667606505 else 3628506270
def kernelRow0LLLRLR (i : ℕ) : ℕ := if i < 11 then 3979393375 else 4136945299
def kernelRow0LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow0LLLRLL i else kernelRow0LLLRLR i
def kernelRow0LLLRRL (i : ℕ) : ℕ := if i < 13 then 2685484155 else 2867040651
def kernelRow0LLLRRR (i : ℕ) : ℕ := if i < 15 then 4114616174 else 4356846463
def kernelRow0LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow0LLLRRL i else kernelRow0LLLRRR i
def kernelRow0LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow0LLLRL i else kernelRow0LLLRR i
def kernelRow0LLL (i : ℕ) : ℕ := if i < 8 then kernelRow0LLLL i else kernelRow0LLLR i
def kernelRow0LLRLLL (i : ℕ) : ℕ := if i < 17 then 3361765321 else 3422299798
def kernelRow0LLRLLR (i : ℕ) : ℕ := if i < 19 then 4738031554 else 4908964028
def kernelRow0LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow0LLRLLL i else kernelRow0LLRLLR i
def kernelRow0LLRLRL (i : ℕ) : ℕ := if i < 21 then 4280772014 else 4122434641
def kernelRow0LLRLRR (i : ℕ) : ℕ := if i < 23 then 3517282627 else 3715300378
def kernelRow0LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow0LLRLRL i else kernelRow0LLRLRR i
def kernelRow0LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow0LLRLL i else kernelRow0LLRLR i
def kernelRow0LLRRLL (i : ℕ) : ℕ := if i < 25 then 3827319721 else 3687591123
def kernelRow0LLRRLR (i : ℕ) : ℕ := if i < 27 then 3660801632 else 3804014839
def kernelRow0LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow0LLRRLL i else kernelRow0LLRRLR i
def kernelRow0LLRRRL (i : ℕ) : ℕ := if i < 29 then 4520538308 else 4212689218
def kernelRow0LLRRRR (i : ℕ) : ℕ := if i < 31 then 5404187492 else 5566599031
def kernelRow0LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow0LLRRRL i else kernelRow0LLRRRR i
def kernelRow0LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow0LLRRL i else kernelRow0LLRRR i
def kernelRow0LLR (i : ℕ) : ℕ := if i < 24 then kernelRow0LLRL i else kernelRow0LLRR i
def kernelRow0LL (i : ℕ) : ℕ := if i < 16 then kernelRow0LLL i else kernelRow0LLR i
def kernelRow0LRLLLL (i : ℕ) : ℕ := if i < 33 then 7093299360 else 6956083638
def kernelRow0LRLLLR (i : ℕ) : ℕ := if i < 35 then 7300110453 else 7349715322
def kernelRow0LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow0LRLLLL i else kernelRow0LRLLLR i
def kernelRow0LRLLRL (i : ℕ) : ℕ := if i < 37 then 7847752247 else 7440254016
def kernelRow0LRLLRR (i : ℕ) : ℕ := if i < 39 then 7273749009 else 7861500229
def kernelRow0LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow0LRLLRL i else kernelRow0LRLLRR i
def kernelRow0LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow0LRLLL i else kernelRow0LRLLR i
def kernelRow0LRLRLL (i : ℕ) : ℕ := if i < 41 then 8296171988 else 7858144782
def kernelRow0LRLRLR (i : ℕ) : ℕ := if i < 43 then 9064942585 else 9190462594
def kernelRow0LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow0LRLRLL i else kernelRow0LRLRLR i
def kernelRow0LRLRRL (i : ℕ) : ℕ := if i < 45 then 10714109779 else 10098790295
def kernelRow0LRLRRR (i : ℕ) : ℕ := if i < 47 then 10586837430 else 10821286167
def kernelRow0LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow0LRLRRL i else kernelRow0LRLRRR i
def kernelRow0LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow0LRLRL i else kernelRow0LRLRR i
def kernelRow0LRL (i : ℕ) : ℕ := if i < 40 then kernelRow0LRLL i else kernelRow0LRLR i
def kernelRow0LRRLLL (i : ℕ) : ℕ := if i < 49 then 11405381501 else 11203183157
def kernelRow0LRRLLR (i : ℕ) : ℕ := if i < 51 then 11304081444 else 11789585071
def kernelRow0LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow0LRRLLL i else kernelRow0LRRLLR i
def kernelRow0LRRLRL (i : ℕ) : ℕ := if i < 53 then 14175250935 else 13773040979
def kernelRow0LRRLRR (i : ℕ) : ℕ := if i < 55 then 14327610188 else 15115265827
def kernelRow0LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow0LRRLRL i else kernelRow0LRRLRR i
def kernelRow0LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow0LRRLL i else kernelRow0LRRLR i
def kernelRow0LRRRLL (i : ℕ) : ℕ := if i < 57 then 17791489387 else 18008709837
def kernelRow0LRRRLR (i : ℕ) : ℕ := if i < 59 then 20316871393 else 20924925057
def kernelRow0LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow0LRRRLL i else kernelRow0LRRRLR i
def kernelRow0LRRRRL (i : ℕ) : ℕ := if i < 61 then 20010577143 else 19122744352
def kernelRow0LRRRRR (i : ℕ) : ℕ := if i < 63 then 17841042225 else 18161524539
def kernelRow0LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow0LRRRRL i else kernelRow0LRRRRR i
def kernelRow0LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow0LRRRL i else kernelRow0LRRRR i
def kernelRow0LRR (i : ℕ) : ℕ := if i < 56 then kernelRow0LRRL i else kernelRow0LRRR i
def kernelRow0LR (i : ℕ) : ℕ := if i < 48 then kernelRow0LRL i else kernelRow0LRR i
def kernelRow0L (i : ℕ) : ℕ := if i < 32 then kernelRow0LL i else kernelRow0LR i
def kernelRow0RLLLLL (i : ℕ) : ℕ := if i < 65 then 18161524539 else 17841042225
def kernelRow0RLLLLR (i : ℕ) : ℕ := if i < 67 then 19122744352 else 20010577143
def kernelRow0RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow0RLLLLL i else kernelRow0RLLLLR i
def kernelRow0RLLLRL (i : ℕ) : ℕ := if i < 69 then 20924925057 else 20316871393
def kernelRow0RLLLRR (i : ℕ) : ℕ := if i < 71 then 18008709837 else 17791489387
def kernelRow0RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow0RLLLRL i else kernelRow0RLLLRR i
def kernelRow0RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow0RLLLL i else kernelRow0RLLLR i
def kernelRow0RLLRLL (i : ℕ) : ℕ := if i < 73 then 15115265827 else 14327610188
def kernelRow0RLLRLR (i : ℕ) : ℕ := if i < 75 then 13773040979 else 14175250935
def kernelRow0RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow0RLLRLL i else kernelRow0RLLRLR i
def kernelRow0RLLRRL (i : ℕ) : ℕ := if i < 77 then 11789585071 else 11304081444
def kernelRow0RLLRRR (i : ℕ) : ℕ := if i < 79 then 11203183157 else 11405381501
def kernelRow0RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow0RLLRRL i else kernelRow0RLLRRR i
def kernelRow0RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow0RLLRL i else kernelRow0RLLRR i
def kernelRow0RLL (i : ℕ) : ℕ := if i < 72 then kernelRow0RLLL i else kernelRow0RLLR i
def kernelRow0RLRLLL (i : ℕ) : ℕ := if i < 81 then 10821286167 else 10586837430
def kernelRow0RLRLLR (i : ℕ) : ℕ := if i < 83 then 10098790295 else 10714109779
def kernelRow0RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow0RLRLLL i else kernelRow0RLRLLR i
def kernelRow0RLRLRL (i : ℕ) : ℕ := if i < 85 then 9190462594 else 9064942585
def kernelRow0RLRLRR (i : ℕ) : ℕ := if i < 87 then 7858144782 else 8296171988
def kernelRow0RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow0RLRLRL i else kernelRow0RLRLRR i
def kernelRow0RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow0RLRLL i else kernelRow0RLRLR i
def kernelRow0RLRRLL (i : ℕ) : ℕ := if i < 89 then 7861500229 else 7273749009
def kernelRow0RLRRLR (i : ℕ) : ℕ := if i < 91 then 7440254016 else 7847752247
def kernelRow0RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow0RLRRLL i else kernelRow0RLRRLR i
def kernelRow0RLRRRL (i : ℕ) : ℕ := if i < 93 then 7349715322 else 7300110453
def kernelRow0RLRRRR (i : ℕ) : ℕ := if i < 95 then 6956083638 else 7093299360
def kernelRow0RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow0RLRRRL i else kernelRow0RLRRRR i
def kernelRow0RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow0RLRRL i else kernelRow0RLRRR i
def kernelRow0RLR (i : ℕ) : ℕ := if i < 88 then kernelRow0RLRL i else kernelRow0RLRR i
def kernelRow0RL (i : ℕ) : ℕ := if i < 80 then kernelRow0RLL i else kernelRow0RLR i
def kernelRow0RRLLLL (i : ℕ) : ℕ := if i < 97 then 5566599031 else 5404187492
def kernelRow0RRLLLR (i : ℕ) : ℕ := if i < 99 then 4212689218 else 4520538308
def kernelRow0RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow0RRLLLL i else kernelRow0RRLLLR i
def kernelRow0RRLLRL (i : ℕ) : ℕ := if i < 101 then 3804014839 else 3660801632
def kernelRow0RRLLRR (i : ℕ) : ℕ := if i < 103 then 3687591123 else 3827319721
def kernelRow0RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow0RRLLRL i else kernelRow0RRLLRR i
def kernelRow0RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow0RRLLL i else kernelRow0RRLLR i
def kernelRow0RRLRLL (i : ℕ) : ℕ := if i < 105 then 3715300378 else 3517282627
def kernelRow0RRLRLR (i : ℕ) : ℕ := if i < 107 then 4122434641 else 4280772014
def kernelRow0RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow0RRLRLL i else kernelRow0RRLRLR i
def kernelRow0RRLRRL (i : ℕ) : ℕ := if i < 109 then 4908964028 else 4738031554
def kernelRow0RRLRRR (i : ℕ) : ℕ := if i < 111 then 3422299798 else 3361765321
def kernelRow0RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow0RRLRRL i else kernelRow0RRLRRR i
def kernelRow0RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow0RRLRL i else kernelRow0RRLRR i
def kernelRow0RRL (i : ℕ) : ℕ := if i < 104 then kernelRow0RRLL i else kernelRow0RRLR i
def kernelRow0RRRLLL (i : ℕ) : ℕ := if i < 113 then 4356846463 else 4114616174
def kernelRow0RRRLLR (i : ℕ) : ℕ := if i < 115 then 2867040651 else 2685484155
def kernelRow0RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow0RRRLLL i else kernelRow0RRRLLR i
def kernelRow0RRRLRL (i : ℕ) : ℕ := if i < 117 then 4136945299 else 3979393375
def kernelRow0RRRLRR (i : ℕ) : ℕ := if i < 119 then 3628506270 else 3667606505
def kernelRow0RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow0RRRLRL i else kernelRow0RRRLRR i
def kernelRow0RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow0RRRLL i else kernelRow0RRRLR i
def kernelRow0RRRRLL (i : ℕ) : ℕ := if i < 121 then 2520256063 else 2537899164
def kernelRow0RRRRLR (i : ℕ) : ℕ := if i < 123 then 1658228109 else 1691464608
def kernelRow0RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow0RRRRLL i else kernelRow0RRRRLR i
def kernelRow0RRRRRL (i : ℕ) : ℕ := if i < 125 then 944113919 else 958096528
def kernelRow0RRRRRR (i : ℕ) : ℕ := if i < 127 then 1264471874 else 1213946189
def kernelRow0RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow0RRRRRL i else kernelRow0RRRRRR i
def kernelRow0RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow0RRRRL i else kernelRow0RRRRR i
def kernelRow0RRR (i : ℕ) : ℕ := if i < 120 then kernelRow0RRRL i else kernelRow0RRRR i
def kernelRow0RR (i : ℕ) : ℕ := if i < 112 then kernelRow0RRL i else kernelRow0RRR i
def kernelRow0R (i : ℕ) : ℕ := if i < 96 then kernelRow0RL i else kernelRow0RR i
def kernelRow0 (i : ℕ) : ℕ := if i < 64 then kernelRow0L i else kernelRow0R i
def kernelRow1LLLLLL (i : ℕ) : ℕ := if i < 1 then 4054327818 else 3910475081
def kernelRow1LLLLLR (i : ℕ) : ℕ := if i < 3 then 9195395534 else 9324827876
def kernelRow1LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow1LLLLLL i else kernelRow1LLLLLR i
def kernelRow1LLLLRL (i : ℕ) : ℕ := if i < 5 then 10357972635 else 9932570276
def kernelRow1LLLLRR (i : ℕ) : ℕ := if i < 7 then 12977369683 else 13195319136
def kernelRow1LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow1LLLLRL i else kernelRow1LLLLRR i
def kernelRow1LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow1LLLLL i else kernelRow1LLLLR i
def kernelRow1LLLRLL (i : ℕ) : ℕ := if i < 9 then 6146601105 else 6088878450
def kernelRow1LLLRLR (i : ℕ) : ℕ := if i < 11 then 9863176390 else 10403914439
def kernelRow1LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow1LLLRLL i else kernelRow1LLLRLR i
def kernelRow1LLLRRL (i : ℕ) : ℕ := if i < 13 then 7911175189 else 6909943164
def kernelRow1LLLRRR (i : ℕ) : ℕ := if i < 15 then 4740203902 else 5113563432
def kernelRow1LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow1LLLRRL i else kernelRow1LLLRRR i
def kernelRow1LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow1LLLRL i else kernelRow1LLLRR i
def kernelRow1LLL (i : ℕ) : ℕ := if i < 8 then kernelRow1LLLL i else kernelRow1LLLR i
def kernelRow1LLRLLL (i : ℕ) : ℕ := if i < 17 then 7397185681 else 7057041426
def kernelRow1LLRLLR (i : ℕ) : ℕ := if i < 19 then 7923071897 else 8030890400
def kernelRow1LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow1LLRLLL i else kernelRow1LLRLLR i
def kernelRow1LLRLRL (i : ℕ) : ℕ := if i < 21 then 5963986776 else 5644746368
def kernelRow1LLRLRR (i : ℕ) : ℕ := if i < 23 then 5184373373 else 5206788967
def kernelRow1LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow1LLRLRL i else kernelRow1LLRLRR i
def kernelRow1LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow1LLRLL i else kernelRow1LLRLR i
def kernelRow1LLRRLL (i : ℕ) : ℕ := if i < 25 then 7562616872 else 7220634562
def kernelRow1LLRRLR (i : ℕ) : ℕ := if i < 27 then 9527405310 else 8554671740
def kernelRow1LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow1LLRRLL i else kernelRow1LLRRLR i
def kernelRow1LLRRRL (i : ℕ) : ℕ := if i < 29 then 10589827446 else 11375412561
def kernelRow1LLRRRR (i : ℕ) : ℕ := if i < 31 then 10713798509 else 9643124078
def kernelRow1LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow1LLRRRL i else kernelRow1LLRRRR i
def kernelRow1LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow1LLRRL i else kernelRow1LLRRR i
def kernelRow1LLR (i : ℕ) : ℕ := if i < 24 then kernelRow1LLRL i else kernelRow1LLRR i
def kernelRow1LL (i : ℕ) : ℕ := if i < 16 then kernelRow1LLL i else kernelRow1LLR i
def kernelRow1LRLLLL (i : ℕ) : ℕ := if i < 33 then 10214022245 else 10281399024
def kernelRow1LRLLLR (i : ℕ) : ℕ := if i < 35 then 9535281481 else 9595880394
def kernelRow1LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow1LRLLLL i else kernelRow1LRLLLR i
def kernelRow1LRLLRL (i : ℕ) : ℕ := if i < 37 then 7025249227 else 7588064882
def kernelRow1LRLLRR (i : ℕ) : ℕ := if i < 39 then 5592466746 else 5346870060
def kernelRow1LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow1LRLLRL i else kernelRow1LRLLRR i
def kernelRow1LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow1LRLLL i else kernelRow1LRLLR i
def kernelRow1LRLRLL (i : ℕ) : ℕ := if i < 41 then 7540100389 else 7626830507
def kernelRow1LRLRLR (i : ℕ) : ℕ := if i < 43 then 7730955997 else 7746660828
def kernelRow1LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow1LRLRLL i else kernelRow1LRLRLR i
def kernelRow1LRLRRL (i : ℕ) : ℕ := if i < 45 then 5732307006 else 5717204358
def kernelRow1LRLRRR (i : ℕ) : ℕ := if i < 47 then 5200637670 else 5349081018
def kernelRow1LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow1LRLRRL i else kernelRow1LRLRRR i
def kernelRow1LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow1LRLRL i else kernelRow1LRLRR i
def kernelRow1LRL (i : ℕ) : ℕ := if i < 40 then kernelRow1LRLL i else kernelRow1LRLR i
def kernelRow1LRRLLL (i : ℕ) : ℕ := if i < 49 then 6566692965 else 6881599295
def kernelRow1LRRLLR (i : ℕ) : ℕ := if i < 51 then 4072607685 else 4407916941
def kernelRow1LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow1LRRLLL i else kernelRow1LRRLLR i
def kernelRow1LRRLRL (i : ℕ) : ℕ := if i < 53 then 9503622675 else 9992632869
def kernelRow1LRRLRR (i : ℕ) : ℕ := if i < 55 then 9755806586 else 9229672920
def kernelRow1LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow1LRRLRL i else kernelRow1LRRLRR i
def kernelRow1LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow1LRRLL i else kernelRow1LRRLR i
def kernelRow1LRRRLL (i : ℕ) : ℕ := if i < 57 then 6647226630 else 6839748762
def kernelRow1LRRRLR (i : ℕ) : ℕ := if i < 59 then 8990400669 else 8756853780
def kernelRow1LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow1LRRRLL i else kernelRow1LRRRLR i
def kernelRow1LRRRRL (i : ℕ) : ℕ := if i < 61 then 6513143607 else 6353722015
def kernelRow1LRRRRR (i : ℕ) : ℕ := if i < 63 then 10375858948 else 9568191745
def kernelRow1LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow1LRRRRL i else kernelRow1LRRRRR i
def kernelRow1LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow1LRRRL i else kernelRow1LRRRR i
def kernelRow1LRR (i : ℕ) : ℕ := if i < 56 then kernelRow1LRRL i else kernelRow1LRRR i
def kernelRow1LR (i : ℕ) : ℕ := if i < 48 then kernelRow1LRL i else kernelRow1LRR i
def kernelRow1L (i : ℕ) : ℕ := if i < 32 then kernelRow1LL i else kernelRow1LR i
def kernelRow1RLLLLL (i : ℕ) : ℕ := if i < 65 then 9568191745 else 10375858948
def kernelRow1RLLLLR (i : ℕ) : ℕ := if i < 67 then 6353722015 else 6513143607
def kernelRow1RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow1RLLLLL i else kernelRow1RLLLLR i
def kernelRow1RLLLRL (i : ℕ) : ℕ := if i < 69 then 8756853780 else 8990400669
def kernelRow1RLLLRR (i : ℕ) : ℕ := if i < 71 then 6839748762 else 6647226630
def kernelRow1RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow1RLLLRL i else kernelRow1RLLLRR i
def kernelRow1RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow1RLLLL i else kernelRow1RLLLR i
def kernelRow1RLLRLL (i : ℕ) : ℕ := if i < 73 then 9229672920 else 9755806586
def kernelRow1RLLRLR (i : ℕ) : ℕ := if i < 75 then 9992632869 else 9503622675
def kernelRow1RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow1RLLRLL i else kernelRow1RLLRLR i
def kernelRow1RLLRRL (i : ℕ) : ℕ := if i < 77 then 4407916941 else 4072607685
def kernelRow1RLLRRR (i : ℕ) : ℕ := if i < 79 then 6881599295 else 6566692965
def kernelRow1RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow1RLLRRL i else kernelRow1RLLRRR i
def kernelRow1RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow1RLLRL i else kernelRow1RLLRR i
def kernelRow1RLL (i : ℕ) : ℕ := if i < 72 then kernelRow1RLLL i else kernelRow1RLLR i
def kernelRow1RLRLLL (i : ℕ) : ℕ := if i < 81 then 5349081018 else 5200637670
def kernelRow1RLRLLR (i : ℕ) : ℕ := if i < 83 then 5717204358 else 5732307006
def kernelRow1RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow1RLRLLL i else kernelRow1RLRLLR i
def kernelRow1RLRLRL (i : ℕ) : ℕ := if i < 85 then 7746660828 else 7730955997
def kernelRow1RLRLRR (i : ℕ) : ℕ := if i < 87 then 7626830507 else 7540100389
def kernelRow1RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow1RLRLRL i else kernelRow1RLRLRR i
def kernelRow1RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow1RLRLL i else kernelRow1RLRLR i
def kernelRow1RLRRLL (i : ℕ) : ℕ := if i < 89 then 5346870060 else 5592466746
def kernelRow1RLRRLR (i : ℕ) : ℕ := if i < 91 then 7588064882 else 7025249227
def kernelRow1RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow1RLRRLL i else kernelRow1RLRRLR i
def kernelRow1RLRRRL (i : ℕ) : ℕ := if i < 93 then 9595880394 else 9535281481
def kernelRow1RLRRRR (i : ℕ) : ℕ := if i < 95 then 10281399024 else 10214022245
def kernelRow1RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow1RLRRRL i else kernelRow1RLRRRR i
def kernelRow1RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow1RLRRL i else kernelRow1RLRRR i
def kernelRow1RLR (i : ℕ) : ℕ := if i < 88 then kernelRow1RLRL i else kernelRow1RLRR i
def kernelRow1RL (i : ℕ) : ℕ := if i < 80 then kernelRow1RLL i else kernelRow1RLR i
def kernelRow1RRLLLL (i : ℕ) : ℕ := if i < 97 then 9643124078 else 10713798509
def kernelRow1RRLLLR (i : ℕ) : ℕ := if i < 99 then 11375412561 else 10589827446
def kernelRow1RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow1RRLLLL i else kernelRow1RRLLLR i
def kernelRow1RRLLRL (i : ℕ) : ℕ := if i < 101 then 8554671740 else 9527405310
def kernelRow1RRLLRR (i : ℕ) : ℕ := if i < 103 then 7220634562 else 7562616872
def kernelRow1RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow1RRLLRL i else kernelRow1RRLLRR i
def kernelRow1RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow1RRLLL i else kernelRow1RRLLR i
def kernelRow1RRLRLL (i : ℕ) : ℕ := if i < 105 then 5206788967 else 5184373373
def kernelRow1RRLRLR (i : ℕ) : ℕ := if i < 107 then 5644746368 else 5963986776
def kernelRow1RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow1RRLRLL i else kernelRow1RRLRLR i
def kernelRow1RRLRRL (i : ℕ) : ℕ := if i < 109 then 8030890400 else 7923071897
def kernelRow1RRLRRR (i : ℕ) : ℕ := if i < 111 then 7057041426 else 7397185681
def kernelRow1RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow1RRLRRL i else kernelRow1RRLRRR i
def kernelRow1RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow1RRLRL i else kernelRow1RRLRR i
def kernelRow1RRL (i : ℕ) : ℕ := if i < 104 then kernelRow1RRLL i else kernelRow1RRLR i
def kernelRow1RRRLLL (i : ℕ) : ℕ := if i < 113 then 5113563432 else 4740203902
def kernelRow1RRRLLR (i : ℕ) : ℕ := if i < 115 then 6909943164 else 7911175189
def kernelRow1RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow1RRRLLL i else kernelRow1RRRLLR i
def kernelRow1RRRLRL (i : ℕ) : ℕ := if i < 117 then 10403914439 else 9863176390
def kernelRow1RRRLRR (i : ℕ) : ℕ := if i < 119 then 6088878450 else 6146601105
def kernelRow1RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow1RRRLRL i else kernelRow1RRRLRR i
def kernelRow1RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow1RRRLL i else kernelRow1RRRLR i
def kernelRow1RRRRLL (i : ℕ) : ℕ := if i < 121 then 13195319136 else 12977369683
def kernelRow1RRRRLR (i : ℕ) : ℕ := if i < 123 then 9932570276 else 10357972635
def kernelRow1RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow1RRRRLL i else kernelRow1RRRRLR i
def kernelRow1RRRRRL (i : ℕ) : ℕ := if i < 125 then 9324827876 else 9195395534
def kernelRow1RRRRRR (i : ℕ) : ℕ := if i < 127 then 3910475081 else 4054327818
def kernelRow1RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow1RRRRRL i else kernelRow1RRRRRR i
def kernelRow1RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow1RRRRL i else kernelRow1RRRRR i
def kernelRow1RRR (i : ℕ) : ℕ := if i < 120 then kernelRow1RRRL i else kernelRow1RRRR i
def kernelRow1RR (i : ℕ) : ℕ := if i < 112 then kernelRow1RRL i else kernelRow1RRR i
def kernelRow1R (i : ℕ) : ℕ := if i < 96 then kernelRow1RL i else kernelRow1RR i
def kernelRow1 (i : ℕ) : ℕ := if i < 64 then kernelRow1L i else kernelRow1R i
def kernelRow2LLLLLL (i : ℕ) : ℕ := if i < 1 then 1573702116 else 1594328772
def kernelRow2LLLLLR (i : ℕ) : ℕ := if i < 3 then 2147952778 else 2196683400
def kernelRow2LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow2LLLLLL i else kernelRow2LLLLLR i
def kernelRow2LLLLRL (i : ℕ) : ℕ := if i < 5 then 5872632731 else 5573536725
def kernelRow2LLLLRR (i : ℕ) : ℕ := if i < 7 then 6304759188 else 6178177291
def kernelRow2LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow2LLLLRL i else kernelRow2LLLLRR i
def kernelRow2LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow2LLLLL i else kernelRow2LLLLR i
def kernelRow2LLLRLL (i : ℕ) : ℕ := if i < 9 then 2123364736 else 2127531967
def kernelRow2LLLRLR (i : ℕ) : ℕ := if i < 11 then 3451373953 else 3387514914
def kernelRow2LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow2LLLRLL i else kernelRow2LLLRLR i
def kernelRow2LLLRRL (i : ℕ) : ℕ := if i < 13 then 8978922441 else 8955675944
def kernelRow2LLLRRR (i : ℕ) : ℕ := if i < 15 then 6669998900 else 6961050764
def kernelRow2LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow2LLLRRL i else kernelRow2LLLRRR i
def kernelRow2LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow2LLLRL i else kernelRow2LLLRR i
def kernelRow2LLL (i : ℕ) : ℕ := if i < 8 then kernelRow2LLLL i else kernelRow2LLLR i
def kernelRow2LLRLLL (i : ℕ) : ℕ := if i < 17 then 11288345256 else 11496766337
def kernelRow2LLRLLR (i : ℕ) : ℕ := if i < 19 then 5204232613 else 5241878607
def kernelRow2LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow2LLRLLL i else kernelRow2LLRLLR i
def kernelRow2LLRLRL (i : ℕ) : ℕ := if i < 21 then 9388853421 else 9796059550
def kernelRow2LLRLRR (i : ℕ) : ℕ := if i < 23 then 6624235554 else 6518873027
def kernelRow2LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow2LLRLRL i else kernelRow2LLRLRR i
def kernelRow2LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow2LLRLL i else kernelRow2LLRLR i
def kernelRow2LLRRLL (i : ℕ) : ℕ := if i < 25 then 10802977847 else 10959386357
def kernelRow2LLRRLR (i : ℕ) : ℕ := if i < 27 then 7154269126 else 6847292497
def kernelRow2LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow2LLRRLL i else kernelRow2LLRRLR i
def kernelRow2LLRRRL (i : ℕ) : ℕ := if i < 29 then 7539984476 else 7853096918
def kernelRow2LLRRRR (i : ℕ) : ℕ := if i < 31 then 4907510138 else 5097115120
def kernelRow2LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow2LLRRRL i else kernelRow2LLRRRR i
def kernelRow2LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow2LLRRL i else kernelRow2LLRRR i
def kernelRow2LLR (i : ℕ) : ℕ := if i < 24 then kernelRow2LLRL i else kernelRow2LLRR i
def kernelRow2LL (i : ℕ) : ℕ := if i < 16 then kernelRow2LLL i else kernelRow2LLR i
def kernelRow2LRLLLL (i : ℕ) : ℕ := if i < 33 then 13930766084 else 13642534570
def kernelRow2LRLLLR (i : ℕ) : ℕ := if i < 35 then 10574259919 else 10990414706
def kernelRow2LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow2LRLLLL i else kernelRow2LRLLLR i
def kernelRow2LRLLRL (i : ℕ) : ℕ := if i < 37 then 15090397682 else 15004391696
def kernelRow2LRLLRR (i : ℕ) : ℕ := if i < 39 then 16180626980 else 16815072664
def kernelRow2LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow2LRLLRL i else kernelRow2LRLLRR i
def kernelRow2LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow2LRLLL i else kernelRow2LRLLR i
def kernelRow2LRLRLL (i : ℕ) : ℕ := if i < 41 then 12673427498 else 12833927431
def kernelRow2LRLRLR (i : ℕ) : ℕ := if i < 43 then 9400527993 else 9496885736
def kernelRow2LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow2LRLRLL i else kernelRow2LRLRLR i
def kernelRow2LRLRRL (i : ℕ) : ℕ := if i < 45 then 9682790711 else 9570213201
def kernelRow2LRLRRR (i : ℕ) : ℕ := if i < 47 then 9120384455 else 9394868980
def kernelRow2LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow2LRLRRL i else kernelRow2LRLRRR i
def kernelRow2LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow2LRLRL i else kernelRow2LRLRR i
def kernelRow2LRL (i : ℕ) : ℕ := if i < 40 then kernelRow2LRLL i else kernelRow2LRLR i
def kernelRow2LRRLLL (i : ℕ) : ℕ := if i < 49 then 12108505367 else 11485670682
def kernelRow2LRRLLR (i : ℕ) : ℕ := if i < 51 then 5106144732 else 5725058398
def kernelRow2LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow2LRRLLL i else kernelRow2LRRLLR i
def kernelRow2LRRLRL (i : ℕ) : ℕ := if i < 53 then 6086480823 else 5871199324
def kernelRow2LRRLRR (i : ℕ) : ℕ := if i < 55 then 6768126813 else 7227455033
def kernelRow2LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow2LRRLRL i else kernelRow2LRRLRR i
def kernelRow2LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow2LRRLL i else kernelRow2LRRLR i
def kernelRow2LRRRLL (i : ℕ) : ℕ := if i < 57 then 5648988921 else 5718868145
def kernelRow2LRRRLR (i : ℕ) : ℕ := if i < 59 then 6187923301 else 6231283759
def kernelRow2LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow2LRRRLL i else kernelRow2LRRRLR i
def kernelRow2LRRRRL (i : ℕ) : ℕ := if i < 61 then 5622871781 else 5534723129
def kernelRow2LRRRRR (i : ℕ) : ℕ := if i < 63 then 4654545529 else 4802580493
def kernelRow2LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow2LRRRRL i else kernelRow2LRRRRR i
def kernelRow2LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow2LRRRL i else kernelRow2LRRRR i
def kernelRow2LRR (i : ℕ) : ℕ := if i < 56 then kernelRow2LRRL i else kernelRow2LRRR i
def kernelRow2LR (i : ℕ) : ℕ := if i < 48 then kernelRow2LRL i else kernelRow2LRR i
def kernelRow2L (i : ℕ) : ℕ := if i < 32 then kernelRow2LL i else kernelRow2LR i
def kernelRow2RLLLLL (i : ℕ) : ℕ := if i < 65 then 4802580493 else 4654545529
def kernelRow2RLLLLR (i : ℕ) : ℕ := if i < 67 then 5534723129 else 5622871781
def kernelRow2RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow2RLLLLL i else kernelRow2RLLLLR i
def kernelRow2RLLLRL (i : ℕ) : ℕ := if i < 69 then 6231283759 else 6187923301
def kernelRow2RLLLRR (i : ℕ) : ℕ := if i < 71 then 5718868145 else 5648988921
def kernelRow2RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow2RLLLRL i else kernelRow2RLLLRR i
def kernelRow2RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow2RLLLL i else kernelRow2RLLLR i
def kernelRow2RLLRLL (i : ℕ) : ℕ := if i < 73 then 7227455033 else 6768126813
def kernelRow2RLLRLR (i : ℕ) : ℕ := if i < 75 then 5871199324 else 6086480823
def kernelRow2RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow2RLLRLL i else kernelRow2RLLRLR i
def kernelRow2RLLRRL (i : ℕ) : ℕ := if i < 77 then 5725058398 else 5106144732
def kernelRow2RLLRRR (i : ℕ) : ℕ := if i < 79 then 11485670682 else 12108505367
def kernelRow2RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow2RLLRRL i else kernelRow2RLLRRR i
def kernelRow2RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow2RLLRL i else kernelRow2RLLRR i
def kernelRow2RLL (i : ℕ) : ℕ := if i < 72 then kernelRow2RLLL i else kernelRow2RLLR i
def kernelRow2RLRLLL (i : ℕ) : ℕ := if i < 81 then 9394868980 else 9120384455
def kernelRow2RLRLLR (i : ℕ) : ℕ := if i < 83 then 9570213201 else 9682790711
def kernelRow2RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow2RLRLLL i else kernelRow2RLRLLR i
def kernelRow2RLRLRL (i : ℕ) : ℕ := if i < 85 then 9496885736 else 9400527993
def kernelRow2RLRLRR (i : ℕ) : ℕ := if i < 87 then 12833927431 else 12673427498
def kernelRow2RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow2RLRLRL i else kernelRow2RLRLRR i
def kernelRow2RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow2RLRLL i else kernelRow2RLRLR i
def kernelRow2RLRRLL (i : ℕ) : ℕ := if i < 89 then 16815072664 else 16180626980
def kernelRow2RLRRLR (i : ℕ) : ℕ := if i < 91 then 15004391696 else 15090397682
def kernelRow2RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow2RLRRLL i else kernelRow2RLRRLR i
def kernelRow2RLRRRL (i : ℕ) : ℕ := if i < 93 then 10990414706 else 10574259919
def kernelRow2RLRRRR (i : ℕ) : ℕ := if i < 95 then 13642534570 else 13930766084
def kernelRow2RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow2RLRRRL i else kernelRow2RLRRRR i
def kernelRow2RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow2RLRRL i else kernelRow2RLRRR i
def kernelRow2RLR (i : ℕ) : ℕ := if i < 88 then kernelRow2RLRL i else kernelRow2RLRR i
def kernelRow2RL (i : ℕ) : ℕ := if i < 80 then kernelRow2RLL i else kernelRow2RLR i
def kernelRow2RRLLLL (i : ℕ) : ℕ := if i < 97 then 5097115120 else 4907510138
def kernelRow2RRLLLR (i : ℕ) : ℕ := if i < 99 then 7853096918 else 7539984476
def kernelRow2RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow2RRLLLL i else kernelRow2RRLLLR i
def kernelRow2RRLLRL (i : ℕ) : ℕ := if i < 101 then 6847292497 else 7154269126
def kernelRow2RRLLRR (i : ℕ) : ℕ := if i < 103 then 10959386357 else 10802977847
def kernelRow2RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow2RRLLRL i else kernelRow2RRLLRR i
def kernelRow2RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow2RRLLL i else kernelRow2RRLLR i
def kernelRow2RRLRLL (i : ℕ) : ℕ := if i < 105 then 6518873027 else 6624235554
def kernelRow2RRLRLR (i : ℕ) : ℕ := if i < 107 then 9796059550 else 9388853421
def kernelRow2RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow2RRLRLL i else kernelRow2RRLRLR i
def kernelRow2RRLRRL (i : ℕ) : ℕ := if i < 109 then 5241878607 else 5204232613
def kernelRow2RRLRRR (i : ℕ) : ℕ := if i < 111 then 11496766337 else 11288345256
def kernelRow2RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow2RRLRRL i else kernelRow2RRLRRR i
def kernelRow2RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow2RRLRL i else kernelRow2RRLRR i
def kernelRow2RRL (i : ℕ) : ℕ := if i < 104 then kernelRow2RRLL i else kernelRow2RRLR i
def kernelRow2RRRLLL (i : ℕ) : ℕ := if i < 113 then 6961050764 else 6669998900
def kernelRow2RRRLLR (i : ℕ) : ℕ := if i < 115 then 8955675944 else 8978922441
def kernelRow2RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow2RRRLLL i else kernelRow2RRRLLR i
def kernelRow2RRRLRL (i : ℕ) : ℕ := if i < 117 then 3387514914 else 3451373953
def kernelRow2RRRLRR (i : ℕ) : ℕ := if i < 119 then 2127531967 else 2123364736
def kernelRow2RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow2RRRLRL i else kernelRow2RRRLRR i
def kernelRow2RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow2RRRLL i else kernelRow2RRRLR i
def kernelRow2RRRRLL (i : ℕ) : ℕ := if i < 121 then 6178177291 else 6304759188
def kernelRow2RRRRLR (i : ℕ) : ℕ := if i < 123 then 5573536725 else 5872632731
def kernelRow2RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow2RRRRLL i else kernelRow2RRRRLR i
def kernelRow2RRRRRL (i : ℕ) : ℕ := if i < 125 then 2196683400 else 2147952778
def kernelRow2RRRRRR (i : ℕ) : ℕ := if i < 127 then 1594328772 else 1573702116
def kernelRow2RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow2RRRRRL i else kernelRow2RRRRRR i
def kernelRow2RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow2RRRRL i else kernelRow2RRRRR i
def kernelRow2RRR (i : ℕ) : ℕ := if i < 120 then kernelRow2RRRL i else kernelRow2RRRR i
def kernelRow2RR (i : ℕ) : ℕ := if i < 112 then kernelRow2RRL i else kernelRow2RRR i
def kernelRow2R (i : ℕ) : ℕ := if i < 96 then kernelRow2RL i else kernelRow2RR i
def kernelRow2 (i : ℕ) : ℕ := if i < 64 then kernelRow2L i else kernelRow2R i
def kernelRow3LLLLLL (i : ℕ) : ℕ := if i < 1 then 227067071 else 218955465
def kernelRow3LLLLLR (i : ℕ) : ℕ := if i < 3 then 322563287 else 320829881
def kernelRow3LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow3LLLLLL i else kernelRow3LLLLLR i
def kernelRow3LLLLRL (i : ℕ) : ℕ := if i < 5 then 708749414 else 747488571
def kernelRow3LLLLRR (i : ℕ) : ℕ := if i < 7 then 660810019 else 638546593
def kernelRow3LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow3LLLLRL i else kernelRow3LLLLRR i
def kernelRow3LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow3LLLLL i else kernelRow3LLLLR i
def kernelRow3LLLRLL (i : ℕ) : ℕ := if i < 9 then 1881942179 else 1957695065
def kernelRow3LLLRLR (i : ℕ) : ℕ := if i < 11 then 2753596429 else 2524764489
def kernelRow3LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow3LLLRLL i else kernelRow3LLLRLR i
def kernelRow3LLLRRL (i : ℕ) : ℕ := if i < 13 then 5345739345 else 5614813405
def kernelRow3LLLRRR (i : ℕ) : ℕ := if i < 15 then 6960127558 else 6789008295
def kernelRow3LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow3LLLRRL i else kernelRow3LLLRRR i
def kernelRow3LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow3LLLRL i else kernelRow3LLLRR i
def kernelRow3LLL (i : ℕ) : ℕ := if i < 8 then kernelRow3LLLL i else kernelRow3LLLR i
def kernelRow3LLRLLL (i : ℕ) : ℕ := if i < 17 then 8010204934 else 8081572309
def kernelRow3LLRLLR (i : ℕ) : ℕ := if i < 19 then 10200007968 else 9999977352
def kernelRow3LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow3LLRLLL i else kernelRow3LLRLLR i
def kernelRow3LLRLRL (i : ℕ) : ℕ := if i < 21 then 10451436366 else 10174129510
def kernelRow3LLRLRR (i : ℕ) : ℕ := if i < 23 then 13116654993 else 13175810672
def kernelRow3LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow3LLRLRL i else kernelRow3LLRLRR i
def kernelRow3LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow3LLRLL i else kernelRow3LLRLR i
def kernelRow3LLRRLL (i : ℕ) : ℕ := if i < 25 then 13868049755 else 13631399394
def kernelRow3LLRRLR (i : ℕ) : ℕ := if i < 27 then 13731839922 else 14022932027
def kernelRow3LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow3LLRRLL i else kernelRow3LLRRLR i
def kernelRow3LLRRRL (i : ℕ) : ℕ := if i < 29 then 13203703108 else 12895168784
def kernelRow3LLRRRR (i : ℕ) : ℕ := if i < 31 then 9213009047 else 9274892828
def kernelRow3LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow3LLRRRL i else kernelRow3LLRRRR i
def kernelRow3LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow3LLRRL i else kernelRow3LLRRR i
def kernelRow3LLR (i : ℕ) : ℕ := if i < 24 then kernelRow3LLRL i else kernelRow3LLRR i
def kernelRow3LL (i : ℕ) : ℕ := if i < 16 then kernelRow3LLL i else kernelRow3LLR i
def kernelRow3LRLLLL (i : ℕ) : ℕ := if i < 33 then 6324920612 else 6315838298
def kernelRow3LRLLLR (i : ℕ) : ℕ := if i < 35 then 8647961030 else 8680771893
def kernelRow3LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow3LRLLLL i else kernelRow3LRLLLR i
def kernelRow3LRLLRL (i : ℕ) : ℕ := if i < 37 then 8761541608 else 9026859754
def kernelRow3LRLLRR (i : ℕ) : ℕ := if i < 39 then 9175271325 else 9110893230
def kernelRow3LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow3LRLLRL i else kernelRow3LRLLRR i
def kernelRow3LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow3LRLLL i else kernelRow3LRLLR i
def kernelRow3LRLRLL (i : ℕ) : ℕ := if i < 41 then 7315214903 else 7328505293
def kernelRow3LRLRLR (i : ℕ) : ℕ := if i < 43 then 13229475003 else 12905131994
def kernelRow3LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow3LRLRLL i else kernelRow3LRLRLR i
def kernelRow3LRLRRL (i : ℕ) : ℕ := if i < 45 then 11790597128 else 12172441555
def kernelRow3LRLRRR (i : ℕ) : ℕ := if i < 47 then 7141129803 else 6353421301
def kernelRow3LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow3LRLRRL i else kernelRow3LRLRRR i
def kernelRow3LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow3LRLRL i else kernelRow3LRLRR i
def kernelRow3LRL (i : ℕ) : ℕ := if i < 40 then kernelRow3LRLL i else kernelRow3LRLR i
def kernelRow3LRRLLL (i : ℕ) : ℕ := if i < 49 then 6591737402 else 6746263270
def kernelRow3LRRLLR (i : ℕ) : ℕ := if i < 51 then 6829642540 else 6602913876
def kernelRow3LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow3LRRLLL i else kernelRow3LRRLLR i
def kernelRow3LRRLRL (i : ℕ) : ℕ := if i < 53 then 7135270787 else 7084199222
def kernelRow3LRRLRR (i : ℕ) : ℕ := if i < 55 then 9295016772 else 9472839304
def kernelRow3LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow3LRRLRL i else kernelRow3LRRLRR i
def kernelRow3LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow3LRRLL i else kernelRow3LRRLR i
def kernelRow3LRRRLL (i : ℕ) : ℕ := if i < 57 then 9478876166 else 9333183481
def kernelRow3LRRRLR (i : ℕ) : ℕ := if i < 59 then 8785925861 else 8508644302
def kernelRow3LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow3LRRRLL i else kernelRow3LRRRLR i
def kernelRow3LRRRRL (i : ℕ) : ℕ := if i < 61 then 10379304723 else 10408319131
def kernelRow3LRRRRR (i : ℕ) : ℕ := if i < 63 then 9190843644 else 9153558754
def kernelRow3LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow3LRRRRL i else kernelRow3LRRRRR i
def kernelRow3LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow3LRRRL i else kernelRow3LRRRR i
def kernelRow3LRR (i : ℕ) : ℕ := if i < 56 then kernelRow3LRRL i else kernelRow3LRRR i
def kernelRow3LR (i : ℕ) : ℕ := if i < 48 then kernelRow3LRL i else kernelRow3LRR i
def kernelRow3L (i : ℕ) : ℕ := if i < 32 then kernelRow3LL i else kernelRow3LR i
def kernelRow3RLLLLL (i : ℕ) : ℕ := if i < 65 then 9153558754 else 9190843644
def kernelRow3RLLLLR (i : ℕ) : ℕ := if i < 67 then 10408319131 else 10379304723
def kernelRow3RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow3RLLLLL i else kernelRow3RLLLLR i
def kernelRow3RLLLRL (i : ℕ) : ℕ := if i < 69 then 8508644302 else 8785925861
def kernelRow3RLLLRR (i : ℕ) : ℕ := if i < 71 then 9333183481 else 9478876166
def kernelRow3RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow3RLLLRL i else kernelRow3RLLLRR i
def kernelRow3RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow3RLLLL i else kernelRow3RLLLR i
def kernelRow3RLLRLL (i : ℕ) : ℕ := if i < 73 then 9472839304 else 9295016772
def kernelRow3RLLRLR (i : ℕ) : ℕ := if i < 75 then 7084199222 else 7135270787
def kernelRow3RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow3RLLRLL i else kernelRow3RLLRLR i
def kernelRow3RLLRRL (i : ℕ) : ℕ := if i < 77 then 6602913876 else 6829642540
def kernelRow3RLLRRR (i : ℕ) : ℕ := if i < 79 then 6746263270 else 6591737402
def kernelRow3RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow3RLLRRL i else kernelRow3RLLRRR i
def kernelRow3RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow3RLLRL i else kernelRow3RLLRR i
def kernelRow3RLL (i : ℕ) : ℕ := if i < 72 then kernelRow3RLLL i else kernelRow3RLLR i
def kernelRow3RLRLLL (i : ℕ) : ℕ := if i < 81 then 6353421301 else 7141129803
def kernelRow3RLRLLR (i : ℕ) : ℕ := if i < 83 then 12172441555 else 11790597128
def kernelRow3RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow3RLRLLL i else kernelRow3RLRLLR i
def kernelRow3RLRLRL (i : ℕ) : ℕ := if i < 85 then 12905131994 else 13229475003
def kernelRow3RLRLRR (i : ℕ) : ℕ := if i < 87 then 7328505293 else 7315214903
def kernelRow3RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow3RLRLRL i else kernelRow3RLRLRR i
def kernelRow3RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow3RLRLL i else kernelRow3RLRLR i
def kernelRow3RLRRLL (i : ℕ) : ℕ := if i < 89 then 9110893230 else 9175271325
def kernelRow3RLRRLR (i : ℕ) : ℕ := if i < 91 then 9026859754 else 8761541608
def kernelRow3RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow3RLRRLL i else kernelRow3RLRRLR i
def kernelRow3RLRRRL (i : ℕ) : ℕ := if i < 93 then 8680771893 else 8647961030
def kernelRow3RLRRRR (i : ℕ) : ℕ := if i < 95 then 6315838298 else 6324920612
def kernelRow3RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow3RLRRRL i else kernelRow3RLRRRR i
def kernelRow3RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow3RLRRL i else kernelRow3RLRRR i
def kernelRow3RLR (i : ℕ) : ℕ := if i < 88 then kernelRow3RLRL i else kernelRow3RLRR i
def kernelRow3RL (i : ℕ) : ℕ := if i < 80 then kernelRow3RLL i else kernelRow3RLR i
def kernelRow3RRLLLL (i : ℕ) : ℕ := if i < 97 then 9274892828 else 9213009047
def kernelRow3RRLLLR (i : ℕ) : ℕ := if i < 99 then 12895168784 else 13203703108
def kernelRow3RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow3RRLLLL i else kernelRow3RRLLLR i
def kernelRow3RRLLRL (i : ℕ) : ℕ := if i < 101 then 14022932027 else 13731839922
def kernelRow3RRLLRR (i : ℕ) : ℕ := if i < 103 then 13631399394 else 13868049755
def kernelRow3RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow3RRLLRL i else kernelRow3RRLLRR i
def kernelRow3RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow3RRLLL i else kernelRow3RRLLR i
def kernelRow3RRLRLL (i : ℕ) : ℕ := if i < 105 then 13175810672 else 13116654993
def kernelRow3RRLRLR (i : ℕ) : ℕ := if i < 107 then 10174129510 else 10451436366
def kernelRow3RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow3RRLRLL i else kernelRow3RRLRLR i
def kernelRow3RRLRRL (i : ℕ) : ℕ := if i < 109 then 9999977352 else 10200007968
def kernelRow3RRLRRR (i : ℕ) : ℕ := if i < 111 then 8081572309 else 8010204934
def kernelRow3RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow3RRLRRL i else kernelRow3RRLRRR i
def kernelRow3RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow3RRLRL i else kernelRow3RRLRR i
def kernelRow3RRL (i : ℕ) : ℕ := if i < 104 then kernelRow3RRLL i else kernelRow3RRLR i
def kernelRow3RRRLLL (i : ℕ) : ℕ := if i < 113 then 6789008295 else 6960127558
def kernelRow3RRRLLR (i : ℕ) : ℕ := if i < 115 then 5614813405 else 5345739345
def kernelRow3RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow3RRRLLL i else kernelRow3RRRLLR i
def kernelRow3RRRLRL (i : ℕ) : ℕ := if i < 117 then 2524764489 else 2753596429
def kernelRow3RRRLRR (i : ℕ) : ℕ := if i < 119 then 1957695065 else 1881942179
def kernelRow3RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow3RRRLRL i else kernelRow3RRRLRR i
def kernelRow3RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow3RRRLL i else kernelRow3RRRLR i
def kernelRow3RRRRLL (i : ℕ) : ℕ := if i < 121 then 638546593 else 660810019
def kernelRow3RRRRLR (i : ℕ) : ℕ := if i < 123 then 747488571 else 708749414
def kernelRow3RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow3RRRRLL i else kernelRow3RRRRLR i
def kernelRow3RRRRRL (i : ℕ) : ℕ := if i < 125 then 320829881 else 322563287
def kernelRow3RRRRRR (i : ℕ) : ℕ := if i < 127 then 218955465 else 227067071
def kernelRow3RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow3RRRRRL i else kernelRow3RRRRRR i
def kernelRow3RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow3RRRRL i else kernelRow3RRRRR i
def kernelRow3RRR (i : ℕ) : ℕ := if i < 120 then kernelRow3RRRL i else kernelRow3RRRR i
def kernelRow3RR (i : ℕ) : ℕ := if i < 112 then kernelRow3RRL i else kernelRow3RRR i
def kernelRow3R (i : ℕ) : ℕ := if i < 96 then kernelRow3RL i else kernelRow3RR i
def kernelRow3 (i : ℕ) : ℕ := if i < 64 then kernelRow3L i else kernelRow3R i
def kernelRow4LLLLLL (i : ℕ) : ℕ := if i < 1 then 2280844296 else 2040073091
def kernelRow4LLLLLR (i : ℕ) : ℕ := if i < 3 then 3666252552 else 4018562469
def kernelRow4LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow4LLLLLL i else kernelRow4LLLLLR i
def kernelRow4LLLLRL (i : ℕ) : ℕ := if i < 5 then 4131861125 else 3985983240
def kernelRow4LLLLRR (i : ℕ) : ℕ := if i < 7 then 5001301633 else 5505037673
def kernelRow4LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow4LLLLRL i else kernelRow4LLLLRR i
def kernelRow4LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow4LLLLL i else kernelRow4LLLLR i
def kernelRow4LLLRLL (i : ℕ) : ℕ := if i < 9 then 7576142179 else 6591217739
def kernelRow4LLLRLR (i : ℕ) : ℕ := if i < 11 then 8356160638 else 9236830607
def kernelRow4LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow4LLLRLL i else kernelRow4LLLRLR i
def kernelRow4LLLRRL (i : ℕ) : ℕ := if i < 13 then 13619835641 else 12291586341
def kernelRow4LLLRRR (i : ℕ) : ℕ := if i < 15 then 11179364931 else 12152367691
def kernelRow4LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow4LLLRRL i else kernelRow4LLLRRR i
def kernelRow4LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow4LLLRL i else kernelRow4LLLRR i
def kernelRow4LLL (i : ℕ) : ℕ := if i < 8 then kernelRow4LLLL i else kernelRow4LLLR i
def kernelRow4LLRLLL (i : ℕ) : ℕ := if i < 17 then 8543742260 else 7733658019
def kernelRow4LLRLLR (i : ℕ) : ℕ := if i < 19 then 10595389364 else 11755129401
def kernelRow4LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow4LLRLLL i else kernelRow4LLRLLR i
def kernelRow4LLRLRL (i : ℕ) : ℕ := if i < 21 then 10051870602 else 9419616782
def kernelRow4LLRLRR (i : ℕ) : ℕ := if i < 23 then 8762768153 else 9579456988
def kernelRow4LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow4LLRLRL i else kernelRow4LLRLRR i
def kernelRow4LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow4LLRLL i else kernelRow4LLRLR i
def kernelRow4LLRRLL (i : ℕ) : ℕ := if i < 25 then 6773241315 else 6620675964
def kernelRow4LLRRLR (i : ℕ) : ℕ := if i < 27 then 8047435185 else 8135137612
def kernelRow4LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow4LLRRLL i else kernelRow4LLRRLR i
def kernelRow4LLRRRL (i : ℕ) : ℕ := if i < 29 then 7143154798 else 6672154016
def kernelRow4LLRRRR (i : ℕ) : ℕ := if i < 31 then 5149077732 else 5596702111
def kernelRow4LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow4LLRRRL i else kernelRow4LLRRRR i
def kernelRow4LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow4LLRRL i else kernelRow4LLRRR i
def kernelRow4LLR (i : ℕ) : ℕ := if i < 24 then kernelRow4LLRL i else kernelRow4LLRR i
def kernelRow4LL (i : ℕ) : ℕ := if i < 16 then kernelRow4LLL i else kernelRow4LLR i
def kernelRow4LRLLLL (i : ℕ) : ℕ := if i < 33 then 5425721594 else 5468073553
def kernelRow4LRLLLR (i : ℕ) : ℕ := if i < 35 then 5065221278 else 5274946987
def kernelRow4LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow4LRLLLL i else kernelRow4LRLLLR i
def kernelRow4LRLLRL (i : ℕ) : ℕ := if i < 37 then 5658236327 else 5454732483
def kernelRow4LRLLRR (i : ℕ) : ℕ := if i < 39 then 7895216580 else 8299903919
def kernelRow4LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow4LRLLRL i else kernelRow4LRLLRR i
def kernelRow4LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow4LRLLL i else kernelRow4LRLLR i
def kernelRow4LRLRLL (i : ℕ) : ℕ := if i < 41 then 10902340216 else 10708066037
def kernelRow4LRLRLR (i : ℕ) : ℕ := if i < 43 then 12530957013 else 13018681635
def kernelRow4LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow4LRLRLL i else kernelRow4LRLRLR i
def kernelRow4LRLRRL (i : ℕ) : ℕ := if i < 45 then 13273717236 else 11716106515
def kernelRow4LRLRRR (i : ℕ) : ℕ := if i < 47 then 11344973002 else 12340613067
def kernelRow4LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow4LRLRRL i else kernelRow4LRLRRR i
def kernelRow4LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow4LRLRL i else kernelRow4LRLRR i
def kernelRow4LRL (i : ℕ) : ℕ := if i < 40 then kernelRow4LRLL i else kernelRow4LRLR i
def kernelRow4LRRLLL (i : ℕ) : ℕ := if i < 49 then 11011759340 else 10660272565
def kernelRow4LRRLLR (i : ℕ) : ℕ := if i < 51 then 6218654530 else 6525276126
def kernelRow4LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow4LRRLLL i else kernelRow4LRRLLR i
def kernelRow4LRRLRL (i : ℕ) : ℕ := if i < 53 then 6048533709 else 5625839255
def kernelRow4LRRLRR (i : ℕ) : ℕ := if i < 55 then 5730491976 else 5629367354
def kernelRow4LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow4LRRLRL i else kernelRow4LRRLRR i
def kernelRow4LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow4LRRLL i else kernelRow4LRRLR i
def kernelRow4LRRRLL (i : ℕ) : ℕ := if i < 57 then 6896857684 else 6278173124
def kernelRow4LRRRLR (i : ℕ) : ℕ := if i < 59 then 6729739915 else 6175547170
def kernelRow4LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow4LRRRLL i else kernelRow4LRRRLR i
def kernelRow4LRRRRL (i : ℕ) : ℕ := if i < 61 then 6746579206 else 7159927532
def kernelRow4LRRRRR (i : ℕ) : ℕ := if i < 63 then 7966295962 else 8006544962
def kernelRow4LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow4LRRRRL i else kernelRow4LRRRRR i
def kernelRow4LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow4LRRRL i else kernelRow4LRRRR i
def kernelRow4LRR (i : ℕ) : ℕ := if i < 56 then kernelRow4LRRL i else kernelRow4LRRR i
def kernelRow4LR (i : ℕ) : ℕ := if i < 48 then kernelRow4LRL i else kernelRow4LRR i
def kernelRow4L (i : ℕ) : ℕ := if i < 32 then kernelRow4LL i else kernelRow4LR i
def kernelRow4RLLLLL (i : ℕ) : ℕ := if i < 65 then 8006544962 else 7966295962
def kernelRow4RLLLLR (i : ℕ) : ℕ := if i < 67 then 7159927532 else 6746579206
def kernelRow4RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow4RLLLLL i else kernelRow4RLLLLR i
def kernelRow4RLLLRL (i : ℕ) : ℕ := if i < 69 then 6175547170 else 6729739915
def kernelRow4RLLLRR (i : ℕ) : ℕ := if i < 71 then 6278173124 else 6896857684
def kernelRow4RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow4RLLLRL i else kernelRow4RLLLRR i
def kernelRow4RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow4RLLLL i else kernelRow4RLLLR i
def kernelRow4RLLRLL (i : ℕ) : ℕ := if i < 73 then 5629367354 else 5730491976
def kernelRow4RLLRLR (i : ℕ) : ℕ := if i < 75 then 5625839255 else 6048533709
def kernelRow4RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow4RLLRLL i else kernelRow4RLLRLR i
def kernelRow4RLLRRL (i : ℕ) : ℕ := if i < 77 then 6525276126 else 6218654530
def kernelRow4RLLRRR (i : ℕ) : ℕ := if i < 79 then 10660272565 else 11011759340
def kernelRow4RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow4RLLRRL i else kernelRow4RLLRRR i
def kernelRow4RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow4RLLRL i else kernelRow4RLLRR i
def kernelRow4RLL (i : ℕ) : ℕ := if i < 72 then kernelRow4RLLL i else kernelRow4RLLR i
def kernelRow4RLRLLL (i : ℕ) : ℕ := if i < 81 then 12340613067 else 11344973002
def kernelRow4RLRLLR (i : ℕ) : ℕ := if i < 83 then 11716106515 else 13273717236
def kernelRow4RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow4RLRLLL i else kernelRow4RLRLLR i
def kernelRow4RLRLRL (i : ℕ) : ℕ := if i < 85 then 13018681635 else 12530957013
def kernelRow4RLRLRR (i : ℕ) : ℕ := if i < 87 then 10708066037 else 10902340216
def kernelRow4RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow4RLRLRL i else kernelRow4RLRLRR i
def kernelRow4RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow4RLRLL i else kernelRow4RLRLR i
def kernelRow4RLRRLL (i : ℕ) : ℕ := if i < 89 then 8299903919 else 7895216580
def kernelRow4RLRRLR (i : ℕ) : ℕ := if i < 91 then 5454732483 else 5658236327
def kernelRow4RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow4RLRRLL i else kernelRow4RLRRLR i
def kernelRow4RLRRRL (i : ℕ) : ℕ := if i < 93 then 5274946987 else 5065221278
def kernelRow4RLRRRR (i : ℕ) : ℕ := if i < 95 then 5468073553 else 5425721594
def kernelRow4RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow4RLRRRL i else kernelRow4RLRRRR i
def kernelRow4RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow4RLRRL i else kernelRow4RLRRR i
def kernelRow4RLR (i : ℕ) : ℕ := if i < 88 then kernelRow4RLRL i else kernelRow4RLRR i
def kernelRow4RL (i : ℕ) : ℕ := if i < 80 then kernelRow4RLL i else kernelRow4RLR i
def kernelRow4RRLLLL (i : ℕ) : ℕ := if i < 97 then 5596702111 else 5149077732
def kernelRow4RRLLLR (i : ℕ) : ℕ := if i < 99 then 6672154016 else 7143154798
def kernelRow4RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow4RRLLLL i else kernelRow4RRLLLR i
def kernelRow4RRLLRL (i : ℕ) : ℕ := if i < 101 then 8135137612 else 8047435185
def kernelRow4RRLLRR (i : ℕ) : ℕ := if i < 103 then 6620675964 else 6773241315
def kernelRow4RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow4RRLLRL i else kernelRow4RRLLRR i
def kernelRow4RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow4RRLLL i else kernelRow4RRLLR i
def kernelRow4RRLRLL (i : ℕ) : ℕ := if i < 105 then 9579456988 else 8762768153
def kernelRow4RRLRLR (i : ℕ) : ℕ := if i < 107 then 9419616782 else 10051870602
def kernelRow4RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow4RRLRLL i else kernelRow4RRLRLR i
def kernelRow4RRLRRL (i : ℕ) : ℕ := if i < 109 then 11755129401 else 10595389364
def kernelRow4RRLRRR (i : ℕ) : ℕ := if i < 111 then 7733658019 else 8543742260
def kernelRow4RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow4RRLRRL i else kernelRow4RRLRRR i
def kernelRow4RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow4RRLRL i else kernelRow4RRLRR i
def kernelRow4RRL (i : ℕ) : ℕ := if i < 104 then kernelRow4RRLL i else kernelRow4RRLR i
def kernelRow4RRRLLL (i : ℕ) : ℕ := if i < 113 then 12152367691 else 11179364931
def kernelRow4RRRLLR (i : ℕ) : ℕ := if i < 115 then 12291586341 else 13619835641
def kernelRow4RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow4RRRLLL i else kernelRow4RRRLLR i
def kernelRow4RRRLRL (i : ℕ) : ℕ := if i < 117 then 9236830607 else 8356160638
def kernelRow4RRRLRR (i : ℕ) : ℕ := if i < 119 then 6591217739 else 7576142179
def kernelRow4RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow4RRRLRL i else kernelRow4RRRLRR i
def kernelRow4RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow4RRRLL i else kernelRow4RRRLR i
def kernelRow4RRRRLL (i : ℕ) : ℕ := if i < 121 then 5505037673 else 5001301633
def kernelRow4RRRRLR (i : ℕ) : ℕ := if i < 123 then 3985983240 else 4131861125
def kernelRow4RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow4RRRRLL i else kernelRow4RRRRLR i
def kernelRow4RRRRRL (i : ℕ) : ℕ := if i < 125 then 4018562469 else 3666252552
def kernelRow4RRRRRR (i : ℕ) : ℕ := if i < 127 then 2040073091 else 2280844296
def kernelRow4RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow4RRRRRL i else kernelRow4RRRRRR i
def kernelRow4RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow4RRRRL i else kernelRow4RRRRR i
def kernelRow4RRR (i : ℕ) : ℕ := if i < 120 then kernelRow4RRRL i else kernelRow4RRRR i
def kernelRow4RR (i : ℕ) : ℕ := if i < 112 then kernelRow4RRL i else kernelRow4RRR i
def kernelRow4R (i : ℕ) : ℕ := if i < 96 then kernelRow4RL i else kernelRow4RR i
def kernelRow4 (i : ℕ) : ℕ := if i < 64 then kernelRow4L i else kernelRow4R i
def kernelRow5LLLLLL (i : ℕ) : ℕ := if i < 1 then 3910777853 else 3913096039
def kernelRow5LLLLLR (i : ℕ) : ℕ := if i < 3 then 3382944260 else 3319051999
def kernelRow5LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow5LLLLLL i else kernelRow5LLLLLR i
def kernelRow5LLLLRL (i : ℕ) : ℕ := if i < 5 then 3822821760 else 3941171685
def kernelRow5LLLLRR (i : ℕ) : ℕ := if i < 7 then 5185339550 else 5636082328
def kernelRow5LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow5LLLLRL i else kernelRow5LLLLRR i
def kernelRow5LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow5LLLLL i else kernelRow5LLLLR i
def kernelRow5LLLRLL (i : ℕ) : ℕ := if i < 9 then 6106432131 else 6385132698
def kernelRow5LLLRLR (i : ℕ) : ℕ := if i < 11 then 8116998541 else 7642647409
def kernelRow5LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow5LLLRLL i else kernelRow5LLLRLR i
def kernelRow5LLLRRL (i : ℕ) : ℕ := if i < 13 then 2840863125 else 2839434124
def kernelRow5LLLRRR (i : ℕ) : ℕ := if i < 15 then 5884085344 else 5901140434
def kernelRow5LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow5LLLRRL i else kernelRow5LLLRRR i
def kernelRow5LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow5LLLRL i else kernelRow5LLLRR i
def kernelRow5LLL (i : ℕ) : ℕ := if i < 8 then kernelRow5LLLL i else kernelRow5LLLR i
def kernelRow5LLRLLL (i : ℕ) : ℕ := if i < 17 then 4788226571 else 4468898218
def kernelRow5LLRLLR (i : ℕ) : ℕ := if i < 19 then 5767287678 else 5859822313
def kernelRow5LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow5LLRLLL i else kernelRow5LLRLLR i
def kernelRow5LLRLRL (i : ℕ) : ℕ := if i < 21 then 7847804491 else 7528891452
def kernelRow5LLRLRR (i : ℕ) : ℕ := if i < 23 then 9477386544 else 10018807981
def kernelRow5LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow5LLRLRL i else kernelRow5LLRLRR i
def kernelRow5LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow5LLRLL i else kernelRow5LLRLR i
def kernelRow5LLRRLL (i : ℕ) : ℕ := if i < 25 then 10333274146 else 9931406960
def kernelRow5LLRRLR (i : ℕ) : ℕ := if i < 27 then 8713026456 else 8892316680
def kernelRow5LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow5LLRRLL i else kernelRow5LLRRLR i
def kernelRow5LLRRRL (i : ℕ) : ℕ := if i < 29 then 13285662864 else 13003154450
def kernelRow5LLRRRR (i : ℕ) : ℕ := if i < 31 then 7285005457 else 7486475415
def kernelRow5LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow5LLRRRL i else kernelRow5LLRRRR i
def kernelRow5LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow5LLRRL i else kernelRow5LLRRR i
def kernelRow5LLR (i : ℕ) : ℕ := if i < 24 then kernelRow5LLRL i else kernelRow5LLRR i
def kernelRow5LL (i : ℕ) : ℕ := if i < 16 then kernelRow5LLL i else kernelRow5LLR i
def kernelRow5LRLLLL (i : ℕ) : ℕ := if i < 33 then 8396819484 else 7638579297
def kernelRow5LRLLLR (i : ℕ) : ℕ := if i < 35 then 9944246991 else 9538023187
def kernelRow5LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow5LRLLLL i else kernelRow5LRLLLR i
def kernelRow5LRLLRL (i : ℕ) : ℕ := if i < 37 then 7343358953 else 7137136964
def kernelRow5LRLLRR (i : ℕ) : ℕ := if i < 39 then 13756080122 else 14151626895
def kernelRow5LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow5LRLLRL i else kernelRow5LRLLRR i
def kernelRow5LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow5LRLLL i else kernelRow5LRLLR i
def kernelRow5LRLRLL (i : ℕ) : ℕ := if i < 41 then 10382172284 else 11974331104
def kernelRow5LRLRLR (i : ℕ) : ℕ := if i < 43 then 13244828141 else 12496850179
def kernelRow5LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow5LRLRLL i else kernelRow5LRLRLR i
def kernelRow5LRLRRL (i : ℕ) : ℕ := if i < 45 then 7001645065 else 7698800138
def kernelRow5LRLRRR (i : ℕ) : ℕ := if i < 47 then 6571825011 else 6976566140
def kernelRow5LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow5LRLRRL i else kernelRow5LRLRRR i
def kernelRow5LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow5LRLRL i else kernelRow5LRLRR i
def kernelRow5LRL (i : ℕ) : ℕ := if i < 40 then kernelRow5LRLL i else kernelRow5LRLR i
def kernelRow5LRRLLL (i : ℕ) : ℕ := if i < 49 then 8185890238 else 8081792607
def kernelRow5LRRLLR (i : ℕ) : ℕ := if i < 51 then 10973969627 else 10588653277
def kernelRow5LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow5LRRLLL i else kernelRow5LRRLLR i
def kernelRow5LRRLRL (i : ℕ) : ℕ := if i < 53 then 6569054924 else 6677106078
def kernelRow5LRRLRR (i : ℕ) : ℕ := if i < 55 then 8735314047 else 8745709724
def kernelRow5LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow5LRRLRL i else kernelRow5LRRLRR i
def kernelRow5LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow5LRRLL i else kernelRow5LRRLR i
def kernelRow5LRRRLL (i : ℕ) : ℕ := if i < 57 then 7853913015 else 7359689653
def kernelRow5LRRRLR (i : ℕ) : ℕ := if i < 59 then 10745451850 else 10983219310
def kernelRow5LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow5LRRRLL i else kernelRow5LRRRLR i
def kernelRow5LRRRRL (i : ℕ) : ℕ := if i < 61 then 5260340654 else 5085958756
def kernelRow5LRRRRR (i : ℕ) : ℕ := if i < 63 then 8094312473 else 8291266856
def kernelRow5LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow5LRRRRL i else kernelRow5LRRRRR i
def kernelRow5LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow5LRRRL i else kernelRow5LRRRR i
def kernelRow5LRR (i : ℕ) : ℕ := if i < 56 then kernelRow5LRRL i else kernelRow5LRRR i
def kernelRow5LR (i : ℕ) : ℕ := if i < 48 then kernelRow5LRL i else kernelRow5LRR i
def kernelRow5L (i : ℕ) : ℕ := if i < 32 then kernelRow5LL i else kernelRow5LR i
def kernelRow5RLLLLL (i : ℕ) : ℕ := if i < 65 then 8291266856 else 8094312473
def kernelRow5RLLLLR (i : ℕ) : ℕ := if i < 67 then 5085958756 else 5260340654
def kernelRow5RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow5RLLLLL i else kernelRow5RLLLLR i
def kernelRow5RLLLRL (i : ℕ) : ℕ := if i < 69 then 10983219310 else 10745451850
def kernelRow5RLLLRR (i : ℕ) : ℕ := if i < 71 then 7359689653 else 7853913015
def kernelRow5RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow5RLLLRL i else kernelRow5RLLLRR i
def kernelRow5RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow5RLLLL i else kernelRow5RLLLR i
def kernelRow5RLLRLL (i : ℕ) : ℕ := if i < 73 then 8745709724 else 8735314047
def kernelRow5RLLRLR (i : ℕ) : ℕ := if i < 75 then 6677106078 else 6569054924
def kernelRow5RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow5RLLRLL i else kernelRow5RLLRLR i
def kernelRow5RLLRRL (i : ℕ) : ℕ := if i < 77 then 10588653277 else 10973969627
def kernelRow5RLLRRR (i : ℕ) : ℕ := if i < 79 then 8081792607 else 8185890238
def kernelRow5RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow5RLLRRL i else kernelRow5RLLRRR i
def kernelRow5RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow5RLLRL i else kernelRow5RLLRR i
def kernelRow5RLL (i : ℕ) : ℕ := if i < 72 then kernelRow5RLLL i else kernelRow5RLLR i
def kernelRow5RLRLLL (i : ℕ) : ℕ := if i < 81 then 6976566140 else 6571825011
def kernelRow5RLRLLR (i : ℕ) : ℕ := if i < 83 then 7698800138 else 7001645065
def kernelRow5RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow5RLRLLL i else kernelRow5RLRLLR i
def kernelRow5RLRLRL (i : ℕ) : ℕ := if i < 85 then 12496850179 else 13244828141
def kernelRow5RLRLRR (i : ℕ) : ℕ := if i < 87 then 11974331104 else 10382172284
def kernelRow5RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow5RLRLRL i else kernelRow5RLRLRR i
def kernelRow5RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow5RLRLL i else kernelRow5RLRLR i
def kernelRow5RLRRLL (i : ℕ) : ℕ := if i < 89 then 14151626895 else 13756080122
def kernelRow5RLRRLR (i : ℕ) : ℕ := if i < 91 then 7137136964 else 7343358953
def kernelRow5RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow5RLRRLL i else kernelRow5RLRRLR i
def kernelRow5RLRRRL (i : ℕ) : ℕ := if i < 93 then 9538023187 else 9944246991
def kernelRow5RLRRRR (i : ℕ) : ℕ := if i < 95 then 7638579297 else 8396819484
def kernelRow5RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow5RLRRRL i else kernelRow5RLRRRR i
def kernelRow5RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow5RLRRL i else kernelRow5RLRRR i
def kernelRow5RLR (i : ℕ) : ℕ := if i < 88 then kernelRow5RLRL i else kernelRow5RLRR i
def kernelRow5RL (i : ℕ) : ℕ := if i < 80 then kernelRow5RLL i else kernelRow5RLR i
def kernelRow5RRLLLL (i : ℕ) : ℕ := if i < 97 then 7486475415 else 7285005457
def kernelRow5RRLLLR (i : ℕ) : ℕ := if i < 99 then 13003154450 else 13285662864
def kernelRow5RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow5RRLLLL i else kernelRow5RRLLLR i
def kernelRow5RRLLRL (i : ℕ) : ℕ := if i < 101 then 8892316680 else 8713026456
def kernelRow5RRLLRR (i : ℕ) : ℕ := if i < 103 then 9931406960 else 10333274146
def kernelRow5RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow5RRLLRL i else kernelRow5RRLLRR i
def kernelRow5RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow5RRLLL i else kernelRow5RRLLR i
def kernelRow5RRLRLL (i : ℕ) : ℕ := if i < 105 then 10018807981 else 9477386544
def kernelRow5RRLRLR (i : ℕ) : ℕ := if i < 107 then 7528891452 else 7847804491
def kernelRow5RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow5RRLRLL i else kernelRow5RRLRLR i
def kernelRow5RRLRRL (i : ℕ) : ℕ := if i < 109 then 5859822313 else 5767287678
def kernelRow5RRLRRR (i : ℕ) : ℕ := if i < 111 then 4468898218 else 4788226571
def kernelRow5RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow5RRLRRL i else kernelRow5RRLRRR i
def kernelRow5RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow5RRLRL i else kernelRow5RRLRR i
def kernelRow5RRL (i : ℕ) : ℕ := if i < 104 then kernelRow5RRLL i else kernelRow5RRLR i
def kernelRow5RRRLLL (i : ℕ) : ℕ := if i < 113 then 5901140434 else 5884085344
def kernelRow5RRRLLR (i : ℕ) : ℕ := if i < 115 then 2839434124 else 2840863125
def kernelRow5RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow5RRRLLL i else kernelRow5RRRLLR i
def kernelRow5RRRLRL (i : ℕ) : ℕ := if i < 117 then 7642647409 else 8116998541
def kernelRow5RRRLRR (i : ℕ) : ℕ := if i < 119 then 6385132698 else 6106432131
def kernelRow5RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow5RRRLRL i else kernelRow5RRRLRR i
def kernelRow5RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow5RRRLL i else kernelRow5RRRLR i
def kernelRow5RRRRLL (i : ℕ) : ℕ := if i < 121 then 5636082328 else 5185339550
def kernelRow5RRRRLR (i : ℕ) : ℕ := if i < 123 then 3941171685 else 3822821760
def kernelRow5RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow5RRRRLL i else kernelRow5RRRRLR i
def kernelRow5RRRRRL (i : ℕ) : ℕ := if i < 125 then 3319051999 else 3382944260
def kernelRow5RRRRRR (i : ℕ) : ℕ := if i < 127 then 3913096039 else 3910777853
def kernelRow5RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow5RRRRRL i else kernelRow5RRRRRR i
def kernelRow5RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow5RRRRL i else kernelRow5RRRRR i
def kernelRow5RRR (i : ℕ) : ℕ := if i < 120 then kernelRow5RRRL i else kernelRow5RRRR i
def kernelRow5RR (i : ℕ) : ℕ := if i < 112 then kernelRow5RRL i else kernelRow5RRR i
def kernelRow5R (i : ℕ) : ℕ := if i < 96 then kernelRow5RL i else kernelRow5RR i
def kernelRow5 (i : ℕ) : ℕ := if i < 64 then kernelRow5L i else kernelRow5R i
def kernelRow6LLLLLL (i : ℕ) : ℕ := if i < 1 then 3453840319 else 3848999088
def kernelRow6LLLLLR (i : ℕ) : ℕ := if i < 3 then 5848584706 else 5516519903
def kernelRow6LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow6LLLLLL i else kernelRow6LLLLLR i
def kernelRow6LLLLRL (i : ℕ) : ℕ := if i < 5 then 4224115756 else 4558050599
def kernelRow6LLLLRR (i : ℕ) : ℕ := if i < 7 then 5007555039 else 4603803032
def kernelRow6LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow6LLLLRL i else kernelRow6LLLLRR i
def kernelRow6LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow6LLLLL i else kernelRow6LLLLR i
def kernelRow6LLLRLL (i : ℕ) : ℕ := if i < 9 then 7890675415 else 8265318750
def kernelRow6LLLRLR (i : ℕ) : ℕ := if i < 11 then 10783540791 else 9986908295
def kernelRow6LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow6LLLRLL i else kernelRow6LLLRLR i
def kernelRow6LLLRRL (i : ℕ) : ℕ := if i < 13 then 9410170589 else 10369543207
def kernelRow6LLLRRR (i : ℕ) : ℕ := if i < 15 then 14821195943 else 13389427483
def kernelRow6LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow6LLLRRL i else kernelRow6LLLRRR i
def kernelRow6LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow6LLLRL i else kernelRow6LLLRR i
def kernelRow6LLL (i : ℕ) : ℕ := if i < 8 then kernelRow6LLLL i else kernelRow6LLLR i
def kernelRow6LLRLLL (i : ℕ) : ℕ := if i < 17 then 12799433018 else 13610929209
def kernelRow6LLRLLR (i : ℕ) : ℕ := if i < 19 then 12847943005 else 12218716153
def kernelRow6LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow6LLRLLL i else kernelRow6LLRLLR i
def kernelRow6LLRLRL (i : ℕ) : ℕ := if i < 21 then 8128478059 else 8499837376
def kernelRow6LLRLRR (i : ℕ) : ℕ := if i < 23 then 6606330874 else 6741251994
def kernelRow6LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow6LLRLRL i else kernelRow6LLRLRR i
def kernelRow6LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow6LLRLL i else kernelRow6LLRLR i
def kernelRow6LLRRLL (i : ℕ) : ℕ := if i < 25 then 5630297339 else 5789621533
def kernelRow6LLRRLR (i : ℕ) : ℕ := if i < 27 then 7975031278 else 8453296192
def kernelRow6LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow6LLRRLL i else kernelRow6LLRRLR i
def kernelRow6LLRRRL (i : ℕ) : ℕ := if i < 29 then 4944155949 else 5141307339
def kernelRow6LLRRRR (i : ℕ) : ℕ := if i < 31 then 7754151293 else 8040906666
def kernelRow6LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow6LLRRRL i else kernelRow6LLRRRR i
def kernelRow6LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow6LLRRL i else kernelRow6LLRRR i
def kernelRow6LLR (i : ℕ) : ℕ := if i < 24 then kernelRow6LLRL i else kernelRow6LLRR i
def kernelRow6LL (i : ℕ) : ℕ := if i < 16 then kernelRow6LLL i else kernelRow6LLR i
def kernelRow6LRLLLL (i : ℕ) : ℕ := if i < 33 then 8924668573 else 8154404246
def kernelRow6LRLLLR (i : ℕ) : ℕ := if i < 35 then 9151003670 else 9015635011
def kernelRow6LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow6LRLLLL i else kernelRow6LRLLLR i
def kernelRow6LRLLRL (i : ℕ) : ℕ := if i < 37 then 7885744023 else 8071771675
def kernelRow6LRLLRR (i : ℕ) : ℕ := if i < 39 then 5924937911 else 5992628582
def kernelRow6LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow6LRLLRL i else kernelRow6LRLLRR i
def kernelRow6LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow6LRLLL i else kernelRow6LRLLR i
def kernelRow6LRLRLL (i : ℕ) : ℕ := if i < 41 then 7432884442 else 7339268695
def kernelRow6LRLRLR (i : ℕ) : ℕ := if i < 43 then 6542629845 else 6873875077
def kernelRow6LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow6LRLRLL i else kernelRow6LRLRLR i
def kernelRow6LRLRRL (i : ℕ) : ℕ := if i < 45 then 6698639483 else 7046962914
def kernelRow6LRLRRR (i : ℕ) : ℕ := if i < 47 then 7726908024 else 7346268698
def kernelRow6LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow6LRLRRL i else kernelRow6LRLRRR i
def kernelRow6LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow6LRLRL i else kernelRow6LRLRR i
def kernelRow6LRL (i : ℕ) : ℕ := if i < 40 then kernelRow6LRLL i else kernelRow6LRLR i
def kernelRow6LRRLLL (i : ℕ) : ℕ := if i < 49 then 7811623429 else 7493029813
def kernelRow6LRRLLR (i : ℕ) : ℕ := if i < 51 then 8521576124 else 8575780564
def kernelRow6LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow6LRRLLL i else kernelRow6LRRLLR i
def kernelRow6LRRLRL (i : ℕ) : ℕ := if i < 53 then 6849552525 else 6995412102
def kernelRow6LRRLRR (i : ℕ) : ℕ := if i < 55 then 6499772181 else 6985331250
def kernelRow6LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow6LRRLRL i else kernelRow6LRRLRR i
def kernelRow6LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow6LRRLL i else kernelRow6LRRLR i
def kernelRow6LRRRLL (i : ℕ) : ℕ := if i < 57 then 5613120735 else 5455788459
def kernelRow6LRRRLR (i : ℕ) : ℕ := if i < 59 then 9450076519 else 9015687118
def kernelRow6LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow6LRRRLL i else kernelRow6LRRRLR i
def kernelRow6LRRRRL (i : ℕ) : ℕ := if i < 61 then 5971858376 else 5730244463
def kernelRow6LRRRRR (i : ℕ) : ℕ := if i < 63 then 10672116348 else 11070862933
def kernelRow6LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow6LRRRRL i else kernelRow6LRRRRR i
def kernelRow6LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow6LRRRL i else kernelRow6LRRRR i
def kernelRow6LRR (i : ℕ) : ℕ := if i < 56 then kernelRow6LRRL i else kernelRow6LRRR i
def kernelRow6LR (i : ℕ) : ℕ := if i < 48 then kernelRow6LRL i else kernelRow6LRR i
def kernelRow6L (i : ℕ) : ℕ := if i < 32 then kernelRow6LL i else kernelRow6LR i
def kernelRow6RLLLLL (i : ℕ) : ℕ := if i < 65 then 11070862933 else 10672116348
def kernelRow6RLLLLR (i : ℕ) : ℕ := if i < 67 then 5730244463 else 5971858376
def kernelRow6RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow6RLLLLL i else kernelRow6RLLLLR i
def kernelRow6RLLLRL (i : ℕ) : ℕ := if i < 69 then 9015687118 else 9450076519
def kernelRow6RLLLRR (i : ℕ) : ℕ := if i < 71 then 5455788459 else 5613120735
def kernelRow6RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow6RLLLRL i else kernelRow6RLLLRR i
def kernelRow6RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow6RLLLL i else kernelRow6RLLLR i
def kernelRow6RLLRLL (i : ℕ) : ℕ := if i < 73 then 6985331250 else 6499772181
def kernelRow6RLLRLR (i : ℕ) : ℕ := if i < 75 then 6995412102 else 6849552525
def kernelRow6RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow6RLLRLL i else kernelRow6RLLRLR i
def kernelRow6RLLRRL (i : ℕ) : ℕ := if i < 77 then 8575780564 else 8521576124
def kernelRow6RLLRRR (i : ℕ) : ℕ := if i < 79 then 7493029813 else 7811623429
def kernelRow6RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow6RLLRRL i else kernelRow6RLLRRR i
def kernelRow6RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow6RLLRL i else kernelRow6RLLRR i
def kernelRow6RLL (i : ℕ) : ℕ := if i < 72 then kernelRow6RLLL i else kernelRow6RLLR i
def kernelRow6RLRLLL (i : ℕ) : ℕ := if i < 81 then 7346268698 else 7726908024
def kernelRow6RLRLLR (i : ℕ) : ℕ := if i < 83 then 7046962914 else 6698639483
def kernelRow6RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow6RLRLLL i else kernelRow6RLRLLR i
def kernelRow6RLRLRL (i : ℕ) : ℕ := if i < 85 then 6873875077 else 6542629845
def kernelRow6RLRLRR (i : ℕ) : ℕ := if i < 87 then 7339268695 else 7432884442
def kernelRow6RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow6RLRLRL i else kernelRow6RLRLRR i
def kernelRow6RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow6RLRLL i else kernelRow6RLRLR i
def kernelRow6RLRRLL (i : ℕ) : ℕ := if i < 89 then 5992628582 else 5924937911
def kernelRow6RLRRLR (i : ℕ) : ℕ := if i < 91 then 8071771675 else 7885744023
def kernelRow6RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow6RLRRLL i else kernelRow6RLRRLR i
def kernelRow6RLRRRL (i : ℕ) : ℕ := if i < 93 then 9015635011 else 9151003670
def kernelRow6RLRRRR (i : ℕ) : ℕ := if i < 95 then 8154404246 else 8924668573
def kernelRow6RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow6RLRRRL i else kernelRow6RLRRRR i
def kernelRow6RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow6RLRRL i else kernelRow6RLRRR i
def kernelRow6RLR (i : ℕ) : ℕ := if i < 88 then kernelRow6RLRL i else kernelRow6RLRR i
def kernelRow6RL (i : ℕ) : ℕ := if i < 80 then kernelRow6RLL i else kernelRow6RLR i
def kernelRow6RRLLLL (i : ℕ) : ℕ := if i < 97 then 8040906666 else 7754151293
def kernelRow6RRLLLR (i : ℕ) : ℕ := if i < 99 then 5141307339 else 4944155949
def kernelRow6RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow6RRLLLL i else kernelRow6RRLLLR i
def kernelRow6RRLLRL (i : ℕ) : ℕ := if i < 101 then 8453296192 else 7975031278
def kernelRow6RRLLRR (i : ℕ) : ℕ := if i < 103 then 5789621533 else 5630297339
def kernelRow6RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow6RRLLRL i else kernelRow6RRLLRR i
def kernelRow6RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow6RRLLL i else kernelRow6RRLLR i
def kernelRow6RRLRLL (i : ℕ) : ℕ := if i < 105 then 6741251994 else 6606330874
def kernelRow6RRLRLR (i : ℕ) : ℕ := if i < 107 then 8499837376 else 8128478059
def kernelRow6RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow6RRLRLL i else kernelRow6RRLRLR i
def kernelRow6RRLRRL (i : ℕ) : ℕ := if i < 109 then 12218716153 else 12847943005
def kernelRow6RRLRRR (i : ℕ) : ℕ := if i < 111 then 13610929209 else 12799433018
def kernelRow6RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow6RRLRRL i else kernelRow6RRLRRR i
def kernelRow6RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow6RRLRL i else kernelRow6RRLRR i
def kernelRow6RRL (i : ℕ) : ℕ := if i < 104 then kernelRow6RRLL i else kernelRow6RRLR i
def kernelRow6RRRLLL (i : ℕ) : ℕ := if i < 113 then 13389427483 else 14821195943
def kernelRow6RRRLLR (i : ℕ) : ℕ := if i < 115 then 10369543207 else 9410170589
def kernelRow6RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow6RRRLLL i else kernelRow6RRRLLR i
def kernelRow6RRRLRL (i : ℕ) : ℕ := if i < 117 then 9986908295 else 10783540791
def kernelRow6RRRLRR (i : ℕ) : ℕ := if i < 119 then 8265318750 else 7890675415
def kernelRow6RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow6RRRLRL i else kernelRow6RRRLRR i
def kernelRow6RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow6RRRLL i else kernelRow6RRRLR i
def kernelRow6RRRRLL (i : ℕ) : ℕ := if i < 121 then 4603803032 else 5007555039
def kernelRow6RRRRLR (i : ℕ) : ℕ := if i < 123 then 4558050599 else 4224115756
def kernelRow6RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow6RRRRLL i else kernelRow6RRRRLR i
def kernelRow6RRRRRL (i : ℕ) : ℕ := if i < 125 then 5516519903 else 5848584706
def kernelRow6RRRRRR (i : ℕ) : ℕ := if i < 127 then 3848999088 else 3453840319
def kernelRow6RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow6RRRRRL i else kernelRow6RRRRRR i
def kernelRow6RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow6RRRRL i else kernelRow6RRRRR i
def kernelRow6RRR (i : ℕ) : ℕ := if i < 120 then kernelRow6RRRL i else kernelRow6RRRR i
def kernelRow6RR (i : ℕ) : ℕ := if i < 112 then kernelRow6RRL i else kernelRow6RRR i
def kernelRow6R (i : ℕ) : ℕ := if i < 96 then kernelRow6RL i else kernelRow6RR i
def kernelRow6 (i : ℕ) : ℕ := if i < 64 then kernelRow6L i else kernelRow6R i
def kernelRow7LLLLLL (i : ℕ) : ℕ := if i < 1 then 2209813120 else 2291992270
def kernelRow7LLLLLR (i : ℕ) : ℕ := if i < 3 then 1419270661 else 1406175978
def kernelRow7LLLLL (i : ℕ) : ℕ := if i < 2 then kernelRow7LLLLLL i else kernelRow7LLLLLR i
def kernelRow7LLLLRL (i : ℕ) : ℕ := if i < 5 then 2589939036 else 2688916416
def kernelRow7LLLLRR (i : ℕ) : ℕ := if i < 7 then 2973918020 else 2758257225
def kernelRow7LLLLR (i : ℕ) : ℕ := if i < 6 then kernelRow7LLLLRL i else kernelRow7LLLLRR i
def kernelRow7LLLL (i : ℕ) : ℕ := if i < 4 then kernelRow7LLLLL i else kernelRow7LLLLR i
def kernelRow7LLLRLL (i : ℕ) : ℕ := if i < 9 then 3031248700 else 3127114167
def kernelRow7LLLRLR (i : ℕ) : ℕ := if i < 11 then 4434882776 else 4596367909
def kernelRow7LLLRL (i : ℕ) : ℕ := if i < 10 then kernelRow7LLLRLL i else kernelRow7LLLRLR i
def kernelRow7LLLRRL (i : ℕ) : ℕ := if i < 13 then 4273578564 else 4251819687
def kernelRow7LLLRRR (i : ℕ) : ℕ := if i < 15 then 3941214450 else 3745117691
def kernelRow7LLLRR (i : ℕ) : ℕ := if i < 14 then kernelRow7LLLRRL i else kernelRow7LLLRRR i
def kernelRow7LLLR (i : ℕ) : ℕ := if i < 12 then kernelRow7LLLRL i else kernelRow7LLLRR i
def kernelRow7LLL (i : ℕ) : ℕ := if i < 8 then kernelRow7LLLL i else kernelRow7LLLR i
def kernelRow7LLRLLL (i : ℕ) : ℕ := if i < 17 then 5936903380 else 6140477148
def kernelRow7LLRLLR (i : ℕ) : ℕ := if i < 19 then 7101849976 else 7299325410
def kernelRow7LLRLL (i : ℕ) : ℕ := if i < 18 then kernelRow7LLRLLL i else kernelRow7LLRLLR i
def kernelRow7LLRLRL (i : ℕ) : ℕ := if i < 21 then 7259839553 else 7198286840
def kernelRow7LLRLRR (i : ℕ) : ℕ := if i < 23 then 6125926079 else 5952377921
def kernelRow7LLRLR (i : ℕ) : ℕ := if i < 22 then kernelRow7LLRLRL i else kernelRow7LLRLRR i
def kernelRow7LLRL (i : ℕ) : ℕ := if i < 20 then kernelRow7LLRLL i else kernelRow7LLRLR i
def kernelRow7LLRRLL (i : ℕ) : ℕ := if i < 25 then 9019108149 else 8796406183
def kernelRow7LLRRLR (i : ℕ) : ℕ := if i < 27 then 8319318093 else 8363333654
def kernelRow7LLRRL (i : ℕ) : ℕ := if i < 26 then kernelRow7LLRRLL i else kernelRow7LLRRLR i
def kernelRow7LLRRRL (i : ℕ) : ℕ := if i < 29 then 4923736824 else 5020458635
def kernelRow7LLRRRR (i : ℕ) : ℕ := if i < 31 then 6362061624 else 6499703042
def kernelRow7LLRRR (i : ℕ) : ℕ := if i < 30 then kernelRow7LLRRRL i else kernelRow7LLRRRR i
def kernelRow7LLRR (i : ℕ) : ℕ := if i < 28 then kernelRow7LLRRL i else kernelRow7LLRRR i
def kernelRow7LLR (i : ℕ) : ℕ := if i < 24 then kernelRow7LLRL i else kernelRow7LLRR i
def kernelRow7LL (i : ℕ) : ℕ := if i < 16 then kernelRow7LLL i else kernelRow7LLR i
def kernelRow7LRLLLL (i : ℕ) : ℕ := if i < 33 then 8691889053 else 8551907859
def kernelRow7LRLLLR (i : ℕ) : ℕ := if i < 35 then 11595780431 else 12384516668
def kernelRow7LRLLL (i : ℕ) : ℕ := if i < 34 then kernelRow7LRLLLL i else kernelRow7LRLLLR i
def kernelRow7LRLLRL (i : ℕ) : ℕ := if i < 37 then 20976397176 else 20083861304
def kernelRow7LRLLRR (i : ℕ) : ℕ := if i < 39 then 21748852979 else 22057689324
def kernelRow7LRLLR (i : ℕ) : ℕ := if i < 38 then kernelRow7LRLLRL i else kernelRow7LRLLRR i
def kernelRow7LRLL (i : ℕ) : ℕ := if i < 36 then kernelRow7LRLLL i else kernelRow7LRLLR i
def kernelRow7LRLRLL (i : ℕ) : ℕ := if i < 41 then 11218192053 else 11252766026
def kernelRow7LRLRLR (i : ℕ) : ℕ := if i < 43 then 9579541354 else 9969849644
def kernelRow7LRLRL (i : ℕ) : ℕ := if i < 42 then kernelRow7LRLRLL i else kernelRow7LRLRLR i
def kernelRow7LRLRRL (i : ℕ) : ℕ := if i < 45 then 12555276074 else 11356404923
def kernelRow7LRLRRR (i : ℕ) : ℕ := if i < 47 then 10641713759 else 10965963866
def kernelRow7LRLRR (i : ℕ) : ℕ := if i < 46 then kernelRow7LRLRRL i else kernelRow7LRLRRR i
def kernelRow7LRLR (i : ℕ) : ℕ := if i < 44 then kernelRow7LRLRL i else kernelRow7LRLRR i
def kernelRow7LRL (i : ℕ) : ℕ := if i < 40 then kernelRow7LRLL i else kernelRow7LRLR i
def kernelRow7LRRLLL (i : ℕ) : ℕ := if i < 49 then 9482128396 else 9158231810
def kernelRow7LRRLLR (i : ℕ) : ℕ := if i < 51 then 7923351873 else 8115137618
def kernelRow7LRRLL (i : ℕ) : ℕ := if i < 50 then kernelRow7LRRLLL i else kernelRow7LRRLLR i
def kernelRow7LRRLRL (i : ℕ) : ℕ := if i < 53 then 7501990324 else 7336001645
def kernelRow7LRRLRR (i : ℕ) : ℕ := if i < 55 then 7358584971 else 7750371176
def kernelRow7LRRLR (i : ℕ) : ℕ := if i < 54 then kernelRow7LRRLRL i else kernelRow7LRRLRR i
def kernelRow7LRRL (i : ℕ) : ℕ := if i < 52 then kernelRow7LRRLL i else kernelRow7LRRLR i
def kernelRow7LRRRLL (i : ℕ) : ℕ := if i < 57 then 10372437015 else 10428478251
def kernelRow7LRRRLR (i : ℕ) : ℕ := if i < 59 then 7458847473 else 7365129172
def kernelRow7LRRRL (i : ℕ) : ℕ := if i < 58 then kernelRow7LRRRLL i else kernelRow7LRRRLR i
def kernelRow7LRRRRL (i : ℕ) : ℕ := if i < 61 then 7889075997 else 7456224649
def kernelRow7LRRRRR (i : ℕ) : ℕ := if i < 63 then 5352598226 else 5362069730
def kernelRow7LRRRR (i : ℕ) : ℕ := if i < 62 then kernelRow7LRRRRL i else kernelRow7LRRRRR i
def kernelRow7LRRR (i : ℕ) : ℕ := if i < 60 then kernelRow7LRRRL i else kernelRow7LRRRR i
def kernelRow7LRR (i : ℕ) : ℕ := if i < 56 then kernelRow7LRRL i else kernelRow7LRRR i
def kernelRow7LR (i : ℕ) : ℕ := if i < 48 then kernelRow7LRL i else kernelRow7LRR i
def kernelRow7L (i : ℕ) : ℕ := if i < 32 then kernelRow7LL i else kernelRow7LR i
def kernelRow7RLLLLL (i : ℕ) : ℕ := if i < 65 then 5362069730 else 5352598226
def kernelRow7RLLLLR (i : ℕ) : ℕ := if i < 67 then 7456224649 else 7889075997
def kernelRow7RLLLL (i : ℕ) : ℕ := if i < 66 then kernelRow7RLLLLL i else kernelRow7RLLLLR i
def kernelRow7RLLLRL (i : ℕ) : ℕ := if i < 69 then 7365129172 else 7458847473
def kernelRow7RLLLRR (i : ℕ) : ℕ := if i < 71 then 10428478251 else 10372437015
def kernelRow7RLLLR (i : ℕ) : ℕ := if i < 70 then kernelRow7RLLLRL i else kernelRow7RLLLRR i
def kernelRow7RLLL (i : ℕ) : ℕ := if i < 68 then kernelRow7RLLLL i else kernelRow7RLLLR i
def kernelRow7RLLRLL (i : ℕ) : ℕ := if i < 73 then 7750371176 else 7358584971
def kernelRow7RLLRLR (i : ℕ) : ℕ := if i < 75 then 7336001645 else 7501990324
def kernelRow7RLLRL (i : ℕ) : ℕ := if i < 74 then kernelRow7RLLRLL i else kernelRow7RLLRLR i
def kernelRow7RLLRRL (i : ℕ) : ℕ := if i < 77 then 8115137618 else 7923351873
def kernelRow7RLLRRR (i : ℕ) : ℕ := if i < 79 then 9158231810 else 9482128396
def kernelRow7RLLRR (i : ℕ) : ℕ := if i < 78 then kernelRow7RLLRRL i else kernelRow7RLLRRR i
def kernelRow7RLLR (i : ℕ) : ℕ := if i < 76 then kernelRow7RLLRL i else kernelRow7RLLRR i
def kernelRow7RLL (i : ℕ) : ℕ := if i < 72 then kernelRow7RLLL i else kernelRow7RLLR i
def kernelRow7RLRLLL (i : ℕ) : ℕ := if i < 81 then 10965963866 else 10641713759
def kernelRow7RLRLLR (i : ℕ) : ℕ := if i < 83 then 11356404923 else 12555276074
def kernelRow7RLRLL (i : ℕ) : ℕ := if i < 82 then kernelRow7RLRLLL i else kernelRow7RLRLLR i
def kernelRow7RLRLRL (i : ℕ) : ℕ := if i < 85 then 9969849644 else 9579541354
def kernelRow7RLRLRR (i : ℕ) : ℕ := if i < 87 then 11252766026 else 11218192053
def kernelRow7RLRLR (i : ℕ) : ℕ := if i < 86 then kernelRow7RLRLRL i else kernelRow7RLRLRR i
def kernelRow7RLRL (i : ℕ) : ℕ := if i < 84 then kernelRow7RLRLL i else kernelRow7RLRLR i
def kernelRow7RLRRLL (i : ℕ) : ℕ := if i < 89 then 22057689324 else 21748852979
def kernelRow7RLRRLR (i : ℕ) : ℕ := if i < 91 then 20083861304 else 20976397176
def kernelRow7RLRRL (i : ℕ) : ℕ := if i < 90 then kernelRow7RLRRLL i else kernelRow7RLRRLR i
def kernelRow7RLRRRL (i : ℕ) : ℕ := if i < 93 then 12384516668 else 11595780431
def kernelRow7RLRRRR (i : ℕ) : ℕ := if i < 95 then 8551907859 else 8691889053
def kernelRow7RLRRR (i : ℕ) : ℕ := if i < 94 then kernelRow7RLRRRL i else kernelRow7RLRRRR i
def kernelRow7RLRR (i : ℕ) : ℕ := if i < 92 then kernelRow7RLRRL i else kernelRow7RLRRR i
def kernelRow7RLR (i : ℕ) : ℕ := if i < 88 then kernelRow7RLRL i else kernelRow7RLRR i
def kernelRow7RL (i : ℕ) : ℕ := if i < 80 then kernelRow7RLL i else kernelRow7RLR i
def kernelRow7RRLLLL (i : ℕ) : ℕ := if i < 97 then 6499703042 else 6362061624
def kernelRow7RRLLLR (i : ℕ) : ℕ := if i < 99 then 5020458635 else 4923736824
def kernelRow7RRLLL (i : ℕ) : ℕ := if i < 98 then kernelRow7RRLLLL i else kernelRow7RRLLLR i
def kernelRow7RRLLRL (i : ℕ) : ℕ := if i < 101 then 8363333654 else 8319318093
def kernelRow7RRLLRR (i : ℕ) : ℕ := if i < 103 then 8796406183 else 9019108149
def kernelRow7RRLLR (i : ℕ) : ℕ := if i < 102 then kernelRow7RRLLRL i else kernelRow7RRLLRR i
def kernelRow7RRLL (i : ℕ) : ℕ := if i < 100 then kernelRow7RRLLL i else kernelRow7RRLLR i
def kernelRow7RRLRLL (i : ℕ) : ℕ := if i < 105 then 5952377921 else 6125926079
def kernelRow7RRLRLR (i : ℕ) : ℕ := if i < 107 then 7198286840 else 7259839553
def kernelRow7RRLRL (i : ℕ) : ℕ := if i < 106 then kernelRow7RRLRLL i else kernelRow7RRLRLR i
def kernelRow7RRLRRL (i : ℕ) : ℕ := if i < 109 then 7299325410 else 7101849976
def kernelRow7RRLRRR (i : ℕ) : ℕ := if i < 111 then 6140477148 else 5936903380
def kernelRow7RRLRR (i : ℕ) : ℕ := if i < 110 then kernelRow7RRLRRL i else kernelRow7RRLRRR i
def kernelRow7RRLR (i : ℕ) : ℕ := if i < 108 then kernelRow7RRLRL i else kernelRow7RRLRR i
def kernelRow7RRL (i : ℕ) : ℕ := if i < 104 then kernelRow7RRLL i else kernelRow7RRLR i
def kernelRow7RRRLLL (i : ℕ) : ℕ := if i < 113 then 3745117691 else 3941214450
def kernelRow7RRRLLR (i : ℕ) : ℕ := if i < 115 then 4251819687 else 4273578564
def kernelRow7RRRLL (i : ℕ) : ℕ := if i < 114 then kernelRow7RRRLLL i else kernelRow7RRRLLR i
def kernelRow7RRRLRL (i : ℕ) : ℕ := if i < 117 then 4596367909 else 4434882776
def kernelRow7RRRLRR (i : ℕ) : ℕ := if i < 119 then 3127114167 else 3031248700
def kernelRow7RRRLR (i : ℕ) : ℕ := if i < 118 then kernelRow7RRRLRL i else kernelRow7RRRLRR i
def kernelRow7RRRL (i : ℕ) : ℕ := if i < 116 then kernelRow7RRRLL i else kernelRow7RRRLR i
def kernelRow7RRRRLL (i : ℕ) : ℕ := if i < 121 then 2758257225 else 2973918020
def kernelRow7RRRRLR (i : ℕ) : ℕ := if i < 123 then 2688916416 else 2589939036
def kernelRow7RRRRL (i : ℕ) : ℕ := if i < 122 then kernelRow7RRRRLL i else kernelRow7RRRRLR i
def kernelRow7RRRRRL (i : ℕ) : ℕ := if i < 125 then 1406175978 else 1419270661
def kernelRow7RRRRRR (i : ℕ) : ℕ := if i < 127 then 2291992270 else 2209813120
def kernelRow7RRRRR (i : ℕ) : ℕ := if i < 126 then kernelRow7RRRRRL i else kernelRow7RRRRRR i
def kernelRow7RRRR (i : ℕ) : ℕ := if i < 124 then kernelRow7RRRRL i else kernelRow7RRRRR i
def kernelRow7RRR (i : ℕ) : ℕ := if i < 120 then kernelRow7RRRL i else kernelRow7RRRR i
def kernelRow7RR (i : ℕ) : ℕ := if i < 112 then kernelRow7RRL i else kernelRow7RRR i
def kernelRow7R (i : ℕ) : ℕ := if i < 96 then kernelRow7RL i else kernelRow7RR i
def kernelRow7 (i : ℕ) : ℕ := if i < 64 then kernelRow7L i else kernelRow7R i
def weightRow0LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 78904189846105 else 82188263104105
def weightRow0LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 63507445559105 else 62649921178105
def weightRow0LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow0LLLLLLLL i else weightRow0LLLLLLLR i
def weightRow0LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 112167339279105 else 110044947245105
def weightRow0LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 168936611049105 else 167794590059105
def weightRow0LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow0LLLLLLRL i else weightRow0LLLLLLRR i
def weightRow0LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow0LLLLLLL i else weightRow0LLLLLLR i
def weightRow0LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 245005261192105 else 242450727036105
def weightRow0LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 269099127263105 else 279286689667105
def weightRow0LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow0LLLLLRLL i else weightRow0LLLLLRLR i
def weightRow0LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 189202373722105 else 201109389938105
def weightRow0LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 285049456102105 else 301086217330105
def weightRow0LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow0LLLLLRRL i else weightRow0LLLLLRRR i
def weightRow0LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow0LLLLLRL i else weightRow0LLLLLRR i
def weightRow0LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow0LLLLLL i else weightRow0LLLLLR i
def weightRow0LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 240569372666105 else 245047053975105
def weightRow0LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 333783376344105 else 345506382221105
def weightRow0LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow0LLLLRLLL i else weightRow0LLLLRLLR i
def weightRow0LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 309277701702105 else 299782171814105
def weightRow0LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 264485100756105 else 278003622382105
def weightRow0LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow0LLLLRLRL i else weightRow0LLLLRLRR i
def weightRow0LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow0LLLLRLL i else weightRow0LLLLRLR i
def weightRow0LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 288769213513105 else 280546241354105
def weightRow0LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 282458216916105 else 292497231505105
def weightRow0LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow0LLLLRRLL i else weightRow0LLLLRRLR i
def weightRow0LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 342753164686105 else 323630601320105
def weightRow0LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 405544106102105 else 416689225736105
def weightRow0LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow0LLLLRRRL i else weightRow0LLLLRRRR i
def weightRow0LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow0LLLLRRL i else weightRow0LLLLRRR i
def weightRow0LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow0LLLLRL i else weightRow0LLLLRR i
def weightRow0LLLL (i : ℕ) : ℕ := if i < 16 then weightRow0LLLLL i else weightRow0LLLLR i
def weightRow0LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 521670246081105 else 513514212689105
def weightRow0LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 543263585641105 else 547123483618105
def weightRow0LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow0LLLRLLLL i else weightRow0LLLRLLLR i
def weightRow0LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 587348266197105 else 561557446271105
def weightRow0LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 559216689925105 else 597712128475105
def weightRow0LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow0LLLRLLRL i else weightRow0LLLRLLRR i
def weightRow0LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow0LLLRLLL i else weightRow0LLLRLLR i
def weightRow0LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 634410189008105 else 606833613817105
def weightRow0LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 694291469370105 else 702913720588105
def weightRow0LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow0LLLRLRLL i else weightRow0LLLRLRLR i
def weightRow0LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 812333083433105 else 772936889462105
def weightRow0LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 816753569820105 else 831975162441105
def weightRow0LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow0LLLRLRRL i else weightRow0LLLRLRRR i
def weightRow0LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow0LLLRLRL i else weightRow0LLLRLRR i
def weightRow0LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow0LLLRLL i else weightRow0LLLRLR i
def weightRow0LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 882719739039105 else 869797558658105
def weightRow0LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 889928404181105 else 921503284399105
def weightRow0LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow0LLLRRLLL i else weightRow0LLLRRLLR i
def weightRow0LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 1090454370799105 else 1064823374642105
def weightRow0LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 1117396325983105 else 1168703940145105
def weightRow0LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow0LLLRRLRL i else weightRow0LLLRRLRR i
def weightRow0LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow0LLLRRLL i else weightRow0LLLRRLR i
def weightRow0LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 1360002061706105 else 1375034259031105
def weightRow0LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 1545397142607105 else 1586068019343105
def weightRow0LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow0LLLRRRLL i else weightRow0LLLRRRLR i
def weightRow0LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 1549636664087105 else 1493713254422105
def weightRow0LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 1432834095093105 else 1454575281316105
def weightRow0LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow0LLLRRRRL i else weightRow0LLLRRRRR i
def weightRow0LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow0LLLRRRL i else weightRow0LLLRRRR i
def weightRow0LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow0LLLRRL i else weightRow0LLLRRR i
def weightRow0LLLR (i : ℕ) : ℕ := if i < 48 then weightRow0LLLRL i else weightRow0LLLRR i
def weightRow0LLL (i : ℕ) : ℕ := if i < 32 then weightRow0LLLL i else weightRow0LLLR i
def weightRow0LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 1476053738186105 else 1456472962352105
def weightRow0LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 1561594851498105 else 1620246660764105
def weightRow0LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow0LLRLLLLL i else weightRow0LLRLLLLR i
def weightRow0LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 1703133251559105 else 1665473028823105
def weightRow0LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 1540197649395105 else 1527351094579105
def weightRow0LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow0LLRLLLRL i else weightRow0LLRLLLRR i
def weightRow0LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow0LLRLLLL i else weightRow0LLRLLLR i
def weightRow0LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 1376195265022105 else 1326071241210105
def weightRow0LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 1310456105190105 else 1336887802255105
def weightRow0LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow0LLRLLRLL i else weightRow0LLRLLRLR i
def weightRow0LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 1202012273823105 else 1171157135326105
def weightRow0LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 1182679077509105 else 1196041500875105
def weightRow0LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow0LLRLLRRL i else weightRow0LLRLLRRR i
def weightRow0LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow0LLRLLRL i else weightRow0LLRLLRR i
def weightRow0LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow0LLRLLL i else weightRow0LLRLLR i
def weightRow0LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 1176336290957105 else 1161526607015105
def weightRow0LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 1147755986464105 else 1187948093566105
def weightRow0LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow0LLRLRLLL i else weightRow0LLRLRLLR i
def weightRow0LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 1106649983448105 else 1099318683912105
def weightRow0LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 1037344345455105 else 1066526624024105
def weightRow0LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow0LLRLRLRL i else weightRow0LLRLRLRR i
def weightRow0LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow0LLRLRLL i else weightRow0LLRLRLR i
def weightRow0LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 1053772478653105 else 1016736235092105
def weightRow0LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 1042856657322105 else 1069931917907105
def weightRow0LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow0LLRLRRLL i else weightRow0LLRLRRLR i
def weightRow0LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1053267874663105 else 1051055040072105
def weightRow0LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 1044140080940105 else 1054035686408105
def weightRow0LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow0LLRLRRRL i else weightRow0LLRLRRRR i
def weightRow0LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow0LLRLRRL i else weightRow0LLRLRRR i
def weightRow0LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow0LLRLRL i else weightRow0LLRLRR i
def weightRow0LLRL (i : ℕ) : ℕ := if i < 80 then weightRow0LLRLL i else weightRow0LLRLR i
def weightRow0LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 970141460646105 else 960717388786105
def weightRow0LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 897298326403105 else 918292993786105
def weightRow0LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow0LLRRLLLL i else weightRow0LLRRLLLR i
def weightRow0LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 884756928003105 else 876759939035105
def weightRow0LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 891013780121105 else 901283081023105
def weightRow0LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow0LLRRLLRL i else weightRow0LLRRLLRR i
def weightRow0LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow0LLRRLLL i else weightRow0LLRRLLR i
def weightRow0LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 906738085659105 else 895216333688105
def weightRow0LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 947368942192105 else 958828366869105
def weightRow0LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow0LLRRLRLL i else weightRow0LLRRLRLR i
def weightRow0LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1013296020611105 else 1003531460950105
def weightRow0LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 932497240533105 else 929757050009105
def weightRow0LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow0LLRRLRRL i else weightRow0LLRRLRRR i
def weightRow0LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow0LLRRLRL i else weightRow0LLRRLRR i
def weightRow0LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow0LLRRLL i else weightRow0LLRRLR i
def weightRow0LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1007811269475105 else 993220187949105
def weightRow0LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 926725370964105 else 915848188267105
def weightRow0LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow0LLRRRLLL i else weightRow0LLRRRLLR i
def weightRow0LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 1023748039084105 else 1014260710558105
def weightRow0LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 1006696771873105 else 1009841799683105
def weightRow0LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow0LLRRRLRL i else weightRow0LLRRRLRR i
def weightRow0LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow0LLRRRLL i else weightRow0LLRRRLR i
def weightRow0LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 950391864841105 else 952195435023105
def weightRow0LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 909212558616105 else 912055142510105
def weightRow0LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow0LLRRRRLL i else weightRow0LLRRRRLR i
def weightRow0LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 877002994735105 else 878639412426105
def weightRow0LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 911528215272105 else 908999315240105
def weightRow0LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow0LLRRRRRL i else weightRow0LLRRRRRR i
def weightRow0LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow0LLRRRRL i else weightRow0LLRRRRR i
def weightRow0LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow0LLRRRL i else weightRow0LLRRRR i
def weightRow0LLRR (i : ℕ) : ℕ := if i < 112 then weightRow0LLRRL i else weightRow0LLRRR i
def weightRow0LLR (i : ℕ) : ℕ := if i < 96 then weightRow0LLRL i else weightRow0LLRR i
def weightRow0LL (i : ℕ) : ℕ := if i < 64 then weightRow0LLL i else weightRow0LLR i
def weightRow0LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 843582641506105 else 844295306558105
def weightRow0LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 855532219189105 else 856205199852105
def weightRow0LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow0LRLLLLLL i else weightRow0LRLLLLLR i
def weightRow0LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 867906556120105 else 868604330168105
def weightRow0LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 879710972797105 else 880456257602105
def weightRow0LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow0LRLLLLRL i else weightRow0LRLLLLRR i
def weightRow0LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow0LRLLLLL i else weightRow0LRLLLLR i
def weightRow0LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 890817650348105 else 891587540932105
def weightRow0LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 900909130302105 else 901725805089105
def weightRow0LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow0LRLLLRLL i else weightRow0LRLLLRLR i
def weightRow0LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 910781500363105 else 911459159833105
def weightRow0LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 922055254782105 else 922553779700105
def weightRow0LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow0LRLLLRRL i else weightRow0LRLLLRRR i
def weightRow0LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow0LRLLLRL i else weightRow0LRLLLRR i
def weightRow0LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow0LRLLLL i else weightRow0LRLLLR i
def weightRow0LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 932009421050105 else 932270084009105
def weightRow0LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 942812968018105 else 943002768306105
def weightRow0LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow0LRLLRLLL i else weightRow0LRLLRLLR i
def weightRow0LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 952328913476105 else 952337127653105
def weightRow0LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 962375263956105 else 962534972300105
def weightRow0LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow0LRLLRLRL i else weightRow0LRLLRLRR i
def weightRow0LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow0LRLLRLL i else weightRow0LRLLRLR i
def weightRow0LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 973281723692105 else 973229329079105
def weightRow0LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 983977916032105 else 984057361319105
def weightRow0LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow0LRLLRRLL i else weightRow0LRLLRRLR i
def weightRow0LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 994937086835105 else 994861786420105
def weightRow0LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 1005125632677105 else 1005348390811105
def weightRow0LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow0LRLLRRRL i else weightRow0LRLLRRRR i
def weightRow0LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow0LRLLRRL i else weightRow0LRLLRRR i
def weightRow0LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow0LRLLRL i else weightRow0LRLLRR i
def weightRow0LRLL (i : ℕ) : ℕ := if i < 144 then weightRow0LRLLL i else weightRow0LRLLR i
def weightRow0LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 1014491260109105 else 1014535859286105
def weightRow0LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 1022188277154105 else 1022366218257105
def weightRow0LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow0LRLRLLLL i else weightRow0LRLRLLLR i
def weightRow0LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 1029671735761105 else 1029789284699105
def weightRow0LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 1036587952359105 else 1037108269501105
def weightRow0LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow0LRLRLLRL i else weightRow0LRLRLLRR i
def weightRow0LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow0LRLRLLL i else weightRow0LRLRLLR i
def weightRow0LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 1044041917570105 else 1043972444958105
def weightRow0LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 1050440235881105 else 1050803364864105
def weightRow0LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow0LRLRLRLL i else weightRow0LRLRLRLR i
def weightRow0LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 1056000632514105 else 1056232044326105
def weightRow0LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 1059811313690105 else 1060654655426105
def weightRow0LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow0LRLRLRRL i else weightRow0LRLRLRRR i
def weightRow0LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow0LRLRLRL i else weightRow0LRLRLRR i
def weightRow0LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow0LRLRLL i else weightRow0LRLRLR i
def weightRow0LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 1063604351287105 else 1064223936304105
def weightRow0LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 1066430871510105 else 1067271173925105
def weightRow0LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow0LRLRRLLL i else weightRow0LRLRRLLR i
def weightRow0LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 1069186390686105 else 1069540495410105
def weightRow0LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 1068855280605105 else 1069614617068105
def weightRow0LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow0LRLRRLRL i else weightRow0LRLRRLRR i
def weightRow0LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow0LRLRRLL i else weightRow0LRLRRLR i
def weightRow0LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 1068084155300105 else 1068057671973105
def weightRow0LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 1063521873133105 else 1063250298969105
def weightRow0LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow0LRLRRRLL i else weightRow0LRLRRRLR i
def weightRow0LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 1055989845941105 else 1055082634385105
def weightRow0LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1048283880609105 else 1048234707977105
def weightRow0LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow0LRLRRRRL i else weightRow0LRLRRRRR i
def weightRow0LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow0LRLRRRL i else weightRow0LRLRRRR i
def weightRow0LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow0LRLRRL i else weightRow0LRLRRR i
def weightRow0LRLR (i : ℕ) : ℕ := if i < 176 then weightRow0LRLRL i else weightRow0LRLRR i
def weightRow0LRL (i : ℕ) : ℕ := if i < 160 then weightRow0LRLL i else weightRow0LRLR i
def weightRow0LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1042268761086105 else 1041887224466105
def weightRow0LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1035491841332105 else 1035406271710105
def weightRow0LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow0LRRLLLLL i else weightRow0LRRLLLLR i
def weightRow0LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1027267862673105 else 1026258776864105
def weightRow0LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1016711611459105 else 1016273960428105
def weightRow0LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow0LRRLLLRL i else weightRow0LRRLLLRR i
def weightRow0LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow0LRRLLLL i else weightRow0LRRLLLR i
def weightRow0LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1008531350791105 else 1008297216615105
def weightRow0LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1002793780903105 else 1003330666956105
def weightRow0LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow0LRRLLRLL i else weightRow0LRRLLRLR i
def weightRow0LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 997985492497105 else 998126948895105
def weightRow0LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 994800039090105 else 995422009668105
def weightRow0LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow0LRRLLRRL i else weightRow0LRRLLRRR i
def weightRow0LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow0LRRLLRL i else weightRow0LRRLLRR i
def weightRow0LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow0LRRLLL i else weightRow0LRRLLR i
def weightRow0LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 991862692994105 else 992286021997105
def weightRow0LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 988982165697105 else 989638836542105
def weightRow0LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow0LRRLRLLL i else weightRow0LRRLRLLR i
def weightRow0LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 986500655387105 else 986542370841105
def weightRow0LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 984624594050105 else 984785938119105
def weightRow0LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow0LRRLRLRL i else weightRow0LRRLRLRR i
def weightRow0LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow0LRRLRLL i else weightRow0LRRLRLR i
def weightRow0LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 983799304558105 else 983509165756105
def weightRow0LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 982708173781105 else 982987825076105
def weightRow0LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow0LRRLRRLL i else weightRow0LRRLRRLR i
def weightRow0LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 981767288496105 else 981629407988105
def weightRow0LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 980650193470105 else 980543316194105
def weightRow0LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow0LRRLRRRL i else weightRow0LRRLRRRR i
def weightRow0LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow0LRRLRRL i else weightRow0LRRLRRR i
def weightRow0LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow0LRRLRL i else weightRow0LRRLRR i
def weightRow0LRRL (i : ℕ) : ℕ := if i < 208 then weightRow0LRRLL i else weightRow0LRRLR i
def weightRow0LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 979660533702105 else 979395617477105
def weightRow0LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 979810631425105 else 979691135068105
def weightRow0LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow0LRRRLLLL i else weightRow0LRRRLLLR i
def weightRow0LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 981098849456105 else 980653091091105
def weightRow0LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 982605621656105 else 982276018830105
def weightRow0LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow0LRRRLLRL i else weightRow0LRRRLLRR i
def weightRow0LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow0LRRRLLL i else weightRow0LRRRLLR i
def weightRow0LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 984034922543105 else 983542366790105
def weightRow0LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 985243428381105 else 984919355100105
def weightRow0LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow0LRRRLRLL i else weightRow0LRRRLRLR i
def weightRow0LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 985832942871105 else 985322832456105
def weightRow0LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 985404680647105 else 985045994467105
def weightRow0LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow0LRRRLRRL i else weightRow0LRRRLRRR i
def weightRow0LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow0LRRRLRL i else weightRow0LRRRLRR i
def weightRow0LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow0LRRRLL i else weightRow0LRRRLR i
def weightRow0LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 986231947011105 else 985903797778105
def weightRow0LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 985893662835105 else 985796676737105
def weightRow0LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow0LRRRRLLL i else weightRow0LRRRRLLR i
def weightRow0LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 986817302732105 else 986883732666105
def weightRow0LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 986242525240105 else 986455089145105
def weightRow0LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow0LRRRRLRL i else weightRow0LRRRRLRR i
def weightRow0LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow0LRRRRLL i else weightRow0LRRRRLR i
def weightRow0LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 985924544882105 else 986091831224105
def weightRow0LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 986480243276105 else 986623037711105
def weightRow0LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow0LRRRRRLL i else weightRow0LRRRRRLR i
def weightRow0LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 987687418810105 else 987791557289105
def weightRow0LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 989418216370105 else 989493065770105
def weightRow0LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow0LRRRRRRL i else weightRow0LRRRRRRR i
def weightRow0LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow0LRRRRRL i else weightRow0LRRRRRR i
def weightRow0LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow0LRRRRL i else weightRow0LRRRRR i
def weightRow0LRRR (i : ℕ) : ℕ := if i < 240 then weightRow0LRRRL i else weightRow0LRRRR i
def weightRow0LRR (i : ℕ) : ℕ := if i < 224 then weightRow0LRRL i else weightRow0LRRR i
def weightRow0LR (i : ℕ) : ℕ := if i < 192 then weightRow0LRL i else weightRow0LRR i
def weightRow0L (i : ℕ) : ℕ := if i < 128 then weightRow0LL i else weightRow0LR i
def weightRow0RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 990636013169105 else 990755344277105
def weightRow0RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 992933810137105 else 993043936559105
def weightRow0RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow0RLLLLLLL i else weightRow0RLLLLLLR i
def weightRow0RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 995081001238105 else 995181965571105
def weightRow0RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 997068287349105 else 997159880730105
def weightRow0RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow0RLLLLLRL i else weightRow0RLLLLLRR i
def weightRow0RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow0RLLLLLL i else weightRow0RLLLLLR i
def weightRow0RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 998902271623105 else 998983456752105
def weightRow0RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 1000591403453105 else 1000661804275105
def weightRow0RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow0RLLLLRLL i else weightRow0RLLLLRLR i
def weightRow0RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 1002149263800105 else 1002207986574105
def weightRow0RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 1003577177103105 else 1003626115557105
def weightRow0RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow0RLLLLRRL i else weightRow0RLLLLRRR i
def weightRow0RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow0RLLLLRL i else weightRow0RLLLLRR i
def weightRow0RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow0RLLLLL i else weightRow0RLLLLR i
def weightRow0RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 1004851289259105 else 1004893157261105
def weightRow0RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 1005989724352105 else 1006028032413105
def weightRow0RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow0RLLLRLLL i else weightRow0RLLLRLLR i
def weightRow0RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 1006977194307105 else 1007013108088105
def weightRow0RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 1007831261480105 else 1007867610031105
def weightRow0RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow0RLLLRLRL i else weightRow0RLLLRLRR i
def weightRow0RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow0RLLLRLL i else weightRow0RLLLRLR i
def weightRow0RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 1008541674684105 else 1008576109764105
def weightRow0RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 1009092735740105 else 1009128569918105
def weightRow0RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow0RLLLRRLL i else weightRow0RLLLRRLR i
def weightRow0RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 1009485221500105 else 1009520388545105
def weightRow0RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 1009712594565105 else 1009749419476105
def weightRow0RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow0RLLLRRRL i else weightRow0RLLLRRRR i
def weightRow0RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow0RLLLRRL i else weightRow0RLLLRRR i
def weightRow0RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow0RLLLRL i else weightRow0RLLLRR i
def weightRow0RLLL (i : ℕ) : ℕ := if i < 272 then weightRow0RLLLL i else weightRow0RLLLR i
def weightRow0RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 1009784201554105 else 1009818075081105
def weightRow0RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 1009710506678105 else 1009744300110105
def weightRow0RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow0RLLRLLLL i else weightRow0RLLRLLLR i
def weightRow0RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 1009515271287105 else 1009546814192105
def weightRow0RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1009199902819105 else 1009230155559105
def weightRow0RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow0RLLRLLRL i else weightRow0RLLRLLRR i
def weightRow0RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow0RLLRLLL i else weightRow0RLLRLLR i
def weightRow0RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1008771323578105 else 1008794044348105
def weightRow0RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1008219562409105 else 1008243738400105
def weightRow0RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow0RLLRLRLL i else weightRow0RLLRLRLR i
def weightRow0RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1007559162525105 else 1007578039868105
def weightRow0RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1006801491822105 else 1006816999399105
def weightRow0RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow0RLLRLRRL i else weightRow0RLLRLRRR i
def weightRow0RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow0RLLRLRL i else weightRow0RLLRLRR i
def weightRow0RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow0RLLRLL i else weightRow0RLLRLR i
def weightRow0RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1005972183946105 else 1005974988098105
def weightRow0RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1005070507471105 else 1005063852899105
def weightRow0RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow0RLLRRLLL i else weightRow0RLLRRLLR i
def weightRow0RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1004110569503105 else 1004090671126105
def weightRow0RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1003092662573105 else 1003066924425105
def weightRow0RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow0RLLRRLRL i else weightRow0RLLRRLRR i
def weightRow0RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow0RLLRRLL i else weightRow0RLLRRLR i
def weightRow0RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1002063786108105 else 1002025783863105
def weightRow0RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1001031005025105 else 1000992729520105
def weightRow0RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow0RLLRRRLL i else weightRow0RLLRRRLR i
def weightRow0RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1000053074962105 else 1000018607560105
def weightRow0RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 999177600672105 else 999156702288105
def weightRow0RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow0RLLRRRRL i else weightRow0RLLRRRRR i
def weightRow0RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow0RLLRRRL i else weightRow0RLLRRRR i
def weightRow0RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow0RLLRRL i else weightRow0RLLRRR i
def weightRow0RLLR (i : ℕ) : ℕ := if i < 304 then weightRow0RLLRL i else weightRow0RLLRR i
def weightRow0RLL (i : ℕ) : ℕ := if i < 288 then weightRow0RLLL i else weightRow0RLLR i
def weightRow0RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 998408632649105 else 998388229364105
def weightRow0RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 997721705450105 else 997706792786105
def weightRow0RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow0RLRLLLLL i else weightRow0RLRLLLLR i
def weightRow0RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 997130370578105 else 997116491478105
def weightRow0RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 996658504247105 else 996660205243105
def weightRow0RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow0RLRLLLRL i else weightRow0RLRLLLRR i
def weightRow0RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow0RLRLLLL i else weightRow0RLRLLLR i
def weightRow0RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 996344182458105 else 996352803899105
def weightRow0RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 996152714928105 else 996165088977105
def weightRow0RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow0RLRLLRLL i else weightRow0RLRLLRLR i
def weightRow0RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 996048200887105 else 996052579924105
def weightRow0RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 996017981667105 else 996020218272105
def weightRow0RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow0RLRLLRRL i else weightRow0RLRLLRRR i
def weightRow0RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow0RLRLLRL i else weightRow0RLRLLRR i
def weightRow0RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow0RLRLLL i else weightRow0RLRLLR i
def weightRow0RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 996037466398105 else 996029944883105
def weightRow0RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 996103209190105 else 996088883782105
def weightRow0RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow0RLRLRLLL i else weightRow0RLRLRLLR i
def weightRow0RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 996214955112105 else 996190251557105
def weightRow0RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 996367184504105 else 996341536164105
def weightRow0RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow0RLRLRLRL i else weightRow0RLRLRLRR i
def weightRow0RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow0RLRLRLL i else weightRow0RLRLRLR i
def weightRow0RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 996551103042105 else 996522505563105
def weightRow0RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 996751202431105 else 996726521638105
def weightRow0RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow0RLRLRRLL i else weightRow0RLRLRRLR i
def weightRow0RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 996971676143105 else 996942328290105
def weightRow0RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 997210541085105 else 997182835671105
def weightRow0RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow0RLRLRRRL i else weightRow0RLRLRRRR i
def weightRow0RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow0RLRLRRL i else weightRow0RLRLRRR i
def weightRow0RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow0RLRLRL i else weightRow0RLRLRR i
def weightRow0RLRL (i : ℕ) : ℕ := if i < 336 then weightRow0RLRLL i else weightRow0RLRLR i
def weightRow0RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 997470258785105 else 997443879131105
def weightRow0RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 997749365921105 else 997726700212105
def weightRow0RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow0RLRRLLLL i else weightRow0RLRRLLLR i
def weightRow0RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 998030513003105 else 998009511251105
def weightRow0RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 998296385677105 else 998282035249105
def weightRow0RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow0RLRRLLRL i else weightRow0RLRRLLRR i
def weightRow0RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow0RLRRLLL i else weightRow0RLRRLLR i
def weightRow0RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 998543275596105 else 998533891644105
def weightRow0RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 998771883178105 else 998769813093105
def weightRow0RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow0RLRRLRLL i else weightRow0RLRRLRLR i
def weightRow0RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 998984871153105 else 998987843081105
def weightRow0RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 999191524217105 else 999202495016105
def weightRow0RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow0RLRRLRRL i else weightRow0RLRRLRRR i
def weightRow0RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow0RLRRLRL i else weightRow0RLRRLRR i
def weightRow0RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow0RLRRLL i else weightRow0RLRRLR i
def weightRow0RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 999408113382105 else 999424831869105
def weightRow0RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 999615595126105 else 999637675008105
def weightRow0RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow0RLRRRLLL i else weightRow0RLRRRLLR i
def weightRow0RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 999831624886105 else 999855394251105
def weightRow0RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 1000037096535105 else 1000060194283105
def weightRow0RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow0RLRRRLRL i else weightRow0RLRRRLRR i
def weightRow0RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow0RLRRRLL i else weightRow0RLRRRLR i
def weightRow0RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 1000255069724105 else 1000275298626105
def weightRow0RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 1000480982820105 else 1000498884254105
def weightRow0RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow0RLRRRRLL i else weightRow0RLRRRRLR i
def weightRow0RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 1000702076762105 else 1000718126382105
def weightRow0RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 1000906836352105 else 1000921544063105
def weightRow0RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow0RLRRRRRL i else weightRow0RLRRRRRR i
def weightRow0RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow0RLRRRRL i else weightRow0RLRRRRR i
def weightRow0RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow0RLRRRL i else weightRow0RLRRRR i
def weightRow0RLRR (i : ℕ) : ℕ := if i < 368 then weightRow0RLRRL i else weightRow0RLRRR i
def weightRow0RLR (i : ℕ) : ℕ := if i < 352 then weightRow0RLRL i else weightRow0RLRR i
def weightRow0RL (i : ℕ) : ℕ := if i < 320 then weightRow0RLL i else weightRow0RLR i
def weightRow0RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 1001091565720105 else 1001105427740105
def weightRow0RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 1001260881319105 else 1001273237728105
def weightRow0RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow0RRLLLLLL i else weightRow0RRLLLLLR i
def weightRow0RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 1001393160450105 else 1001403488231105
def weightRow0RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 1001495239775105 else 1001504520170105
def weightRow0RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow0RRLLLLRL i else weightRow0RRLLLLRR i
def weightRow0RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow0RRLLLLL i else weightRow0RRLLLLR i
def weightRow0RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 1001564059543105 else 1001571436109105
def weightRow0RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 1001612173489105 else 1001619239264105
def weightRow0RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow0RRLLLRLL i else weightRow0RRLLLRLR i
def weightRow0RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 1001628314274105 else 1001633531906105
def weightRow0RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 1001620013121105 else 1001624412847105
def weightRow0RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow0RRLLLRRL i else weightRow0RRLLLRRR i
def weightRow0RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow0RRLLLRL i else weightRow0RRLLLRR i
def weightRow0RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow0RRLLLL i else weightRow0RRLLLR i
def weightRow0RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 1001592158423105 else 1001595400429105
def weightRow0RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 1001539532136105 else 1001541848721105
def weightRow0RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow0RRLLRLLL i else weightRow0RRLLRLLR i
def weightRow0RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1001474727948105 else 1001476712377105
def weightRow0RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1001380806356105 else 1001381727639105
def weightRow0RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow0RRLLRLRL i else weightRow0RRLLRLRR i
def weightRow0RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow0RRLLRLL i else weightRow0RRLLRLR i
def weightRow0RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1001278290088105 else 1001280838452105
def weightRow0RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1001164978026105 else 1001165808818105
def weightRow0RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow0RRLLRRLL i else weightRow0RRLLRRLR i
def weightRow0RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1001039529222105 else 1001040191044105
def weightRow0RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000904136515105 else 1000903404248105
def weightRow0RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow0RRLLRRRL i else weightRow0RRLLRRRR i
def weightRow0RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow0RRLLRRL i else weightRow0RRLLRRR i
def weightRow0RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow0RRLLRL i else weightRow0RRLLRR i
def weightRow0RRLL (i : ℕ) : ℕ := if i < 400 then weightRow0RRLLL i else weightRow0RRLLR i
def weightRow0RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000757023373105 else 1000756528226105
def weightRow0RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000608524179105 else 1000609593488105
def weightRow0RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow0RRLRLLLL i else weightRow0RRLRLLLR i
def weightRow0RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000454806060105 else 1000454277526105
def weightRow0RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000304192001105 else 1000303539613105
def weightRow0RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow0RRLRLLRL i else weightRow0RRLRLLRR i
def weightRow0RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow0RRLRLLL i else weightRow0RRLRLLR i
def weightRow0RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000156394834105 else 1000156006640105
def weightRow0RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000015138903105 else 1000012546085105
def weightRow0RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow0RRLRLRLL i else weightRow0RRLRLRLR i
def weightRow0RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 999881794056105 else 999878988680105
def weightRow0RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 999751297009105 else 999746101805105
def weightRow0RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow0RRLRLRRL i else weightRow0RRLRLRRR i
def weightRow0RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow0RRLRLRL i else weightRow0RRLRLRR i
def weightRow0RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow0RRLRLL i else weightRow0RRLRLR i
def weightRow0RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 999629314751105 else 999628828869105
def weightRow0RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 999515158927105 else 999513422567105
def weightRow0RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow0RRLRRLLL i else weightRow0RRLRRLLR i
def weightRow0RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 999425018090105 else 999423020515105
def weightRow0RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 999355240256105 else 999347557620105
def weightRow0RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow0RRLRRLRL i else weightRow0RRLRRLRR i
def weightRow0RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow0RRLRRLL i else weightRow0RRLRRLR i
def weightRow0RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 999278996602105 else 999273528493105
def weightRow0RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 999229840726105 else 999224149147105
def weightRow0RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow0RRLRRRLL i else weightRow0RRLRRRLR i
def weightRow0RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 999179180278105 else 999180028430105
def weightRow0RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 999164334053105 else 999156252517105
def weightRow0RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow0RRLRRRRL i else weightRow0RRLRRRRR i
def weightRow0RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow0RRLRRRL i else weightRow0RRLRRRR i
def weightRow0RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow0RRLRRL i else weightRow0RRLRRR i
def weightRow0RRLR (i : ℕ) : ℕ := if i < 432 then weightRow0RRLRL i else weightRow0RRLRR i
def weightRow0RRL (i : ℕ) : ℕ := if i < 416 then weightRow0RRLL i else weightRow0RRLR i
def weightRow0RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 999154884014105 else 999152535038105
def weightRow0RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 999162391071105 else 999156882804105
def weightRow0RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow0RRRLLLLL i else weightRow0RRRLLLLR i
def weightRow0RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 999209121787105 else 999210438962105
def weightRow0RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 999253778144105 else 999250373624105
def weightRow0RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow0RRRLLLRL i else weightRow0RRRLLLRR i
def weightRow0RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow0RRRLLLL i else weightRow0RRRLLLR i
def weightRow0RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 999293701601105 else 999293042808105
def weightRow0RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 999336032793105 else 999336567932105
def weightRow0RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow0RRRLLRLL i else weightRow0RRRLLRLR i
def weightRow0RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 999410313984105 else 999418194900105
def weightRow0RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 999513851761105 else 999517616806105
def weightRow0RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow0RRRLLRRL i else weightRow0RRRLLRRR i
def weightRow0RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow0RRRLLRL i else weightRow0RRRLLRR i
def weightRow0RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow0RRRLLL i else weightRow0RRRLLR i
def weightRow0RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 999596156823105 else 999591818762105
def weightRow0RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 999655204674105 else 999651130390105
def weightRow0RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow0RRRLRLLL i else weightRow0RRRLRLLR i
def weightRow0RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999710400819105 else 999712937070105
def weightRow0RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999764367908105 else 999766783778105
def weightRow0RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow0RRRLRLRL i else weightRow0RRRLRLRR i
def weightRow0RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow0RRRLRLL i else weightRow0RRRLRLR i
def weightRow0RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999817729389105 else 999819579184105
def weightRow0RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999894769627105 else 999889701063105
def weightRow0RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow0RRRLRRLL i else weightRow0RRRLRRLR i
def weightRow0RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999959134222105 else 999967565410105
def weightRow0RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 1000022342868105 else 1000023016224105
def weightRow0RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow0RRRLRRRL i else weightRow0RRRLRRRR i
def weightRow0RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow0RRRLRRL i else weightRow0RRRLRRR i
def weightRow0RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow0RRRLRL i else weightRow0RRRLRR i
def weightRow0RRRL (i : ℕ) : ℕ := if i < 464 then weightRow0RRRLL i else weightRow0RRRLR i
def weightRow0RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 1000046065232105 else 1000054029131105
def weightRow0RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 1000082861537105 else 1000080138057105
def weightRow0RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow0RRRRLLLL i else weightRow0RRRRLLLR i
def weightRow0RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 1000123309987105 else 1000133120297105
def weightRow0RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 1000185346527105 else 1000192347345105
def weightRow0RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow0RRRRLLRL i else weightRow0RRRRLLRR i
def weightRow0RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow0RRRRLLL i else weightRow0RRRRLLR i
def weightRow0RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 1000246077516105 else 1000248930169105
def weightRow0RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 1000282260235105 else 1000276031799105
def weightRow0RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow0RRRRLRLL i else weightRow0RRRRLRLR i
def weightRow0RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 1000291200248105 else 1000291299619105
def weightRow0RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 1000279653713105 else 1000279812238105
def weightRow0RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow0RRRRLRRL i else weightRow0RRRRLRRR i
def weightRow0RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow0RRRRLRL i else weightRow0RRRRLRR i
def weightRow0RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow0RRRRLL i else weightRow0RRRRLR i
def weightRow0RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 1000300112732105 else 1000305482092105
def weightRow0RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 1000344124655105 else 1000342581987105
def weightRow0RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow0RRRRRLLL i else weightRow0RRRRRLLR i
def weightRow0RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 1000355522266105 else 1000355799010105
def weightRow0RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 1000397434927105 else 1000401560908105
def weightRow0RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow0RRRRRLRL i else weightRow0RRRRRLRR i
def weightRow0RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow0RRRRRLL i else weightRow0RRRRRLR i
def weightRow0RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 1000426396906105 else 1000435446591105
def weightRow0RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 1000406293744105 else 1000404475700105
def weightRow0RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow0RRRRRRLL i else weightRow0RRRRRRLR i
def weightRow0RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 1000429062867105 else 1000437049389105
def weightRow0RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 1000366230972105 else 1000373738813105
def weightRow0RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow0RRRRRRRL i else weightRow0RRRRRRRR i
def weightRow0RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow0RRRRRRL i else weightRow0RRRRRRR i
def weightRow0RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow0RRRRRL i else weightRow0RRRRRR i
def weightRow0RRRR (i : ℕ) : ℕ := if i < 496 then weightRow0RRRRL i else weightRow0RRRRR i
def weightRow0RRR (i : ℕ) : ℕ := if i < 480 then weightRow0RRRL i else weightRow0RRRR i
def weightRow0RR (i : ℕ) : ℕ := if i < 448 then weightRow0RRL i else weightRow0RRR i
def weightRow0R (i : ℕ) : ℕ := if i < 384 then weightRow0RL i else weightRow0RR i
def weightRow0 (i : ℕ) : ℕ := if i < 256 then weightRow0L i else weightRow0R i
def weightRow1LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 263523585097105 else 254173431213105
def weightRow1LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 601801144679105 else 610067890210105
def weightRow1LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow1LLLLLLLL i else weightRow1LLLLLLLR i
def weightRow1LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 686770375181105 else 659103106290105
def weightRow1LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 867757361007105 else 881474402383105
def weightRow1LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow1LLLLLLRL i else weightRow1LLLLLLRR i
def weightRow1LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow1LLLLLLL i else weightRow1LLLLLLR i
def weightRow1LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 437329500169105 else 433342718829105
def weightRow1LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 685732668310105 else 720582447344105
def weightRow1LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow1LLLLLRLL i else weightRow1LLLLLRLR i
def weightRow1LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 569570853283105 else 504740025382105
def weightRow1LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 372364198651105 else 395866172703105
def weightRow1LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow1LLLLLRRL i else weightRow1LLLLLRRR i
def weightRow1LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow1LLLLLRL i else weightRow1LLLLLRR i
def weightRow1LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow1LLLLLL i else weightRow1LLLLLR i
def weightRow1LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 550879954384105 else 528373542589105
def weightRow1LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 593669617809105 else 599928562851105
def weightRow1LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow1LLLLRLLL i else weightRow1LLLLRLLR i
def weightRow1LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 475609703370105 else 454207559149105
def weightRow1LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 432367247574105 else 432838108494105
def weightRow1LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow1LLLLRLRL i else weightRow1LLLLRLRR i
def weightRow1LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow1LLLLRLL i else weightRow1LLLLRLR i
def weightRow1LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 593706369257105 else 570497593732105
def weightRow1LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 730688684318105 else 666122090536105
def weightRow1LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow1LLLLRRLL i else weightRow1LLLLRRLR i
def weightRow1LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 811162374631105 else 859873595042105
def weightRow1LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 831895088769105 else 760714189268105
def weightRow1LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow1LLLLRRRL i else weightRow1LLLLRRRR i
def weightRow1LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow1LLLLRRL i else weightRow1LLLLRRR i
def weightRow1LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow1LLLLRL i else weightRow1LLLLRR i
def weightRow1LLLL (i : ℕ) : ℕ := if i < 16 then weightRow1LLLLL i else weightRow1LLLLR i
def weightRow1LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 812408847048105 else 814087375307105
def weightRow1LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 780985325994105 else 782249992805105
def weightRow1LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow1LLLRLLLL i else weightRow1LLLRLLLR i
def weightRow1LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 630042765022105 else 663969556537105
def weightRow1LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 546757241582105 else 528671066160105
def weightRow1LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow1LLLRLLRL i else weightRow1LLLRLLRR i
def weightRow1LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow1LLLRLLL i else weightRow1LLLRLLR i
def weightRow1LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 681894160134105 else 685124986080105
def weightRow1LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 704953911037105 else 703618733410105
def weightRow1LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow1LLLRLRLL i else weightRow1LLLRLRLR i
def weightRow1LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 586061200767105 else 582700772107105
def weightRow1LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 560661574424105 else 567878346333105
def weightRow1LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow1LLLRLRRL i else weightRow1LLLRLRRR i
def weightRow1LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow1LLLRLRL i else weightRow1LLLRLRR i
def weightRow1LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow1LLLRLL i else weightRow1LLLRLR i
def weightRow1LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 658213501364105 else 676363448089105
def weightRow1LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 506386209036105 else 526147429476105
def weightRow1LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow1LLLRRLLL i else weightRow1LLLRRLLR i
def weightRow1LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 867306647036105 else 897364609503105
def weightRow1LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 897247565691105 else 861796775247105
def weightRow1LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow1LLLRRLRL i else weightRow1LLLRRLRR i
def weightRow1LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow1LLLRRLL i else weightRow1LLLRRLR i
def weightRow1LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 709217154538105 else 719921605063105
def weightRow1LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 872599714945105 else 855779017222105
def weightRow1LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow1LLLRRRLL i else weightRow1LLLRRRLR i
def weightRow1LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 725218239004105 else 712952009998105
def weightRow1LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 987618783030105 else 933026241926105
def weightRow1LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow1LLLRRRRL i else weightRow1LLLRRRRR i
def weightRow1LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow1LLLRRRL i else weightRow1LLLRRRR i
def weightRow1LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow1LLLRRL i else weightRow1LLLRRR i
def weightRow1LLLR (i : ℕ) : ℕ := if i < 48 then weightRow1LLLRL i else weightRow1LLLRR i
def weightRow1LLL (i : ℕ) : ℕ := if i < 32 then weightRow1LLLL i else weightRow1LLLR i
def weightRow1LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 950554069700105 else 1000102697508105
def weightRow1LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 756472433628105 else 764660924823105
def weightRow1LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow1LLRLLLLL i else weightRow1LLRLLLLR i
def weightRow1LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 924491200247105 else 937623844592105
def weightRow1LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 814328786632105 else 799975790622105
def weightRow1LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow1LLRLLLRL i else weightRow1LLRLLLRR i
def weightRow1LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow1LLRLLLL i else weightRow1LLRLLLR i
def weightRow1LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 982394975782105 else 1014525581300105
def weightRow1LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 1047336474281105 else 1013986084568105
def weightRow1LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow1LLRLLRLL i else weightRow1LLRLLRLR i
def weightRow1LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 700706826008105 else 676825056663105
def weightRow1LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 872436141566105 else 849514669002105
def weightRow1LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow1LLRLLRRL i else weightRow1LLRLLRRR i
def weightRow1LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow1LLRLLRL i else weightRow1LLRLLRR i
def weightRow1LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow1LLRLLL i else weightRow1LLRLLR i
def weightRow1LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 786458805194105 else 773996313625105
def weightRow1LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 822675923769105 else 820648543186105
def weightRow1LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow1LLRLRLLL i else weightRow1LLRLRLLR i
def weightRow1LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 967439926488105 else 963378212510105
def weightRow1LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 974769535435105 else 966025917490105
def weightRow1LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow1LLRLRLRL i else weightRow1LLRLRLRR i
def weightRow1LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow1LLRLRLL i else weightRow1LLRLRLR i
def weightRow1LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 841808767250105 else 854527527155105
def weightRow1LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 1000635484406105 else 961010769533105
def weightRow1LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow1LLRLRRLL i else weightRow1LLRLRRLR i
def weightRow1LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1146776038867105 else 1139171017091105
def weightRow1LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 1209249239320105 else 1201093500026105
def weightRow1LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow1LLRLRRRL i else weightRow1LLRLRRRR i
def weightRow1LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow1LLRLRRL i else weightRow1LLRLRRR i
def weightRow1LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow1LLRLRL i else weightRow1LLRLRR i
def weightRow1LLRL (i : ℕ) : ℕ := if i < 80 then weightRow1LLRLL i else weightRow1LLRLR i
def weightRow1LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 1186655839463105 else 1252344915034105
def weightRow1LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 1317798544321105 else 1263853311908105
def weightRow1LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow1LLRRLLLL i else weightRow1LLRRLLLR i
def weightRow1LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1155043546334105 else 1214549707615105
def weightRow1LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 1086386019923105 else 1105818029901105
def weightRow1LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow1LLRRLLRL i else weightRow1LLRRLLRR i
def weightRow1LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow1LLRRLLL i else weightRow1LLRRLLR i
def weightRow1LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 972465527318105 else 968510172014105
def weightRow1LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1016122841517105 else 1034320545280105
def weightRow1LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow1LLRRLRLL i else weightRow1LLRRLRLR i
def weightRow1LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1187088742469105 else 1177818757909105
def weightRow1LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 1142346448624105 else 1162038379316105
def weightRow1LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow1LLRRLRRL i else weightRow1LLRRLRRR i
def weightRow1LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow1LLRRLRL i else weightRow1LLRRLRR i
def weightRow1LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow1LLRRLL i else weightRow1LLRRLR i
def weightRow1LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1033869025453105 else 1007499557090105
def weightRow1LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 1166791781834105 else 1229350168486105
def weightRow1LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow1LLRRRLLL i else weightRow1LLRRRLLR i
def weightRow1LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 1412120853276105 else 1375439433133105
def weightRow1LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 1153724265661105 else 1155355901086105
def weightRow1LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow1LLRRRLRL i else weightRow1LLRRRLRR i
def weightRow1LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow1LLRRRLL i else weightRow1LLRRRLR i
def weightRow1LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 1633649829160105 else 1617393599561105
def weightRow1LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 1447102962375105 else 1472409612183105
def weightRow1LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow1LLRRRRLL i else weightRow1LLRRRRLR i
def weightRow1LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 1430212745928105 else 1419853363936105
def weightRow1LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 1100637776637105 else 1107885151654105
def weightRow1LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow1LLRRRRRL i else weightRow1LLRRRRRR i
def weightRow1LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow1LLRRRRL i else weightRow1LLRRRRR i
def weightRow1LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow1LLRRRL i else weightRow1LLRRRR i
def weightRow1LLRR (i : ℕ) : ℕ := if i < 112 then weightRow1LLRRL i else weightRow1LLRRR i
def weightRow1LLR (i : ℕ) : ℕ := if i < 96 then weightRow1LLRL i else weightRow1LLRR i
def weightRow1LL (i : ℕ) : ℕ := if i < 64 then weightRow1LLL i else weightRow1LLR i
def weightRow1LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 863654683068105 else 861666590951105
def weightRow1LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 873020465456105 else 871148058154105
def weightRow1LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow1LRLLLLLL i else weightRow1LRLLLLLR i
def weightRow1LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 877258773887105 else 875227272348105
def weightRow1LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 880243248865105 else 878568434284105
def weightRow1LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow1LRLLLLRL i else weightRow1LRLLLLRR i
def weightRow1LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow1LRLLLLL i else weightRow1LRLLLLR i
def weightRow1LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 880429026860105 else 878565179349105
def weightRow1LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 887356740861105 else 885508160504105
def weightRow1LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow1LRLLLRLL i else weightRow1LRLLLRLR i
def weightRow1LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 890515159519105 else 888086465884105
def weightRow1LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 895530610498105 else 894089560839105
def weightRow1LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow1LRLLLRRL i else weightRow1LRLLLRRR i
def weightRow1LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow1LRLLLRL i else weightRow1LRLLLRR i
def weightRow1LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow1LRLLLL i else weightRow1LRLLLR i
def weightRow1LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 903699379948105 else 901864117246105
def weightRow1LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 909212615484105 else 907692787015105
def weightRow1LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow1LRLLRLLL i else weightRow1LRLLRLLR i
def weightRow1LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 914146639817105 else 912507690969105
def weightRow1LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 920998422333105 else 919676774000105
def weightRow1LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow1LRLLRLRL i else weightRow1LRLLRLRR i
def weightRow1LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow1LRLLRLL i else weightRow1LRLLRLR i
def weightRow1LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 928626865171105 else 927284120948105
def weightRow1LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 933857054949105 else 932851191396105
def weightRow1LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow1LRLLRRLL i else weightRow1LRLLRRLR i
def weightRow1LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 937037581613105 else 937008154716105
def weightRow1LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 938993199373105 else 938220618432105
def weightRow1LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow1LRLLRRRL i else weightRow1LRLLRRRR i
def weightRow1LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow1LRLLRRL i else weightRow1LRLLRRR i
def weightRow1LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow1LRLLRL i else weightRow1LRLLRR i
def weightRow1LRLL (i : ℕ) : ℕ := if i < 144 then weightRow1LRLLL i else weightRow1LRLLR i
def weightRow1LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 940672394196105 else 940988185603105
def weightRow1LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 942682359950105 else 942969656520105
def weightRow1LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow1LRLRLLLL i else weightRow1LRLRLLLR i
def weightRow1LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 945212462481105 else 945485436079105
def weightRow1LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 950132827244105 else 949895178362105
def weightRow1LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow1LRLRLLRL i else weightRow1LRLRLLRR i
def weightRow1LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow1LRLRLLL i else weightRow1LRLRLLR i
def weightRow1LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 956431869594105 else 956473505435105
def weightRow1LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 960727024359105 else 960701856036105
def weightRow1LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow1LRLRLRLL i else weightRow1LRLRLRLR i
def weightRow1LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 964722342876105 else 964726845669105
def weightRow1LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 970637824344105 else 970703377092105
def weightRow1LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow1LRLRLRRL i else weightRow1LRLRLRRR i
def weightRow1LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow1LRLRLRL i else weightRow1LRLRLRR i
def weightRow1LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow1LRLRLL i else weightRow1LRLRLR i
def weightRow1LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 977045201108105 else 976984336018105
def weightRow1LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 982024168316105 else 981697589562105
def weightRow1LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow1LRLRRLLL i else weightRow1LRLRRLLR i
def weightRow1LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 989455845893105 else 988795683931105
def weightRow1LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 991361221803105 else 990221809015105
def weightRow1LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow1LRLRRLRL i else weightRow1LRLRRLRR i
def weightRow1LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow1LRLRRLL i else weightRow1LRLRRLR i
def weightRow1LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 992832429369105 else 992245756129105
def weightRow1LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 997268662170105 else 996485532717105
def weightRow1LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow1LRLRRRLL i else weightRow1LRLRRRLR i
def weightRow1LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 999205544930105 else 998704459358105
def weightRow1LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1003485739175105 else 1003145893200105
def weightRow1LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow1LRLRRRRL i else weightRow1LRLRRRRR i
def weightRow1LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow1LRLRRRL i else weightRow1LRLRRRR i
def weightRow1LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow1LRLRRL i else weightRow1LRLRRR i
def weightRow1LRLR (i : ℕ) : ℕ := if i < 176 then weightRow1LRLRL i else weightRow1LRLRR i
def weightRow1LRL (i : ℕ) : ℕ := if i < 160 then weightRow1LRLL i else weightRow1LRLR i
def weightRow1LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1003741087806105 else 1004237567502105
def weightRow1LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1004574306559105 else 1004319563602105
def weightRow1LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow1LRRLLLLL i else weightRow1LRRLLLLR i
def weightRow1LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1008448582239105 else 1008051477972105
def weightRow1LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1009752999094105 else 1009165523897105
def weightRow1LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow1LRRLLLRL i else weightRow1LRRLLLRR i
def weightRow1LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow1LRRLLLL i else weightRow1LRRLLLR i
def weightRow1LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1012809248699105 else 1012422353777105
def weightRow1LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1013286479353105 else 1012371836087105
def weightRow1LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow1LRRLLRLL i else weightRow1LRRLLRLR i
def weightRow1LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1012750032716105 else 1012382481118105
def weightRow1LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1017632533120105 else 1017608151103105
def weightRow1LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow1LRRLLRRL i else weightRow1LRRLLRRR i
def weightRow1LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow1LRRLLRL i else weightRow1LRRLLRR i
def weightRow1LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow1LRRLLL i else weightRow1LRRLLR i
def weightRow1LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1019906873983105 else 1020238144237105
def weightRow1LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1023545604463105 else 1024090980124105
def weightRow1LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow1LRRLRLLL i else weightRow1LRRLRLLR i
def weightRow1LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1026681604192105 else 1027260828163105
def weightRow1LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1027610622656105 else 1028251351511105
def weightRow1LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow1LRRLRLRL i else weightRow1LRRLRLRR i
def weightRow1LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow1LRRLRLL i else weightRow1LRRLRLR i
def weightRow1LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1028437241104105 else 1029235438427105
def weightRow1LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1031342726238105 else 1031966175550105
def weightRow1LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow1LRRLRRLL i else weightRow1LRRLRRLR i
def weightRow1LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1031827476878105 else 1033066720620105
def weightRow1LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1030031288523105 else 1031404292689105
def weightRow1LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow1LRRLRRRL i else weightRow1LRRLRRRR i
def weightRow1LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow1LRRLRRL i else weightRow1LRRLRRR i
def weightRow1LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow1LRRLRL i else weightRow1LRRLRR i
def weightRow1LRRL (i : ℕ) : ℕ := if i < 208 then weightRow1LRRLL i else weightRow1LRRLR i
def weightRow1LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 1027232063118105 else 1028750093713105
def weightRow1LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 1024727120906105 else 1025253331630105
def weightRow1LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow1LRRRLLLL i else weightRow1LRRRLLLR i
def weightRow1LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 1020161970539105 else 1021528498336105
def weightRow1LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 1018056589861105 else 1018519680535105
def weightRow1LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow1LRRRLLRL i else weightRow1LRRRLLRR i
def weightRow1LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow1LRRRLLL i else weightRow1LRRRLLR i
def weightRow1LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 1016992257328105 else 1017160709330105
def weightRow1LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 1017681308824105 else 1017927969243105
def weightRow1LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow1LRRRLRLL i else weightRow1LRRRLRLR i
def weightRow1LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 1017709883732105 else 1017657513248105
def weightRow1LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 1015066638102105 else 1015148555648105
def weightRow1LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow1LRRRLRRL i else weightRow1LRRRLRRR i
def weightRow1LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow1LRRRLRL i else weightRow1LRRRLRR i
def weightRow1LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow1LRRRLL i else weightRow1LRRRLR i
def weightRow1LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 1013067998043105 else 1012866808679105
def weightRow1LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 1012745215785105 else 1012949095613105
def weightRow1LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow1LRRRRLLL i else weightRow1LRRRRLLR i
def weightRow1LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 1010336325540105 else 1009554445186105
def weightRow1LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 1004054898983105 else 1003867476243105
def weightRow1LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow1LRRRRLRL i else weightRow1LRRRRLRR i
def weightRow1LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow1LRRRRLL i else weightRow1LRRRRLR i
def weightRow1LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 1001714617955105 else 1001465252153105
def weightRow1LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 991842497721105 else 991850272502105
def weightRow1LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow1LRRRRRLL i else weightRow1LRRRRRLR i
def weightRow1LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 984733084231105 else 984334594760105
def weightRow1LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 977780221805105 else 977540554426105
def weightRow1LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow1LRRRRRRL i else weightRow1LRRRRRRR i
def weightRow1LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow1LRRRRRL i else weightRow1LRRRRRR i
def weightRow1LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow1LRRRRL i else weightRow1LRRRRR i
def weightRow1LRRR (i : ℕ) : ℕ := if i < 240 then weightRow1LRRRL i else weightRow1LRRRR i
def weightRow1LRR (i : ℕ) : ℕ := if i < 224 then weightRow1LRRL i else weightRow1LRRR i
def weightRow1LR (i : ℕ) : ℕ := if i < 192 then weightRow1LRL i else weightRow1LRR i
def weightRow1L (i : ℕ) : ℕ := if i < 128 then weightRow1LL i else weightRow1LR i
def weightRow1RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 975861215585105 else 975518856785105
def weightRow1RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 977614710087105 else 977296777229105
def weightRow1RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow1RLLLLLLL i else weightRow1RLLLLLLR i
def weightRow1RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 979249461144105 else 978954244698105
def weightRow1RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 980842774606105 else 980574431410105
def weightRow1RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow1RLLLLLRL i else weightRow1RLLLLLRR i
def weightRow1RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow1RLLLLLL i else weightRow1RLLLLLR i
def weightRow1RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 982414020527105 else 982168174146105
def weightRow1RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 984006850282105 else 983785882251105
def weightRow1RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow1RLLLLRLL i else weightRow1RLLLLRLR i
def weightRow1RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 985516547818105 else 985320959565105
def weightRow1RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 987000210908105 else 986839570290105
def weightRow1RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow1RLLLLRRL i else weightRow1RLLLLRRR i
def weightRow1RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow1RLLLLRL i else weightRow1RLLLLRR i
def weightRow1RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow1RLLLLL i else weightRow1RLLLLR i
def weightRow1RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 988428747844105 else 988288029123105
def weightRow1RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 989751966591105 else 989637608980105
def weightRow1RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow1RLLLRLLL i else weightRow1RLLLRLLR i
def weightRow1RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 991009622033105 else 990917434550105
def weightRow1RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 992209949180105 else 992142028741105
def weightRow1RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow1RLLLRLRL i else weightRow1RLLLRLRR i
def weightRow1RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow1RLLLRLL i else weightRow1RLLLRLR i
def weightRow1RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 993321874722105 else 993273575926105
def weightRow1RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 994332345228105 else 994304040298105
def weightRow1RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow1RLLLRRLL i else weightRow1RLLLRRLR i
def weightRow1RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 995277130969105 else 995263901241105
def weightRow1RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 996186714015105 else 996173851030105
def weightRow1RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow1RLLLRRRL i else weightRow1RLLLRRRR i
def weightRow1RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow1RLLLRRL i else weightRow1RLLLRRR i
def weightRow1RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow1RLLLRL i else weightRow1RLLLRR i
def weightRow1RLLL (i : ℕ) : ℕ := if i < 272 then weightRow1RLLLL i else weightRow1RLLLR i
def weightRow1RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 997079825501105 else 997078647166105
def weightRow1RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 997960311214105 else 997954154490105
def weightRow1RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow1RLLRLLLL i else weightRow1RLLRLLLR i
def weightRow1RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 998823126682105 else 998812575708105
def weightRow1RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 999660136378105 else 999645230640105
def weightRow1RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow1RLLRLLRL i else weightRow1RLLRLLRR i
def weightRow1RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow1RLLRLLL i else weightRow1RLLRLLR i
def weightRow1RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1000433652513105 else 1000422092030105
def weightRow1RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1001120967726105 else 1001108301817105
def weightRow1RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow1RLLRLRLL i else weightRow1RLLRLRLR i
def weightRow1RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1001751961297105 else 1001739812886105
def weightRow1RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1002330124389105 else 1002317678738105
def weightRow1RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow1RLLRLRRL i else weightRow1RLLRLRRR i
def weightRow1RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow1RLLRLRL i else weightRow1RLLRLRR i
def weightRow1RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow1RLLRLL i else weightRow1RLLRLR i
def weightRow1RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1002824947948105 else 1002811174530105
def weightRow1RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1003227707914105 else 1003214746504105
def weightRow1RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow1RLLRRLLL i else weightRow1RLLRRLLR i
def weightRow1RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1003558721712105 else 1003550362858105
def weightRow1RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1003778772892105 else 1003780702742105
def weightRow1RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow1RLLRRLRL i else weightRow1RLLRRLRR i
def weightRow1RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow1RLLRRLL i else weightRow1RLLRRLR i
def weightRow1RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1003971901564105 else 1003991697040105
def weightRow1RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1004144608842105 else 1004173672061105
def weightRow1RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow1RLLRRRLL i else weightRow1RLLRRRLR i
def weightRow1RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1004250701846105 else 1004292699367105
def weightRow1RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1004328440695105 else 1004378598066105
def weightRow1RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow1RLLRRRRL i else weightRow1RLLRRRRR i
def weightRow1RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow1RLLRRRL i else weightRow1RLLRRRR i
def weightRow1RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow1RLLRRL i else weightRow1RLLRRR i
def weightRow1RLLR (i : ℕ) : ℕ := if i < 304 then weightRow1RLLRL i else weightRow1RLLRR i
def weightRow1RLL (i : ℕ) : ℕ := if i < 288 then weightRow1RLLL i else weightRow1RLLR i
def weightRow1RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1004342138521105 else 1004398441505105
def weightRow1RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1004351834553105 else 1004401490434105
def weightRow1RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow1RLRLLLLL i else weightRow1RLRLLLLR i
def weightRow1RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1004348473757105 else 1004402764114105
def weightRow1RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1004284583152105 else 1004346466607105
def weightRow1RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow1RLRLLLRL i else weightRow1RLRLLLRR i
def weightRow1RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow1RLRLLLL i else weightRow1RLRLLLR i
def weightRow1RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1004200365500105 else 1004272065819105
def weightRow1RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1004068440631105 else 1004147478683105
def weightRow1RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow1RLRLLRLL i else weightRow1RLRLLRLR i
def weightRow1RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1003927129844105 else 1004021947303105
def weightRow1RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1003792353843105 else 1003894237921105
def weightRow1RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow1RLRLLRRL i else weightRow1RLRLLRRR i
def weightRow1RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow1RLRLLRL i else weightRow1RLRLLRR i
def weightRow1RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow1RLRLLL i else weightRow1RLRLLR i
def weightRow1RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1003579545962105 else 1003683221243105
def weightRow1RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1003326729523105 else 1003427043220105
def weightRow1RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow1RLRLRLLL i else weightRow1RLRLRLLR i
def weightRow1RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 1003012774249105 else 1003105735631105
def weightRow1RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 1002645434011105 else 1002730750670105
def weightRow1RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow1RLRLRLRL i else weightRow1RLRLRLRR i
def weightRow1RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow1RLRLRLL i else weightRow1RLRLRLR i
def weightRow1RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 1002257742026105 else 1002334514335105
def weightRow1RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 1001851058529105 else 1001916452381105
def weightRow1RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow1RLRLRRLL i else weightRow1RLRLRRLR i
def weightRow1RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 1001391820075105 else 1001448250016105
def weightRow1RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 1000918040249105 else 1000956129808105
def weightRow1RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow1RLRLRRRL i else weightRow1RLRLRRRR i
def weightRow1RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow1RLRLRRL i else weightRow1RLRLRRR i
def weightRow1RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow1RLRLRL i else weightRow1RLRLRR i
def weightRow1RLRL (i : ℕ) : ℕ := if i < 336 then weightRow1RLRLL i else weightRow1RLRLR i
def weightRow1RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 1000465340544105 else 1000482490454105
def weightRow1RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 1000048786455105 else 1000042674426105
def weightRow1RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow1RLRRLLLL i else weightRow1RLRRLLLR i
def weightRow1RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 999665422224105 else 999650695783105
def weightRow1RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 999347643711105 else 999311206172105
def weightRow1RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow1RLRRLLRL i else weightRow1RLRRLLRR i
def weightRow1RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow1RLRRLLL i else weightRow1RLRRLLR i
def weightRow1RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 999056358067105 else 999012010893105
def weightRow1RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 998775619072105 else 998727923495105
def weightRow1RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow1RLRRLRLL i else weightRow1RLRRLRLR i
def weightRow1RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 998478368223105 else 998425705003105
def weightRow1RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 998176451706105 else 998123907832105
def weightRow1RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow1RLRRLRRL i else weightRow1RLRRLRRR i
def weightRow1RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow1RLRRLRL i else weightRow1RLRRLRR i
def weightRow1RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow1RLRRLL i else weightRow1RLRRLR i
def weightRow1RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 997910481157105 else 997856877802105
def weightRow1RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 997672641461105 else 997621478326105
def weightRow1RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow1RLRRRLLL i else weightRow1RLRRRLLR i
def weightRow1RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 997434921864105 else 997380066187105
def weightRow1RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 997229093581105 else 997185778444105
def weightRow1RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow1RLRRRLRL i else weightRow1RLRRRLRR i
def weightRow1RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow1RLRRRLL i else weightRow1RLRRRLR i
def weightRow1RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 997118042870105 else 997076581687105
def weightRow1RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 997041978663105 else 997003825202105
def weightRow1RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow1RLRRRRLL i else weightRow1RLRRRRLR i
def weightRow1RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 997122920678105 else 997083629843105
def weightRow1RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 997315705210105 else 997282158688105
def weightRow1RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow1RLRRRRRL i else weightRow1RLRRRRRR i
def weightRow1RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow1RLRRRRL i else weightRow1RLRRRRR i
def weightRow1RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow1RLRRRL i else weightRow1RLRRRR i
def weightRow1RLRR (i : ℕ) : ℕ := if i < 368 then weightRow1RLRRL i else weightRow1RLRRR i
def weightRow1RLR (i : ℕ) : ℕ := if i < 352 then weightRow1RLRL i else weightRow1RLRR i
def weightRow1RL (i : ℕ) : ℕ := if i < 320 then weightRow1RLL i else weightRow1RLR i
def weightRow1RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 997610919394105 else 997580354704105
def weightRow1RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 997952682355105 else 997928243332105
def weightRow1RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow1RRLLLLLL i else weightRow1RRLLLLLR i
def weightRow1RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 998261161537105 else 998241050410105
def weightRow1RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 998553057222105 else 998537761827105
def weightRow1RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow1RRLLLLRL i else weightRow1RRLLLLRR i
def weightRow1RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow1RRLLLLL i else weightRow1RRLLLLR i
def weightRow1RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 998817662109105 else 998806752030105
def weightRow1RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 999056970766105 else 999048871767105
def weightRow1RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow1RRLLLRLL i else weightRow1RRLLLRLR i
def weightRow1RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 999312150521105 else 999308572344105
def weightRow1RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 999520918023105 else 999513632635105
def weightRow1RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow1RRLLLRRL i else weightRow1RRLLLRRR i
def weightRow1RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow1RRLLLRL i else weightRow1RRLLLRR i
def weightRow1RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow1RRLLLL i else weightRow1RRLLLR i
def weightRow1RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 999719309032105 else 999720655336105
def weightRow1RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 999888417939105 else 999887018888105
def weightRow1RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow1RRLLRLLL i else weightRow1RRLLRLLR i
def weightRow1RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000043829720105 else 1000053072222105
def weightRow1RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000194696281105 else 1000199603174105
def weightRow1RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow1RRLLRLRL i else weightRow1RRLLRLRR i
def weightRow1RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow1RRLLRLL i else weightRow1RRLLRLR i
def weightRow1RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000316184571105 else 1000322568387105
def weightRow1RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000437447470105 else 1000442512528105
def weightRow1RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow1RRLLRRLL i else weightRow1RRLLRRLR i
def weightRow1RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000543386091105 else 1000551526329105
def weightRow1RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000615255702105 else 1000625198050105
def weightRow1RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow1RRLLRRRL i else weightRow1RRLLRRRR i
def weightRow1RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow1RRLLRRL i else weightRow1RRLLRRR i
def weightRow1RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow1RRLLRL i else weightRow1RRLLRR i
def weightRow1RRLL (i : ℕ) : ℕ := if i < 400 then weightRow1RRLLL i else weightRow1RRLLR i
def weightRow1RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000665432953105 else 1000673189763105
def weightRow1RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000701222034105 else 1000713789325105
def weightRow1RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow1RRLRLLLL i else weightRow1RRLRLLLR i
def weightRow1RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000752121482105 else 1000762845782105
def weightRow1RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000800402583105 else 1000807562139105
def weightRow1RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow1RRLRLLRL i else weightRow1RRLRLLRR i
def weightRow1RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow1RRLRLLL i else weightRow1RRLRLLR i
def weightRow1RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000833151041105 else 1000842851276105
def weightRow1RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000840787662105 else 1000849955119105
def weightRow1RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow1RRLRLRLL i else weightRow1RRLRLRLR i
def weightRow1RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000853002748105 else 1000868602790105
def weightRow1RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000815096759105 else 1000827882669105
def weightRow1RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow1RRLRLRRL i else weightRow1RRLRLRRR i
def weightRow1RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow1RRLRLRL i else weightRow1RRLRLRR i
def weightRow1RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow1RRLRLL i else weightRow1RRLRLR i
def weightRow1RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000797109613105 else 1000809146378105
def weightRow1RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000790084075105 else 1000793445258105
def weightRow1RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow1RRLRRLLL i else weightRow1RRLRRLLR i
def weightRow1RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000727809210105 else 1000738951613105
def weightRow1RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000689638682105 else 1000692597816105
def weightRow1RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow1RRLRRLRL i else weightRow1RRLRRLRR i
def weightRow1RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow1RRLRRLL i else weightRow1RRLRRLR i
def weightRow1RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000595548614105 else 1000604167991105
def weightRow1RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000512415606105 else 1000522540162105
def weightRow1RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow1RRLRRRLL i else weightRow1RRLRRRLR i
def weightRow1RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000465161047105 else 1000474598253105
def weightRow1RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000400968471105 else 1000422953130105
def weightRow1RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow1RRLRRRRL i else weightRow1RRLRRRRR i
def weightRow1RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow1RRLRRRL i else weightRow1RRLRRRR i
def weightRow1RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow1RRLRRL i else weightRow1RRLRRR i
def weightRow1RRLR (i : ℕ) : ℕ := if i < 432 then weightRow1RRLRL i else weightRow1RRLRR i
def weightRow1RRL (i : ℕ) : ℕ := if i < 416 then weightRow1RRLL i else weightRow1RRLR i
def weightRow1RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 1000450030109105 else 1000460185964105
def weightRow1RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 1000379545898105 else 1000393753351105
def weightRow1RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow1RRRLLLLL i else weightRow1RRRLLLLR i
def weightRow1RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 1000307044575105 else 1000316733669105
def weightRow1RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 1000252048373105 else 1000280053034105
def weightRow1RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow1RRRLLLRL i else weightRow1RRRLLLRR i
def weightRow1RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow1RRRLLLL i else weightRow1RRRLLLR i
def weightRow1RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 1000242510611105 else 1000251326591105
def weightRow1RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 1000278639763105 else 1000294963181105
def weightRow1RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow1RRRLLRLL i else weightRow1RRRLLRLR i
def weightRow1RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 1000233852770105 else 1000231576956105
def weightRow1RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 1000195925647105 else 1000210109811105
def weightRow1RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow1RRRLLRRL i else weightRow1RRRLLRRR i
def weightRow1RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow1RRRLLRL i else weightRow1RRRLLRR i
def weightRow1RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow1RRRLLL i else weightRow1RRRLLR i
def weightRow1RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 1000173651223105 else 1000160450347105
def weightRow1RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 1000057635932105 else 1000058444624105
def weightRow1RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow1RRRLRLLL i else weightRow1RRRLRLLR i
def weightRow1RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999976579435105 else 999956889165105
def weightRow1RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999962630575105 else 999955962507105
def weightRow1RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow1RRRLRLRL i else weightRow1RRRLRLRR i
def weightRow1RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow1RRRLRLL i else weightRow1RRRLRLR i
def weightRow1RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999921585562105 else 999912470321105
def weightRow1RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999886389837105 else 999870653998105
def weightRow1RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow1RRRLRRLL i else weightRow1RRRLRRLR i
def weightRow1RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999792270522105 else 999786686621105
def weightRow1RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999785760061105 else 999790376287105
def weightRow1RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow1RRRLRRRL i else weightRow1RRRLRRRR i
def weightRow1RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow1RRRLRRL i else weightRow1RRRLRRR i
def weightRow1RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow1RRRLRL i else weightRow1RRRLRR i
def weightRow1RRRL (i : ℕ) : ℕ := if i < 464 then weightRow1RRRLL i else weightRow1RRRLR i
def weightRow1RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999795823982105 else 999784132233105
def weightRow1RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999754920806105 else 999755869263105
def weightRow1RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow1RRRRLLLL i else weightRow1RRRRLLLR i
def weightRow1RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999774199502105 else 999752205574105
def weightRow1RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999808153553105 else 999785938960105
def weightRow1RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow1RRRRLLRL i else weightRow1RRRRLLRR i
def weightRow1RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow1RRRRLLL i else weightRow1RRRRLLR i
def weightRow1RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999726991689105 else 999707989035105
def weightRow1RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 999644911348105 else 999628681864105
def weightRow1RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow1RRRRLRLL i else weightRow1RRRRLRLR i
def weightRow1RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 999559134719105 else 999539234601105
def weightRow1RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 999605981178105 else 999602574549105
def weightRow1RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow1RRRRLRRL i else weightRow1RRRRLRRR i
def weightRow1RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow1RRRRLRL i else weightRow1RRRRLRR i
def weightRow1RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow1RRRRLL i else weightRow1RRRRLR i
def weightRow1RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 999596803634105 else 999624769584105
def weightRow1RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 999668686566105 else 999685999911105
def weightRow1RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow1RRRRRLLL i else weightRow1RRRRRLLR i
def weightRow1RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 999628062691105 else 999640427486105
def weightRow1RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 999520033606105 else 999526677811105
def weightRow1RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow1RRRRRLRL i else weightRow1RRRRRLRR i
def weightRow1RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow1RRRRRLL i else weightRow1RRRRRLR i
def weightRow1RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 999535743324105 else 999543272011105
def weightRow1RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 999577852032105 else 999580605556105
def weightRow1RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow1RRRRRRLL i else weightRow1RRRRRRLR i
def weightRow1RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 999870494967105 else 999851741907105
def weightRow1RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 999885775588105 else 999886320208105
def weightRow1RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow1RRRRRRRL i else weightRow1RRRRRRRR i
def weightRow1RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow1RRRRRRL i else weightRow1RRRRRRR i
def weightRow1RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow1RRRRRL i else weightRow1RRRRRR i
def weightRow1RRRR (i : ℕ) : ℕ := if i < 496 then weightRow1RRRRL i else weightRow1RRRRR i
def weightRow1RRR (i : ℕ) : ℕ := if i < 480 then weightRow1RRRL i else weightRow1RRRR i
def weightRow1RR (i : ℕ) : ℕ := if i < 448 then weightRow1RRL i else weightRow1RRR i
def weightRow1R (i : ℕ) : ℕ := if i < 384 then weightRow1RL i else weightRow1RR i
def weightRow1 (i : ℕ) : ℕ := if i < 256 then weightRow1L i else weightRow1R i
def weightRow2LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 102287639818105 else 103628333137105
def weightRow2LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 141211236725105 else 144399584690105
def weightRow2LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow2LLLLLLLL i else weightRow2LLLLLLLR i
def weightRow2LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 385514932414105 else 366145034271105
def weightRow2LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 419626365124105 else 411166868337105
def weightRow2LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow2LLLLLLRL i else weightRow2LLLLLLRR i
def weightRow2LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow2LLLLLLL i else weightRow2LLLLLLR i
def weightRow2LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 154400710438105 else 154307470439105
def weightRow2LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 243130799073105 else 238614558388105
def weightRow2LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow2LLLLLRLL i else weightRow2LLLLLRLR i
def weightRow2LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 606209897802105 else 604262813583105
def weightRow2LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 465607071317105 else 484058374864105
def weightRow2LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow2LLLLLRRL i else weightRow2LLLLLRRR i
def weightRow2LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow2LLLLLRL i else weightRow2LLLLLRR i
def weightRow2LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow2LLLLLL i else weightRow2LLLLLR i
def weightRow2LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 773065867457105 else 786434950430105
def weightRow2LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 389690075297105 else 392167781288105
def weightRow2LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow2LLLLRLLL i else weightRow2LLLLRLLR i
def weightRow2LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 667770632068105 else 694308422085105
def weightRow2LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 498509742976105 else 492145623344105
def weightRow2LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow2LLLLRLRL i else weightRow2LLLLRLRR i
def weightRow2LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow2LLLLRLL i else weightRow2LLLLRLR i
def weightRow2LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 777911076567105 else 788461234392105
def weightRow2LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 552905948166105 else 533502904583105
def weightRow2LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow2LLLLRRLL i else weightRow2LLLLRRLR i
def weightRow2LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 586615537777105 else 607215165344105
def weightRow2LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 424676568434105 else 437568553200105
def weightRow2LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow2LLLLRRRL i else weightRow2LLLLRRRR i
def weightRow2LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow2LLLLRRL i else weightRow2LLLLRRR i
def weightRow2LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow2LLLLRL i else weightRow2LLLLRR i
def weightRow2LLLL (i : ℕ) : ℕ := if i < 16 then weightRow2LLLLL i else weightRow2LLLLR i
def weightRow2LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 1017805376345105 else 999841939516105
def weightRow2LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 815545048748105 else 843082211835105
def weightRow2LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow2LLLRLLLL i else weightRow2LLLRLLLR i
def weightRow2LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 1121827225862105 else 1117158003099105
def weightRow2LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 1210219551359105 else 1252304396865105
def weightRow2LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow2LLLRLLRL i else weightRow2LLLRLLRR i
def weightRow2LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow2LLLRLLL i else weightRow2LLLRLLR i
def weightRow2LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 1001167501103105 else 1013106192667105
def weightRow2LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 804080340278105 else 812033689120105
def weightRow2LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow2LLLRLRLL i else weightRow2LLLRLRLR i
def weightRow2LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 834988764563105 else 829487586170105
def weightRow2LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 811483399834105 else 831051379043105
def weightRow2LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow2LLLRLRRL i else weightRow2LLLRLRRR i
def weightRow2LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow2LLLRLRL i else weightRow2LLLRLRR i
def weightRow2LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow2LLLRLL i else weightRow2LLLRLR i
def weightRow2LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 1018380425980105 else 979936529850105
def weightRow2LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 579157927121105 else 620819466256105
def weightRow2LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow2LLLRRLLL i else weightRow2LLLRRLLR i
def weightRow2LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 651924476111105 else 640019328883105
def weightRow2LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 706418331477105 else 738171635921105
def weightRow2LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow2LLLRRLRL i else weightRow2LLLRRLRR i
def weightRow2LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow2LLLRRLL i else weightRow2LLLRRLR i
def weightRow2LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 644713823206105 else 651651271600105
def weightRow2LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 689819589903105 else 695140320534105
def weightRow2LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow2LLLRRRLL i else weightRow2LLLRRRLR i
def weightRow2LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 663866714486105 else 660728677618105
def weightRow2LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 611306458305105 else 623462876384105
def weightRow2LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow2LLLRRRRL i else weightRow2LLLRRRRR i
def weightRow2LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow2LLLRRRL i else weightRow2LLLRRRR i
def weightRow2LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow2LLLRRL i else weightRow2LLLRRR i
def weightRow2LLLR (i : ℕ) : ℕ := if i < 48 then weightRow2LLLRL i else weightRow2LLLRR i
def weightRow2LLL (i : ℕ) : ℕ := if i < 32 then weightRow2LLLL i else weightRow2LLLR i
def weightRow2LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 630473485180105 else 623584378216105
def weightRow2LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 687918243737105 else 696265005856105
def weightRow2LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow2LLRLLLLL i else weightRow2LLRLLLLR i
def weightRow2LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 743938750534105 else 743874360699105
def weightRow2LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 722260172714105 else 720468422901105
def weightRow2LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow2LLRLLLRL i else weightRow2LLRLLLRR i
def weightRow2LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow2LLRLLLL i else weightRow2LLRLLLR i
def weightRow2LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 831598079705105 else 804469319621105
def weightRow2LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 756442856524105 else 772729721367105
def weightRow2LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow2LLRLLRLL i else weightRow2LLRLLRLR i
def weightRow2LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 758758766111105 else 721085415493105
def weightRow2LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 1145048749353105 else 1187490485877105
def weightRow2LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow2LLRLLRRL i else weightRow2LLRLLRRR i
def weightRow2LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow2LLRLLRL i else weightRow2LLRLLRR i
def weightRow2LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow2LLRLLL i else weightRow2LLRLLR i
def weightRow2LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 1027037387409105 else 1011829063023105
def weightRow2LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 1054486865959105 else 1064192171327105
def weightRow2LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow2LLRLRLLL i else weightRow2LLRLRLLR i
def weightRow2LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 1066194627206105 else 1062477218271105
def weightRow2LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 1299758931809105 else 1291803894043105
def weightRow2LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow2LLRLRLRL i else weightRow2LLRLRLRR i
def weightRow2LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow2LLRLRLL i else weightRow2LLRLRLR i
def weightRow2LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 1578831042568105 else 1539954972644105
def weightRow2LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 1485815257943105 else 1493155357060105
def weightRow2LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow2LLRLRRLL i else weightRow2LLRLRRLR i
def weightRow2LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1248127275586105 else 1222949550553105
def weightRow2LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 1440014688799105 else 1460219121340105
def weightRow2LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow2LLRLRRRL i else weightRow2LLRLRRRR i
def weightRow2LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow2LLRLRRL i else weightRow2LLRLRRR i
def weightRow2LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow2LLRLRL i else weightRow2LLRLRR i
def weightRow2LLRL (i : ℕ) : ℕ := if i < 80 then weightRow2LLRLL i else weightRow2LLRLR i
def weightRow2LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 907075721659105 else 896545463555105
def weightRow2LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 1100385734734105 else 1081652372870105
def weightRow2LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow2LLRRLLLL i else weightRow2LLRRLLLR i
def weightRow2LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1052203001686105 else 1073492723650105
def weightRow2LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 1335924064505105 else 1327423557346105
def weightRow2LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow2LLRRLLRL i else weightRow2LLRRLLRR i
def weightRow2LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow2LLRRLLL i else weightRow2LLRRLLR i
def weightRow2LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 1068173696595105 else 1076554876925105
def weightRow2LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1297875590191105 else 1273065473305105
def weightRow2LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow2LLRRLRLL i else weightRow2LLRRLRLR i
def weightRow2LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1022139291216105 else 1020970545571105
def weightRow2LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 1444663771979105 else 1432378180865105
def weightRow2LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow2LLRRLRRL i else weightRow2LLRRLRRR i
def weightRow2LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow2LLRRLRL i else weightRow2LLRRLRR i
def weightRow2LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow2LLRRLL i else weightRow2LLRRLR i
def weightRow2LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1172434076383105 else 1154578601831105
def weightRow2LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 1320393168324105 else 1322694190961105
def weightRow2LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow2LLRRRLLL i else weightRow2LLRRRLLR i
def weightRow2LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 979107394564105 else 984084072545105
def weightRow2LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 912507140898105 else 913135278618105
def weightRow2LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow2LLRRRLRL i else weightRow2LLRRRLRR i
def weightRow2LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow2LLRRRLL i else weightRow2LLRRRLR i
def weightRow2LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 1190057972968105 else 1199182549718105
def weightRow2LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 1169338964252105 else 1189837240396105
def weightRow2LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow2LLRRRRLL i else weightRow2LLRRRRLR i
def weightRow2LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 968136658446105 else 966333518930105
def weightRow2LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 944096510629105 else 944117813052105
def weightRow2LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow2LLRRRRRL i else weightRow2LLRRRRRR i
def weightRow2LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow2LLRRRRL i else weightRow2LLRRRRR i
def weightRow2LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow2LLRRRL i else weightRow2LLRRRR i
def weightRow2LLRR (i : ℕ) : ℕ := if i < 112 then weightRow2LLRRL i else weightRow2LLRRR i
def weightRow2LLR (i : ℕ) : ℕ := if i < 96 then weightRow2LLRL i else weightRow2LLRR i
def weightRow2LL (i : ℕ) : ℕ := if i < 64 then weightRow2LLL i else weightRow2LLR i
def weightRow2LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 855234155889105 else 856566442841105
def weightRow2LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 866976177078105 else 868338283712105
def weightRow2LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow2LRLLLLLL i else weightRow2LRLLLLLR i
def weightRow2LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 878330512539105 else 879635540801105
def weightRow2LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 886026433550105 else 887652225626105
def weightRow2LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow2LRLLLLRL i else weightRow2LRLLLLRR i
def weightRow2LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow2LRLLLLL i else weightRow2LRLLLLR i
def weightRow2LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 893323107980105 else 895115371726105
def weightRow2LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 904849853659105 else 906699716734105
def weightRow2LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow2LRLLLRLL i else weightRow2LRLLLRLR i
def weightRow2LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 915200492017105 else 917099165486105
def weightRow2LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 920008243755105 else 922013815353105
def weightRow2LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow2LRLLLRRL i else weightRow2LRLLLRRR i
def weightRow2LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow2LRLLLRL i else weightRow2LRLLLRR i
def weightRow2LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow2LRLLLL i else weightRow2LRLLLR i
def weightRow2LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 927123909629105 else 928829066332105
def weightRow2LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 929527192356105 else 931090993358105
def weightRow2LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow2LRLLRLLL i else weightRow2LRLLRLLR i
def weightRow2LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 937971607820105 else 939481556797105
def weightRow2LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 942177570317105 else 943335303987105
def weightRow2LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow2LRLLRLRL i else weightRow2LRLLRLRR i
def weightRow2LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow2LRLLRLL i else weightRow2LRLLRLR i
def weightRow2LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 949119677060105 else 950356405947105
def weightRow2LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 951791748224105 else 952901991708105
def weightRow2LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow2LRLLRRLL i else weightRow2LRLLRRLR i
def weightRow2LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 958031459355105 else 959445727275105
def weightRow2LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 963818921046105 else 964987907289105
def weightRow2LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow2LRLLRRRL i else weightRow2LRLLRRRR i
def weightRow2LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow2LRLLRRL i else weightRow2LRLLRRR i
def weightRow2LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow2LRLLRL i else weightRow2LRLLRR i
def weightRow2LRLL (i : ℕ) : ℕ := if i < 144 then weightRow2LRLLL i else weightRow2LRLLR i
def weightRow2LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 972252829176105 else 973180071179105
def weightRow2LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 971530812280105 else 972787936748105
def weightRow2LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow2LRLRLLLL i else weightRow2LRLRLLLR i
def weightRow2LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 973963503174105 else 974793319041105
def weightRow2LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 971655915172105 else 972564686425105
def weightRow2LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow2LRLRLLRL i else weightRow2LRLRLLRR i
def weightRow2LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow2LRLRLLL i else weightRow2LRLRLLR i
def weightRow2LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 967934292887105 else 968202339916105
def weightRow2LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 967415435466105 else 967511481324105
def weightRow2LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow2LRLRLRLL i else weightRow2LRLRLRLR i
def weightRow2LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 969967501960105 else 969934080197105
def weightRow2LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 972072019183105 else 972140907237105
def weightRow2LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow2LRLRLRRL i else weightRow2LRLRLRRR i
def weightRow2LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow2LRLRLRL i else weightRow2LRLRLRR i
def weightRow2LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow2LRLRLL i else weightRow2LRLRLR i
def weightRow2LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 974588073044105 else 974315726317105
def weightRow2LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 973907469842105 else 974264024349105
def weightRow2LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow2LRLRRLLL i else weightRow2LRLRRLLR i
def weightRow2LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 980072427663105 else 979778318671105
def weightRow2LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 985200523383105 else 985081756881105
def weightRow2LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow2LRLRRLRL i else weightRow2LRLRRLRR i
def weightRow2LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow2LRLRRLL i else weightRow2LRLRRLR i
def weightRow2LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 989551249654105 else 988944274846105
def weightRow2LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 994945968037105 else 994211350629105
def weightRow2LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow2LRLRRRLL i else weightRow2LRLRRRLR i
def weightRow2LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 999712990188105 else 998881479838105
def weightRow2LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1004962389739105 else 1004173292901105
def weightRow2LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow2LRLRRRRL i else weightRow2LRLRRRRR i
def weightRow2LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow2LRLRRRL i else weightRow2LRLRRRR i
def weightRow2LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow2LRLRRL i else weightRow2LRLRRR i
def weightRow2LRLR (i : ℕ) : ℕ := if i < 176 then weightRow2LRLRL i else weightRow2LRLRR i
def weightRow2LRL (i : ℕ) : ℕ := if i < 160 then weightRow2LRLL i else weightRow2LRLR i
def weightRow2LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1011105035642105 else 1010119570871105
def weightRow2LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1017060998284105 else 1016151567941105
def weightRow2LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow2LRRLLLLL i else weightRow2LRRLLLLR i
def weightRow2LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1022192691448105 else 1021145506058105
def weightRow2LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1026541795303105 else 1025492905325105
def weightRow2LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow2LRRLLLRL i else weightRow2LRRLLLRR i
def weightRow2LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow2LRRLLLL i else weightRow2LRRLLLR i
def weightRow2LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1031298013409105 else 1030252334328105
def weightRow2LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1034431527969105 else 1033774824674105
def weightRow2LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow2LRRLLRLL i else weightRow2LRRLLRLR i
def weightRow2LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1038748352668105 else 1037867929675105
def weightRow2LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1043136335913105 else 1042780949997105
def weightRow2LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow2LRRLLRRL i else weightRow2LRRLLRRR i
def weightRow2LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow2LRRLLRL i else weightRow2LRRLLRR i
def weightRow2LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow2LRRLLL i else weightRow2LRRLLR i
def weightRow2LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1041533760509105 else 1040536673959105
def weightRow2LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1041772116424105 else 1040979727112105
def weightRow2LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow2LRRLRLLL i else weightRow2LRRLRLLR i
def weightRow2LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1041555062670105 else 1040629708064105
def weightRow2LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1041172822359105 else 1040281474695105
def weightRow2LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow2LRRLRLRL i else weightRow2LRRLRLRR i
def weightRow2LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow2LRRLRLL i else weightRow2LRRLRLR i
def weightRow2LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1037124270931105 else 1036337267956105
def weightRow2LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1028670845335105 else 1028458540297105
def weightRow2LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow2LRRLRRLL i else weightRow2LRRLRRLR i
def weightRow2LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1021519937574105 else 1021223438049105
def weightRow2LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1017998036107105 else 1018038237118105
def weightRow2LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow2LRRLRRRL i else weightRow2LRRLRRRR i
def weightRow2LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow2LRRLRRL i else weightRow2LRRLRRR i
def weightRow2LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow2LRRLRL i else weightRow2LRRLRR i
def weightRow2LRRL (i : ℕ) : ℕ := if i < 208 then weightRow2LRRLL i else weightRow2LRRLR i
def weightRow2LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 1011395696846105 else 1011172597147105
def weightRow2LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 1013026966379105 else 1012947756082105
def weightRow2LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow2LRRRLLLL i else weightRow2LRRRLLLR i
def weightRow2LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 1011660742820105 else 1011881493010105
def weightRow2LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 1011026878178105 else 1010895707814105
def weightRow2LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow2LRRRLLRL i else weightRow2LRRRLLRR i
def weightRow2LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow2LRRRLLL i else weightRow2LRRRLLR i
def weightRow2LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 1005949948560105 else 1005976700987105
def weightRow2LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 1004980979985105 else 1004857203576105
def weightRow2LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow2LRRRLRLL i else weightRow2LRRRLRLR i
def weightRow2LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 1000403543947105 else 1000691171545105
def weightRow2LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 1000061896217105 else 1000338095209105
def weightRow2LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow2LRRRLRRL i else weightRow2LRRRLRRR i
def weightRow2LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow2LRRRLRL i else weightRow2LRRRLRR i
def weightRow2LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow2LRRRLL i else weightRow2LRRRLR i
def weightRow2LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 993110429494105 else 993612023528105
def weightRow2LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 990318815086105 else 991077681900105
def weightRow2LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow2LRRRRLLL i else weightRow2LRRRRLLR i
def weightRow2LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 985166033863105 else 985914865133105
def weightRow2LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 985254171556105 else 985958037776105
def weightRow2LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow2LRRRRLRL i else weightRow2LRRRRLRR i
def weightRow2LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow2LRRRRLL i else weightRow2LRRRRLR i
def weightRow2LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 986391617298105 else 987077205180105
def weightRow2LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 983213676377105 else 983757773250105
def weightRow2LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow2LRRRRRLL i else weightRow2LRRRRRLR i
def weightRow2LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 980305768301105 else 980551451907105
def weightRow2LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 980498211938105 else 980772211932105
def weightRow2LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow2LRRRRRRL i else weightRow2LRRRRRRR i
def weightRow2LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow2LRRRRRL i else weightRow2LRRRRRR i
def weightRow2LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow2LRRRRL i else weightRow2LRRRRR i
def weightRow2LRRR (i : ℕ) : ℕ := if i < 240 then weightRow2LRRRL i else weightRow2LRRRR i
def weightRow2LRR (i : ℕ) : ℕ := if i < 224 then weightRow2LRRL i else weightRow2LRRR i
def weightRow2LR (i : ℕ) : ℕ := if i < 192 then weightRow2LRL i else weightRow2LRR i
def weightRow2L (i : ℕ) : ℕ := if i < 128 then weightRow2LL i else weightRow2LR i
def weightRow2RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 981068201698105 else 981350292733105
def weightRow2RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 983034130332105 else 983299919449105
def weightRow2RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow2RLLLLLLL i else weightRow2RLLLLLLR i
def weightRow2RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 984847693823105 else 985095667743105
def weightRow2RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 986511812353105 else 986743312867105
def weightRow2RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow2RLLLLLRL i else weightRow2RLLLLLRR i
def weightRow2RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow2RLLLLLL i else weightRow2RLLLLLR i
def weightRow2RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 988081521009105 else 988291573264105
def weightRow2RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 989561477252105 else 989746681546105
def weightRow2RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow2RLLLLRLL i else weightRow2RLLLLRLR i
def weightRow2RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 990884659271105 else 991043504745105
def weightRow2RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 992066634636105 else 992198501640105
def weightRow2RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow2RLLLLRRL i else weightRow2RLLLLRRR i
def weightRow2RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow2RLLLLRL i else weightRow2RLLLLRR i
def weightRow2RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow2RLLLLL i else weightRow2RLLLLR i
def weightRow2RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 993192190681105 else 993294463427105
def weightRow2RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 994223837586105 else 994301258790105
def weightRow2RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow2RLLLRLLL i else weightRow2RLLLRLLR i
def weightRow2RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 995233688746105 else 995287581315105
def weightRow2RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 996127489255105 else 996158907312105
def weightRow2RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow2RLLLRLRL i else weightRow2RLLLRLRR i
def weightRow2RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow2RLLLRLL i else weightRow2RLLLRLR i
def weightRow2RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 996969684625105 else 996983249199105
def weightRow2RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 997716721006105 else 997711381486105
def weightRow2RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow2RLLLRRLL i else weightRow2RLLLRRLR i
def weightRow2RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 998433401224105 else 998410753532105
def weightRow2RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 999063675789105 else 999018971101105
def weightRow2RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow2RLLLRRRL i else weightRow2RLLLRRRR i
def weightRow2RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow2RLLLRRL i else weightRow2RLLLRRR i
def weightRow2RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow2RLLLRL i else weightRow2RLLLRR i
def weightRow2RLLL (i : ℕ) : ℕ := if i < 272 then weightRow2RLLLL i else weightRow2RLLLR i
def weightRow2RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 999613768018105 else 999549352125105
def weightRow2RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 1000040608245105 else 999961037192105
def weightRow2RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow2RLLRLLLL i else weightRow2RLLRLLLR i
def weightRow2RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 1000485360966105 else 1000384549933105
def weightRow2RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1000899540860105 else 1000784056060105
def weightRow2RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow2RLLRLLRL i else weightRow2RLLRLLRR i
def weightRow2RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow2RLLRLLL i else weightRow2RLLRLLR i
def weightRow2RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1001355932797105 else 1001224606224105
def weightRow2RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1001877725699105 else 1001740101661105
def weightRow2RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow2RLLRLRLL i else weightRow2RLLRLRLR i
def weightRow2RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1002415706119105 else 1002274350355105
def weightRow2RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1002922089463105 else 1002779036795105
def weightRow2RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow2RLLRLRRL i else weightRow2RLLRLRRR i
def weightRow2RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow2RLLRLRL i else weightRow2RLLRLRR i
def weightRow2RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow2RLLRLL i else weightRow2RLLRLR i
def weightRow2RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1003403797486105 else 1003256987829105
def weightRow2RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1003854063101105 else 1003709590033105
def weightRow2RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow2RLLRRLLL i else weightRow2RLLRRLLR i
def weightRow2RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1004321552721105 else 1004169049251105
def weightRow2RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1004700303507105 else 1004549925574105
def weightRow2RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow2RLLRRLRL i else weightRow2RLLRRLRR i
def weightRow2RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow2RLLRRLL i else weightRow2RLLRRLR i
def weightRow2RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1005004234691105 else 1004853389786105
def weightRow2RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1005245693546105 else 1005101820618105
def weightRow2RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow2RLLRRRLL i else weightRow2RLLRRRLR i
def weightRow2RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1005406590528105 else 1005271813837105
def weightRow2RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1005495178686105 else 1005371440044105
def weightRow2RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow2RLLRRRRL i else weightRow2RLLRRRRR i
def weightRow2RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow2RLLRRRL i else weightRow2RLLRRRR i
def weightRow2RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow2RLLRRL i else weightRow2RLLRRR i
def weightRow2RLLR (i : ℕ) : ℕ := if i < 304 then weightRow2RLLRL i else weightRow2RLLRR i
def weightRow2RLL (i : ℕ) : ℕ := if i < 288 then weightRow2RLLL i else weightRow2RLLR i
def weightRow2RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1005503236863105 else 1005389996171105
def weightRow2RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1005415562555105 else 1005315817407105
def weightRow2RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow2RLRLLLLL i else weightRow2RLRLLLLR i
def weightRow2RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1005232625584105 else 1005145559671105
def weightRow2RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1004967205754105 else 1004895238611105
def weightRow2RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow2RLRLLLRL i else weightRow2RLRLLLRR i
def weightRow2RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow2RLRLLLL i else weightRow2RLRLLLR i
def weightRow2RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1004629645245105 else 1004572916260105
def weightRow2RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1004214142636105 else 1004173031951105
def weightRow2RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow2RLRLLRLL i else weightRow2RLRLLRLR i
def weightRow2RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1003742805612105 else 1003711727497105
def weightRow2RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1003196998561105 else 1003178701788105
def weightRow2RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow2RLRLLRRL i else weightRow2RLRLLRRR i
def weightRow2RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow2RLRLLRL i else weightRow2RLRLLRR i
def weightRow2RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow2RLRLLL i else weightRow2RLRLLR i
def weightRow2RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1002573713985105 else 1002561288208105
def weightRow2RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1001966494005105 else 1001969301046105
def weightRow2RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow2RLRLRLLL i else weightRow2RLRLRLLR i
def weightRow2RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 1001346106952105 else 1001361910326105
def weightRow2RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 1000720478458105 else 1000750317336105
def weightRow2RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow2RLRLRLRL i else weightRow2RLRLRLRR i
def weightRow2RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow2RLRLRLL i else weightRow2RLRLRLR i
def weightRow2RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 1000090127522105 else 1000134196850105
def weightRow2RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 999513136300105 else 999569896201105
def weightRow2RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow2RLRLRRLL i else weightRow2RLRLRRLR i
def weightRow2RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 999058760940105 else 999120174812105
def weightRow2RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 998709653585105 else 998776276493105
def weightRow2RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow2RLRLRRRL i else weightRow2RLRLRRRR i
def weightRow2RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow2RLRLRRL i else weightRow2RLRLRRR i
def weightRow2RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow2RLRLRL i else weightRow2RLRLRR i
def weightRow2RLRL (i : ℕ) : ℕ := if i < 336 then weightRow2RLRLL i else weightRow2RLRLR i
def weightRow2RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 998411012301105 else 998478722468105
def weightRow2RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 998210195401105 else 998282340937105
def weightRow2RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow2RLRRLLLL i else weightRow2RLRRLLLR i
def weightRow2RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 997981107028105 else 998055756921105
def weightRow2RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 997769185645105 else 997841315946105
def weightRow2RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow2RLRRLLRL i else weightRow2RLRRLLRR i
def weightRow2RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow2RLRRLLL i else weightRow2RLRRLLR i
def weightRow2RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 997564267976105 else 997639984028105
def weightRow2RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 997435606437105 else 997512209467105
def weightRow2RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow2RLRRLRLL i else weightRow2RLRRLRLR i
def weightRow2RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 997321048197105 else 997401181550105
def weightRow2RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 997275171559105 else 997351597353105
def weightRow2RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow2RLRRLRRL i else weightRow2RLRRLRRR i
def weightRow2RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow2RLRRLRL i else weightRow2RLRRLRR i
def weightRow2RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow2RLRRLL i else weightRow2RLRRLR i
def weightRow2RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 997234022907105 else 997307703141105
def weightRow2RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 997299877352105 else 997366679450105
def weightRow2RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow2RLRRRLLL i else weightRow2RLRRRLLR i
def weightRow2RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 997410826635105 else 997467343748105
def weightRow2RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 997601275818105 else 997647050887105
def weightRow2RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow2RLRRRLRL i else weightRow2RLRRRLRR i
def weightRow2RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow2RLRRRLL i else weightRow2RLRRRLR i
def weightRow2RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 997792946828105 else 997827811816105
def weightRow2RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 997966539401105 else 997991174224105
def weightRow2RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow2RLRRRRLL i else weightRow2RLRRRRLR i
def weightRow2RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 998197802138105 else 998214650643105
def weightRow2RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 998474956436105 else 998488499969105
def weightRow2RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow2RLRRRRRL i else weightRow2RLRRRRRR i
def weightRow2RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow2RLRRRRL i else weightRow2RLRRRRR i
def weightRow2RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow2RLRRRL i else weightRow2RLRRRR i
def weightRow2RLRR (i : ℕ) : ℕ := if i < 368 then weightRow2RLRRL i else weightRow2RLRRR i
def weightRow2RLR (i : ℕ) : ℕ := if i < 352 then weightRow2RLRL i else weightRow2RLRR i
def weightRow2RL (i : ℕ) : ℕ := if i < 320 then weightRow2RLL i else weightRow2RLR i
def weightRow2RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 998752926558105 else 998762128452105
def weightRow2RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 999022998249105 else 999028516343105
def weightRow2RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow2RRLLLLLL i else weightRow2RRLLLLLR i
def weightRow2RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 999265326864105 else 999266069158105
def weightRow2RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 999490256685105 else 999487239736105
def weightRow2RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow2RRLLLLRL i else weightRow2RRLLLLRR i
def weightRow2RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow2RRLLLLL i else weightRow2RRLLLLR i
def weightRow2RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 999686586571105 else 999679618835105
def weightRow2RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 999848796959105 else 999839025407105
def weightRow2RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow2RRLLLRLL i else weightRow2RRLLLRLR i
def weightRow2RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 1000011895680105 else 999997451826105
def weightRow2RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 1000147574104105 else 1000130308698105
def weightRow2RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow2RRLLLRRL i else weightRow2RRLLLRRR i
def weightRow2RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow2RRLLLRL i else weightRow2RRLLLRR i
def weightRow2RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow2RRLLLL i else weightRow2RRLLLR i
def weightRow2RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 1000275480451105 else 1000255902738105
def weightRow2RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 1000375373767105 else 1000353332897105
def weightRow2RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow2RRLLRLLL i else weightRow2RRLLRLLR i
def weightRow2RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000448188372105 else 1000425389454105
def weightRow2RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000542604791105 else 1000521891358105
def weightRow2RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow2RRLLRLRL i else weightRow2RRLLRLRR i
def weightRow2RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow2RRLLRLL i else weightRow2RRLLRLR i
def weightRow2RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000610854535105 else 1000581983177105
def weightRow2RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000680446953105 else 1000655675797105
def weightRow2RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow2RRLLRRLL i else weightRow2RRLLRRLR i
def weightRow2RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000714774721105 else 1000682805823105
def weightRow2RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000746534990105 else 1000723727880105
def weightRow2RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow2RRLLRRRL i else weightRow2RRLLRRRR i
def weightRow2RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow2RRLLRRL i else weightRow2RRLLRRR i
def weightRow2RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow2RRLLRL i else weightRow2RRLLRR i
def weightRow2RRLL (i : ℕ) : ℕ := if i < 400 then weightRow2RRLLL i else weightRow2RRLLR i
def weightRow2RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000775312244105 else 1000746467365105
def weightRow2RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000801867862105 else 1000778765504105
def weightRow2RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow2RRLRLLLL i else weightRow2RRLRLLLR i
def weightRow2RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000797895340105 else 1000770487211105
def weightRow2RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000826402185105 else 1000803519024105
def weightRow2RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow2RRLRLLRL i else weightRow2RRLRLLRR i
def weightRow2RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow2RRLRLLL i else weightRow2RRLRLLR i
def weightRow2RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000812453031105 else 1000791583971105
def weightRow2RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000812233627105 else 1000793291859105
def weightRow2RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow2RRLRLRLL i else weightRow2RRLRLRLR i
def weightRow2RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000797109111105 else 1000774405936105
def weightRow2RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000759655627105 else 1000745744526105
def weightRow2RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow2RRLRLRRL i else weightRow2RRLRLRRR i
def weightRow2RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow2RRLRLRL i else weightRow2RRLRLRR i
def weightRow2RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow2RRLRLL i else weightRow2RRLRLR i
def weightRow2RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000738447605105 else 1000717571634105
def weightRow2RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000731381807105 else 1000718011418105
def weightRow2RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow2RRLRRLLL i else weightRow2RRLRRLLR i
def weightRow2RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000654802480105 else 1000644103062105
def weightRow2RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000612649914105 else 1000606941977105
def weightRow2RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow2RRLRRLRL i else weightRow2RRLRRLRR i
def weightRow2RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow2RRLRRLL i else weightRow2RRLRRLR i
def weightRow2RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000511545189105 else 1000505935095105
def weightRow2RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000484570613105 else 1000481181227105
def weightRow2RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow2RRLRRRLL i else weightRow2RRLRRRLR i
def weightRow2RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000415453028105 else 1000402985593105
def weightRow2RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000315480863105 else 1000321014076105
def weightRow2RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow2RRLRRRRL i else weightRow2RRLRRRRR i
def weightRow2RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow2RRLRRRL i else weightRow2RRLRRRR i
def weightRow2RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow2RRLRRL i else weightRow2RRLRRR i
def weightRow2RRLR (i : ℕ) : ℕ := if i < 432 then weightRow2RRLRL i else weightRow2RRLRR i
def weightRow2RRL (i : ℕ) : ℕ := if i < 416 then weightRow2RRLL i else weightRow2RRLR i
def weightRow2RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 1000245353099105 else 1000251808306105
def weightRow2RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 1000159467294105 else 1000166418845105
def weightRow2RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow2RRRLLLLL i else weightRow2RRRLLLLR i
def weightRow2RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 1000034435807105 else 1000031254336105
def weightRow2RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 999981613984105 else 999985617322105
def weightRow2RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow2RRRLLLRL i else weightRow2RRRLLLRR i
def weightRow2RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow2RRRLLLL i else weightRow2RRRLLLR i
def weightRow2RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 999894872797105 else 999918708634105
def weightRow2RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 999937923072105 else 999953283740105
def weightRow2RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow2RRRLLRLL i else weightRow2RRRLLRLR i
def weightRow2RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 999856386145105 else 999877919726105
def weightRow2RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 999792862145105 else 999797609605105
def weightRow2RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow2RRRLLRRL i else weightRow2RRRLLRRR i
def weightRow2RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow2RRRLLRL i else weightRow2RRRLLRR i
def weightRow2RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow2RRRLLL i else weightRow2RRRLLR i
def weightRow2RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 999731366321105 else 999752172585105
def weightRow2RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 999725791963105 else 999729224829105
def weightRow2RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow2RRRLRLLL i else weightRow2RRRLRLLR i
def weightRow2RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999707423033105 else 999738637449105
def weightRow2RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999735196557105 else 999716334954105
def weightRow2RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow2RRRLRLRL i else weightRow2RRRLRLRR i
def weightRow2RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow2RRRLRLL i else weightRow2RRRLRLR i
def weightRow2RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999651205364105 else 999681262512105
def weightRow2RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999647198460105 else 999637127652105
def weightRow2RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow2RRRLRRLL i else weightRow2RRRLRRLR i
def weightRow2RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999623651089105 else 999656757736105
def weightRow2RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999672893753105 else 999672005172105
def weightRow2RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow2RRRLRRRL i else weightRow2RRRLRRRR i
def weightRow2RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow2RRRLRRL i else weightRow2RRRLRRR i
def weightRow2RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow2RRRLRL i else weightRow2RRRLRR i
def weightRow2RRRL (i : ℕ) : ℕ := if i < 464 then weightRow2RRRLL i else weightRow2RRRLR i
def weightRow2RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999763858807105 else 999784267334105
def weightRow2RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999741112851105 else 999749210103105
def weightRow2RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow2RRRRLLLL i else weightRow2RRRRLLLR i
def weightRow2RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999783530811105 else 999806152762105
def weightRow2RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999782036430105 else 999769751218105
def weightRow2RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow2RRRRLLRL i else weightRow2RRRRLLRR i
def weightRow2RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow2RRRRLLL i else weightRow2RRRRLLR i
def weightRow2RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999832377580105 else 999856682211105
def weightRow2RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 999886568674105 else 999900913016105
def weightRow2RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow2RRRRLRLL i else weightRow2RRRRLRLR i
def weightRow2RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 999984506515105 else 1000013744838105
def weightRow2RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 999962515997105 else 999954771163105
def weightRow2RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow2RRRRLRRL i else weightRow2RRRRLRRR i
def weightRow2RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow2RRRRLRL i else weightRow2RRRRLRR i
def weightRow2RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow2RRRRLL i else weightRow2RRRRLR i
def weightRow2RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 1000012781026105 else 1000021175188105
def weightRow2RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 999984952678105 else 999994659516105
def weightRow2RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow2RRRRRLLL i else weightRow2RRRRRLLR i
def weightRow2RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 1000071755577105 else 1000088750715105
def weightRow2RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 999941112566105 else 999940949954105
def weightRow2RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow2RRRRRLRL i else weightRow2RRRRRLRR i
def weightRow2RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow2RRRRRLL i else weightRow2RRRRRLR i
def weightRow2RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 999941006086105 else 999924830821105
def weightRow2RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 999760352823105 else 999756610375105
def weightRow2RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow2RRRRRRLL i else weightRow2RRRRRRLR i
def weightRow2RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 1000135519852105 else 1000143457385105
def weightRow2RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 999958537615105 else 999978565348105
def weightRow2RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow2RRRRRRRL i else weightRow2RRRRRRRR i
def weightRow2RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow2RRRRRRL i else weightRow2RRRRRRR i
def weightRow2RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow2RRRRRL i else weightRow2RRRRRR i
def weightRow2RRRR (i : ℕ) : ℕ := if i < 496 then weightRow2RRRRL i else weightRow2RRRRR i
def weightRow2RRR (i : ℕ) : ℕ := if i < 480 then weightRow2RRRL i else weightRow2RRRR i
def weightRow2RR (i : ℕ) : ℕ := if i < 448 then weightRow2RRL i else weightRow2RRR i
def weightRow2R (i : ℕ) : ℕ := if i < 384 then weightRow2RL i else weightRow2RR i
def weightRow2 (i : ℕ) : ℕ := if i < 256 then weightRow2L i else weightRow2R i
def weightRow3LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 14758927079105 else 14231688140105
def weightRow3LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 21196629547105 else 21075722592105
def weightRow3LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow3LLLLLLLL i else weightRow3LLLLLLLR i
def weightRow3LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 46629215050105 else 49137058404105
def weightRow3LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 44241866013105 else 42823847378105
def weightRow3LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow3LLLLLLRL i else weightRow3LLLLLLRR i
def weightRow3LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow3LLLLLLL i else weightRow3LLLLLLR i
def weightRow3LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 124304439170105 else 129235133999105
def weightRow3LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 182902665190105 else 168112973333105
def weightRow3LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow3LLLLLRLL i else weightRow3LLLLLRLR i
def weightRow3LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 354245072137105 else 371587212603105
def weightRow3LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 464712601262105 else 453714005887105
def weightRow3LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow3LLLLLRRL i else weightRow3LLLLLRRR i
def weightRow3LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow3LLLLLRL i else weightRow3LLLLLRR i
def weightRow3LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow3LLLLLL i else weightRow3LLLLLR i
def weightRow3LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 540227129709105 else 544817905917105
def weightRow3LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 691001403151105 else 678023494856105
def weightRow3LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow3LLLLRLLL i else weightRow3LLLLRLLR i
def weightRow3LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 718141033906105 else 699937619735105
def weightRow3LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 902596496497105 else 905977913272105
def weightRow3LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow3LLLLRLRL i else weightRow3LLLLRLRR i
def weightRow3LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow3LLLLRLL i else weightRow3LLLLRLR i
def weightRow3LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 965539026210105 else 949746783931105
def weightRow3LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 971772898395105 else 990036101577105
def weightRow3LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow3LLLLRRLL i else weightRow3LLLLRRLR i
def weightRow3LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 952628744954105 else 932203113443105
def weightRow3LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 708126728293105 else 711458150265105
def weightRow3LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow3LLLLRRRL i else weightRow3LLLLRRRR i
def weightRow3LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow3LLLLRRL i else weightRow3LLLLRRR i
def weightRow3LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow3LLLLRL i else weightRow3LLLLRR i
def weightRow3LLLL (i : ℕ) : ℕ := if i < 16 then weightRow3LLLLL i else weightRow3LLLLR i
def weightRow3LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 531470764436105 else 530241589280105
def weightRow3LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 690767968447105 else 692242873217105
def weightRow3LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow3LLLRLLLL i else weightRow3LLLRLLLR i
def weightRow3LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 708944367896105 else 725554852559105
def weightRow3LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 746913419895105 else 742354322848105
def weightRow3LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow3LLLRLLRL i else weightRow3LLLRLLRR i
def weightRow3LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow3LLLRLLL i else weightRow3LLLRLLR i
def weightRow3LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 637684201932105 else 638102071933105
def weightRow3LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 1032064093992105 else 1010542699624105
def weightRow3LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow3LLLRLRLL i else weightRow3LLLRLRLR i
def weightRow3LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 954666018072105 else 978709553662105
def weightRow3LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 667377271334105 else 615777557059105
def weightRow3LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow3LLLRLRRL i else weightRow3LLLRLRRR i
def weightRow3LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow3LLLRLRL i else weightRow3LLLRLRR i
def weightRow3LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow3LLLRLL i else weightRow3LLLRLR i
def weightRow3LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 642095115739105 else 650933080473105
def weightRow3LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 667590421448105 else 651786824503105
def weightRow3LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow3LLLRRLLL i else weightRow3LLLRRLLR i
def weightRow3LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 697887379028105 else 693253523374105
def weightRow3LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 849171952650105 else 859342913496105
def weightRow3LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow3LLLRRLRL i else weightRow3LLLRRLRR i
def weightRow3LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow3LLLRRLL i else weightRow3LLLRRLR i
def weightRow3LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 874391892749105 else 863693764870105
def weightRow3LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 843013218398105 else 823596118884105
def weightRow3LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow3LLLRRRLL i else weightRow3LLLRRRLR i
def weightRow3LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 959752972455105 else 959939929439105
def weightRow3LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 897502603193105 else 893382297704105
def weightRow3LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow3LLLRRRRL i else weightRow3LLLRRRRR i
def weightRow3LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow3LLLRRRL i else weightRow3LLLRRRR i
def weightRow3LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow3LLLRRL i else weightRow3LLLRRR i
def weightRow3LLLR (i : ℕ) : ℕ := if i < 48 then weightRow3LLLRL i else weightRow3LLLRR i
def weightRow3LLL (i : ℕ) : ℕ := if i < 32 then weightRow3LLLL i else weightRow3LLLR i
def weightRow3LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 909103018830105 else 909764910794105
def weightRow3LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 1004864278720105 else 1001228180560105
def weightRow3LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow3LLRLLLLL i else weightRow3LLRLLLLR i
def weightRow3LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 897091339716105 else 913306357573105
def weightRow3LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 964700741981105 else 972617922048105
def weightRow3LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow3LLRLLLRL i else weightRow3LLRLLLRR i
def weightRow3LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow3LLRLLLL i else weightRow3LLRLLLR i
def weightRow3LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 988853028726105 else 975865753794105
def weightRow3LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 849047398438105 else 850735015488105
def weightRow3LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow3LLRLLRLL i else weightRow3LLRLLRLR i
def weightRow3LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 831030321762105 else 844162249772105
def weightRow3LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 853333114038105 else 841889712886105
def weightRow3LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow3LLRLLRRL i else weightRow3LLRLLRRR i
def weightRow3LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow3LLRLLRL i else weightRow3LLRLLRR i
def weightRow3LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow3LLRLLL i else weightRow3LLRLLR i
def weightRow3LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 841133317183105 else 890754253779105
def weightRow3LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 1232501011036105 else 1206879049219105
def weightRow3LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow3LLRLRLLL i else weightRow3LLRLRLLR i
def weightRow3LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 1299385364594105 else 1319260597643105
def weightRow3LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 957217095470105 else 955460045610105
def weightRow3LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow3LLRLRLRL i else weightRow3LLRLRLRR i
def weightRow3LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow3LLRLRLL i else weightRow3LLRLRLR i
def weightRow3LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 1088025352005105 else 1091290148195105
def weightRow3LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 1099564371496105 else 1081451939883105
def weightRow3LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow3LLRLRRLL i else weightRow3LLRLRRLR i
def weightRow3LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1094251214335105 else 1090966414837105
def weightRow3LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 957633079185105 else 957020103607105
def weightRow3LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow3LLRLRRRL i else weightRow3LLRLRRRR i
def weightRow3LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow3LLRLRRL i else weightRow3LLRLRRR i
def weightRow3LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow3LLRLRL i else weightRow3LLRLRR i
def weightRow3LLRL (i : ℕ) : ℕ := if i < 80 then weightRow3LLRLL i else weightRow3LLRLR i
def weightRow3LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 1164929642136105 else 1159694476129105
def weightRow3LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 1418441842311105 else 1437201747027105
def weightRow3LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow3LLRRLLLL i else weightRow3LLRRLLLR i
def weightRow3LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1513911010015105 else 1493986846560105
def weightRow3LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 1512116834347105 else 1526187933452105
def weightRow3LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow3LLRRLLRL i else weightRow3LLRRLLRR i
def weightRow3LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow3LLRRLLL i else weightRow3LLRRLLR i
def weightRow3LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 1506131581909105 else 1501192987514105
def weightRow3LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1334562602337105 else 1351416100788105
def weightRow3LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow3LLRRLRLL i else weightRow3LLRRLRLR i
def weightRow3LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1344095851769105 else 1356189517532105
def weightRow3LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 1240405061081105 else 1235048053189105
def weightRow3LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow3LLRRLRRL i else weightRow3LLRRLRRR i
def weightRow3LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow3LLRRLRL i else weightRow3LLRRLRR i
def weightRow3LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow3LLRRLL i else weightRow3LLRRLR i
def weightRow3LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1175774655630105 else 1186094658161105
def weightRow3LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 1117823863810105 else 1099696648791105
def weightRow3LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow3LLRRRLLL i else weightRow3LLRRRLLR i
def weightRow3LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 934442369163105 else 948391551274105
def weightRow3LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 912183136422105 else 906557463978105
def weightRow3LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow3LLRRRLRL i else weightRow3LLRRRLRR i
def weightRow3LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow3LLRRRLL i else weightRow3LLRRRLR i
def weightRow3LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 840693216862105 else 841352195072105
def weightRow3LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 860915294035105 else 857611854482105
def weightRow3LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow3LLRRRRLL i else weightRow3LLRRRRLR i
def weightRow3LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 846634629155105 else 845908640204105
def weightRow3LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 853240060997105 else 852921595270105
def weightRow3LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow3LLRRRRRL i else weightRow3LLRRRRRR i
def weightRow3LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow3LLRRRRL i else weightRow3LLRRRRR i
def weightRow3LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow3LLRRRL i else weightRow3LLRRRR i
def weightRow3LLRR (i : ℕ) : ℕ := if i < 112 then weightRow3LLRRL i else weightRow3LLRRR i
def weightRow3LLR (i : ℕ) : ℕ := if i < 96 then weightRow3LLRL i else weightRow3LLRR i
def weightRow3LL (i : ℕ) : ℕ := if i < 64 then weightRow3LLL i else weightRow3LLR i
def weightRow3LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 852340207635105 else 851486598216105
def weightRow3LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 865429701665105 else 864569743843105
def weightRow3LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow3LRLLLLLL i else weightRow3LRLLLLLR i
def weightRow3LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 878613381994105 else 877753445326105
def weightRow3LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 891619365603105 else 890700322263105
def weightRow3LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow3LRLLLLRL i else weightRow3LRLLLLRR i
def weightRow3LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow3LRLLLLL i else weightRow3LRLLLLR i
def weightRow3LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 904859015457105 else 903944482467105
def weightRow3LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 917051483828105 else 916054323984105
def weightRow3LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow3LRLLLRLL i else weightRow3LRLLLRLR i
def weightRow3LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 928520534565105 else 927729706962105
def weightRow3LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 937495636873105 else 936411549017105
def weightRow3LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow3LRLLLRRL i else weightRow3LRLLLRRR i
def weightRow3LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow3LRLLLRL i else weightRow3LRLLLRR i
def weightRow3LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow3LRLLLL i else weightRow3LRLLLR i
def weightRow3LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 944874662177105 else 943954962923105
def weightRow3LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 951192611946105 else 950183860492105
def weightRow3LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow3LRLLRLLL i else weightRow3LRLLRLLR i
def weightRow3LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 955253167226105 else 954450431286105
def weightRow3LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 958963902602105 else 958416759389105
def weightRow3LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow3LRLLRLRL i else weightRow3LRLLRLRR i
def weightRow3LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow3LRLLRLL i else weightRow3LRLLRLR i
def weightRow3LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 959841009138105 else 959229387418105
def weightRow3LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 959752287836105 else 959377242283105
def weightRow3LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow3LRLLRRLL i else weightRow3LRLLRRLR i
def weightRow3LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 959567888089105 else 958898318858105
def weightRow3LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 959683943815105 else 959315808527105
def weightRow3LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow3LRLLRRRL i else weightRow3LRLLRRRR i
def weightRow3LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow3LRLLRRL i else weightRow3LRLLRRR i
def weightRow3LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow3LRLLRL i else weightRow3LRLLRR i
def weightRow3LRLL (i : ℕ) : ℕ := if i < 144 then weightRow3LRLLL i else weightRow3LRLLR i
def weightRow3LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 963609275665105 else 963203838080105
def weightRow3LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 970356106091105 else 969962896209105
def weightRow3LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow3LRLRLLLL i else weightRow3LRLRLLLR i
def weightRow3LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 974730375083105 else 974299363214105
def weightRow3LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 978885547060105 else 978183955431105
def weightRow3LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow3LRLRLLRL i else weightRow3LRLRLLRR i
def weightRow3LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow3LRLRLLL i else weightRow3LRLRLLR i
def weightRow3LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 982501690859105 else 981890726687105
def weightRow3LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 987890862197105 else 987230687680105
def weightRow3LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow3LRLRLRLL i else weightRow3LRLRLRLR i
def weightRow3LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 987206148675105 else 986862629269105
def weightRow3LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 987708983360105 else 987010929087105
def weightRow3LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow3LRLRLRRL i else weightRow3LRLRLRRR i
def weightRow3LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow3LRLRLRL i else weightRow3LRLRLRR i
def weightRow3LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow3LRLRLL i else weightRow3LRLRLR i
def weightRow3LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 992720021966105 else 992809970285105
def weightRow3LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 998197869453105 else 998153275693105
def weightRow3LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow3LRLRRLLL i else weightRow3LRLRRLLR i
def weightRow3LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 1003359743777105 else 1003569710478105
def weightRow3LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 1008136630564105 else 1008403409066105
def weightRow3LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow3LRLRRLRL i else weightRow3LRLRRLRR i
def weightRow3LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow3LRLRRLL i else weightRow3LRLRRLR i
def weightRow3LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 1010620665248105 else 1010730037276105
def weightRow3LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 1012740011926105 else 1013035949860105
def weightRow3LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow3LRLRRRLL i else weightRow3LRLRRRLR i
def weightRow3LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 1015394472160105 else 1015985852587105
def weightRow3LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1016263931398105 else 1016864168487105
def weightRow3LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow3LRLRRRRL i else weightRow3LRLRRRRR i
def weightRow3LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow3LRLRRRL i else weightRow3LRLRRRR i
def weightRow3LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow3LRLRRL i else weightRow3LRLRRR i
def weightRow3LRLR (i : ℕ) : ℕ := if i < 176 then weightRow3LRLRL i else weightRow3LRLRR i
def weightRow3LRL (i : ℕ) : ℕ := if i < 160 then weightRow3LRLL i else weightRow3LRLR i
def weightRow3LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1018118479554105 else 1018798671406105
def weightRow3LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1019818543137105 else 1020496691275105
def weightRow3LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow3LRRLLLLL i else weightRow3LRRLLLLR i
def weightRow3LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1020059130663105 else 1020805268807105
def weightRow3LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1021979821292105 else 1022478818264105
def weightRow3LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow3LRRLLLRL i else weightRow3LRRLLLRR i
def weightRow3LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow3LRRLLLL i else weightRow3LRRLLLR i
def weightRow3LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1022874650871105 else 1023245302950105
def weightRow3LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1023399961628105 else 1023998698288105
def weightRow3LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow3LRRLLRLL i else weightRow3LRRLLRLR i
def weightRow3LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1026130215132105 else 1026706448635105
def weightRow3LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1029177489871105 else 1029553507393105
def weightRow3LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow3LRRLLRRL i else weightRow3LRRLLRRR i
def weightRow3LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow3LRRLLRL i else weightRow3LRRLLRR i
def weightRow3LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow3LRRLLL i else weightRow3LRRLLR i
def weightRow3LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1031916595448105 else 1032498346330105
def weightRow3LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1034891555623105 else 1034699886397105
def weightRow3LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow3LRRLRLLL i else weightRow3LRRLRLLR i
def weightRow3LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1031816078478105 else 1031991164855105
def weightRow3LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1027633065450105 else 1027526148850105
def weightRow3LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow3LRRLRLRL i else weightRow3LRRLRLRR i
def weightRow3LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow3LRRLRLL i else weightRow3LRRLRLR i
def weightRow3LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1028729233884105 else 1028642986428105
def weightRow3LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1027802292439105 else 1027663828902105
def weightRow3LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow3LRRLRRLL i else weightRow3LRRLRRLR i
def weightRow3LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1026686515386105 else 1026818500418105
def weightRow3LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1025628036723105 else 1025832103402105
def weightRow3LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow3LRRLRRRL i else weightRow3LRRLRRRR i
def weightRow3LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow3LRRLRRL i else weightRow3LRRLRRR i
def weightRow3LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow3LRRLRL i else weightRow3LRRLRR i
def weightRow3LRRL (i : ℕ) : ℕ := if i < 208 then weightRow3LRRLL i else weightRow3LRRLR i
def weightRow3LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 1026684304171105 else 1026904306290105
def weightRow3LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 1024523035767105 else 1024815529741105
def weightRow3LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow3LRRRLLLL i else weightRow3LRRRLLLR i
def weightRow3LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 1018363220718105 else 1018369440101105
def weightRow3LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 1010622614333105 else 1010936201785105
def weightRow3LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow3LRRRLLRL i else weightRow3LRRRLLRR i
def weightRow3LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow3LRRRLLL i else weightRow3LRRRLLR i
def weightRow3LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 1002787670218105 else 1002883172682105
def weightRow3LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 994925845878105 else 995107892458105
def weightRow3LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow3LRRRLRLL i else weightRow3LRRRLRLR i
def weightRow3LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 989620987799105 else 989537816046105
def weightRow3LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 984083371394105 else 983814041280105
def weightRow3LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow3LRRRLRRL i else weightRow3LRRRLRRR i
def weightRow3LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow3LRRRLRL i else weightRow3LRRRLRR i
def weightRow3LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow3LRRRLL i else weightRow3LRRRLR i
def weightRow3LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 980081016028105 else 979890336575105
def weightRow3LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 977025937565105 else 976667286175105
def weightRow3LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow3LRRRRLLL i else weightRow3LRRRRLLR i
def weightRow3LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 974829951192105 else 974754061894105
def weightRow3LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 975462103401105 else 975166378300105
def weightRow3LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow3LRRRRLRL i else weightRow3LRRRRLRR i
def weightRow3LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow3LRRRRLL i else weightRow3LRRRRLR i
def weightRow3LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 976452048630105 else 976243006619105
def weightRow3LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 978573781962105 else 978349400831105
def weightRow3LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow3LRRRRRLL i else weightRow3LRRRRRLR i
def weightRow3LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 980412840646105 else 980237025213105
def weightRow3LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 982503495404105 else 982335816119105
def weightRow3LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow3LRRRRRRL i else weightRow3LRRRRRRR i
def weightRow3LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow3LRRRRRL i else weightRow3LRRRRRR i
def weightRow3LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow3LRRRRL i else weightRow3LRRRRR i
def weightRow3LRRR (i : ℕ) : ℕ := if i < 240 then weightRow3LRRRL i else weightRow3LRRRR i
def weightRow3LRR (i : ℕ) : ℕ := if i < 224 then weightRow3LRRL i else weightRow3LRRR i
def weightRow3LR (i : ℕ) : ℕ := if i < 192 then weightRow3LRL i else weightRow3LRR i
def weightRow3L (i : ℕ) : ℕ := if i < 128 then weightRow3LL i else weightRow3LR i
def weightRow3RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 984523320074105 else 984358664230105
def weightRow3RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 986588652042105 else 986434644344105
def weightRow3RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow3RLLLLLLL i else weightRow3RLLLLLLR i
def weightRow3RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 988481579636105 else 988338629064105
def weightRow3RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 990198146654105 else 990066241670105
def weightRow3RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow3RLLLLLRL i else weightRow3RLLLLLRR i
def weightRow3RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow3RLLLLLL i else weightRow3RLLLLLR i
def weightRow3RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 991738127878105 else 991618533148105
def weightRow3RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 993095260335105 else 992988147369105
def weightRow3RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow3RLLLLRLL i else weightRow3RLLLLRLR i
def weightRow3RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 994283039750105 else 994189734803105
def weightRow3RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 995310126477105 else 995227853095105
def weightRow3RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow3RLLLLRRL i else weightRow3RLLLLRRR i
def weightRow3RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow3RLLLLRL i else weightRow3RLLLLRR i
def weightRow3RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow3RLLLLL i else weightRow3RLLLLR i
def weightRow3RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 996212875396105 else 996146451801105
def weightRow3RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 997014477463105 else 996961462305105
def weightRow3RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow3RLLLRLLL i else weightRow3RLLLRLLR i
def weightRow3RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 997729909244105 else 997691852382105
def weightRow3RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 998393082131105 else 998366615353105
def weightRow3RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow3RLLLRLRL i else weightRow3RLLLRLRR i
def weightRow3RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow3RLLLRLL i else weightRow3RLLLRLR i
def weightRow3RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 999008554565105 else 998990101024105
def weightRow3RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 999619840885105 else 999610605393105
def weightRow3RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow3RLLLRRLL i else weightRow3RLLLRRLR i
def weightRow3RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 1000242081126105 else 1000238484354105
def weightRow3RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 1000876815969105 else 1000883666001105
def weightRow3RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow3RLLLRRRL i else weightRow3RLLLRRRR i
def weightRow3RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow3RLLLRRL i else weightRow3RLLLRRR i
def weightRow3RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow3RLLLRL i else weightRow3RLLLRR i
def weightRow3RLLL (i : ℕ) : ℕ := if i < 272 then weightRow3RLLLL i else weightRow3RLLLR i
def weightRow3RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 1001519440682105 else 1001532323485105
def weightRow3RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 1002110951870105 else 1002130349674105
def weightRow3RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow3RLLRLLLL i else weightRow3RLLRLLLR i
def weightRow3RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 1002606617365105 else 1002632237023105
def weightRow3RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1003041733521105 else 1003074502207105
def weightRow3RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow3RLLRLLRL i else weightRow3RLLRLLRR i
def weightRow3RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow3RLLRLLL i else weightRow3RLLRLLR i
def weightRow3RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1003418582486105 else 1003462989982105
def weightRow3RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1003744836550105 else 1003798981036105
def weightRow3RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow3RLLRLRLL i else weightRow3RLLRLRLR i
def weightRow3RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1003992118117105 else 1004057566472105
def weightRow3RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1004253880717105 else 1004326109203105
def weightRow3RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow3RLLRLRRL i else weightRow3RLLRLRRR i
def weightRow3RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow3RLLRLRL i else weightRow3RLLRLRR i
def weightRow3RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow3RLLRLL i else weightRow3RLLRLR i
def weightRow3RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1004512084842105 else 1004596216609105
def weightRow3RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1004695854745105 else 1004779973548105
def weightRow3RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow3RLLRRLLL i else weightRow3RLLRRLLR i
def weightRow3RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1004796963686105 else 1004883166970105
def weightRow3RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1004819218799105 else 1004903335564105
def weightRow3RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow3RLLRRLRL i else weightRow3RLLRRLRR i
def weightRow3RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow3RLLRRLL i else weightRow3RLLRRLR i
def weightRow3RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1004767044037105 else 1004848472661105
def weightRow3RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1004675024846105 else 1004756224182105
def weightRow3RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow3RLLRRRLL i else weightRow3RLLRRRLR i
def weightRow3RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1004548789636105 else 1004626500680105
def weightRow3RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1004379301193105 else 1004449103673105
def weightRow3RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow3RLLRRRRL i else weightRow3RLLRRRRR i
def weightRow3RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow3RLLRRRL i else weightRow3RLLRRRR i
def weightRow3RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow3RLLRRL i else weightRow3RLLRRR i
def weightRow3RLLR (i : ℕ) : ℕ := if i < 304 then weightRow3RLLRL i else weightRow3RLLRR i
def weightRow3RLL (i : ℕ) : ℕ := if i < 288 then weightRow3RLLL i else weightRow3RLLR i
def weightRow3RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1004193389610105 else 1004254906279105
def weightRow3RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1003975452474105 else 1004027078868105
def weightRow3RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow3RLRLLLLL i else weightRow3RLRLLLLR i
def weightRow3RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1003727246806105 else 1003768958085105
def weightRow3RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1003471018428105 else 1003501589533105
def weightRow3RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow3RLRLLLRL i else weightRow3RLRLLLRR i
def weightRow3RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow3RLRLLLL i else weightRow3RLRLLLR i
def weightRow3RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1003180805019105 else 1003203993715105
def weightRow3RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1002871952434105 else 1002889999712105
def weightRow3RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow3RLRLLRLL i else weightRow3RLRLLRLR i
def weightRow3RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1002550547656105 else 1002559533295105
def weightRow3RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1002181354781105 else 1002181398641105
def weightRow3RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow3RLRLLRRL i else weightRow3RLRLLRRR i
def weightRow3RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow3RLRLLRL i else weightRow3RLRLLRR i
def weightRow3RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow3RLRLLL i else weightRow3RLRLLR i
def weightRow3RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1001759170333105 else 1001753593820105
def weightRow3RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1001288718196105 else 1001273723578105
def weightRow3RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow3RLRLRLLL i else weightRow3RLRLRLLR i
def weightRow3RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 1000765090182105 else 1000752790002105
def weightRow3RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 1000281671319105 else 1000266869488105
def weightRow3RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow3RLRLRLRL i else weightRow3RLRLRLRR i
def weightRow3RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow3RLRLRLL i else weightRow3RLRLRLR i
def weightRow3RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 999856651635105 else 999843358672105
def weightRow3RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 999408208001105 else 999396101307105
def weightRow3RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow3RLRLRRLL i else weightRow3RLRLRRLR i
def weightRow3RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 998967793772105 else 998957579018105
def weightRow3RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 998537770251105 else 998525769524105
def weightRow3RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow3RLRLRRRL i else weightRow3RLRLRRRR i
def weightRow3RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow3RLRLRRL i else weightRow3RLRLRRR i
def weightRow3RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow3RLRLRL i else weightRow3RLRLRR i
def weightRow3RLRL (i : ℕ) : ℕ := if i < 336 then weightRow3RLRLL i else weightRow3RLRLR i
def weightRow3RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 998118369896105 else 998102822963105
def weightRow3RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 997676269265105 else 997656742688105
def weightRow3RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow3RLRRLLLL i else weightRow3RLRRLLLR i
def weightRow3RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 997260420645105 else 997235818135105
def weightRow3RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 996934052589105 else 996908910600105
def weightRow3RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow3RLRRLLRL i else weightRow3RLRRLLRR i
def weightRow3RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow3RLRRLLL i else weightRow3RLRRLLR i
def weightRow3RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 996723488044105 else 996692913040105
def weightRow3RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 996631581771105 else 996599063914105
def weightRow3RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow3RLRRLRLL i else weightRow3RLRRLRLR i
def weightRow3RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 996660222120105 else 996624058796105
def weightRow3RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 996771706398105 else 996736231772105
def weightRow3RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow3RLRRLRRL i else weightRow3RLRRLRRR i
def weightRow3RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow3RLRRLRL i else weightRow3RLRRLRR i
def weightRow3RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow3RLRRLL i else weightRow3RLRRLR i
def weightRow3RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 996971471184105 else 996939690785105
def weightRow3RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 997236646682105 else 997207341763105
def weightRow3RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow3RLRRRLLL i else weightRow3RLRRRLLR i
def weightRow3RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 997552843309105 else 997528635512105
def weightRow3RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 997907707174105 else 997884314766105
def weightRow3RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow3RLRRRLRL i else weightRow3RLRRRLRR i
def weightRow3RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow3RLRRRLL i else weightRow3RLRRRLR i
def weightRow3RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 998257768521105 else 998238657594105
def weightRow3RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 998597367254105 else 998581200559105
def weightRow3RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow3RLRRRRLL i else weightRow3RLRRRRLR i
def weightRow3RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 998908239053105 else 998895517126105
def weightRow3RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 999194924946105 else 999184941879105
def weightRow3RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow3RLRRRRRL i else weightRow3RLRRRRRR i
def weightRow3RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow3RLRRRRL i else weightRow3RLRRRRR i
def weightRow3RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow3RLRRRL i else weightRow3RLRRRR i
def weightRow3RLRR (i : ℕ) : ℕ := if i < 368 then weightRow3RLRRL i else weightRow3RLRRR i
def weightRow3RLR (i : ℕ) : ℕ := if i < 352 then weightRow3RLRL i else weightRow3RLRR i
def weightRow3RL (i : ℕ) : ℕ := if i < 320 then weightRow3RLL i else weightRow3RLR i
def weightRow3RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 999453007458105 else 999445680903105
def weightRow3RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 999682083872105 else 999677389891105
def weightRow3RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow3RRLLLLLL i else weightRow3RRLLLLLR i
def weightRow3RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 999883510079105 else 999881482388105
def weightRow3RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 1000057777246105 else 1000057855180105
def weightRow3RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow3RRLLLLRL i else weightRow3RRLLLLRR i
def weightRow3RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow3RRLLLLL i else weightRow3RRLLLLR i
def weightRow3RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 1000208512502105 else 1000211281019105
def weightRow3RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 1000337677380105 else 1000341903889105
def weightRow3RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow3RRLLLRLL i else weightRow3RRLLLRLR i
def weightRow3RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 1000443561964105 else 1000448892967105
def weightRow3RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 1000537464022105 else 1000545199302105
def weightRow3RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow3RRLLLRRL i else weightRow3RRLLLRRR i
def weightRow3RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow3RRLLLRL i else weightRow3RRLLLRR i
def weightRow3RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow3RRLLLL i else weightRow3RRLLLR i
def weightRow3RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 1000608880469105 else 1000616323374105
def weightRow3RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 1000672547851105 else 1000683128086105
def weightRow3RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow3RRLLRLLL i else weightRow3RRLLRLLR i
def weightRow3RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000723413626105 else 1000732558580105
def weightRow3RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000762412037105 else 1000773841608105
def weightRow3RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow3RRLLRLRL i else weightRow3RRLLRLRR i
def weightRow3RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow3RRLLRLL i else weightRow3RRLLRLR i
def weightRow3RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000798708355105 else 1000810096124105
def weightRow3RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000817214119105 else 1000828565695105
def weightRow3RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow3RRLLRRLL i else weightRow3RRLLRRLR i
def weightRow3RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000834539109105 else 1000848241776105
def weightRow3RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000843002901105 else 1000853489120105
def weightRow3RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow3RRLLRRRL i else weightRow3RRLLRRRR i
def weightRow3RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow3RRLLRRL i else weightRow3RRLLRRR i
def weightRow3RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow3RRLLRL i else weightRow3RRLLRR i
def weightRow3RRLL (i : ℕ) : ℕ := if i < 400 then weightRow3RRLLL i else weightRow3RRLLR i
def weightRow3RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000835421899105 else 1000848157261105
def weightRow3RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000835190231105 else 1000845369703105
def weightRow3RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow3RRLRLLLL i else weightRow3RRLRLLLR i
def weightRow3RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000823984858105 else 1000834983604105
def weightRow3RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000807155534105 else 1000818990682105
def weightRow3RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow3RRLRLLRL i else weightRow3RRLRLLRR i
def weightRow3RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow3RRLRLLL i else weightRow3RRLRLLR i
def weightRow3RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000768526123105 else 1000780510689105
def weightRow3RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000712174546105 else 1000724233318105
def weightRow3RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow3RRLRLRLL i else weightRow3RRLRLRLR i
def weightRow3RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000678463220105 else 1000691782323105
def weightRow3RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000629508965105 else 1000642882225105
def weightRow3RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow3RRLRLRRL i else weightRow3RRLRLRRR i
def weightRow3RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow3RRLRLRL i else weightRow3RRLRLRR i
def weightRow3RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow3RRLRLL i else weightRow3RRLRLR i
def weightRow3RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000578153262105 else 1000587648355105
def weightRow3RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000513730402105 else 1000524232382105
def weightRow3RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow3RRLRRLLL i else weightRow3RRLRRLLR i
def weightRow3RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000451903612105 else 1000462013435105
def weightRow3RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000390789940105 else 1000400693958105
def weightRow3RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow3RRLRRLRL i else weightRow3RRLRRLRR i
def weightRow3RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow3RRLRRLL i else weightRow3RRLRRLR i
def weightRow3RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000319392097105 else 1000324708629105
def weightRow3RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000235638132105 else 1000240375722105
def weightRow3RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow3RRLRRRLL i else weightRow3RRLRRRLR i
def weightRow3RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000175611112105 else 1000181325431105
def weightRow3RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000125618374105 else 1000126940374105
def weightRow3RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow3RRLRRRRL i else weightRow3RRLRRRRR i
def weightRow3RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow3RRLRRRL i else weightRow3RRLRRRR i
def weightRow3RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow3RRLRRL i else weightRow3RRLRRR i
def weightRow3RRLR (i : ℕ) : ℕ := if i < 432 then weightRow3RRLRL i else weightRow3RRLRR i
def weightRow3RRL (i : ℕ) : ℕ := if i < 416 then weightRow3RRLL i else weightRow3RRLR i
def weightRow3RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 1000044593865105 else 1000044916857105
def weightRow3RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 999968154475105 else 999961643729105
def weightRow3RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow3RRRLLLLL i else weightRow3RRRLLLLR i
def weightRow3RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 999884011792105 else 999877143720105
def weightRow3RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 999804429932105 else 999798703489105
def weightRow3RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow3RRRLLLRL i else weightRow3RRRLLLRR i
def weightRow3RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow3RRRLLLL i else weightRow3RRRLLLR i
def weightRow3RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 999748309907105 else 999741032130105
def weightRow3RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 999689578908105 else 999682200107105
def weightRow3RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow3RRRLLRLL i else weightRow3RRRLLRLR i
def weightRow3RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 999662067080105 else 999661998609105
def weightRow3RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 999613241057105 else 999604750945105
def weightRow3RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow3RRRLLRRL i else weightRow3RRRLLRRR i
def weightRow3RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow3RRRLLRL i else weightRow3RRRLLRR i
def weightRow3RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow3RRRLLL i else weightRow3RRRLLR i
def weightRow3RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 999603153614105 else 999600279956105
def weightRow3RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 999625678561105 else 999628958242105
def weightRow3RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow3RRRLRLLL i else weightRow3RRRLRLLR i
def weightRow3RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999639708662105 else 999642807196105
def weightRow3RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999658342191105 else 999661227605105
def weightRow3RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow3RRRLRLRL i else weightRow3RRRLRLRR i
def weightRow3RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow3RRRLRLL i else weightRow3RRRLRLR i
def weightRow3RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999690046696105 else 999689526969105
def weightRow3RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999706994175105 else 999702900205105
def weightRow3RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow3RRRLRRLL i else weightRow3RRRLRRLR i
def weightRow3RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999750455866105 else 999736237384105
def weightRow3RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999763506505105 else 999767968628105
def weightRow3RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow3RRRLRRRL i else weightRow3RRRLRRRR i
def weightRow3RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow3RRRLRRL i else weightRow3RRRLRRR i
def weightRow3RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow3RRRLRL i else weightRow3RRRLRR i
def weightRow3RRRL (i : ℕ) : ℕ := if i < 464 then weightRow3RRRLL i else weightRow3RRRLR i
def weightRow3RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999832434559105 else 999821057494105
def weightRow3RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999876741651105 else 999867529561105
def weightRow3RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow3RRRRLLLL i else weightRow3RRRRLLLR i
def weightRow3RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999874407077105 else 999857536227105
def weightRow3RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999893009064105 else 999893646654105
def weightRow3RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow3RRRRLLRL i else weightRow3RRRRLLRR i
def weightRow3RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow3RRRRLLL i else weightRow3RRRRLLR i
def weightRow3RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999942850250105 else 999931804965105
def weightRow3RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 999965261464105 else 999962535308105
def weightRow3RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow3RRRRLRLL i else weightRow3RRRRLRLR i
def weightRow3RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 999966037076105 else 999952786383105
def weightRow3RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 999990535739105 else 999984787866105
def weightRow3RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow3RRRRLRRL i else weightRow3RRRRLRRR i
def weightRow3RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow3RRRRLRL i else weightRow3RRRRLRR i
def weightRow3RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow3RRRRLL i else weightRow3RRRRLR i
def weightRow3RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 1000042496773105 else 1000049790720105
def weightRow3RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 1000079396877105 else 1000080144923105
def weightRow3RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow3RRRRRLLL i else weightRow3RRRRRLLR i
def weightRow3RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 1000071746365105 else 1000065551221105
def weightRow3RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 1000078083601105 else 1000078789334105
def weightRow3RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow3RRRRRLRL i else weightRow3RRRRRLRR i
def weightRow3RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow3RRRRRLL i else weightRow3RRRRRLR i
def weightRow3RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 1000082038573105 else 1000083333803105
def weightRow3RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 1000080917297105 else 1000082268621105
def weightRow3RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow3RRRRRRLL i else weightRow3RRRRRRLR i
def weightRow3RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 1000045814565105 else 1000059579732105
def weightRow3RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 1000042159124105 else 1000056555826105
def weightRow3RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow3RRRRRRRL i else weightRow3RRRRRRRR i
def weightRow3RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow3RRRRRRL i else weightRow3RRRRRRR i
def weightRow3RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow3RRRRRL i else weightRow3RRRRRR i
def weightRow3RRRR (i : ℕ) : ℕ := if i < 496 then weightRow3RRRRL i else weightRow3RRRRR i
def weightRow3RRR (i : ℕ) : ℕ := if i < 480 then weightRow3RRRL i else weightRow3RRRR i
def weightRow3RR (i : ℕ) : ℕ := if i < 448 then weightRow3RRL i else weightRow3RRR i
def weightRow3R (i : ℕ) : ℕ := if i < 384 then weightRow3RL i else weightRow3RR i
def weightRow3 (i : ℕ) : ℕ := if i < 256 then weightRow3L i else weightRow3R i
def weightRow4LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 148250534432105 else 132600864764105
def weightRow4LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 240616069011105 else 263270992917105
def weightRow4LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow4LLLLLLLL i else weightRow4LLLLLLLR i
def weightRow4LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 274639663263105 else 265267352845105
def weightRow4LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 335442972886105 else 368147887525105
def weightRow4LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow4LLLLLLRL i else weightRow4LLLLLLRR i
def weightRow4LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow4LLLLLLL i else weightRow4LLLLLLR i
def weightRow4LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 508044176320105 else 444500013199105
def weightRow4LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 566682370914105 else 623405357751105
def weightRow4LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow4LLLLLRLL i else weightRow4LLLLLRLR i
def weightRow4LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 917665997550105 else 831699742319105
def weightRow4LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 773379335059105 else 835646877519105
def weightRow4LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow4LLLLLRRL i else weightRow4LLLLLRRR i
def weightRow4LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow4LLLLLRL i else weightRow4LLLLLRR i
def weightRow4LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow4LLLLLL i else weightRow4LLLLLR i
def weightRow4LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 614152863278105 else 561496511670105
def weightRow4LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 757101791770105 else 831657453987105
def weightRow4LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow4LLLLRLLL i else weightRow4LLLLRLLR i
def weightRow4LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 733604677475105 else 692848657625105
def weightRow4LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 661278128771105 else 714064091784105
def weightRow4LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow4LLLLRLRL i else weightRow4LLLLRLRR i
def weightRow4LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow4LLLLRLL i else weightRow4LLLLRLR i
def weightRow4LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 542295228190105 else 532906704254105
def weightRow4LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 633588992604105 else 639670670179105
def weightRow4LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow4LLLLRRLL i else weightRow4LLLLRRLR i
def weightRow4LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 584711606962105 else 554574510650105
def weightRow4LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 464237871230105 else 493337266857105
def weightRow4LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow4LLLLRRRL i else weightRow4LLLLRRRR i
def weightRow4LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow4LLLLRRL i else weightRow4LLLLRRR i
def weightRow4LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow4LLLLRL i else weightRow4LLLLRR i
def weightRow4LLLL (i : ℕ) : ℕ := if i < 16 then weightRow4LLLLL i else weightRow4LLLLR i
def weightRow4LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 489473420537105 else 492685668851105
def weightRow4LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 473688448848105 else 487831129319105
def weightRow4LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow4LLLRLLLL i else weightRow4LLLRLLLR i
def weightRow4LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 519635380674105 else 507140080635105
def weightRow4LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 673154119216105 else 699994683282105
def weightRow4LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow4LLLRLLRL i else weightRow4LLLRLLRR i
def weightRow4LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow4LLLRLLL i else weightRow4LLLRLLR i
def weightRow4LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 879130352928105 else 867458908404105
def weightRow4LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 998724118739105 else 1031198666707105
def weightRow4LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow4LLLRLRLL i else weightRow4LLLRLRLR i
def weightRow4LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 1062607814470105 else 962647558504105
def weightRow4LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 953846438474105 else 1018280271109105
def weightRow4LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow4LLLRLRRL i else weightRow4LLLRLRRR i
def weightRow4LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow4LLLRLRL i else weightRow4LLLRLRR i
def weightRow4LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow4LLLRLL i else weightRow4LLLRLR i
def weightRow4LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 947093007332105 else 924973267930105
def weightRow4LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 650348330640105 else 670658361395105
def weightRow4LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow4LLLRRLLL i else weightRow4LLLRRLLR i
def weightRow4LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 649453450947105 else 622675481193105
def weightRow4LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 638928132705105 else 632633835539105
def weightRow4LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow4LLLRRLRL i else weightRow4LLLRRLRR i
def weightRow4LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow4LLLRRLL i else weightRow4LLLRRLR i
def weightRow4LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 724723798801105 else 684691430319105
def weightRow4LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 725186082302105 else 688718705418105
def weightRow4LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow4LLLRRRLL i else weightRow4LLLRRRLR i
def weightRow4LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 737612724486105 else 763464986658105
def weightRow4LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 828416003808105 else 830421081079105
def weightRow4LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow4LLLRRRRL i else weightRow4LLLRRRRR i
def weightRow4LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow4LLLRRRL i else weightRow4LLLRRRR i
def weightRow4LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow4LLLRRL i else weightRow4LLLRRR i
def weightRow4LLLR (i : ℕ) : ℕ := if i < 48 then weightRow4LLLRL i else weightRow4LLLRR i
def weightRow4LLL (i : ℕ) : ℕ := if i < 32 then weightRow4LLLL i else weightRow4LLLR i
def weightRow4LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 843977938454105 else 840781853979105
def weightRow4LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 802135538183105 else 774640391657105
def weightRow4LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow4LLRLLLLL i else weightRow4LLRLLLLR i
def weightRow4LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 750687221548105 else 785650441079105
def weightRow4LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 769086695570105 else 808787829058105
def weightRow4LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow4LLRLLLRL i else weightRow4LLRLLLRR i
def weightRow4LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow4LLRLLLL i else weightRow4LLRLLLR i
def weightRow4LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 738932997516105 else 745615718954105
def weightRow4LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 750248978341105 else 777936571526105
def weightRow4LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow4LLRLLRLL i else weightRow4LLRLLRLR i
def weightRow4LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 820435197605105 else 801150974351105
def weightRow4LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 1102020435148105 else 1125213468165105
def weightRow4LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow4LLRLLRRL i else weightRow4LLRLLRRR i
def weightRow4LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow4LLRLLRL i else weightRow4LLRLLRR i
def weightRow4LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow4LLRLLL i else weightRow4LLRLLR i
def weightRow4LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 1228460384683105 else 1164454236936105
def weightRow4LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 1207064387914105 else 1308011096058105
def weightRow4LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow4LLRLRLLL i else weightRow4LLRLRLLR i
def weightRow4LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 1310590941288105 else 1280171839847105
def weightRow4LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 1180882279024105 else 1194318473116105
def weightRow4LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow4LLRLRLRL i else weightRow4LLRLRLRR i
def weightRow4LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow4LLRLRLL i else weightRow4LLRLRLR i
def weightRow4LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 1042810222175105 else 1017523394076105
def weightRow4LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 874171363494105 else 888024837380105
def weightRow4LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow4LLRLRRLL i else weightRow4LLRLRRLR i
def weightRow4LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 876146082319105 else 863354944832105
def weightRow4LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 902386952097105 else 900274716844105
def weightRow4LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow4LLRLRRRL i else weightRow4LLRLRRRR i
def weightRow4LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow4LLRLRRL i else weightRow4LLRLRRR i
def weightRow4LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow4LLRLRL i else weightRow4LLRLRR i
def weightRow4LLRL (i : ℕ) : ℕ := if i < 80 then weightRow4LLRLL i else weightRow4LLRLR i
def weightRow4LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 924849602794105 else 896363903595105
def weightRow4LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 1009203278435105 else 1039980995216105
def weightRow4LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow4LLRRLLLL i else weightRow4LLRRLLLR i
def weightRow4LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1120066974686105 else 1115005430151105
def weightRow4LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 1039128404427105 else 1049610294708105
def weightRow4LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow4LLRRLLRL i else weightRow4LLRRLLRR i
def weightRow4LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow4LLRRLLL i else weightRow4LLRRLLR i
def weightRow4LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 1247680342728105 else 1195324609624105
def weightRow4LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1256785335989105 else 1297792142272105
def weightRow4LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow4LLRRLRLL i else weightRow4LLRRLRLR i
def weightRow4LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1428228303462105 else 1353398648654105
def weightRow4LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 1189156687928105 else 1241193703449105
def weightRow4LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow4LLRRLRRL i else weightRow4LLRRLRRR i
def weightRow4LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow4LLRRLRL i else weightRow4LLRRLRR i
def weightRow4LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow4LLRRLL i else weightRow4LLRRLR i
def weightRow4LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1494947032129105 else 1431895173091105
def weightRow4LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 1527353526399105 else 1612897336406105
def weightRow4LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow4LLRRRLLL i else weightRow4LLRRRLLR i
def weightRow4LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 1352663186562105 else 1295971006891105
def weightRow4LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 1201841515632105 else 1265520377836105
def weightRow4LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow4LLRRRLRL i else weightRow4LLRRRLRR i
def weightRow4LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow4LLRRRLL i else weightRow4LLRRRLR i
def weightRow4LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 1150020361085105 else 1117931481196105
def weightRow4LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 1069254225632105 else 1078890360296105
def weightRow4LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow4LLRRRRLL i else weightRow4LLRRRRLR i
def weightRow4LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 1088077372965105 else 1065484812122105
def weightRow4LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 976486596753105 else 992086638142105
def weightRow4LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow4LLRRRRRL i else weightRow4LLRRRRRR i
def weightRow4LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow4LLRRRRL i else weightRow4LLRRRRR i
def weightRow4LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow4LLRRRL i else weightRow4LLRRRR i
def weightRow4LLRR (i : ℕ) : ℕ := if i < 112 then weightRow4LLRRL i else weightRow4LLRRR i
def weightRow4LLR (i : ℕ) : ℕ := if i < 96 then weightRow4LLRL i else weightRow4LLRR i
def weightRow4LL (i : ℕ) : ℕ := if i < 64 then weightRow4LLL i else weightRow4LLR i
def weightRow4LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 859136859176105 else 859328140790105
def weightRow4LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 870244227264105 else 870677197580105
def weightRow4LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow4LRLLLLLL i else weightRow4LRLLLLLR i
def weightRow4LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 880076600253105 else 880177705258105
def weightRow4LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 889541905035105 else 889784528188105
def weightRow4LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow4LRLLLLRL i else weightRow4LRLLLLRR i
def weightRow4LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow4LRLLLLL i else weightRow4LRLLLLR i
def weightRow4LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 898188044237105 else 897929823910105
def weightRow4LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 904281790516105 else 905019865140105
def weightRow4LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow4LRLLLRLL i else weightRow4LRLLLRLR i
def weightRow4LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 909553601762105 else 909400125650105
def weightRow4LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 909438642580105 else 910608936052105
def weightRow4LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow4LRLLLRRL i else weightRow4LRLLLRRR i
def weightRow4LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow4LRLLLRL i else weightRow4LRLLLRR i
def weightRow4LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow4LRLLLL i else weightRow4LRLLLR i
def weightRow4LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 911554711510105 else 911797772018105
def weightRow4LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 916205186351105 else 917258025523105
def weightRow4LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow4LRLLRLLL i else weightRow4LRLLRLLR i
def weightRow4LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 918688831049105 else 918599796825105
def weightRow4LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 921586525297105 else 922125261204105
def weightRow4LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow4LRLLRLRL i else weightRow4LRLLRLRR i
def weightRow4LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow4LRLLRLL i else weightRow4LRLLRLR i
def weightRow4LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 925650121888105 else 925392189207105
def weightRow4LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 931645541961105 else 931518153322105
def weightRow4LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow4LRLLRRLL i else weightRow4LRLLRRLR i
def weightRow4LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 936304338939105 else 936076341983105
def weightRow4LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 941797740828105 else 942041508020105
def weightRow4LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow4LRLLRRRL i else weightRow4LRLLRRRR i
def weightRow4LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow4LRLLRRL i else weightRow4LRLLRRR i
def weightRow4LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow4LRLLRL i else weightRow4LRLLRR i
def weightRow4LRLL (i : ℕ) : ℕ := if i < 144 then weightRow4LRLLL i else weightRow4LRLLR i
def weightRow4LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 949259843392105 else 949050267110105
def weightRow4LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 956444705719105 else 956181288561105
def weightRow4LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow4LRLRLLLL i else weightRow4LRLRLLLR i
def weightRow4LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 963984890354105 else 963500574740105
def weightRow4LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 970921756378105 else 970627981443105
def weightRow4LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow4LRLRLLRL i else weightRow4LRLRLLRR i
def weightRow4LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow4LRLRLLL i else weightRow4LRLRLLR i
def weightRow4LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 975570913661105 else 974855286134105
def weightRow4LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 977079062795105 else 976527115317105
def weightRow4LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow4LRLRLRLL i else weightRow4LRLRLRLR i
def weightRow4LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 976732046957105 else 975672572433105
def weightRow4LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 975398328724105 else 975873808337105
def weightRow4LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow4LRLRLRRL i else weightRow4LRLRLRRR i
def weightRow4LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow4LRLRLRL i else weightRow4LRLRLRR i
def weightRow4LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow4LRLRLL i else weightRow4LRLRLR i
def weightRow4LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 975737948054105 else 975207791197105
def weightRow4LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 976192025992105 else 976005404177105
def weightRow4LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow4LRLRRLLL i else weightRow4LRLRRLLR i
def weightRow4LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 981280736133105 else 980776062284105
def weightRow4LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 986464841936105 else 986374485375105
def weightRow4LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow4LRLRRLRL i else weightRow4LRLRRLRR i
def weightRow4LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow4LRLRRLL i else weightRow4LRLRRLR i
def weightRow4LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 991892252317105 else 991899168695105
def weightRow4LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 996067535586105 else 996694276331105
def weightRow4LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow4LRLRRRLL i else weightRow4LRLRRRLR i
def weightRow4LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 1000296991520105 else 1001507170138105
def weightRow4LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1004398564332105 else 1005229481695105
def weightRow4LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow4LRLRRRRL i else weightRow4LRLRRRRR i
def weightRow4LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow4LRLRRRL i else weightRow4LRLRRRR i
def weightRow4LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow4LRLRRL i else weightRow4LRLRRR i
def weightRow4LRLR (i : ℕ) : ℕ := if i < 176 then weightRow4LRLRL i else weightRow4LRLRR i
def weightRow4LRL (i : ℕ) : ℕ := if i < 160 then weightRow4LRLL i else weightRow4LRLR i
def weightRow4LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1007152910067105 else 1007960143205105
def weightRow4LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1009704664930105 else 1010569136874105
def weightRow4LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow4LRRLLLLL i else weightRow4LRRLLLLR i
def weightRow4LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1012949545504105 else 1014253228816105
def weightRow4LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1017046742882105 else 1017824544302105
def weightRow4LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow4LRRLLLRL i else weightRow4LRRLLLRR i
def weightRow4LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow4LRRLLLL i else weightRow4LRRLLLR i
def weightRow4LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1020923068939105 else 1021090632953105
def weightRow4LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1025322717379105 else 1025399170965105
def weightRow4LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow4LRRLLRLL i else weightRow4LRRLLRLR i
def weightRow4LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1029613316978105 else 1029272160768105
def weightRow4LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1032881327845105 else 1032822698897105
def weightRow4LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow4LRRLLRRL i else weightRow4LRRLLRRR i
def weightRow4LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow4LRRLLRL i else weightRow4LRRLLRR i
def weightRow4LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow4LRRLLL i else weightRow4LRRLLR i
def weightRow4LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1031796644286105 else 1031373035218105
def weightRow4LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1028725781967105 else 1029295402311105
def weightRow4LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow4LRRLRLLL i else weightRow4LRRLRLLR i
def weightRow4LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1025938347612105 else 1024932628978105
def weightRow4LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1021495713284105 else 1020948235692105
def weightRow4LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow4LRRLRLRL i else weightRow4LRRLRLRR i
def weightRow4LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow4LRRLRLL i else weightRow4LRRLRLR i
def weightRow4LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1019005006487105 else 1018238524901105
def weightRow4LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1018633101322105 else 1018263615122105
def weightRow4LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow4LRRLRRLL i else weightRow4LRRLRRLR i
def weightRow4LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1020893473433105 else 1020298156087105
def weightRow4LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1023157712751105 else 1022749258924105
def weightRow4LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow4LRRLRRRL i else weightRow4LRRLRRRR i
def weightRow4LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow4LRRLRRL i else weightRow4LRRLRRR i
def weightRow4LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow4LRRLRL i else weightRow4LRRLRR i
def weightRow4LRRL (i : ℕ) : ℕ := if i < 208 then weightRow4LRRLL i else weightRow4LRRLR i
def weightRow4LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 1025038791267105 else 1024662936467105
def weightRow4LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 1026607786667105 else 1026667934158105
def weightRow4LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow4LRRRLLLL i else weightRow4LRRRLLLR i
def weightRow4LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 1026879150285105 else 1026450996563105
def weightRow4LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 1025422186188105 else 1025075327284105
def weightRow4LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow4LRRRLLRL i else weightRow4LRRRLLRR i
def weightRow4LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow4LRRRLLL i else weightRow4LRRRLLR i
def weightRow4LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 1025198854729105 else 1024683789459105
def weightRow4LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 1021727338007105 else 1022022028934105
def weightRow4LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow4LRRRLRLL i else weightRow4LRRRLRLR i
def weightRow4LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 1018053119129105 else 1017700893941105
def weightRow4LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 1011645115024105 else 1012474821267105
def weightRow4LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow4LRRRLRRL i else weightRow4LRRRLRRR i
def weightRow4LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow4LRRRLRL i else weightRow4LRRRLRR i
def weightRow4LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow4LRRRLL i else weightRow4LRRRLR i
def weightRow4LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 1008862859449105 else 1008887696291105
def weightRow4LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 1001278039708105 else 1002264480058105
def weightRow4LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow4LRRRRLLL i else weightRow4LRRRRLLR i
def weightRow4LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 993053617040105 else 992738262488105
def weightRow4LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 987444314795105 else 988002963725105
def weightRow4LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow4LRRRRLRL i else weightRow4LRRRRLRR i
def weightRow4LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow4LRRRRLL i else weightRow4LRRRRLR i
def weightRow4LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 984091868240105 else 983671475166105
def weightRow4LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 981500684768105 else 981577365902105
def weightRow4LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow4LRRRRRLL i else weightRow4LRRRRRLR i
def weightRow4LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 980130599672105 else 980053220011105
def weightRow4LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 978449194439105 else 978719251772105
def weightRow4LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow4LRRRRRRL i else weightRow4LRRRRRRR i
def weightRow4LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow4LRRRRRL i else weightRow4LRRRRRR i
def weightRow4LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow4LRRRRL i else weightRow4LRRRRR i
def weightRow4LRRR (i : ℕ) : ℕ := if i < 240 then weightRow4LRRRL i else weightRow4LRRRR i
def weightRow4LRR (i : ℕ) : ℕ := if i < 224 then weightRow4LRRL i else weightRow4LRRR i
def weightRow4LR (i : ℕ) : ℕ := if i < 192 then weightRow4LRL i else weightRow4LRR i
def weightRow4L (i : ℕ) : ℕ := if i < 128 then weightRow4LL i else weightRow4LR i
def weightRow4RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 978479391650105 else 978518895157105
def weightRow4RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 980343986503105 else 980380730087105
def weightRow4RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow4RLLLLLLL i else weightRow4RLLLLLLR i
def weightRow4RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 982064252197105 else 982094385581105
def weightRow4RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 983657438664105 else 983686326058105
def weightRow4RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow4RLLLLLRL i else weightRow4RLLLLLRR i
def weightRow4RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow4RLLLLLL i else weightRow4RLLLLLR i
def weightRow4RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 985127460892105 else 985152947463105
def weightRow4RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 986485377386105 else 986515189523105
def weightRow4RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow4RLLLLRLL i else weightRow4RLLLLRLR i
def weightRow4RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 987769436771105 else 987787732056105
def weightRow4RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 988991196459105 else 989012096852105
def weightRow4RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow4RLLLLRRL i else weightRow4RLLLLRRR i
def weightRow4RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow4RLLLLRL i else weightRow4RLLLLRR i
def weightRow4RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow4RLLLLL i else weightRow4RLLLLR i
def weightRow4RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 990233394557105 else 990236552604105
def weightRow4RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 991462009527105 else 991461186901105
def weightRow4RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow4RLLLRLLL i else weightRow4RLLLRLLR i
def weightRow4RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 992637145006105 else 992619879361105
def weightRow4RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 993792001846105 else 993775715334105
def weightRow4RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow4RLLLRLRL i else weightRow4RLLLRLRR i
def weightRow4RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow4RLLLRLL i else weightRow4RLLLRLR i
def weightRow4RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 994919582980105 else 994894750385105
def weightRow4RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 996001265050105 else 995979746343105
def weightRow4RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow4RLLLRRLL i else weightRow4RLLLRRLR i
def weightRow4RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 997006174731105 else 996986364312105
def weightRow4RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 997953993427105 else 997937521297105
def weightRow4RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow4RLLLRRRL i else weightRow4RLLLRRRR i
def weightRow4RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow4RLLLRRL i else weightRow4RLLLRRR i
def weightRow4RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow4RLLLRL i else weightRow4RLLLRR i
def weightRow4RLLL (i : ℕ) : ℕ := if i < 272 then weightRow4RLLLL i else weightRow4RLLLR i
def weightRow4RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 998830841252105 else 998810354553105
def weightRow4RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 999604808285105 else 999587362133105
def weightRow4RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow4RLLRLLLL i else weightRow4RLLRLLLR i
def weightRow4RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 1000278547795105 else 1000265087033105
def weightRow4RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1000845213160105 else 1000839104446105
def weightRow4RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow4RLLRLLRL i else weightRow4RLLRLLRR i
def weightRow4RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow4RLLRLLL i else weightRow4RLLRLLR i
def weightRow4RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1001312444714105 else 1001310800131105
def weightRow4RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1001714146721105 else 1001723517528105
def weightRow4RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow4RLLRLRLL i else weightRow4RLLRLRLR i
def weightRow4RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1002098485063105 else 1002116685532105
def weightRow4RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1002494566568105 else 1002529317400105
def weightRow4RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow4RLLRLRRL i else weightRow4RLLRLRRR i
def weightRow4RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow4RLLRLRL i else weightRow4RLLRLRR i
def weightRow4RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow4RLLRLL i else weightRow4RLLRLR i
def weightRow4RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1002917546761105 else 1002945524749105
def weightRow4RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1003341966970105 else 1003378740931105
def weightRow4RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow4RLLRRLLL i else weightRow4RLLRRLLR i
def weightRow4RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1003765680785105 else 1003806170031105
def weightRow4RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1004116514644105 else 1004165484083105
def weightRow4RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow4RLLRRLRL i else weightRow4RLLRRLRR i
def weightRow4RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow4RLLRRLL i else weightRow4RLLRRLR i
def weightRow4RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1004391763219105 else 1004442854849105
def weightRow4RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1004586667583105 else 1004638308795105
def weightRow4RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow4RLLRRRLL i else weightRow4RLLRRRLR i
def weightRow4RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1004719299964105 else 1004762032037105
def weightRow4RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1004787974086105 else 1004812290738105
def weightRow4RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow4RLLRRRRL i else weightRow4RLLRRRRR i
def weightRow4RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow4RLLRRRL i else weightRow4RLLRRRR i
def weightRow4RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow4RLLRRL i else weightRow4RLLRRR i
def weightRow4RLLR (i : ℕ) : ℕ := if i < 304 then weightRow4RLLRL i else weightRow4RLLRR i
def weightRow4RLL (i : ℕ) : ℕ := if i < 288 then weightRow4RLLL i else weightRow4RLLR i
def weightRow4RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1004793563846105 else 1004805182441105
def weightRow4RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1004756392613105 else 1004755314183105
def weightRow4RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow4RLRLLLLL i else weightRow4RLRLLLLR i
def weightRow4RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1004678419440105 else 1004663873216105
def weightRow4RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1004548662670105 else 1004513619977105
def weightRow4RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow4RLRLLLRL i else weightRow4RLRLLLRR i
def weightRow4RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow4RLRLLLL i else weightRow4RLRLLLR i
def weightRow4RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1004353565670105 else 1004306188333105
def weightRow4RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1004095244843105 else 1004044711843105
def weightRow4RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow4RLRLLRLL i else weightRow4RLRLLRLR i
def weightRow4RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1003764723601105 else 1003712218503105
def weightRow4RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1003362086221105 else 1003313998102105
def weightRow4RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow4RLRLLRRL i else weightRow4RLRLLRRR i
def weightRow4RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow4RLRLLRL i else weightRow4RLRLLRR i
def weightRow4RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow4RLRLLL i else weightRow4RLRLLR i
def weightRow4RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1002903463245105 else 1002855567059105
def weightRow4RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1002455586926105 else 1002413493829105
def weightRow4RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow4RLRLRLLL i else weightRow4RLRLRLLR i
def weightRow4RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 1002048849291105 else 1001996978272105
def weightRow4RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 1001679172667105 else 1001642317043105
def weightRow4RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow4RLRLRLRL i else weightRow4RLRLRLRR i
def weightRow4RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow4RLRLRLL i else weightRow4RLRLRLR i
def weightRow4RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 1001373044713105 else 1001344159331105
def weightRow4RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 1001100800691105 else 1001083525993105
def weightRow4RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow4RLRLRRLL i else weightRow4RLRLRRLR i
def weightRow4RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 1000829614059105 else 1000817399847105
def weightRow4RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 1000518043610105 else 1000515056355105
def weightRow4RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow4RLRLRRRL i else weightRow4RLRLRRRR i
def weightRow4RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow4RLRLRRL i else weightRow4RLRLRRR i
def weightRow4RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow4RLRLRL i else weightRow4RLRLRR i
def weightRow4RLRL (i : ℕ) : ℕ := if i < 336 then weightRow4RLRLL i else weightRow4RLRLR i
def weightRow4RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 1000166077363105 else 1000169505261105
def weightRow4RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 999778728124105 else 999788026234105
def weightRow4RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow4RLRRLLLL i else weightRow4RLRRLLLR i
def weightRow4RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 999360273519105 else 999368904595105
def weightRow4RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 998931358060105 else 998947100849105
def weightRow4RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow4RLRRLLRL i else weightRow4RLRRLLRR i
def weightRow4RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow4RLRRLLL i else weightRow4RLRRLLR i
def weightRow4RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 998518512257105 else 998540062806105
def weightRow4RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 998102150787105 else 998132236356105
def weightRow4RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow4RLRRLRLL i else weightRow4RLRRLRLR i
def weightRow4RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 997732834188105 else 997758725851105
def weightRow4RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 997415146332105 else 997447439732105
def weightRow4RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow4RLRRLRRL i else weightRow4RLRRLRRR i
def weightRow4RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow4RLRRLRL i else weightRow4RLRRLRR i
def weightRow4RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow4RLRRLL i else weightRow4RLRRLR i
def weightRow4RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 997192610030105 else 997212035313105
def weightRow4RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 997009636778105 else 997029252307105
def weightRow4RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow4RLRRRLLL i else weightRow4RLRRRLLR i
def weightRow4RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 996941994619105 else 996946601328105
def weightRow4RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 997000697590105 else 997010397314105
def weightRow4RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow4RLRRRLRL i else weightRow4RLRRRLRR i
def weightRow4RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow4RLRRRLL i else weightRow4RLRRRLR i
def weightRow4RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 997148425523105 else 997149153449105
def weightRow4RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 997350506724105 else 997358189267105
def weightRow4RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow4RLRRRRLL i else weightRow4RLRRRRLR i
def weightRow4RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 997596495765105 else 997602809827105
def weightRow4RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 997865806773105 else 997873924333105
def weightRow4RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow4RLRRRRRL i else weightRow4RLRRRRRR i
def weightRow4RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow4RLRRRRL i else weightRow4RLRRRRR i
def weightRow4RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow4RLRRRL i else weightRow4RLRRRR i
def weightRow4RLRR (i : ℕ) : ℕ := if i < 368 then weightRow4RLRRL i else weightRow4RLRRR i
def weightRow4RLR (i : ℕ) : ℕ := if i < 352 then weightRow4RLRL i else weightRow4RLRR i
def weightRow4RL (i : ℕ) : ℕ := if i < 320 then weightRow4RLL i else weightRow4RLR i
def weightRow4RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 998163168459105 else 998165495428105
def weightRow4RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 998466880934105 else 998469799351105
def weightRow4RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow4RRLLLLLL i else weightRow4RRLLLLLR i
def weightRow4RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 998747371094105 else 998748850213105
def weightRow4RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 999000341090105 else 999002670862105
def weightRow4RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow4RRLLLLRL i else weightRow4RRLLLLRR i
def weightRow4RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow4RRLLLLL i else weightRow4RRLLLLR i
def weightRow4RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 999233316342105 else 999232922198105
def weightRow4RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 999446609972105 else 999445872860105
def weightRow4RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow4RRLLLRLL i else weightRow4RRLLLRLR i
def weightRow4RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 999645982291105 else 999646057915105
def weightRow4RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 999835109345105 else 999832048627105
def weightRow4RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow4RRLLLRRL i else weightRow4RRLLLRRR i
def weightRow4RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow4RRLLLRL i else weightRow4RRLLLRR i
def weightRow4RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow4RRLLLL i else weightRow4RRLLLR i
def weightRow4RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 999983942561105 else 999985365152105
def weightRow4RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 1000132937005105 else 1000129060144105
def weightRow4RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow4RRLLRLLL i else weightRow4RRLLRLLR i
def weightRow4RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000267625355105 else 1000268168782105
def weightRow4RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000396436506105 else 1000390801143105
def weightRow4RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow4RRLLRLRL i else weightRow4RRLLRLRR i
def weightRow4RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow4RRLLRLL i else weightRow4RRLLRLR i
def weightRow4RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000503150731105 else 1000503373430105
def weightRow4RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000583174199105 else 1000578987651105
def weightRow4RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow4RRLLRRLL i else weightRow4RRLLRRLR i
def weightRow4RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000662058529105 else 1000665529137105
def weightRow4RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000722542754105 else 1000722386360105
def weightRow4RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow4RRLLRRRL i else weightRow4RRLLRRRR i
def weightRow4RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow4RRLLRRL i else weightRow4RRLLRRR i
def weightRow4RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow4RRLLRL i else weightRow4RRLLRR i
def weightRow4RRLL (i : ℕ) : ℕ := if i < 400 then weightRow4RRLLL i else weightRow4RRLLR i
def weightRow4RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000767778801105 else 1000770196106105
def weightRow4RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000801822934105 else 1000800951729105
def weightRow4RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow4RRLRLLLL i else weightRow4RRLRLLLR i
def weightRow4RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000815844498105 else 1000818433446105
def weightRow4RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000836468092105 else 1000835478927105
def weightRow4RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow4RRLRLLRL i else weightRow4RRLRLLRR i
def weightRow4RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow4RRLRLLL i else weightRow4RRLRLLR i
def weightRow4RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000832368700105 else 1000836657563105
def weightRow4RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000807473456105 else 1000814003802105
def weightRow4RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow4RRLRLRLL i else weightRow4RRLRLRLR i
def weightRow4RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000789641581105 else 1000799208858105
def weightRow4RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000778376711105 else 1000777887508105
def weightRow4RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow4RRLRLRRL i else weightRow4RRLRLRRR i
def weightRow4RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow4RRLRLRL i else weightRow4RRLRLRR i
def weightRow4RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow4RRLRLL i else weightRow4RRLRLR i
def weightRow4RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000753344861105 else 1000762880612105
def weightRow4RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000733427379105 else 1000729499896105
def weightRow4RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow4RRLRRLLL i else weightRow4RRLRRLLR i
def weightRow4RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000685043021105 else 1000693906792105
def weightRow4RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000634471782105 else 1000627694688105
def weightRow4RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow4RRLRRLRL i else weightRow4RRLRRLRR i
def weightRow4RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow4RRLRRLL i else weightRow4RRLRRLR i
def weightRow4RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000574854648105 else 1000571799262105
def weightRow4RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000521214654105 else 1000513570198105
def weightRow4RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow4RRLRRRLL i else weightRow4RRLRRRLR i
def weightRow4RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000453065171105 else 1000453939441105
def weightRow4RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000385028487105 else 1000375123850105
def weightRow4RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow4RRLRRRRL i else weightRow4RRLRRRRR i
def weightRow4RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow4RRLRRRL i else weightRow4RRLRRRR i
def weightRow4RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow4RRLRRL i else weightRow4RRLRRR i
def weightRow4RRLR (i : ℕ) : ℕ := if i < 432 then weightRow4RRLRL i else weightRow4RRLRR i
def weightRow4RRL (i : ℕ) : ℕ := if i < 416 then weightRow4RRLL i else weightRow4RRLR i
def weightRow4RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 1000308056020105 else 1000310280178105
def weightRow4RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 1000255966851105 else 1000239282669105
def weightRow4RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow4RRRLLLLL i else weightRow4RRRLLLLR i
def weightRow4RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 1000164261671105 else 1000163026942105
def weightRow4RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 1000108284850105 else 1000098522774105
def weightRow4RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow4RRRLLLRL i else weightRow4RRRLLLRR i
def weightRow4RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow4RRRLLLL i else weightRow4RRRLLLR i
def weightRow4RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 1000082293140105 else 1000092668732105
def weightRow4RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 1000047517115105 else 1000041146273105
def weightRow4RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow4RRRLLRLL i else weightRow4RRRLLRLR i
def weightRow4RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 1000013710461105 else 1000008318516105
def weightRow4RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 999953075154105 else 999962597636105
def weightRow4RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow4RRRLLRRL i else weightRow4RRRLLRRR i
def weightRow4RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow4RRRLLRL i else weightRow4RRRLLRR i
def weightRow4RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow4RRRLLL i else weightRow4RRRLLR i
def weightRow4RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 999987030511105 else 999995550083105
def weightRow4RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 1000001267241105 else 1000005105761105
def weightRow4RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow4RRRLRLLL i else weightRow4RRRLRLLR i
def weightRow4RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999978611775105 else 999972497239105
def weightRow4RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999940960094105 else 999948085292105
def weightRow4RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow4RRRLRLRL i else weightRow4RRRLRLRR i
def weightRow4RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow4RRRLRLL i else weightRow4RRRLRLR i
def weightRow4RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999917360926105 else 999913692348105
def weightRow4RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999883687490105 else 999881725758105
def weightRow4RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow4RRRLRRLL i else weightRow4RRRLRRLR i
def weightRow4RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999835056276105 else 999812235617105
def weightRow4RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999771101116105 else 999782227216105
def weightRow4RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow4RRRLRRRL i else weightRow4RRRLRRRR i
def weightRow4RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow4RRRLRRL i else weightRow4RRRLRRR i
def weightRow4RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow4RRRLRL i else weightRow4RRRLRR i
def weightRow4RRRL (i : ℕ) : ℕ := if i < 464 then weightRow4RRRLL i else weightRow4RRRLR i
def weightRow4RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999757027159105 else 999755205448105
def weightRow4RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999711155462105 else 999714267160105
def weightRow4RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow4RRRRLLLL i else weightRow4RRRRLLLR i
def weightRow4RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999681586312105 else 999686789393105
def weightRow4RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999706247546105 else 999719248198105
def weightRow4RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow4RRRRLLRL i else weightRow4RRRRLLRR i
def weightRow4RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow4RRRRLLL i else weightRow4RRRRLLR i
def weightRow4RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999721026439105 else 999724659781105
def weightRow4RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 999692123478105 else 999707551449105
def weightRow4RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow4RRRRLRLL i else weightRow4RRRRLRLR i
def weightRow4RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 999673080527105 else 999677384894105
def weightRow4RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 999705840908105 else 999728674690105
def weightRow4RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow4RRRRLRRL i else weightRow4RRRRLRRR i
def weightRow4RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow4RRRRLRL i else weightRow4RRRRLRR i
def weightRow4RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow4RRRRLL i else weightRow4RRRRLR i
def weightRow4RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 999733199541105 else 999727901323105
def weightRow4RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 999737294197105 else 999769865222105
def weightRow4RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow4RRRRRLLL i else weightRow4RRRRRLLR i
def weightRow4RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 999768430831105 else 999762803276105
def weightRow4RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 999734558720105 else 999749028257105
def weightRow4RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow4RRRRRLRL i else weightRow4RRRRRLRR i
def weightRow4RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow4RRRRRLL i else weightRow4RRRRRLR i
def weightRow4RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 999815541563105 else 999789073928105
def weightRow4RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 999831825534105 else 999860182545105
def weightRow4RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow4RRRRRRLL i else weightRow4RRRRRRLR i
def weightRow4RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 999885430501105 else 999876142008105
def weightRow4RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 999795956557105 else 999830067099105
def weightRow4RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow4RRRRRRRL i else weightRow4RRRRRRRR i
def weightRow4RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow4RRRRRRL i else weightRow4RRRRRRR i
def weightRow4RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow4RRRRRL i else weightRow4RRRRRR i
def weightRow4RRRR (i : ℕ) : ℕ := if i < 496 then weightRow4RRRRL i else weightRow4RRRRR i
def weightRow4RRR (i : ℕ) : ℕ := if i < 480 then weightRow4RRRL i else weightRow4RRRR i
def weightRow4RR (i : ℕ) : ℕ := if i < 448 then weightRow4RRL i else weightRow4RRR i
def weightRow4R (i : ℕ) : ℕ := if i < 384 then weightRow4RL i else weightRow4RR i
def weightRow4 (i : ℕ) : ℕ := if i < 256 then weightRow4L i else weightRow4R i
def weightRow5LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 254193110786105 else 254343788452105
def weightRow5LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 223857081407105 else 219706560709105
def weightRow5LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow5LLLLLLLL i else weightRow5LLLLLLLR i
def weightRow5LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 255946275487105 else 263576291547105
def weightRow5LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 348506405767105 else 377860556084105
def weightRow5LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow5LLLLLLRL i else weightRow5LLLLLLRR i
def weightRow5LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow5LLLLLLL i else weightRow5LLLLLLR i
def weightRow5LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 413821417269105 else 432451857361105
def weightRow5LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 550970402931105 else 520945017435105
def weightRow5LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow5LLLLLRLL i else weightRow5LLLLLRLR i
def weightRow5LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 216641082280105 else 216885503337105
def weightRow5LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 417829593320105 else 419279264680105
def weightRow5LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow5LLLLLRRL i else weightRow5LLLLLRRR i
def weightRow5LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow5LLLLLRL i else weightRow5LLLLLRR i
def weightRow5LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow5LLLLLL i else weightRow5LLLLLR i
def weightRow5LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 353128659565105 else 332737515370105
def weightRow5LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 422284648318105 else 428344289214105
def weightRow5LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow5LLLLRLLL i else weightRow5LLLLRLLR i
def weightRow5LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 564112212653105 else 543523461670105
def weightRow5LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 678846989859105 else 713856652181105
def weightRow5LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow5LLLLRLRL i else weightRow5LLLLRLRR i
def weightRow5LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow5LLLLRLL i else weightRow5LLLLRLR i
def weightRow5LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 745085140398105 else 719330029799105
def weightRow5LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 651414195971105 else 663031156170105
def weightRow5LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow5LLLLRRLL i else weightRow5LLLLRRLR i
def weightRow5LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 958806136476105 else 940587485719105
def weightRow5LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 583755864072105 else 596711373724105
def weightRow5LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow5LLLLRRRL i else weightRow5LLLLRRRR i
def weightRow5LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow5LLLLRRL i else weightRow5LLLLRRR i
def weightRow5LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow5LLLLRL i else weightRow5LLLLRR i
def weightRow5LLLL (i : ℕ) : ℕ := if i < 16 then weightRow5LLLLL i else weightRow5LLLLR i
def weightRow5LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 665143138111105 else 615921556056105
def weightRow5LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 776115383096105 else 749005462445105
def weightRow5LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow5LLLRLLLL i else weightRow5LLLRLLLR i
def weightRow5LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 619190267072105 else 604656856479105
def weightRow5LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 1045679180482105 else 1070032771519105
def weightRow5LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow5LLLRLLRL i else weightRow5LLLRLLRR i
def weightRow5LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow5LLLRLLL i else weightRow5LLLRLLR i
def weightRow5LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 842722517006105 else 945232983519105
def weightRow5LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 1041957115152105 else 993965381681105
def weightRow5LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow5LLLRLRLL i else weightRow5LLLRLRLR i
def weightRow5LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 652442034012105 else 697631861263105
def weightRow5LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 634701205079105 else 661588966808105
def weightRow5LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow5LLLRLRRL i else weightRow5LLLRLRRR i
def weightRow5LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow5LLLRLRL i else weightRow5LLLRLRR i
def weightRow5LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow5LLLRLL i else weightRow5LLLRLR i
def weightRow5LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 749527637011105 else 743763676209105
def weightRow5LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 942459743858105 else 918326461891105
def weightRow5LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow5LLLRRLLL i else weightRow5LLLRRLLR i
def weightRow5LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 670875905770105 else 678433616523105
def weightRow5LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 822158991200105 else 823490110278105
def weightRow5LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow5LLLRRLRL i else weightRow5LLLRRLRR i
def weightRow5LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow5LLLRRLL i else weightRow5LLLRRLR i
def weightRow5LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 777718637104105 else 746267948768105
def weightRow5LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 977814376998105 else 993452148071105
def weightRow5LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow5LLLRRRLL i else weightRow5LLLRRRLR i
def weightRow5LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 636572110001105 else 625664088246105
def weightRow5LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 830721018819105 else 843779176867105
def weightRow5LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow5LLLRRRRL i else weightRow5LLLRRRRR i
def weightRow5LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow5LLLRRRL i else weightRow5LLLRRRR i
def weightRow5LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow5LLLRRL i else weightRow5LLLRRR i
def weightRow5LLLR (i : ℕ) : ℕ := if i < 48 then weightRow5LLLRL i else weightRow5LLLRR i
def weightRow5LLL (i : ℕ) : ℕ := if i < 32 then weightRow5LLLL i else weightRow5LLLR i
def weightRow5LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 856503055276105 else 844161848971105
def weightRow5LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 661546215278105 else 673149599796105
def weightRow5LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow5LLRLLLLL i else weightRow5LLRLLLLR i
def weightRow5LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 1055196188817105 else 1040189335453105
def weightRow5LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 836159857681105 else 868499260931105
def weightRow5LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow5LLRLLLRL i else weightRow5LLRLLLRR i
def weightRow5LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow5LLRLLLL i else weightRow5LLRLLLR i
def weightRow5LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 939315387985105 else 939358605774105
def weightRow5LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 819535747724105 else 813234982590105
def weightRow5LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow5LLRLLRLL i else weightRow5LLRLLRLR i
def weightRow5LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 1086586240248105 else 1112253360894105
def weightRow5LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 940622140943105 else 948412547564105
def weightRow5LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow5LLRLLRRL i else weightRow5LLRLLRRR i
def weightRow5LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow5LLRLLRL i else weightRow5LLRLLRR i
def weightRow5LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow5LLRLLL i else weightRow5LLRLLR i
def weightRow5LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 883485228116105 else 858320127296105
def weightRow5LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 944229143758105 else 899668767323105
def weightRow5LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow5LLRLRLLL i else weightRow5LLRLRLLR i
def weightRow5LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 1270850192343105 else 1319521675333105
def weightRow5LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 1256743780700105 else 1154075633609105
def weightRow5LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow5LLRLRLRL i else weightRow5LLRLRLRR i
def weightRow5LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow5LLRLRLL i else weightRow5LLRLRLR i
def weightRow5LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 1417904303108105 else 1391405101540105
def weightRow5LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 984128370820105 else 996330923442105
def weightRow5LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow5LLRLRRLL i else weightRow5LLRLRRLR i
def weightRow5LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1155559377131105 else 1180951574940105
def weightRow5LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 1050153988194105 else 1098826129317105
def weightRow5LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow5LLRLRRRL i else weightRow5LLRLRRRR i
def weightRow5LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow5LLRLRRL i else weightRow5LLRLRRR i
def weightRow5LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow5LLRLRL i else weightRow5LLRLRR i
def weightRow5LLRL (i : ℕ) : ℕ := if i < 80 then weightRow5LLRLL i else weightRow5LLRLR i
def weightRow5LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 1056679593969105 else 1043729422467105
def weightRow5LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 1431761053886105 else 1450072302690105
def weightRow5LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow5LLRRLLLL i else weightRow5LLRRLLLR i
def weightRow5LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1186939127344105 else 1175515219963105
def weightRow5LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 1273023584721105 else 1299195381548105
def weightRow5LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow5LLRRLLRL i else weightRow5LLRRLLRR i
def weightRow5LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow5LLRRLLL i else weightRow5LLRRLLR i
def weightRow5LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 1298594032065105 else 1263865395646105
def weightRow5LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1157047340451105 else 1177696754080105
def weightRow5LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow5LLRRLRLL i else weightRow5LLRRLRLR i
def weightRow5LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1066643388308105 else 1060862299372105
def weightRow5LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 992899643408105 else 1013804797707105
def weightRow5LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow5LLRRLRRL i else weightRow5LLRRLRRR i
def weightRow5LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow5LLRRLRL i else weightRow5LLRRLRR i
def weightRow5LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow5LLRRLL i else weightRow5LLRRLR i
def weightRow5LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1101502297858105 else 1100876332554105
def weightRow5LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 919713299971105 else 920274654663105
def weightRow5LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow5LLRRRLLL i else weightRow5LLRRRLLR i
def weightRow5LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 1246282891245105 else 1277594002210105
def weightRow5LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 1184021013069105 else 1166874020261105
def weightRow5LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow5LLRRRLRL i else weightRow5LLRRRLRR i
def weightRow5LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow5LLRRRLL i else weightRow5LLRRRLR i
def weightRow5LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 1153834874478105 else 1125233830733105
def weightRow5LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 1061704329181105 else 1054256668340105
def weightRow5LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow5LLRRRRLL i else weightRow5LLRRRRLR i
def weightRow5LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 1037851458486105 else 1042135273856105
def weightRow5LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 1092675976251105 else 1092734161590105
def weightRow5LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow5LLRRRRRL i else weightRow5LLRRRRRR i
def weightRow5LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow5LLRRRRL i else weightRow5LLRRRRR i
def weightRow5LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow5LLRRRL i else weightRow5LLRRRR i
def weightRow5LLRR (i : ℕ) : ℕ := if i < 112 then weightRow5LLRRL i else weightRow5LLRRR i
def weightRow5LLR (i : ℕ) : ℕ := if i < 96 then weightRow5LLRL i else weightRow5LLRR i
def weightRow5LL (i : ℕ) : ℕ := if i < 64 then weightRow5LLL i else weightRow5LLR i
def weightRow5LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 855403229336105 else 855602403348105
def weightRow5LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 864796603777105 else 865000619732105
def weightRow5LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow5LRLLLLLL i else weightRow5LRLLLLLR i
def weightRow5LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 874807196972105 else 875081458250105
def weightRow5LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 884479672200105 else 884638875664105
def weightRow5LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow5LRLLLLRL i else weightRow5LRLLLLRR i
def weightRow5LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow5LRLLLLL i else weightRow5LRLLLLR i
def weightRow5LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 892853219256105 else 892554646812105
def weightRow5LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 900344762131105 else 899725244099105
def weightRow5LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow5LRLLLRLL i else weightRow5LRLLLRLR i
def weightRow5LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 905797178540105 else 905670206545105
def weightRow5LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 916569081994105 else 916414908295105
def weightRow5LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow5LRLLLRRL i else weightRow5LRLLLRRR i
def weightRow5LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow5LRLLLRL i else weightRow5LRLLLRR i
def weightRow5LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow5LRLLLL i else weightRow5LRLLLR i
def weightRow5LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 924355640312105 else 924188944614105
def weightRow5LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 933282259691105 else 933433079895105
def weightRow5LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow5LRLLRLLL i else weightRow5LRLLRLLR i
def weightRow5LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 941255515894105 else 941327825064105
def weightRow5LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 947166854827105 else 947523560616105
def weightRow5LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow5LRLLRLRL i else weightRow5LRLLRLRR i
def weightRow5LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow5LRLLRLL i else weightRow5LRLLRLR i
def weightRow5LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 951340972026105 else 951186783785105
def weightRow5LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 954570561112105 else 954814451899105
def weightRow5LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow5LRLLRRLL i else weightRow5LRLLRRLR i
def weightRow5LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 959309705937105 else 959341127946105
def weightRow5LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 959319294126105 else 959655132251105
def weightRow5LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow5LRLLRRRL i else weightRow5LRLLRRRR i
def weightRow5LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow5LRLLRRL i else weightRow5LRLLRRR i
def weightRow5LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow5LRLLRL i else weightRow5LRLLRR i
def weightRow5LRLL (i : ℕ) : ℕ := if i < 144 then weightRow5LRLLL i else weightRow5LRLLR i
def weightRow5LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 965172453423105 else 965336759896105
def weightRow5LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 969874657702105 else 970783775214105
def weightRow5LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow5LRLRLLLL i else weightRow5LRLRLLLR i
def weightRow5LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 972893733141105 else 974274436968105
def weightRow5LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 978421598075105 else 980006518378105
def weightRow5LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow5LRLRLLRL i else weightRow5LRLRLLRR i
def weightRow5LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow5LRLRLLL i else weightRow5LRLRLLR i
def weightRow5LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 977369693420105 else 978619198537105
def weightRow5LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 979475903768105 else 979123318769105
def weightRow5LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow5LRLRLRLL i else weightRow5LRLRLRLR i
def weightRow5LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 978508935690105 else 978909969179105
def weightRow5LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 983594368870105 else 983309702094105
def weightRow5LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow5LRLRLRRL i else weightRow5LRLRLRRR i
def weightRow5LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow5LRLRLRL i else weightRow5LRLRLRR i
def weightRow5LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow5LRLRLL i else weightRow5LRLRLR i
def weightRow5LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 989046689329105 else 988339816894105
def weightRow5LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 992784105158105 else 992142397969105
def weightRow5LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow5LRLRRLLL i else weightRow5LRLRRLLR i
def weightRow5LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 993577107357105 else 993310465994105
def weightRow5LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 998609917742105 else 998230589130105
def weightRow5LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow5LRLRRLRL i else weightRow5LRLRRLRR i
def weightRow5LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow5LRLRRLL i else weightRow5LRLRRLR i
def weightRow5LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 1001377760901105 else 1000962289451105
def weightRow5LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 1004871806822105 else 1004914139188105
def weightRow5LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow5LRLRRRLL i else weightRow5LRLRRRLR i
def weightRow5LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 1005290103063105 else 1005125072645105
def weightRow5LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1011049297474105 else 1011041497435105
def weightRow5LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow5LRLRRRRL i else weightRow5LRLRRRRR i
def weightRow5LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow5LRLRRRL i else weightRow5LRLRRRR i
def weightRow5LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow5LRLRRL i else weightRow5LRLRRR i
def weightRow5LRLR (i : ℕ) : ℕ := if i < 176 then weightRow5LRLRL i else weightRow5LRLRR i
def weightRow5LRL (i : ℕ) : ℕ := if i < 160 then weightRow5LRLL i else weightRow5LRLR i
def weightRow5LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1013874455372105 else 1013644724353105
def weightRow5LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1016318917219105 else 1016322433242105
def weightRow5LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow5LRRLLLLL i else weightRow5LRRLLLLR i
def weightRow5LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1021867331387105 else 1021654573699105
def weightRow5LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1021352406200105 else 1021379048650105
def weightRow5LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow5LRRLLLRL i else weightRow5LRRLLLRR i
def weightRow5LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow5LRRLLLL i else weightRow5LRRLLLR i
def weightRow5LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1024246259855105 else 1023756659475105
def weightRow5LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1025562190454105 else 1025088300073105
def weightRow5LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow5LRRLLRLL i else weightRow5LRRLLRLR i
def weightRow5LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1028786433140105 else 1028372392442105
def weightRow5LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1027887024267105 else 1027072355438105
def weightRow5LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow5LRRLLRRL i else weightRow5LRRLLRRR i
def weightRow5LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow5LRRLLRL i else weightRow5LRRLLRR i
def weightRow5LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow5LRRLLL i else weightRow5LRRLLR i
def weightRow5LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1029242674718105 else 1028312591931105
def weightRow5LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1031518031775105 else 1030974896258105
def weightRow5LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow5LRRLRLLL i else weightRow5LRRLRLLR i
def weightRow5LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1032883249995105 else 1033006149003105
def weightRow5LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1029155319044105 else 1028540398912105
def weightRow5LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow5LRRLRLRL i else weightRow5LRRLRLRR i
def weightRow5LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow5LRRLRLL i else weightRow5LRRLRLR i
def weightRow5LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1025608838061105 else 1026549445483105
def weightRow5LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1019479027242105 else 1020878682079105
def weightRow5LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow5LRRLRRLL i else weightRow5LRRLRRLR i
def weightRow5LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1020036793277105 else 1021243151988105
def weightRow5LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1017913845337105 else 1018757410334105
def weightRow5LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow5LRRLRRRL i else weightRow5LRRLRRRR i
def weightRow5LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow5LRRLRRL i else weightRow5LRRLRRR i
def weightRow5LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow5LRRLRL i else weightRow5LRRLRR i
def weightRow5LRRL (i : ℕ) : ℕ := if i < 208 then weightRow5LRRLL i else weightRow5LRRLR i
def weightRow5LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 1017405208738105 else 1017520862135105
def weightRow5LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 1016794658543105 else 1017081092996105
def weightRow5LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow5LRRRLLLL i else weightRow5LRRRLLLR i
def weightRow5LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 1010308839733105 else 1010334426003105
def weightRow5LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 1007548252982105 else 1007752145844105
def weightRow5LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow5LRRRLLRL i else weightRow5LRRRLLRR i
def weightRow5LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow5LRRRLLL i else weightRow5LRRRLLR i
def weightRow5LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 1003403477106105 else 1003192737064105
def weightRow5LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 998796839983105 else 999119375713105
def weightRow5LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow5LRRRLRLL i else weightRow5LRRRLRLR i
def weightRow5LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 996319658198105 else 996336525879105
def weightRow5LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 995226379483105 else 995335202176105
def weightRow5LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow5LRRRLRRL i else weightRow5LRRRLRRR i
def weightRow5LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow5LRRRLRL i else weightRow5LRRRLRR i
def weightRow5LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow5LRRRLL i else weightRow5LRRRLR i
def weightRow5LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 995263979603105 else 995035284849105
def weightRow5LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 993599081256105 else 993400588872105
def weightRow5LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow5LRRRRLLL i else weightRow5LRRRRLLR i
def weightRow5LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 994752575070105 else 994523380748105
def weightRow5LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 990822756706105 else 990108077196105
def weightRow5LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow5LRRRRLRL i else weightRow5LRRRRLRR i
def weightRow5LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow5LRRRRLL i else weightRow5LRRRRLR i
def weightRow5LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 987806700141105 else 987344868746105
def weightRow5LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 985213072403105 else 985193881901105
def weightRow5LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow5LRRRRRLL i else weightRow5LRRRRRLR i
def weightRow5LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 984017913152105 else 984117865653105
def weightRow5LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 983181301579105 else 983200587561105
def weightRow5LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow5LRRRRRRL i else weightRow5LRRRRRRR i
def weightRow5LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow5LRRRRRL i else weightRow5LRRRRRR i
def weightRow5LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow5LRRRRL i else weightRow5LRRRRR i
def weightRow5LRRR (i : ℕ) : ℕ := if i < 240 then weightRow5LRRRL i else weightRow5LRRRR i
def weightRow5LRR (i : ℕ) : ℕ := if i < 224 then weightRow5LRRL i else weightRow5LRRR i
def weightRow5LR (i : ℕ) : ℕ := if i < 192 then weightRow5LRL i else weightRow5LRR i
def weightRow5L (i : ℕ) : ℕ := if i < 128 then weightRow5LL i else weightRow5LR i
def weightRow5RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 981471780668105 else 981503903903105
def weightRow5RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 983441491591105 else 983471210393105
def weightRow5RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow5RLLLLLLL i else weightRow5RLLLLLLR i
def weightRow5RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 985295690375105 else 985321523337105
def weightRow5RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 987021940383105 else 987043783873105
def weightRow5RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow5RLLLLLRL i else weightRow5RLLLLLRR i
def weightRow5RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow5RLLLLLL i else weightRow5RLLLLLR i
def weightRow5RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 988623810897105 else 988643325449105
def weightRow5RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 990119924238105 else 990144326737105
def weightRow5RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow5RLLLLRLL i else weightRow5RLLLLRLR i
def weightRow5RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 991522169387105 else 991556997887105
def weightRow5RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 992861031098105 else 992898203456105
def weightRow5RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow5RLLLLRRL i else weightRow5RLLLLRRR i
def weightRow5RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow5RLLLLRL i else weightRow5RLLLLRR i
def weightRow5RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow5RLLLLL i else weightRow5RLLLLR i
def weightRow5RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 994052475914105 else 994092822831105
def weightRow5RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 995140821734105 else 995184401638105
def weightRow5RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow5RLLLRLLL i else weightRow5RLLLRLLR i
def weightRow5RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 996106866683105 else 996148810280105
def weightRow5RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 996963568575105 else 997004502907105
def weightRow5RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow5RLLLRLRL i else weightRow5RLLLRLRR i
def weightRow5RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow5RLLLRLL i else weightRow5RLLLRLR i
def weightRow5RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 997740840673105 else 997777293307105
def weightRow5RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 998465351168105 else 998504586284105
def weightRow5RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow5RLLLRRLL i else weightRow5RLLLRRLR i
def weightRow5RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 999150596768105 else 999186380850105
def weightRow5RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 999772380846105 else 999808818501105
def weightRow5RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow5RLLLRRRL i else weightRow5RLLLRRRR i
def weightRow5RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow5RLLLRRL i else weightRow5RLLLRRR i
def weightRow5RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow5RLLLRL i else weightRow5RLLLRR i
def weightRow5RLLL (i : ℕ) : ℕ := if i < 272 then weightRow5RLLLL i else weightRow5RLLLR i
def weightRow5RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 1000403588081105 else 1000435343320105
def weightRow5RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 1000953685234105 else 1000983170703105
def weightRow5RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow5RLLRLLLL i else weightRow5RLLRLLLR i
def weightRow5RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 1001438548871105 else 1001454202944105
def weightRow5RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1001884050707105 else 1001877836708105
def weightRow5RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow5RLLRLLRL i else weightRow5RLLRLLRR i
def weightRow5RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow5RLLRLLL i else weightRow5RLLRLLR i
def weightRow5RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1002250223713105 else 1002219379971105
def weightRow5RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1002638383174105 else 1002587469584105
def weightRow5RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow5RLLRLRLL i else weightRow5RLLRLRLR i
def weightRow5RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1003000068695105 else 1002954010002105
def weightRow5RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1003382005704105 else 1003329189132105
def weightRow5RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow5RLLRLRRL i else weightRow5RLLRLRRR i
def weightRow5RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow5RLLRLRL i else weightRow5RLLRLRR i
def weightRow5RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow5RLLRLL i else weightRow5RLLRLR i
def weightRow5RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1003691152321105 else 1003641765763105
def weightRow5RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1003919660961105 else 1003880447984105
def weightRow5RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow5RLLRRLLL i else weightRow5RLLRRLLR i
def weightRow5RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1004093287890105 else 1004063418135105
def weightRow5RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1004257110602105 else 1004230957926105
def weightRow5RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow5RLLRRLRL i else weightRow5RLLRRLRR i
def weightRow5RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow5RLLRRLL i else weightRow5RLLRRLR i
def weightRow5RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1004344568799105 else 1004323683229105
def weightRow5RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1004390076189105 else 1004375141789105
def weightRow5RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow5RLLRRRLL i else weightRow5RLLRRRLR i
def weightRow5RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1004381909695105 else 1004366773883105
def weightRow5RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1004367380042105 else 1004354216218105
def weightRow5RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow5RLLRRRRL i else weightRow5RLLRRRRR i
def weightRow5RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow5RLLRRRL i else weightRow5RLLRRRR i
def weightRow5RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow5RLLRRL i else weightRow5RLLRRR i
def weightRow5RLLR (i : ℕ) : ℕ := if i < 304 then weightRow5RLLRL i else weightRow5RLLRR i
def weightRow5RLL (i : ℕ) : ℕ := if i < 288 then weightRow5RLLL i else weightRow5RLLR i
def weightRow5RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1004262853357105 else 1004249696045105
def weightRow5RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1004111877684105 else 1004102401950105
def weightRow5RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow5RLRLLLLL i else weightRow5RLRLLLLR i
def weightRow5RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1003921196479105 else 1003911329974105
def weightRow5RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1003640953081105 else 1003634267351105
def weightRow5RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow5RLRLLLRL i else weightRow5RLRLLLRR i
def weightRow5RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow5RLRLLLL i else weightRow5RLRLLLR i
def weightRow5RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1003364481112105 else 1003357172453105
def weightRow5RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1003038289347105 else 1003038777552105
def weightRow5RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow5RLRLLRLL i else weightRow5RLRLLRLR i
def weightRow5RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1002687079910105 else 1002694796155105
def weightRow5RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1002280441629105 else 1002295264983105
def weightRow5RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow5RLRLLRRL i else weightRow5RLRLLRRR i
def weightRow5RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow5RLRLLRL i else weightRow5RLRLLRR i
def weightRow5RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow5RLRLLL i else weightRow5RLRLLR i
def weightRow5RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1001881276104105 else 1001909435790105
def weightRow5RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1001455244452105 else 1001498033492105
def weightRow5RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow5RLRLRLLL i else weightRow5RLRLRLLR i
def weightRow5RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 1000986869842105 else 1001038735903105
def weightRow5RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 1000490225967105 else 1000540841146105
def weightRow5RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow5RLRLRLRL i else weightRow5RLRLRLRR i
def weightRow5RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow5RLRLRLL i else weightRow5RLRLRLR i
def weightRow5RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 1000044104012105 else 1000104842082105
def weightRow5RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 999646093253105 else 999693420840105
def weightRow5RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow5RLRLRRLL i else weightRow5RLRLRRLR i
def weightRow5RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 999337896829105 else 999363890584105
def weightRow5RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 999015994012105 else 999023912169105
def weightRow5RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow5RLRLRRRL i else weightRow5RLRLRRRR i
def weightRow5RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow5RLRLRRL i else weightRow5RLRLRRR i
def weightRow5RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow5RLRLRL i else weightRow5RLRLRR i
def weightRow5RLRL (i : ℕ) : ℕ := if i < 336 then weightRow5RLRLL i else weightRow5RLRLR i
def weightRow5RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 998723136769105 else 998717845793105
def weightRow5RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 998434057849105 else 998426719036105
def weightRow5RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow5RLRRLLLL i else weightRow5RLRRLLLR i
def weightRow5RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 998150216581105 else 998138314373105
def weightRow5RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 997962961973105 else 997950446858105
def weightRow5RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow5RLRRLLRL i else weightRow5RLRRLLRR i
def weightRow5RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow5RLRRLLL i else weightRow5RLRRLLR i
def weightRow5RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 997815370193105 else 997799019765105
def weightRow5RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 997728967618105 else 997715512270105
def weightRow5RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow5RLRRLRLL i else weightRow5RLRRLRLR i
def weightRow5RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 997713519511105 else 997694960610105
def weightRow5RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 997736558247105 else 997717757697105
def weightRow5RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow5RLRRLRRL i else weightRow5RLRRLRRR i
def weightRow5RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow5RLRRLRL i else weightRow5RLRRLRR i
def weightRow5RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow5RLRRLL i else weightRow5RLRRLR i
def weightRow5RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 997777668356105 else 997756688552105
def weightRow5RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 997818032524105 else 997800849702105
def weightRow5RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow5RLRRRLLL i else weightRow5RLRRRLLR i
def weightRow5RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 997882747116105 else 997868332088105
def weightRow5RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 997931172431105 else 997920431212105
def weightRow5RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow5RLRRRLRL i else weightRow5RLRRRLRR i
def weightRow5RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow5RLRRRLL i else weightRow5RLRRRLR i
def weightRow5RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 998042330775105 else 998042410892105
def weightRow5RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 998201567901105 else 998208789938105
def weightRow5RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow5RLRRRRLL i else weightRow5RLRRRRLR i
def weightRow5RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 998404511982105 else 998411614544105
def weightRow5RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 998623261767105 else 998628872097105
def weightRow5RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow5RLRRRRRL i else weightRow5RLRRRRRR i
def weightRow5RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow5RLRRRRL i else weightRow5RLRRRRR i
def weightRow5RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow5RLRRRL i else weightRow5RLRRRR i
def weightRow5RLRR (i : ℕ) : ℕ := if i < 368 then weightRow5RLRRL i else weightRow5RLRRR i
def weightRow5RLR (i : ℕ) : ℕ := if i < 352 then weightRow5RLRL i else weightRow5RLRR i
def weightRow5RL (i : ℕ) : ℕ := if i < 320 then weightRow5RLL i else weightRow5RLR i
def weightRow5RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 998861805400105 else 998867720227105
def weightRow5RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 999135743773105 else 999141563151105
def weightRow5RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow5RRLLLLLL i else weightRow5RRLLLLLR i
def weightRow5RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 999370581455105 else 999375864171105
def weightRow5RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 999588222432105 else 999593868740105
def weightRow5RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow5RRLLLLRL i else weightRow5RRLLLLRR i
def weightRow5RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow5RRLLLLL i else weightRow5RRLLLLR i
def weightRow5RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 999771058746105 else 999776192223105
def weightRow5RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 999950052592105 else 999955483872105
def weightRow5RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow5RRLLLRLL i else weightRow5RRLLLRLR i
def weightRow5RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 1000100377184105 else 1000102657419105
def weightRow5RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 1000220645708105 else 1000223222324105
def weightRow5RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow5RRLLLRRL i else weightRow5RRLLLRRR i
def weightRow5RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow5RRLLLRL i else weightRow5RRLLLRR i
def weightRow5RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow5RRLLLL i else weightRow5RRLLLR i
def weightRow5RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 1000337155455105 else 1000340568858105
def weightRow5RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 1000426748565105 else 1000429700104105
def weightRow5RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow5RRLLRLLL i else weightRow5RRLLRLLR i
def weightRow5RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000522359278105 else 1000524914044105
def weightRow5RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000580285467105 else 1000578762896105
def weightRow5RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow5RRLLRLRL i else weightRow5RRLLRLRR i
def weightRow5RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow5RRLLRLL i else weightRow5RRLLRLR i
def weightRow5RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000634730261105 else 1000638328459105
def weightRow5RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000678043082105 else 1000678031623105
def weightRow5RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow5RRLLRRLL i else weightRow5RRLLRRLR i
def weightRow5RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000708149482105 else 1000707224254105
def weightRow5RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000737403123105 else 1000734281681105
def weightRow5RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow5RRLLRRRL i else weightRow5RRLLRRRR i
def weightRow5RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow5RRLLRRL i else weightRow5RRLLRRR i
def weightRow5RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow5RRLLRL i else weightRow5RRLLRR i
def weightRow5RRLL (i : ℕ) : ℕ := if i < 400 then weightRow5RRLLL i else weightRow5RRLLR i
def weightRow5RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000734624071105 else 1000732601956105
def weightRow5RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000761066769105 else 1000758113219105
def weightRow5RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow5RRLRLLLL i else weightRow5RRLRLLLR i
def weightRow5RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000742201837105 else 1000735788310105
def weightRow5RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000737677593105 else 1000732075057105
def weightRow5RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow5RRLRLLRL i else weightRow5RRLRLLRR i
def weightRow5RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow5RRLRLLL i else weightRow5RRLRLLR i
def weightRow5RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000725973758105 else 1000726692812105
def weightRow5RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000691680390105 else 1000690760200105
def weightRow5RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow5RRLRLRLL i else weightRow5RRLRLRLR i
def weightRow5RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000685107996105 else 1000682397582105
def weightRow5RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000633360891105 else 1000629189322105
def weightRow5RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow5RRLRLRRL i else weightRow5RRLRLRRR i
def weightRow5RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow5RRLRLRL i else weightRow5RRLRLRR i
def weightRow5RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow5RRLRLL i else weightRow5RRLRLR i
def weightRow5RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000619669961105 else 1000616959347105
def weightRow5RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000560130687105 else 1000556795006105
def weightRow5RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow5RRLRRLLL i else weightRow5RRLRRLLR i
def weightRow5RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000490984206105 else 1000490773459105
def weightRow5RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000442822570105 else 1000438084878105
def weightRow5RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow5RRLRRLRL i else weightRow5RRLRRLRR i
def weightRow5RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow5RRLRRLL i else weightRow5RRLRRLR i
def weightRow5RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000346919341105 else 1000350167148105
def weightRow5RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000291239643105 else 1000286513680105
def weightRow5RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow5RRLRRRLL i else weightRow5RRLRRRLR i
def weightRow5RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000247671547105 else 1000257671834105
def weightRow5RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000187047778105 else 1000187705206105
def weightRow5RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow5RRLRRRRL i else weightRow5RRLRRRRR i
def weightRow5RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow5RRLRRRL i else weightRow5RRLRRRR i
def weightRow5RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow5RRLRRL i else weightRow5RRLRRR i
def weightRow5RRLR (i : ℕ) : ℕ := if i < 432 then weightRow5RRLRL i else weightRow5RRLRR i
def weightRow5RRL (i : ℕ) : ℕ := if i < 416 then weightRow5RRLL i else weightRow5RRLR i
def weightRow5RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 1000141701308105 else 1000145076748105
def weightRow5RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 1000036895287105 else 1000045152868105
def weightRow5RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow5RRRLLLLL i else weightRow5RRRLLLLR i
def weightRow5RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 1000016507562105 else 1000032336774105
def weightRow5RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 999962135293105 else 999966812354105
def weightRow5RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow5RRRLLLRL i else weightRow5RRRLLLRR i
def weightRow5RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow5RRRLLLL i else weightRow5RRRLLLR i
def weightRow5RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 999923305955105 else 999918681674105
def weightRow5RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 999857741052105 else 999866125480105
def weightRow5RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow5RRRLLRLL i else weightRow5RRRLLRLR i
def weightRow5RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 999840155453105 else 999842396310105
def weightRow5RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 999827849692105 else 999846086317105
def weightRow5RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow5RRRLLRRL i else weightRow5RRRLLRRR i
def weightRow5RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow5RRRLLRL i else weightRow5RRRLLRR i
def weightRow5RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow5RRRLLL i else weightRow5RRRLLR i
def weightRow5RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 999788943762105 else 999790476019105
def weightRow5RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 999773581778105 else 999768784077105
def weightRow5RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow5RRRLRLLL i else weightRow5RRRLRLLR i
def weightRow5RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999745578712105 else 999750939366105
def weightRow5RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999745009934105 else 999742334916105
def weightRow5RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow5RRRLRLRL i else weightRow5RRRLRLRR i
def weightRow5RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow5RRRLRLL i else weightRow5RRRLRLR i
def weightRow5RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999728969929105 else 999732740855105
def weightRow5RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999719188901105 else 999712106041105
def weightRow5RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow5RRRLRRLL i else weightRow5RRRLRRLR i
def weightRow5RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999728756742105 else 999733189281105
def weightRow5RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999741260079105 else 999737135296105
def weightRow5RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow5RRRLRRRL i else weightRow5RRRLRRRR i
def weightRow5RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow5RRRLRRL i else weightRow5RRRLRRR i
def weightRow5RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow5RRRLRL i else weightRow5RRRLRR i
def weightRow5RRRL (i : ℕ) : ℕ := if i < 464 then weightRow5RRRLL i else weightRow5RRRLR i
def weightRow5RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999801617717105 else 999789264377105
def weightRow5RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999840984591105 else 999851660018105
def weightRow5RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow5RRRRLLLL i else weightRow5RRRRLLLR i
def weightRow5RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999883087765105 else 999869436787105
def weightRow5RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999889169746105 else 999895765419105
def weightRow5RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow5RRRRLLRL i else weightRow5RRRRLLRR i
def weightRow5RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow5RRRRLLL i else weightRow5RRRRLLR i
def weightRow5RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999885834692105 else 999862519763105
def weightRow5RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 999838643097105 else 999830902964105
def weightRow5RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow5RRRRLRLL i else weightRow5RRRRLRLR i
def weightRow5RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 999907017082105 else 999896117300105
def weightRow5RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 999931524054105 else 999957382342105
def weightRow5RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow5RRRRLRRL i else weightRow5RRRRLRRR i
def weightRow5RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow5RRRRLRL i else weightRow5RRRRLRR i
def weightRow5RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow5RRRRLL i else weightRow5RRRRLR i
def weightRow5RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 1000018968062105 else 1000004145798105
def weightRow5RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 1000002499375105 else 1000026740758105
def weightRow5RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow5RRRRRLLL i else weightRow5RRRRRLLR i
def weightRow5RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 999881142567105 else 999893795626105
def weightRow5RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 999959231747105 else 999974957328105
def weightRow5RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow5RRRRRLRL i else weightRow5RRRRRLRR i
def weightRow5RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow5RRRRRLL i else weightRow5RRRRRLR i
def weightRow5RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 1000023684289105 else 1000023008534105
def weightRow5RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 1000009403732105 else 1000003820892105
def weightRow5RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow5RRRRRRLL i else weightRow5RRRRRRLR i
def weightRow5RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 1000079993637105 else 1000051854098105
def weightRow5RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 999711791802105 else 999718824920105
def weightRow5RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow5RRRRRRRL i else weightRow5RRRRRRRR i
def weightRow5RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow5RRRRRRL i else weightRow5RRRRRRR i
def weightRow5RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow5RRRRRL i else weightRow5RRRRRR i
def weightRow5RRRR (i : ℕ) : ℕ := if i < 496 then weightRow5RRRRL i else weightRow5RRRRR i
def weightRow5RRR (i : ℕ) : ℕ := if i < 480 then weightRow5RRRL i else weightRow5RRRR i
def weightRow5RR (i : ℕ) : ℕ := if i < 448 then weightRow5RRL i else weightRow5RRR i
def weightRow5R (i : ℕ) : ℕ := if i < 384 then weightRow5RL i else weightRow5RR i
def weightRow5 (i : ℕ) : ℕ := if i < 256 then weightRow5L i else weightRow5R i
def weightRow6LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 224493041516105 else 250177608765105
def weightRow6LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 383654905448105 else 362472685673105
def weightRow6LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow6LLLLLLLL i else weightRow6LLLLLLLR i
def weightRow6LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 284062606020105 else 305838079713105
def weightRow6LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 339423072632105 else 313590551389105
def weightRow6LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow6LLLLLLRL i else weightRow6LLLLLLRR i
def weightRow6LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow6LLLLLLL i else weightRow6LLLLLLR i
def weightRow6LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 532123931987105 else 556482001529105
def weightRow6LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 728469479309105 else 677077411581105
def weightRow6LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow6LLLLLRLL i else weightRow6LLLLLRLR i
def weightRow6LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 650585926568105 else 712527879064105
def weightRow6LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 1012458116537105 else 919948291436105
def weightRow6LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow6LLLLLRRL i else weightRow6LLLLLRRR i
def weightRow6LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow6LLLLLRL i else weightRow6LLLLLRR i
def weightRow6LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow6LLLLLL i else weightRow6LLLLLR i
def weightRow6LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 896866946480105 else 948720174644105
def weightRow6LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 914034096759105 else 873053025498105
def weightRow6LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow6LLLLRLLL i else weightRow6LLLLRLLR i
def weightRow6LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 621560155242105 else 644974391468105
def weightRow6LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 532335474583105 else 540747745900105
def weightRow6LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow6LLLLRLRL i else weightRow6LLLLRLRR i
def weightRow6LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow6LLLLRLL i else weightRow6LLLLRLR i
def weightRow6LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 477211830996105 else 487342657719105
def weightRow6LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 637072103734105 else 668091686703105
def weightRow6LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow6LLLLRRLL i else weightRow6LLLLRRLR i
def weightRow6LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 450025916415105 else 463257697309105
def weightRow6LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 639701544054105 else 658965369075105
def weightRow6LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow6LLLLRRRL i else weightRow6LLLLRRRR i
def weightRow6LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow6LLLLRRL i else weightRow6LLLLRRR i
def weightRow6LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow6LLLLRL i else weightRow6LLLLRR i
def weightRow6LLLL (i : ℕ) : ℕ := if i < 16 then weightRow6LLLLL i else weightRow6LLLLR i
def weightRow6LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 725779085117105 else 676638512862105
def weightRow6LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 751831038566105 else 743190437340105
def weightRow6LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow6LLLRLLLL i else weightRow6LLLRLLLR i
def weightRow6LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 681339405169105 else 693453338866105
def weightRow6LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 564536830238105 else 569149589276105
def weightRow6LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow6LLLRLLRL i else weightRow6LLLRLLRR i
def weightRow6LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow6LLLRLLL i else weightRow6LLLRLLR i
def weightRow6LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 671371205704105 else 665570821429105
def weightRow6LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 623995844724105 else 645720929972105
def weightRow6LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow6LLLRLRLL i else weightRow6LLLRLRLR i
def weightRow6LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 643887962708105 else 667060617533105
def weightRow6LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 720783095308105 else 696939221225105
def weightRow6LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow6LLLRLRRL i else weightRow6LLLRLRRR i
def weightRow6LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow6LLLRLRL i else weightRow6LLLRLRR i
def weightRow6LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow6LLLRLL i else weightRow6LLLRLR i
def weightRow6LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 737553195473105 else 717368335638105
def weightRow6LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 795222868844105 else 798954263573105
def weightRow6LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow6LLLRRLLL i else weightRow6LLLRRLLR i
def weightRow6LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 698971095050105 else 708716182591105
def weightRow6LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 687157419511105 else 719135613297105
def weightRow6LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow6LLLRRLRL i else weightRow6LLLRRLRR i
def weightRow6LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow6LLLRRLL i else weightRow6LLLRRLR i
def weightRow6LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 640264368463105 else 630954141483105
def weightRow6LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 899662885148105 else 872199858355105
def weightRow6LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow6LLLRRRLL i else weightRow6LLLRRRLR i
def weightRow6LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 687644381269105 else 672280956610105
def weightRow6LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 1003894989215105 else 1029917806774105
def weightRow6LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow6LLLRRRRL i else weightRow6LLLRRRRR i
def weightRow6LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow6LLLRRRL i else weightRow6LLLRRRR i
def weightRow6LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow6LLLRRL i else weightRow6LLLRRR i
def weightRow6LLLR (i : ℕ) : ℕ := if i < 48 then weightRow6LLLRL i else weightRow6LLLRR i
def weightRow6LLL (i : ℕ) : ℕ := if i < 32 then weightRow6LLLL i else weightRow6LLLR i
def weightRow6LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 1045500161306105 else 1020091282622105
def weightRow6LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 714706496507105 else 730524553419105
def weightRow6LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow6LLRLLLLL i else weightRow6LLRLLLLR i
def weightRow6LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 939420591217105 else 968016425279105
def weightRow6LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 722712914964105 else 733747610024105
def weightRow6LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow6LLRLLLRL i else weightRow6LLRLLLRR i
def weightRow6LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow6LLRLLLL i else weightRow6LLRLLLR i
def weightRow6LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 833424920690105 else 802841684540105
def weightRow6LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 847099803726105 else 838122301470105
def weightRow6LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow6LLRLLRLL i else weightRow6LLRLLRLR i
def weightRow6LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 963059837196105 else 959896056835105
def weightRow6LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 907728578253105 else 928752225446105
def weightRow6LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow6LLRLLRRL i else weightRow6LLRLLRRR i
def weightRow6LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow6LLRLLRL i else weightRow6LLRLLRR i
def weightRow6LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow6LLRLLL i else weightRow6LLRLLR i
def weightRow6LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 912375291195105 else 937757194389105
def weightRow6LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 907178064309105 else 885573583844105
def weightRow6LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow6LLRLRLLL i else weightRow6LLRLRLLR i
def weightRow6LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 910101065889105 else 889270517656105
def weightRow6LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 954571835716105 else 961033197282105
def weightRow6LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow6LLRLRLRL i else weightRow6LLRLRLRR i
def weightRow6LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow6LLRLRLL i else weightRow6LLRLRLR i
def weightRow6LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 881960747533105 else 878033152685105
def weightRow6LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 1030879446257105 else 1019203398284105
def weightRow6LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow6LLRLRRLL i else weightRow6LLRLRRLR i
def weightRow6LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1108336451487105 else 1117368962168105
def weightRow6LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 1069676942467105 else 1120117217364105
def weightRow6LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow6LLRLRRRL i else weightRow6LLRLRRRR i
def weightRow6LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow6LLRLRRL i else weightRow6LLRLRRR i
def weightRow6LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow6LLRLRL i else weightRow6LLRLRR i
def weightRow6LLRL (i : ℕ) : ℕ := if i < 80 then weightRow6LLRLL i else weightRow6LLRLR i
def weightRow6LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 1079015254423105 else 1061535274573105
def weightRow6LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 907406590737105 else 895482149415105
def weightRow6LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow6LLRRLLLL i else weightRow6LLRRLLLR i
def weightRow6LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1136859446164105 else 1106472818707105
def weightRow6LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 981490454390105 else 971357864926105
def weightRow6LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow6LLRRLLRL i else weightRow6LLRRLLRR i
def weightRow6LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow6LLRRLLL i else weightRow6LLRRLLR i
def weightRow6LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 1058679715931105 else 1049978067474105
def weightRow6LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1189522034731105 else 1165320738909105
def weightRow6LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow6LLRRLRLL i else weightRow6LLRRLRLR i
def weightRow6LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1449832255229105 else 1490285092341105
def weightRow6LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 1562978235592105 else 1510419978851105
def weightRow6LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow6LLRRLRRL i else weightRow6LLRRLRRR i
def weightRow6LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow6LLRRLRL i else weightRow6LLRRLRR i
def weightRow6LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow6LLRRLL i else weightRow6LLRRLR i
def weightRow6LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 1573000541063105 else 1665432665113105
def weightRow6LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 1401297487153105 else 1339747985082105
def weightRow6LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow6LLRRRLLL i else weightRow6LLRRRLLR i
def weightRow6LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 1398320646051105 else 1449946901139105
def weightRow6LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 1308269634195105 else 1284564049432105
def weightRow6LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow6LLRRRLRL i else weightRow6LLRRRLRR i
def weightRow6LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow6LLRRRLL i else weightRow6LLRRRLR i
def weightRow6LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 1090714725585105 else 1117244758605105
def weightRow6LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 1104787813808105 else 1083782108858105
def weightRow6LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow6LLRRRRLL i else weightRow6LLRRRRLR i
def weightRow6LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 1184349127599105 else 1206304723158105
def weightRow6LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 1094469206037105 else 1069502880659105
def weightRow6LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow6LLRRRRRL i else weightRow6LLRRRRRR i
def weightRow6LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow6LLRRRRL i else weightRow6LLRRRRR i
def weightRow6LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow6LLRRRL i else weightRow6LLRRRR i
def weightRow6LLRR (i : ℕ) : ℕ := if i < 112 then weightRow6LLRRL i else weightRow6LLRRR i
def weightRow6LLR (i : ℕ) : ℕ := if i < 96 then weightRow6LLRL i else weightRow6LLRR i
def weightRow6LL (i : ℕ) : ℕ := if i < 64 then weightRow6LLL i else weightRow6LLR i
def weightRow6LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 861384454814105 else 861717045577105
def weightRow6LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 871341257062105 else 871257509230105
def weightRow6LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow6LRLLLLLL i else weightRow6LRLLLLLR i
def weightRow6LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 878961611234105 else 879208094691105
def weightRow6LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 888250898022105 else 888170772473105
def weightRow6LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow6LRLLLLRL i else weightRow6LRLLLLRR i
def weightRow6LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow6LRLLLLL i else weightRow6LRLLLLR i
def weightRow6LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 896819716638105 else 897146890820105
def weightRow6LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 902517346825105 else 902460871109105
def weightRow6LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow6LRLLLRLL i else weightRow6LRLLLRLR i
def weightRow6LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 905233682512105 else 905997384905105
def weightRow6LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 909208250358105 else 909000271745105
def weightRow6LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow6LRLLLRRL i else weightRow6LRLLLRRR i
def weightRow6LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow6LRLLLRL i else weightRow6LRLLLRR i
def weightRow6LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow6LRLLLL i else weightRow6LRLLLR i
def weightRow6LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 907598617832105 else 908829672728105
def weightRow6LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 907769183503105 else 908204054470105
def weightRow6LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow6LRLLRLLL i else weightRow6LRLLRLLR i
def weightRow6LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 907680204417105 else 908760111682105
def weightRow6LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 912151956629105 else 912881457205105
def weightRow6LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow6LRLLRLRL i else weightRow6LRLLRLRR i
def weightRow6LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow6LRLLRLL i else weightRow6LRLLRLR i
def weightRow6LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 918078729648105 else 918710308077105
def weightRow6LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 924973258374105 else 925434257975105
def weightRow6LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow6LRLLRRLL i else weightRow6LRLLRRLR i
def weightRow6LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 929469160675105 else 929471224664105
def weightRow6LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 936961434865105 else 936749715249105
def weightRow6LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow6LRLLRRRL i else weightRow6LRLLRRRR i
def weightRow6LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow6LRLLRRL i else weightRow6LRLLRRR i
def weightRow6LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow6LRLLRL i else weightRow6LRLLRR i
def weightRow6LRLL (i : ℕ) : ℕ := if i < 144 then weightRow6LRLLL i else weightRow6LRLLR i
def weightRow6LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 941596402099105 else 941091348310105
def weightRow6LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 944978825659105 else 945212871183105
def weightRow6LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow6LRLRLLLL i else weightRow6LRLRLLLR i
def weightRow6LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 947996447583105 else 948370541454105
def weightRow6LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 952160492079105 else 952361145828105
def weightRow6LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow6LRLRLLRL i else weightRow6LRLRLLRR i
def weightRow6LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow6LRLRLLL i else weightRow6LRLRLLR i
def weightRow6LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 958212922399105 else 958344669232105
def weightRow6LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 962699822298105 else 962922471375105
def weightRow6LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow6LRLRLRLL i else weightRow6LRLRLRLR i
def weightRow6LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 967990769358105 else 967880507577105
def weightRow6LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 973052201472105 else 972578355090105
def weightRow6LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow6LRLRLRRL i else weightRow6LRLRLRRR i
def weightRow6LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow6LRLRLRL i else weightRow6LRLRLRR i
def weightRow6LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow6LRLRLL i else weightRow6LRLRLR i
def weightRow6LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 976995420804105 else 976886036147105
def weightRow6LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 980737115839105 else 980932655321105
def weightRow6LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow6LRLRRLLL i else weightRow6LRLRRLLR i
def weightRow6LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 983639184319105 else 983775455933105
def weightRow6LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 988082711503105 else 988076579158105
def weightRow6LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow6LRLRRLRL i else weightRow6LRLRRLRR i
def weightRow6LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow6LRLRRLL i else weightRow6LRLRRLR i
def weightRow6LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 992782045363105 else 992293503101105
def weightRow6LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 998292115510105 else 997916629153105
def weightRow6LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow6LRLRRRLL i else weightRow6LRLRRRLR i
def weightRow6LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 999826472699105 else 999905483181105
def weightRow6LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1004706970641105 else 1005004227071105
def weightRow6LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow6LRLRRRRL i else weightRow6LRLRRRRR i
def weightRow6LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow6LRLRRRL i else weightRow6LRLRRRR i
def weightRow6LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow6LRLRRL i else weightRow6LRLRRR i
def weightRow6LRLR (i : ℕ) : ℕ := if i < 176 then weightRow6LRLRL i else weightRow6LRLRR i
def weightRow6LRL (i : ℕ) : ℕ := if i < 160 then weightRow6LRLL i else weightRow6LRLR i
def weightRow6LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1004723383647105 else 1004599652962105
def weightRow6LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1004085444154105 else 1004381722654105
def weightRow6LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow6LRRLLLLL i else weightRow6LRRLLLLR i
def weightRow6LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1008607219165105 else 1008643080604105
def weightRow6LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1009687447072105 else 1009293774487105
def weightRow6LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow6LRRLLLRL i else weightRow6LRRLLLRR i
def weightRow6LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow6LRRLLLL i else weightRow6LRRLLLR i
def weightRow6LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1014168670913105 else 1013597088503105
def weightRow6LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1016989868556105 else 1016893039308105
def weightRow6LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow6LRRLLRLL i else weightRow6LRRLLRLR i
def weightRow6LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1019647298388105 else 1019675839943105
def weightRow6LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1020531332795105 else 1020612768584105
def weightRow6LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow6LRRLLRRL i else weightRow6LRRLLRRR i
def weightRow6LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow6LRRLLRL i else weightRow6LRRLLRR i
def weightRow6LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow6LRRLLL i else weightRow6LRRLLR i
def weightRow6LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1022299892129105 else 1022044135131105
def weightRow6LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1024009785511105 else 1023362626459105
def weightRow6LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow6LRRLRLLL i else weightRow6LRRLRLLR i
def weightRow6LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1025835744377105 else 1025517120100105
def weightRow6LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1027640690686105 else 1027642223778105
def weightRow6LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow6LRRLRLRL i else weightRow6LRRLRLRR i
def weightRow6LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow6LRRLRLL i else weightRow6LRRLRLR i
def weightRow6LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1028785141932105 else 1028689790830105
def weightRow6LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1031073104251105 else 1031037317533105
def weightRow6LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow6LRRLRRLL i else weightRow6LRRLRRLR i
def weightRow6LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1031079019908105 else 1031220867792105
def weightRow6LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1029875767589105 else 1029876052299105
def weightRow6LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow6LRRLRRRL i else weightRow6LRRLRRRR i
def weightRow6LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow6LRRLRRL i else weightRow6LRRLRRR i
def weightRow6LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow6LRRLRL i else weightRow6LRRLRR i
def weightRow6LRRL (i : ℕ) : ℕ := if i < 208 then weightRow6LRRLL i else weightRow6LRRLR i
def weightRow6LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 1029259637987105 else 1028460177078105
def weightRow6LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 1028474455829105 else 1027957999543105
def weightRow6LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow6LRRRLLLL i else weightRow6LRRRLLLR i
def weightRow6LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 1030365365833105 else 1030010949972105
def weightRow6LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 1028703312344105 else 1028828571856105
def weightRow6LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow6LRRRLLRL i else weightRow6LRRRLLRR i
def weightRow6LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow6LRRRLLL i else weightRow6LRRRLLR i
def weightRow6LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 1029441862787105 else 1029727004865105
def weightRow6LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 1028978382270105 else 1029410634510105
def weightRow6LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow6LRRRLRLL i else weightRow6LRRRLRLR i
def weightRow6LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 1026466246182105 else 1027277688820105
def weightRow6LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 1019849070479105 else 1020040323188105
def weightRow6LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow6LRRRLRRL i else weightRow6LRRRLRRR i
def weightRow6LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow6LRRRLRL i else weightRow6LRRRLRR i
def weightRow6LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow6LRRRLL i else weightRow6LRRRLR i
def weightRow6LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 1011372809813105 else 1012363789162105
def weightRow6LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 1002586709400105 else 1002176980673105
def weightRow6LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow6LRRRRLLL i else weightRow6LRRRRLLR i
def weightRow6LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 996363764765105 else 996898176097105
def weightRow6LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 990087950645105 else 989821942866105
def weightRow6LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow6LRRRRLRL i else weightRow6LRRRRLRR i
def weightRow6LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow6LRRRRLL i else weightRow6LRRRRLR i
def weightRow6LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 985119666246105 else 985227284425105
def weightRow6LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 983464187133105 else 983168352356105
def weightRow6LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow6LRRRRRLL i else weightRow6LRRRRRLR i
def weightRow6LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 981572806895105 else 981586563802105
def weightRow6LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 978407174045105 else 978075315936105
def weightRow6LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow6LRRRRRRL i else weightRow6LRRRRRRR i
def weightRow6LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow6LRRRRRL i else weightRow6LRRRRRR i
def weightRow6LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow6LRRRRL i else weightRow6LRRRRR i
def weightRow6LRRR (i : ℕ) : ℕ := if i < 240 then weightRow6LRRRL i else weightRow6LRRRR i
def weightRow6LRR (i : ℕ) : ℕ := if i < 224 then weightRow6LRRL i else weightRow6LRRR i
def weightRow6LR (i : ℕ) : ℕ := if i < 192 then weightRow6LRL i else weightRow6LRR i
def weightRow6L (i : ℕ) : ℕ := if i < 128 then weightRow6LL i else weightRow6LR i
def weightRow6RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 976595784918105 else 976659735726105
def weightRow6RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 978395956545105 else 978455091842105
def weightRow6RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow6RLLLLLLL i else weightRow6RLLLLLLR i
def weightRow6RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 980068609190105 else 980129278411105
def weightRow6RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 981647759509105 else 981705777047105
def weightRow6RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow6RLLLLLRL i else weightRow6RLLLLLRR i
def weightRow6RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow6RLLLLLL i else weightRow6RLLLLLR i
def weightRow6RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 983106425003105 else 983166534470105
def weightRow6RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 984454168957105 else 984510021076105
def weightRow6RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow6RLLLLRLL i else weightRow6RLLLLRLR i
def weightRow6RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 985733998176105 else 985791516683105
def weightRow6RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 986991302895105 else 987037369901105
def weightRow6RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow6RLLLLRRL i else weightRow6RLLLLRRR i
def weightRow6RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow6RLLLLRL i else weightRow6RLLLLRR i
def weightRow6RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow6RLLLLL i else weightRow6RLLLLR i
def weightRow6RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 988206097085105 else 988255936934105
def weightRow6RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 989464812324105 else 989496174475105
def weightRow6RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow6RLLLRLLL i else weightRow6RLLLRLLR i
def weightRow6RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 990740689010105 else 990765657310105
def weightRow6RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 992037542413105 else 992046239878105
def weightRow6RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow6RLLLRLRL i else weightRow6RLLLRLRR i
def weightRow6RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow6RLLLRLL i else weightRow6RLLLRLR i
def weightRow6RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 993284898550105 else 993282430464105
def weightRow6RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 994459439978105 else 994446888039105
def weightRow6RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow6RLLLRRLL i else weightRow6RLLLRRLR i
def weightRow6RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 995544713017105 else 995524907413105
def weightRow6RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 996576536338105 else 996556202561105
def weightRow6RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow6RLLLRRRL i else weightRow6RLLLRRRR i
def weightRow6RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow6RLLLRRL i else weightRow6RLLLRRR i
def weightRow6RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow6RLLLRL i else weightRow6RLLLRR i
def weightRow6RLLL (i : ℕ) : ℕ := if i < 272 then weightRow6RLLLL i else weightRow6RLLLR i
def weightRow6RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 997507292089105 else 997489966907105
def weightRow6RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 998380466451105 else 998370449169105
def weightRow6RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow6RLLRLLLL i else weightRow6RLLRLLLR i
def weightRow6RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 999214484738105 else 999200791883105
def weightRow6RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1000014275573105 else 999994666720105
def weightRow6RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow6RLLRLLRL i else weightRow6RLLRLLRR i
def weightRow6RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow6RLLRLLL i else weightRow6RLLRLLR i
def weightRow6RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1000761580713105 else 1000738472635105
def weightRow6RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1001425975458105 else 1001400487073105
def weightRow6RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow6RLLRLRLL i else weightRow6RLLRLRLR i
def weightRow6RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1002030482948105 else 1002001052721105
def weightRow6RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1002561756126105 else 1002533592857105
def weightRow6RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow6RLLRLRRL i else weightRow6RLLRLRRR i
def weightRow6RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow6RLLRLRL i else weightRow6RLLRLRR i
def weightRow6RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow6RLLRLL i else weightRow6RLLRLR i
def weightRow6RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1003022523488105 else 1003001218484105
def weightRow6RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1003428829191105 else 1003408973887105
def weightRow6RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow6RLLRRLLL i else weightRow6RLLRRLLR i
def weightRow6RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1003783248179105 else 1003759976712105
def weightRow6RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1004097601835105 else 1004072182991105
def weightRow6RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow6RLLRRLRL i else weightRow6RLLRRLRR i
def weightRow6RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow6RLLRRLL i else weightRow6RLLRRLR i
def weightRow6RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1004347509311105 else 1004321749214105
def weightRow6RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1004527734068105 else 1004508780911105
def weightRow6RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow6RLLRRRLL i else weightRow6RLLRRRLR i
def weightRow6RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1004624589166105 else 1004611509382105
def weightRow6RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1004699252168105 else 1004684141985105
def weightRow6RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow6RLLRRRRL i else weightRow6RLLRRRRR i
def weightRow6RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow6RLLRRRL i else weightRow6RLLRRRR i
def weightRow6RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow6RLLRRL i else weightRow6RLLRRR i
def weightRow6RLLR (i : ℕ) : ℕ := if i < 304 then weightRow6RLLRL i else weightRow6RLLRR i
def weightRow6RLL (i : ℕ) : ℕ := if i < 288 then weightRow6RLLL i else weightRow6RLLR i
def weightRow6RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1004698980911105 else 1004678949167105
def weightRow6RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1004697489082105 else 1004679347787105
def weightRow6RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow6RLRLLLLL i else weightRow6RLRLLLLR i
def weightRow6RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1004706149553105 else 1004683015784105
def weightRow6RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1004644971946105 else 1004621273348105
def weightRow6RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow6RLRLLLRL i else weightRow6RLRLLLRR i
def weightRow6RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow6RLRLLLL i else weightRow6RLRLLLR i
def weightRow6RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1004566960300105 else 1004548962732105
def weightRow6RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1004418322291105 else 1004409032969105
def weightRow6RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow6RLRLLRLL i else weightRow6RLRLLRLR i
def weightRow6RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1004223664147105 else 1004215591338105
def weightRow6RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1003985204169105 else 1003976743002105
def weightRow6RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow6RLRLLRRL i else weightRow6RLRLLRRR i
def weightRow6RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow6RLRLLRL i else weightRow6RLRLLRR i
def weightRow6RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow6RLRLLL i else weightRow6RLRLLR i
def weightRow6RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1003729525634105 else 1003719605615105
def weightRow6RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1003441862510105 else 1003435988189105
def weightRow6RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow6RLRLRLLL i else weightRow6RLRLRLLR i
def weightRow6RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 1003124042020105 else 1003128189328105
def weightRow6RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 1002773312277105 else 1002782454767105
def weightRow6RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow6RLRLRLRL i else weightRow6RLRLRLRR i
def weightRow6RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow6RLRLRLL i else weightRow6RLRLRLR i
def weightRow6RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 1002388962309105 else 1002398102725105
def weightRow6RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 1001979949130105 else 1001990493099105
def weightRow6RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow6RLRLRRLL i else weightRow6RLRLRRLR i
def weightRow6RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 1001528247959105 else 1001539502504105
def weightRow6RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 1001069539503105 else 1001078521694105
def weightRow6RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow6RLRLRRRL i else weightRow6RLRLRRRR i
def weightRow6RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow6RLRLRRL i else weightRow6RLRLRRR i
def weightRow6RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow6RLRLRL i else weightRow6RLRLRR i
def weightRow6RLRL (i : ℕ) : ℕ := if i < 336 then weightRow6RLRLL i else weightRow6RLRLR i
def weightRow6RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 1000621484222105 else 1000630759773105
def weightRow6RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 1000175362474105 else 1000197412201105
def weightRow6RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow6RLRRLLLL i else weightRow6RLRRLLLR i
def weightRow6RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 999734207801105 else 999764745711105
def weightRow6RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 999256887958105 else 999293790616105
def weightRow6RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow6RLRRLLRL i else weightRow6RLRRLLRR i
def weightRow6RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow6RLRRLLL i else weightRow6RLRRLLR i
def weightRow6RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 998797061370105 else 998832899828105
def weightRow6RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 998318208396105 else 998349958402105
def weightRow6RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow6RLRRLRLL i else weightRow6RLRRLRLR i
def weightRow6RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 997838601516105 else 997864160244105
def weightRow6RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 997391252699105 else 997404273082105
def weightRow6RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow6RLRRLRRL i else weightRow6RLRRLRRR i
def weightRow6RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow6RLRRLRL i else weightRow6RLRRLRR i
def weightRow6RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow6RLRRLL i else weightRow6RLRRLR i
def weightRow6RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 997039478383105 else 997049762554105
def weightRow6RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 996813589594105 else 996808991956105
def weightRow6RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow6RLRRRLLL i else weightRow6RLRRRLLR i
def weightRow6RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 996720166592105 else 996721600880105
def weightRow6RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 996720928258105 else 996713934894105
def weightRow6RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow6RLRRRLRL i else weightRow6RLRRRLRR i
def weightRow6RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow6RLRRRLL i else weightRow6RLRRRLR i
def weightRow6RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 996820279722105 else 996817972450105
def weightRow6RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 997000825459105 else 996996643629105
def weightRow6RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow6RLRRRRLL i else weightRow6RLRRRRLR i
def weightRow6RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 997210042712105 else 997210787568105
def weightRow6RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 997449457396105 else 997449346086105
def weightRow6RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow6RLRRRRRL i else weightRow6RLRRRRRR i
def weightRow6RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow6RLRRRRL i else weightRow6RLRRRRR i
def weightRow6RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow6RLRRRL i else weightRow6RLRRRR i
def weightRow6RLRR (i : ℕ) : ℕ := if i < 368 then weightRow6RLRRL i else weightRow6RLRRR i
def weightRow6RLR (i : ℕ) : ℕ := if i < 352 then weightRow6RLRL i else weightRow6RLRR i
def weightRow6RL (i : ℕ) : ℕ := if i < 320 then weightRow6RLL i else weightRow6RLR i
def weightRow6RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 997740309853105 else 997746554118105
def weightRow6RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 998071398665105 else 998075921911105
def weightRow6RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow6RRLLLLLL i else weightRow6RRLLLLLR i
def weightRow6RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 998372258235105 else 998375952646105
def weightRow6RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 998649743983105 else 998651801725105
def weightRow6RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow6RRLLLLRL i else weightRow6RRLLLLRR i
def weightRow6RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow6RRLLLLL i else weightRow6RRLLLLR i
def weightRow6RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 998904959823105 else 998905828244105
def weightRow6RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 999156017571105 else 999156198803105
def weightRow6RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow6RRLLLRLL i else weightRow6RRLLLRLR i
def weightRow6RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 999385213036105 else 999383972678105
def weightRow6RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 999587464219105 else 999585813806105
def weightRow6RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow6RRLLLRRL i else weightRow6RRLLLRRR i
def weightRow6RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow6RRLLLRL i else weightRow6RRLLLRR i
def weightRow6RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow6RRLLLL i else weightRow6RRLLLR i
def weightRow6RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 999776685110105 else 999771201449105
def weightRow6RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 999947534375105 else 999948147394105
def weightRow6RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow6RRLLRLLL i else weightRow6RRLLRLLR i
def weightRow6RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000121702003105 else 1000115327843105
def weightRow6RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000261273813105 else 1000257905433105
def weightRow6RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow6RRLLRLRL i else weightRow6RRLLRLRR i
def weightRow6RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow6RRLLRLL i else weightRow6RRLLRLR i
def weightRow6RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000394775058105 else 1000386571723105
def weightRow6RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000518591327105 else 1000512281549105
def weightRow6RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow6RRLLRRLL i else weightRow6RRLLRRLR i
def weightRow6RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000625490564105 else 1000618599577105
def weightRow6RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000689853019105 else 1000683535836105
def weightRow6RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow6RRLLRRRL i else weightRow6RRLLRRRR i
def weightRow6RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow6RRLLRRL i else weightRow6RRLLRRR i
def weightRow6RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow6RRLLRL i else weightRow6RRLLRR i
def weightRow6RRLL (i : ℕ) : ℕ := if i < 400 then weightRow6RRLLL i else weightRow6RRLLR i
def weightRow6RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000749362574105 else 1000745744116105
def weightRow6RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000804045860105 else 1000799675483105
def weightRow6RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow6RRLRLLLL i else weightRow6RRLRLLLR i
def weightRow6RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000858401911105 else 1000856237873105
def weightRow6RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000877331231105 else 1000874923512105
def weightRow6RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow6RRLRLLRL i else weightRow6RRLRLLRR i
def weightRow6RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow6RRLRLLL i else weightRow6RRLRLLR i
def weightRow6RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000893024050105 else 1000889745729105
def weightRow6RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000890413326105 else 1000891234633105
def weightRow6RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow6RRLRLRLL i else weightRow6RRLRLRLR i
def weightRow6RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000874374668105 else 1000871455419105
def weightRow6RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000856671147105 else 1000857543539105
def weightRow6RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow6RRLRLRRL i else weightRow6RRLRLRRR i
def weightRow6RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow6RRLRLRL i else weightRow6RRLRLRR i
def weightRow6RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow6RRLRLL i else weightRow6RRLRLR i
def weightRow6RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000842275439105 else 1000841850425105
def weightRow6RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000810078063105 else 1000814024233105
def weightRow6RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow6RRLRRLLL i else weightRow6RRLRRLLR i
def weightRow6RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000779517763105 else 1000776804920105
def weightRow6RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000728782367105 else 1000729074535105
def weightRow6RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow6RRLRRLRL i else weightRow6RRLRRLRR i
def weightRow6RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow6RRLRRLL i else weightRow6RRLRRLR i
def weightRow6RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000669668062105 else 1000666162122105
def weightRow6RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000599089436105 else 1000590238566105
def weightRow6RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow6RRLRRRLL i else weightRow6RRLRRRLR i
def weightRow6RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000538393125105 else 1000541032328105
def weightRow6RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000474163494105 else 1000472205374105
def weightRow6RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow6RRLRRRRL i else weightRow6RRLRRRRR i
def weightRow6RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow6RRLRRRL i else weightRow6RRLRRRR i
def weightRow6RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow6RRLRRL i else weightRow6RRLRRR i
def weightRow6RRLR (i : ℕ) : ℕ := if i < 432 then weightRow6RRLRL i else weightRow6RRLRR i
def weightRow6RRL (i : ℕ) : ℕ := if i < 416 then weightRow6RRLL i else weightRow6RRLR i
def weightRow6RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 1000428695829105 else 1000424158914105
def weightRow6RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 1000300973324105 else 1000302215361105
def weightRow6RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow6RRRLLLLL i else weightRow6RRRLLLLR i
def weightRow6RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 1000245864141105 else 1000245992642105
def weightRow6RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 1000220785649105 else 1000231026064105
def weightRow6RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow6RRRLLLRL i else weightRow6RRRLLLRR i
def weightRow6RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow6RRRLLLL i else weightRow6RRRLLLR i
def weightRow6RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 1000216013609105 else 1000215144720105
def weightRow6RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 1000184898951105 else 1000196165628105
def weightRow6RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow6RRRLLRLL i else weightRow6RRRLLRLR i
def weightRow6RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 1000141274346105 else 1000147458686105
def weightRow6RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 1000133032869105 else 1000145455168105
def weightRow6RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow6RRRLLRRL i else weightRow6RRRLLRRR i
def weightRow6RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow6RRRLLRL i else weightRow6RRRLLRR i
def weightRow6RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow6RRRLLL i else weightRow6RRRLLR i
def weightRow6RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 1000094940499105 else 1000097412816105
def weightRow6RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 1000028290777105 else 1000030088357105
def weightRow6RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow6RRRLRLLL i else weightRow6RRRLRLLR i
def weightRow6RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 1000036298306105 else 1000038724952105
def weightRow6RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 1000029758725105 else 1000030968703105
def weightRow6RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow6RRRLRLRL i else weightRow6RRRLRLRR i
def weightRow6RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow6RRRLRLL i else weightRow6RRRLRLR i
def weightRow6RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999991582345105 else 999986161381105
def weightRow6RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999908187360105 else 999905514965105
def weightRow6RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow6RRRLRRLL i else weightRow6RRRLRRLR i
def weightRow6RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999839932664105 else 999843485224105
def weightRow6RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999823769304105 else 999818631716105
def weightRow6RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow6RRRLRRRL i else weightRow6RRRLRRRR i
def weightRow6RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow6RRRLRRL i else weightRow6RRRLRRR i
def weightRow6RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow6RRRLRL i else weightRow6RRRLRR i
def weightRow6RRRL (i : ℕ) : ℕ := if i < 464 then weightRow6RRRLL i else weightRow6RRRLR i
def weightRow6RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999753525032105 else 999757683822105
def weightRow6RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999702233633105 else 999693789247105
def weightRow6RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow6RRRRLLLL i else weightRow6RRRRLLLR i
def weightRow6RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999667856308105 else 999675722844105
def weightRow6RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999683170649105 else 999693086859105
def weightRow6RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow6RRRRLLRL i else weightRow6RRRRLLRR i
def weightRow6RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow6RRRRLLL i else weightRow6RRRRLLR i
def weightRow6RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999629229383105 else 999644631662105
def weightRow6RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 999616419187105 else 999607704191105
def weightRow6RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow6RRRRLRLL i else weightRow6RRRRLRLR i
def weightRow6RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 999600270861105 else 999610748062105
def weightRow6RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 999646940987105 else 999643794618105
def weightRow6RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow6RRRRLRRL i else weightRow6RRRRLRRR i
def weightRow6RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow6RRRRLRL i else weightRow6RRRRLRR i
def weightRow6RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow6RRRRLL i else weightRow6RRRRLR i
def weightRow6RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 999627615663105 else 999640953717105
def weightRow6RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 999609223661105 else 999619027868105
def weightRow6RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow6RRRRRLLL i else weightRow6RRRRRLLR i
def weightRow6RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 999555333896105 else 999547480050105
def weightRow6RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 999498408791105 else 999492963681105
def weightRow6RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow6RRRRRLRL i else weightRow6RRRRRLRR i
def weightRow6RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow6RRRRRLL i else weightRow6RRRRRLR i
def weightRow6RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 999577892929105 else 999614191765105
def weightRow6RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 999750906773105 else 999742251911105
def weightRow6RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow6RRRRRRLL i else weightRow6RRRRRRLR i
def weightRow6RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 999781811766105 else 999822724246105
def weightRow6RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 999654569159105 else 999612175678105
def weightRow6RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow6RRRRRRRL i else weightRow6RRRRRRRR i
def weightRow6RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow6RRRRRRL i else weightRow6RRRRRRR i
def weightRow6RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow6RRRRRL i else weightRow6RRRRRR i
def weightRow6RRRR (i : ℕ) : ℕ := if i < 496 then weightRow6RRRRL i else weightRow6RRRRR i
def weightRow6RRR (i : ℕ) : ℕ := if i < 480 then weightRow6RRRL i else weightRow6RRRR i
def weightRow6RR (i : ℕ) : ℕ := if i < 448 then weightRow6RRL i else weightRow6RRR i
def weightRow6R (i : ℕ) : ℕ := if i < 384 then weightRow6RL i else weightRow6RR i
def weightRow6 (i : ℕ) : ℕ := if i < 256 then weightRow6L i else weightRow6R i
def weightRow7LLLLLLLL (i : ℕ) : ℕ := if i < 1 then 143633643335105 else 148975131505105
def weightRow7LLLLLLLR (i : ℕ) : ℕ := if i < 3 then 94494380540105 else 93726719861105
def weightRow7LLLLLLL (i : ℕ) : ℕ := if i < 2 then weightRow7LLLLLLLL i else weightRow7LLLLLLLR i
def weightRow7LLLLLLRL (i : ℕ) : ℕ := if i < 5 then 172062150236105 else 178566962010105
def weightRow7LLLLLLRR (i : ℕ) : ℕ := if i < 7 then 199708527112105 else 185864096680105
def weightRow7LLLLLLR (i : ℕ) : ℕ := if i < 6 then weightRow7LLLLLLRL i else weightRow7LLLLLLRR i
def weightRow7LLLLLL (i : ℕ) : ℕ := if i < 4 then weightRow7LLLLLLL i else weightRow7LLLLLLR i
def weightRow7LLLLLRLL (i : ℕ) : ℕ := if i < 9 then 206555587858105 else 212743434807105
def weightRow7LLLLLRLR (i : ℕ) : ℕ := if i < 11 then 301016466876105 else 311566151114105
def weightRow7LLLLLRL (i : ℕ) : ℕ := if i < 10 then weightRow7LLLLLRLL i else weightRow7LLLLLRLR i
def weightRow7LLLLLRRL (i : ℕ) : ℕ := if i < 13 then 295235729998105 else 294039790579105
def weightRow7LLLLLRRR (i : ℕ) : ℕ := if i < 15 then 278245897804105 else 265699603287105
def weightRow7LLLLLRR (i : ℕ) : ℕ := if i < 14 then weightRow7LLLLLRRL i else weightRow7LLLLLRRR i
def weightRow7LLLLLR (i : ℕ) : ℕ := if i < 12 then weightRow7LLLLLRL i else weightRow7LLLLLRR i
def weightRow7LLLLL (i : ℕ) : ℕ := if i < 8 then weightRow7LLLLLL i else weightRow7LLLLLR i
def weightRow7LLLLRLLL (i : ℕ) : ℕ := if i < 17 then 412309041697105 else 425544948359105
def weightRow7LLLLRLLR (i : ℕ) : ℕ := if i < 19 then 494471575811105 else 507517324492105
def weightRow7LLLLRLL (i : ℕ) : ℕ := if i < 18 then weightRow7LLLLRLLL i else weightRow7LLLLRLLR i
def weightRow7LLLLRLRL (i : ℕ) : ℕ := if i < 21 then 512466657201105 else 508880326952105
def weightRow7LLLLRLRR (i : ℕ) : ℕ := if i < 23 then 446772113472105 else 435850113283105
def weightRow7LLLLRLR (i : ℕ) : ℕ := if i < 22 then weightRow7LLLLRLRL i else weightRow7LLLLRLRR i
def weightRow7LLLLRL (i : ℕ) : ℕ := if i < 20 then weightRow7LLLLRLL i else weightRow7LLLLRLR i
def weightRow7LLLLRRLL (i : ℕ) : ℕ := if i < 25 then 641804300771105 else 627516826675105
def weightRow7LLLLRRLR (i : ℕ) : ℕ := if i < 27 then 606347608002105 else 609173091260105
def weightRow7LLLLRRL (i : ℕ) : ℕ := if i < 26 then weightRow7LLLLRRLL i else weightRow7LLLLRRLR i
def weightRow7LLLLRRRL (i : ℕ) : ℕ := if i < 29 then 395115873362105 else 401411296908105
def weightRow7LLLLRRRR (i : ℕ) : ℕ := if i < 31 then 494778123996105 else 503831385962105
def weightRow7LLLLRRR (i : ℕ) : ℕ := if i < 30 then weightRow7LLLLRRRL i else weightRow7LLLLRRRR i
def weightRow7LLLLRR (i : ℕ) : ℕ := if i < 28 then weightRow7LLLLRRL i else weightRow7LLLLRRR i
def weightRow7LLLLR (i : ℕ) : ℕ := if i < 24 then weightRow7LLLLRL i else weightRow7LLLLRR i
def weightRow7LLLL (i : ℕ) : ℕ := if i < 16 then weightRow7LLLLL i else weightRow7LLLLR i
def weightRow7LLLRLLLL (i : ℕ) : ℕ := if i < 33 then 653942737481105 else 645093455555105
def weightRow7LLLRLLLR (i : ℕ) : ℕ := if i < 35 then 852908915874105 else 904285712167105
def weightRow7LLLRLLL (i : ℕ) : ℕ := if i < 34 then weightRow7LLLRLLLL i else weightRow7LLLRLLLR i
def weightRow7LLLRLLRL (i : ℕ) : ℕ := if i < 37 then 1475958406011105 else 1418858821549105
def weightRow7LLLRLLRR (i : ℕ) : ℕ := if i < 39 then 1549230206920105 else 1569324974030105
def weightRow7LLLRLLR (i : ℕ) : ℕ := if i < 38 then weightRow7LLLRLLRL i else weightRow7LLLRLLRR i
def weightRow7LLLRLL (i : ℕ) : ℕ := if i < 36 then weightRow7LLLRLLL i else weightRow7LLLRLLR i
def weightRow7LLLRLRLL (i : ℕ) : ℕ := if i < 41 then 888964050607105 else 891547105856105
def weightRow7LLLRLRLR (i : ℕ) : ℕ := if i < 43 then 796344635202105 else 822089409795105
def weightRow7LLLRLRL (i : ℕ) : ℕ := if i < 42 then weightRow7LLLRLRLL i else weightRow7LLLRLRLR i
def weightRow7LLLRLRRL (i : ℕ) : ℕ := if i < 45 then 1002204390748105 else 925057558544105
def weightRow7LLLRLRRR (i : ℕ) : ℕ := if i < 47 then 893486724185105 else 914134650638105
def weightRow7LLLRLRR (i : ℕ) : ℕ := if i < 46 then weightRow7LLLRLRRL i else weightRow7LLLRLRRR i
def weightRow7LLLRLR (i : ℕ) : ℕ := if i < 44 then weightRow7LLLRLRL i else weightRow7LLLRLRR i
def weightRow7LLLRL (i : ℕ) : ℕ := if i < 40 then weightRow7LLLRLL i else weightRow7LLLRLR i
def weightRow7LLLRRLLL (i : ℕ) : ℕ := if i < 49 then 832076314729105 else 810919818151105
def weightRow7LLLRRLLR (i : ℕ) : ℕ := if i < 51 then 743761364915105 else 755791648102105
def weightRow7LLLRRLL (i : ℕ) : ℕ := if i < 50 then weightRow7LLLRRLLL i else weightRow7LLLRRLLR i
def weightRow7LLLRRLRL (i : ℕ) : ℕ := if i < 53 then 727993061624105 else 716958941298105
def weightRow7LLLRRLRR (i : ℕ) : ℕ := if i < 55 then 730047991203105 else 755094131072105
def weightRow7LLLRRLR (i : ℕ) : ℕ := if i < 54 then weightRow7LLLRRLRL i else weightRow7LLLRRLRR i
def weightRow7LLLRRL (i : ℕ) : ℕ := if i < 52 then weightRow7LLLRRLL i else weightRow7LLLRRLR i
def weightRow7LLLRRRLL (i : ℕ) : ℕ := if i < 57 then 937352738174105 else 940964799577105
def weightRow7LLLRRRLR (i : ℕ) : ℕ := if i < 59 then 762620331636105 else 756556627562105
def weightRow7LLLRRRL (i : ℕ) : ℕ := if i < 58 then weightRow7LLLRRRLL i else weightRow7LLLRRRLR i
def weightRow7LLLRRRRL (i : ℕ) : ℕ := if i < 61 then 802499085985105 else 774300044164105
def weightRow7LLLRRRRR (i : ℕ) : ℕ := if i < 63 then 650172758089105 else 650281473882105
def weightRow7LLLRRRR (i : ℕ) : ℕ := if i < 62 then weightRow7LLLRRRRL i else weightRow7LLLRRRRR i
def weightRow7LLLRRR (i : ℕ) : ℕ := if i < 60 then weightRow7LLLRRRL i else weightRow7LLLRRRR i
def weightRow7LLLRR (i : ℕ) : ℕ := if i < 56 then weightRow7LLLRRL i else weightRow7LLLRRR i
def weightRow7LLLR (i : ℕ) : ℕ := if i < 48 then weightRow7LLLRL i else weightRow7LLLRR i
def weightRow7LLL (i : ℕ) : ℕ := if i < 32 then weightRow7LLLL i else weightRow7LLLR i
def weightRow7LLRLLLLL (i : ℕ) : ℕ := if i < 65 then 660946979748105 else 659826828759105
def weightRow7LLRLLLLR (i : ℕ) : ℕ := if i < 67 then 807391640043105 else 835002133595105
def weightRow7LLRLLLL (i : ℕ) : ℕ := if i < 66 then weightRow7LLRLLLLL i else weightRow7LLRLLLLR i
def weightRow7LLRLLLRL (i : ℕ) : ℕ := if i < 69 then 814086518220105 else 820087690625105
def weightRow7LLRLLLRR (i : ℕ) : ℕ := if i < 71 then 1025917966292105 else 1022279981212105
def weightRow7LLRLLLR (i : ℕ) : ℕ := if i < 70 then weightRow7LLRLLLRL i else weightRow7LLRLLLRR i
def weightRow7LLRLLL (i : ℕ) : ℕ := if i < 68 then weightRow7LLRLLLL i else weightRow7LLRLLLR i
def weightRow7LLRLLRLL (i : ℕ) : ℕ := if i < 73 then 867876617571105 else 842360066879105
def weightRow7LLRLLRLR (i : ℕ) : ℕ := if i < 75 then 854506057154105 else 864841504611105
def weightRow7LLRLLRL (i : ℕ) : ℕ := if i < 74 then weightRow7LLRLLRLL i else weightRow7LLRLLRLR i
def weightRow7LLRLLRRL (i : ℕ) : ℕ := if i < 77 then 918499345784105 else 905741685984105
def weightRow7LLRLLRRR (i : ℕ) : ℕ := if i < 79 then 1000651449484105 else 1021211360276105
def weightRow7LLRLLRR (i : ℕ) : ℕ := if i < 78 then weightRow7LLRLLRRL i else weightRow7LLRLLRRR i
def weightRow7LLRLLR (i : ℕ) : ℕ := if i < 76 then weightRow7LLRLLRL i else weightRow7LLRLLRR i
def weightRow7LLRLL (i : ℕ) : ℕ := if i < 72 then weightRow7LLRLLL i else weightRow7LLRLLR i
def weightRow7LLRLRLLL (i : ℕ) : ℕ := if i < 81 then 1133785408646105 else 1112539941608105
def weightRow7LLRLRLLR (i : ℕ) : ℕ := if i < 83 then 1176879873275105 else 1254302504034105
def weightRow7LLRLRLL (i : ℕ) : ℕ := if i < 82 then weightRow7LLRLRLLL i else weightRow7LLRLRLLR i
def weightRow7LLRLRLRL (i : ℕ) : ℕ := if i < 85 then 1105145669717105 else 1080487724239105
def weightRow7LLRLRLRR (i : ℕ) : ℕ := if i < 87 then 1205800408456105 else 1203876228746105
def weightRow7LLRLRLR (i : ℕ) : ℕ := if i < 86 then weightRow7LLRLRLRL i else weightRow7LLRLRLRR i
def weightRow7LLRLRL (i : ℕ) : ℕ := if i < 84 then weightRow7LLRLRLL i else weightRow7LLRLRLR i
def weightRow7LLRLRRLL (i : ℕ) : ℕ := if i < 89 then 1926942666640105 else 1907160201403105
def weightRow7LLRLRRLR (i : ℕ) : ℕ := if i < 91 then 1828756372668105 else 1886755544012105
def weightRow7LLRLRRL (i : ℕ) : ℕ := if i < 90 then weightRow7LLRLRRLL i else weightRow7LLRLRRLR i
def weightRow7LLRLRRRL (i : ℕ) : ℕ := if i < 93 then 1356888699254105 else 1306515016331105
def weightRow7LLRLRRRR (i : ℕ) : ℕ := if i < 95 then 1128978915759105 else 1138180039286105
def weightRow7LLRLRRR (i : ℕ) : ℕ := if i < 94 then weightRow7LLRLRRRL i else weightRow7LLRLRRRR i
def weightRow7LLRLRR (i : ℕ) : ℕ := if i < 92 then weightRow7LLRLRRL i else weightRow7LLRLRRR i
def weightRow7LLRLR (i : ℕ) : ℕ := if i < 88 then weightRow7LLRLRL i else weightRow7LLRLRR i
def weightRow7LLRL (i : ℕ) : ℕ := if i < 80 then weightRow7LLRLL i else weightRow7LLRLR i
def weightRow7LLRRLLLL (i : ℕ) : ℕ := if i < 97 then 1013229463520105 else 1004531870896105
def weightRow7LLRRLLLR (i : ℕ) : ℕ := if i < 99 then 932910483658105 else 926736089552105
def weightRow7LLRRLLL (i : ℕ) : ℕ := if i < 98 then weightRow7LLRRLLLL i else weightRow7LLRRLLLR i
def weightRow7LLRRLLRL (i : ℕ) : ℕ := if i < 101 then 1164771706606105 else 1161923693746105
def weightRow7LLRRLLRR (i : ℕ) : ℕ := if i < 103 then 1211119491952105 else 1225569550900105
def weightRow7LLRRLLR (i : ℕ) : ℕ := if i < 102 then weightRow7LLRRLLRL i else weightRow7LLRRLLRR i
def weightRow7LLRRLL (i : ℕ) : ℕ := if i < 100 then weightRow7LLRRLLL i else weightRow7LLRRLLR i
def weightRow7LLRRLRLL (i : ℕ) : ℕ := if i < 105 then 1045186741338105 else 1056668912552105
def weightRow7LLRRLRLR (i : ℕ) : ℕ := if i < 107 then 1142502265145105 else 1146876316456105
def weightRow7LLRRLRL (i : ℕ) : ℕ := if i < 106 then weightRow7LLRRLRLL i else weightRow7LLRRLRLR i
def weightRow7LLRRLRRL (i : ℕ) : ℕ := if i < 109 then 1166923496488105 else 1154527942466105
def weightRow7LLRRLRRR (i : ℕ) : ℕ := if i < 111 then 1109830164846105 else 1096849115156105
def weightRow7LLRRLRR (i : ℕ) : ℕ := if i < 110 then weightRow7LLRRLRRL i else weightRow7LLRRLRRR i
def weightRow7LLRRLR (i : ℕ) : ℕ := if i < 108 then weightRow7LLRRLRL i else weightRow7LLRRLRR i
def weightRow7LLRRL (i : ℕ) : ℕ := if i < 104 then weightRow7LLRRLL i else weightRow7LLRRLR i
def weightRow7LLRRRLLL (i : ℕ) : ℕ := if i < 113 then 971480037130105 else 984275074166105
def weightRow7LLRRRLLR (i : ℕ) : ℕ := if i < 115 then 1019589334238105 else 1021264562939105
def weightRow7LLRRRLL (i : ℕ) : ℕ := if i < 114 then weightRow7LLRRRLLL i else weightRow7LLRRRLLR i
def weightRow7LLRRRLRL (i : ℕ) : ℕ := if i < 117 then 1057919247155105 else 1047700370279105
def weightRow7LLRRRLRR (i : ℕ) : ℕ := if i < 119 then 978953927509105 else 972827055190105
def weightRow7LLRRRLR (i : ℕ) : ℕ := if i < 118 then weightRow7LLRRRLRL i else weightRow7LLRRRLRR i
def weightRow7LLRRRL (i : ℕ) : ℕ := if i < 116 then weightRow7LLRRRLL i else weightRow7LLRRRLR i
def weightRow7LLRRRRLL (i : ℕ) : ℕ := if i < 121 then 970273417678105 else 984307898654105
def weightRow7LLRRRRLR (i : ℕ) : ℕ := if i < 123 then 980926169677105 else 974733712047105
def weightRow7LLRRRRL (i : ℕ) : ℕ := if i < 122 then weightRow7LLRRRRLL i else weightRow7LLRRRRLR i
def weightRow7LLRRRRRL (i : ℕ) : ℕ := if i < 125 then 912884613431105 else 913870878560105
def weightRow7LLRRRRRR (i : ℕ) : ℕ := if i < 127 then 984717633771105 else 979540581878105
def weightRow7LLRRRRR (i : ℕ) : ℕ := if i < 126 then weightRow7LLRRRRRL i else weightRow7LLRRRRRR i
def weightRow7LLRRRR (i : ℕ) : ℕ := if i < 124 then weightRow7LLRRRRL i else weightRow7LLRRRRR i
def weightRow7LLRRR (i : ℕ) : ℕ := if i < 120 then weightRow7LLRRRL i else weightRow7LLRRRR i
def weightRow7LLRR (i : ℕ) : ℕ := if i < 112 then weightRow7LLRRL i else weightRow7LLRRR i
def weightRow7LLR (i : ℕ) : ℕ := if i < 96 then weightRow7LLRL i else weightRow7LLRR i
def weightRow7LL (i : ℕ) : ℕ := if i < 64 then weightRow7LLL i else weightRow7LLR i
def weightRow7LRLLLLLL (i : ℕ) : ℕ := if i < 129 then 851124070078105 else 851200646674105
def weightRow7LRLLLLLR (i : ℕ) : ℕ := if i < 131 then 862179927505105 else 862175084493105
def weightRow7LRLLLLL (i : ℕ) : ℕ := if i < 130 then weightRow7LRLLLLLL i else weightRow7LRLLLLLR i
def weightRow7LRLLLLRL (i : ℕ) : ℕ := if i < 133 then 874179868789105 else 874182680685105
def weightRow7LRLLLLRR (i : ℕ) : ℕ := if i < 135 then 885148547333105 else 885055361438105
def weightRow7LRLLLLR (i : ℕ) : ℕ := if i < 134 then weightRow7LRLLLLRL i else weightRow7LRLLLLRR i
def weightRow7LRLLLL (i : ℕ) : ℕ := if i < 132 then weightRow7LRLLLLL i else weightRow7LRLLLLR i
def weightRow7LRLLLRLL (i : ℕ) : ℕ := if i < 137 then 895859504988105 else 895976435222105
def weightRow7LRLLLRLR (i : ℕ) : ℕ := if i < 139 then 906630769967105 else 906642293476105
def weightRow7LRLLLRL (i : ℕ) : ℕ := if i < 138 then weightRow7LRLLLRLL i else weightRow7LRLLLRLR i
def weightRow7LRLLLRRL (i : ℕ) : ℕ := if i < 141 then 916085150278105 else 915940610658105
def weightRow7LRLLLRRR (i : ℕ) : ℕ := if i < 143 then 925777913897105 else 925664528341105
def weightRow7LRLLLRR (i : ℕ) : ℕ := if i < 142 then weightRow7LRLLLRRL i else weightRow7LRLLLRRR i
def weightRow7LRLLLR (i : ℕ) : ℕ := if i < 140 then weightRow7LRLLLRL i else weightRow7LRLLLRR i
def weightRow7LRLLL (i : ℕ) : ℕ := if i < 136 then weightRow7LRLLLL i else weightRow7LRLLLR i
def weightRow7LRLLRLLL (i : ℕ) : ℕ := if i < 145 then 935901935890105 else 935971998678105
def weightRow7LRLLRLLR (i : ℕ) : ℕ := if i < 147 then 944088510282105 else 943947808937105
def weightRow7LRLLRLL (i : ℕ) : ℕ := if i < 146 then weightRow7LRLLRLLL i else weightRow7LRLLRLLR i
def weightRow7LRLLRLRL (i : ℕ) : ℕ := if i < 149 then 951109575890105 else 950768835198105
def weightRow7LRLLRLRR (i : ℕ) : ℕ := if i < 151 then 957960803441105 else 957681819866105
def weightRow7LRLLRLR (i : ℕ) : ℕ := if i < 150 then weightRow7LRLLRLRL i else weightRow7LRLLRLRR i
def weightRow7LRLLRL (i : ℕ) : ℕ := if i < 148 then weightRow7LRLLRLL i else weightRow7LRLLRLR i
def weightRow7LRLLRRLL (i : ℕ) : ℕ := if i < 153 then 965952563826105 else 965809881809105
def weightRow7LRLLRRLR (i : ℕ) : ℕ := if i < 155 then 971015638639105 else 971088937775105
def weightRow7LRLLRRL (i : ℕ) : ℕ := if i < 154 then weightRow7LRLLRRLL i else weightRow7LRLLRRLR i
def weightRow7LRLLRRRL (i : ℕ) : ℕ := if i < 157 then 976711028261105 else 976769096875105
def weightRow7LRLLRRRR (i : ℕ) : ℕ := if i < 159 then 985802087305105 else 985762862322105
def weightRow7LRLLRRR (i : ℕ) : ℕ := if i < 158 then weightRow7LRLLRRRL i else weightRow7LRLLRRRR i
def weightRow7LRLLRR (i : ℕ) : ℕ := if i < 156 then weightRow7LRLLRRL i else weightRow7LRLLRRR i
def weightRow7LRLLR (i : ℕ) : ℕ := if i < 152 then weightRow7LRLLRL i else weightRow7LRLLRR i
def weightRow7LRLL (i : ℕ) : ℕ := if i < 144 then weightRow7LRLLL i else weightRow7LRLLR i
def weightRow7LRLRLLLL (i : ℕ) : ℕ := if i < 161 then 993473283608105 else 993282424523105
def weightRow7LRLRLLLR (i : ℕ) : ℕ := if i < 163 then 998759479577105 else 998727380528105
def weightRow7LRLRLLL (i : ℕ) : ℕ := if i < 162 then weightRow7LRLRLLLL i else weightRow7LRLRLLLR i
def weightRow7LRLRLLRL (i : ℕ) : ℕ := if i < 165 then 1001027628491105 else 1000176831994105
def weightRow7LRLRLLRR (i : ℕ) : ℕ := if i < 167 then 993622665578105 else 993614183048105
def weightRow7LRLRLLR (i : ℕ) : ℕ := if i < 166 then weightRow7LRLRLLRL i else weightRow7LRLRLLRR i
def weightRow7LRLRLL (i : ℕ) : ℕ := if i < 164 then weightRow7LRLRLLL i else weightRow7LRLRLLR i
def weightRow7LRLRLRLL (i : ℕ) : ℕ := if i < 169 then 984950098079105 else 984653120911105
def weightRow7LRLRLRLR (i : ℕ) : ℕ := if i < 171 then 986446611604105 else 986115722323105
def weightRow7LRLRLRL (i : ℕ) : ℕ := if i < 170 then weightRow7LRLRLRLL i else weightRow7LRLRLRLR i
def weightRow7LRLRLRRL (i : ℕ) : ℕ := if i < 173 then 989410007038105 else 988664189316105
def weightRow7LRLRLRRR (i : ℕ) : ℕ := if i < 175 then 989218236308105 else 989656468192105
def weightRow7LRLRLRR (i : ℕ) : ℕ := if i < 174 then weightRow7LRLRLRRL i else weightRow7LRLRLRRR i
def weightRow7LRLRLR (i : ℕ) : ℕ := if i < 172 then weightRow7LRLRLRL i else weightRow7LRLRLRR i
def weightRow7LRLRL (i : ℕ) : ℕ := if i < 168 then weightRow7LRLRLL i else weightRow7LRLRLR i
def weightRow7LRLRRLLL (i : ℕ) : ℕ := if i < 177 then 990715045155105 else 990843386835105
def weightRow7LRLRRLLR (i : ℕ) : ℕ := if i < 179 then 993195388154105 else 993665128402105
def weightRow7LRLRRLL (i : ℕ) : ℕ := if i < 178 then weightRow7LRLRRLLL i else weightRow7LRLRRLLR i
def weightRow7LRLRRLRL (i : ℕ) : ℕ := if i < 181 then 997089097421105 else 997379878900105
def weightRow7LRLRRLRR (i : ℕ) : ℕ := if i < 183 then 1001296354626105 else 1001760308891105
def weightRow7LRLRRLR (i : ℕ) : ℕ := if i < 182 then weightRow7LRLRRLRL i else weightRow7LRLRRLRR i
def weightRow7LRLRRL (i : ℕ) : ℕ := if i < 180 then weightRow7LRLRRLL i else weightRow7LRLRRLR i
def weightRow7LRLRRRLL (i : ℕ) : ℕ := if i < 185 then 1005528605087105 else 1005603203350105
def weightRow7LRLRRRLR (i : ℕ) : ℕ := if i < 187 then 1006595526905105 else 1006624684969105
def weightRow7LRLRRRL (i : ℕ) : ℕ := if i < 186 then weightRow7LRLRRRLL i else weightRow7LRLRRRLR i
def weightRow7LRLRRRRL (i : ℕ) : ℕ := if i < 189 then 1010418414376105 else 1010517058202105
def weightRow7LRLRRRRR (i : ℕ) : ℕ := if i < 191 then 1013665001259105 else 1014220378048105
def weightRow7LRLRRRR (i : ℕ) : ℕ := if i < 190 then weightRow7LRLRRRRL i else weightRow7LRLRRRRR i
def weightRow7LRLRRR (i : ℕ) : ℕ := if i < 188 then weightRow7LRLRRRL i else weightRow7LRLRRRR i
def weightRow7LRLRR (i : ℕ) : ℕ := if i < 184 then weightRow7LRLRRL i else weightRow7LRLRRR i
def weightRow7LRLR (i : ℕ) : ℕ := if i < 176 then weightRow7LRLRL i else weightRow7LRLRR i
def weightRow7LRL (i : ℕ) : ℕ := if i < 160 then weightRow7LRLL i else weightRow7LRLR i
def weightRow7LRRLLLLL (i : ℕ) : ℕ := if i < 193 then 1019333486773105 else 1019909485587105
def weightRow7LRRLLLLR (i : ℕ) : ℕ := if i < 195 then 1024933660580105 else 1025526263678105
def weightRow7LRRLLLL (i : ℕ) : ℕ := if i < 194 then weightRow7LRRLLLLL i else weightRow7LRRLLLLR i
def weightRow7LRRLLLRL (i : ℕ) : ℕ := if i < 197 then 1028333121005105 else 1028508333450105
def weightRow7LRRLLLRR (i : ℕ) : ℕ := if i < 199 then 1031678947548105 else 1031752377072105
def weightRow7LRRLLLR (i : ℕ) : ℕ := if i < 198 then weightRow7LRRLLLRL i else weightRow7LRRLLLRR i
def weightRow7LRRLLL (i : ℕ) : ℕ := if i < 196 then weightRow7LRRLLLL i else weightRow7LRRLLLR i
def weightRow7LRRLLRLL (i : ℕ) : ℕ := if i < 201 then 1031770357198105 else 1031913405325105
def weightRow7LRRLLRLR (i : ℕ) : ℕ := if i < 203 then 1034338658304105 else 1034878393703105
def weightRow7LRRLLRL (i : ℕ) : ℕ := if i < 202 then weightRow7LRRLLRLL i else weightRow7LRRLLRLR i
def weightRow7LRRLLRRL (i : ℕ) : ℕ := if i < 205 then 1037145901091105 else 1037523842854105
def weightRow7LRRLLRRR (i : ℕ) : ℕ := if i < 207 then 1038989731985105 else 1039574207879105
def weightRow7LRRLLRR (i : ℕ) : ℕ := if i < 206 then weightRow7LRRLLRRL i else weightRow7LRRLLRRR i
def weightRow7LRRLLR (i : ℕ) : ℕ := if i < 204 then weightRow7LRRLLRL i else weightRow7LRRLLRR i
def weightRow7LRRLL (i : ℕ) : ℕ := if i < 200 then weightRow7LRRLLL i else weightRow7LRRLLR i
def weightRow7LRRLRLLL (i : ℕ) : ℕ := if i < 209 then 1039580615450105 else 1039859401148105
def weightRow7LRRLRLLR (i : ℕ) : ℕ := if i < 211 then 1038122041021105 else 1038720404886105
def weightRow7LRRLRLL (i : ℕ) : ℕ := if i < 210 then weightRow7LRRLRLLL i else weightRow7LRRLRLLR i
def weightRow7LRRLRLRL (i : ℕ) : ℕ := if i < 213 then 1035946327326105 else 1035367882134105
def weightRow7LRRLRLRR (i : ℕ) : ℕ := if i < 215 then 1034850872247105 else 1034680735597105
def weightRow7LRRLRLR (i : ℕ) : ℕ := if i < 214 then weightRow7LRRLRLRL i else weightRow7LRRLRLRR i
def weightRow7LRRLRL (i : ℕ) : ℕ := if i < 212 then weightRow7LRRLRLL i else weightRow7LRRLRLR i
def weightRow7LRRLRRLL (i : ℕ) : ℕ := if i < 217 then 1032177883285105 else 1031987247462105
def weightRow7LRRLRRLR (i : ℕ) : ℕ := if i < 219 then 1018209290545105 else 1018297167516105
def weightRow7LRRLRRL (i : ℕ) : ℕ := if i < 218 then weightRow7LRRLRRLL i else weightRow7LRRLRRLR i
def weightRow7LRRLRRRL (i : ℕ) : ℕ := if i < 221 then 1005540438001105 else 1004759365301105
def weightRow7LRRLRRRR (i : ℕ) : ℕ := if i < 223 then 1000061856618105 else 1000050956199105
def weightRow7LRRLRRR (i : ℕ) : ℕ := if i < 222 then weightRow7LRRLRRRL i else weightRow7LRRLRRRR i
def weightRow7LRRLRR (i : ℕ) : ℕ := if i < 220 then weightRow7LRRLRRL i else weightRow7LRRLRRR i
def weightRow7LRRLR (i : ℕ) : ℕ := if i < 216 then weightRow7LRRLRL i else weightRow7LRRLRR i
def weightRow7LRRL (i : ℕ) : ℕ := if i < 208 then weightRow7LRRLL i else weightRow7LRRLR i
def weightRow7LRRRLLLL (i : ℕ) : ℕ := if i < 225 then 998049792264105 else 997893944633105
def weightRow7LRRRLLLR (i : ℕ) : ℕ := if i < 227 then 997806831030105 else 997802677000105
def weightRow7LRRRLLL (i : ℕ) : ℕ := if i < 226 then weightRow7LRRRLLLL i else weightRow7LRRRLLLR i
def weightRow7LRRRLLRL (i : ℕ) : ℕ := if i < 229 then 998819008034105 else 998902951512105
def weightRow7LRRRLLRR (i : ℕ) : ℕ := if i < 231 then 996232052537105 else 996346184923105
def weightRow7LRRRLLR (i : ℕ) : ℕ := if i < 230 then weightRow7LRRRLLRL i else weightRow7LRRRLLRR i
def weightRow7LRRRLL (i : ℕ) : ℕ := if i < 228 then weightRow7LRRRLLL i else weightRow7LRRRLLR i
def weightRow7LRRRLRLL (i : ℕ) : ℕ := if i < 233 then 992872384060105 else 992777792466105
def weightRow7LRRRLRLR (i : ℕ) : ℕ := if i < 235 then 992053700178105 else 991775329929105
def weightRow7LRRRLRL (i : ℕ) : ℕ := if i < 234 then weightRow7LRRRLRLL i else weightRow7LRRRLRLR i
def weightRow7LRRRLRRL (i : ℕ) : ℕ := if i < 237 then 989702688494105 else 989351008183105
def weightRow7LRRRLRRR (i : ℕ) : ℕ := if i < 239 then 986938285890105 else 986767909990105
def weightRow7LRRRLRR (i : ℕ) : ℕ := if i < 238 then weightRow7LRRRLRRL i else weightRow7LRRRLRRR i
def weightRow7LRRRLR (i : ℕ) : ℕ := if i < 236 then weightRow7LRRRLRL i else weightRow7LRRRLRR i
def weightRow7LRRRL (i : ℕ) : ℕ := if i < 232 then weightRow7LRRRLL i else weightRow7LRRRLR i
def weightRow7LRRRRLLL (i : ℕ) : ℕ := if i < 241 then 985018252287105 else 985057488704105
def weightRow7LRRRRLLR (i : ℕ) : ℕ := if i < 243 then 985229276935105 else 985068455961105
def weightRow7LRRRRLL (i : ℕ) : ℕ := if i < 242 then weightRow7LRRRRLLL i else weightRow7LRRRRLLR i
def weightRow7LRRRRLRL (i : ℕ) : ℕ := if i < 245 then 984692951445105 else 984499394406105
def weightRow7LRRRRLRR (i : ℕ) : ℕ := if i < 247 then 983550197533105 else 983517381464105
def weightRow7LRRRRLR (i : ℕ) : ℕ := if i < 246 then weightRow7LRRRRLRL i else weightRow7LRRRRLRR i
def weightRow7LRRRRL (i : ℕ) : ℕ := if i < 244 then weightRow7LRRRRLL i else weightRow7LRRRRLR i
def weightRow7LRRRRRLL (i : ℕ) : ℕ := if i < 249 then 983624529095105 else 983684544613105
def weightRow7LRRRRRLR (i : ℕ) : ℕ := if i < 251 then 983832726308105 else 983673348125105
def weightRow7LRRRRRL (i : ℕ) : ℕ := if i < 250 then weightRow7LRRRRRLL i else weightRow7LRRRRRLR i
def weightRow7LRRRRRRL (i : ℕ) : ℕ := if i < 253 then 983878016754105 else 983819654586105
def weightRow7LRRRRRRR (i : ℕ) : ℕ := if i < 255 then 984989637646105 else 984904464336105
def weightRow7LRRRRRR (i : ℕ) : ℕ := if i < 254 then weightRow7LRRRRRRL i else weightRow7LRRRRRRR i
def weightRow7LRRRRR (i : ℕ) : ℕ := if i < 252 then weightRow7LRRRRRL i else weightRow7LRRRRRR i
def weightRow7LRRRR (i : ℕ) : ℕ := if i < 248 then weightRow7LRRRRL i else weightRow7LRRRRR i
def weightRow7LRRR (i : ℕ) : ℕ := if i < 240 then weightRow7LRRRL i else weightRow7LRRRR i
def weightRow7LRR (i : ℕ) : ℕ := if i < 224 then weightRow7LRRL i else weightRow7LRRR i
def weightRow7LR (i : ℕ) : ℕ := if i < 192 then weightRow7LRL i else weightRow7LRR i
def weightRow7L (i : ℕ) : ℕ := if i < 128 then weightRow7LL i else weightRow7LR i
def weightRow7RLLLLLLL (i : ℕ) : ℕ := if i < 257 then 984995211039105 else 984996579575105
def weightRow7RLLLLLLR (i : ℕ) : ℕ := if i < 259 then 987087005542105 else 987087390939105
def weightRow7RLLLLLL (i : ℕ) : ℕ := if i < 258 then weightRow7RLLLLLLL i else weightRow7RLLLLLLR i
def weightRow7RLLLLLRL (i : ℕ) : ℕ := if i < 261 then 989038979959105 else 989038847299105
def weightRow7RLLLLLRR (i : ℕ) : ℕ := if i < 263 then 990833592208105 else 990833380386105
def weightRow7RLLLLLR (i : ℕ) : ℕ := if i < 262 then weightRow7RLLLLLRL i else weightRow7RLLLLLRR i
def weightRow7RLLLLL (i : ℕ) : ℕ := if i < 260 then weightRow7RLLLLLL i else weightRow7RLLLLLR i
def weightRow7RLLLLRLL (i : ℕ) : ℕ := if i < 265 then 992484722363105 else 992485864321105
def weightRow7RLLLLRLR (i : ℕ) : ℕ := if i < 267 then 993994269441105 else 993993550981105
def weightRow7RLLLLRL (i : ℕ) : ℕ := if i < 266 then weightRow7RLLLLRLL i else weightRow7RLLLLRLR i
def weightRow7RLLLLRRL (i : ℕ) : ℕ := if i < 269 then 995359010202105 else 995358234720105
def weightRow7RLLLLRRR (i : ℕ) : ℕ := if i < 271 then 996597306607105 else 996598748546105
def weightRow7RLLLLRR (i : ℕ) : ℕ := if i < 270 then weightRow7RLLLLRRL i else weightRow7RLLLLRRR i
def weightRow7RLLLLR (i : ℕ) : ℕ := if i < 268 then weightRow7RLLLLRL i else weightRow7RLLLLRR i
def weightRow7RLLLL (i : ℕ) : ℕ := if i < 264 then weightRow7RLLLLL i else weightRow7RLLLLR i
def weightRow7RLLLRLLL (i : ℕ) : ℕ := if i < 273 then 997703484943105 else 997706563179105
def weightRow7RLLLRLLR (i : ℕ) : ℕ := if i < 275 then 998668653580105 else 998670589957105
def weightRow7RLLLRLL (i : ℕ) : ℕ := if i < 274 then weightRow7RLLLRLLL i else weightRow7RLLLRLLR i
def weightRow7RLLLRLRL (i : ℕ) : ℕ := if i < 277 then 999520913925105 else 999525067655105
def weightRow7RLLLRLRR (i : ℕ) : ℕ := if i < 279 then 1000276742432105 else 1000286299439105
def weightRow7RLLLRLR (i : ℕ) : ℕ := if i < 278 then weightRow7RLLLRLRL i else weightRow7RLLLRLRR i
def weightRow7RLLLRL (i : ℕ) : ℕ := if i < 276 then weightRow7RLLLRLL i else weightRow7RLLLRLR i
def weightRow7RLLLRRLL (i : ℕ) : ℕ := if i < 281 then 1000937249426105 else 1000951008775105
def weightRow7RLLLRRLR (i : ℕ) : ℕ := if i < 283 then 1001483136781105 else 1001499613176105
def weightRow7RLLLRRL (i : ℕ) : ℕ := if i < 282 then weightRow7RLLLRRLL i else weightRow7RLLLRRLR i
def weightRow7RLLLRRRL (i : ℕ) : ℕ := if i < 285 then 1001958358523105 else 1001974505730105
def weightRow7RLLLRRRR (i : ℕ) : ℕ := if i < 287 then 1002352113620105 else 1002367619412105
def weightRow7RLLLRRR (i : ℕ) : ℕ := if i < 286 then weightRow7RLLLRRRL i else weightRow7RLLLRRRR i
def weightRow7RLLLRR (i : ℕ) : ℕ := if i < 284 then weightRow7RLLLRRL i else weightRow7RLLLRRR i
def weightRow7RLLLR (i : ℕ) : ℕ := if i < 280 then weightRow7RLLLRL i else weightRow7RLLLRR i
def weightRow7RLLL (i : ℕ) : ℕ := if i < 272 then weightRow7RLLLL i else weightRow7RLLLR i
def weightRow7RLLRLLLL (i : ℕ) : ℕ := if i < 289 then 1002610021350105 else 1002626185276105
def weightRow7RLLRLLLR (i : ℕ) : ℕ := if i < 291 then 1002751965333105 else 1002771513595105
def weightRow7RLLRLLL (i : ℕ) : ℕ := if i < 290 then weightRow7RLLRLLLL i else weightRow7RLLRLLLR i
def weightRow7RLLRLLRL (i : ℕ) : ℕ := if i < 293 then 1002813998104105 else 1002833839358105
def weightRow7RLLRLLRR (i : ℕ) : ℕ := if i < 295 then 1002841925115105 else 1002875020312105
def weightRow7RLLRLLR (i : ℕ) : ℕ := if i < 294 then weightRow7RLLRLLRL i else weightRow7RLLRLLRR i
def weightRow7RLLRLL (i : ℕ) : ℕ := if i < 292 then weightRow7RLLRLLL i else weightRow7RLLRLLR i
def weightRow7RLLRLRLL (i : ℕ) : ℕ := if i < 297 then 1002985401626105 else 1003019638814105
def weightRow7RLLRLRLR (i : ℕ) : ℕ := if i < 299 then 1003266235486105 else 1003305745683105
def weightRow7RLLRLRL (i : ℕ) : ℕ := if i < 298 then weightRow7RLLRLRLL i else weightRow7RLLRLRLR i
def weightRow7RLLRLRRL (i : ℕ) : ℕ := if i < 301 then 1003528334287105 else 1003573451910105
def weightRow7RLLRLRRR (i : ℕ) : ℕ := if i < 303 then 1003748591243105 else 1003805945539105
def weightRow7RLLRLRR (i : ℕ) : ℕ := if i < 302 then weightRow7RLLRLRRL i else weightRow7RLLRLRRR i
def weightRow7RLLRLR (i : ℕ) : ℕ := if i < 300 then weightRow7RLLRLRL i else weightRow7RLLRLRR i
def weightRow7RLLRL (i : ℕ) : ℕ := if i < 296 then weightRow7RLLRLL i else weightRow7RLLRLR i
def weightRow7RLLRRLLL (i : ℕ) : ℕ := if i < 305 then 1003975392039105 else 1004026917591105
def weightRow7RLLRRLLR (i : ℕ) : ℕ := if i < 307 then 1004182167875105 else 1004232454560105
def weightRow7RLLRRLL (i : ℕ) : ℕ := if i < 306 then weightRow7RLLRRLLL i else weightRow7RLLRRLLR i
def weightRow7RLLRRLRL (i : ℕ) : ℕ := if i < 309 then 1004352951833105 else 1004396749815105
def weightRow7RLLRRLRR (i : ℕ) : ℕ := if i < 311 then 1004465847251105 else 1004505616980105
def weightRow7RLLRRLR (i : ℕ) : ℕ := if i < 310 then weightRow7RLLRRLRL i else weightRow7RLLRRLRR i
def weightRow7RLLRRL (i : ℕ) : ℕ := if i < 308 then weightRow7RLLRRLL i else weightRow7RLLRRLR i
def weightRow7RLLRRRLL (i : ℕ) : ℕ := if i < 313 then 1004514898512105 else 1004547983032105
def weightRow7RLLRRRLR (i : ℕ) : ℕ := if i < 315 then 1004499064621105 else 1004531509317105
def weightRow7RLLRRRL (i : ℕ) : ℕ := if i < 314 then weightRow7RLLRRRLL i else weightRow7RLLRRRLR i
def weightRow7RLLRRRRL (i : ℕ) : ℕ := if i < 317 then 1004466024367105 else 1004498353516105
def weightRow7RLLRRRRR (i : ℕ) : ℕ := if i < 319 then 1004372644042105 else 1004404293742105
def weightRow7RLLRRRR (i : ℕ) : ℕ := if i < 318 then weightRow7RLLRRRRL i else weightRow7RLLRRRRR i
def weightRow7RLLRRR (i : ℕ) : ℕ := if i < 316 then weightRow7RLLRRRL i else weightRow7RLLRRRR i
def weightRow7RLLRR (i : ℕ) : ℕ := if i < 312 then weightRow7RLLRRL i else weightRow7RLLRRR i
def weightRow7RLLR (i : ℕ) : ℕ := if i < 304 then weightRow7RLLRL i else weightRow7RLLRR i
def weightRow7RLL (i : ℕ) : ℕ := if i < 288 then weightRow7RLLL i else weightRow7RLLR i
def weightRow7RLRLLLLL (i : ℕ) : ℕ := if i < 321 then 1004227075509105 else 1004250590598105
def weightRow7RLRLLLLR (i : ℕ) : ℕ := if i < 323 then 1003990132798105 else 1004004936299105
def weightRow7RLRLLLL (i : ℕ) : ℕ := if i < 322 then weightRow7RLRLLLLL i else weightRow7RLRLLLLR i
def weightRow7RLRLLLRL (i : ℕ) : ℕ := if i < 325 then 1003661764892105 else 1003667579276105
def weightRow7RLRLLLRR (i : ℕ) : ℕ := if i < 327 then 1003275750036105 else 1003278816384105
def weightRow7RLRLLLR (i : ℕ) : ℕ := if i < 326 then weightRow7RLRLLLRL i else weightRow7RLRLLLRR i
def weightRow7RLRLLL (i : ℕ) : ℕ := if i < 324 then weightRow7RLRLLLL i else weightRow7RLRLLLR i
def weightRow7RLRLLRLL (i : ℕ) : ℕ := if i < 329 then 1002831859363105 else 1002834061528105
def weightRow7RLRLLRLR (i : ℕ) : ℕ := if i < 331 then 1002379768457105 else 1002379654067105
def weightRow7RLRLLRL (i : ℕ) : ℕ := if i < 330 then weightRow7RLRLLRLL i else weightRow7RLRLLRLR i
def weightRow7RLRLLRRL (i : ℕ) : ℕ := if i < 333 then 1001880385893105 else 1001872023954105
def weightRow7RLRLLRRR (i : ℕ) : ℕ := if i < 335 then 1001329278709105 else 1001315243232105
def weightRow7RLRLLRR (i : ℕ) : ℕ := if i < 334 then weightRow7RLRLLRRL i else weightRow7RLRLLRRR i
def weightRow7RLRLLR (i : ℕ) : ℕ := if i < 332 then weightRow7RLRLLRL i else weightRow7RLRLLRR i
def weightRow7RLRLL (i : ℕ) : ℕ := if i < 328 then weightRow7RLRLLL i else weightRow7RLRLLR i
def weightRow7RLRLRLLL (i : ℕ) : ℕ := if i < 337 then 1000741245580105 else 1000718133669105
def weightRow7RLRLRLLR (i : ℕ) : ℕ := if i < 339 then 1000135469977105 else 1000107350653105
def weightRow7RLRLRLL (i : ℕ) : ℕ := if i < 338 then weightRow7RLRLRLLL i else weightRow7RLRLRLLR i
def weightRow7RLRLRLRL (i : ℕ) : ℕ := if i < 341 then 999543048985105 else 999505458545105
def weightRow7RLRLRLRR (i : ℕ) : ℕ := if i < 343 then 998975169449105 else 998945835093105
def weightRow7RLRLRLR (i : ℕ) : ℕ := if i < 342 then weightRow7RLRLRLRL i else weightRow7RLRLRLRR i
def weightRow7RLRLRL (i : ℕ) : ℕ := if i < 340 then weightRow7RLRLRLL i else weightRow7RLRLRLR i
def weightRow7RLRLRRLL (i : ℕ) : ℕ := if i < 345 then 998415237814105 else 998387274543105
def weightRow7RLRLRRLR (i : ℕ) : ℕ := if i < 347 then 997888375079105 else 997862672744105
def weightRow7RLRLRRL (i : ℕ) : ℕ := if i < 346 then weightRow7RLRLRRLL i else weightRow7RLRLRRLR i
def weightRow7RLRLRRRL (i : ℕ) : ℕ := if i < 349 then 997571443146105 else 997544485039105
def weightRow7RLRLRRRR (i : ℕ) : ℕ := if i < 351 then 997448241000105 else 997433088614105
def weightRow7RLRLRRR (i : ℕ) : ℕ := if i < 350 then weightRow7RLRLRRRL i else weightRow7RLRLRRRR i
def weightRow7RLRLRR (i : ℕ) : ℕ := if i < 348 then weightRow7RLRLRRL i else weightRow7RLRLRRR i
def weightRow7RLRLR (i : ℕ) : ℕ := if i < 344 then weightRow7RLRLRL i else weightRow7RLRLRR i
def weightRow7RLRL (i : ℕ) : ℕ := if i < 336 then weightRow7RLRLL i else weightRow7RLRLR i
def weightRow7RLRRLLLL (i : ℕ) : ℕ := if i < 353 then 997409339122105 else 997394437305105
def weightRow7RLRRLLLR (i : ℕ) : ℕ := if i < 355 then 997401817682105 else 997389126863105
def weightRow7RLRRLLL (i : ℕ) : ℕ := if i < 354 then weightRow7RLRRLLLL i else weightRow7RLRRLLLR i
def weightRow7RLRRLLRL (i : ℕ) : ℕ := if i < 357 then 997398335263105 else 997385056043105
def weightRow7RLRRLLRR (i : ℕ) : ℕ := if i < 359 then 997377899590105 else 997363090371105
def weightRow7RLRRLLR (i : ℕ) : ℕ := if i < 358 then weightRow7RLRRLLRL i else weightRow7RLRRLLRR i
def weightRow7RLRRLL (i : ℕ) : ℕ := if i < 356 then weightRow7RLRRLLL i else weightRow7RLRRLLR i
def weightRow7RLRRLRLL (i : ℕ) : ℕ := if i < 361 then 997397703474105 else 997381260520105
def weightRow7RLRRLRLR (i : ℕ) : ℕ := if i < 363 then 997471672586105 else 997456584612105
def weightRow7RLRRLRL (i : ℕ) : ℕ := if i < 362 then weightRow7RLRRLRLL i else weightRow7RLRRLRLR i
def weightRow7RLRRLRRL (i : ℕ) : ℕ := if i < 365 then 997561368978105 else 997550313526105
def weightRow7RLRRLRRR (i : ℕ) : ℕ := if i < 367 then 997688524362105 else 997682657211105
def weightRow7RLRRLRR (i : ℕ) : ℕ := if i < 366 then weightRow7RLRRLRRL i else weightRow7RLRRLRRR i
def weightRow7RLRRLR (i : ℕ) : ℕ := if i < 364 then weightRow7RLRRLRL i else weightRow7RLRRLRR i
def weightRow7RLRRL (i : ℕ) : ℕ := if i < 360 then weightRow7RLRRLL i else weightRow7RLRRLR i
def weightRow7RLRRRLLL (i : ℕ) : ℕ := if i < 369 then 997859604006105 else 997856475263105
def weightRow7RLRRRLLR (i : ℕ) : ℕ := if i < 371 then 998063618126105 else 998059765758105
def weightRow7RLRRRLL (i : ℕ) : ℕ := if i < 370 then weightRow7RLRRRLLL i else weightRow7RLRRRLLR i
def weightRow7RLRRRLRL (i : ℕ) : ℕ := if i < 373 then 998266481179105 else 998264888415105
def weightRow7RLRRRLRR (i : ℕ) : ℕ := if i < 375 then 998479929510105 else 998481215251105
def weightRow7RLRRRLR (i : ℕ) : ℕ := if i < 374 then weightRow7RLRRRLRL i else weightRow7RLRRRLRR i
def weightRow7RLRRRL (i : ℕ) : ℕ := if i < 372 then weightRow7RLRRRLL i else weightRow7RLRRRLR i
def weightRow7RLRRRRLL (i : ℕ) : ℕ := if i < 377 then 998714597944105 else 998716167753105
def weightRow7RLRRRRLR (i : ℕ) : ℕ := if i < 379 then 998949254772105 else 998949787607105
def weightRow7RLRRRRL (i : ℕ) : ℕ := if i < 378 then weightRow7RLRRRRLL i else weightRow7RLRRRRLR i
def weightRow7RLRRRRRL (i : ℕ) : ℕ := if i < 381 then 999185428103105 else 999188613296105
def weightRow7RLRRRRRR (i : ℕ) : ℕ := if i < 383 then 999420482427105 else 999424398025105
def weightRow7RLRRRRR (i : ℕ) : ℕ := if i < 382 then weightRow7RLRRRRRL i else weightRow7RLRRRRRR i
def weightRow7RLRRRR (i : ℕ) : ℕ := if i < 380 then weightRow7RLRRRRL i else weightRow7RLRRRRR i
def weightRow7RLRRR (i : ℕ) : ℕ := if i < 376 then weightRow7RLRRRL i else weightRow7RLRRRR i
def weightRow7RLRR (i : ℕ) : ℕ := if i < 368 then weightRow7RLRRL i else weightRow7RLRRR i
def weightRow7RLR (i : ℕ) : ℕ := if i < 352 then weightRow7RLRL i else weightRow7RLRR i
def weightRow7RL (i : ℕ) : ℕ := if i < 320 then weightRow7RLL i else weightRow7RLR i
def weightRow7RRLLLLLL (i : ℕ) : ℕ := if i < 385 then 999646030310105 else 999651816951105
def weightRow7RRLLLLLR (i : ℕ) : ℕ := if i < 387 then 999875672809105 else 999882198591105
def weightRow7RRLLLLL (i : ℕ) : ℕ := if i < 386 then weightRow7RRLLLLLL i else weightRow7RRLLLLLR i
def weightRow7RRLLLLRL (i : ℕ) : ℕ := if i < 389 then 1000068789834105 else 1000075093543105
def weightRow7RRLLLLRR (i : ℕ) : ℕ := if i < 391 then 1000239072187105 else 1000245376053105
def weightRow7RRLLLLR (i : ℕ) : ℕ := if i < 390 then weightRow7RRLLLLRL i else weightRow7RRLLLLRR i
def weightRow7RRLLLL (i : ℕ) : ℕ := if i < 388 then weightRow7RRLLLLL i else weightRow7RRLLLLR i
def weightRow7RRLLLRLL (i : ℕ) : ℕ := if i < 393 then 1000376959030105 else 1000381533469105
def weightRow7RRLLLRLR (i : ℕ) : ℕ := if i < 395 then 1000498114388105 else 1000504957111105
def weightRow7RRLLLRL (i : ℕ) : ℕ := if i < 394 then weightRow7RRLLLRLL i else weightRow7RRLLLRLR i
def weightRow7RRLLLRRL (i : ℕ) : ℕ := if i < 397 then 1000596378295105 else 1000601884804105
def weightRow7RRLLLRRR (i : ℕ) : ℕ := if i < 399 then 1000665868513105 else 1000671928061105
def weightRow7RRLLLRR (i : ℕ) : ℕ := if i < 398 then weightRow7RRLLLRRL i else weightRow7RRLLLRRR i
def weightRow7RRLLLR (i : ℕ) : ℕ := if i < 396 then weightRow7RRLLLRL i else weightRow7RRLLLRR i
def weightRow7RRLLL (i : ℕ) : ℕ := if i < 392 then weightRow7RRLLLL i else weightRow7RRLLLR i
def weightRow7RRLLRLLL (i : ℕ) : ℕ := if i < 401 then 1000723766338105 else 1000728911382105
def weightRow7RRLLRLLR (i : ℕ) : ℕ := if i < 403 then 1000766476151105 else 1000772634066105
def weightRow7RRLLRLL (i : ℕ) : ℕ := if i < 402 then weightRow7RRLLRLLL i else weightRow7RRLLRLLR i
def weightRow7RRLLRLRL (i : ℕ) : ℕ := if i < 405 then 1000798994711105 else 1000807128409105
def weightRow7RRLLRLRR (i : ℕ) : ℕ := if i < 407 then 1000815529233105 else 1000823676246105
def weightRow7RRLLRLR (i : ℕ) : ℕ := if i < 406 then weightRow7RRLLRLRL i else weightRow7RRLLRLRR i
def weightRow7RRLLRL (i : ℕ) : ℕ := if i < 404 then weightRow7RRLLRLL i else weightRow7RRLLRLR i
def weightRow7RRLLRRLL (i : ℕ) : ℕ := if i < 409 then 1000812155048105 else 1000818115325105
def weightRow7RRLLRRLR (i : ℕ) : ℕ := if i < 411 then 1000813205864105 else 1000820403971105
def weightRow7RRLLRRL (i : ℕ) : ℕ := if i < 410 then weightRow7RRLLRRLL i else weightRow7RRLLRRLR i
def weightRow7RRLLRRRL (i : ℕ) : ℕ := if i < 413 then 1000801104480105 else 1000807420142105
def weightRow7RRLLRRRR (i : ℕ) : ℕ := if i < 415 then 1000783487549105 else 1000790861093105
def weightRow7RRLLRRR (i : ℕ) : ℕ := if i < 414 then weightRow7RRLLRRRL i else weightRow7RRLLRRRR i
def weightRow7RRLLRR (i : ℕ) : ℕ := if i < 412 then weightRow7RRLLRRL i else weightRow7RRLLRRR i
def weightRow7RRLLR (i : ℕ) : ℕ := if i < 408 then weightRow7RRLLRL i else weightRow7RRLLRR i
def weightRow7RRLL (i : ℕ) : ℕ := if i < 400 then weightRow7RRLLL i else weightRow7RRLLR i
def weightRow7RRLRLLLL (i : ℕ) : ℕ := if i < 417 then 1000759575389105 else 1000762784886105
def weightRow7RRLRLLLR (i : ℕ) : ℕ := if i < 419 then 1000725795465105 else 1000732776938105
def weightRow7RRLRLLL (i : ℕ) : ℕ := if i < 418 then weightRow7RRLRLLLL i else weightRow7RRLRLLLR i
def weightRow7RRLRLLRL (i : ℕ) : ℕ := if i < 421 then 1000695292312105 else 1000701226863105
def weightRow7RRLRLLRR (i : ℕ) : ℕ := if i < 423 then 1000673651139105 else 1000678179574105
def weightRow7RRLRLLR (i : ℕ) : ℕ := if i < 422 then weightRow7RRLRLLRL i else weightRow7RRLRLLRR i
def weightRow7RRLRLL (i : ℕ) : ℕ := if i < 420 then weightRow7RRLRLLL i else weightRow7RRLRLLR i
def weightRow7RRLRLRLL (i : ℕ) : ℕ := if i < 425 then 1000622641651105 else 1000630421432105
def weightRow7RRLRLRLR (i : ℕ) : ℕ := if i < 427 then 1000569685557105 else 1000576527912105
def weightRow7RRLRLRL (i : ℕ) : ℕ := if i < 426 then weightRow7RRLRLRLL i else weightRow7RRLRLRLR i
def weightRow7RRLRLRRL (i : ℕ) : ℕ := if i < 429 then 1000537987903105 else 1000541989617105
def weightRow7RRLRLRRR (i : ℕ) : ℕ := if i < 431 then 1000507739130105 else 1000507116659105
def weightRow7RRLRLRR (i : ℕ) : ℕ := if i < 430 then weightRow7RRLRLRRL i else weightRow7RRLRLRRR i
def weightRow7RRLRLR (i : ℕ) : ℕ := if i < 428 then weightRow7RRLRLRL i else weightRow7RRLRLRR i
def weightRow7RRLRL (i : ℕ) : ℕ := if i < 424 then weightRow7RRLRLL i else weightRow7RRLRLR i
def weightRow7RRLRRLLL (i : ℕ) : ℕ := if i < 433 then 1000474165434105 else 1000473566511105
def weightRow7RRLRRLLR (i : ℕ) : ℕ := if i < 435 then 1000406265613105 else 1000405098671105
def weightRow7RRLRRLL (i : ℕ) : ℕ := if i < 434 then weightRow7RRLRRLLL i else weightRow7RRLRRLLR i
def weightRow7RRLRRLRL (i : ℕ) : ℕ := if i < 437 then 1000322201630105 else 1000327876557105
def weightRow7RRLRRLRR (i : ℕ) : ℕ := if i < 439 then 1000268162214105 else 1000270413194105
def weightRow7RRLRRLR (i : ℕ) : ℕ := if i < 438 then weightRow7RRLRRLRL i else weightRow7RRLRRLRR i
def weightRow7RRLRRL (i : ℕ) : ℕ := if i < 436 then weightRow7RRLRRLL i else weightRow7RRLRRLR i
def weightRow7RRLRRRLL (i : ℕ) : ℕ := if i < 441 then 1000215385146105 else 1000216411512105
def weightRow7RRLRRRLR (i : ℕ) : ℕ := if i < 443 then 1000174413898105 else 1000171617013105
def weightRow7RRLRRRL (i : ℕ) : ℕ := if i < 442 then weightRow7RRLRRRLL i else weightRow7RRLRRRLR i
def weightRow7RRLRRRRL (i : ℕ) : ℕ := if i < 445 then 1000088227915105 else 1000086466193105
def weightRow7RRLRRRRR (i : ℕ) : ℕ := if i < 447 then 1000030789614105 else 1000024715224105
def weightRow7RRLRRRR (i : ℕ) : ℕ := if i < 446 then weightRow7RRLRRRRL i else weightRow7RRLRRRRR i
def weightRow7RRLRRR (i : ℕ) : ℕ := if i < 444 then weightRow7RRLRRRL i else weightRow7RRLRRRR i
def weightRow7RRLRR (i : ℕ) : ℕ := if i < 440 then weightRow7RRLRRL i else weightRow7RRLRRR i
def weightRow7RRLR (i : ℕ) : ℕ := if i < 432 then weightRow7RRLRL i else weightRow7RRLRR i
def weightRow7RRL (i : ℕ) : ℕ := if i < 416 then weightRow7RRLL i else weightRow7RRLR i
def weightRow7RRRLLLLL (i : ℕ) : ℕ := if i < 449 then 999954526467105 else 999954650432105
def weightRow7RRRLLLLR (i : ℕ) : ℕ := if i < 451 then 999845084968105 else 999844740618105
def weightRow7RRRLLLL (i : ℕ) : ℕ := if i < 450 then weightRow7RRRLLLLL i else weightRow7RRRLLLLR i
def weightRow7RRRLLLRL (i : ℕ) : ℕ := if i < 453 then 999764637689105 else 999763618696105
def weightRow7RRRLLLRR (i : ℕ) : ℕ := if i < 455 then 999742461508105 else 999737952327105
def weightRow7RRRLLLR (i : ℕ) : ℕ := if i < 454 then weightRow7RRRLLLRL i else weightRow7RRRLLLRR i
def weightRow7RRRLLL (i : ℕ) : ℕ := if i < 452 then weightRow7RRRLLLL i else weightRow7RRRLLLR i
def weightRow7RRRLLRLL (i : ℕ) : ℕ := if i < 457 then 999714562119105 else 999717561557105
def weightRow7RRRLLRLR (i : ℕ) : ℕ := if i < 459 then 999678691299105 else 999671025286105
def weightRow7RRRLLRL (i : ℕ) : ℕ := if i < 458 then weightRow7RRRLLRLL i else weightRow7RRRLLRLR i
def weightRow7RRRLLRRL (i : ℕ) : ℕ := if i < 461 then 999634973981105 else 999646032789105
def weightRow7RRRLLRRR (i : ℕ) : ℕ := if i < 463 then 999598083292105 else 999606063967105
def weightRow7RRRLLRR (i : ℕ) : ℕ := if i < 462 then weightRow7RRRLLRRL i else weightRow7RRRLLRRR i
def weightRow7RRRLLR (i : ℕ) : ℕ := if i < 460 then weightRow7RRRLLRL i else weightRow7RRRLLRR i
def weightRow7RRRLL (i : ℕ) : ℕ := if i < 456 then weightRow7RRRLLL i else weightRow7RRRLLR i
def weightRow7RRRLRLLL (i : ℕ) : ℕ := if i < 465 then 999596221461105 else 999592998501105
def weightRow7RRRLRLLR (i : ℕ) : ℕ := if i < 467 then 999607363820105 else 999590105984105
def weightRow7RRRLRLL (i : ℕ) : ℕ := if i < 466 then weightRow7RRRLRLLL i else weightRow7RRRLRLLR i
def weightRow7RRRLRLRL (i : ℕ) : ℕ := if i < 469 then 999618859672105 else 999615663141105
def weightRow7RRRLRLRR (i : ℕ) : ℕ := if i < 471 then 999600783894105 else 999590697605105
def weightRow7RRRLRLR (i : ℕ) : ℕ := if i < 470 then weightRow7RRRLRLRL i else weightRow7RRRLRLRR i
def weightRow7RRRLRL (i : ℕ) : ℕ := if i < 468 then weightRow7RRRLRLL i else weightRow7RRRLRLR i
def weightRow7RRRLRRLL (i : ℕ) : ℕ := if i < 473 then 999566350093105 else 999568619507105
def weightRow7RRRLRRLR (i : ℕ) : ℕ := if i < 475 then 999588548712105 else 999574586762105
def weightRow7RRRLRRL (i : ℕ) : ℕ := if i < 474 then weightRow7RRRLRRLL i else weightRow7RRRLRRLR i
def weightRow7RRRLRRRL (i : ℕ) : ℕ := if i < 477 then 999627782188105 else 999624821799105
def weightRow7RRRLRRRR (i : ℕ) : ℕ := if i < 479 then 999702102650105 else 999706264328105
def weightRow7RRRLRRR (i : ℕ) : ℕ := if i < 478 then weightRow7RRRLRRRL i else weightRow7RRRLRRRR i
def weightRow7RRRLRR (i : ℕ) : ℕ := if i < 476 then weightRow7RRRLRRL i else weightRow7RRRLRRR i
def weightRow7RRRLR (i : ℕ) : ℕ := if i < 472 then weightRow7RRRLRL i else weightRow7RRRLRR i
def weightRow7RRRL (i : ℕ) : ℕ := if i < 464 then weightRow7RRRLL i else weightRow7RRRLR i
def weightRow7RRRRLLLL (i : ℕ) : ℕ := if i < 481 then 999791678260105 else 999807351242105
def weightRow7RRRRLLLR (i : ℕ) : ℕ := if i < 483 then 999871786365105 else 999860871910105
def weightRow7RRRRLLL (i : ℕ) : ℕ := if i < 482 then weightRow7RRRRLLLL i else weightRow7RRRRLLLR i
def weightRow7RRRRLLRL (i : ℕ) : ℕ := if i < 485 then 999925623645105 else 999912348361105
def weightRow7RRRRLLRR (i : ℕ) : ℕ := if i < 487 then 999895747658105 else 999902014481105
def weightRow7RRRRLLR (i : ℕ) : ℕ := if i < 486 then weightRow7RRRRLLRL i else weightRow7RRRRLLRR i
def weightRow7RRRRLL (i : ℕ) : ℕ := if i < 484 then weightRow7RRRRLLL i else weightRow7RRRRLLR i
def weightRow7RRRRLRLL (i : ℕ) : ℕ := if i < 489 then 999952667974105 else 999967393140105
def weightRow7RRRRLRLR (i : ℕ) : ℕ := if i < 491 then 1000081359471105 else 1000094644965105
def weightRow7RRRRLRL (i : ℕ) : ℕ := if i < 490 then weightRow7RRRRLRLL i else weightRow7RRRRLRLR i
def weightRow7RRRRLRRL (i : ℕ) : ℕ := if i < 493 then 1000238177104105 else 1000238269200105
def weightRow7RRRRLRRR (i : ℕ) : ℕ := if i < 495 then 1000239770292105 else 1000236367948105
def weightRow7RRRRLRR (i : ℕ) : ℕ := if i < 494 then weightRow7RRRRLRRL i else weightRow7RRRRLRRR i
def weightRow7RRRRLR (i : ℕ) : ℕ := if i < 492 then weightRow7RRRRLRL i else weightRow7RRRRLRR i
def weightRow7RRRRL (i : ℕ) : ℕ := if i < 488 then weightRow7RRRRLL i else weightRow7RRRRLR i
def weightRow7RRRRRLLL (i : ℕ) : ℕ := if i < 497 then 1000208576462105 else 1000213533118105
def weightRow7RRRRRLLR (i : ℕ) : ℕ := if i < 499 then 1000264165608105 else 1000265818602105
def weightRow7RRRRRLL (i : ℕ) : ℕ := if i < 498 then weightRow7RRRRRLLL i else weightRow7RRRRRLLR i
def weightRow7RRRRRLRL (i : ℕ) : ℕ := if i < 501 then 1000232546842105 else 1000226909772105
def weightRow7RRRRRLRR (i : ℕ) : ℕ := if i < 503 then 1000204925670105 else 1000195314753105
def weightRow7RRRRRLR (i : ℕ) : ℕ := if i < 502 then weightRow7RRRRRLRL i else weightRow7RRRRRLRR i
def weightRow7RRRRRL (i : ℕ) : ℕ := if i < 500 then weightRow7RRRRRLL i else weightRow7RRRRRLR i
def weightRow7RRRRRRLL (i : ℕ) : ℕ := if i < 505 then 1000233403762105 else 1000224748898105
def weightRow7RRRRRRLR (i : ℕ) : ℕ := if i < 507 then 1000098638926105 else 1000091202996105
def weightRow7RRRRRRL (i : ℕ) : ℕ := if i < 506 then weightRow7RRRRRRLL i else weightRow7RRRRRRLR i
def weightRow7RRRRRRRL (i : ℕ) : ℕ := if i < 509 then 1000186463958105 else 1000196712220105
def weightRow7RRRRRRRR (i : ℕ) : ℕ := if i < 511 then 999933244146105 else 999927120320105
def weightRow7RRRRRRR (i : ℕ) : ℕ := if i < 510 then weightRow7RRRRRRRL i else weightRow7RRRRRRRR i
def weightRow7RRRRRR (i : ℕ) : ℕ := if i < 508 then weightRow7RRRRRRL i else weightRow7RRRRRRR i
def weightRow7RRRRR (i : ℕ) : ℕ := if i < 504 then weightRow7RRRRRL i else weightRow7RRRRRR i
def weightRow7RRRR (i : ℕ) : ℕ := if i < 496 then weightRow7RRRRL i else weightRow7RRRRR i
def weightRow7RRR (i : ℕ) : ℕ := if i < 480 then weightRow7RRRL i else weightRow7RRRR i
def weightRow7RR (i : ℕ) : ℕ := if i < 448 then weightRow7RRL i else weightRow7RRR i
def weightRow7R (i : ℕ) : ℕ := if i < 384 then weightRow7RL i else weightRow7RR i
def weightRow7 (i : ℕ) : ℕ := if i < 256 then weightRow7L i else weightRow7R i
def mixRowLL (i : ℕ) : ℕ := if i < 1 then 422972356839 else 56455640755
def mixRowLR (i : ℕ) : ℕ := if i < 3 then 2342754306 else 221227015251
def mixRowL (i : ℕ) : ℕ := if i < 2 then mixRowLL i else mixRowLR i
def mixRowRL (i : ℕ) : ℕ := if i < 5 then 143927345853 else 20182087393
def mixRowRR (i : ℕ) : ℕ := if i < 7 then 58064372370 else 74828427233
def mixRowR (i : ℕ) : ℕ := if i < 6 then mixRowRL i else mixRowRR i
def mixRow (i : ℕ) : ℕ := if i < 4 then mixRowL i else mixRowR i

def kernelNat (r i : ℕ) : ℕ :=
  match r with
  | 0 => kernelRow0 i
  | 1 => kernelRow1 i
  | 2 => kernelRow2 i
  | 3 => kernelRow3 i
  | 4 => kernelRow4 i
  | 5 => kernelRow5 i
  | 6 => kernelRow6 i
  | _ => kernelRow7 i

def weightNat (r i : ℕ) : ℕ :=
  match r with
  | 0 => weightRow0 i
  | 1 => weightRow1 i
  | 2 => weightRow2 i
  | 3 => weightRow3 i
  | 4 => weightRow4 i
  | 5 => weightRow5 i
  | 6 => weightRow6 i
  | _ => weightRow7 i

def mixN (r : Fin 8) : ℕ := mixRow r.val
def kernelN (r : Fin 8) (i : Fin 128) : ℕ := kernelNat r.val i.val
def weightN (r : Fin 8) (j : Fin 512) : ℕ := weightNat r.val j.val


def mixDen : ℕ := 1000000000000
def kernelDen : ℕ := 1000000000000
def weightDen : ℕ := 1000000000000000

def mixQ (m : Fin 8 → ℕ) (r : Fin 8) : ℚ := m r / mixDen

def kernelQ (p : Fin 8 → Fin 128 → ℕ) (r : Fin 8) (i : Fin 128) : ℚ :=
  p r i / kernelDen

def weightQ (w : Fin 8 → Fin 512 → ℕ) (r : Fin 8) (j : Fin 512) : ℚ :=
  w r j / weightDen

def extW (w : Fin 8 → Fin 512 → ℕ) (r : Fin 8) (j : ℕ) : ℕ :=
  if hj : j < 512 then w r ⟨j,hj⟩ else weightDen

def extQ (w : Fin 8 → Fin 512 → ℕ) (r : Fin 8) (j : ℕ) : ℚ :=
  if hj : j < 512 then weightQ w r ⟨j,hj⟩ else 1

lemma extQ_eq (w : Fin 8 → Fin 512 → ℕ) (r : Fin 8) (j : ℕ) :
    extQ w r j = (extW w r j : ℚ) / weightDen := by
  unfold extQ extW weightQ
  split_ifs <;> norm_num [weightDen]

def coverN (m : Fin 8 → ℕ) (p : Fin 8 → Fin 128 → ℕ)
    (w : Fin 8 → Fin 512 → ℕ) (q : ℕ) : ℕ :=
  ∑ r, m r * ∑ i, p r i * extW w r (q+i.val)

lemma cover_eq (m : Fin 8 → ℕ) (p : Fin 8 → Fin 128 → ℕ)
    (w : Fin 8 → Fin 512 → ℕ) (q : ℕ) :
    (∑ r, mixQ m r * ∑ i, kernelQ p r i * extQ w r (q+i.val)) =
      (coverN m p w q : ℚ) / (mixDen * kernelDen * weightDen) := by
  unfold mixQ kernelQ coverN
  simp_rw [extQ_eq, div_mul_div_comm, ← Finset.sum_div, div_mul_div_comm, ← Finset.sum_div]
  push_cast
  ring

def energyAN (m : Fin 8 → ℕ) (p : Fin 8 → Fin 128 → ℕ) : ℕ :=
  ∑ r, m r * ∑ i, (p r i)^2

def weightNormN (m : Fin 8 → ℕ) (w : Fin 8 → Fin 512 → ℕ) : ℕ :=
  ∑ r, m r * ∑ j, (w r j)^2

def energyBZ (m : Fin 8 → ℕ) (w : Fin 8 → Fin 512 → ℕ) : ℤ :=
  2 * (weightNormN m w : ℤ) - 7 * mixDen * weightDen^2 * 128

lemma energyA_eq (m : Fin 8 → ℕ) (p : Fin 8 → Fin 128 → ℕ) :
    (128 * ∑ r, mixQ m r * ∑ i, (kernelQ p r i)^2) =
    128 * (energyAN m p : ℚ) / (mixDen * kernelDen^2) := by
  unfold mixQ kernelQ energyAN
  simp_rw [div_pow, ← Finset.sum_div, div_mul_div_comm, ← Finset.sum_div]
  push_cast
  ring

lemma energyB_eq (m : Fin 8 → ℕ) (w : Fin 8 → Fin 512 → ℕ) :
    (1 + 2 * ((∑ r, mixQ m r * ∑ j, (weightQ w r j)^2) / 128 - 4)) =
    (energyBZ m w : ℚ) / (mixDen * weightDen^2 * 128) := by
  unfold mixQ weightQ energyBZ weightNormN
  simp_rw [div_pow, ← Finset.sum_div, div_mul_div_comm, ← Finset.sum_div]
  push_cast
  norm_num [mixDen, weightDen]
  ring



/-- A primitive recursive sum that constructs no index list or finite set. -/
def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumN f n + f n

lemma sumN_eq_sum_range (f : ℕ → ℕ) (n : ℕ) :
    sumN f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => simp only [sumN, Finset.sum_range_succ, ih]

lemma sumN_eq_sum_fin (f : ℕ → ℕ) (n : ℕ) :
    sumN f n = ∑ i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range, sumN_eq_sum_range]

/-- The existing constant extension, expressed entirely with natural indices. -/
def extNatW (w : ℕ → ℕ → ℕ) (r j : ℕ) : ℕ :=
  if j < 512 then w r j else weightDen

lemma extW_eq_extNatW (w : ℕ → ℕ → ℕ) (r : Fin 8) (j : ℕ) :
    extW (fun r j => w r.val j.val) r j = extNatW w r.val j := by
  unfold extW extNatW
  split_ifs <;> rfl

def coverRec (m : ℕ → ℕ) (p w : ℕ → ℕ → ℕ) (q : ℕ) : ℕ :=
  sumN (fun r => m r * sumN (fun i => p r i * extNatW w r (q + i)) 128) 8

def energyARec (m : ℕ → ℕ) (p : ℕ → ℕ → ℕ) : ℕ :=
  sumN (fun r => m r * sumN (fun i => (p r i)^2) 128) 8

def weightNormRec (m : ℕ → ℕ) (w : ℕ → ℕ → ℕ) : ℕ :=
  sumN (fun r => m r * sumN (fun j => (w r j)^2) 512) 8

def energyBRec (m : ℕ → ℕ) (w : ℕ → ℕ → ℕ) : ℤ :=
  2 * (weightNormRec m w : ℤ) - 7 * mixDen * weightDen^2 * 128

lemma coverN_eq_coverRec (m : ℕ → ℕ) (p w : ℕ → ℕ → ℕ) (q : ℕ) :
    coverN (fun r => m r.val) (fun r i => p r.val i.val)
      (fun r j => w r.val j.val) q = coverRec m p w q := by
  unfold coverN coverRec
  simp only [sumN_eq_sum_fin, extW_eq_extNatW]

lemma energyAN_eq_energyARec (m : ℕ → ℕ) (p : ℕ → ℕ → ℕ) :
    energyAN (fun r => m r.val) (fun r i => p r.val i.val) = energyARec m p := by
  unfold energyAN energyARec
  simp only [sumN_eq_sum_fin]

lemma weightNormN_eq_weightNormRec (m : ℕ → ℕ) (w : ℕ → ℕ → ℕ) :
    weightNormN (fun r => m r.val) (fun r j => w r.val j.val) =
      weightNormRec m w := by
  unfold weightNormN weightNormRec
  simp only [sumN_eq_sum_fin]

lemma energyBZ_eq_energyBRec (m : ℕ → ℕ) (w : ℕ → ℕ → ℕ) :
    energyBZ (fun r => m r.val) (fun r j => w r.val j.val) = energyBRec m w := by
  unfold energyBZ energyBRec
  rw [weightNormN_eq_weightNormRec]

/-- Assemble 32 independently checked blocks of 16 values and the final value.
The proof never evaluates `P`, so its cost is independent of the numerical check. -/
lemma forall_fin513_of_blocks (P : ℕ → Prop)
    (blocks : ∀ b : Fin 32, ∀ i : Fin 16, P (16 * b.val + i.val))
    (last : P 512) : ∀ q : Fin 513, P q.val := by
  intro q
  by_cases hq : q.val < 512
  · have hb : q.val / 16 < 32 := by omega
    have hi : q.val % 16 < 16 := Nat.mod_lt _ (by decide)
    have h := blocks ⟨q.val / 16, hb⟩ ⟨q.val % 16, hi⟩
    have heq : 16 * (q.val / 16) + q.val % 16 = q.val := by omega
    change P (16 * (q.val / 16) + q.val % 16) at h
    simpa only [heq] using h
  · have heq : q.val = 512 := by omega
    simpa only [heq] using last

#print axioms sumN_eq_sum_fin
#print axioms coverN_eq_coverRec
#print axioms energyAN_eq_energyARec
#print axioms weightNormN_eq_weightNormRec
#print axioms energyBZ_eq_energyBRec
#print axioms forall_fin513_of_blocks

theorem validCertificate_of_integer
    (m : Fin 8 → ℕ) (p : Fin 8 → Fin 128 → ℕ) (w : Fin 8 → Fin 512 → ℕ)
    (hm : (∑ r, m r) = mixDen)
    (hp : ∀ r, (∑ i, p r i) = kernelDen)
    (hsymm : ∀ r i, p r i = p r i.rev)
    (hcover : ∀ q : Fin 513, mixDen * kernelDen * weightDen ≤ coverN m p w q.val)
    (ha : 0 < energyAN m p)
    (hb : 0 < energyBZ m w)
    (hab : (energyAN m p : ℤ) * energyBZ m w * (1000000 : ℤ)^2 <
      (942838 : ℤ)^2 * mixDen^2 * kernelDen^2 * weightDen^2) :
    ValidCertificate (mixQ m) (kernelQ p) (weightQ w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    unfold mixQ
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hm' : (∑ r, (m r : ℚ)) = (mixDen : ℚ) := by exact_mod_cast hm
    simp only [mixQ, ← Finset.sum_div, hm']
    norm_num [mixDen]
  · intro r i
    unfold kernelQ
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro r
    have hp' : (∑ i, (p r i : ℚ)) = (kernelDen : ℚ) := by exact_mod_cast hp r
    simp only [kernelQ, ← Finset.sum_div, hp']
    norm_num [kernelDen]
  · intro r i
    unfold kernelQ
    rw [hsymm r i]
  · intro q
    change 1 ≤ ∑ r, mixQ m r * ∑ i, kernelQ p r i * extQ w r (q.val+i.val)
    rw [cover_eq]
    apply (le_div_iff₀ (by norm_num [mixDen, kernelDen, weightDen])).mpr
    simp only [one_mul]
    exact_mod_cast hcover q
  · unfold energyA
    rw [energyA_eq]
    have ha' : 0 < (energyAN m p : ℚ) := by exact_mod_cast ha
    exact div_pos (mul_pos (by norm_num) ha') (by norm_num [mixDen, kernelDen])
  · unfold energyB
    rw [energyB_eq]
    have hb' : 0 < (energyBZ m w : ℚ) := by exact_mod_cast hb
    exact div_pos hb' (by norm_num [mixDen, weightDen])
  · unfold energyA energyB
    rw [energyA_eq, energyB_eq]
    have hab' : (energyAN m p : ℚ) * (energyBZ m w : ℚ) * (1000000 : ℚ)^2 <
        (942838 : ℚ)^2 * (mixDen : ℚ)^2 * (kernelDen : ℚ)^2 * (weightDen : ℚ)^2 := by
      exact_mod_cast hab
    generalize hA : (energyAN m p : ℚ) = A at hab' ⊢
    generalize hB : (energyBZ m w : ℚ) = B at hab' ⊢
    norm_num [mixDen, kernelDen, weightDen] at hab' ⊢
    nlinarith only [hab']

#print axioms validCertificate_of_integer

lemma first_cover_recursive :
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat 0 := by
  decide +kernel

lemma cover_block_0 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 0 + i.val) := by
  decide +kernel

#print axioms cover_block_0

lemma cover_block_1 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 1 + i.val) := by
  decide +kernel

#print axioms cover_block_1

lemma cover_block_2 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 2 + i.val) := by
  decide +kernel

#print axioms cover_block_2

lemma cover_block_3 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 3 + i.val) := by
  decide +kernel

#print axioms cover_block_3

lemma cover_block_4 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 4 + i.val) := by
  decide +kernel

#print axioms cover_block_4

lemma cover_block_5 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 5 + i.val) := by
  decide +kernel

#print axioms cover_block_5

lemma cover_block_6 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 6 + i.val) := by
  decide +kernel

#print axioms cover_block_6

lemma cover_block_7 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 7 + i.val) := by
  decide +kernel

#print axioms cover_block_7

lemma cover_block_8 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 8 + i.val) := by
  decide +kernel

#print axioms cover_block_8

lemma cover_block_9 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 9 + i.val) := by
  decide +kernel

#print axioms cover_block_9

lemma cover_block_10 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 10 + i.val) := by
  decide +kernel

#print axioms cover_block_10

lemma cover_block_11 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 11 + i.val) := by
  decide +kernel

#print axioms cover_block_11

lemma cover_block_12 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 12 + i.val) := by
  decide +kernel

#print axioms cover_block_12

lemma cover_block_13 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 13 + i.val) := by
  decide +kernel

#print axioms cover_block_13

lemma cover_block_14 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 14 + i.val) := by
  decide +kernel

#print axioms cover_block_14

lemma cover_block_15 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 15 + i.val) := by
  decide +kernel

#print axioms cover_block_15

lemma cover_block_16 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 16 + i.val) := by
  decide +kernel

#print axioms cover_block_16

lemma cover_block_17 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 17 + i.val) := by
  decide +kernel

#print axioms cover_block_17

lemma cover_block_18 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 18 + i.val) := by
  decide +kernel

#print axioms cover_block_18

lemma cover_block_19 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 19 + i.val) := by
  decide +kernel

#print axioms cover_block_19

lemma cover_block_20 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 20 + i.val) := by
  decide +kernel

#print axioms cover_block_20

lemma cover_block_21 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 21 + i.val) := by
  decide +kernel

#print axioms cover_block_21

lemma cover_block_22 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 22 + i.val) := by
  decide +kernel

#print axioms cover_block_22

lemma cover_block_23 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 23 + i.val) := by
  decide +kernel

#print axioms cover_block_23

lemma cover_block_24 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 24 + i.val) := by
  decide +kernel

#print axioms cover_block_24

lemma cover_block_25 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 25 + i.val) := by
  decide +kernel

#print axioms cover_block_25

lemma cover_block_26 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 26 + i.val) := by
  decide +kernel

#print axioms cover_block_26

lemma cover_block_27 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 27 + i.val) := by
  decide +kernel

#print axioms cover_block_27

lemma cover_block_28 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 28 + i.val) := by
  decide +kernel

#print axioms cover_block_28

lemma cover_block_29 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 29 + i.val) := by
  decide +kernel

#print axioms cover_block_29

lemma cover_block_30 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 30 + i.val) := by
  decide +kernel

#print axioms cover_block_30

lemma cover_block_31 : ∀ i : Fin 16,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat (16 * 31 + i.val) := by
  decide +kernel

#print axioms cover_block_31

lemma last_cover_recursive :
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat 512 := by
  decide +kernel

lemma recursive_covers : ∀ q : Fin 513,
    mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat q.val := by
  apply forall_fin513_of_blocks
    (fun q => mixDen * kernelDen * weightDen ≤ coverRec mixRow kernelNat weightNat q)
  · intro b
    fin_cases b
    · exact cover_block_0
    · exact cover_block_1
    · exact cover_block_2
    · exact cover_block_3
    · exact cover_block_4
    · exact cover_block_5
    · exact cover_block_6
    · exact cover_block_7
    · exact cover_block_8
    · exact cover_block_9
    · exact cover_block_10
    · exact cover_block_11
    · exact cover_block_12
    · exact cover_block_13
    · exact cover_block_14
    · exact cover_block_15
    · exact cover_block_16
    · exact cover_block_17
    · exact cover_block_18
    · exact cover_block_19
    · exact cover_block_20
    · exact cover_block_21
    · exact cover_block_22
    · exact cover_block_23
    · exact cover_block_24
    · exact cover_block_25
    · exact cover_block_26
    · exact cover_block_27
    · exact cover_block_28
    · exact cover_block_29
    · exact cover_block_30
    · exact cover_block_31
  · exact last_cover_recursive

lemma integer_covers : ∀ q : Fin 513,
    mixDen * kernelDen * weightDen ≤ coverN mixN kernelN weightN q.val := by
  intro q
  unfold mixN kernelN weightN
  rw [coverN_eq_coverRec mixRow kernelNat weightNat q.val]
  exact recursive_covers q

#print axioms integer_covers

lemma integer_energyA_positive : 0 < energyAN mixN kernelN := by
  unfold mixN kernelN
  rw [energyAN_eq_energyARec]
  decide +kernel

lemma integer_energyB_positive : 0 < energyBZ mixN weightN := by
  unfold mixN weightN
  rw [energyBZ_eq_energyBRec]
  decide +kernel

lemma integer_coefficient_improved :
    (energyAN mixN kernelN : ℤ) * energyBZ mixN weightN * (1000000 : ℤ)^2 <
      (942838 : ℤ)^2 * mixDen^2 * kernelDen^2 * weightDen^2 := by
  unfold mixN kernelN weightN
  rw [energyAN_eq_energyARec, energyBZ_eq_energyBRec]
  decide +kernel

#print axioms integer_coefficient_improved

lemma integer_mix_normalized : (∑ r, mixN r) = mixDen := by
  have h : sumN mixRow 8 = mixDen := by decide +kernel
  simpa only [sumN_eq_sum_fin, mixN] using h

lemma integer_kernels_normalized : ∀ r, (∑ i, kernelN r i) = kernelDen := by
  have h : ∀ r : Fin 8, sumN (kernelNat r.val) 128 = kernelDen := by
    decide +kernel
  intro r
  simpa only [sumN_eq_sum_fin, kernelN] using h r

lemma integer_kernels_symmetric : ∀ r i, kernelN r i = kernelN r i.rev := by
  decide +kernel

def mix : Fin 8 → ℚ := mixQ mixN
def kernel : Fin 8 → Fin 128 → ℚ := kernelQ kernelN
def weight : Fin 8 → Fin 512 → ℚ := weightQ weightN

theorem certificate : ValidCertificate mix kernel weight :=
  validCertificate_of_integer mixN kernelN weightN
    integer_mix_normalized integer_kernels_normalized integer_kernels_symmetric
    integer_covers integer_energyA_positive integer_energyB_positive integer_coefficient_improved

theorem proof : statement := ⟨mix, kernel, weight, certificate⟩

#print axioms proof

end Submissions.Erdos30VectorSmoothingCertificate942838.Declan

namespace Submissions.Erdos30VectorSmoothingCertificate942838.Declan

noncomputable def realMix (mix : Fin 8 → ℚ) (r : Fin 8) : ℝ := mix r

noncomputable def realKernel (p : Fin 8 → Fin 128 → ℚ) (r : Fin 8) (i : ℕ) : ℝ :=
  if hi : i < 128 then (p r ⟨i, hi⟩ : ℝ) else 0

noncomputable def realWeight (w : Fin 8 → Fin 512 → ℚ) (r : Fin 8) (j : ℕ) : ℝ :=
  if hj : j < 512 then (w r ⟨j, hj⟩ : ℝ) else 1

noncomputable def realEnergyA (mix : Fin 8 → ℝ) (p : Fin 8 → ℕ → ℝ) : ℝ :=
  128 * ∑ r, mix r * ∑ i ∈ Finset.range 128, (p r i)^2

noncomputable def realEnergyB (mix : Fin 8 → ℝ) (w : Fin 8 → ℕ → ℝ) : ℝ :=
  1 + 2 * ((∑ r, mix r * ∑ j ∈ Finset.range 512, (w r j)^2) / 128 - 4)

lemma realWeight_eq_cast (w : Fin 8 → Fin 512 → ℚ) (r : Fin 8) (j : ℕ) :
    realWeight w r j = (extendedWeight w r j : ℝ) := by
  unfold realWeight extendedWeight
  split_ifs <;> simp

lemma real_energyA_eq (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) :
    realEnergyA (realMix mix) (realKernel p) = (energyA mix p : ℝ) := by
  unfold realEnergyA energyA
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simp [realMix, realKernel, Rat.cast_sum]

lemma real_energyB_eq (mix : Fin 8 → ℚ) (w : Fin 8 → Fin 512 → ℚ) :
    realEnergyB (realMix mix) (realWeight w) = (energyB mix w : ℝ) := by
  unfold realEnergyB energyB
  simp_rw [← Fin.sum_univ_eq_sum_range]
  simp [realMix, realWeight, Rat.cast_sum]

lemma real_cover_eq (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ)
    (w : Fin 8 → Fin 512 → ℚ) (q : ℕ) :
    (∑ r, realMix mix r * ∑ i ∈ Finset.range 128,
      realKernel p r i * realWeight w r (q + i)) =
    ((∑ r, mix r * ∑ i, p r i * extendedWeight w r (q + i.val)) : ℚ) := by
  simp_rw [← Fin.sum_univ_eq_sum_range, realWeight_eq_cast]
  simp [realMix, realKernel, Rat.cast_sum]

/-- All real hypotheses of the vector boundary lemma, lifted from the exact rational certificate.
The kernel is zero beyond bin 127 and the weight is one beyond bin 511 by definition. -/
theorem lift_valid_certificate
    (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) (w : Fin 8 → Fin 512 → ℚ)
    (h : ValidCertificate mix p w) :
    (∀ r, 0 ≤ realMix mix r) ∧ (∑ r, realMix mix r) = 1 ∧
    (∀ r i, 0 ≤ realKernel p r i) ∧
    (∀ r, (∑ i ∈ Finset.range 128, realKernel p r i) = 1) ∧
    (∀ r i, i < 128 → realKernel p r i = realKernel p r (127-i)) ∧
    (∀ q, q ≤ 512 → 1 ≤ ∑ r, realMix mix r * ∑ i ∈ Finset.range 128,
      realKernel p r i * realWeight w r (q+i)) ∧
    0 < realEnergyA (realMix mix) (realKernel p) ∧
    0 < realEnergyB (realMix mix) (realWeight w) ∧
    realEnergyA (realMix mix) (realKernel p) * realEnergyB (realMix mix) (realWeight w) <
      (942838 / 1000000 : ℝ)^2 := by
  rcases h with ⟨hm0, hm1, hp0, hp1, hsymm, hcover, ha, hb, hab⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    unfold realMix
    exact_mod_cast hm0 r
  · unfold realMix
    exact_mod_cast hm1
  · intro r i
    unfold realKernel
    split_ifs with hi
    · exact_mod_cast hp0 r ⟨i, hi⟩
    · exact le_rfl
  · intro r
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [realKernel, Fin.isLt, dite_true]
    exact_mod_cast hp1 r
  · intro r i hi
    have hrev : 127-i < 128 := by omega
    simp only [realKernel, hi, hrev, dite_true]
    have hfin : (⟨i, hi⟩ : Fin 128).rev = ⟨127-i, hrev⟩ := by
      apply Fin.ext
      change 128 - (i+1) = 127-i
      omega
    exact_mod_cast hfin ▸ hsymm r ⟨i, hi⟩
  · intro q hq
    rw [real_cover_eq]
    exact_mod_cast hcover ⟨q, by omega⟩
  · rw [real_energyA_eq]
    exact_mod_cast ha
  · rw [real_energyB_eq]
    exact_mod_cast hb
  · rw [real_energyA_eq, real_energyB_eq]
    have hh := (Rat.cast_lt (K := ℝ)).mpr hab
    push_cast at hh
    exact hh

#print axioms lift_valid_certificate

end Submissions.Erdos30VectorSmoothingCertificate942838.Declan


namespace Submissions.Erdos30VectorSmoothingCertificate942838.Declan

lemma realWeight_tail (w : Fin 8 → Fin 512 → ℚ) (r : Fin 8) (j : ℕ) (hj : 512 ≤ j) :
    realWeight w r j = 1 := by
  simp [realWeight, Nat.not_lt.mpr hj]

/-- All analytic kernel and boundary hypotheses have already been discharged.
The only input here is the exact finite rational certificate. -/
theorem rational_finite_bound
    (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) (w : Fin 8 → Fin 512 → ℚ)
    (hc : ValidCertificate mix p w) (N h : ℕ) (hh : 0 < h)
    (hN : 2*(4*128*h) ≤ N) (A : Finset ℤ) (hA : SidonConvolutionEnergy.IsSidon A)
    (hAN : A ⊆ Finset.Ico (0:ℤ) (N:ℤ)) :
    (A.card:ℝ)^2 ≤
      ((N:ℝ)+realEnergyB (realMix mix) (realWeight w)*((128:ℝ)*h)-1) *
      (1+realEnergyA (realMix mix) (realKernel p)*((A.card:ℝ)-1)/((128:ℝ)*h)) := by
  obtain ⟨hl0, hl1, hp0, hp1, hsym, hcover, _, _, _⟩ := lift_valid_certificate mix p w hc
  have he := SidonConcrete.finite_bound_from_certificate N 128 h 4 (by decide) hh hN
    (realMix mix) (realKernel p) (realWeight w) hl0 hl1 (fun r i _ => hp0 r i) hp1
    (fun r i hi => (hsym r i hi).symm) (fun r j hj => realWeight_tail w r j hj)
    hcover A hA hAN
  exact he

/-- A verified finite certificate yields the complete eventual Sidon upper bound,
with the advertised coefficient and an N-independent additive constant. -/
theorem upper_bound_of_rational_certificate
    (mix : Fin 8 → ℚ) (p : Fin 8 → Fin 128 → ℚ) (w : Fin 8 → Fin 512 → ℚ)
    (hc : ValidCertificate mix p w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ, A ⊆ Finset.Ico 0 (N:ℤ) →
        (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
          a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
      (A.card:ℝ) ≤ Real.sqrt N + (942838/1000000:ℝ)*Real.sqrt (Real.sqrt N)+C := by
  obtain ⟨_, _, _, _, _, _, ha, hb, hab⟩ := lift_valid_certificate mix p w hc
  let a := realEnergyA (realMix mix) (realKernel p)
  let b := realEnergyB (realMix mix) (realWeight w)
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  obtain ⟨N₀, hN₀⟩ := SidonAlgebraicTransfer.eventual_bound_of_coefficient 128 4
    (by decide) ha' hb' (by norm_num : (0:ℝ)<942838/1000000) hab
  refine ⟨a*b+b*128+1, by positivity, N₀, ?_⟩
  intro N hN A hAN hAS
  have hA : SidonConvolutionEnergy.IsSidon A :=
    (SidonConvolutionEnergy.isSidon_iff_unique_sums A).mpr hAS
  suffices hbound : (A.card:ℝ) ≤ Real.sqrt N + (942838/1000000:ℝ)*Real.sqrt (Real.sqrt N) +
      a*b+b*128+1 by simpa only [add_assoc] using hbound
  apply hN₀ N hN (A.card:ℝ) (by positivity)
  intro h hh hsep
  have hsepNat : 2*(4*128*h) ≤ N := by
    norm_num [← mul_assoc] at hsep ⊢
    exact_mod_cast hsep
  exact rational_finite_bound mix p w hc N h hh hsepNat A hA hAN

#print axioms upper_bound_of_rational_certificate

end Submissions.Erdos30VectorSmoothingCertificate942838.Declan



namespace Submissions.Erdos30SidonUpperBound942838.Declan

/-- Standard unordered-sum uniqueness, including repeated summands. -/
def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A one-sided eventual bound for all finite interval Sidon sets.
This is strictly weaker than the full subpower error asked in Erdős #30. -/
abbrev statement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℤ, A ⊆ Finset.Ico 0 (N : ℤ) → IsSidon A →
      (A.card : ℝ) ≤ Real.sqrt N +
        (942838 / 1000000 : ℝ) * Real.sqrt (Real.sqrt N) + C

theorem proof : statement := by
  obtain ⟨mix, p, w, h⟩ := Submissions.Erdos30VectorSmoothingCertificate942838.Declan.proof
  exact Submissions.Erdos30VectorSmoothingCertificate942838.Declan.upper_bound_of_rational_certificate mix p w h

#print axioms proof

end Submissions.Erdos30SidonUpperBound942838.Declan
