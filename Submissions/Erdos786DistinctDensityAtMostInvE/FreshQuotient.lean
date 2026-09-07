import Mathlib

/-! Explicit proof of the natural-density bound for distinct factors.
The constant is historically attributed to Ruzsa (Erdos, 1980 survey, p.114).
The compound-Poisson endgame follows the argument already in Jig 172 statement 6.
The proposed contribution is the fresh-balanced quotient structural reduction.
This source is generated from the reviewable local modules; no priority claim.
-/

section
/- Source module: SmoothRoughArithmetic.lean -/

/-! Canonical smooth/rough decomposition used in the concentration bridge. -/
namespace Erdos786Audit

def smoothPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∈ P)).prod

def roughPart (P : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p => p ∉ P)).prod

theorem smoothPart_factored (P : Finset ℕ) (n : ℕ) :
    smoothPart P n ∈ Nat.factoredNumbers P := Nat.prod_mem_factoredNumbers P n

theorem roughPart_ne_zero (P : Finset ℕ) (n : ℕ) : roughPart P n ≠ 0 := by
  apply List.prod_ne_zero
  intro h
  exact (Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)).false

theorem smoothPart_mul_roughPart (P : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    smoothPart P n * roughPart P n = n := by
  have hp := (List.filter_append_perm (fun p => p ∈ P) n.primeFactorsList).prod_eq
  simpa [smoothPart, roughPart, List.prod_append, Nat.prod_primeFactorsList hn] using hp

theorem prime_not_dvd_roughPart (P : Finset ℕ) (n p : ℕ)
    (hp : p.Prime) (hpP : p ∈ P) : ¬ p ∣ roughPart P n := by
  intro hdiv
  have hm := mem_list_primes_of_dvd_prod hp.prime
    (fun q hq => (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) hdiv
  have hnot : p ∉ P := by
    simpa only [decide_eq_true_eq] using List.of_mem_filter hm
  exact hnot hpP

theorem factored_coprime_rough {P : Finset ℕ} {s r : ℕ}
    (hs : s ∈ Nat.factoredNumbers P)
    (hr : ∀ p ∈ P, p.Prime → ¬ p ∣ r) : s.Coprime r := by
  apply Nat.coprime_of_dvd'
  intro p hp hps hpr
  exact False.elim (hr p ((Nat.mem_factoredNumbers'.mp hs) p hp hps) hp hpr)

theorem smooth_rough_unique {P : Finset ℕ} {s r t u : ℕ}
    (hs : s ∈ Nat.factoredNumbers P) (ht : t ∈ Nat.factoredNumbers P)
    (hr : ∀ p ∈ P, p.Prime → ¬ p ∣ r)
    (hu : ∀ p ∈ P, p.Prime → ¬ p ∣ u)
    (heq : s * r = t * u) : s = t ∧ r = u := by
  have hsu := factored_coprime_rough hs hu
  have htr := factored_coprime_rough ht hr
  have hst : s ∣ t := hsu.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right s r)
  have hts : t ∣ s := htr.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right t u)
  have hst_eq : s = t := Nat.dvd_antisymm hst hts
  refine ⟨hst_eq, ?_⟩
  rw [← hst_eq] at heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs.1) heq

theorem canonical_parts_of_smooth_mul_rough {P : Finset ℕ} {s r : ℕ}
    (hs : s ∈ Nat.factoredNumbers P) (hr0 : r ≠ 0)
    (hr : ∀ p ∈ P, p.Prime → ¬ p ∣ r) :
    smoothPart P (s * r) = s ∧ roughPart P (s * r) = r := by
  exact smooth_rough_unique (smoothPart_factored P (s * r)) hs
    (fun p hp hpprime => prime_not_dvd_roughPart P (s * r) p hpprime hp) hr
    (smoothPart_mul_roughPart P (s * r) (mul_ne_zero hs.1 hr0))

theorem canonical_pair_injective_on_positive (P : Finset ℕ) :
    Set.InjOn (fun n => (roughPart P n, smoothPart P n)) {n | n ≠ 0} := by
  intro n hn m hm heq
  have hr := congrArg Prod.fst heq
  have hs := congrArg Prod.snd heq
  dsimp only at hr hs
  calc
    n = smoothPart P n * roughPart P n := (smoothPart_mul_roughPart P n hn).symm
    _ = smoothPart P m * roughPart P m := by rw [hr, hs]
    _ = m := smoothPart_mul_roughPart P m hm

theorem reciprocal_canonical_parts (P : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ) / n = (1 / (roughPart P n : ℝ)) * (1 / (smoothPart P n : ℝ)) := by
  rw [one_div_mul_one_div, ← Nat.cast_mul, mul_comm (roughPart P n),
    smoothPart_mul_roughPart P n hn]

theorem harmonic_sum_eq_canonical_pair_sum (P F : Finset ℕ)
    (hF : ∀ n ∈ F, n ≠ 0) :
    (∑ n ∈ F, (1 : ℝ) / n) =
      ∑ x ∈ F.image (fun n => (roughPart P n, smoothPart P n)),
        (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    exact reciprocal_canonical_parts P n (hF n hn)
  · intro n hn m hm heq
    exact canonical_pair_injective_on_positive P (hF n hn) (hF m hm) heq

open Classical in
theorem harmonic_sum_le_selected_rows (P F R S : Finset ℕ) (A : Set ℕ)
    (hF : ∀ n ∈ F, n ≠ 0)
    (hA : ∀ n ∈ F, n ∈ A)
    (hR : ∀ n ∈ F, roughPart P n ∈ R)
    (hS : ∀ n ∈ F, smoothPart P n ∈ S) :
    (∑ n ∈ F, (1 : ℝ) / n) ≤
      ∑ r ∈ R, (1 / (r : ℝ)) *
        (∑ s ∈ S.filter (fun s => r * s ∈ A), (1 : ℝ) / s) := by
  rw [harmonic_sum_eq_canonical_pair_sum P F hF]
  have hsub : F.image (fun n => (roughPart P n, smoothPart P n)) ⊆
      (R ×ˢ S).filter (fun x => x.1 * x.2 ∈ A) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hR n hn, hS n hn⟩, ?_⟩
    simpa only [mul_comm (roughPart P n), smoothPart_mul_roughPart P n (hF n hn)]
      using hA n hn
  calc
    _ ≤ ∑ x ∈ (R ×ˢ S).filter (fun x => x.1 * x.2 ∈ A),
        (1 / (x.1 : ℝ)) * (1 / (x.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x _ _
      positivity
    _ = _ := by
      simp only [Finset.sum_filter, Finset.sum_product, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp

def roughCoresUpTo (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun r => ∀ p ∈ P, p.Prime → ¬ p ∣ r)

theorem roughPart_le (P : Finset ℕ) (n : ℕ) (hn : n ≠ 0) : roughPart P n ≤ n := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
  refine ⟨smoothPart P n, ?_⟩
  rw [mul_comm, smoothPart_mul_roughPart P n hn]

theorem roughPart_mem_cutoff (P : Finset ℕ) {n N : ℕ}
    (hn : n ≠ 0) (hN : n ≤ N) : roughPart P n ∈ roughCoresUpTo P N := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (roughPart_ne_zero P n),
    (roughPart_le P n hn).trans hN⟩, ?_⟩
  intro p hp hpprime
  exact prime_not_dvd_roughPart P n p hpprime hp

open Classical in
theorem harmonic_sum_le_cutoff_rows (P F S : Finset ℕ) (A : Set ℕ) (N : ℕ)
    (hF : ∀ n ∈ F, n ≠ 0) (hN : ∀ n ∈ F, n ≤ N)
    (hA : ∀ n ∈ F, n ∈ A) (hS : ∀ n ∈ F, smoothPart P n ∈ S) :
    (∑ n ∈ F, (1 : ℝ) / n) ≤
      ∑ r ∈ roughCoresUpTo P N, (1 / (r : ℝ)) *
        (∑ s ∈ S.filter (fun s => r * s ∈ A), (1 : ℝ) / s) := by
  exact harmonic_sum_le_selected_rows P F (roughCoresUpTo P N) S A hF hA
    (fun n hn => roughPart_mem_cutoff P (hF n hn) (hN n hn)) hS

open Classical in
theorem harmonic_sum_le_cutoff_rows_add_tail (P F S : Finset ℕ) (A : Set ℕ) (N : ℕ)
    (hF : ∀ n ∈ F, n ≠ 0) (hN : ∀ n ∈ F, n ≤ N)
    (hA : ∀ n ∈ F, n ∈ A) :
    (∑ n ∈ F, (1 : ℝ) / n) ≤
      (∑ r ∈ roughCoresUpTo P N, (1 / (r : ℝ)) *
        (∑ s ∈ S.filter (fun s => r * s ∈ A), (1 : ℝ) / s)) +
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S), (1 : ℝ) / n := by
  have hsplit : (∑ n ∈ F, (1 : ℝ) / n) =
      (∑ n ∈ F.filter (fun n => smoothPart P n ∈ S), (1 : ℝ) / n) +
      ∑ n ∈ F.filter (fun n => smoothPart P n ∉ S), (1 : ℝ) / n := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp_all
  rw [hsplit]
  apply add_le_add
  · apply harmonic_sum_le_cutoff_rows P _ S A N
    · intro n hn
      exact hF n (Finset.mem_filter.mp hn).1
    · intro n hn
      exact hN n (Finset.mem_filter.mp hn).1
    · intro n hn
      exact hA n (Finset.mem_filter.mp hn).1
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hnF, hnS⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.pos_of_ne_zero (hF n hnF), hN n hnF⟩, hnS⟩
    · intro n _ _
      positivity

theorem smoothPart_eq_iff_rough_multiple {P : Finset ℕ} {n s : ℕ}
    (hn : n ≠ 0) (hs : s ∈ Nat.factoredNumbers P) :
    smoothPart P n = s ↔ ∃ r : ℕ, r ≠ 0 ∧
      (∀ p ∈ P, p.Prime → ¬ p ∣ r) ∧ n = s * r := by
  constructor
  · intro heq
    refine ⟨roughPart P n, roughPart_ne_zero P n, ?_, ?_⟩
    · intro p hp hpprime
      exact prime_not_dvd_roughPart P n p hpprime hp
    · rw [← heq, smoothPart_mul_roughPart P n hn]
  · rintro ⟨r, hr0, hr, rfl⟩
    exact (canonical_parts_of_smooth_mul_rough hs hr0 hr).1

theorem prescribed_smooth_cutoff_eq_image (P : Finset ℕ) (s N : ℕ)
    (hs : s ∈ Nat.factoredNumbers P) :
    (Finset.Icc 1 N).filter (fun n => smoothPart P n = s) =
      (roughCoresUpTo P (N / s)).image (fun r => s * r) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hnS⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    obtain ⟨r, hr0, hr, heq⟩ :=
      (smoothPart_eq_iff_rough_multiple (by omega) hs).mp hnS
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hr0, ?_⟩, hr⟩,
      heq.symm⟩
    apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hs.1)).mpr
    simpa only [heq, Nat.mul_comm r s] using hnN
  · intro hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hrI, hrrough⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrpos, hrN⟩ := Finset.mem_Icc.mp hrI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      (canonical_parts_of_smooth_mul_rough hs (by omega) hrrough).1⟩
    · exact Nat.mul_pos (Nat.pos_of_ne_zero hs.1) hrpos
    · have hh := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hs.1)).mp hrN
      simpa only [Nat.mul_comm r s] using hh

theorem prescribed_smooth_cutoff_card (P : Finset ℕ) (s N : ℕ)
    (hs : s ∈ Nat.factoredNumbers P) :
    ((Finset.Icc 1 N).filter (fun n => smoothPart P n = s)).card =
      (roughCoresUpTo P (N / s)).card := by
  rw [prescribed_smooth_cutoff_eq_image P s N hs]
  apply Finset.card_image_iff.mpr
  intro r _ t _ heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs.1) heq


end Erdos786Audit

end

section
/- Source module: FreshRelations.lean -/

namespace Erdos786Audit

noncomputable section

/-- Balanced relations realizable outside every finite forbidden set. -/
def FreshBalanced {α G : Type*} [AddCommGroup G] (g : α → G) (h : G) : Prop :=
  ∀ T : Finset α, ∃ U V : Finset α,
    Disjoint U T ∧ Disjoint V T ∧ U.card = V.card ∧
      (∑ a ∈ U, g a) - (∑ a ∈ V, g a) = h

/-- These relations themselves form a subgroup; no choice of a presentation by
recurrent generators is needed. -/
def freshBalancedSubgroup {α G : Type*} [AddCommGroup G] (g : α → G) : AddSubgroup G where
  carrier := FreshBalanced g
  zero_mem' := by
    intro T
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp⟩
  neg_mem' := by
    intro h hh T
    obtain ⟨U, V, hUT, hVT, hcard, hsum⟩ := hh T
    exact ⟨V, U, hVT, hUT, hcard.symm, by rw [← hsum]; abel⟩
  add_mem' := by
    classical
    intro h k hh hk T
    obtain ⟨U, V, hUT, hVT, hcard, hsum⟩ := hh T
    obtain ⟨U', V', hU', hV', hcard', hsum'⟩ := hk (T ∪ (U ∪ V))
    simp only [Finset.disjoint_union_right] at hU' hV'
    refine ⟨U ∪ U', V ∪ V',
      Finset.disjoint_union_left.mpr ⟨hUT, hU'.1⟩,
      Finset.disjoint_union_left.mpr ⟨hVT, hV'.1⟩, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hU'.2.1.symm,
        Finset.card_union_of_disjoint hV'.2.2.symm, hcard, hcard']
    · rw [Finset.sum_union hU'.2.1.symm, Finset.sum_union hV'.2.2.symm,
        ← hsum, ← hsum']
      abel

/-- A quotient that kills only fresh balanced relations preserves the original
distinct-object equal-sum/equal-length law. -/
theorem length_law_descends_fresh_relations
    {α G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (g : α → G)
    (hlength : ∀ U V : Finset α,
      (∑ a ∈ U, g a) = (∑ a ∈ V, g a) → U.card = V.card)
    (q : G →+ Q) (hker : q.ker ≤ freshBalancedSubgroup g)
    (U V : Finset α)
    (heq : (∑ a ∈ U, q (g a)) = (∑ a ∈ V, q (g a))) :
    U.card = V.card := by
  classical
  have hm : (∑ a ∈ V, g a) - (∑ a ∈ U, g a) ∈ q.ker := by
    change q ((∑ a ∈ V, g a) - (∑ a ∈ U, g a)) = 0
    rw [map_sub, map_sum, map_sum, heq, sub_self]
  obtain ⟨U', V', hU', hV', hcard', hsum'⟩ := hker hm (U ∪ V)
  simp only [Finset.disjoint_union_right] at hU' hV'
  have hs : (∑ a ∈ U ∪ U', g a) = (∑ a ∈ V ∪ V', g a) := by
    rw [Finset.sum_union hU'.1.symm, Finset.sum_union hV'.2.symm]
    apply sub_eq_zero.mp
    calc
      _ = ((∑ a ∈ U, g a) - (∑ a ∈ V, g a)) +
          ((∑ a ∈ U', g a) - (∑ a ∈ V', g a)) := by abel
      _ = 0 := by rw [hsum']; abel
  have hc := hlength (U ∪ U') (V ∪ V') hs
  rw [Finset.card_union_of_disjoint hU'.1.symm,
    Finset.card_union_of_disjoint hV'.2.symm, hcard'] at hc
  exact Nat.add_right_cancel hc


/-- An infinitely recurrent difference is a fresh balanced relation. Injectivity
ensures that forbidding finitely many second entries excludes finitely many
first entries as well. -/
theorem recurrent_difference_is_fresh {α G : Type*} [AddCommGroup G]
    (g : α → G) (hg : Function.Injective g) (h : G)
    (hr : Set.Infinite {a | ∃ b, g a - g b = h}) : FreshBalanced g h := by
  classical
  intro T
  have hb : ∀ b : α, Set.Finite {a | g a - g b = h} := by
    intro b
    have he : {a | g a - g b = h} = g ⁻¹' {h + g b} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        sub_eq_iff_eq_add]
    rw [he]
    exact Set.Finite.preimage hg.injOn (Set.finite_singleton _)
  let bad : Set α := (T : Set α) ∪ ⋃ b ∈ (T : Set α), {a | g a - g b = h}
  have hbad : bad.Finite := T.finite_toSet.union
    (T.finite_toSet.biUnion (fun b _ => hb b))
  obtain ⟨a, ha, han⟩ := hr.exists_notMem_finite hbad
  obtain ⟨b, hab⟩ := ha
  have haT : a ∉ T := fun ha => han (Or.inl ha)
  have hbT : b ∉ T := by
    intro hb
    apply han
    exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hab⟩⟩)
  refine ⟨{a}, {b}, ?_, ?_, by simp, ?_⟩
  · simpa only [Finset.disjoint_singleton_left] using haT
  · simpa only [Finset.disjoint_singleton_left] using hbT
  · simpa only [Finset.sum_singleton] using hab

theorem finite_difference_fibre_outside_fresh_subgroup
    {α G : Type*} [AddCommGroup G]
    (g : α → G) (hg : Function.Injective g) (h : G)
    (hh : h ∉ freshBalancedSubgroup g) :
    Set.Finite {a | ∃ b, g a - g b = h} := by
  by_contra hn
  exact hh (recurrent_difference_is_fresh g hg h hn)


end
end Erdos786Audit

end

section
/- Source module: IntegerQuotient.lean -/

/-! Embedding the original positive-integer product law in the fresh-relation group. -/
namespace Erdos786Audit

noncomputable def integerLog (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (a : A) : Additive ℚˣ :=
  Additive.ofMul (Units.mk0 (a.val : ℚ) (by exact_mod_cast hA a.val a.property))

theorem integerLog_injective (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) :
    Function.Injective (integerLog A hA) := by
  intro a b hab
  have hh := congrArg (fun x : Additive ℚˣ => ((Additive.toMul x : ℚˣ) : ℚ)) hab
  simp only [integerLog, toMul_ofMul, Units.val_mk0] at hh
  apply Subtype.ext
  exact_mod_cast hh

theorem integerLog_sum_eq_implies_product_eq (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (U V : Finset A)
    (h : (∑ a ∈ U, integerLog A hA a) = ∑ a ∈ V, integerLog A hA a) :
    (∏ a ∈ U, (a : ℕ)) = ∏ a ∈ V, (a : ℕ) := by
  have hh := congrArg (fun x : Additive ℚˣ => ((Additive.toMul x : ℚˣ) : ℚ)) h
  simp only [toMul_sum, integerLog, toMul_ofMul, Units.coe_prod,
    Units.val_mk0] at hh
  exact_mod_cast hh

theorem integerLog_preserves_length_law (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (hlength : ∀ U V : Finset A,
      (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card) :
    ∀ U V : Finset A, (∑ a ∈ U, integerLog A hA a) =
      (∑ a ∈ V, integerLog A hA a) → U.card = V.card := by
  intro U V h
  exact hlength U V (integerLog_sum_eq_implies_product_eq A hA U V h)

abbrev FreshIntegerQuotient (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) :=
  Additive ℚˣ ⧸ freshBalancedSubgroup (integerLog A hA)

noncomputable def integerQuotientMap (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) :
    Additive ℚˣ →+ FreshIntegerQuotient A hA :=
  QuotientAddGroup.mk' (freshBalancedSubgroup (integerLog A hA))

theorem integer_quotient_length_law (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (hlength : ∀ U V : Finset A,
      (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card)
    (U V : Finset A)
    (h : (∑ a ∈ U, integerQuotientMap A hA (integerLog A hA a)) =
      ∑ a ∈ V, integerQuotientMap A hA (integerLog A hA a)) : U.card = V.card := by
  apply length_law_descends_fresh_relations (integerLog A hA)
    (integerLog_preserves_length_law A hA hlength) (integerQuotientMap A hA) _ U V h
  change (QuotientAddGroup.mk' (freshBalancedSubgroup (integerLog A hA))).ker ≤ _
  rw [QuotientAddGroup.ker_mk']

noncomputable def positiveIntegerLog (n : ℕ) (hn : n ≠ 0) : Additive ℚˣ :=
  Additive.ofMul (Units.mk0 (n : ℚ) (by exact_mod_cast hn))

theorem common_multiplier_log_difference (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (r s t : ℕ) (hs : s ≠ 0) (ht : t ≠ 0)
    (hrs : r * s ∈ A) (hrt : r * t ∈ A) :
    integerLog A hA ⟨r * s, hrs⟩ - integerLog A hA ⟨r * t, hrt⟩ =
      positiveIntegerLog s hs - positiveIntegerLog t ht := by
  apply Additive.ext
  apply Units.ext
  simp only [toMul_sub, integerLog, positiveIntegerLog, toMul_ofMul,
    Units.val_div_eq_div_val, Units.val_mk0, Nat.cast_mul]
  have hr : r ≠ 0 := (mul_ne_zero_iff.mp (hA (r * s) hrs)).1
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast hr
  field_simp

theorem finite_common_multipliers_of_distinct_quotient_classes
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) (s t : ℕ) (hs : s ≠ 0) (ht : t ≠ 0)
    (hne : integerQuotientMap A hA (positiveIntegerLog s hs) ≠
      integerQuotientMap A hA (positiveIntegerLog t ht)) :
    Set.Finite {r : ℕ | r * s ∈ A ∧ r * t ∈ A} := by
  classical
  let d := positiveIntegerLog s hs - positiveIntegerLog t ht
  have hd : d ∉ freshBalancedSubgroup (integerLog A hA) := by
    intro hd
    have hk : d ∈ (integerQuotientMap A hA).ker := by
      change d ∈ (QuotientAddGroup.mk' (freshBalancedSubgroup (integerLog A hA))).ker
      rwa [QuotientAddGroup.ker_mk']
    have hz : integerQuotientMap A hA d = 0 := hk
    apply hne
    exact sub_eq_zero.mp (by simpa only [d, map_sub] using hz)
  have hf := finite_difference_fibre_outside_fresh_subgroup (integerLog A hA)
    (integerLog_injective A hA) d hd
  let D := {r : ℕ | r * s ∈ A ∧ r * t ∈ A}
  let f : D → {a : A | ∃ b : A, integerLog A hA a - integerLog A hA b = d} :=
    fun r => ⟨⟨r.val * s, r.property.1⟩, ⟨⟨r.val * t, r.property.2⟩,
      common_multiplier_log_difference A hA r.val s t hs ht r.property.1 r.property.2⟩⟩
  have hinj : Function.Injective f := by
    intro r u heq
    have hv := congrArg Subtype.val (congrArg Subtype.val heq)
    change r.val * s = u.val * s at hv
    apply Subtype.ext
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs) hv
  let := hf.fintype
  have : Finite D := Finite.of_injective f hinj
  exact Set.toFinite D

noncomputable def integerClass (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (n : ℕ) : FreshIntegerQuotient A hA :=
  if hn : n ≠ 0 then integerQuotientMap A hA (positiveIntegerLog n hn) else 0

theorem finite_common_multipliers_of_distinct_integer_classes
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) (s t : ℕ) (hs : s ≠ 0) (ht : t ≠ 0)
    (hne : integerClass A hA s ≠ integerClass A hA t) :
    Set.Finite {r : ℕ | r * s ∈ A ∧ r * t ∈ A} := by
  apply finite_common_multipliers_of_distinct_quotient_classes A hA s t hs ht
  simpa only [integerClass, dif_pos hs, dif_pos ht] using hne

theorem positiveIntegerLog_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    positiveIntegerLog (m * n) (mul_ne_zero hm hn) =
      positiveIntegerLog m hm + positiveIntegerLog n hn := by
  apply Additive.ext
  apply Units.ext
  simp only [positiveIntegerLog, toMul_ofMul, toMul_add, Units.val_mul,
    Units.val_mk0, Nat.cast_mul]

theorem integerClass_mul_nonzero (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    integerClass A hA (m * n) = integerClass A hA m + integerClass A hA n := by
  simp only [integerClass, dif_pos hm, dif_pos hn, dif_pos (mul_ne_zero hm hn),
    positiveIntegerLog_mul m n hm hn, map_add]

theorem integerClass_one (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) : integerClass A hA 1 = 0 := by
  have hh := integerClass_mul_nonzero A hA 1 1 one_ne_zero one_ne_zero
  simp only [one_mul] at hh
  exact (add_eq_left.mp hh.symm)


end Erdos786Audit

end

section
/- Source module: SmoothClassReduction.lean -/

/-! A completely additive class map ignores the rough part when its prime classes vanish. -/
namespace Erdos786Audit

theorem additive_class_list_product
    {G : Type*} [AddCommMonoid G] (b : ℕ → G) (h1 : b 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → b (m * n) = b m + b n)
    (L : List ℕ) (hL : ∀ p ∈ L, p ≠ 0) :
    b L.prod = (L.map b).sum := by
  induction L with
  | nil => simpa using h1
  | cons p L ih =>
    have hp := hL p (by simp)
    have ht : ∀ q ∈ L, q ≠ 0 := fun q hq => hL q (by simp [hq])
    have hprod : L.prod ≠ 0 := List.prod_ne_zero (fun h => ht 0 h rfl)
    simpa only [List.prod_cons, List.map_cons, List.sum_cons] using
      (hmul p L.prod hp hprod).trans (congrArg (fun x => b p + x) (ih ht))

theorem additive_class_eq_smoothPart
    {G : Type*} [AddCommMonoid G] (b : ℕ → G) (h1 : b 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → b (m * n) = b m + b n)
    (P : Finset ℕ) (n : ℕ) (hn : n ≠ 0)
    (hrough : ∀ p, p.Prime → p ∣ n → p ∉ P → b p = 0) :
    b n = b (smoothPart P n) := by
  have hs : smoothPart P n ≠ 0 := by
    intro hz
    have he := smoothPart_mul_roughPart P n hn
    rw [hz, zero_mul] at he
    exact hn he.symm
  have hr : b (roughPart P n) = 0 := by
    unfold roughPart
    rw [additive_class_list_product b h1 hmul _ (fun p hp =>
      (Nat.pos_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).ne')]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hpn := List.mem_of_mem_filter hp
    exact hrough p (Nat.prime_of_mem_primeFactorsList hpn)
      (Nat.dvd_of_mem_primeFactorsList hpn)
      (by simpa only [decide_eq_true_eq] using List.of_mem_filter hp)
  calc
    b n = b (smoothPart P n * roughPart P n) :=
      congrArg b (smoothPart_mul_roughPart P n hn).symm
    _ = b (smoothPart P n) + b (roughPart P n) :=
      hmul _ _ hs (roughPart_ne_zero P n)
    _ = b (smoothPart P n) := by rw [hr, add_zero]


theorem quotient_integer_class_eq_smoothPart
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    {G : Type*} [AddCommGroup G] (q : FreshIntegerQuotient A hA →+ G)
    (P : Finset ℕ) (n : ℕ) (hn : n ≠ 0)
    (hrough : ∀ p, p.Prime → p ∣ n → p ∉ P → q (integerClass A hA p) = 0) :
    q (integerClass A hA n) = q (integerClass A hA (smoothPart P n)) := by
  apply additive_class_eq_smoothPart (fun n => q (integerClass A hA n))
    (by rw [integerClass_one, map_zero]) _ P n hn hrough
  intro m n hm hn
  rw [integerClass_mul_nonzero A hA m n hm hn, map_add]


open Classical in
theorem outside_smooth_classes_count_bound
    {G : Type*} [AddCommMonoid G] (b : ℕ → G) (h1 : b 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → b (m * n) = b m + b n)
    (P S : Finset ℕ) (D : Set ℕ)
    (hD : ∀ p, p.Prime → p ∉ P → b p ≠ 0 → p ∈ D) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => b n ∉ S.image b)).card ≤
      ((Finset.Icc 1 N).filter (fun n => ∃ p ∈ D, p ∣ n)).card +
      ((Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S)).card := by
  apply le_trans (Finset.card_le_card (show
    (Finset.Icc 1 N).filter (fun n => b n ∉ S.image b) ⊆
      (Finset.Icc 1 N).filter (fun n => ∃ p ∈ D, p ∣ n) ∪
      (Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S) from ?_))
    (Finset.card_union_le _ _)
  intro n hn
  obtain ⟨hnI, hnC⟩ := Finset.mem_filter.mp hn
  by_cases hd : ∃ p ∈ D, p ∣ n
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hd⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hnI, ?_⟩
    intro hs
    apply hnC
    have he := additive_class_eq_smoothPart b h1 hmul P n
      (by have := (Finset.mem_Icc.mp hnI).1; omega) (fun p hp hpn hpP => by
        by_contra hne
        exact hd ⟨p, hD p hp hpP hne, hpn⟩)
    exact Finset.mem_image.mpr ⟨smoothPart P n, hs, he.symm⟩


end Erdos786Audit

end

section
/- Source module: HarmonicConcentration.lean -/

/-! Weighted inequalities and density transfer for the smooth/rough concentration bridge.
The full arithmetic concentration theorem is not yet assembled. -/
namespace Erdos786Audit

open scoped BigOperators

theorem monochromatic_weight_le
    {S C : Type*} [DecidableEq S] [DecidableEq C]
    (s t : Finset S) (g : S → C) (w : S → ℝ) (b : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hb : 0 ≤ b) (ht : t ⊆ s)
    (hmono : ∀ x ∈ t, ∀ y ∈ t, g x = g y)
    (hclass : ∀ c, (∑ x ∈ s.filter (fun x => g x = c), w x) ≤ b) :
    (∑ x ∈ t, w x) ≤ b := by
  classical
  by_cases he : t.Nonempty
  · obtain ⟨a, ha⟩ := he
    apply le_trans _ (hclass (g a))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact Finset.mem_filter.mpr ⟨ht hx, hmono x hx a ha⟩
    · intro x _ _
      exact hw x
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty]
    exact hb

theorem weighted_exceptional_rows_bound
    {R : Type*} [DecidableEq R]
    (r t : Finset R) (u v : R → ℝ) (b total : ℝ)
    (hu : ∀ x, 0 ≤ u x) (hb : 0 ≤ b)
    (hv : ∀ x ∈ r, v x ≤ total)
    (hgood : ∀ x ∈ r, x ∉ t → v x ≤ b)
    (htotal : 0 ≤ total) :
    (∑ x ∈ r, u x * v x) ≤
      b * (∑ x ∈ r, u x) + total * (∑ x ∈ t, u x) := by
  classical
  have hpoint : ∀ x ∈ r, u x * v x ≤
      b * u x + if x ∈ t then total * u x else 0 := by
    intro x hx
    by_cases hxt : x ∈ t
    · simp only [hxt, if_true]
      calc
        u x * v x ≤ total * u x := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left (hv x hx) (hu x)
        _ ≤ b * u x + total * u x := le_add_of_nonneg_left (mul_nonneg hb (hu x))
    · simp only [hxt, if_false, add_zero]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hgood x hx hxt) (hu x)
  calc
    _ ≤ ∑ x ∈ r, (b * u x + if x ∈ t then total * u x else 0) :=
      Finset.sum_le_sum hpoint
    _ = b * (∑ x ∈ r, u x) + ∑ x ∈ r.filter (fun x => x ∈ t), total * u x := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter]
    _ ≤ b * (∑ x ∈ r, u x) + ∑ x ∈ t, total * u x := by
      apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x _ _
        exact mul_nonneg htotal (hu x)
    _ = _ := by simp only [Finset.mul_sum]

/-! Discrete partial summation, with indexing chosen to avoid division by zero. -/
theorem harmonic_partial_summation (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, a k / (k + 1)) =
      (∑ k ∈ Finset.range n, a k) / (n + 1) +
      ∑ k ∈ Finset.range n,
        (∑ j ∈ Finset.range (k + 1), a j) / ((k + 1) * (k + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have hn3 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem reciprocal_difference_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1) * (k + 2))) =
      1 - 1 / (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have hn3 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem harmonic_sum_mono_of_prefix_le (a b : ℕ → ℝ) (n : ℕ)
    (h : ∀ m ≤ n, (∑ k ∈ Finset.range m, a k) ≤ ∑ k ∈ Finset.range m, b k) :
    (∑ k ∈ Finset.range n, a k / (k + 1)) ≤
      ∑ k ∈ Finset.range n, b k / (k + 1) := by
  rw [harmonic_partial_summation, harmonic_partial_summation]
  apply add_le_add
  · exact div_le_div_of_nonneg_right (h n le_rfl) (by positivity)
  · apply Finset.sum_le_sum
    intro k hk
    exact div_le_div_of_nonneg_right
      (h (k + 1) (by have := Finset.mem_range.mp hk; omega)) (by positivity)

theorem harmonic_sum_le_of_prefix_bound (a : ℕ → ℝ) (n : ℕ) (C ε : ℝ)
    (hC : 0 ≤ C)
    (h : ∀ m ≤ n, (∑ k ∈ Finset.range m, a k) ≤ C + ε * m) :
    (∑ k ∈ Finset.range n, a k / (k + 1)) ≤
      C + ε * (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) := by
  classical
  by_cases hn : n = 0
  · simp [hn, hC]
  let b : ℕ → ℝ := fun k => ε + if k = 0 then C else 0
  have hprefix : ∀ m ≤ n,
      (∑ k ∈ Finset.range m, a k) ≤ ∑ k ∈ Finset.range m, b k := by
    intro m hm
    by_cases hm0 : m = 0
    · simp [hm0]
    · simpa [b, Finset.sum_add_distrib, Finset.sum_ite_eq', hm0,
        Nat.pos_of_ne_zero hm0, mul_comm, add_comm] using h m hm
  have hb : (∑ k ∈ Finset.range n, b k / (k + 1)) =
      C + ε * (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) := by
    simp [b, add_div, Finset.sum_add_distrib, ite_div, Finset.sum_ite_eq',
      Nat.pos_of_ne_zero hn, Finset.mul_sum, add_comm]
    simp only [div_eq_mul_inv]
  exact hb ▸ harmonic_sum_mono_of_prefix_le a b n hprefix

theorem abs_harmonic_sum_le_of_prefix_bound (a : ℕ → ℝ) (n : ℕ) (C ε : ℝ)
    (hC : 0 ≤ C)
    (h : ∀ m ≤ n, |∑ k ∈ Finset.range m, a k| ≤ C + ε * m) :
    |∑ k ∈ Finset.range n, a k / (k + 1)| ≤
      C + ε * (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) := by
  apply abs_le.mpr
  constructor
  · have hneg := harmonic_sum_le_of_prefix_bound (fun k => -a k) n C ε hC
      (fun m hm => by
        rw [Finset.sum_neg_distrib]
        have := (abs_le.mp (h m hm)).1
        linarith)
    simp only [neg_div, Finset.sum_neg_distrib] at hneg
    linarith
  · exact harmonic_sum_le_of_prefix_bound a n C ε hC
      (fun m hm => le_trans (le_abs_self _) (h m hm))

open Filter in
theorem tendsto_ratio_zero_of_epsilon_bound (f H : ℕ → ℝ)
    (hH : Tendsto H atTop atTop)
    (h : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |f n| ≤ C + ε * H n) :
    Tendsto (fun n => f n / H n) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h (ε / 2) (by positivity)
  filter_upwards [hH.eventually_gt_atTop (max 0 (2 * C / ε))] with n hn
  have hn0 : 0 < H n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnC : 2 * C / ε < H n := lt_of_le_of_lt (le_max_right _ _) hn
  have hc : C < (ε / 2) * H n := by
    have := (div_lt_iff₀ hε).mp hnC
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn0]
  apply (div_lt_iff₀ hn0).mpr
  have := hbound n
  nlinarith

open Filter in
theorem prefix_bound_of_average_tendsto_zero (a : ℕ → ℝ)
    (h : Tendsto (fun n => (∑ k ∈ Finset.range n, a k) / (n : ℝ))
      atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |∑ k ∈ Finset.range n, a k| ≤ C + ε * n := by
  have he := (Metric.tendsto_nhds.mp h) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let C : ℝ := ∑ m ∈ Finset.range N, |∑ k ∈ Finset.range m, a k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn0 : n = 0
  · simpa [hn0] using hC
  by_cases hn : n < N
  · have hsmall : |∑ k ∈ Finset.range n, a k| ≤ C := by
      exact Finset.single_le_sum
        (f := fun m => |∑ k ∈ Finset.range m, a k|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    have hterm : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg n)
    linarith
  · have hlarge := hN n (by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos] at hlarge
    have := (div_lt_iff₀ hnpos).mp hlarge
    linarith

open Filter in
theorem harmonic_average_zero_of_average_zero (a : ℕ → ℝ)
    (h : Tendsto (fun n => (∑ k ∈ Finset.range n, a k) / (n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n => (∑ k ∈ Finset.range n, a k / (k + 1)) /
      (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1))) atTop (nhds 0) := by
  apply tendsto_ratio_zero_of_epsilon_bound _ _
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := prefix_bound_of_average_tendsto_zero a h ε hε
  exact ⟨C, hC, fun n => abs_harmonic_sum_le_of_prefix_bound a n C ε hC
    (fun m _ => hbound m)⟩

open Filter in
theorem harmonic_average_of_average (a : ℕ → ℝ) (δ : ℝ)
    (h : Tendsto (fun n => (∑ k ∈ Finset.range n, a k) / (n : ℝ))
      atTop (nhds δ)) :
    Tendsto (fun n => (∑ k ∈ Finset.range n, a k / (k + 1)) /
      (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1))) atTop (nhds δ) := by
  have hcenter : Tendsto (fun n => (∑ k ∈ Finset.range n, (a k - δ)) / (n : ℝ))
      atTop (nhds 0) := by
    have hh := h.sub_const δ
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sub_div]
    field_simp
  have hc := harmonic_average_zero_of_average_zero (fun k => a k - δ) hcenter
  have hh := hc.add_const δ
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : 0 < ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
    apply Finset.sum_pos
    · intro k _
      positivity
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  simp only [sub_div, Finset.sum_sub_distrib]
  have hid : (∑ k ∈ Finset.range n, δ / (k + 1)) =
      δ * (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) := by
    rw [Finset.mul_sum]
    simp only [mul_one_div]
  rw [hid]
  field_simp
  ring

theorem finite_exceptional_rows_of_pairwise_finite
    {R S C : Type*} [DecidableEq R] [DecidableEq S]
    (s : Finset S) (g : S → C) (selected : R → S → Prop)
    (hfinite : ∀ x ∈ s, ∀ y ∈ s, g x ≠ g y →
      Set.Finite {r | selected r x ∧ selected r y}) :
    ∃ t : Finset R, ∀ r, r ∉ t → ∀ x ∈ s, ∀ y ∈ s,
      selected r x → selected r y → g x = g y := by
  classical
  let bad : S → S → Finset R := fun x y =>
    if h : x ∈ s ∧ y ∈ s ∧ g x ≠ g y then
      (hfinite x h.1 y h.2.1 h.2.2).toFinset else ∅
  refine ⟨s.biUnion (fun x => s.biUnion (bad x)), ?_⟩
  intro r hr x hx y hy hrx hry
  by_contra hne
  apply hr
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩⟩
  have hbad : x ∈ s ∧ y ∈ s ∧ g x ≠ g y := ⟨hx, hy, hne⟩
  simp only [bad, dif_pos hbad, Set.Finite.mem_toFinset]
  exact ⟨hrx, hry⟩

open Classical in
theorem weighted_selected_rows_bound
    {R S C : Type*} [DecidableEq R] [DecidableEq S] [DecidableEq C]
    (r t : Finset R) (s : Finset S) (g : S → C)
    (selected : R → S → Prop) (u : R → ℝ) (w : S → ℝ) (b : ℝ)
    (hu : ∀ x, 0 ≤ u x) (hw : ∀ x, 0 ≤ w x) (hb : 0 ≤ b)
    (hclass : ∀ c, (∑ x ∈ s.filter (fun x => g x = c), w x) ≤ b)
    (hmono : ∀ x ∈ r, x ∉ t → ∀ y ∈ s, ∀ z ∈ s,
      selected x y → selected x z → g y = g z) :
    (∑ x ∈ r, u x * (∑ y ∈ s.filter (selected x), w y)) ≤
      b * (∑ x ∈ r, u x) + (∑ y ∈ s, w y) * (∑ x ∈ t, u x) := by
  apply weighted_exceptional_rows_bound r t u _ b _ hu hb
  · intro x _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun y _ _ => hw y)
  · intro x hx hxt
    apply monochromatic_weight_le s (s.filter (selected x)) g w b hw hb
      (Finset.filter_subset _ _) _ hclass
    intro y hy z hz
    exact hmono x hx hxt y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1
      (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
  · exact Finset.sum_nonneg (fun y _ => hw y)

open Classical in
theorem exists_uniform_weighted_row_bound
    {R S C : Type*} [DecidableEq R] [DecidableEq S] [DecidableEq C]
    (s : Finset S) (g : S → C) (selected : R → S → Prop)
    (u : R → ℝ) (w : S → ℝ) (b : ℝ)
    (hu : ∀ x, 0 ≤ u x) (hw : ∀ x, 0 ≤ w x) (hb : 0 ≤ b)
    (hclass : ∀ c, (∑ x ∈ s.filter (fun x => g x = c), w x) ≤ b)
    (hfinite : ∀ x ∈ s, ∀ y ∈ s, g x ≠ g y →
      Set.Finite {r | selected r x ∧ selected r y}) :
    ∃ t : Finset R, ∀ r : Finset R,
      (∑ x ∈ r, u x * (∑ y ∈ s.filter (selected x), w y)) ≤
        b * (∑ x ∈ r, u x) + (∑ y ∈ s, w y) * (∑ x ∈ t, u x) := by
  obtain ⟨t, ht⟩ := finite_exceptional_rows_of_pairwise_finite s g selected hfinite
  refine ⟨t, fun r => ?_⟩
  exact weighted_selected_rows_bound r t s g selected u w b hu hw hb hclass
    (fun x _ hxt => ht x hxt)


open Filter Classical in
theorem harmonic_density_of_counting_density (D : Set ℕ) (δ : ℝ)
    (h : Tendsto (fun n =>
      ((Finset.range n).filter (fun k => k + 1 ∈ D)).card / (n : ℝ))
      atTop (nhds δ)) :
    Tendsto (fun n =>
      (∑ k ∈ (Finset.range n).filter (fun k => k + 1 ∈ D), (1 : ℝ) / (k + 1)) /
      (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1))) atTop (nhds δ) := by
  have hh := harmonic_average_of_average (fun k => if k + 1 ∈ D then (1 : ℝ) else 0) δ
  have hcount : ∀ n, (∑ k ∈ Finset.range n, if k + 1 ∈ D then (1 : ℝ) else 0) =
      ((Finset.range n).filter (fun k => k + 1 ∈ D)).card := by
    intro n
    simp
  have hmean : Tendsto (fun n =>
      (∑ k ∈ Finset.range n, if k + 1 ∈ D then (1 : ℝ) else 0) / (n : ℝ))
      atTop (nhds δ) := by
    simpa only [hcount] using h
  simpa only [ite_div, zero_div, ← Finset.sum_filter] using hh hmean


end Erdos786Audit

end

section
/- Source module: PeriodicDensity.lean -/

/-! Periodic counting sums for the arithmetic concentration argument. -/
namespace Erdos786Audit

theorem periodic_prefix_add (a : ℕ → ℝ) (m : ℕ)
    (hper : ∀ k, a (k + m) = a k) (n : ℕ) :
    (∑ k ∈ Finset.range (n + m), a k) =
      (∑ k ∈ Finset.range n, a k) + ∑ k ∈ Finset.range m, a k := by
  rw [Nat.add_comm n m, Finset.sum_range_add]
  have hs : (∑ k ∈ Finset.range n, a (m + k)) = ∑ k ∈ Finset.range n, a k := by
    apply Finset.sum_congr rfl
    intro k _
    simpa only [Nat.add_comm m k] using hper k
  rw [hs, add_comm]

theorem periodic_prefix_blocks (a : ℕ → ℝ) (m : ℕ)
    (hper : ∀ k, a (k + m) = a k) (q r : ℕ) :
    (∑ k ∈ Finset.range (q * m + r), a k) =
      (q : ℝ) * (∑ k ∈ Finset.range m, a k) + ∑ k ∈ Finset.range r, a k := by
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : (q + 1) * m + r = (q * m + r) + m := by ring
    rw [heq, periodic_prefix_add a m hper, ih]
    push_cast
    ring

theorem periodic_prefix_div_mod (a : ℕ → ℝ) (m : ℕ)
    (hper : ∀ k, a (k + m) = a k) (n : ℕ) :
    (∑ k ∈ Finset.range n, a k) =
      (n / m : ℕ) * (∑ k ∈ Finset.range m, a k) +
      ∑ k ∈ Finset.range (n % m), a k := by
  have hh := periodic_prefix_blocks a m hper (n / m) (n % m)
  simpa only [Nat.mul_comm (n / m) m, Nat.div_add_mod] using hh

theorem periodic_prefix_remainder_bound (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hper : ∀ k, a (k + m) = a k) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ k < m, |a k| ≤ M) (n : ℕ) :
    |(∑ k ∈ Finset.range n, a k) -
      (n / m : ℕ) * (∑ k ∈ Finset.range m, a k)| ≤ (m : ℝ) * M := by
  rw [periodic_prefix_div_mod a m hper n, add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ Finset.range (n % m), |a k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (n % m), M := by
      apply Finset.sum_le_sum
      intro k hk
      exact ha k ((Finset.mem_range.mp hk).trans (Nat.mod_lt n hm))
    _ = (n % m : ℕ) * M := by simp
    _ ≤ (m : ℝ) * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast (Nat.mod_lt n hm).le

open Filter in
theorem tendsto_nat_quotient_ratio (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n / m : ℕ) : ℝ) / n) atTop (nhds (1 / (m : ℝ))) := by
  have hmod := tendsto_mod_div_atTop_nhds_zero_nat hm
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := (hconst.sub hmod).div_const (m : ℝ)
  have hlim : Tendsto (fun n : ℕ => (1 - ((n % m : ℕ) : ℝ) / n) / m)
      atTop (nhds (1 / (m : ℝ))) := by simpa using hh
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hid : (m : ℝ) * (n / m : ℕ) + (n % m : ℕ) = n := by
    exact_mod_cast Nat.div_add_mod n m
  field_simp
  nlinarith

open Filter in
theorem periodic_average_tendsto (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hper : ∀ k, a (k + m) = a k) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ k < m, |a k| ≤ M) :
    Tendsto (fun n => (∑ k ∈ Finset.range n, a k) / (n : ℝ)) atTop
      (nhds ((∑ k ∈ Finset.range m, a k) / (m : ℝ))) := by
  let e : ℕ → ℝ := fun n => (∑ k ∈ Finset.range n, a k) -
    (n / m : ℕ) * (∑ k ∈ Finset.range m, a k)
  have he : ∀ n, |e n| ≤ (m : ℝ) * M :=
    periodic_prefix_remainder_bound a m hm hper M hM ha
  have he0 : Tendsto (fun n => e n / (n : ℝ)) atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (.of_forall (fun n => (abs_le.mp (he n)).1))
      (.of_forall (fun n => (abs_le.mp (he n)).2)) tendsto_natCast_atTop_atTop
  have hh := ((tendsto_nat_quotient_ratio m hm).mul_const
    (∑ k ∈ Finset.range m, a k)).add he0
  simp only [add_zero, one_div_mul_eq_div] at hh
  apply hh.congr
  intro n
  dsimp [e]
  ring

open Filter Classical in
theorem periodic_set_counting_density (D : Set ℕ) (m : ℕ) (hm : 0 < m)
    (hper : ∀ k, k + m ∈ D ↔ k ∈ D) :
    Tendsto (fun n => ((Finset.range n).filter (fun k => k + 1 ∈ D)).card / (n : ℝ))
      atTop (nhds (((Finset.range m).filter (fun k => k + 1 ∈ D)).card / (m : ℝ))) := by
  have hp : ∀ k, (if k + m + 1 ∈ D then (1 : ℝ) else 0) =
      (if k + 1 ∈ D then (1 : ℝ) else 0) := by
    intro k
    have he : k + m + 1 = (k + 1) + m := by omega
    simp only [he, hper]
  have hh := periodic_average_tendsto (fun k => if k + 1 ∈ D then (1 : ℝ) else 0)
    m hm hp 1 (by norm_num) (fun k _ => by split_ifs <;> norm_num)
  simpa using hh

theorem rough_iff_coprime_prime_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∀ p ∈ P, ¬ p ∣ n) ↔ (∏ p ∈ P, p).Coprime n := by
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    exact (hP p hp).coprime_iff_not_dvd.mpr (h p hp)
  · intro h p hp
    exact (hP p hp).coprime_iff_not_dvd.mp (h p hp)

theorem rough_membership_periodic (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∀ p ∈ P, ¬ p ∣ n + ∏ q ∈ P, q) ↔ (∀ p ∈ P, ¬ p ∣ n) := by
  rw [rough_iff_coprime_prime_product P hP, rough_iff_coprime_prime_product P hP]
  exact (Nat.periodic_coprime (∏ p ∈ P, p) n).to_iff

open Filter Classical in
theorem rough_counting_density_residue_form (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun n => ((Finset.range n).filter
      (fun k => ∀ p ∈ P, ¬ p ∣ k + 1)).card / (n : ℝ)) atTop
      (nhds (((Finset.range (∏ p ∈ P, p)).filter
        (fun k => ∀ p ∈ P, ¬ p ∣ k + 1)).card / ((∏ p ∈ P, p : ℕ) : ℝ))) := by
  simpa only [Set.mem_ofPred_eq] using
    periodic_set_counting_density {n | ∀ p ∈ P, ¬ p ∣ n} (∏ p ∈ P, p)
      (Finset.prod_pos (fun p hp => (hP p hp).pos)) (rough_membership_periodic P hP)

theorem shifted_coprime_residue_count (m : ℕ) :
    ((Finset.range m).filter (fun k => m.Coprime (k + 1))).card = m.totient := by
  have hh := Nat.filter_coprime_Ico_eq_totient m 1
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_Ico_eq_sum_range] at hh
  simpa [Nat.add_comm] using hh

theorem rough_residue_count_totient (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ((Finset.range (∏ p ∈ P, p)).filter
      (fun k => ∀ p ∈ P, ¬ p ∣ k + 1)).card = (∏ p ∈ P, p).totient := by
  simp_rw [rough_iff_coprime_prime_product P hP]
  exact shifted_coprime_residue_count _

open Filter Classical in
theorem rough_counting_density_totient (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun n => ((Finset.range n).filter
      (fun k => ∀ p ∈ P, ¬ p ∣ k + 1)).card / (n : ℝ)) atTop
      (nhds (((∏ p ∈ P, p).totient : ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ))) := by
  simpa only [rough_residue_count_totient P hP] using rough_counting_density_residue_form P hP

theorem totient_finite_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p).totient = ∏ p ∈ P, (p - 1) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hprime : p.Prime := hP p (Finset.mem_insert_self _ _)
    have hrest : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hprime (hrest q hq)).mpr
      intro heq
      exact hp (heq.symm ▸ hq)
    rw [Finset.prod_insert hp, Nat.totient_mul hcop, Nat.totient_prime hprime,
      ih hrest, Finset.prod_insert hp]

theorem rough_totient_ratio_euler_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((∏ p ∈ P, p).totient : ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ) =
      ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  rw [totient_finite_prime_product P hP]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (hP p hp).one_lt.le, Nat.cast_one]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp

open Filter Classical in
theorem rough_counting_density_euler_product (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun n => ((Finset.range n).filter
      (fun k => ∀ p ∈ P, ¬ p ∣ k + 1)).card / (n : ℝ)) atTop
      (nhds (∏ p ∈ P, (1 - (1 : ℝ) / p))) := by
  simpa only [rough_totient_ratio_euler_product P hP] using rough_counting_density_totient P hP

theorem rough_euler_product_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)

open Filter in
theorem counting_density_under_dilation (f : ℕ → ℝ) (a : ℝ) (s : ℕ) (hs : 0 < s)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (nhds a)) :
    Tendsto (fun n => f (n / s) / (n : ℝ)) atTop (nhds (a / (s : ℝ))) := by
  have hdiv : Tendsto (fun n : ℕ => n / s) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b * s)] with n hn
    exact (Nat.le_div_iff_mul_le hs).mpr hn
  have hh := (hf.comp hdiv).mul (tendsto_nat_quotient_ratio s hs)
  simp only [mul_one_div] at hh
  apply hh.congr'
  filter_upwards [hdiv.eventually_ge_atTop 1] with n hn
  have hq : ((n / s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n / s ≠ 0 by omega)
  dsimp only [Function.comp_def]
  field_simp


end Erdos786Audit

end

section
/- Source module: SmoothMass.lean -/

/-! Reciprocal mass of integers supported on a fixed finite prime set. -/
namespace Erdos786Audit

noncomputable def reciprocalNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_comm]

theorem reciprocal_prime_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖reciprocalNatHom p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_of_nonneg (by positivity)]
  exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

theorem smooth_reciprocal_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun s : Nat.factoredNumbers P => (1 : ℝ) / (s : ℕ))
      (∏ p ∈ P, (1 - (1 : ℝ) / p))⁻¹ := by
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalNatHom) (fun hp => reciprocal_prime_norm_lt_one hp) P).2
  simpa [reciprocalNatHom, Finset.filter_eq_self.mpr hP, one_div,
    Finset.prod_inv_distrib] using hh

theorem exists_finite_smooth_reciprocal_approximation (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ s ∈ S, s ∈ Nat.factoredNumbers P) ∧
      |(∑ s ∈ S, (1 : ℝ) / s) - (∏ p ∈ P, (1 - (1 : ℝ) / p))⁻¹| < ε := by
  classical
  have hh := smooth_reciprocal_hasSum P hP
  obtain ⟨T, hT⟩ := ((Metric.tendsto_nhds.mp hh) ε hε).exists
  refine ⟨T.image (fun s : Nat.factoredNumbers P => (s : ℕ)), ?_, ?_⟩
  · intro s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    exact t.property
  · rw [Finset.sum_image]
    · simpa only [Real.dist_eq] using hT
    · intro s _ t _ heq
      exact Subtype.val_injective heq

theorem exists_finite_smooth_tail_small (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ s ∈ S, s ∈ Nat.factoredNumbers P) ∧
      1 - (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ S, (1 : ℝ) / s) < ε := by
  let a : ℝ := ∏ p ∈ P, (1 - (1 : ℝ) / p)
  have ha : 0 < a := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)
  obtain ⟨S, hS, happrox⟩ := exists_finite_smooth_reciprocal_approximation P hP
    (ε / a) (div_pos hε ha)
  refine ⟨S, hS, ?_⟩
  change |(∑ s ∈ S, (1 : ℝ) / s) - a⁻¹| < ε / a at happrox
  have hlo := mul_lt_mul_of_pos_left (abs_lt.mp happrox).1 ha
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hdiv : a * (ε / a) = ε := by field_simp
  change 1 - a * (∑ s ∈ S, (1 : ℝ) / s) < ε
  nlinarith

theorem normalized_smooth_mass_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun s : Nat.factoredNumbers P =>
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ)) 1 := by
  let a : ℝ := ∏ p ∈ P, (1 - (1 : ℝ) / p)
  have ha : 0 < a := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1)
  have hh := (smooth_reciprocal_hasSum P hP).mul_left a
  change HasSum (fun s : Nat.factoredNumbers P => a * (1 / (s : ℝ))) (a * a⁻¹) at hh
  simpa only [mul_one_div, mul_inv_cancel₀ ha.ne'] using hh


end Erdos786Audit

end

section
/- Source module: ArithmeticAssembly.lean -/

/-! Finite arithmetic concentration and individual smooth-part densities.
The original quotient hypothesis, finite tails, and geometric law remain to be connected. -/
namespace Erdos786Audit

open Classical in
theorem exists_uniform_arithmetic_error
    {G : Type*} [DecidableEq G]
    (P S : Finset ℕ) (A : Set ℕ) (g : ℕ → G) (b : ℝ)
    (hb : 0 ≤ b)
    (hclass : ∀ c, (∑ s ∈ S.filter (fun s => g s = c), (1 : ℝ) / s) ≤ b)
    (hfinite : ∀ s ∈ S, ∀ t ∈ S, g s ≠ g t →
      Set.Finite {r : ℕ | r * s ∈ A ∧ r * t ∈ A}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (F : Finset ℕ),
      (∀ n ∈ F, n ≠ 0) → (∀ n ∈ F, n ≤ N) → (∀ n ∈ F, n ∈ A) →
      (∑ n ∈ F, (1 : ℝ) / n) ≤
        b * (∑ r ∈ roughCoresUpTo P N, (1 : ℝ) / r) + C +
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S), (1 : ℝ) / n := by
  obtain ⟨T, hT⟩ := exists_uniform_weighted_row_bound S g
    (fun r s => r * s ∈ A) (fun r => (1 : ℝ) / r) (fun s => (1 : ℝ) / s) b
    (fun _ => by positivity) (fun _ => by positivity) hb hclass hfinite
  refine ⟨(∑ s ∈ S, (1 : ℝ) / s) * (∑ r ∈ T, (1 : ℝ) / r), ?_, ?_⟩
  · positivity
  · intro N F hF hN hA
    exact (harmonic_sum_le_cutoff_rows_add_tail P F S A N hF hN hA).trans
      (add_le_add_left (hT (roughCoresUpTo P N)) _)

open Filter in
theorem density_bound_of_uniform_harmonic_error
    (f r t H : ℕ → ℝ) (δ a τ b C : ℝ)
    (hH : Tendsto H atTop atTop)
    (hf : Tendsto (fun n => f n / H n) atTop (nhds δ))
    (hr : Tendsto (fun n => r n / H n) atTop (nhds a))
    (ht : Tendsto (fun n => t n / H n) atTop (nhds τ))
    (hbound : ∀ n, f n ≤ b * r n + C + t n) : δ ≤ b * a + τ := by
  have hlim := ((hr.const_mul b).add (hH.const_div_atTop C)).add ht
  simp only [add_zero] at hlim
  apply le_of_tendsto_of_tendsto hf hlim
  filter_upwards [hH.eventually_gt_atTop 0] with n hn
  have hh := div_le_div_of_nonneg_right (hbound n) hn.le
  simpa only [add_div, mul_div_assoc] using hh

open Classical in
theorem positive_cutoff_card_eq_shift (D : Set ℕ) (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => n ∈ D)).card =
      ((Finset.range N).filter (fun k => k + 1 ∈ D)).card := by
  symm
  apply Finset.card_bij (fun k _ => k + 1)
  · intro k hk
    obtain ⟨hkN, hkD⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by omega, by have := Finset.mem_range.mp hkN; omega⟩, hkD⟩
  · intro k _ l _ heq
    omega
  · intro n hn
    obtain ⟨hnI, hnD⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    refine ⟨n - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa only [Nat.sub_add_cancel hnpos] using hnD

open Filter Classical in
theorem rough_cutoff_density (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun N => ((roughCoresUpTo P N).card : ℝ) / N) atTop
      (nhds (∏ p ∈ P, (1 - (1 : ℝ) / p))) := by
  have hcount : ∀ N, (roughCoresUpTo P N).card =
      ((Finset.range N).filter (fun k => ∀ p ∈ P, ¬ p ∣ k + 1)).card := by
    intro N
    have hh := positive_cutoff_card_eq_shift {n | ∀ p ∈ P, p.Prime → ¬ p ∣ n} N
    have hpred : ∀ n, (∀ p ∈ P, p.Prime → ¬ p ∣ n) ↔ (∀ p ∈ P, ¬ p ∣ n) := by
      intro n
      exact ⟨fun h p hp => h p hp (hP p hp), fun h p hp _ => h p hp⟩
    simpa only [roughCoresUpTo, Set.mem_ofPred_eq, hpred] using hh
  simpa only [hcount] using rough_counting_density_euler_product P hP

open Filter Classical in
theorem prescribed_smooth_part_density (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : ℕ) (hs : s ∈ Nat.factoredNumbers P) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n = s)).card : ℝ) / N)
      atTop (nhds ((∏ p ∈ P, (1 - (1 : ℝ) / p)) / s)) := by
  have hh := counting_density_under_dilation (fun N => ((roughCoresUpTo P N).card : ℝ))
    (∏ p ∈ P, (1 - (1 : ℝ) / p)) s (Nat.pos_of_ne_zero hs.1) (rough_cutoff_density P hP)
  simpa only [prescribed_smooth_cutoff_card P s _ hs] using hh

open Filter Classical in
theorem finite_smooth_parts_density (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ s ∈ S, s ∈ Nat.factoredNumbers P) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∈ S)).card : ℝ) / N)
      atTop (nhds ((∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ S, (1 : ℝ) / s))) := by
  have hh := tendsto_finsetSum S (fun s hs => prescribed_smooth_part_density P hP s (hS s hs))
  have hc : ∀ N, (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∈ S)).card : ℝ) =
      ∑ s ∈ S, (((Finset.Icc 1 N).filter (fun n => smoothPart P n = s)).card : ℝ) := by
    intro N
    exact_mod_cast (Finset.sum_card_fiberwise_eq_card_filter (Finset.Icc 1 N) S
      (smoothPart P)).symm
  simpa only [hc, Finset.sum_div, Finset.mul_sum, mul_one_div] using hh

open Filter Classical in
theorem finite_smooth_tail_density (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ s ∈ S, s ∈ Nat.factoredNumbers P) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S)).card : ℝ) / N)
      atTop (nhds (1 - (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ S, (1 : ℝ) / s))) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := hconst.sub (finite_smooth_parts_density P S hP hS)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc : (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∈ S)).card : ℝ) +
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S)).card : ℝ) = N := by
    exact_mod_cast (show ((Finset.Icc 1 N).filter (fun n => smoothPart P n ∈ S)).card +
      ((Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S)).card = N by
        simpa using Finset.card_filter_add_card_filter_not
          (s := Finset.Icc 1 N) (fun n => smoothPart P n ∈ S))
  field_simp
  linarith

open Classical in
theorem positive_cutoff_sum_eq_shift (D : Set ℕ) (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∈ D), w n) =
      ∑ k ∈ (Finset.range N).filter (fun k => k + 1 ∈ D), w (k + 1) := by
  symm
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    obtain ⟨hkN, hkD⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by omega, by have := Finset.mem_range.mp hkN; omega⟩, hkD⟩
  · intro k _ l _ heq
    omega
  · intro n hn
    obtain ⟨hnI, hnD⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    refine ⟨n - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa only [Nat.sub_add_cancel hnpos] using hnD
  · intro k _
    rfl

open Filter Classical in
theorem harmonic_cutoff_density (D : Set ℕ) (δ : ℝ)
    (h : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ D)).card : ℝ) / N)
      atTop (nhds δ)) :
    Tendsto (fun N => (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∈ D), (1 : ℝ) / n) /
      (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1))) atTop (nhds δ) := by
  have hindex : Tendsto (fun N =>
      (((Finset.range N).filter (fun k => k + 1 ∈ D)).card : ℝ) / N) atTop (nhds δ) := by
    simpa only [positive_cutoff_card_eq_shift D] using h
  have hh := harmonic_density_of_counting_density D δ hindex
  simpa only [positive_cutoff_sum_eq_shift D (fun n => (1 : ℝ) / n), Nat.cast_add,
    Nat.cast_one] using hh

open Filter Classical in
theorem density_le_class_weight_add_smooth_tail
    {G : Type*} [DecidableEq G] (P S : Finset ℕ) (A : Set ℕ) (g : ℕ → G)
    (δ b : ℝ) (hP : ∀ p ∈ P, p.Prime) (hS : ∀ s ∈ S, s ∈ Nat.factoredNumbers P)
    (hA : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
      atTop (nhds δ)) (hb : 0 ≤ b)
    (hclass : ∀ c, (∑ s ∈ S.filter (fun s => g s = c), (1 : ℝ) / s) ≤ b)
    (hfinite : ∀ s ∈ S, ∀ t ∈ S, g s ≠ g t →
      Set.Finite {r : ℕ | r * s ∈ A ∧ r * t ∈ A}) :
    δ ≤ b * (∏ p ∈ P, (1 - (1 : ℝ) / p)) +
      (1 - (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ S, (1 : ℝ) / s)) := by
  obtain ⟨C, _, hC⟩ := exists_uniform_arithmetic_error P S A g b hb hclass hfinite
  have hr := harmonic_cutoff_density {n | ∀ p ∈ P, p.Prime → ¬ p ∣ n}
    (∏ p ∈ P, (1 - (1 : ℝ) / p)) (by
      simpa only [Set.mem_ofPred_eq, roughCoresUpTo] using rough_cutoff_density P hP)
  have ht := harmonic_cutoff_density {n | smoothPart P n ∉ S}
    (1 - (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ S, (1 : ℝ) / s)) (by
      simpa only [Set.mem_ofPred_eq] using finite_smooth_tail_density P S hP hS)
  apply density_bound_of_uniform_harmonic_error _ _ _ _ δ _ _ b C
    Real.tendsto_sum_range_one_div_nat_succ_atTop (harmonic_cutoff_density A δ hA) hr ht
  intro N
  have hh := hC N ((Finset.Icc 1 N).filter (fun n => n ∈ A))
    (fun n hn => by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1; omega)
    (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  simpa only [Set.mem_ofPred_eq, roughCoresUpTo] using hh

open Filter Classical in
theorem density_le_uniform_smooth_class_mass
    {G : Type*} [DecidableEq G] (P : Finset ℕ) (A : Set ℕ) (g : ℕ → G)
    (δ B : ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hA : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
      atTop (nhds δ)) (hB : 0 ≤ B)
    (hclass : ∀ S : Finset ℕ, (∀ s ∈ S, s ∈ Nat.factoredNumbers P) → ∀ c,
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) *
        (∑ s ∈ S.filter (fun s => g s = c), (1 : ℝ) / s) ≤ B)
    (hfinite : ∀ s ∈ Nat.factoredNumbers P, ∀ t ∈ Nat.factoredNumbers P, g s ≠ g t →
      Set.Finite {r : ℕ | r * s ∈ A ∧ r * t ∈ A}) : δ ≤ B := by
  let a : ℝ := ∏ p ∈ P, (1 - (1 : ℝ) / p)
  have ha : 0 < a := rough_euler_product_pos P hP
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S, hS, htail⟩ := exists_finite_smooth_tail_small P hP ε hε
  have hc : ∀ c, (∑ s ∈ S.filter (fun s => g s = c), (1 : ℝ) / s) ≤ B / a := by
    intro c
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using hclass S hS c
  have hd := density_le_class_weight_add_smooth_tail P S A g δ (B / a) hP hS hA
    (div_nonneg hB ha.le) hc (fun s hs t ht => hfinite s (hS s hs) t (hS t ht))
  change δ ≤ B / a * a + (1 - a * (∑ s ∈ S, (1 : ℝ) / s)) at hd
  rw [div_mul_cancel₀ _ ha.ne'] at hd
  linarith

open Filter Classical in
theorem exists_approximate_smooth_class_mass
    {G : Type*} [DecidableEq G] [Nonempty G]
    (P : Finset ℕ) (A : Set ℕ) (g : ℕ → G) (δ : ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hA : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
      atTop (nhds δ))
    (hfinite : ∀ s ∈ Nat.factoredNumbers P, ∀ t ∈ Nat.factoredNumbers P, g s ≠ g t →
      Set.Finite {r : ℕ | r * s ∈ A ∧ r * t ∈ A}) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ s ∈ S, s ∈ Nat.factoredNumbers P) ∧ ∃ c : G,
      δ - ε ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p)) *
        (∑ s ∈ S.filter (fun s => g s = c), (1 : ℝ) / s) := by
  by_contra hnot
  push Not at hnot
  have hzero : 0 < δ - ε := by
    simpa using hnot ∅ (by simp) (Classical.choice (inferInstance : Nonempty G))
  have hd := density_le_uniform_smooth_class_mass P A g δ (δ - ε) hP hA hzero.le
    (fun S hS c => (hnot S hS c).le) hfinite
  linarith

open Filter Classical in
theorem actual_integer_quotient_concentration
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ)
    (hA : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
      atTop (nhds δ)) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ s ∈ S, s ∈ Nat.factoredNumbers P) ∧
      ∃ c : FreshIntegerQuotient A hpositive,
        δ - ε ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p)) *
          (∑ s ∈ S.filter (fun s => integerClass A hpositive s = c), (1 : ℝ) / s) := by
  apply exists_approximate_smooth_class_mass P A (integerClass A hpositive) δ hP hA
    _ ε hε
  intro s hs t ht hne
  exact finite_common_multipliers_of_distinct_integer_classes A hpositive s t hs.1 ht.1 hne


end Erdos786Audit

end

section
/- Source module: DivisorTail.lean -/

/-! Uniform counting bounds for unions of divisibility events. -/
namespace Erdos786Audit

theorem multiples_cutoff_card (p N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => p ∣ n)).card = N / p := by
  classical
  have h := positive_cutoff_card_eq_shift {n | p ∣ n} N
  simp only [Set.mem_ofPred_eq] at h
  exact h.trans (Nat.card_multiples N p)

theorem finite_divisor_union_bound (P : Finset ℕ) (N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ∣ n)).card : ℝ) ≤
      N * ∑ p ∈ P, (1 : ℝ) / p := by
  classical
  have heq : (Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ∣ n) =
      P.biUnion (fun p => (Finset.Icc 1 N).filter (fun n => p ∣ n)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ p ∈ P, (((Finset.Icc 1 N).filter (fun n => p ∣ n)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := P)
        (t := fun p => (Finset.Icc 1 N).filter (fun n => p ∣ n)))
    _ ≤ ∑ p ∈ P, (N : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p _
      rw [multiples_cutoff_card]
      exact Nat.cast_div_le
    _ = _ := by rw [Finset.mul_sum]; simp only [mul_one_div]


open Classical in
theorem summable_divisor_union_bound (D : Set ℕ) (hD : ∀ p ∈ D, 0 < p)
    (hs : Summable (fun p : D => (1 : ℝ) / (p : ℕ))) (N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => ∃ p ∈ D, p ∣ n)).card : ℝ) ≤
      N * ∑' p : D, (1 : ℝ) / (p : ℕ) := by
  classical
  let Q := (Finset.Icc 1 N).filter (fun p => p ∈ D)
  have hQ : ∀ p ∈ Q, p ∈ D := fun _ hp => (Finset.mem_filter.mp hp).2
  have heq : (Finset.Icc 1 N).filter (fun n => ∃ p ∈ D, p ∣ n) =
      (Finset.Icc 1 N).filter (fun n => ∃ p ∈ Q, p ∣ n) := by
    apply Finset.filter_congr
    intro n hn
    obtain ⟨hnpos, _⟩ := Finset.mem_Icc.mp hn
    constructor
    · rintro ⟨p, hp, hpn⟩
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hD p hp, ?_⟩, hp⟩, hpn⟩
      exact (Nat.le_of_dvd hnpos hpn).trans (Finset.mem_Icc.mp hn).2
    · rintro ⟨p, hp, hpn⟩
      exact ⟨p, hQ p hp, hpn⟩
  rw [heq]
  apply (finite_divisor_union_bound Q N).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hsum := hs.sum_le_tsum (Q.subtype (fun p => p ∈ D))
    (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  rw [Finset.sum_subtype_of_mem (fun p : ℕ => (1 : ℝ) / p) hQ] at hsum
  exact hsum


end Erdos786Audit

end

section
/- Source module: SummableSetTail.lean -/

/-! Small reciprocal tails of a summable set of integers. -/
namespace Erdos786Audit

open Classical in
theorem summable_set_has_small_reciprocal_tail
    (D : Set ℕ) (hs : Summable (fun p : D => (1 : ℝ) / (p : ℕ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p ∈ D) ∧
      Summable (fun p : {p : ℕ // p ∈ D ∧ p ∉ P} => (1 : ℝ) / (p : ℕ)) ∧
      (∑' p : {p : ℕ // p ∈ D ∧ p ∉ P}, (1 : ℝ) / (p : ℕ)) < ε := by
  have ht := tendsto_tsum_compl_atTop_zero (fun p : D => (1 : ℝ) / (p : ℕ))
  obtain ⟨F, hF⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  let P := F.image (fun p : D => (p : ℕ))
  have hmem (p : D) : (p : ℕ) ∈ P ↔ p ∈ F := by
    simp only [P, Finset.mem_image]
    exact ⟨fun ⟨q, hq, heq⟩ => Subtype.ext heq ▸ hq, fun hp => ⟨p, hp, rfl⟩⟩
  let e : {p : ℕ // p ∈ D ∧ p ∉ P} ≃ {p : D // p ∉ F} :=
    { toFun := fun p => ⟨⟨p, p.property.1⟩, fun hp => p.property.2 ((hmem _).mpr hp)⟩
      invFun := fun p => ⟨p.val, p.val.property, fun hp => p.property ((hmem _).mp hp)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  · exact e.summable_iff.mpr (hs.subtype (fun p : D => p ∉ F))
  · have he := e.tsum_eq (fun p : {p : D // p ∉ F} => (1 : ℝ) / (p.val : ℕ))
    exact he.trans_lt hF


open Classical in
theorem summable_prime_indicator_to_set
    (D : Set ℕ) (hD : ∀ p ∈ D, p.Prime)
    (hs : Summable (fun p : {p : ℕ // p.Prime} =>
      if (p : ℕ) ∈ D then (1 : ℝ) / (p : ℕ) else 0)) :
    Summable (fun p : D => (1 : ℝ) / (p : ℕ)) := by
  let i : D → {p : ℕ // p.Prime} := fun p => ⟨p, hD p p.property⟩
  have hi : Function.Injective i := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun x : {p : ℕ // p.Prime} => x.val) hpq)
  have ht := hs.comp_injective hi
  exact ht.congr (fun p => if_pos p.property)


end Erdos786Audit

end

section
/- Source module: FiniteFibreDensity.lean -/

/-! Removing finite fibres once the class distribution is tight. -/
namespace Erdos786Audit

theorem finite_fibres_over_finite_classes
    {G : Type*} (A : Set ℕ) (b : ℕ → G) (C : Finset G) :
    Set.Finite {n | n ∈ A ∧ b n ∈ C ∧ Set.Finite {m | m ∈ A ∧ b m = b n}} := by
  classical
  let D := {c : G | c ∈ C ∧ Set.Finite {m | m ∈ A ∧ b m = c}}
  have hD : D.Finite := C.finite_toSet.subset (fun _ h => h.1)
  have hU : (⋃ c ∈ D, {m | m ∈ A ∧ b m = c}).Finite :=
    hD.biUnion (fun c hc => hc.2)
  apply hU.subset
  intro n hn
  exact Set.mem_iUnion.mpr ⟨b n, Set.mem_iUnion.mpr ⟨⟨hn.2.1, hn.2.2⟩, hn.1, rfl⟩⟩

open Filter Classical in
theorem finite_fibre_density_zero_of_tightness
    {G : Type*} (A : Set ℕ) (b : ℕ → G)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ C : Finset G, ∀ N : ℕ,
      (((Finset.Icc 1 N).filter (fun n => b n ∉ C)).card : ℝ) ≤ ε * N) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A ∧
        Set.Finite {m | m ∈ A ∧ b m = b n})).card : ℝ) / N) atTop (nhds 0) := by
  apply tendsto_ratio_zero_of_epsilon_bound _ _ tendsto_natCast_atTop_atTop
  intro ε hε
  obtain ⟨C, hC⟩ := htight ε hε
  let T := (finite_fibres_over_finite_classes A b C).toFinset
  refine ⟨T.card, Nat.cast_nonneg _, ?_⟩
  intro N
  have hsub : (Finset.Icc 1 N).filter (fun n => n ∈ A ∧
      Set.Finite {m | m ∈ A ∧ b m = b n}) ⊆
      T ∪ (Finset.Icc 1 N).filter (fun n => b n ∉ C) := by
    intro n hn
    obtain ⟨hnN, hnA, hnfin⟩ := Finset.mem_filter.mp hn
    by_cases hc : b n ∈ C
    · apply Finset.mem_union_left
      simpa only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
        And.intro hnA (And.intro hc hnfin)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hc⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hreal : (((Finset.Icc 1 N).filter (fun n => n ∈ A ∧
      Set.Finite {m | m ∈ A ∧ b m = b n})).card : ℝ) ≤
      T.card + (((Finset.Icc 1 N).filter (fun n => b n ∉ C)).card : ℝ) := by
    exact_mod_cast hcard
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact hreal.trans (add_le_add_right (hC N) _)


open Filter Classical in
theorem uniform_tightness_of_eventual_tightness
    {G : Type*} (b : ℕ → G)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : Finset G, ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (fun n => b n ∉ C)).card : ℝ) ≤ ε * N) :
    ∀ ε : ℝ, 0 < ε → ∃ C : Finset G, ∀ N : ℕ,
      (((Finset.Icc 1 N).filter (fun n => b n ∉ C)).card : ℝ) ≤ ε * N := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
  refine ⟨C ∪ (Finset.Icc 1 N₀).image b, ?_⟩
  intro N
  by_cases hN : N₀ ≤ N
  · apply le_trans _ (hN₀ N hN)
    exact_mod_cast Finset.card_le_card (show
      (Finset.Icc 1 N).filter (fun n => b n ∉ C ∪ (Finset.Icc 1 N₀).image b) ⊆
      (Finset.Icc 1 N).filter (fun n => b n ∉ C) by
        intro n hn
        obtain ⟨hnI, hnC⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hnI, fun hc => hnC (Finset.mem_union_left _ hc)⟩)
  · have hempty : (Finset.Icc 1 N).filter
        (fun n => b n ∉ C ∪ (Finset.Icc 1 N₀).image b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hnI, hnC⟩ := Finset.mem_filter.mp hn
      apply hnC
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨n, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnI).1,
        (Finset.mem_Icc.mp hnI).2.trans (by omega)⟩, rfl⟩
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε.le (Nat.cast_nonneg _)

open Filter Classical in
theorem finite_fibre_density_zero_of_eventual_tightness
    {G : Type*} (A : Set ℕ) (b : ℕ → G)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ C : Finset G, ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (fun n => b n ∉ C)).card : ℝ) ≤ ε * N) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A ∧
        Set.Finite {m | m ∈ A ∧ b m = b n})).card : ℝ) / N) atTop (nhds 0) :=
  finite_fibre_density_zero_of_tightness A b (uniform_tightness_of_eventual_tightness b htight)


end Erdos786Audit

end

section
/- Source module: ClassTightness.lean -/

/-! Finite-class concentration from summable prime support. -/
namespace Erdos786Audit

open Filter Classical in
theorem eventual_class_tightness_of_summable_prime_support
    {G : Type*} [AddCommMonoid G] (b : ℕ → G) (h1 : b 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → b (m * n) = b m + b n)
    (D : Set ℕ) (hD : ∀ p ∈ D, p.Prime)
    (hsupport : ∀ p, p.Prime → b p ≠ 0 → p ∈ D)
    (hs : Summable (fun p : D => (1 : ℝ) / (p : ℕ))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : Finset G, ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (fun n => b n ∉ C)).card : ℝ) ≤ ε * N := by
  intro ε hε
  obtain ⟨P, hPD, hsTail, htail⟩ :=
    summable_set_has_small_reciprocal_tail D hs (ε / 2) (by positivity)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => hD p (hPD p hp)
  obtain ⟨S, hS, hsmall⟩ := exists_finite_smooth_tail_small P hP (ε / 2) (by positivity)
  have ht := (finite_smooth_tail_density P S hP hS).eventually (gt_mem_nhds hsmall)
  refine ⟨S.image b, ?_⟩
  filter_upwards [ht, eventually_ge_atTop 1] with N hN hNpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcount := outside_smooth_classes_count_bound b h1 hmul P S
    {p | p ∈ D ∧ p ∉ P}
    (fun p hp hpP hbp => ⟨hsupport p hp hbp, hpP⟩) N
  have hreal : (((Finset.Icc 1 N).filter (fun n => b n ∉ S.image b)).card : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n => ∃ p ∈ {p | p ∈ D ∧ p ∉ P}, p ∣ n)).card : ℝ) +
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S)).card : ℝ) := by
    exact_mod_cast hcount
  have hd := summable_divisor_union_bound {p | p ∈ D ∧ p ∉ P}
    (fun p hp => (hD p hp.1).pos) hsTail N
  have hdm := mul_le_mul_of_nonneg_left htail.le hNR.le
  have hsm := (div_lt_iff₀ hNR).mp hN
  have hsum := hreal.trans (add_le_add (hd.trans hdm) hsm.le)
  nlinarith only [hsum]

open Filter Classical in
theorem finite_fibre_density_zero_of_summable_prime_support
    {G : Type*} [AddCommMonoid G] (A : Set ℕ)
    (b : ℕ → G) (h1 : b 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → b (m * n) = b m + b n)
    (D : Set ℕ) (hD : ∀ p ∈ D, p.Prime)
    (hsupport : ∀ p, p.Prime → b p ≠ 0 → p ∈ D)
    (hs : Summable (fun p : D => (1 : ℝ) / (p : ℕ))) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A ∧
        Set.Finite {m | m ∈ A ∧ b m = b n})).card : ℝ) / N) atTop (nhds 0) :=
  finite_fibre_density_zero_of_eventual_tightness A b
    (eventual_class_tightness_of_summable_prime_support b h1 hmul D hD hsupport hs)


end Erdos786Audit

end

section
/- Source module: SmoothCharacters.lean -/

/-! Multiplicative character weights on actual integers for the smooth-law Fourier bridge. -/
namespace Erdos786Audit

noncomputable def integerCharacterWeight (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle) (n : ℕ) : ℂ :=
  (n : ℂ)⁻¹ * (χ (Multiplicative.ofAdd (integerClass A hA n)) : ℂ)

theorem integerCharacterWeight_one (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle) :
    integerCharacterWeight A hA χ 1 = 1 := by
  simp [integerCharacterWeight, integerClass_one]

theorem integerCharacterWeight_mul (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle) (m n : ℕ) :
    integerCharacterWeight A hA χ (m * n) =
      integerCharacterWeight A hA χ m * integerCharacterWeight A hA χ n := by
  by_cases hm : m = 0
  · simp [hm, integerCharacterWeight]
  by_cases hn : n = 0
  · simp [hn, integerCharacterWeight]
  simp only [integerCharacterWeight, integerClass_mul_nonzero A hA m n hm hn,
    ofAdd_add, map_mul, Circle.coe_mul, Nat.cast_mul, mul_inv_rev]
  ring

noncomputable def integerCharacterWeightHom (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle) : ℕ →* ℂ where
  toFun := integerCharacterWeight A hA χ
  map_one' := integerCharacterWeight_one A hA χ
  map_mul' := integerCharacterWeight_mul A hA χ

theorem integerCharacterWeight_norm (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle) (n : ℕ) :
    ‖integerCharacterWeight A hA χ n‖ = (n : ℝ)⁻¹ := by
  have hc : ‖(χ (Multiplicative.ofAdd (integerClass A hA n)) : ℂ)‖ = 1 :=
    (χ (Multiplicative.ofAdd (integerClass A hA n))).norm_coe
  simpa [integerCharacterWeight, norm_inv] using congrArg (fun x : ℝ => (n : ℝ)⁻¹ * x) hc

theorem smooth_character_euler_hasSum (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun s : Nat.factoredNumbers P => integerCharacterWeight A hA χ s)
      (∏ p ∈ P, (1 - integerCharacterWeight A hA χ p)⁻¹) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖integerCharacterWeightHom A hA χ p‖ < 1 := by
    intro p hp
    change ‖integerCharacterWeight A hA χ p‖ < 1
    rw [integerCharacterWeight_norm]
    exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := integerCharacterWeightHom A hA χ) hp P).2
  simpa only [integerCharacterWeightHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Finset.filter_eq_self.mpr hP] using hh

theorem normalized_smooth_character_hasSum (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun s : Nat.factoredNumbers P =>
      (∏ p ∈ P, (1 - (1 : ℂ) / p)) * integerCharacterWeight A hA χ s)
      (∏ p ∈ P, (1 - (1 : ℂ) / p) /
        (1 - (p : ℂ)⁻¹ * (χ (Multiplicative.ofAdd (integerClass A hA p)) : ℂ))) := by
  have hh := (smooth_character_euler_hasSum A hA χ P hP).mul_left
    (∏ p ∈ P, (1 - (1 : ℂ) / p))
  simpa only [← Finset.prod_mul_distrib, integerCharacterWeight, div_eq_mul_inv] using hh

theorem normalized_smooth_character_real_weights (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun s : Nat.factoredNumbers P =>
      (((∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ) : ℝ) : ℂ) *
        (χ (Multiplicative.ofAdd (integerClass A hA s)) : ℂ))
      (∏ p ∈ P, (1 - (1 : ℂ) / p) /
        (1 - (p : ℂ)⁻¹ * (χ (Multiplicative.ofAdd (integerClass A hA p)) : ℂ))) := by
  have hh := normalized_smooth_character_hasSum A hA χ P hP
  convert hh using 1
  funext s
  simp [integerCharacterWeight, div_eq_mul_inv, mul_assoc]


end Erdos786Audit

end

section
/- Source module: ClassMass.lean -/

/-! Regrouping nonnegative scalar mass and character series by a class map. -/
namespace Erdos786Audit

noncomputable def classMass {S G : Type*} (w : S → ℝ) (g : S → G) (c : G) : ℝ :=
  ∑' s : g ⁻¹' {c}, w s

theorem classMass_nonneg {S G : Type*} (w : S → ℝ) (g : S → G)
    (hw : ∀ s, 0 ≤ w s) (c : G) : 0 ≤ classMass w g c :=
  tsum_nonneg (fun s => hw s)

theorem classMass_hasSum_one {S G : Type*} (w : S → ℝ) (g : S → G)
    (hw : HasSum w 1) : HasSum (classMass w g) 1 := hw.tsum_fiberwise g

theorem classMass_character_hasSum {S G : Type*} (w : S → ℝ) (g : S → G)
    (χ : G → ℂ) (z : ℂ)
    (h : HasSum (fun s => (w s : ℂ) * χ (g s)) z) :
    HasSum (fun c => (classMass w g c : ℂ) * χ c) z := by
  have hh := h.tsum_fiberwise g
  have heq : ∀ c, (∑' s : g ⁻¹' {c}, (w s : ℂ) * χ (g s)) =
      (classMass w g c : ℂ) * χ c := by
    intro c
    have hi : ∀ s : g ⁻¹' {c}, χ (g s) = χ c := by
      intro s
      exact congrArg χ (Set.mem_singleton_iff.mp s.property)
    simp_rw [hi]
    rw [tsum_mul_right, ← Complex.ofReal_tsum]
    rfl
  simpa only [heq] using hh

theorem finite_class_sum_le_classMass {S G : Type*} (w : S → ℝ) (g : S → G)
    (hw : ∀ s, 0 ≤ w s) (hsum : Summable w) (T : Finset S) (c : G)
    (hT : ∀ s ∈ T, g s = c) : (∑ s ∈ T, w s) ≤ classMass w g c := by
  classical
  rw [classMass, tsum_subtype]
  have hind : Summable ((g ⁻¹' {c}).indicator w) := hsum.indicator _
  have heq : (∑ s ∈ T, w s) = ∑ s ∈ T, (g ⁻¹' {c}).indicator w s := by
    apply Finset.sum_congr rfl
    intro s hs
    exact (Set.indicator_of_mem (by exact hT s hs) w).symm
  rw [heq]
  exact hind.sum_le_tsum T (fun s _ => Set.indicator_nonneg (fun _ _ => hw _) _)


end Erdos786Audit

end

section
/- Source module: SmoothClassLaw.lean -/

/-! The actual normalized smooth distribution, grouped in the fresh integer quotient. -/
namespace Erdos786Audit

noncomputable def smoothClassWeight (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (P : Finset ℕ) (c : Multiplicative (FreshIntegerQuotient A hA)) : ℝ :=
  classMass (fun s : Nat.factoredNumbers P => (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ))
    (fun s => Multiplicative.ofAdd (integerClass A hA s)) c

theorem smoothClassWeight_nonneg (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : Multiplicative (FreshIntegerQuotient A hA)) : 0 ≤ smoothClassWeight A hA P c := by
  apply classMass_nonneg
  intro s
  exact div_nonneg (rough_euler_product_pos P hP).le (Nat.cast_nonneg _)

theorem smoothClassWeight_hasSum_one (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (smoothClassWeight A hA P) 1 :=
  classMass_hasSum_one _ _ (normalized_smooth_mass_hasSum P hP)

theorem smoothClassWeight_character_hasSum (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : Multiplicative (FreshIntegerQuotient A hA) →* Circle) :
    HasSum (fun c => (smoothClassWeight A hA P c : ℂ) * (χ c : ℂ))
      (∏ p ∈ P, (1 - (1 : ℂ) / p) /
        (1 - (p : ℂ)⁻¹ * (χ (Multiplicative.ofAdd (integerClass A hA p)) : ℂ))) :=
  classMass_character_hasSum _ _ (fun c => (χ c : ℂ)) _
    (normalized_smooth_character_real_weights A hA χ P hP)


end Erdos786Audit

end

section
/- Source module: SmoothConcentration.lean -/

/-! Approximate atoms of the actual smooth class distribution from natural density. -/
namespace Erdos786Audit

open Classical in
theorem finite_smooth_class_mass_le_weight
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ s ∈ S, s ∈ Nat.factoredNumbers P)
    (c : FreshIntegerQuotient A hA) :
    (∏ p ∈ P, (1 - (1 : ℝ) / p)) *
      (∑ s ∈ S.filter (fun s => integerClass A hA s = c), (1 : ℝ) / s) ≤
      smoothClassWeight A hA P (Multiplicative.ofAdd c) := by
  let U := S.filter (fun s => integerClass A hA s = c)
  have hU : ∀ s ∈ U, s ∈ Nat.factoredNumbers P :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hh := finite_class_sum_le_classMass
    (fun s : Nat.factoredNumbers P => (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ))
    (fun s => Multiplicative.ofAdd (integerClass A hA s))
    (fun s => div_nonneg (rough_euler_product_pos P hP).le (Nat.cast_nonneg _))
    (normalized_smooth_mass_hasSum P hP).summable
    (U.subtype (fun s => s ∈ Nat.factoredNumbers P)) (Multiplicative.ofAdd c) (by
      intro s hs
      have hsU : s.val ∈ U := by simpa only [Finset.mem_subtype] using hs
      exact congrArg Multiplicative.ofAdd (Finset.mem_filter.mp hsU).2)
  rw [Finset.sum_subtype_of_mem
    (fun n : ℕ => (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (n : ℝ)) hU] at hh
  simpa only [smoothClassWeight, Finset.mul_sum, mul_one_div, U] using hh

open Filter Classical in
theorem actual_smooth_class_approximate_atom
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ)
    (hA : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
      atTop (nhds δ)) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : Multiplicative (FreshIntegerQuotient A hpositive),
      δ - ε ≤ smoothClassWeight A hpositive P c := by
  obtain ⟨S, hS, c, hc⟩ := actual_integer_quotient_concentration A hpositive δ hA P hP ε hε
  exact ⟨Multiplicative.ofAdd c, hc.trans (finite_smooth_class_mass_le_weight A hpositive P S hP hS c)⟩


end Erdos786Audit

end

section
/- Source module: DiscreteCharacters.lean -/

namespace Erdos786Audit

noncomputable section

def rationalCircleToRealCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ))
    (AddSubgroup.zmultiples (1 : ℝ)) (Rat.castHom ℝ).toAddMonoidHom (by
      intro a ha
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
      change ((Rat.castHom ℝ).toAddMonoidHom (z • (1 : ℚ))) ∈
        AddSubgroup.zmultiples (1 : ℝ)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, by simp⟩)

theorem rationalCircleToRealCircle_injective : Function.Injective rationalCircleToRealCircle := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H r =>
    change ((r : ℝ) : AddCircle (1 : ℝ)) = 0 at hx
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hx
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨z, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hz ⊢
    exact_mod_cast hz

/-- Circle-valued characters separate points of arbitrary discrete abelian
groups. This uses Q/Z characters, not a full Pontryagin reflexivity theorem. -/
theorem exists_discrete_character_ne_one {G : Type*} [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G] {g : G} (hg : g ≠ 1) :
    ∃ χ : PontryaginDual G, χ g ≠ 1 := by
  have hga : Additive.ofMul g ≠ (0 : Additive G) := hg
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hga
  let d : Additive G →+ AddCircle (1 : ℝ) := rationalCircleToRealCircle.comp c
  let χ : PontryaginDual G := {
    toFun := fun x => AddCircle.toCircle (d (Additive.ofMul x))
    map_one' := by simp
    map_mul' := by
      intro x y
      change AddCircle.toCircle (d (Additive.ofMul x + Additive.ofMul y)) = _
      rw [map_add, AddCircle.toCircle_add]
    continuous_toFun := continuous_of_discreteTopology }
  refine ⟨χ, ?_⟩
  intro he
  change AddCircle.toCircle (d (Additive.ofMul g)) = 1 at he
  have hz : d (Additive.ofMul g) = 0 :=
    AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
      (by simpa only [AddCircle.toCircle_zero] using he)
  apply hc
  change rationalCircleToRealCircle (c (Additive.ofMul g)) = 0 at hz
  exact rationalCircleToRealCircle_injective
    (by simpa only [map_zero] using hz)


theorem discrete_characters_separate {G : Type*} [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G] {g h : G}
    (he : ∀ χ : PontryaginDual G, χ g = χ h) : g = h := by
  by_contra hn
  have hd : g / h ≠ 1 := fun hh => hn (div_eq_one.mp hh)
  obtain ⟨χ, hχ⟩ := exists_discrete_character_ne_one hd
  exact hχ (by rw [map_div, he χ]; exact div_self' _)

def dualAnnihilator {G : Type*} [CommGroup G] [TopologicalSpace G]
    (L : Subgroup (PontryaginDual G)) : Subgroup G where
  carrier := {g | ∀ χ ∈ L, χ g = 1}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh χ hχ
    rw [map_mul, hg χ hχ, hh χ hχ, one_mul]
  inv_mem' := by
    intro g hg χ hχ
    rw [map_inv, hg χ hχ, inv_one]

/-- An open subgroup of the compact dual has finite annihilator. The proof
embeds that annihilator in the dual of the finite quotient, using only
character separation and the compact/discrete instances already in Mathlib. -/
theorem finite_dualAnnihilator_of_isOpen {G : Type*} [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G]
    (L : Subgroup (PontryaginDual G)) (hL : IsOpen (L : Set (PontryaginDual G))) :
    Finite (dualAnnihilator L) := by
  let : DiscreteTopology (PontryaginDual G ⧸ L) := QuotientGroup.discreteTopology hL
  let eval (g : dualAnnihilator L) : PontryaginDual G →* Circle := {
    toFun := fun χ => χ g.val
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let φ : dualAnnihilator L → PontryaginDual (PontryaginDual G ⧸ L) := fun g => {
    toMonoidHom := QuotientGroup.lift L (eval g) (fun χ hχ => g.property χ hχ)
    continuous_toFun := continuous_of_discreteTopology }
  apply Finite.of_injective φ
  intro g h hgh
  apply Subtype.ext
  apply discrete_characters_separate
  intro χ
  exact congrArg (fun ψ : PontryaginDual (PontryaginDual G ⧸ L) =>
    ψ (QuotientGroup.mk χ)) hgh


open MeasureTheory in
theorem integral_nontrivial_circle_character {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (χ : G →* Circle) (hχ : χ ≠ 1) :
    (∫ x, (χ x : ℂ) ∂μ) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra! hn
    apply hχ
    apply MonoidHom.ext
    intro g
    exact hn g
  have ht := integral_mul_left_eq_self (μ := μ) (fun x => (χ x : ℂ)) g
  simp only [map_mul, Circle.coe_mul, integral_const_mul] at ht
  have hc : (χ g : ℂ) ≠ 1 := fun h => hg (Subtype.ext h)
  have hz : ((χ g : ℂ) - 1) * (∫ x, (χ x : ℂ) ∂μ) = 0 := by
    linear_combination ht
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

open MeasureTheory in
theorem integral_one_sub_re_nontrivial_character {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (χ : G →* Circle) (hχ : χ ≠ 1) (hi : Integrable (fun x => (χ x : ℂ)) μ) :
    (∫ x, 1 - (χ x : ℂ).re ∂μ) = 1 := by
  have hir : Integrable (fun x => (χ x : ℂ).re) μ := hi.re
  have hre := integral_re hi
  change (∫ x, (χ x : ℂ).re ∂μ) = (∫ x, (χ x : ℂ) ∂μ).re at hre
  rw [integral_sub (integrable_const 1) hir, integral_const, hre,
    integral_nontrivial_circle_character μ χ hχ]
  simp


def restrictedDualEvaluation {G : Type*} [CommGroup G] [TopologicalSpace G]
    (L : Subgroup (PontryaginDual G)) (g : G) : L →* Circle where
  toFun χ := χ.val g
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrictedDualEvaluation_eq_one_iff {G : Type*} [CommGroup G]
    [TopologicalSpace G] (L : Subgroup (PontryaginDual G)) (g : G) :
    restrictedDualEvaluation L g = 1 ↔ g ∈ dualAnnihilator L := by
  constructor
  · intro he χ hχ
    exact DFunLike.congr_fun he ⟨χ, hχ⟩
  · intro hg
    apply MonoidHom.ext
    intro χ
    exact hg χ.val χ.property

open MeasureTheory Classical in
theorem integral_dual_energy_eq_annihilator_indicator
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (L : Subgroup (PontryaginDual G)) [MeasurableSpace L] [MeasurableMul L]
    (μ : Measure L) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ] (g : G)
    (hi : Integrable (fun χ : L => (χ.val g : ℂ)) μ) :
    (∫ χ : L, 1 - (χ.val g : ℂ).re ∂μ) =
      if g ∈ dualAnnihilator L then 0 else 1 := by
  classical
  by_cases hg : g ∈ dualAnnihilator L
  · rw [if_pos hg]
    have he : (fun χ : L => 1 - (χ.val g : ℂ).re) = fun _ => (0 : ℝ) := by
      funext χ
      rw [hg χ.val χ.property]
      simp
    rw [he, integral_zero]
  · rw [if_neg hg]
    exact integral_one_sub_re_nontrivial_character μ (restrictedDualEvaluation L g)
      (fun he => hg ((restrictedDualEvaluation_eq_one_iff L g).mp he)) hi


open MeasureTheory Classical in
theorem summable_weights_outside_annihilator
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (L : Subgroup (PontryaginDual G)) [MeasurableSpace L] [MeasurableMul L]
    (μ : Measure L) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (g : ℕ → G) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hi : ∀ i, Integrable (fun χ : L => (χ.val (g i) : ℂ)) μ)
    (C : ℝ)
    (hb : ∀ χ : L, ∀ n,
      (∑ i ∈ Finset.range n, w i * (1 - (χ.val (g i) : ℂ).re)) ≤ C) :
    Summable (fun i => if g i ∈ dualAnnihilator L then 0 else w i) := by
  let E : ℕ → L → ℝ := fun i χ => w i * (1 - (χ.val (g i) : ℂ).re)
  have hE : ∀ i, Integrable (E i) μ := by
    intro i
    have hr : Integrable (fun χ : L => (χ.val (g i) : ℂ).re) μ := (hi i).re
    exact ((integrable_const 1).sub hr).const_mul (w i)
  have he : ∀ i, (∫ χ, E i χ ∂μ) =
      if g i ∈ dualAnnihilator L then 0 else w i := by
    intro i
    dsimp [E]
    rw [integral_const_mul, integral_dual_energy_eq_annihilator_indicator L μ (g i) (hi i)]
    split_ifs <;> simp
  apply summable_of_sum_range_le (fun i => by split_ifs <;> first | exact le_rfl | exact hw i)
  intro n
  simp only [← he]
  rw [← integral_finsetSum (Finset.range n) (fun i _ => hE i)]
  have hsum : Integrable (fun χ => ∑ i ∈ Finset.range n, E i χ) μ :=
    integrable_finsetSum (Finset.range n) (fun i _ => hE i)
  have hle := integral_mono hsum (integrable_const C) (fun χ => hb χ n)
  simpa using hle


theorem continuous_restrictedDualEvaluation {G : Type*} [CommGroup G]
    [TopologicalSpace G] (L : Subgroup (PontryaginDual G)) (g : G) :
    Continuous (restrictedDualEvaluation L g) := by
  change Continuous (fun χ : L => (χ.val : G →ₜ* Circle) g)
  have he : Continuous (fun χ : G →ₜ* Circle => χ g) := continuous_eval_const g
  exact he.comp continuous_subtype_val

open MeasureTheory in
theorem integrable_restrictedDualEvaluation {G : Type*} [CommGroup G]
    [TopologicalSpace G] (L : Subgroup (PontryaginDual G))
    [MeasurableSpace L] [BorelSpace L] (μ : Measure L) [IsFiniteMeasure μ] (g : G) :
    Integrable (fun χ : L => (χ.val g : ℂ)) μ := by
  have hcirc : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have hc : Continuous (fun χ : L => (χ.val g : ℂ)) :=
    hcirc.comp (continuous_restrictedDualEvaluation L g)
  apply Integrable.of_bound hc.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun χ => (χ.val g).norm_coe.le)


open MeasureTheory Classical in
theorem finite_subgroup_with_summable_exceptions_of_open_energy_bound
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (L : Subgroup (PontryaginDual G)) (hL : IsOpen (L : Set (PontryaginDual G)))
    [MeasurableSpace L] [BorelSpace L] [MeasurableMul L]
    (μ : Measure L) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (g : ℕ → G) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (C : ℝ)
    (hb : ∀ χ : L, ∀ n,
      (∑ i ∈ Finset.range n, w i * (1 - (χ.val (g i) : ℂ).re)) ≤ C) :
    ∃ K : Subgroup G, Finite K ∧
      Summable (fun i => if g i ∈ K then 0 else w i) := by
  refine ⟨dualAnnihilator L, finite_dualAnnihilator_of_isOpen L hL, ?_⟩
  exact summable_weights_outside_annihilator L μ g w hw
    (fun i => integrable_restrictedDualEvaluation L μ (g i)) C hb


end
end Erdos786Audit

end

section
/- Source module: FourierConcentration.lean -/

namespace Erdos786Audit

open MeasureTheory in
theorem square_integral_le_integral_square
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  let m := ∫ x, f x ∂μ
  have hb : ∀ x, 2*m*f x - m^2 ≤ (f x)^2 := by
    intro x
    nlinarith [sq_nonneg (f x-m)]
  have hi := integral_mono ((hf.const_mul (2*m)).sub (integrable_const (m^2))) hf2 hb
  change (∫ x, 2*m*f x - m^2 ∂μ) ≤ ∫ x, (f x)^2 ∂μ at hi
  rw [integral_sub (hf.const_mul (2*m)) (integrable_const (m^2)),
    integral_const_mul, integral_const] at hi
  have hμ : μ.real Set.univ = 1 := by simp
  rw [hμ, one_smul] at hi
  dsimp [m] at hi
  nlinarith

open MeasureTheory in
theorem square_norm_integral_le_integral_square_norm
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  have hn := norm_integral_le_integral_norm f (μ := μ)
  have hsq := square_integral_le_integral_square μ (fun x => ‖f x‖) hf.norm hf2
  have hi : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg (fun x => norm_nonneg _)
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]


noncomputable def weightedCharacterSeries {G : Type*} [Monoid G] [TopologicalSpace G]
    (w : G → ℝ) (χ : PontryaginDual G) : ℂ := ∑' g, (w g : ℂ) * (χ g : ℂ)

theorem continuous_complex_dual_evaluation {G : Type*} [Monoid G] [TopologicalSpace G]
    (g : G) : Continuous (fun χ : PontryaginDual G => (χ g : ℂ)) := by
  have hc : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have he : Continuous (fun χ : G →ₜ* Circle => χ g) := continuous_eval_const g
  exact hc.comp he

theorem weighted_character_term_norm {G : Type*} [Monoid G] [TopologicalSpace G]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (χ : PontryaginDual G) (g : G) :
    ‖(w g : ℂ) * (χ g : ℂ)‖ = w g := by
  rw [norm_mul, (χ g).norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hw g)]

theorem continuous_weightedCharacterSeries {G : Type*} [Monoid G] [TopologicalSpace G]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hs : Summable w) :
    Continuous (weightedCharacterSeries w) := by
  apply continuous_tsum (fun g => continuous_const.mul (continuous_complex_dual_evaluation g)) hs
  intro g χ
  exact (weighted_character_term_norm w hw χ g).le

theorem norm_weightedCharacterSeries_le {G : Type*} [Monoid G] [TopologicalSpace G]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hs : Summable w) (χ : PontryaginDual G) :
    ‖weightedCharacterSeries w χ‖ ≤ ∑' g, w g := by
  have hn : Summable (fun g => ‖(w g : ℂ) * (χ g : ℂ)‖) := by
    simpa only [weighted_character_term_norm w hw χ] using hs
  simpa only [weightedCharacterSeries, weighted_character_term_norm w hw χ] using
    norm_tsum_le_tsum_norm hn


open MeasureTheory Classical in
theorem integral_dual_evaluation
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    [MeasurableSpace (PontryaginDual G)] [MeasurableMul (PontryaginDual G)]
    (μ : Measure (PontryaginDual G)) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (g : G) : (∫ χ, (χ g : ℂ) ∂μ) = if g = 1 then 1 else 0 := by
  by_cases hg : g = 1
  · rw [if_pos hg, hg]
    simp
  · rw [if_neg hg]
    let ψ : PontryaginDual G →* Circle := {
      toFun χ := χ g
      map_one' := rfl
      map_mul' _ _ := rfl }
    obtain ⟨χ, hχ⟩ := exists_discrete_character_ne_one hg
    exact integral_nontrivial_circle_character μ ψ
      (fun he => hχ (DFunLike.congr_fun he χ))

theorem projected_weightedCharacterSeries
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (w : G → ℝ) (χ : PontryaginDual G) (a : G) :
    weightedCharacterSeries w χ * (χ a : ℂ)⁻¹ =
      ∑' g, (w g : ℂ) * (χ (g/a) : ℂ) := by
  rw [weightedCharacterSeries, ← tsum_mul_right]
  apply tsum_congr
  intro g
  simp only [div_eq_mul_inv, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, mul_assoc]

open MeasureTheory in
theorem recover_weight_from_character_series
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    [MeasurableMul (PontryaginDual G)]
    (μ : Measure (PontryaginDual G)) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hs : Summable w) (a : G) :
    (∫ χ, weightedCharacterSeries w χ * (χ a : ℂ)⁻¹ ∂μ) = (w a : ℂ) := by
  classical
  let T : G → PontryaginDual G → ℂ := fun g χ => (w g : ℂ) * (χ (g/a) : ℂ)
  have hn : ∀ g χ, ‖T g χ‖ = w g := by
    intro g χ
    exact weighted_character_term_norm (fun _ : G => w g) (fun _ => hw g) χ (g/a)
  have hi : ∀ g, Integrable (T g) μ := by
    intro g
    have hc : Continuous (T g) :=
      continuous_const.mul (continuous_complex_dual_evaluation (g/a))
    exact Integrable.of_bound hc.aestronglyMeasurable (w g)
      (Filter.Eventually.of_forall (fun χ => (hn g χ).le))
  have hni : ∀ g, (∫ χ, ‖T g χ‖ ∂μ) = w g := by
    intro g
    simp_rw [hn g]
    simp
  have hsum : Summable (fun g => ∫ χ, ‖T g χ‖ ∂μ) := by
    simpa only [hni] using hs
  calc
    _ = ∫ χ, ∑' g, T g χ ∂μ := by
      simp only [projected_weightedCharacterSeries, T]
    _ = ∑' g, ∫ χ, T g χ ∂μ :=
      (integral_tsum_of_summable_integral_norm hi hsum).symm
    _ = ∑' g, if g = a then (w a : ℂ) else 0 := by
      apply tsum_congr
      intro g
      dsimp [T]
      rw [integral_const_mul, integral_dual_evaluation]
      by_cases hg : g = a
      · subst g
        simp
      · simp [hg, div_eq_one]
    _ = (w a : ℂ) := by simp


open MeasureTheory in
theorem atom_square_le_fourier_energy
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    [MeasurableMul (PontryaginDual G)]
    (μ : Measure (PontryaginDual G)) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hs : Summable w) (h1 : ∑' g, w g = 1)
    (a : G) : (w a)^2 ≤ ∫ χ, ‖weightedCharacterSeries w χ‖^2 ∂μ := by
  let P : PontryaginDual G → ℂ := fun χ => weightedCharacterSeries w χ * (χ a⁻¹ : ℂ)
  have hPc : Continuous P :=
    (continuous_weightedCharacterSeries w hw hs).mul (continuous_complex_dual_evaluation a⁻¹)
  have hPn : ∀ χ, ‖P χ‖ = ‖weightedCharacterSeries w χ‖ := by
    intro χ
    exact (norm_mul _ _).trans (by rw [(χ a⁻¹).norm_coe, mul_one])
  have hPb : ∀ χ, ‖P χ‖ ≤ 1 := fun χ => by
    rw [hPn χ]
    exact (norm_weightedCharacterSeries_le w hw hs χ).trans_eq h1
  have hPi : Integrable P μ := Integrable.of_bound hPc.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hPb)
  have hPi2 : Integrable (fun χ => ‖P χ‖^2) μ := by
    apply Integrable.of_bound (hPc.norm.pow 2).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro χ
    change ‖(‖P χ‖^2 : ℝ)‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hPb χ, norm_nonneg (P χ)]
  have hmean : (∫ χ, P χ ∂μ) = (w a : ℂ) := by
    simpa only [P, map_inv, Circle.coe_inv] using recover_weight_from_character_series μ w hw hs a
  have hb := square_norm_integral_le_integral_square_norm μ P hPi hPi2
  rw [hmean, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw a)] at hb
  simpa only [hPn] using hb


open MeasureTheory in
theorem approximate_atom_square_le_fourier_energy
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    [MeasurableMul (PontryaginDual G)]
    (μ : Measure (PontryaginDual G)) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hs : Summable w) (h1 : ∑' g, w g = 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ a, δ-ε ≤ w a) :
    δ^2 ≤ ∫ χ, ‖weightedCharacterSeries w χ‖^2 ∂μ := by
  let I := ∫ χ, ‖weightedCharacterSeries w χ‖^2 ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun χ => sq_nonneg _)
  have hsqrt : (Real.sqrt I)^2 = I := Real.sq_sqrt hI
  have hroot : δ ≤ Real.sqrt I := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a, ha⟩ := hnear ε hε
    have hb : (w a)^2 ≤ I := atom_square_le_fourier_energy μ w hw hs h1 a
    have hc : w a ≤ Real.sqrt I := by
      nlinarith [hw a, Real.sqrt_nonneg I]
    linarith
  change δ^2 ≤ I
  nlinarith [Real.sqrt_nonneg I]


end Erdos786Audit

end

section
/- Source module: GeometricFourier.lean -/

namespace Erdos786Audit

theorem geometric_character_hasSum (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (z : Circle) :
    HasSum (fun j : ℕ => ((1-q : ℝ) : ℂ) * (q : ℂ)^j * (z : ℂ)^j)
      (((1-q : ℝ) : ℂ) / (1 - (q : ℂ)*(z : ℂ))) := by
  have hn : ‖(q : ℂ) * (z : ℂ)‖ < 1 := by
    rw [norm_mul, z.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    exact hq1
  have h := (hasSum_geometric_of_norm_lt_one hn).mul_left ((1-q : ℝ) : ℂ)
  simpa only [mul_pow, mul_assoc, div_eq_mul_inv] using h

theorem geometric_denominator_normSq (q : ℝ) (z : Circle) :
    Complex.normSq (1 - (q : ℂ)*(z : ℂ)) =
      (1-q)^2 + 2*q*(1-(z : ℂ).re) := by
  have hz := z.normSq_coe
  rw [Complex.normSq_apply] at hz ⊢
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_im, Complex.one_im,
    Complex.mul_im]
  nlinarith [congrArg (fun x : ℝ => q^2 * x) hz]

theorem geometric_character_normSq (q : ℝ) (hq : q ≠ 1) (z : Circle) :
    Complex.normSq (((1-q : ℝ) : ℂ) / (1 - (q : ℂ)*(z : ℂ))) =
      (1 + 2*q*(1-(z : ℂ).re)/(1-q)^2)⁻¹ := by
  rw [Complex.normSq_div, Complex.normSq_ofReal, geometric_denominator_normSq]
  have hd : (1-q)^2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hq))
  have he : 1 + 2*q*(1-(z : ℂ).re)/(1-q)^2 =
      ((1-q)^2 + 2*q*(1-(z : ℂ).re))/(1-q)^2 := by
    rw [add_div, div_self hd]
  rw [he, inv_div, pow_two]


theorem circle_real_defect_bounds (z : Circle) :
    0 ≤ 1-(z : ℂ).re ∧ 1-(z : ℂ).re ≤ 2 := by
  have hr : |(z : ℂ).re| ≤ 1 := by
    simpa only [z.norm_coe] using Complex.abs_re_le_norm (z : ℂ)
  obtain ⟨hl, hu⟩ := abs_le.mp hr
  constructor <;> linarith

theorem geometric_factor_bounds (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (z : Circle) :
    0 < Complex.normSq (((1-q : ℝ) : ℂ) / (1-(q : ℂ)*(z : ℂ))) ∧
    Complex.normSq (((1-q : ℝ) : ℂ) / (1-(q : ℂ)*(z : ℂ))) ≤ 1 := by
  rw [geometric_character_normSq q hq1.ne z]
  have hu : 0 ≤ 2*q*(1-(z : ℂ).re)/(1-q)^2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq)
      (circle_real_defect_bounds z).1) (sq_nonneg _)
  have hd : 0 < 1 + 2*q*(1-(z : ℂ).re)/(1-q)^2 := by linarith
  exact ⟨inv_pos.mpr hd, (inv_le_one₀ hd).mpr (by linarith)⟩


noncomputable def geometricFourierProduct (q : ℕ → ℝ) (z : ℕ → Circle) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n,
    Complex.normSq (((1-q i : ℝ) : ℂ) / (1-(q i : ℂ)*(z i : ℂ)))

theorem geometricFourierProduct_pos (q : ℕ → ℝ) (z : ℕ → Circle)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (n : ℕ) :
    0 < geometricFourierProduct q z n := by
  exact Finset.prod_pos (fun i _ => (geometric_factor_bounds (q i) (hq i) (hq1 i) (z i)).1)

theorem geometricFourierProduct_antitone (q : ℕ → ℝ) (z : ℕ → Circle)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    Antitone (geometricFourierProduct q z) := by
  apply antitone_nat_of_succ_le
  intro n
  change (∏ i ∈ Finset.range (n+1),
    Complex.normSq (((1-q i : ℝ) : ℂ) / (1-(q i : ℂ)*(z i : ℂ)))) ≤ _
  rw [Finset.prod_range_succ]
  exact mul_le_of_le_one_right (geometricFourierProduct_pos q z hq hq1 n).le
    (geometric_factor_bounds (q n) (hq n) (hq1 n) (z n)).2

theorem geometricFourierProduct_le_one (q : ℕ → ℝ) (z : ℕ → Circle)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (n : ℕ) :
    geometricFourierProduct q z n ≤ 1 := by
  simpa [geometricFourierProduct] using
    geometricFourierProduct_antitone q z hq hq1 (Nat.zero_le n)


theorem continuous_geometric_factor (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Continuous (fun z : Circle =>
      Complex.normSq (((1-q : ℝ) : ℂ) / (1-(q : ℂ)*(z : ℂ)))) := by
  have he : (fun z : Circle =>
      Complex.normSq (((1-q : ℝ) : ℂ) / (1-(q : ℂ)*(z : ℂ)))) =
      fun z : Circle => (1 + 2*q*(1-(z : ℂ).re)/(1-q)^2)⁻¹ :=
    by
      funext z
      exact geometric_character_normSq q hq1.ne z
  rw [he]
  apply Continuous.inv₀ (by fun_prop)
  intro z
  have hu : 0 ≤ 2*q*(1-(z : ℂ).re)/(1-q)^2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq)
      (circle_real_defect_bounds z).1) (sq_nonneg _)
  linarith

theorem continuous_geometricFourierProduct {X : Type*} [TopologicalSpace X]
    (q : ℕ → ℝ) (z : ℕ → X → Circle)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hz : ∀ i, Continuous (z i)) (n : ℕ) :
    Continuous (fun x => geometricFourierProduct q (fun i => z i x) n) := by
  unfold geometricFourierProduct
  apply continuous_finsetProd
  intro i _
  exact (continuous_geometric_factor (q i) (hq i) (hq1 i)).comp (hz i)


end Erdos786Audit

end

section
/- Source module: FourierLog.lean -/

namespace Erdos786Audit

theorem bounded_log_comparison {u : ℝ} (hu : 0 ≤ u) (hu8 : u ≤ 8) :
    u / 9 ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  constructor
  · have h := Real.le_log_one_add_of_nonneg hu
    have hd : 0 < u + 2 := by linarith
    have hsmall : u / 9 ≤ 2 * u / (u + 2) := by
      apply (le_div_iff₀ hd).2
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hu8)]
    exact hsmall.trans h
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)
    linarith

theorem fourier_log_comparison {q v : ℝ}
    (hq : 0 < q) (hqhalf : q ≤ 1/2) (hv : 0 ≤ v) (hv2 : v ≤ 2) :
    (2/9) * q * v ≤ Real.log (1 + 2*q*v/(1-q)^2) ∧
      Real.log (1 + 2*q*v/(1-q)^2) ≤ 8*q*v := by
  let d := (1-q)^2
  let u := 2*q*v/d
  have hd : 0 < d := by
    dsimp [d]
    exact sq_pos_of_pos (by linarith)
  have hdlo : (1:ℝ)/4 ≤ d := by dsimp [d]; nlinarith
  have hdhi : d ≤ 1 := by dsimp [d]; nlinarith
  have hqv : 0 ≤ q*v := mul_nonneg hq.le hv
  have hqvhi : q*v ≤ 1 := by nlinarith
  have hunonneg : 0 ≤ u := by dsimp [u]; positivity
  have hulow : 2*q*v ≤ u := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg hqv (sub_nonneg.mpr hdhi)]
  have huhi : u ≤ 8*q*v := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hqv (sub_nonneg.mpr hdlo)]
  have hu8 : u ≤ 8 := by linarith
  obtain ⟨hl, hh⟩ := bounded_log_comparison hunonneg hu8
  change (2/9)*q*v ≤ Real.log (1+u) ∧ Real.log (1+u) ≤ 8*q*v
  constructor <;> linarith


theorem energy_bounded_of_product_lower
    (q v : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (hv : ∀ i, 0 ≤ v i) (hv2 : ∀ i, v i ≤ 2)
    (c : ℝ) (hc : 0 < c)
    (hprod : ∀ n, c ≤ ∏ i ∈ Finset.range n,
      (1 + 2*q i*v i/(1-q i)^2)⁻¹) :
    ∀ n, (∑ i ∈ Finset.range n, q i*v i) ≤ -(9/2)*Real.log c := by
  intro n
  let a : ℕ → ℝ := fun i => 1 + 2*q i*v i/(1-q i)^2
  have ha : ∀ i, 0 < a i := by
    intro i
    dsimp [a]
    have hden : 0 < (1-q i)^2 := sq_pos_of_pos (by linarith [hqhalf i])
    have hu : 0 ≤ 2*q i*v i/(1-q i)^2 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hq i).le) (hv i)) hden.le
    linarith
  have hlog := Real.log_le_log hc (hprod n)
  change Real.log c ≤ Real.log (∏ i ∈ Finset.range n, (a i)⁻¹) at hlog
  rw [Real.log_prod (fun i _ => inv_ne_zero (ne_of_gt (ha i)))] at hlog
  simp only [Real.log_inv, Finset.sum_neg_distrib] at hlog
  have hsum : (2/9) * (∑ i ∈ Finset.range n, q i*v i) ≤
      ∑ i ∈ Finset.range n, Real.log (a i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := (fourier_log_comparison (hq i) (hqhalf i) (hv i) (hv2 i)).1
    dsimp [a]
    nlinarith
  linarith


open MeasureTheory in
theorem nested_superlevels_positive {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : ℕ → X → ℝ)
    (hF : ∀ n, Measurable (F n)) (hmono : ∀ x, Antitone (fun n => F n x))
    (c : ℝ) (ε : ENNReal) (hε : 0 < ε)
    (hlevel : ∀ n, ε ≤ μ {x | c ≤ F n x}) :
    0 < μ {x | ∀ n, c ≤ F n x} := by
  let s : ℕ → Set X := fun n => {x | c ≤ F n x}
  have hs : Antitone s := by
    intro i j hij x hx
    exact le_trans hx (hmono x hij)
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_le measurable_const (hF n)
  have heq : {x | ∀ n, c ≤ F n x} = ⋂ n, s n := by
    ext x
    simp [s]
  rw [heq, hs.measure_iInter (fun n => (hsm n).nullMeasurableSet)
    ⟨0, measure_ne_top μ (s 0)⟩]
  exact lt_of_lt_of_le hε (le_iInf hlevel)


open MeasureTheory in
theorem integral_le_threshold_add_superlevel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Integrable f μ) (hfm : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    (c : ℝ) (hc : 0 ≤ c) :
    (∫ x, f x ∂μ) ≤ c + μ.real {x | c ≤ f x} := by
  let s : Set X := {x | c ≤ f x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hfm
  have hi : Integrable (s.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hs
  have hb : ∀ x, f x ≤ c + s.indicator (fun _ : X => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      linarith [hf1 x]
    · rw [Set.indicator_of_notMem hx]
      have hn : ¬ c ≤ f x := hx
      linarith
  have h := integral_mono hf ((integrable_const c).add hi) hb
  change (∫ x, f x ∂μ) ≤ ∫ x, c + s.indicator (fun _ : X => (1 : ℝ)) x ∂μ at h
  rw [integral_add (integrable_const c) hi, integral_const,
    integral_indicator_const 1 hs] at h
  simpa [s] using h


open MeasureTheory in
theorem positive_uniform_superlevel_of_integral_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : ℕ → X → ℝ)
    (hFi : ∀ n, Integrable (F n) μ) (hFm : ∀ n, Measurable (F n))
    (hF1 : ∀ n x, F n x ≤ 1) (hmono : ∀ x, Antitone (fun n => F n x))
    (d : ℝ) (hd : 0 < d) (hint : ∀ n, d ≤ ∫ x, F n x ∂μ) :
    0 < μ {x | ∀ n, d/2 ≤ F n x} := by
  apply nested_superlevels_positive μ F hFm hmono (d/2) (ENNReal.ofReal (d/2))
  · exact ENNReal.ofReal_pos.mpr (by linarith)
  · intro n
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr
    have hb := integral_le_threshold_add_superlevel μ (F n) (hFi n)
      (hFm n) (hF1 n) (d/2) (by linarith)
    change (∫ x, F n x ∂μ) ≤ d/2 + (μ {x | d/2 ≤ F n x}).toReal at hb
    linarith [hint n]


end Erdos786Audit

end

section
/- Source module: CharacterEnergy.lean -/

namespace Erdos786Audit

noncomputable section

def circleEnergy (z : Circle) : ℝ := ‖(z : ℂ) - 1‖ ^ 2

theorem circleEnergy_nonneg (z : Circle) : 0 ≤ circleEnergy z := sq_nonneg _

theorem circleEnergy_eq (z : Circle) : circleEnergy z = 2 * (1 - (z : ℂ).re) := by
  have hz := Circle.normSq_coe z
  rw [Complex.normSq_apply] at hz
  unfold circleEnergy
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

theorem circleEnergy_mul (z w : Circle) :
    circleEnergy (z * w) ≤ 2 * circleEnergy z + 2 * circleEnergy w := by
  have heq : (z : ℂ) * (w : ℂ) - 1 =
      (z : ℂ) * ((w : ℂ) - 1) + ((z : ℂ) - 1) := by ring
  have h := norm_add_le ((z : ℂ) * ((w : ℂ) - 1)) ((z : ℂ) - 1)
  rw [norm_mul, z.norm_coe, one_mul, ← heq] at h
  have hleft := norm_nonneg ((z : ℂ) * (w : ℂ) - 1)
  have hright := norm_nonneg ((w : ℂ) - 1)
  have hright' := norm_nonneg ((z : ℂ) - 1)
  have hsquare := sq_nonneg (‖(z : ℂ) - 1‖ - ‖(w : ℂ) - 1‖)
  change ‖(z : ℂ) * (w : ℂ) - 1‖ ^ 2 ≤ _
  unfold circleEnergy
  nlinarith

theorem circleEnergy_inv (z : Circle) : circleEnergy z⁻¹ = circleEnergy z := by
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  have heq : (z : ℂ)⁻¹ - 1 = -((z : ℂ)⁻¹ * ((z : ℂ) - 1)) := by
    field_simp
    ring
  unfold circleEnergy
  simp only [Circle.coe_inv]
  rw [heq, norm_neg, norm_mul, norm_inv, z.norm_coe]
  simp

@[simp] theorem circleEnergy_one : circleEnergy 1 = 0 := by
  simp [circleEnergy]

def partialEnergy {G : Type*} [Group G]
    (χ : ℕ → G →* Circle) (w : ℕ → ℝ) (x : G) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, w i * circleEnergy (χ i x)

theorem partialEnergy_mul {G : Type*} [Group G]
    (χ : ℕ → G →* Circle) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x y : G) (n : ℕ) :
    partialEnergy χ w (x*y) n ≤
      2 * partialEnergy χ w x n + 2 * partialEnergy χ w y n := by
  unfold partialEnergy
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        w i * (2 * circleEnergy (χ i x) + 2 * circleEnergy (χ i y)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_mul]
      exact mul_le_mul_of_nonneg_left (circleEnergy_mul _ _) (hw i)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem partialEnergy_inv {G : Type*} [Group G]
    (χ : ℕ → G →* Circle) (w : ℕ → ℝ) (x : G) (n : ℕ) :
    partialEnergy χ w x⁻¹ n = partialEnergy χ w x n := by
  simp [partialEnergy, circleEnergy_inv]

def finiteEnergySubgroup {G : Type*} [Group G]
    (χ : ℕ → G →* Circle) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) : Subgroup G where
  carrier := {x | ∃ C : ℝ, ∀ n, partialEnergy χ w x n ≤ C}
  one_mem' := by
    refine ⟨0, ?_⟩
    intro n
    simp [partialEnergy]
  mul_mem' := by
    rintro x y ⟨Cx, hx⟩ ⟨Cy, hy⟩
    refine ⟨2*Cx+2*Cy, ?_⟩
    intro n
    have h := partialEnergy_mul χ w hw x y n
    have hx' := hx n
    have hy' := hy n
    linarith
  inv_mem' := by
    rintro x ⟨C, hx⟩
    exact ⟨C, fun n => by simpa [partialEnergy_inv] using hx n⟩


theorem continuous_circleEnergy : Continuous circleEnergy := by
  unfold circleEnergy
  fun_prop

theorem continuous_partialEnergy {G : Type*} [Group G] [TopologicalSpace G]
    (χ : ℕ → G →* Circle) (w : ℕ → ℝ) (hχ : ∀ i, Continuous (χ i)) (n : ℕ) :
    Continuous (fun x => partialEnergy χ w x n) := by
  unfold partialEnergy
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_circleEnergy.comp (hχ i))

theorem measurableSet_finiteEnergySubgroup
    {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (χ : ℕ → G →* Circle) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hχ : ∀ i, Continuous (χ i)) :
    MeasurableSet (finiteEnergySubgroup χ w hw : Set G) := by
  have heq : (finiteEnergySubgroup χ w hw : Set G) =
      ⋃ k : ℕ, ⋂ n : ℕ, {x : G | partialEnergy χ w x n ≤ (k : ℝ)} := by
    ext x
    constructor
    · rintro ⟨C, hC⟩
      obtain ⟨k, hk⟩ := exists_nat_ge C
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iInter.mpr (fun n => (hC n).trans hk)⟩
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      refine ⟨k, ?_⟩
      intro n
      have hn : x ∈ {x : G | partialEnergy χ w x n ≤ (k : ℝ)} :=
        Set.mem_iInter.mp hk n
      exact hn
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iInter
  intro n
  exact (isClosed_le (continuous_partialEnergy χ w hχ n) continuous_const).measurableSet


def dualEvaluation {G : Type*} [CommGroup G] [TopologicalSpace G]
    (g : G) : PontryaginDual G →* Circle where
  toFun χ := χ g
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_dualEvaluation {G : Type*} [CommGroup G] [TopologicalSpace G]
    (g : G) : Continuous (dualEvaluation g) := by
  change Continuous (fun χ : G →ₜ* Circle => χ g)
  exact continuous_eval_const g

theorem measurableSet_dualFiniteEnergy
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (g : ℕ → G) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    MeasurableSet
      (finiteEnergySubgroup (fun i => dualEvaluation (g i)) w hw :
        Set (PontryaginDual G)) :=
  measurableSet_finiteEnergySubgroup _ w hw (fun i => continuous_dualEvaluation (g i))


open MeasureTheory MeasureTheory.Measure Topology in
open scoped Pointwise in
theorem subgroup_isOpen_of_haar_pos
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ]
    (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (hpos : 0 < μ (H : Set G)) :
    IsOpen (H : Set G) := by
  have hn := div_mem_nhds_one_of_haar_pos μ (H : Set G) hH hpos
  have hsub : (H : Set G) / (H : Set G) ⊆ (H : Set G) := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact H.div_mem hx hy
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset hn hsub)


end
end Erdos786Audit

end

section
/- Source module: CompactBound.lean -/

/- A verification component of the E786 candidate, not a proof of E786.
   It checks the compact-group boundedness step used for the Fourier energy. -/

open Set

namespace Erdos786Audit

theorem compact_energy_bounded
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (S : G → ℝ)
    (hpos : ∀ x, 0 ≤ S x)
    (hinv : ∀ x, S x⁻¹ = S x)
    (hmul : ∀ x y, S (x * y) ≤ 2 * S x + 2 * S y)
    (hclosed : ∀ n : ℕ, IsClosed {x : G | S x ≤ (n : ℝ)}) :
    ∃ C : ℝ, ∀ x, S x ≤ C := by
  classical
  have hcover : (⋃ n : ℕ, {x : G | S x ≤ (n : ℝ)}) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge (S x)
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨n, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let U : G → Set G := fun g =>
    (fun x : G => g⁻¹ * x * a) ⁻¹' interior {x : G | S x ≤ (n : ℝ)}
  have huopen : ∀ g, IsOpen (U g) := by
    intro g
    exact isOpen_interior.preimage (by fun_prop)
  have hucover : (univ : Set G) ⊆ ⋃ g, U g := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x, ?_⟩
    simpa [U] using ha
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U huopen hucover
  refine ⟨2 * (∑ g ∈ t, S g) + 4 * (n : ℝ) + 4 * S a, ?_⟩
  intro x
  obtain ⟨g, hg, hx⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hx' : g⁻¹ * x * a ∈ interior {z : G | S z ≤ (n : ℝ)} := hx
  have hy : S (g⁻¹ * x * a) ≤ (n : ℝ) :=
    (interior_subset : interior {z : G | S z ≤ (n : ℝ)} ⊆
      {z : G | S z ≤ (n : ℝ)}) hx'
  have hdecomp : g * ((g⁻¹ * x * a) * a⁻¹) = x := by group
  have hfirst := hmul g ((g⁻¹ * x * a) * a⁻¹)
  have hsecond := hmul (g⁻¹ * x * a) a⁻¹
  rw [hdecomp] at hfirst
  rw [hinv] at hsecond
  have hsum : S g ≤ ∑ j ∈ t, S j :=
    Finset.single_le_sum (fun j _ => hpos j) hg
  linarith


/- Finite partial sums avoid defining an infinite real sum before proving
   summability. This is the version needed for the character-energy series. -/
theorem compact_energy_family_bounded
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (S : G → ℕ → ℝ)
    (hpos : ∀ x m, 0 ≤ S x m)
    (hinv : ∀ x m, S x⁻¹ m = S x m)
    (hmul : ∀ x y m, S (x * y) m ≤ 2 * S x m + 2 * S y m)
    (hclosed : ∀ m n : ℕ, IsClosed {x : G | S x m ≤ (n : ℝ)})
    (hpoint : ∀ x, ∃ C : ℝ, ∀ m, S x m ≤ C) :
    ∃ C : ℝ, ∀ x m, S x m ≤ C := by
  classical
  let E : ℕ → Set G := fun n => {x | ∀ m, S x m ≤ (n : ℝ)}
  have heclosed : ∀ n, IsClosed (E n) := by
    intro n
    have heq : E n = ⋂ m : ℕ, {x : G | S x m ≤ (n : ℝ)} := by
      ext x
      simp [E]
    rw [heq]
    exact isClosed_iInter (fun m => hclosed m n)
  have hecover : (⋃ n : ℕ, E n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨C, hC⟩ := hpoint x
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact mem_iUnion.mpr ⟨n, fun m => (hC m).trans hn⟩
  obtain ⟨n, a, ha⟩ := nonempty_interior_of_iUnion_of_closed heclosed hecover
  have haE : a ∈ E n := interior_subset ha
  let U : G → Set G := fun g =>
    (fun x : G => g⁻¹ * x * a) ⁻¹' interior (E n)
  have huopen : ∀ g, IsOpen (U g) := by
    intro g
    exact isOpen_interior.preimage (by fun_prop)
  have hucover : (univ : Set G) ⊆ ⋃ g, U g := by
    intro x _
    exact mem_iUnion.mpr ⟨x, by simpa [U] using ha⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U huopen hucover
  choose B hB using hpoint
  have hBpos : ∀ g, 0 ≤ B g := fun g => (hpos g 0).trans (hB g 0)
  refine ⟨2 * (∑ g ∈ t, B g) + 8 * (n : ℝ), ?_⟩
  intro x m
  obtain ⟨g, hg, hx⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hx' : g⁻¹ * x * a ∈ interior (E n) := hx
  have hyE : g⁻¹ * x * a ∈ E n := interior_subset hx'
  have hy : S (g⁻¹ * x * a) m ≤ (n : ℝ) := hyE m
  have ha' : S a m ≤ (n : ℝ) := haE m
  have hdecomp : g * ((g⁻¹ * x * a) * a⁻¹) = x := by group
  have hfirst := hmul g ((g⁻¹ * x * a) * a⁻¹) m
  have hsecond := hmul (g⁻¹ * x * a) a⁻¹ m
  rw [hdecomp] at hfirst
  rw [hinv] at hsecond
  have hsum : B g ≤ ∑ j ∈ t, B j :=
    Finset.single_le_sum (fun j _ => hBpos j) hg
  have hgB := hB g m
  linarith


open MeasureTheory in
theorem summable_integrals_of_bounded_partial_sums
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : ℕ → X → ℝ)
    (hE : ∀ i, Integrable (E i) μ)
    (hpos : ∀ i, 0 ≤ ∫ x, E i x ∂μ)
    (C : ℝ)
    (hbound : ∀ x n, (∑ i ∈ Finset.range n, E i x) ≤ C) :
    Summable (fun i => ∫ x, E i x ∂μ) := by
  apply summable_of_sum_range_le hpos
  intro n
  rw [← integral_finsetSum (Finset.range n) (fun i _ => hE i)]
  have hi : Integrable (fun x => ∑ i ∈ Finset.range n, E i x) μ :=
    integrable_finsetSum (Finset.range n) (fun i _ => hE i)
  have hle := integral_mono hi (integrable_const C) (fun x => hbound x n)
  simpa using hle


end Erdos786Audit

end

section
/- Source module: GeometricLaws.lean -/

namespace Erdos786Audit

theorem pmf_real_weights_sum_one {α : Type*} (p : PMF α) :
    (∑' a, (p a).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

theorem pmf_real_weights_summable {α : Type*} (p : PMF α) :
    Summable (fun a => (p a).toReal) := ENNReal.summable_toReal p.tsum_coe_ne_top

open MeasureTheory in
theorem character_series_eq_pmf_integral
    {G : Type*} [Monoid G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSingletonClass G] (p : PMF G) (χ : PontryaginDual G) :
    weightedCharacterSeries (fun g => (p g).toReal) χ = ∫ g, (χ g : ℂ) ∂p.toMeasure := by
  have hcirc : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have hc : Continuous (fun g => (χ g : ℂ)) := hcirc.comp χ.continuous
  have hi : Integrable (fun g => (χ g : ℂ)) p.toMeasure :=
    Integrable.of_bound hc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun g => (χ g).norm_coe.le))
  rw [PMF.integral_eq_tsum _ _ hi]
  simp only [weightedCharacterSeries, Complex.real_smul]

open MeasureTheory in
theorem character_series_of_pmf_map
    {α G : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Monoid G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSingletonClass G]
    (p : PMF α) (f : α → G) (hf : Measurable f) (χ : PontryaginDual G) :
    weightedCharacterSeries (fun g => (p.map f g).toReal) χ =
      ∑' a, (p a).toReal * (χ (f a) : ℂ) := by
  have hcirc : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have hc : Continuous (fun g => (χ g : ℂ)) := hcirc.comp χ.continuous
  have hi : Integrable (fun g => (χ g : ℂ)) (p.map f).toMeasure :=
    Integrable.of_bound hc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun g => (χ g).norm_coe.le))
  have hif : Integrable (fun a => (χ (f a) : ℂ)) p.toMeasure :=
    Integrable.of_bound (hc.measurable.comp hf).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun a => (χ (f a)).norm_coe.le))
  calc
    _ = ∫ g, (χ g : ℂ) ∂(p.map f).toMeasure := by
      rw [PMF.integral_eq_tsum _ _ hi]
      simp only [weightedCharacterSeries, Complex.real_smul]
    _ = ∫ a, (χ (f a) : ℂ) ∂p.toMeasure := by
      rw [← PMF.toMeasure_map f p hf]
      exact integral_map hf.aemeasurable hc.aestronglyMeasurable
    _ = ∑' a, (p a).toReal * (χ (f a) : ℂ) := by
      rw [PMF.integral_eq_tsum _ _ hif]
      simp only [Complex.real_smul]

open MeasureTheory ProbabilityTheory in
noncomputable def geometricLaw (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) : PMF ℕ :=
  (geometricMeasure (⟨1-q, by constructor <;> linarith⟩ : unitInterval)).toPMF

open MeasureTheory ProbabilityTheory in
theorem geometricLaw_real_weight (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    (geometricLaw q hq hq1 j).toReal = (1-q)*q^j := by
  let p : unitInterval := ⟨1-q, by constructor <;> linarith⟩
  have hp : p ≠ 0 := by
    intro he
    have he' := congrArg Subtype.val he
    change 1-q = 0 at he'
    linarith
  change ((geometricMeasure p).toPMF j).toReal = _
  rw [Measure.toPMF_apply, geometricMeasure_singleton hp,
    ENNReal.toReal_ofReal (geometricMeasure_nonneg p j)]
  dsimp [p]
  rw [sub_sub_cancel, mul_comm]


open MeasureTheory in
noncomputable def independentMultiplicationLaw
    {G : Type*} [Monoid G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (p r : PMF G) : PMF G :=
  ((p.toMeasure.prod r.toMeasure).toPMF).map (fun z : G × G => z.1*z.2)

open MeasureTheory in
theorem character_series_independentMultiplicationLaw
    {G : Type*} [Monoid G] [Countable G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G] [MeasurableMul G]
    (p r : PMF G) (χ : PontryaginDual G) :
    weightedCharacterSeries (fun g => (independentMultiplicationLaw p r g).toReal) χ =
      weightedCharacterSeries (fun g => (p g).toReal) χ *
        weightedCharacterSeries (fun g => (r g).toReal) χ := by
  have hcirc : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop
  have hc : Continuous (fun g => (χ g : ℂ)) := hcirc.comp χ.continuous
  rw [character_series_eq_pmf_integral]
  unfold independentMultiplicationLaw
  rw [← PMF.toMeasure_map (fun z : G × G => z.1*z.2) _ measurable_mul]
  rw [integral_map measurable_mul.aemeasurable hc.aestronglyMeasurable,
    Measure.toPMF_toMeasure]
  simp_rw [map_mul, Circle.coe_mul]
  rw [character_series_eq_pmf_integral p χ, character_series_eq_pmf_integral r χ]
  exact integral_prod_mul (μ := p.toMeasure) (ν := r.toMeasure)
    (fun x => (χ x : ℂ)) (fun x => (χ x : ℂ))

open MeasureTheory in
theorem character_series_geometric_power
    {G : Type*} [Monoid G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (g : G) (χ : PontryaginDual G) :
    weightedCharacterSeries
      (fun a => ((geometricLaw q hq hq1).map (fun j => g^j) a).toReal) χ =
      ((1-q : ℝ) : ℂ) / (1-(q : ℂ)*(χ g : ℂ)) := by
  rw [character_series_of_pmf_map _ _ (measurable_of_countable _) χ]
  simp only [geometricLaw_real_weight, map_pow, Circle.coe_pow,
    Complex.ofReal_mul, Complex.ofReal_pow]
  exact (geometric_character_hasSum q hq hq1 (χ g)).tsum_eq


noncomputable def finiteGeometricLaw
    {G : Type*} [Monoid G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (g : ℕ → G) (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) : ℕ → PMF G
  | 0 => PMF.pure 1
  | n+1 => independentMultiplicationLaw (finiteGeometricLaw g q hq hq1 n)
      ((geometricLaw (q n) (hq n) (hq1 n)).map (fun j => (g n)^j))

open MeasureTheory in
theorem finiteGeometricLaw_characterSeries
    {G : Type*} [Monoid G] [Countable G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G] [MeasurableMul G]
    (g : ℕ → G) (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (n : ℕ) (χ : PontryaginDual G) :
    weightedCharacterSeries (fun a => (finiteGeometricLaw g q hq hq1 n a).toReal) χ =
      ∏ i ∈ Finset.range n, ((1-q i : ℝ) : ℂ) / (1-(q i : ℂ)*(χ (g i) : ℂ)) := by
  induction n with
  | zero =>
    simp only [finiteGeometricLaw, Finset.range_zero, Finset.prod_empty]
    rw [character_series_eq_pmf_integral, PMF.toMeasure_pure]
    simp
  | succ n ih =>
    rw [finiteGeometricLaw, character_series_independentMultiplicationLaw,
      ih, character_series_geometric_power, Finset.prod_range_succ]

theorem finiteGeometricLaw_fourier_energy
    {G : Type*} [Monoid G] [Countable G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSingletonClass G] [MeasurableMul G]
    (g : ℕ → G) (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (n : ℕ) (χ : PontryaginDual G) :
    ‖weightedCharacterSeries (fun a => (finiteGeometricLaw g q hq hq1 n a).toReal) χ‖^2 =
      geometricFourierProduct q (fun i => χ (g i)) n := by
  rw [finiteGeometricLaw_characterSeries, Complex.sq_norm]
  exact map_prod Complex.normSq _ _


end Erdos786Audit

end

section
/- Source module: AnalyticAssembly.lean -/

namespace Erdos786Audit

theorem secondCountable_dual_of_countable_discrete
    {G : Type*} [Monoid G] [TopologicalSpace G] [DiscreteTopology G] [Countable G] :
    SecondCountableTopology (PontryaginDual G) := by
  change SecondCountableTopology (G →ₜ* Circle)
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).secondCountableTopology

theorem actual_product_lower_bounds_energy
    (q : ℕ → ℝ) (z : ℕ → Circle)
    (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (c : ℝ) (hc : 0 < c)
    (hprod : ∀ n, c ≤ geometricFourierProduct q z n) :
    ∀ n, (∑ i ∈ Finset.range n, q i * circleEnergy (z i)) ≤ -9 * Real.log c := by
  have hrew : ∀ n, geometricFourierProduct q z n =
      ∏ i ∈ Finset.range n, (1 + 2*q i*(1-(z i : ℂ).re)/(1-q i)^2)⁻¹ := by
    intro n
    unfold geometricFourierProduct
    apply Finset.prod_congr rfl
    intro i _
    exact geometric_character_normSq (q i) (by linarith [hqhalf i]) (z i)
  have hb := energy_bounded_of_product_lower q (fun i => 1-(z i : ℂ).re)
    hq hqhalf (fun i => (circle_real_defect_bounds (z i)).1)
    (fun i => (circle_real_defect_bounds (z i)).2) c hc
    (fun n => by simpa only [hrew n] using hprod n)
  intro n
  have he : (∑ i ∈ Finset.range n, q i * circleEnergy (z i)) =
      2 * (∑ i ∈ Finset.range n, q i * (1-(z i : ℂ).re)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [circleEnergy_eq]
    ring
  rw [he]
  linarith [hb n]

open MeasureTheory in
theorem finite_energy_positive_of_actual_product_integrals
    {X : Type*} [Group X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (χ : ℕ → X →* Circle) (hχ : ∀ i, Continuous (χ i))
    (q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (d : ℝ) (hd : 0 < d)
    (hint : ∀ n, d ≤ ∫ x, geometricFourierProduct q (fun i => χ i x) n ∂μ) :
    0 < μ (finiteEnergySubgroup χ q (fun i => (hq i).le) : Set X) := by
  let F : ℕ → X → ℝ := fun n x => geometricFourierProduct q (fun i => χ i x) n
  have hq1 : ∀ i, q i < 1 := fun i => by linarith [hqhalf i]
  have hFc : ∀ n, Continuous (F n) := fun n =>
    continuous_geometricFourierProduct q (fun i x => χ i x) (fun i => (hq i).le) hq1 hχ n
  have hFi : ∀ n, Integrable (F n) μ := by
    intro n
    apply Integrable.of_bound (hFc n).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (geometricFourierProduct_pos q _ (fun i => (hq i).le) hq1 n)]
    exact geometricFourierProduct_le_one q _ (fun i => (hq i).le) hq1 n
  have hp := positive_uniform_superlevel_of_integral_lower μ F hFi
    (fun n => (hFc n).measurable)
    (fun n x => geometricFourierProduct_le_one q _ (fun i => (hq i).le) hq1 n)
    (fun x => geometricFourierProduct_antitone q _ (fun i => (hq i).le) hq1) d hd hint
  apply lt_of_lt_of_le hp
  apply measure_mono
  intro x hx
  refine ⟨-9 * Real.log (d/2), ?_⟩
  exact actual_product_lower_bounds_energy q (fun i => χ i x) hq hqhalf
    (d/2) (by linarith) hx


open MeasureTheory MeasureTheory.Measure in
theorem open_subgroup_uniform_energy_of_actual_product_integrals
    {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [IsHaarMeasure μ] [InnerRegular μ]
    (χ : ℕ → X →* Circle) (hχ : ∀ i, Continuous (χ i))
    (q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (d : ℝ) (hd : 0 < d)
    (hint : ∀ n, d ≤ ∫ x, geometricFourierProduct q (fun i => χ i x) n ∂μ) :
    ∃ L : Subgroup X, IsOpen (L : Set X) ∧
      ∃ C : ℝ, ∀ x : L, ∀ n, partialEnergy χ q x.val n ≤ C := by
  let L := finiteEnergySubgroup χ q (fun i => (hq i).le)
  have hm : MeasurableSet (L : Set X) :=
    measurableSet_finiteEnergySubgroup χ q (fun i => (hq i).le) hχ
  have hp : 0 < μ (L : Set X) :=
    finite_energy_positive_of_actual_product_integrals μ χ hχ q hq hqhalf d hd hint
  have ho : IsOpen (L : Set X) := subgroup_isOpen_of_haar_pos μ L hm hp
  refine ⟨L, ho, ?_⟩
  let : CompactSpace L := isCompact_iff_compactSpace.mp (L.isClosed_of_isOpen ho).isCompact
  apply compact_energy_family_bounded (fun x : L => partialEnergy χ q x.val)
  · intro x n
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hq i).le (circleEnergy_nonneg _))
  · intro x n
    exact partialEnergy_inv χ q x.val n
  · intro x y n
    exact partialEnergy_mul χ q (fun i => (hq i).le) x.val y.val n
  · intro m n
    exact isClosed_le ((continuous_partialEnergy χ q hχ m).comp continuous_subtype_val)
      continuous_const
  · intro x
    exact x.property


open MeasureTheory MeasureTheory.Measure Classical TopologicalSpace in
theorem finite_exceptions_of_actual_product_integrals
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    [Countable G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure (PontryaginDual G))
    [IsProbabilityMeasure μ] [IsHaarMeasure μ] [InnerRegular μ]
    (g : ℕ → G) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (d : ℝ) (hd : 0 < d)
    (hint : ∀ n, d ≤ ∫ χ, geometricFourierProduct q (fun i => χ (g i)) n ∂μ) :
    ∃ K : Subgroup G, Finite K ∧
      Summable (fun i => if g i ∈ K then 0 else q i) := by
  classical
  let : SecondCountableTopology (PontryaginDual G) := secondCountable_dual_of_countable_discrete
  obtain ⟨L, hL, C, hC⟩ := open_subgroup_uniform_energy_of_actual_product_integrals μ
    (fun i => dualEvaluation (g i)) (fun i => continuous_dualEvaluation (g i))
    q hq hqhalf d hd hint
  let : CompactSpace L := isCompact_iff_compactSpace.mp (L.isClosed_of_isOpen hL).isCompact
  let K₀ : PositiveCompacts L := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν : Measure L := haarMeasure K₀
  let : IsProbabilityMeasure ν := ⟨haarMeasure_self⟩
  apply finite_subgroup_with_summable_exceptions_of_open_energy_bound L hL ν g q
    (fun i => (hq i).le) C
  intro χ n
  calc
    _ ≤ partialEnergy (fun i => dualEvaluation (g i)) q χ.val n := by
      apply Finset.sum_le_sum
      intro i _
      change q i * (1-(χ.val (g i) : ℂ).re) ≤ q i * circleEnergy (χ.val (g i))
      rw [circleEnergy_eq]
      apply mul_le_mul_of_nonneg_left _ (hq i).le
      linarith [(circle_real_defect_bounds (χ.val (g i))).1]
    _ ≤ C := hC χ n


open MeasureTheory MeasureTheory.Measure TopologicalSpace in
theorem exists_probability_haar_on_compact_group
    {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ IsHaarMeasure μ ∧ InnerRegular μ := by
  let K₀ : PositiveCompacts X := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ : Measure X := haarMeasure K₀
  let : IsProbabilityMeasure μ := ⟨haarMeasure_self⟩
  exact ⟨μ, inferInstance, inferInstance, inferInstance⟩


open MeasureTheory MeasureTheory.Measure Classical in
theorem finite_exceptions_of_geometric_distributions
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure (PontryaginDual G))
    [IsProbabilityMeasure μ] [IsHaarMeasure μ] [InnerRegular μ]
    (g : ℕ → G) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (w : ℕ → G → ℝ) (hw : ∀ n a, 0 ≤ w n a)
    (hs : ∀ n, Summable (w n)) (h1 : ∀ n, ∑' a, w n a = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hnear : ∀ n, ∀ ε : ℝ, 0 < ε → ∃ a, δ-ε ≤ w n a)
    (hFourier : ∀ n χ, ‖weightedCharacterSeries (w n) χ‖^2 =
      geometricFourierProduct q (fun i => χ (g i)) n) :
    ∃ K : Subgroup G, Finite K ∧
      Summable (fun i => if g i ∈ K then 0 else q i) := by
  let : SecondCountableTopology (PontryaginDual G) := secondCountable_dual_of_countable_discrete
  apply finite_exceptions_of_actual_product_integrals μ g q hq hqhalf (δ^2) (sq_pos_of_pos hδ)
  intro n
  have he := approximate_atom_square_le_fourier_energy μ (w n) (hw n) (hs n) (h1 n)
    δ hδ.le (hnear n)
  simpa only [hFourier n] using he


open MeasureTheory MeasureTheory.Measure Classical in
theorem finite_exceptions_of_finite_geometric_law
    {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure (PontryaginDual G))
    [IsProbabilityMeasure μ] [IsHaarMeasure μ] [InnerRegular μ]
    (g : ℕ → G) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i) (hqhalf : ∀ i, q i ≤ 1/2)
    (δ : ℝ) (hδ : 0 < δ)
    (hnear : ∀ n, ∀ ε : ℝ, 0 < ε → ∃ a, δ-ε ≤
      (finiteGeometricLaw g q (fun i => (hq i).le)
        (fun i => lt_of_le_of_lt (hqhalf i) (by norm_num)) n a).toReal) :
    ∃ K : Subgroup G, Finite K ∧
      Summable (fun i => if g i ∈ K then 0 else q i) := by
  let hq1 : ∀ i, q i < 1 := fun i => lt_of_le_of_lt (hqhalf i) (by norm_num)
  let law := finiteGeometricLaw g q (fun i => (hq i).le) hq1
  exact finite_exceptions_of_geometric_distributions μ g q hq hqhalf
    (fun n a => (law n a).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun n => pmf_real_weights_summable (law n))
    (fun n => pmf_real_weights_sum_one (law n)) δ hδ hnear
    (fun n χ => finiteGeometricLaw_fourier_energy g q (fun i => (hq i).le) hq1 n χ)


end Erdos786Audit

end

section
/- Source module: PrimeAnalyticBridge.lean -/

/-! Prime-indexed Fourier identity for the actual smooth quotient law. -/
namespace Erdos786Audit

theorem actual_smooth_fourier_energy
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    [TopologicalSpace (Multiplicative (FreshIntegerQuotient A hA))]
    (p : ℕ → ℕ) (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (n : ℕ) (χ : PontryaginDual (Multiplicative (FreshIntegerQuotient A hA))) :
    ‖weightedCharacterSeries
      (smoothClassWeight A hA ((Finset.range n).image p)) χ‖ ^ 2 =
      geometricFourierProduct (fun i => (1 : ℝ) / p i)
        (fun i => χ (Multiplicative.ofAdd (integerClass A hA (p i)))) n := by
  classical
  have hP : ∀ r ∈ (Finset.range n).image p, r.Prime := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hprime i
  have hf := (smoothClassWeight_character_hasSum A hA
    ((Finset.range n).image p) hP χ.toMonoidHom).tsum_eq
  change weightedCharacterSeries _ χ = _ at hf
  rw [hf, Complex.sq_norm, map_prod Complex.normSq]
  rw [Finset.prod_image (fun i _ j _ hij => hp hij)]
  unfold geometricFourierProduct
  apply Finset.prod_congr rfl
  intro i _
  simp
  rfl

open Filter MeasureTheory MeasureTheory.Measure Classical in
theorem actual_integer_quotient_finite_exceptions
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (hA : Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (nhds δ))
    (p : ℕ → ℕ) (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime) :
    ∃ K : Subgroup (Multiplicative (FreshIntegerQuotient A hpositive)), Finite K ∧
      Summable (fun i => if Multiplicative.ofAdd (integerClass A hpositive (p i)) ∈ K
        then 0 else (1 : ℝ) / p i) := by
  let G := Multiplicative (FreshIntegerQuotient A hpositive)
  let : Countable ℚˣ := Units.val_injective.countable
  let : Countable (Additive ℚˣ) := Additive.toMul.injective.countable
  let : Countable (FreshIntegerQuotient A hpositive) := by
    unfold FreshIntegerQuotient
    exact QuotientAddGroup.mk_surjective.countable
  let : Countable G := by
    exact Multiplicative.toAdd.injective.countable
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : SecondCountableTopology (PontryaginDual G) :=
    secondCountable_dual_of_countable_discrete
  obtain ⟨μ, hprob, hhaar, hregular⟩ :=
    exists_probability_haar_on_compact_group (X := PontryaginDual G)
  let : IsProbabilityMeasure μ := hprob
  let : IsHaarMeasure μ := hhaar
  let : InnerRegular μ := hregular
  have hP : ∀ n, ∀ r ∈ (Finset.range n).image p, r.Prime := by
    intro n r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hprime i
  apply finite_exceptions_of_geometric_distributions μ
    (fun i => Multiplicative.ofAdd (integerClass A hpositive (p i)))
    (fun i => (1 : ℝ) / p i)
    (fun i => one_div_pos.mpr (by exact_mod_cast (hprime i).pos))
    (fun i => one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hprime i).two_le))
    (fun n => smoothClassWeight A hpositive ((Finset.range n).image p))
    (fun n c => smoothClassWeight_nonneg A hpositive _ (hP n) c)
    (fun n => (smoothClassWeight_hasSum_one A hpositive _ (hP n)).summable)
    (fun n => (smoothClassWeight_hasSum_one A hpositive _ (hP n)).tsum_eq)
    δ hδ
    (fun n ε hε => actual_smooth_class_approximate_atom A hpositive δ hA _ (hP n) ε hε)
    (fun n χ => actual_smooth_fourier_energy A hpositive p hp hprime n χ)


noncomputable def primeEnumeration : ℕ ≃ {p : ℕ // p.Prime} :=
  Equiv.ofBijective
    (fun i => ⟨Nat.nth Nat.Prime i,
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i⟩)
    ⟨fun i j h => Nat.nth_injective Nat.infinite_setOfPred_prime
      (congrArg Subtype.val h), by
      intro p
      obtain ⟨i, hi⟩ := Nat.subset_range_nth p.property
      exact ⟨i, Subtype.ext hi⟩⟩

open Filter Classical in
theorem actual_integer_quotient_summable_bad_primes
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (hA : Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (nhds δ)) :
    ∃ K : Subgroup (Multiplicative (FreshIntegerQuotient A hpositive)), Finite K ∧
      Summable (fun p : {p : ℕ // p.Prime} =>
        if Multiplicative.ofAdd (integerClass A hpositive p) ∈ K
        then 0 else (1 : ℝ) / (p : ℕ)) := by
  obtain ⟨K, hK, hs⟩ := actual_integer_quotient_finite_exceptions A hpositive δ hδ hA
    (fun i => (primeEnumeration i : ℕ))
    (fun i j h => primeEnumeration.injective (Subtype.ext h))
    (fun i => (primeEnumeration i).property)
  refine ⟨K, hK, ?_⟩
  exact primeEnumeration.summable_iff.mp hs


end Erdos786Audit

end

section
/- Source module: QuotientRemoval.lean -/

/-! Finite-fibre removal in the quotient supplied by the arithmetic/analytic bridge. -/
namespace Erdos786Audit

abbrev ReducedIntegerQuotient (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (K : Subgroup (Multiplicative (FreshIntegerQuotient A hA))) :=
  FreshIntegerQuotient A hA ⧸ K.toAddSubgroup'

noncomputable def reducedIntegerClass (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (K : Subgroup (Multiplicative (FreshIntegerQuotient A hA))) (n : ℕ) :
    ReducedIntegerQuotient A hA K :=
  QuotientAddGroup.mk' K.toAddSubgroup' (integerClass A hA n)

open Filter Classical in
theorem reduced_integer_finite_fibres_density_zero
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (K : Subgroup (Multiplicative (FreshIntegerQuotient A hA)))
    (hs : Summable (fun p : {p : ℕ // p.Prime} =>
      if Multiplicative.ofAdd (integerClass A hA p) ∈ K then 0 else (1 : ℝ) / (p : ℕ))) :
    Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A ∧
        Set.Finite {m | m ∈ A ∧ reducedIntegerClass A hA K m =
          reducedIntegerClass A hA K n})).card : ℝ) / N) atTop (nhds 0) := by
  let D := {p : ℕ | p.Prime ∧ Multiplicative.ofAdd (integerClass A hA p) ∉ K}
  have hsD : Summable (fun p : D => (1 : ℝ) / (p : ℕ)) := by
    apply summable_prime_indicator_to_set D (fun p hp => hp.1)
    apply hs.congr
    intro p
    simp only [D, Set.mem_ofPred_eq, p.property, true_and, ite_not]
  apply finite_fibre_density_zero_of_summable_prime_support A
    (reducedIntegerClass A hA K) _ _ D (fun p hp => hp.1) _ hsD
  · simp only [reducedIntegerClass, integerClass_one, map_zero]
  · intro m n hm hn
    simp only [reducedIntegerClass, integerClass_mul_nonzero A hA m n hm hn, map_add]
  · intro p hp hne
    refine ⟨hp, ?_⟩
    intro hmem
    apply hne
    have hk : integerClass A hA p ∈ (QuotientAddGroup.mk' K.toAddSubgroup').ker := by
      rw [QuotientAddGroup.ker_mk']
      exact hmem
    exact hk

open Filter Classical in
theorem actual_integer_quotient_density_zero_removal
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (hA : Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (nhds δ)) :
    ∃ K : Subgroup (Multiplicative (FreshIntegerQuotient A hpositive)), Finite K ∧
      Summable (fun p : {p : ℕ // p.Prime} =>
        if Multiplicative.ofAdd (integerClass A hpositive p) ∈ K then 0 else (1 : ℝ) / (p : ℕ)) ∧
      Tendsto (fun N =>
        (((Finset.Icc 1 N).filter (fun n => n ∈ A ∧
          Set.Finite {m | m ∈ A ∧ reducedIntegerClass A hpositive K m =
            reducedIntegerClass A hpositive K n})).card : ℝ) / N) atTop (nhds 0) := by
  obtain ⟨K, hK, hs⟩ := actual_integer_quotient_summable_bad_primes A hpositive δ hδ hA
  exact ⟨K, hK, hs, reduced_integer_finite_fibres_density_zero A hpositive K hs⟩


end Erdos786Audit

end

section
/- Source module: InfiniteFibres.lean -/

namespace Erdos786Audit

/-- Repetitions in a list of group classes can be represented by distinct objects,
provided every listed class has an infinite fibre. -/
theorem realize_list_in_infinite_fibres {α G : Type*} [AddCommMonoid G]
    (g : α → G) (l : List G)
    (hinf : ∀ h ∈ l, Set.Infinite {a | g a = h}) :
    ∃ s : Finset α, s.card = l.length ∧ (∑ a ∈ s, g a) = l.sum := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons h l ih =>
    obtain ⟨s, hcard, hsum⟩ := ih (fun t ht => hinf t (by simp [ht]))
    obtain ⟨a, ha, has⟩ := (hinf h (by simp)).exists_notMem_finset s
    change g a = h at ha
    refine ⟨insert a s, ?_, ?_⟩
    · simp [Finset.card_insert_of_notMem has, hcard]
    · simp [Finset.sum_insert has, ha, hsum]

/-- A distinct-object equal-sum/equal-length law becomes a repeated-class law on
classes with infinite fibres. No multiplicities are assumed in the hypothesis. -/
theorem infinite_fibre_lists_equal_length {α G : Type*} [AddCommMonoid G]
    (g : α → G)
    (hlength : ∀ s t : Finset α,
      (∑ a ∈ s, g a) = (∑ a ∈ t, g a) → s.card = t.card)
    (u v : List G)
    (hu : ∀ h ∈ u, Set.Infinite {a | g a = h})
    (hv : ∀ h ∈ v, Set.Infinite {a | g a = h})
    (heq : u.sum = v.sum) : u.length = v.length := by
  obtain ⟨s, hsc, hss⟩ := realize_list_in_infinite_fibres g u hu
  obtain ⟨t, htc, hts⟩ := realize_list_in_infinite_fibres g v hv
  have h := hlength s t (hss.trans (heq.trans hts.symm))
  exact hsc.symm.trans (h.trans htc)


private theorem repeat_list_sum {G : Type*} [AddCommMonoid G] (l : List G) (k : ℕ) :
    ((List.replicate k l).flatten).sum = k • l.sum := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, succ_nsmul, add_comm]

private theorem repeat_list_length {G : Type*} (l : List G) (k : ℕ) :
    ((List.replicate k l).flatten).length = k * l.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- Even a torsion difference between the two list sums forces equal lengths.
This is the finite-kernel step, before specializing the multiplier to |K|. -/
theorem infinite_fibre_lists_equal_length_of_nsmul {α G : Type*} [AddCommMonoid G]
    (g : α → G)
    (hlength : ∀ s t : Finset α,
      (∑ a ∈ s, g a) = (∑ a ∈ t, g a) → s.card = t.card)
    (u v : List G)
    (hu : ∀ h ∈ u, Set.Infinite {a | g a = h})
    (hv : ∀ h ∈ v, Set.Infinite {a | g a = h})
    (k : ℕ) (hk : 0 < k) (heq : k • u.sum = k • v.sum) :
    u.length = v.length := by
  have hr (l : List G) (hl : ∀ h ∈ l, Set.Infinite {a | g a = h}) :
      ∀ h ∈ (List.replicate k l).flatten, Set.Infinite {a | g a = h} := by
    intro h hh
    obtain ⟨l', hl', hh'⟩ := List.mem_flatten.mp hh
    have he : l' = l := List.eq_of_mem_replicate hl'
    exact hl h (he ▸ hh')
  have h := infinite_fibre_lists_equal_length g hlength
    ((List.replicate k u).flatten) ((List.replicate k v).flatten)
    (hr u hu) (hr v hv) (by simpa only [repeat_list_sum] using heq)
  simp only [repeat_list_length] at h
  exact Nat.eq_of_mul_eq_mul_left hk h


/-- Passing through a homomorphism with finite kernel does not lose the
equal-length law for lists of infinite-fibre classes. -/
theorem infinite_fibre_lists_equal_length_mod_finite_kernel
    {α G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (g : α → G)
    (hlength : ∀ s t : Finset α,
      (∑ a ∈ s, g a) = (∑ a ∈ t, g a) → s.card = t.card)
    (q : G →+ Q) [Finite q.ker] (u v : List G)
    (hu : ∀ h ∈ u, Set.Infinite {a | g a = h})
    (hv : ∀ h ∈ v, Set.Infinite {a | g a = h})
    (heq : q u.sum = q v.sum) : u.length = v.length := by
  have hmem : u.sum - v.sum ∈ q.ker := by
    change q (u.sum - v.sum) = 0
    rw [map_sub, heq, sub_self]
  have hz : Nat.card q.ker • (u.sum - v.sum) = 0 := by
    have ht : Nat.card q.ker • (⟨u.sum - v.sum, hmem⟩ : q.ker) = 0 :=
      card_nsmul_eq_zero'
    exact congrArg (fun x : q.ker => (x : G)) ht
  have he : Nat.card q.ker • u.sum = Nat.card q.ker • v.sum := by
    exact sub_eq_zero.mp (by simpa only [nsmul_sub] using hz)
  exact infinite_fibre_lists_equal_length_of_nsmul g hlength u v hu hv
    (Nat.card q.ker) Nat.card_pos he


/-- Every free abelian word is a difference of two positive lists. -/
theorem freeAbelian_list_difference {C : Type*} (x : FreeAbelianGroup C) :
    ∃ u v : List C,
      x = (u.map FreeAbelianGroup.of).sum - (v.map FreeAbelianGroup.of).sum := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => exact ⟨[], [], by simp⟩
  | of c => exact ⟨[c], [], by simp⟩
  | neg c _ => exact ⟨[], [c], by simp⟩
  | add x y hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u ++ u', v ++ v', ?_⟩
    simp only [List.map_append, List.sum_append]
    abel

/-- The equal-sum/equal-length law implies that assigning degree 1 to each
generator respects every integer relation. -/
theorem degree_kernel_inclusion {C G : Type*} [AddCommGroup G]
    (c : C → G)
    (hlength : ∀ u v : List C,
      (u.map c).sum = (v.map c).sum → u.length = v.length) :
    (FreeAbelianGroup.lift c).ker ≤
      (FreeAbelianGroup.lift (fun _ : C => (1 : ℚ))).ker := by
  intro x hx
  obtain ⟨u, v, rfl⟩ := freeAbelian_list_difference x
  change FreeAbelianGroup.lift c
    ((u.map FreeAbelianGroup.of).sum - (v.map FreeAbelianGroup.of).sum) = 0 at hx
  simp only [map_sub, map_list_sum, List.map_map, Function.comp_def,
    FreeAbelianGroup.lift_apply_of] at hx
  have hlen := hlength u v (sub_eq_zero.mp hx)
  change FreeAbelianGroup.lift (fun _ : C => (1 : ℚ))
    ((u.map FreeAbelianGroup.of).sum - (v.map FreeAbelianGroup.of).sum) = 0
  simp [map_list_sum, List.map_map, Function.comp_def, hlen]


/-- A family whose repeated equal sums always have equal lengths lies in level 1
of a rational-valued additive homomorphism on the entire ambient group.
Divisibility of Q handles torsion without any torsion-free hypothesis on G. -/
theorem exists_rational_level_hom {C G : Type*} [AddCommGroup G]
    (c : C → G)
    (hlength : ∀ u v : List C,
      (u.map c).sum = (v.map c).sum → u.length = v.length) :
    ∃ f : G →+ ℚ, ∀ i, f (c i) = 1 := by
  let π : FreeAbelianGroup C →+ G := FreeAbelianGroup.lift c
  let d : FreeAbelianGroup C →+ ℚ := FreeAbelianGroup.lift (fun _ => 1)
  have hker : π.rangeRestrict.ker ≤ d.ker := by
    rw [AddMonoidHom.ker_rangeRestrict]
    exact degree_kernel_inclusion c hlength
  let d' : π.range →+ ℚ :=
    π.rangeRestrict.liftOfSurjective π.rangeRestrict_surjective ⟨d, hker⟩
  have hcomp : d'.comp π.rangeRestrict = d := by
    exact congrArg Subtype.val
      ((π.rangeRestrict.liftOfSurjective π.rangeRestrict_surjective).symm_apply_apply ⟨d, hker⟩)
  obtain ⟨f, hf⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
    π.range.subtype Subtype.val_injective d'
  refine ⟨f, ?_⟩
  intro i
  have h1 := DFunLike.congr_fun hf (π.rangeRestrict (FreeAbelianGroup.of i))
  have h2 := DFunLike.congr_fun hcomp (FreeAbelianGroup.of i)
  change f (π (FreeAbelianGroup.of i)) = d' (π.rangeRestrict (FreeAbelianGroup.of i)) at h1
  change d' (π.rangeRestrict (FreeAbelianGroup.of i)) = d (FreeAbelianGroup.of i) at h2
  simpa [π, d] using h1.trans h2


theorem finite_fibre_of_finite_kernel {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (q : G →+ Q) [Finite q.ker] (c : Q) : Set.Finite {h | q h = c} := by
  classical
  by_cases hn : ∃ h, q h = c
  · obtain ⟨h, hh⟩ := hn
    have hs := (Set.toFinite (Set.univ : Set q.ker)).image (fun k : q.ker => h + (k : G))
    apply hs.subset
    intro x hx
    have hk : x - h ∈ q.ker := by
      change q (x - h) = 0
      change q x = c at hx
      rw [map_sub, hx, hh, sub_self]
    exact ⟨⟨x - h, hk⟩, Set.mem_univ _, by simp⟩
  · have he : {h | q h = c} = ∅ := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hh => hn ⟨h, hh⟩
    rw [he]
    exact Set.finite_empty

theorem infinite_fibre_lifts_through_finite_kernel
    {α G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (g : α → G) (q : G →+ Q) [Finite q.ker] (c : Q)
    (hinf : Set.Infinite {a | q (g a) = c}) :
    ∃ h, q h = c ∧ Set.Infinite {a | g a = h} := by
  classical
  by_contra! hn
  have hs := finite_fibre_of_finite_kernel q c
  have ht : Set.Finite (⋃ h ∈ {h | q h = c}, {a | g a = h}) :=
    hs.biUnion (fun h hh => hn h hh)
  apply hinf
  apply ht.subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨g a, Set.mem_iUnion.mpr ⟨ha, rfl⟩⟩


/-- The arithmetic structural step of the candidate, assembled end-to-end:
every infinite fibre after a finite-kernel quotient lies on one rational
additive level, provided the original distinct-object length law holds. -/
theorem exists_rational_level_on_infinite_quotient_fibres
    {α G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (g : α → G)
    (hlength : ∀ s t : Finset α,
      (∑ a ∈ s, g a) = (∑ a ∈ t, g a) → s.card = t.card)
    (q : G →+ Q) [Finite q.ker] :
    ∃ f : Q →+ ℚ, ∀ c, Set.Infinite {a | q (g a) = c} → f c = 1 := by
  classical
  let C := {c : Q // Set.Infinite {a | q (g a) = c}}
  have hx : ∀ c : C, ∃ h, q h = c.val ∧ Set.Infinite {a | g a = h} :=
    fun c => infinite_fibre_lifts_through_finite_kernel g q c.val c.property
  choose h hq hi using hx
  have hlen : ∀ u v : List C,
      (u.map Subtype.val).sum = (v.map Subtype.val).sum → u.length = v.length := by
    intro u v heq
    have hu : ∀ x ∈ u.map h, Set.Infinite {a | g a = x} := by
      intro x hx
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      exact hi c
    have hv : ∀ x ∈ v.map h, Set.Infinite {a | g a = x} := by
      intro x hx
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
      exact hi c
    have he : q (u.map h).sum = q (v.map h).sum := by
      simpa only [map_list_sum, List.map_map, Function.comp_def, hq] using heq
    have hl := infinite_fibre_lists_equal_length_mod_finite_kernel
      g hlength q (u.map h) (v.map h) hu hv he
    simpa only [List.length_map] using hl
  obtain ⟨f, hf⟩ := exists_rational_level_hom (fun c : C => c.val) hlen
  exact ⟨f, fun c hc => hf ⟨c, hc⟩⟩


end Erdos786Audit

end

section
/- Source module: IntegerRationalLevel.lean -/

/-! Rational-level descent for the actual integer class map. -/
namespace Erdos786Audit

theorem integerClass_subtype_eq (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0) (a : A) :
    integerClass A hA a = integerQuotientMap A hA (integerLog A hA a) := by
  simp only [integerClass, dif_pos (hA a a.property)]
  rfl

theorem actual_integer_rational_level
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (hlength : ∀ U V : Finset A,
      (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card)
    {Q : Type*} [AddCommGroup Q]
    (q : FreshIntegerQuotient A hA →+ Q) [Finite q.ker] :
    ∃ f : Q →+ ℚ, ∀ c,
      Set.Infinite {a : A | q (integerClass A hA a) = c} → f c = 1 := by
  apply exists_rational_level_on_infinite_quotient_fibres
    (fun a : A => integerClass A hA a) _ q
  intro U V heq
  apply integer_quotient_length_law A hA hlength U V
  simpa only [integerClass_subtype_eq] using heq


theorem actual_integer_additive_level_on_infinite_fibres
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (hlength : ∀ U V : Finset A,
      (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card)
    {Q : Type*} [AddCommGroup Q]
    (q : FreshIntegerQuotient A hA →+ Q) [Finite q.ker] :
    ∃ f : ℕ → ℚ,
      (∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n) ∧
      (∀ n, Set.Infinite {m | m ∈ A ∧
        q (integerClass A hA m) = q (integerClass A hA n)} → f n = 1) := by
  obtain ⟨f, hf⟩ := actual_integer_rational_level A hA hlength q
  refine ⟨fun n => f (q (integerClass A hA n)), ?_, ?_⟩
  · intro m n hm hn
    dsimp only
    rw [integerClass_mul_nonzero A hA m n hm hn, map_add, map_add]
  · intro n hn
    apply hf
    have heq : Subtype.val '' {a : A |
        q (integerClass A hA a) = q (integerClass A hA n)} =
        {m | m ∈ A ∧ q (integerClass A hA m) = q (integerClass A hA n)} := by
      ext m
      simp [and_comm]
    exact Set.Infinite.of_image Subtype.val (heq.symm ▸ hn)


end Erdos786Audit

end

section
/- Source module: StructuralReduction.lean -/

/-! Structural reduction of the original distinct-product condition. -/
namespace Erdos786Audit

theorem finite_kernel_of_reduced_integer_quotient
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (K : Subgroup (Multiplicative (FreshIntegerQuotient A hA))) [Finite K] :
    Finite (QuotientAddGroup.mk' K.toAddSubgroup').ker := by
  have hfinite : Finite K.toAddSubgroup' := by
    let i : K.toAddSubgroup' → K := fun x => ⟨Multiplicative.ofAdd x.val, x.property⟩
    apply Finite.of_injective i
    intro x y h
    apply Subtype.ext
    exact Multiplicative.ofAdd.injective
      (congrArg (fun z : K => z.val) h)
  rw [QuotientAddGroup.ker_mk']
  exact hfinite

theorem reduced_integer_class_zero_of_mem
    (A : Set ℕ) (hA : ∀ n ∈ A, n ≠ 0)
    (K : Subgroup (Multiplicative (FreshIntegerQuotient A hA))) (n : ℕ)
    (hn : Multiplicative.ofAdd (integerClass A hA n) ∈ K) :
    reducedIntegerClass A hA K n = 0 := by
  have hk : integerClass A hA n ∈ (QuotientAddGroup.mk' K.toAddSubgroup').ker := by
    rw [QuotientAddGroup.ker_mk']
    exact hn
  exact hk

open Filter Classical in
theorem actual_distinct_product_structural_reduction
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (hdensity : Tendsto (fun N =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (nhds δ))
    (hlength : ∀ U V : Finset A,
      (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card) :
    ∃ (f : ℕ → ℚ) (E D : Set ℕ),
      (∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n) ∧
      (∀ p ∈ D, p.Prime) ∧
      Summable (fun p : D => (1 : ℝ) / (p : ℕ)) ∧
      (∀ p, p.Prime → p ∉ D → f p = 0) ∧
      Tendsto (fun N =>
        (((Finset.Icc 1 N).filter (fun n => n ∈ E)).card : ℝ) / N) atTop (nhds 0) ∧
      (∀ n ∈ A, n ∉ E → f n = 1) := by
  obtain ⟨K, hK, hs, hzero⟩ :=
    actual_integer_quotient_density_zero_removal A hpositive δ hδ hdensity
  let : Finite K := hK
  let q := QuotientAddGroup.mk' K.toAddSubgroup'
  let : Finite q.ker := finite_kernel_of_reduced_integer_quotient A hpositive K
  obtain ⟨F, hF⟩ := actual_integer_rational_level A hpositive hlength q
  let f := fun n => F (reducedIntegerClass A hpositive K n)
  let D := {p : ℕ | p.Prime ∧ Multiplicative.ofAdd (integerClass A hpositive p) ∉ K}
  let E := {n : ℕ | n ∈ A ∧ Set.Finite {m | m ∈ A ∧
    reducedIntegerClass A hpositive K m = reducedIntegerClass A hpositive K n}}
  refine ⟨f, E, D, ?_, (fun p hp => hp.1), ?_, ?_, ?_, ?_⟩
  · intro m n hm hn
    simp only [f, reducedIntegerClass, integerClass_mul_nonzero A hpositive m n hm hn, map_add]
  · apply summable_prime_indicator_to_set D (fun p hp => hp.1)
    apply hs.congr
    intro p
    simp only [D, Set.mem_ofPred_eq, p.property, true_and, ite_not]
  · intro p hp hpD
    have hk : Multiplicative.ofAdd (integerClass A hpositive p) ∈ K := by
      by_contra hn
      exact hpD ⟨hp, hn⟩
    dsimp only [f]
    rw [reduced_integer_class_zero_of_mem A hpositive K p hk, map_zero]
  · simpa only [E, Set.mem_ofPred_eq] using hzero
  · intro n hn hnE
    have hinf : Set.Infinite {m | m ∈ A ∧
        reducedIntegerClass A hpositive K m = reducedIntegerClass A hpositive K n} :=
      fun hfin => hnE ⟨hn, hfin⟩
    apply hF
    have heq : Subtype.val '' {a : A |
        q (integerClass A hpositive a) = reducedIntegerClass A hpositive K n} =
        {m | m ∈ A ∧ reducedIntegerClass A hpositive K m =
          reducedIntegerClass A hpositive K n} := by
      ext m
      simp [q, reducedIntegerClass, and_comm]
    exact Set.Infinite.of_image Subtype.val (heq.symm ▸ hinf)


end Erdos786Audit

end

section
/- Source module: SmoothLevelDensity.lean -/

/-! Direct natural-density upper bounds for arbitrary smooth-part level sets. -/
namespace Erdos786Audit

open Filter Classical in
theorem smooth_level_eventual_density_upper
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (L : ℕ → Prop) (B : ℝ)
    (hmass : ∀ T : Finset ℕ, (∀ s ∈ T, s ∈ Nat.factoredNumbers P) →
      (∀ s ∈ T, L s) →
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ T, (1 : ℝ) / s) ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (fun n => L (smoothPart P n))).card : ℝ) / N < B + ε := by
  obtain ⟨S, hS, hsmall⟩ := exists_finite_smooth_tail_small P hP ε hε
  let T := S.filter L
  have hT : ∀ s ∈ T, s ∈ Nat.factoredNumbers P :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hTL : ∀ s ∈ T, L s := fun _ hs => (Finset.mem_filter.mp hs).2
  have hm := hmass T hT hTL
  have hlim := (finite_smooth_parts_density P T hP hT).add
    (finite_smooth_tail_density P S hP hS)
  have hless : (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ T, (1 : ℝ) / s) +
      (1 - (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ S, (1 : ℝ) / s)) < B + ε := by
    linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hless)] with N hN
  have hsub : (Finset.Icc 1 N).filter (fun n => L (smoothPart P n)) ⊆
      (Finset.Icc 1 N).filter (fun n => smoothPart P n ∈ T) ∪
      (Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S) := by
    intro n hn
    obtain ⟨hnI, hnL⟩ := Finset.mem_filter.mp hn
    by_cases hs : smoothPart P n ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hnI, Finset.mem_filter.mpr ⟨hs, hnL⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hs⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hr : (((Finset.Icc 1 N).filter (fun n => L (smoothPart P n))).card : ℝ) ≤
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∈ T)).card : ℝ) +
      (((Finset.Icc 1 N).filter (fun n => smoothPart P n ∉ S)).card : ℝ) := by
    exact_mod_cast hcard
  have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [add_div] at hd
  exact hd.trans_lt hN


open Filter Classical in
theorem density_bound_from_finite_smooth_levels
    (A E D : Set ℕ) (f : ℕ → ℚ) (δ B : ℝ)
    (hA : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
      atTop (nhds δ))
    (hE : Tendsto (fun N => (((Finset.Icc 1 N).filter (fun n => n ∈ E)).card : ℝ) / N)
      atTop (nhds 0))
    (h1 : f 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n)
    (hD : ∀ p ∈ D, p.Prime) (hs : Summable (fun p : D => (1 : ℝ) / (p : ℕ)))
    (hvanish : ∀ p, p.Prime → p ∉ D → f p = 0)
    (hlevel : ∀ n ∈ A, n ∉ E → f n = 1)
    (hmass : ∀ P T : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ s ∈ T, s ∈ Nat.factoredNumbers P) → (∀ s ∈ T, f s = 1) →
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ T, (1 : ℝ) / s) ≤ B) : δ ≤ B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨P, hPD, hsTail, htail⟩ :=
    summable_set_has_small_reciprocal_tail D hs (ε / 2) (by positivity)
  have hP : ∀ p ∈ P, p.Prime := fun p hp => hD p (hPD p hp)
  have hb := smooth_level_eventual_density_upper P hP (fun s => f s = 1) B
    (fun T hT hL => hmass P T hP hT hL) (ε / 2) (by positivity)
  have hlim := hA.sub hE
  have hbound : ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N -
      (((Finset.Icc 1 N).filter (fun n => n ∈ E)).card : ℝ) / N ≤ B + ε := by
    filter_upwards [hb, eventually_ge_atTop 1] with N hB hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    let U := (Finset.Icc 1 N).filter (fun n => n ∈ E)
    let V := (Finset.Icc 1 N).filter (fun n => f (smoothPart P n) = 1)
    let W := (Finset.Icc 1 N).filter (fun n => ∃ p ∈ {p | p ∈ D ∧ p ∉ P}, p ∣ n)
    have hsub : (Finset.Icc 1 N).filter (fun n => n ∈ A) ⊆ U ∪ (V ∪ W) := by
      intro n hn
      obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
      by_cases hnE : n ∈ E
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hnE⟩)
      · apply Finset.mem_union_right
        by_cases hd : ∃ p ∈ {p | p ∈ D ∧ p ∉ P}, p ∣ n
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hd⟩)
        · apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨hnI, ?_⟩
          have he := additive_class_eq_smoothPart f h1 hmul P n
            (by have := (Finset.mem_Icc.mp hnI).1; omega) (fun p hp hpn hpP => by
              apply hvanish p hp
              intro hpD
              exact hd ⟨p, ⟨hpD, hpP⟩, hpn⟩)
          exact he.symm.trans (hlevel n hnA hnE)
    have hc := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le U (V ∪ W)).trans (Nat.add_le_add_left (Finset.card_union_le V W) U.card))
    have hr : (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
        (U.card : ℝ) + (V.card + W.card) := by exact_mod_cast hc
    have hdiv := div_le_div_of_nonneg_right hr hNR.le
    rw [add_div, add_div] at hdiv
    have hd := summable_divisor_union_bound {p | p ∈ D ∧ p ∉ P}
      (fun p hp => (hD p hp.1).pos) hsTail N
    have hw : (W.card : ℝ) / N ≤ ε / 2 := by
      apply (div_le_iff₀ hNR).mpr
      exact (hd.trans (mul_le_mul_of_nonneg_left htail.le hNR.le)).trans_eq (mul_comm _ _)
    have hB' : (V.card : ℝ) / N < B + ε / 2 := by
      apply lt_of_eq_of_lt _ hB
      apply congrArg (fun T : Finset ℕ => (T.card : ℝ) / N)
      ext n
      simp only [V, Finset.mem_filter]
    dsimp only [U, V, W] at hdiv hw hB'
    linarith
  simpa only [sub_zero] using le_of_tendsto hlim hbound


end Erdos786Audit

end

section
/- Source module: AdditiveSmoothCharacters.lean -/

/-! Euler transform for the actual values of a completely additive real function. -/
namespace Erdos786Audit

noncomputable def additiveCharacterWeight (f : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ)⁻¹ * (Circle.exp (f n * t) : ℂ)

theorem additiveCharacterWeight_norm (f : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ‖additiveCharacterWeight f t n‖ = (n : ℝ)⁻¹ := by
  have hc := (Circle.exp (f n * t)).norm_coe
  simpa [additiveCharacterWeight, norm_inv] using
    congrArg (fun x : ℝ => (n : ℝ)⁻¹ * x) hc

noncomputable def additiveCharacterWeightHom (f : ℕ → ℝ) (h1 : f 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n) (t : ℝ) : ℕ →* ℂ where
  toFun := additiveCharacterWeight f t
  map_one' := by simp [additiveCharacterWeight, h1]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm, additiveCharacterWeight]
    by_cases hn : n = 0
    · simp [hn, additiveCharacterWeight]
    simp only [additiveCharacterWeight, hmul m n hm hn, add_mul, Circle.exp_add,
      Circle.coe_mul, Nat.cast_mul, mul_inv_rev]
    ring

theorem additive_smooth_character_hasSum (f : ℕ → ℝ) (h1 : f 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    HasSum (fun s : Nat.factoredNumbers P =>
      (((∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ) : ℝ) : ℂ) *
        Complex.exp ((f s : ℂ) * t * Complex.I))
      (∏ p ∈ P, (1 - (1 : ℂ) / p) /
        (1 - (p : ℂ)⁻¹ * Complex.exp ((f p : ℂ) * t * Complex.I))) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖additiveCharacterWeightHom f h1 hmul t p‖ < 1 := by
    intro p hp
    change ‖additiveCharacterWeight f t p‖ < 1
    rw [additiveCharacterWeight_norm]
    exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := additiveCharacterWeightHom f h1 hmul t) hp P).2
  have hn := hh.mul_left (∏ p ∈ P, (1 - (1 : ℂ) / p))
  simpa [additiveCharacterWeightHom, additiveCharacterWeight, Circle.coe_exp,
    Finset.filter_eq_self.mpr hP, Finset.prod_mul_distrib, div_eq_mul_inv,
    mul_assoc] using hn


end Erdos786Audit

end

section
/- Source module: SmoothRealLaw.lean -/

/-! The actual reciprocal-weighted law on values at smooth integers. -/
namespace Erdos786Audit
open MeasureTheory BoundedContinuousFunction

noncomputable def smoothRealLaw (P : Finset ℕ) (f : ℕ → ℝ) : Measure ℝ :=
  Measure.sum (fun s : Nat.factoredNumbers P =>
    ENNReal.ofReal ((∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ)) • Measure.dirac (f s))

theorem smoothRealLaw_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℝ) : IsProbabilityMeasure (smoothRealLaw P f) := by
  have hw : ∀ s : Nat.factoredNumbers P,
      0 ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ) := by
    intro s
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact le_of_lt (sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1))
  constructor
  rw [smoothRealLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hw (normalized_smooth_mass_hasSum P hP).summable,
    (normalized_smooth_mass_hasSum P hP).tsum_eq]
  norm_num

theorem smoothRealLaw_charFun (f : ℕ → ℝ) (h1 : f 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    charFun (smoothRealLaw P f) t =
      ∏ p ∈ P, (1 - (1 : ℂ) / p) /
        (1 - (p : ℂ)⁻¹ * Complex.exp ((f p : ℂ) * t * Complex.I)) := by
  let := smoothRealLaw_probability P hP f
  have hi := (innerProbChar t).integrable (μ := smoothRealLaw P f)
  rw [charFun_eq_integral_innerProbChar, smoothRealLaw, integral_sum_measure hi]
  rw [← (additive_smooth_character_hasSum f h1 hmul P hP t).tsum_eq]
  apply tsum_congr
  intro s
  have hw : 0 ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact le_of_lt (sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1))
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw, Complex.real_smul]
  simp [innerProbChar_apply, mul_comm]


end Erdos786Audit

end

section
/- Source module: PoissonAtomBound.lean -/

/-! Scalar estimates for the existing compound-Poisson endgame. -/
namespace Erdos786Audit

theorem poisson_numerator_max_at_index (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k) :
    Real.exp (-x) * x ^ k ≤ Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have he : x / k ≤ Real.exp (x / k - 1) := by
    have h := Real.add_one_le_exp (x / k - 1)
    linarith
  have hpow : x ^ k ≤ (k : ℝ) ^ k * Real.exp (x - k) := by
    calc
      x ^ k = ((k : ℝ) * (x / k)) ^ k := by rw [mul_div_cancel₀ _ hkR.ne']
      _ ≤ ((k : ℝ) * Real.exp (x / k - 1)) ^ k := by gcongr
      _ = (k : ℝ) ^ k * Real.exp (x - k) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        field_simp
  have h := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-x)).le
  calc
    Real.exp (-x) * x ^ k ≤ Real.exp (-x) * ((k : ℝ) ^ k * Real.exp (x - k)) := h
    _ = Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
      rw [mul_left_comm, ← Real.exp_add]
      rw [show -x + (x - (k : ℝ)) = -(k : ℝ) by ring, mul_comm]

theorem poisson_peak_le_exp_neg_one (k : ℕ) (hk : 0 < k) :
    Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (-1) := by
  by_cases hk1 : k = 1
  · subst k; simp
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hepos := Real.exp_pos (1 : ℝ)
  have hsqrt : Real.exp 1 ≤ Real.sqrt (2 * Real.pi * k) := by
    apply Real.le_sqrt_of_sq_le
    have hpi := Real.pi_gt_three
    have he := Real.exp_one_lt_three
    nlinarith
  have hf := (mul_le_mul_of_nonneg_right hsqrt
    (pow_nonneg (div_nonneg (Nat.cast_nonneg k) hepos.le) k)).trans
      (Stirling.le_factorial_stirling k)
  have hpow : ((k : ℝ) / Real.exp 1) ^ k = Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
    rw [div_pow, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
    simp only [mul_one]
    ring
  rw [hpow] at hf
  have hh := mul_le_mul_of_nonneg_left hf (Real.exp_pos (-1 : ℝ)).le
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  rw [← mul_assoc, he, one_mul] at hh
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos k)).mpr
  simpa only [mul_comm] using hh

theorem poisson_nonzero_atom_le_exp_neg_one (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k) :
    Real.exp (-x) * x ^ k / (k.factorial : ℝ) ≤ Real.exp (-1) := by
  exact (div_le_div_of_nonneg_right (poisson_numerator_max_at_index x hx k hk)
    (Nat.cast_nonneg _)).trans (poisson_peak_le_exp_neg_one k hk)


theorem poisson_probability_nonzero_atom_le_one_div_exp
    (r : NNReal) (k : ℕ) (hk : 0 < k) :
    (ProbabilityTheory.poissonMeasure r).real {k} ≤ 1 / Real.exp 1 := by
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  simpa only [Real.exp_neg, one_div] using
    poisson_nonzero_atom_le_exp_neg_one r r.property k hk


end Erdos786Audit

end

section
/- Source module: PoissonMixtureBound.lean -/

/-! At-most-one-hit and mixture estimates for the existing compound-Poisson endgame. -/
namespace Erdos786Audit

open Classical in
theorem finite_weighted_hits_le
    (S : ℕ → ℝ) (hS : Function.Injective S) (h0 : S 0 = 0)
    (x : ℝ) (hx : x ≠ 0) (w : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw : ∀ k, 0 < k → w k ≤ c) (T : Finset ℕ) :
    (∑ k ∈ T, if S k = x then w k else 0) ≤ c := by
  by_cases hh : ∃ k ∈ T, S k = x
  · obtain ⟨k, hkT, hk⟩ := hh
    have hk0 : 0 < k := by
      by_contra hn
      have hz : k = 0 := by omega
      exact hx (by simpa only [hz, h0] using hk.symm)
    have heq : (∑ j ∈ T, if S j = x then w j else 0) = w k := by
      rw [Finset.sum_eq_single k]
      · simp only [hk, if_pos]
      · intro j _ hj
        apply if_neg
        intro hhit
        exact hj (hS (hhit.trans hk.symm))
      · exact fun h => (h hkT).elim
    rw [heq]
    exact hw k hk0
  · have heq : (∑ k ∈ T, if S k = x then w k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact if_neg (fun h => hh ⟨k, hk, h⟩)
    rw [heq]
    exact hc

open Classical in
theorem finite_poisson_weighted_positive_path_hits_le
    (S : ℕ → ℝ) (hS : StrictMono S) (h0 : S 0 = 0)
    (x : ℝ) (hx : x ≠ 0) (r : NNReal) (T : Finset ℕ) :
    (∑ k ∈ T, if S k = x then
      (ProbabilityTheory.poissonMeasure r).real {k} else 0) ≤ 1 / Real.exp 1 := by
  exact finite_weighted_hits_le S hS.injective h0 x hx _ _ (by positivity)
    (fun k hk => poisson_probability_nonzero_atom_le_one_div_exp r k hk) T

theorem poisson_mixture_le_one_div_exp
    (r : NNReal) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (ha0 : a 0 = 0) (hs : Summable a) (h1 : ∑' k, a k ≤ 1) :
    (∑' k, (ProbabilityTheory.poissonMeasure r).real {k} * a k) ≤ 1 / Real.exp 1 := by
  have hdom : ∀ k, (ProbabilityTheory.poissonMeasure r).real {k} * a k ≤
      (1 / Real.exp 1) * a k := by
    intro k
    by_cases hk : k = 0
    · subst k; simp only [ha0, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right
        (poisson_probability_nonzero_atom_le_one_div_exp r k (Nat.pos_of_ne_zero hk)) (ha k)
  have hn : ∀ k, 0 ≤ (ProbabilityTheory.poissonMeasure r).real {k} * a k :=
    fun k => mul_nonneg (MeasureTheory.measureReal_nonneg) (ha k)
  have hsum := Summable.of_nonneg_of_le hn hdom (hs.mul_left (1 / Real.exp 1))
  calc
    _ ≤ ∑' k, (1 / Real.exp 1) * a k := hsum.tsum_le_tsum hdom (hs.mul_left _)
    _ = (1 / Real.exp 1) * ∑' k, a k := tsum_mul_left
    _ ≤ (1 / Real.exp 1) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _


open MeasureTheory in
theorem increasing_process_hit_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (S k))
    (hi : ∀ ω, StrictMono (fun k => S k ω)) (x : ℝ) :
    Summable (fun k => μ.real {ω | S k ω = x}) ∧
      (∑' k, μ.real {ω | S k ω = x}) ≤ 1 := by
  let H := fun k => {ω | S k ω = x}
  have hmeas : ∀ k, MeasurableSet (H k) := fun k => (hm k) (measurableSet_singleton x)
  have hdis : Pairwise (fun i j => Disjoint (H i) (H j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    exact hij ((hi ω).injective (hωi.trans hωj.symm))
  have heq : (∑' k, μ (H k)) = μ (⋃ k, H k) := (measure_iUnion hdis hmeas).symm
  have hfinite : (∑' k, μ (H k)) ≠ ⊤ := by rw [heq]; exact measure_ne_top _ _
  refine ⟨ENNReal.summable_toReal hfinite, ?_⟩
  change (∑' k, (μ (H k)).toReal) ≤ 1
  rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ (H k)), heq]
  exact measureReal_le_one


open MeasureTheory in
theorem poisson_mixture_of_increasing_process_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (S k))
    (hi : ∀ ω, StrictMono (fun k => S k ω)) (h0 : ∀ ω, S 0 ω = 0)
    (x : ℝ) (hx : x ≠ 0) (r : NNReal) :
    (∑' k, (ProbabilityTheory.poissonMeasure r).real {k} *
      μ.real {ω | S k ω = x}) ≤ 1 / Real.exp 1 := by
  obtain ⟨hs, hsum⟩ := increasing_process_hit_mass μ S hm hi x
  apply poisson_mixture_le_one_div_exp r _ (fun _ => measureReal_nonneg) _ hs hsum
  have heq : {ω | S 0 ω = x} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, h0 ω, Set.mem_empty_iff_false, iff_false]
    exact hx.symm
  rw [heq]
  simp


end Erdos786Audit

end

section
/- Source module: PositiveJumpProcess.lean -/

/-! Canonical positive-jump paths under the infinite product probability measure. -/
namespace Erdos786Audit

abbrev PositiveJump := {x : ℝ // 0 < x}

def positiveJumpPartialSum (k : ℕ) (ω : ℕ → PositiveJump) : ℝ :=
  ∑ i ∈ Finset.range k, (ω i : ℝ)

theorem measurable_positiveJumpPartialSum (k : ℕ) :
    Measurable (positiveJumpPartialSum k) := by
  unfold positiveJumpPartialSum
  fun_prop

theorem strictMono_positiveJumpPartialSum (ω : ℕ → PositiveJump) :
    StrictMono (fun k => positiveJumpPartialSum k ω) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [positiveJumpPartialSum, Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (ω k).property

open MeasureTheory in
noncomputable def positiveJumpPathMeasure (ν : Measure PositiveJump) : Measure (ℕ → PositiveJump) :=
  Measure.infinitePi (fun _ : ℕ => ν)

open MeasureTheory in
instance positiveJumpPathMeasure_probability (ν : Measure PositiveJump) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (positiveJumpPathMeasure ν) := by
  unfold positiveJumpPathMeasure
  infer_instance

open MeasureTheory in
theorem positive_jump_poisson_mixture_atom_bound
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal)
    (x : ℝ) (hx : x ≠ 0) :
    (∑' k, (ProbabilityTheory.poissonMeasure r).real {k} *
      (positiveJumpPathMeasure ν).real {ω | positiveJumpPartialSum k ω = x}) ≤
      1 / Real.exp 1 := by
  exact poisson_mixture_of_increasing_process_le (positiveJumpPathMeasure ν)
    positiveJumpPartialSum measurable_positiveJumpPartialSum strictMono_positiveJumpPartialSum
    (fun ω => by simp [positiveJumpPartialSum]) x hx r


open MeasureTheory ProbabilityTheory in
theorem positive_jump_coordinates_independent
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] :
    iIndepFun (fun i (ω : ℕ → PositiveJump) => ω i) (positiveJumpPathMeasure ν) := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ => ν)
    (X := fun _ x => x) (fun _ => measurable_id)

open MeasureTheory in
theorem positive_jump_coordinate_law
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (i : ℕ) :
    (positiveJumpPathMeasure ν).map (fun ω => ω i) = ν :=
  Measure.infinitePi_map_eval (fun _ : ℕ => ν) i


end Erdos786Audit

end

section
/- Source module: PositiveCompoundPoisson.lean -/

namespace Erdos786Audit
open MeasureTheory

noncomputable def positiveCompoundPoisson (ν : Measure PositiveJump) (r : NNReal) : Measure ℝ :=
  Measure.sum (fun k : ℕ => (ProbabilityTheory.poissonMeasure r) {k} •
    (positiveJumpPathMeasure ν).map (positiveJumpPartialSum k))

instance positiveCompoundPoisson_probability
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal) :
    IsProbabilityMeasure (positiveCompoundPoisson ν r) := by
  constructor
  rw [positiveCompoundPoisson, Measure.sum_apply _ MeasurableSet.univ]
  have ht : ∀ k, ((ProbabilityTheory.poissonMeasure r) {k} •
      (positiveJumpPathMeasure ν).map (positiveJumpPartialSum k)) Set.univ =
      (ProbabilityTheory.poissonMeasure r) {k} := by
    intro k
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_positiveJumpPartialSum k) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, mul_one]
  simp only [ht]
  have h := measure_iUnion (μ := ProbabilityTheory.poissonMeasure r)
    (fun i j hij => Set.disjoint_singleton.mpr hij) (fun k : ℕ => measurableSet_singleton k)
  have hu : (⋃ k : ℕ, ({k} : Set ℕ)) = Set.univ := by
    ext k
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨k, rfl⟩
  rw [hu, measure_univ] at h
  exact h.symm

theorem positiveCompoundPoisson_singleton (ν : Measure PositiveJump) (r : NNReal) (x : ℝ) :
    positiveCompoundPoisson ν r {x} =
      ∑' k, (ProbabilityTheory.poissonMeasure r) {k} *
        positiveJumpPathMeasure ν {ω | positiveJumpPartialSum k ω = x} := by
  rw [positiveCompoundPoisson, Measure.sum_apply _ (measurableSet_singleton x)]
  apply tsum_congr
  intro k
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_positiveJumpPartialSum k) (measurableSet_singleton x)]
  rfl

theorem positiveCompoundPoisson_real_singleton
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal) (x : ℝ) :
    (positiveCompoundPoisson ν r).real {x} =
      ∑' k, (ProbabilityTheory.poissonMeasure r).real {k} *
        (positiveJumpPathMeasure ν).real {ω | positiveJumpPartialSum k ω = x} := by
  rw [measureReal_def, positiveCompoundPoisson_singleton,
    ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  apply tsum_congr
  intro k
  exact ENNReal.toReal_mul

theorem positiveCompoundPoisson_nonzero_atom_bound
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal)
    (x : ℝ) (hx : x ≠ 0) :
    (positiveCompoundPoisson ν r).real {x} ≤ 1 / Real.exp 1 := by
  rw [positiveCompoundPoisson_real_singleton]
  exact positive_jump_poisson_mixture_atom_bound ν r x hx


theorem positiveCompoundPoisson_negative_halfline
    (ν : Measure PositiveJump) (r : NNReal) :
    positiveCompoundPoisson ν r (Set.Iio 0) = 0 := by
  rw [positiveCompoundPoisson, Measure.sum_apply _ measurableSet_Iio]
  apply ENNReal.tsum_eq_zero.mpr
  intro k
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_positiveJumpPartialSum k) measurableSet_Iio]
  have heq : positiveJumpPartialSum k ⁻¹' Set.Iio 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hn : 0 ≤ positiveJumpPartialSum k ω := by
      apply Finset.sum_nonneg
      intro i _
      exact (ω i).property.le
    exact (not_lt_of_ge hn) hω
  rw [heq, measure_empty, mul_zero]


end Erdos786Audit

end

section
/- Source module: SignedAtomBound.lean -/

namespace Erdos786Audit
open MeasureTheory

noncomputable def independentDifferenceLaw (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun z : ℝ × ℝ => z.1 - z.2)

theorem independent_difference_positive_atom_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ENNReal) (hμ : ∀ t : ℝ, t ≠ 0 → μ {t} ≤ c)
    (hν : ν (Set.Iio 0) = 0) (x : ℝ) (hx : 0 < x) :
    independentDifferenceLaw μ ν {x} ≤ c := by
  have hm : Measurable (fun z : ℝ × ℝ => z.1 - z.2) := by fun_prop
  rw [independentDifferenceLaw, Measure.map_apply hm (measurableSet_singleton x),
    Measure.prod_apply_symm (hm (measurableSet_singleton x))]
  have hae : ∀ᵐ y ∂ν, 0 ≤ y := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio_def] using hν
  calc
    _ ≤ ∫⁻ _y, c ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hae] with y hy
      have heq : (fun z => (z, y)) ⁻¹'
          ((fun z : ℝ × ℝ => z.1 - z.2) ⁻¹' {x}) = {x + y} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [heq]
      exact hμ (x + y) (by linarith)
    _ = c := by simp


theorem independent_difference_negative_atom_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ENNReal) (hν : ∀ t : ℝ, t ≠ 0 → ν {t} ≤ c)
    (hμ : μ (Set.Iio 0) = 0) (x : ℝ) (hx : x < 0) :
    independentDifferenceLaw μ ν {x} ≤ c := by
  have hm : Measurable (fun z : ℝ × ℝ => z.1 - z.2) := by fun_prop
  rw [independentDifferenceLaw, Measure.map_apply hm (measurableSet_singleton x),
    Measure.prod_apply (hm (measurableSet_singleton x))]
  have hae : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [ae_iff]
    simpa only [not_le, Set.Iio_def] using hμ
  calc
    _ ≤ ∫⁻ _y, c ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hae] with y hy
      have heq : Prod.mk y ⁻¹'
          ((fun z : ℝ × ℝ => z.1 - z.2) ⁻¹' {x}) = {y - x} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [heq]
      exact hν (y - x) (by linarith)
    _ = c := by simp

instance independentDifferenceLaw_probability
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentDifferenceLaw μ ν) := by
  constructor
  rw [independentDifferenceLaw, Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem signed_positive_compound_poisson_atom_bound
    (ν₁ ν₂ : Measure PositiveJump) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (r₁ r₂ : NNReal) (x : ℝ) (hx : x ≠ 0) :
    (independentDifferenceLaw (positiveCompoundPoisson ν₁ r₁)
      (positiveCompoundPoisson ν₂ r₂)).real {x} ≤ 1 / Real.exp 1 := by
  have hb : ∀ (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal)
      (t : ℝ), t ≠ 0 → positiveCompoundPoisson ν r {t} ≤ ENNReal.ofReal (1 / Real.exp 1) := by
    intro ν _ r t ht
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    exact positiveCompoundPoisson_nonzero_atom_bound ν r t ht
  have he : independentDifferenceLaw (positiveCompoundPoisson ν₁ r₁)
      (positiveCompoundPoisson ν₂ r₂) {x} ≤ ENNReal.ofReal (1 / Real.exp 1) := by
    rcases lt_or_gt_of_ne hx with hn | hp
    · exact independent_difference_negative_atom_le _ _ _ (hb ν₂ r₂)
        (positiveCompoundPoisson_negative_halfline ν₁ r₁) x hn
    · exact independent_difference_positive_atom_le _ _ _ (hb ν₁ r₁)
        (positiveCompoundPoisson_negative_halfline ν₂ r₂) x hp
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mp he


end Erdos786Audit

end

section
/- Source module: FiniteIntensity.lean -/

/-! Normalization of finite positive-jump intensities, including zero intensity. -/
namespace Erdos786Audit
open MeasureTheory BoundedContinuousFunction

theorem finite_positive_intensity_normalization
    (η : Measure PositiveJump) [IsFiniteMeasure η] :
    ∃ (r : NNReal) (ν : Measure PositiveJump), IsProbabilityMeasure ν ∧
      η = (r : ENNReal) • ν := by
  by_cases hη : η = 0
  · refine ⟨0, Measure.dirac ⟨1, by norm_num⟩, inferInstance, ?_⟩
    simp [hη]
  · have hm : η Set.univ ≠ 0 := by
      intro hz
      apply hη
      exact Measure.measure_univ_eq_zero.mp hz
    have hfinite : η Set.univ ≠ ⊤ := measure_ne_top _ _
    let r : NNReal := (η Set.univ).toNNReal
    let ν : Measure PositiveJump := (η Set.univ)⁻¹ • η
    have hprob : IsProbabilityMeasure ν := by
      constructor
      change ((η Set.univ)⁻¹ • η) Set.univ = 1
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm hfinite]
    refine ⟨r, ν, hprob, ?_⟩
    rw [show (r : ENNReal) = η Set.univ from ENNReal.coe_toNNReal hfinite]
    change η = η Set.univ • ((η Set.univ)⁻¹ • η)
    rw [smul_smul, ENNReal.mul_inv_cancel hm hfinite, one_smul]


theorem normalized_intensity_centered_integral
    (η ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal)
    (hη : η = (r : ENNReal) • ν) (g : PositiveJump → ℂ) (hg : Integrable g ν) :
    (∫ x, g x - 1 ∂η) = (r : ℂ) * ((∫ x, g x ∂ν) - 1) := by
  rw [hη, integral_smul_measure, integral_sub hg (integrable_const (1 : ℂ))]
  simp [Complex.real_smul]


noncomputable def atomicPositiveIntensity {ι : Type*} (w : ι → ℝ) (v : ι → PositiveJump) :
    Measure PositiveJump :=
  Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (v i))

theorem atomicPositiveIntensity_total {ι : Type*} (w : ι → ℝ) (v : ι → PositiveJump)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) :
    atomicPositiveIntensity w v Set.univ = ENNReal.ofReal (∑' i, w i) := by
  rw [atomicPositiveIntensity, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact (ENNReal.ofReal_tsum_of_nonneg hw hs).symm

theorem atomicPositiveIntensity_finite {ι : Type*} (w : ι → ℝ) (v : ι → PositiveJump)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) :
    IsFiniteMeasure (atomicPositiveIntensity w v) := by
  constructor
  rw [atomicPositiveIntensity_total w v hw hs]
  exact ENNReal.ofReal_lt_top


theorem atomicPositiveIntensity_integral {ι : Type*} (w : ι → ℝ) (v : ι → PositiveJump)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (g : PositiveJump →ᵇ ℂ) :
    (∫ x, g x ∂atomicPositiveIntensity w v) = ∑' i, (w i : ℂ) * g (v i) := by
  let : IsFiniteMeasure (atomicPositiveIntensity w v) := atomicPositiveIntensity_finite w v hw hs
  have hi := g.integrable (μ := atomicPositiveIntensity w v)
  rw [atomicPositiveIntensity, integral_sum_measure hi]
  apply tsum_congr
  intro i
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), Complex.real_smul]


end Erdos786Audit

end

section
/- Source module: GeometricPoissonIdentity.lean -/

/-! Logarithmic jump series underlying a geometric distribution. -/
namespace Erdos786Audit

theorem geometric_jump_series_hasSum (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (z : Circle) :
    HasSum (fun j : ℕ => (q : ℂ) ^ j / (j : ℂ) * ((z : ℂ) ^ j - 1))
      (Complex.log (1 - (q : ℂ)) - Complex.log (1 - (q : ℂ) * (z : ℂ))) := by
  have hqnorm : ‖(q : ℂ)‖ < 1 := by simpa [abs_of_nonneg hq] using hq1
  have hqz : ‖(q : ℂ) * (z : ℂ)‖ < 1 := by
    rw [norm_mul, z.norm_coe, mul_one]
    exact hqnorm
  have hh := (Complex.hasSum_taylorSeries_neg_log hqz).sub
    (Complex.hasSum_taylorSeries_neg_log hqnorm)
  have he : -Complex.log (1 - (q : ℂ) * (z : ℂ)) - (-Complex.log (1 - (q : ℂ))) =
      Complex.log (1 - (q : ℂ)) - Complex.log (1 - (q : ℂ) * (z : ℂ)) := by ring
  rw [he] at hh
  apply hh.congr_fun
  intro j
  rw [mul_pow]
  ring

theorem geometric_jump_exponential (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (z : Circle) :
    Complex.exp (∑' j : ℕ, (q : ℂ) ^ j / (j : ℂ) * ((z : ℂ) ^ j - 1)) =
      (1 - (q : ℂ)) / (1 - (q : ℂ) * (z : ℂ)) := by
  rw [(geometric_jump_series_hasSum q hq hq1 z).tsum_eq, Complex.exp_sub]
  have hq0 : 1 - (q : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.one_re, Complex.ofReal_re] at hr
    linarith
  have hqz0 : 1 - (q : ℂ) * (z : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hh := congrArg norm he
    rw [norm_one, norm_mul, z.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hq] at hh
    linarith
  rw [Complex.exp_log hq0, Complex.exp_log hqz0]


theorem finite_geometric_jump_exponential
    {ι : Type*} (P : Finset ι) (q : ι → ℝ) (z : ι → Circle)
    (hq : ∀ i ∈ P, 0 ≤ q i) (hq1 : ∀ i ∈ P, q i < 1) :
    Complex.exp (∑ i ∈ P, ∑' j : ℕ,
      (q i : ℂ) ^ j / (j : ℂ) * ((z i : ℂ) ^ j - 1)) =
      ∏ i ∈ P, (1 - (q i : ℂ)) / (1 - (q i : ℂ) * (z i : ℂ)) := by
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact geometric_jump_exponential (q i) (hq i hi) (hq1 i hi) (z i)

theorem geometric_jump_intensity_hasSum (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => q ^ (j + 1) / (j + 1 : ℕ)) (-Real.log (1 - q)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    Real.hasSum_pow_div_log_of_abs_lt_one (x := q) (by simpa only [abs_of_nonneg hq] using hq1)


end Erdos786Audit

end

section
/- Source module: GeometricIntensity.lean -/

/-! The finite positive jump intensity attached to one geometric factor. -/
namespace Erdos786Audit
open MeasureTheory BoundedContinuousFunction

noncomputable def geometricPositiveIntensity (q a : ℝ) (ha : 0 < a) :
    Measure PositiveJump :=
  atomicPositiveIntensity (fun j : ℕ => q ^ (j + 1) / (j + 1 : ℕ))
    (fun j => ⟨(j + 1 : ℕ) * a, by positivity⟩)

theorem geometricPositiveIntensity_finite (q a : ℝ) (ha : 0 < a)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    IsFiniteMeasure (geometricPositiveIntensity q a ha) := by
  apply atomicPositiveIntensity_finite
  · intro j; positivity
  · exact (geometric_jump_intensity_hasSum q hq hq1).summable

theorem geometricPositiveIntensity_total (q a : ℝ) (ha : 0 < a)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    geometricPositiveIntensity q a ha Set.univ = ENNReal.ofReal (-Real.log (1 - q)) := by
  rw [geometricPositiveIntensity, atomicPositiveIntensity_total]
  · rw [(geometric_jump_intensity_hasSum q hq hq1).tsum_eq]
  · intro j; positivity
  · exact (geometric_jump_intensity_hasSum q hq hq1).summable

noncomputable def positiveJumpChar (t : ℝ) : PositiveJump →ᵇ ℂ :=
  (innerProbChar t).compContinuous ⟨Subtype.val, continuous_subtype_val⟩

theorem geometricPositiveIntensity_centered_integral (q a : ℝ) (ha : 0 < a)
    (hq : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    (∫ x, positiveJumpChar t x - 1 ∂geometricPositiveIntensity q a ha) =
      ∑' j : ℕ, ((q ^ (j + 1) / (j + 1 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((j + 1 : ℕ) : ℂ) * a * t * Complex.I) - 1) := by
  have h := atomicPositiveIntensity_integral
    (fun j : ℕ => q ^ (j + 1) / (j + 1 : ℕ))
    (fun j => (⟨(j + 1 : ℕ) * a, by positivity⟩ : PositiveJump))
    (by intro j; positivity) (geometric_jump_intensity_hasSum q hq hq1).summable
    (positiveJumpChar t - 1)
  simpa [geometricPositiveIntensity, positiveJumpChar, innerProbChar_apply,
    real_inner_comm, mul_comm, mul_left_comm, mul_assoc] using h


theorem geometricPositiveIntensity_exponential (q a : ℝ) (ha : 0 < a)
    (hq : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    Complex.exp (∫ x, positiveJumpChar t x - 1 ∂geometricPositiveIntensity q a ha) =
      (1 - (q : ℂ)) / (1 - (q : ℂ) * Complex.exp ((a : ℂ) * t * Complex.I)) := by
  rw [geometricPositiveIntensity_centered_integral q a ha hq hq1 t]
  let z : Circle := Circle.exp (a * t)
  have hz : (z : ℂ) = Complex.exp ((a : ℂ) * t * Complex.I) := by
    simp [z, Circle.coe_exp]
  have hs := (geometric_jump_series_hasSum q hq hq1 z).summable
  have he := hs.tsum_eq_zero_add
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_mul, zero_add] at he
  have hj : (∑' j : ℕ, ((q ^ (j + 1) / (j + 1 : ℕ) : ℝ) : ℂ) *
        (Complex.exp (((j + 1 : ℕ) : ℂ) * a * t * Complex.I) - 1)) =
      ∑' j : ℕ, (q : ℂ) ^ j / (j : ℂ) * ((z : ℂ) ^ j - 1) := by
    rw [he]
    apply tsum_congr
    intro j
    rw [hz, ← Complex.exp_nat_mul]
    push_cast
    simp only [mul_assoc]
  rw [hj, geometric_jump_exponential q hq hq1 z, hz]


end Erdos786Audit

end

section
/- Source module: PoissonTransform.lean -/

/-! The complex power transform of Poisson weights. -/
namespace Erdos786Audit

theorem poisson_weighted_powers_hasSum (r : NNReal) (z : ℂ) :
    HasSum (fun k : ℕ => ((ProbabilityTheory.poissonMeasure r).real {k} : ℂ) * z ^ k)
      (Complex.exp ((r : ℂ) * (z - 1))) := by
  have hf := (NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * z)).mul_left
    (Complex.exp (-(r : ℂ)))
  simp only [← Complex.exp_eq_exp_ℂ] at hf
  have he : Complex.exp (-(r : ℂ)) * Complex.exp ((r : ℂ) * z) =
      Complex.exp ((r : ℂ) * (z - 1)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he] at hf
  apply hf.congr
  intro T
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  push_cast
  rw [mul_pow]
  ring


end Erdos786Audit

end

section
/- Source module: CompoundPoissonTransform.lean -/

namespace Erdos786Audit
open MeasureTheory BoundedContinuousFunction

theorem positiveCompoundPoisson_charFun_series
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal) (t : ℝ) :
    charFun (positiveCompoundPoisson ν r) t =
      ∑' k, ((ProbabilityTheory.poissonMeasure r).real {k} : ℂ) *
        charFun ((positiveJumpPathMeasure ν).map (positiveJumpPartialSum k)) t := by
  have hi : Integrable (innerProbChar t) (positiveCompoundPoisson ν r) :=
    (innerProbChar t).integrable (μ := positiveCompoundPoisson ν r)
  rw [charFun_eq_integral_innerProbChar, positiveCompoundPoisson,
    integral_sum_measure hi]
  apply tsum_congr
  intro k
  rw [integral_smul_measure, charFun_eq_integral_innerProbChar]
  rfl

theorem positiveCompoundPoisson_charFun_of_partial_sum_transform
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal) (t : ℝ) (z : ℂ)
    (hpartial : ∀ k, charFun ((positiveJumpPathMeasure ν).map (positiveJumpPartialSum k)) t = z ^ k) :
    charFun (positiveCompoundPoisson ν r) t = Complex.exp ((r : ℂ) * (z - 1)) := by
  rw [positiveCompoundPoisson_charFun_series]
  simp only [hpartial]
  exact (poisson_weighted_powers_hasSum r z).tsum_eq


open ProbabilityTheory in
theorem positive_jump_partial_sum_charFun
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (k : ℕ) (t : ℝ) :
    charFun ((positiveJumpPathMeasure ν).map (positiveJumpPartialSum k)) t =
      (charFun (ν.map (fun x : PositiveJump => (x : ℝ))) t) ^ k := by
  have hi := (positive_jump_coordinates_independent ν).comp
    (fun _ (x : PositiveJump) => (x : ℝ)) (fun _ => by fun_prop)
  have hmap (i : ℕ) : (positiveJumpPathMeasure ν).map
      (fun ω : ℕ → PositiveJump => (ω i : ℝ)) = ν.map (fun x : PositiveJump => (x : ℝ)) := by
    calc
      _ = ((positiveJumpPathMeasure ν).map (fun ω => ω i)).map
          (fun x : PositiveJump => (x : ℝ)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = _ := by rw [positive_jump_coordinate_law]
  have hh := (hi.restrict (Finset.range k)).charFun_map_fun_finsetSum_eq_prod
    (fun i _ => (measurable_subtype_coe.comp (measurable_pi_apply i)).aemeasurable)
  have ht := congrArg (fun h : ℝ → ℂ => h t) hh
  have he : positiveJumpPartialSum k =
      (fun ω : ℕ → PositiveJump => ∑ i ∈ Finset.range k, (ω i : ℝ)) := rfl
  rw [he]
  simpa only [Function.comp_def, positiveJumpPartialSum, Finset.prod_apply,
    hmap, Finset.prod_const, Finset.card_range] using ht

theorem positiveCompoundPoisson_charFun
    (ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal) (t : ℝ) :
    charFun (positiveCompoundPoisson ν r) t =
      Complex.exp ((r : ℂ) * (charFun (ν.map (fun x : PositiveJump => (x : ℝ))) t - 1)) := by
  exact positiveCompoundPoisson_charFun_of_partial_sum_transform ν r t _
    (fun k => positive_jump_partial_sum_charFun ν k t)


end Erdos786Audit

end

section
/- Source module: IntensityTransform.lean -/

/-! Characteristic functions in terms of the unnormalized jump intensity. -/
namespace Erdos786Audit
open MeasureTheory BoundedContinuousFunction

theorem positiveJumpChar_integral (ν : Measure PositiveJump) (t : ℝ) :
    (∫ x, positiveJumpChar t x ∂ν) =
      charFun (ν.map (fun x : PositiveJump => (x : ℝ))) t := by
  rw [charFun_eq_integral_innerProbChar,
    integral_map_of_stronglyMeasurable measurable_subtype_coe
      (innerProbChar t).continuous.stronglyMeasurable]
  rfl

theorem positiveCompoundPoisson_charFun_intensity
    (η ν : Measure PositiveJump) [IsProbabilityMeasure ν] (r : NNReal)
    (hη : η = (r : ENNReal) • ν) (t : ℝ) :
    charFun (positiveCompoundPoisson ν r) t =
      Complex.exp (∫ x, positiveJumpChar t x - 1 ∂η) := by
  rw [normalized_intensity_centered_integral η ν r hη _
    ((positiveJumpChar t).integrable (μ := ν)), positiveJumpChar_integral,
    positiveCompoundPoisson_charFun]

theorem geometric_intensity_has_compound_poisson_law
    (q a : ℝ) (ha : 0 < a) (hq : 0 ≤ q) (hq1 : q < 1) :
    ∃ (r : NNReal) (ν : Measure PositiveJump), IsProbabilityMeasure ν ∧
      ∀ t : ℝ, charFun (positiveCompoundPoisson ν r) t =
        (1 - (q : ℂ)) / (1 - (q : ℂ) * Complex.exp ((a : ℂ) * t * Complex.I)) := by
  let := geometricPositiveIntensity_finite q a ha hq hq1
  obtain ⟨r, ν, hν, hη⟩ := finite_positive_intensity_normalization
    (geometricPositiveIntensity q a ha)
  let := hν
  refine ⟨r, ν, hν, fun t => ?_⟩
  rw [positiveCompoundPoisson_charFun_intensity _ ν r hη t]
  exact geometricPositiveIntensity_exponential q a ha hq hq1 t


theorem finite_geometric_intensity_has_compound_poisson_law
    {ι : Type*} [Fintype ι] (q a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    ∃ (r : NNReal) (ν : Measure PositiveJump), IsProbabilityMeasure ν ∧
      ∀ t : ℝ, charFun (positiveCompoundPoisson ν r) t =
        ∏ i, (1 - (q i : ℂ)) /
          (1 - (q i : ℂ) * Complex.exp ((a i : ℂ) * t * Complex.I)) := by
  let η : ι → Measure PositiveJump := fun i => geometricPositiveIntensity (q i) (a i) (ha i)
  let : ∀ i, IsFiniteMeasure (η i) := fun i =>
    geometricPositiveIntensity_finite (q i) (a i) (ha i) (hq i) (hq1 i)
  obtain ⟨r, ν, hν, hη⟩ := finite_positive_intensity_normalization (Measure.sum η)
  let := hν
  refine ⟨r, ν, hν, fun t => ?_⟩
  rw [positiveCompoundPoisson_charFun_intensity _ ν r hη t]
  have hi := (positiveJumpChar t - 1).integrable (μ := Measure.sum η)
  change Integrable (fun x => positiveJumpChar t x - 1) (Measure.sum η) at hi
  rw [integral_sum_measure hi, tsum_fintype, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact geometricPositiveIntensity_exponential (q i) (a i) (ha i) (hq i) (hq1 i) t


end Erdos786Audit

end

section
/- Source module: SignedTransform.lean -/

/-! Characteristic-function comparison for independent positive and negative parts. -/
namespace Erdos786Audit
open MeasureTheory

theorem independentDifferenceLaw_charFun
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
    charFun (independentDifferenceLaw μ ν) t = charFun μ t * charFun ν (-t) := by
  rw [independentDifferenceLaw, charFun_apply_real,
    integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  simp only [charFun_apply_real]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem two_families_geometric_law_atom_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q a : ι → ℝ) (s b : κ → ℝ)
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hb : ∀ i, 0 < b i) (hs : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i < 1) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ x : ℝ, x ≠ 0 → μ.real {x} ≤ 1 / Real.exp 1) ∧
      ∀ t : ℝ, charFun μ t =
        (∏ i, (1 - (q i : ℂ)) /
          (1 - (q i : ℂ) * Complex.exp ((a i : ℂ) * t * Complex.I))) *
        (∏ i, (1 - (s i : ℂ)) /
          (1 - (s i : ℂ) * Complex.exp ((b i : ℂ) * (-t) * Complex.I))) := by
  obtain ⟨r₁, ν₁, hν₁, h₁⟩ :=
    finite_geometric_intensity_has_compound_poisson_law q a ha hq hq1
  obtain ⟨r₂, ν₂, hν₂, h₂⟩ :=
    finite_geometric_intensity_has_compound_poisson_law s b hb hs hs1
  let := hν₁
  let := hν₂
  refine ⟨independentDifferenceLaw (positiveCompoundPoisson ν₁ r₁)
    (positiveCompoundPoisson ν₂ r₂), inferInstance, ?_, ?_⟩
  · exact fun x hx => signed_positive_compound_poisson_atom_bound ν₁ ν₂ r₁ r₂ x hx
  · intro t
    rw [independentDifferenceLaw_charFun, h₁, h₂]
    simp only [Complex.ofReal_neg]


theorem atom_bound_of_two_families_geometric_charFun
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q a : ι → ℝ) (s b : κ → ℝ)
    (ha : ∀ i, 0 < a i) (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hb : ∀ i, 0 < b i) (hs : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ t : ℝ, charFun μ t =
        (∏ i, (1 - (q i : ℂ)) /
          (1 - (q i : ℂ) * Complex.exp ((a i : ℂ) * t * Complex.I))) *
        (∏ i, (1 - (s i : ℂ)) /
          (1 - (s i : ℂ) * Complex.exp ((b i : ℂ) * (-t) * Complex.I))))
    (x : ℝ) (hx : x ≠ 0) : μ.real {x} ≤ 1 / Real.exp 1 := by
  obtain ⟨ρ, hρ, hatom, hchar⟩ := two_families_geometric_law_atom_bound
    q a s b ha hq hq1 hb hs hs1
  let := hρ
  have he : μ = ρ := Measure.ext_of_charFun (funext fun t => (hμ t).trans (hchar t).symm)
  rw [he]
  exact hatom x hx


end Erdos786Audit

end

section
/- Source module: GeometricSignSplit.lean -/

namespace Erdos786Audit

noncomputable def geometricFactor (q a t : ℝ) : ℂ :=
  (1 - (q : ℂ)) / (1 - (q : ℂ) * Complex.exp ((a : ℂ) * t * Complex.I))

theorem geometricFactor_zero (q t : ℝ) (hq : q < 1) : geometricFactor q 0 t = 1 := by
  have hn : 1 - (q : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  simp [geometricFactor, hn]

theorem geometricFactor_neg (q a t : ℝ) :
    geometricFactor q (-a) (-t) = geometricFactor q a t := by
  simp [geometricFactor]

theorem geometric_product_sign_split {ι : Type*} (P : Finset ι) (q a : ι → ℝ)
    (hq : ∀ i ∈ P, q i < 1) (t : ℝ) :
    (∏ i ∈ P, geometricFactor (q i) (a i) t) =
      (∏ i ∈ P.filter (fun i => 0 < a i), geometricFactor (q i) (a i) t) *
      (∏ i ∈ P.filter (fun i => a i < 0), geometricFactor (q i) (-a i) (-t)) := by
  classical
  simp only [geometricFactor_neg]
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun i => 0 < a i)]
  congr 1
  symm
  apply Finset.prod_subset
  · intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, by linarith [hi.2]⟩
  · intro i hi hn
    simp only [Finset.mem_filter, not_lt] at hi
    have hz : a i = 0 := by
      have : ¬ a i < 0 := by
        intro h
        exact hn (Finset.mem_filter.mpr ⟨hi.1, h⟩)
      linarith
    rw [hz]
    exact geometricFactor_zero (q i) t (hq i hi.1)


open MeasureTheory in
theorem atom_bound_of_geometric_product_charFun {ι : Type*}
    (P : Finset ι) (q a : ι → ℝ)
    (hq : ∀ i ∈ P, 0 ≤ q i) (hq1 : ∀ i ∈ P, q i < 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ t, charFun μ t = ∏ i ∈ P, geometricFactor (q i) (a i) t)
    (x : ℝ) (hx : x ≠ 0) : μ.real {x} ≤ 1 / Real.exp 1 := by
  classical
  let S := P.filter (fun i => 0 < a i)
  let T := P.filter (fun i => a i < 0)
  apply atom_bound_of_two_families_geometric_charFun
    (fun i : S => q i) (fun i : S => a i)
    (fun i : T => q i) (fun i : T => -a i)
    (fun i => (Finset.mem_filter.mp i.property).2)
    (fun i => hq i (Finset.mem_filter.mp i.property).1)
    (fun i => hq1 i (Finset.mem_filter.mp i.property).1)
    (fun i => neg_pos.mpr (Finset.mem_filter.mp i.property).2)
    (fun i => hq i (Finset.mem_filter.mp i.property).1)
    (fun i => hq1 i (Finset.mem_filter.mp i.property).1) μ _ x hx
  intro t
  rw [hμ, geometric_product_sign_split P q a hq1 t]
  change (∏ i ∈ S, geometricFactor (q i) (a i) t) *
      (∏ i ∈ T, geometricFactor (q i) (-a i) (-t)) = _
  rw [← Finset.prod_coe_sort S (fun i => geometricFactor (q i) (a i) t),
    ← Finset.prod_coe_sort T (fun i => geometricFactor (q i) (-a i) (-t))]
  simp only [geometricFactor, Complex.ofReal_neg]


end Erdos786Audit

end

section
/- Source module: SmoothAtomBound.lean -/

namespace Erdos786Audit
open MeasureTheory

theorem smoothRealLaw_nonzero_atom_bound (f : ℕ → ℝ) (h1 : f 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℝ) (hx : x ≠ 0) :
    (smoothRealLaw P f).real {x} ≤ 1 / Real.exp 1 := by
  let := smoothRealLaw_probability P hP f
  apply atom_bound_of_geometric_product_charFun P (fun p => 1 / (p : ℝ)) f
    (fun p _ => by positivity)
    (fun p hp => (div_lt_one (by exact_mod_cast (hP p hp).pos)).mpr
      (by exact_mod_cast (hP p hp).one_lt)) (smoothRealLaw P f) _ x hx
  intro t
  rw [smoothRealLaw_charFun f h1 hmul P hP t]
  simp [geometricFactor, one_div]


theorem finite_smooth_subtype_mass_le_atom (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℝ) (S : Finset (Nat.factoredNumbers P)) (x : ℝ)
    (hS : ∀ s ∈ S, f s = x) :
    (∑ s ∈ S, (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ)) ≤
      (smoothRealLaw P f).real {x} := by
  let := smoothRealLaw_probability P hP f
  have hw (s : Nat.factoredNumbers P) :
      0 ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact le_of_lt (sub_pos.mpr ((div_lt_one (by linarith)).mpr hp1))
  have he : ENNReal.ofReal (∑ s ∈ S,
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ)) ≤ smoothRealLaw P f {x} := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => hw s), smoothRealLaw,
      Measure.sum_apply _ (measurableSet_singleton x)]
    calc
      _ = ∑ s ∈ S, (ENNReal.ofReal
          ((∏ p ∈ P, (1 - (1 : ℝ) / p)) / (s : ℕ)) • Measure.dirac (f s)) {x} := by
        apply Finset.sum_congr rfl
        intro s hs
        simp [hS s hs]
      _ ≤ _ := ENNReal.sum_le_tsum S
  have hh := ENNReal.toReal_mono (measure_ne_top _ _) he
  simpa only [measureReal_def,
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun s _ => hw s))] using hh


theorem finite_smooth_level_mass_bound (f : ℕ → ℝ) (h1 : f 1 = 0)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n)
    (P T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hT : ∀ s ∈ T, s ∈ Nat.factoredNumbers P)
    (x : ℝ) (hx : x ≠ 0) (hlevel : ∀ s ∈ T, f s = x) :
    (∏ p ∈ P, (1 - (1 : ℝ) / p)) * (∑ s ∈ T, (1 : ℝ) / s) ≤
      1 / Real.exp 1 := by
  classical
  have hb := finite_smooth_subtype_mass_le_atom P hP f
    (T.subtype (fun s => s ∈ Nat.factoredNumbers P)) x
    (fun s hs => hlevel s (by simpa using hs))
  have he := Finset.sum_subtype_of_mem
    (fun s : ℕ => (∏ p ∈ P, (1 - (1 : ℝ) / p)) / s) hT
  rw [he] at hb
  have h := hb.trans (smoothRealLaw_nonzero_atom_bound f h1 hmul P hP x hx)
  simpa only [Finset.mul_sum, mul_one_div] using h


end Erdos786Audit

end

section
/- Source module: DensityRoot.lean -/

/-! Natural-density bound from the original distinct-factor product condition. -/
namespace Erdos786Audit
open Filter Classical

theorem distinct_product_natural_density_le_inv_e
    (A : Set ℕ) (hpositive : ∀ n ∈ A, n ≠ 0) (δ : ℝ)
    (hdensity : Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (nhds δ))
    (hlength : ∀ U V : Finset A,
      (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card) :
    δ ≤ 1 / Real.exp 1 := by
  by_cases hδ : 0 < δ
  · obtain ⟨f, E, D, hmul, hD, hs, hvanish, hE, hlevel⟩ :=
      actual_distinct_product_structural_reduction A hpositive δ hδ hdensity hlength
    have h1 : f 1 = 0 := by
      have hh := hmul 1 1 (by norm_num) (by norm_num)
      norm_num at hh
      linarith
    apply density_bound_from_finite_smooth_levels A E D f δ (1 / Real.exp 1)
      hdensity hE h1 hmul hD hs hvanish hlevel
    intro P T hP hT hL
    exact finite_smooth_level_mass_bound (fun n => (f n : ℝ))
      (by simp [h1]) (fun m n hm hn => by simp only [hmul m n hm hn, Rat.cast_add])
      P T hP hT 1 (by norm_num) (fun s hs => by simp [hL s hs])
  · exact (le_of_not_gt hδ).trans (by positivity)


end Erdos786Audit

end

section
/- Source module: JigStatement.lean -/

/-! Adapter to the canonical statement displayed at Jig #172 statement 6. -/
namespace Erdos786CanonicalAdapter
open Filter Classical
open scoped Topology

noncomputable abbrev partialDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  ((((A ∩ Set.univ) ∩ Set.Iio n).ncard : ℕ) : ℝ) /
    ((((Set.univ : Set ℕ) ∩ Set.Iio n).ncard : ℕ) : ℝ)

def HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (partialDensity A) atTop (𝓝 δ)

def IsMulCardSet (A : Set ℕ) : Prop :=
  ∀ a b : Finset ℕ, (a : Set ℕ) ⊆ A → (b : Set ℕ) ⊆ A →
    a.prod id = b.prod id → a.card = b.card

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (δ : ℝ), 0 ∉ A → HasDensity A δ → IsMulCardSet A → δ ≤ Real.exp (-1)

theorem partialDensity_eq_range (A : Set ℕ) (n : ℕ) :
    partialDensity A n = (((Finset.range n).filter (fun k => k ∈ A)).card : ℝ) / n := by
  have hn : (A ∩ Set.univ) ∩ Set.Iio n =
      ((Finset.range n).filter (fun k => k ∈ A) : Set ℕ) := by
    ext k
    simp [and_comm]
  have hd : (Set.univ : Set ℕ) ∩ Set.Iio n = (Finset.range n : Set ℕ) := by
    ext k
    simp
  simp only [partialDensity, hn, hd, Set.ncard_coe_finset, Finset.card_range]

theorem mulCardSet_subtype (A : Set ℕ) (hA : IsMulCardSet A) :
    ∀ U V : Finset A, (∏ a ∈ U, (a : ℕ)) = (∏ a ∈ V, (a : ℕ)) → U.card = V.card := by
  intro U V he
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hh := hA (U.map e) (V.map e)
    (by intro n hn; obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hn; exact a.property)
    (by intro n hn; obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hn; exact a.property)
    (by simpa [e] using he)
  simpa using hh


theorem hasDensity_Icc (A : Set ℕ) (δ : ℝ) (h0 : 0 ∉ A) (hA : HasDensity A δ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (𝓝 δ) := by
  have hs : Tendsto (fun N : ℕ => partialDensity A (N + 1)) atTop (𝓝 δ) :=
    (tendsto_add_atTop_iff_nat 1).mpr hA
  have hr : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    field_simp
  have hh := hs.mul hr
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [] with N
  have hc : (Finset.range (N + 1)).filter (fun n => n ∈ A) =
      (Finset.Icc 1 N).filter (fun n => n ∈ A) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hn, ha⟩
      have : n ≠ 0 := fun he => h0 (he ▸ ha)
      exact ⟨by omega, ha⟩
    · rintro ⟨hn, ha⟩
      exact ⟨by omega, ha⟩
  rw [partialDensity_eq_range, hc]
  have hn : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem target : statement := by
  intro A δ h0 hd hmul
  have hb := Erdos786Audit.distinct_product_natural_density_le_inv_e A
    (fun n hn he => h0 (he ▸ hn)) δ (hasDensity_Icc A δ h0 hd) (mulCardSet_subtype A hmul)
  simpa only [Real.exp_neg, one_div] using hb


end Erdos786CanonicalAdapter

end

namespace Submissions.Erdos786DistinctDensityAtMostInvE.FreshQuotient
theorem proof : Erdos786CanonicalAdapter.statement :=
  Erdos786CanonicalAdapter.target
#print axioms proof
end Submissions.Erdos786DistinctDensityAtMostInvE.FreshQuotient
