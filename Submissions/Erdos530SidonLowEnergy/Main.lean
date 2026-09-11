import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos530SidonLowEnergy.Main

open scoped BigOperators


/-- The finite Bernoulli weight of a subset of `A`. -/
def subsetWeight {α : Type*} (A B : Finset α) (p : ℝ) : ℝ :=
  p ^ B.card * (1 - p) ^ (A.card - B.card)

/-- The total weight of subsets containing `e` is `p ^ e.card`.
This polynomial identity holds for every real `p`; the later averaging argument
uses `0 < p < 1` to ensure that every weight is positive. -/
theorem subsetWeight_containment {α : Type*} [DecidableEq α]
    (A e : Finset α) (p : ℝ) (he : e ⊆ A) :
    (∑ B ∈ A.powerset, subsetWeight A B p *
      (if e ⊆ B then (1 : ℝ) else 0)) = p ^ e.card := by
  classical
  have hterm (B : Finset α) (hB : B ∈ A.powerset) :
      (∏ x ∈ B, p) * (∏ x ∈ A \ B, if x ∈ e then (0 : ℝ) else 1 - p) =
        subsetWeight A B p * (if e ⊆ B then (1 : ℝ) else 0) := by
    have hBA : B ⊆ A := Finset.mem_powerset.mp hB
    by_cases heB : e ⊆ B
    · have hprod :
          (∏ x ∈ A \ B, if x ∈ e then (0 : ℝ) else 1 - p) =
            ∏ x ∈ A \ B, (1 - p) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hxe : x ∉ e := fun h => (Finset.mem_sdiff.mp hx).2 (heB h)
        simp only [hxe, if_false]
      rw [hprod]
      simp [subsetWeight, heB, Finset.card_sdiff_of_subset hBA]
    · have hex : ∃ x ∈ e, x ∉ B := by
        by_contra h
        apply heB
        intro x hxe
        by_contra hxB
        exact h ⟨x, hxe, hxB⟩
      obtain ⟨x, hxe, hxB⟩ := hex
      have hzero :
          (∏ y ∈ A \ B, if y ∈ e then (0 : ℝ) else 1 - p) = 0 :=
        Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨he hxe, hxB⟩) (by simp [hxe])
      simp [heB, hzero]
  have hleft :
      (∏ x ∈ A, (p + (if x ∈ e then (0 : ℝ) else 1 - p))) = p ^ e.card := by
    calc
      _ = ∏ x ∈ A, if x ∈ e then p else 1 := by
        apply Finset.prod_congr rfl
        intro x hx
        by_cases hxe : x ∈ e
        · simp [hxe]
        · simp only [hxe, if_false]
          ring
      _ = ∏ x ∈ A ∩ e, p := Finset.prod_ite_mem A e (fun _ => p)
      _ = p ^ e.card := by rw [Finset.inter_eq_right.mpr he]; simp
  calc
    _ = ∑ B ∈ A.powerset,
        (∏ x ∈ B, p) * (∏ x ∈ A \ B, if x ∈ e then (0 : ℝ) else 1 - p) := by
      exact Finset.sum_congr rfl fun B hB => (hterm B hB).symm
    _ = ∏ x ∈ A, (p + (if x ∈ e then (0 : ℝ) else 1 - p)) :=
      (Finset.prod_add (fun _ : α => p)
        (fun x => if x ∈ e then (0 : ℝ) else 1 - p) A).symm
    _ = p ^ e.card := hleft

/-- The finite Bernoulli weights sum to one. -/
theorem subsetWeight_sum {α : Type*} [DecidableEq α] (A : Finset α) (p : ℝ) :
    (∑ B ∈ A.powerset, subsetWeight A B p) = 1 := by
  simpa using subsetWeight_containment A ∅ p (Finset.empty_subset A)

open scoped BigOperators


theorem subsetWeight_pos {α : Type*} (A B : Finset α) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < subsetWeight A B p := by
  exact mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)

/-- The weighted number of sampled vertices is `p * A.card`. -/
theorem subsetWeight_card_moment {α : Type*} [DecidableEq α]
    (A : Finset α) (p : ℝ) :
    (∑ B ∈ A.powerset, (subsetWeight A B p * (B.card : ℝ))) = p * A.card := by
  classical
  have hcard (B : Finset α) (hBA : B ⊆ A) :
      (B.card : ℝ) = ∑ a ∈ A, (if a ∈ B then (1 : ℝ) else 0) := by
    have hfilter : A.filter (fun a => a ∈ B) = B := by
      ext a
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hBA h, h⟩⟩
    calc
      _ = ((A.filter (fun a => a ∈ B)).card : ℝ) := by rw [hfilter]
      _ = _ := Finset.natCast_card_filter (fun a => a ∈ B) A
  calc
    _ = ∑ B ∈ A.powerset, ∑ a ∈ A,
        (subsetWeight A B p * (if a ∈ B then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hcard B (Finset.mem_powerset.mp hB), Finset.mul_sum]
    _ = ∑ a ∈ A, ∑ B ∈ A.powerset,
        (subsetWeight A B p * (if a ∈ B then (1 : ℝ) else 0)) :=
      Finset.sum_comm
    _ = ∑ a ∈ A, p := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa only [Finset.singleton_subset_iff, Finset.card_singleton, pow_one] using
        subsetWeight_containment A {a} p (Finset.singleton_subset_iff.mpr ha)
    _ = p * A.card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Every edge contributes its exact containment moment. -/
theorem subsetWeight_edge_moment {α : Type*} [DecidableEq α]
    (A : Finset α) (H : Finset (Finset α)) (p : ℝ)
    (hH : ∀ e ∈ H, e ⊆ A) :
    (∑ B ∈ A.powerset,
      (subsetWeight A B p * ((H.filter (fun e => e ⊆ B)).card : ℝ))) =
        ∑ e ∈ H, p ^ e.card := by
  classical
  calc
    _ = ∑ B ∈ A.powerset, ∑ e ∈ H,
        (subsetWeight A B p * (if e ⊆ B then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.natCast_card_filter, Finset.mul_sum]
    _ = ∑ e ∈ H, ∑ B ∈ A.powerset,
        (subsetWeight A B p * (if e ⊆ B then (1 : ℝ) else 0)) :=
      Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun e he => subsetWeight_containment A e p (hH e he)

/-- Deleting one chosen vertex from each contained edge destroys every edge.
The family can have edges of different sizes. -/
theorem exists_subset_avoiding_edges_card {α : Type*} [DecidableEq α]
    (B : Finset α) (H : Finset (Finset α)) (hne : ∀ e ∈ H, e.Nonempty) :
    ∃ S ⊆ B, (∀ e ∈ H, ¬ e ⊆ S) ∧
      B.card ≤ S.card + (H.filter (fun e => e ⊆ B)).card := by
  classical
  let K := H.filter (fun e => e ⊆ B)
  let pick : {e : Finset α // e ∈ K} → α := fun e =>
    Classical.choose (hne e.1 (Finset.mem_filter.mp e.2).1)
  have hpick (e : {e : Finset α // e ∈ K}) : pick e ∈ e.1 :=
    Classical.choose_spec (hne e.1 (Finset.mem_filter.mp e.2).1)
  let D : Finset α := K.attach.image pick
  have hD : D.card ≤ K.card := by
    calc
      _ ≤ K.attach.card := Finset.card_image_le
      _ = K.card := Finset.card_attach
  refine ⟨B \ D, Finset.sdiff_subset, ?_, ?_⟩
  · intro e he hes
    have heB : e ⊆ B := hes.trans Finset.sdiff_subset
    have heK : e ∈ K := Finset.mem_filter.mpr ⟨he, heB⟩
    let e' : {e : Finset α // e ∈ K} := ⟨e, heK⟩
    have hchosen : pick e' ∈ B \ D := hes (hpick e')
    have hmemD : pick e' ∈ D :=
      Finset.mem_image.mpr ⟨e', Finset.mem_attach K e', rfl⟩
    exact (Finset.mem_sdiff.mp hchosen).2 hmemD
  · have hbase : B.card ≤ (B \ D).card + D.card :=
      Finset.card_le_card_sdiff_add_card
    exact hbase.trans (Nat.add_le_add_left hD _)

/-- Finite alteration with independent inclusion weight `p`.
This statement is purely about finite sets; no probability or hypergraph framework
is needed. Sidon obstruction classification and counting are separate steps. -/
theorem exists_subset_avoiding_edges {α : Type*} [DecidableEq α]
    (A : Finset α) (H : Finset (Finset α)) (p : ℝ)
    (hH : ∀ e ∈ H, e.Nonempty ∧ e ⊆ A) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ S ⊆ A, (∀ e ∈ H, ¬ e ⊆ S) ∧
      p * (A.card : ℝ) - (∑ e ∈ H, p ^ e.card) ≤ (S.card : ℝ) := by
  classical
  let score : Finset α → ℝ := fun B =>
    (B.card : ℝ) - ((H.filter (fun e => e ⊆ B)).card : ℝ)
  let t : ℝ := p * (A.card : ℝ) - (∑ e ∈ H, p ^ e.card)
  have havg :
      (∑ B ∈ A.powerset, (subsetWeight A B p * score B)) = t := by
    dsimp only [score, t]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, subsetWeight_card_moment A p,
      subsetWeight_edge_moment A H p (fun e he => (hH e he).2)]
  have hconst : (∑ B ∈ A.powerset, (subsetWeight A B p * t)) = t := by
    rw [← Finset.sum_mul, subsetWeight_sum A p, one_mul]
  have hsumle :
      (∑ B ∈ A.powerset, (subsetWeight A B p * t)) ≤
        ∑ B ∈ A.powerset, (subsetWeight A B p * score B) := by
    rw [hconst, havg]
  obtain ⟨B, hB, hscore⟩ :=
    Finset.exists_le_of_sum_le (Finset.powerset_nonempty A) hsumle
  have hscore' : t ≤ score B :=
    (mul_le_mul_iff_right₀ (subsetWeight_pos A B p hp0 hp1)).mp hscore
  obtain ⟨S, hSB, havoid, hcard⟩ :=
    exists_subset_avoiding_edges_card B H (fun e he => (hH e he).1)
  refine ⟨S, hSB.trans (Finset.mem_powerset.mp hB), havoid, ?_⟩
  have hcard_real : (B.card : ℝ) ≤
      ((S.card + (H.filter (fun e => e ⊆ B)).card : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcard
  rw [Nat.cast_add] at hcard_real
  change t ≤ (S.card : ℝ)
  dsimp only [score] at hscore'
  linarith only [hscore', hcard_real]

/-- Only the arithmetic budget for sparse-energy alteration.
The counting bounds and probabilistic existence argument are separate obligations. -/
theorem sparse_energy_budget {n E L M : ℝ}
    (hn : 256 ≤ n)
    (hE0 : 0 ≤ E) (hE : E ≤ n ^ 2 * Real.sqrt n / 4)
    (hL0 : 0 ≤ L) (hL : L ≤ Real.sqrt (n * E) / 2)
    (hM0 : 0 ≤ M) (hM : M ≤ E / 8) :
    Real.sqrt n ≤ (2 / Real.sqrt n) * n -
      (2 / Real.sqrt n) ^ 3 * L - (2 / Real.sqrt n) ^ 4 * M := by
  let s := Real.sqrt n
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg n
  have hs_sq : s ^ 2 = n := Real.sq_sqrt hn0
  have hs16 : 16 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith only [hn])
  have hspos : 0 < s := by linarith only [hs16]
  change E ≤ n ^ 2 * s / 4 at hE
  have h16s : 16 * s ≤ n := by
    nlinarith only [hs_sq, mul_nonneg hs0 (sub_nonneg.mpr hs16)]
  have hE64 : 64 * E ≤ n ^ 3 := by
    have hscaled := mul_le_mul_of_nonneg_left h16s (sq_nonneg n)
    nlinarith only [hE, hscaled]
  have hroot : Real.sqrt (n * E) ≤ n ^ 2 / 8 := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ n ^ 2 / 8)).mpr
    have hscaled := mul_le_mul_of_nonneg_left hE64 hn0
    nlinarith only [hscaled]
  have hL16 : 16 * L ≤ n ^ 2 := by linarith only [hL, hroot]
  have hthree : (2 / s) ^ 3 * L ≤ s / 2 := by
    rw [div_pow, div_mul_eq_mul_div₀]
    apply (div_le_iff₀ (pow_pos hspos 3)).mpr
    calc
      2 ^ 3 * L ≤ n ^ 2 / 2 := by nlinarith only [hL16]
      _ = (s / 2) * s ^ 3 := by rw [← hs_sq]; ring
  have hfour : (2 / s) ^ 4 * M ≤ s / 2 := by
    rw [div_pow, div_mul_eq_mul_div₀]
    apply (div_le_iff₀ (pow_pos hspos 4)).mpr
    calc
      2 ^ 4 * M ≤ 2 * E := by nlinarith only [hM]
      _ ≤ n ^ 2 * s / 2 := by linarith only [hE]
      _ = (s / 2) * s ^ 4 := by rw [← hs_sq]; ring
  have hfirst : (2 / s) * n = 2 * s := by
    rw [← hs_sq, pow_two, ← mul_assoc, div_mul_cancel₀ _ hspos.ne']
  change s ≤ (2 / s) * n - (2 / s) ^ 3 * L - (2 / s) ^ 4 * M
  linarith only [hfirst, hthree, hfour]

/-- The original real-domain Sidon predicate, including repeated summands. -/
def IsSidon (S : Finset ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- All points of the support must occur in the equal-sum relation. -/
def IsSumSupport (S : Finset ℝ) : Prop :=
  ∃ a b c d : ℝ, S = {a, b, c, d} ∧ a + b = c + d

/-- Exact k-point supports, not k-sets merely containing a smaller obstruction. -/
noncomputable def edges (A : Finset ℝ) (k : ℕ) : Finset (Finset ℝ) := by
  classical
  exact (A.powersetCard k).filter IsSumSupport

/-
Scoped source intake: read all of the parent-authored SparseDefs.lean before use,
SHA-256 5605a2714e6a554199fd219ddb5fc50118a59a61cdf1033636d061adea5d35e0.
Its real IsSidon retains repeated summands; IsSumSupport requires equality with
the full four-term support. Read the relevant card/insert and powersetCard proofs
in the fixed private Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
Data/Finset/Card.lean SHA-256
174ec68882bf10567b17c3f4d278d6647cef92574dadfa8f7f0821b949967c8f;
Data/Finset/Powerset.lean SHA-256
ffe38ab68a55fd3c24524e502afab8dad28588fb899157deae3976f24ff16b27.
The proof below is independently derived finite algebra. This intake adds no
execution authorization: the parent alone compiles and audits the final source.
-/


/-- Membership means an exact support of the indicated cardinality. -/
theorem mem_edges {A e : Finset ℝ} {k : ℕ} :
    e ∈ edges A k ↔ e ⊆ A ∧ e.card = k ∧ IsSumSupport e := by
  classical
  simp only [edges, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

/-- A nontrivial real pair-sum collision has exactly three or four support points.
The three-point case includes repeated summands. -/
theorem card_sum_support_of_nontrivial {a b c d : ℝ}
    (hsum : a + b = c + d)
    (hbad : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    ({a, b, c, d} : Finset ℝ).card = 3 ∨
      ({a, b, c, d} : Finset ℝ).card = 4 := by
  classical
  have hac : a ≠ c := by
    intro h
    exact hbad (Or.inl ⟨h, by linarith only [hsum, h]⟩)
  have had : a ≠ d := by
    intro h
    exact hbad (Or.inr ⟨h, by linarith only [hsum, h]⟩)
  have hbc : b ≠ c := by
    intro h
    exact hbad (Or.inr ⟨by linarith only [hsum, h], h⟩)
  have hbd : b ≠ d := by
    intro h
    exact hbad (Or.inl ⟨by linarith only [hsum, h], h⟩)
  by_cases hab : a = b
  · subst b
    have hcd : c ≠ d := by
      intro h
      apply hac
      linarith only [hsum, h]
    left
    simp [hac, had, hcd]
  · by_cases hcd : c = d
    · subst d
      left
      simp [hab, hac, hbc]
    · right
      simp [hab, hac, had, hbc, hbd, hcd]

/-- Every failure of the canonical Sidon property contains an exact obstruction. -/
theorem not_isSidon_exists_sum_support (S : Finset ℝ) (hS : ¬ IsSidon S) :
    ∃ e ⊆ S, (e.card = 3 ∨ e.card = 4) ∧ IsSumSupport e := by
  classical
  by_contra hnone
  apply hS
  intro a b c d ha hb hc hd hsum
  by_contra hbad
  apply hnone
  refine ⟨{a, b, c, d}, ?_, card_sum_support_of_nontrivial hsum hbad, ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb, hc, hd⟩
  · exact ⟨a, b, c, d, rfl, hsum⟩

/-- In particular, repeated-summand collisions cannot obstruct a set of size at most two. -/
theorem isSidon_of_card_le_two {S : Finset ℝ} (hcard : S.card ≤ 2) : IsSidon S := by
  classical
  by_contra hS
  obtain ⟨e, heS, hecard, _⟩ := not_isSidon_exists_sum_support S hS
  have hle : e.card ≤ 2 := (Finset.card_le_card heS).trans hcard
  rcases hecard with hecard | hecard <;> simp [hecard] at hle

/-- A failure inside `S ⊆ A` produces a member of the exact-support edge families. -/
theorem not_isSidon_exists_edge {A S : Finset ℝ} (hSA : S ⊆ A) (hS : ¬ IsSidon S) :
    ∃ e ∈ edges A 3 ∪ edges A 4, e ⊆ S := by
  classical
  obtain ⟨e, heS, hecard, hesupport⟩ := not_isSidon_exists_sum_support S hS
  have heA : e ⊆ A := heS.trans hSA
  refine ⟨e, ?_, heS⟩
  rcases hecard with hecard | hecard
  · exact Finset.mem_union.mpr (Or.inl (mem_edges.mpr ⟨heA, hecard, hesupport⟩))
  · exact Finset.mem_union.mpr (Or.inr (mem_edges.mpr ⟨heA, hecard, hesupport⟩))

/-- Avoiding both exact three- and four-point sum supports gives canonical Sidon. -/
theorem isSidon_of_avoids_edges {A S : Finset ℝ} (hSA : S ⊆ A)
    (havoid : ∀ e ∈ edges A 3 ∪ edges A 4, ¬ e ⊆ S) : IsSidon S := by
  classical
  by_contra hS
  obtain ⟨e, he, heS⟩ := not_isSidon_exists_edge hSA hS
  exact havoid e he heS

/- Scoped intake: read all of SparseDefs.lean and SidonObstructions.lean.
SparseDefs SHA-256: 5605a2714e6a554199fd219ddb5fc50118a59a61cdf1033636d061adea5d35e0.
SidonObstructions SHA-256: 30535e4280c76e068e5803b0b02fd9b9bfb8277244d72e09cbe3ed1440976369.
Read the existing restricted-pair energy theorem and its proof in pinned Mathlib
Combinatorics/Additive/Energy.lean, SHA-256
cae1b5c3e605db63615a7cf9f0f7604183c14d09767d40366df6b6680fb8dbf0.
No external claim or source text grants execution authority. Only the parent
compiles this candidate. This source performs no native evaluation or custom
metaprogram execution and introduces no axioms or admissions. -/


/-- An exact three-point equal-sum support is an arithmetic progression.
The midpoint is written first; only the two endpoints need be distinguished here. -/
theorem three_support_is_progression {S : Finset ℝ} (hcard : S.card = 3)
    (hsupport : IsSumSupport S) :
    ∃ y x z : ℝ, S = {y, x, z} ∧ x ≠ z ∧ x + z = y + y := by
  classical
  obtain ⟨a, b, c, d, rfl, heq⟩ := hsupport
  by_cases hab : a = b
  · subst b
    refine ⟨a, c, d, by simp, ?_, heq.symm⟩
    intro hcd
    have hac : a = c := by linarith
    subst d
    subst c
    simp at hcard
  by_cases hcd : c = d
  · subst d
    refine ⟨c, a, b, ?_, hab, heq⟩
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have no_cross (w x y z : ℝ) (hsum : w + x = y + z)
      (hc : ({w, x, y, z} : Finset ℝ).card = 3) : w ≠ y := by
    intro hwy
    have hxz : x = z := by linarith
    have hs : ({w, x, y, z} : Finset ℝ) = {w, x} := by
      ext u
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [← hwy, ← hxz]
      tauto
    rw [hs] at hc
    have hle : ({w, x} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    omega
  have hac : a ≠ c := no_cross a b c d heq hcard
  have had : a ≠ d := no_cross a b d c (by linarith) (by
    simpa only [Finset.insert_comm, Finset.pair_comm] using hcard)
  have hbc : b ≠ c := no_cross b a c d (by linarith) (by
    simpa only [Finset.insert_comm, Finset.pair_comm] using hcard)
  have hbd : b ≠ d := no_cross b a d c (by linarith) (by
    simpa only [Finset.insert_comm, Finset.pair_comm] using hcard)
  have hfour : ({a, b, c, d} : Finset ℝ).card = 4 := by
    simp [hab, hac, had, hbc, hbd, hcd]
  omega

/-- Each three-point edge supplies two ordered endpoint pairs with a midpoint in A.
The endpoint pair determines its midpoint and therefore its entire support. -/
theorem two_mul_three_edges_le_midpoint_pairs (A : Finset ℝ) :
    2 * (edges A 3).card ≤
      ((A ×ˢ A).filter fun p => p.1 + p.2 ∈ A.image (fun a => a + a)).card := by
  classical
  let I := {S : Finset ℝ // S ∈ edges A 3}
  let target := (A ×ˢ A).filter fun p => p.1 + p.2 ∈ A.image (fun a => a + a)
  change 2 * (edges A 3).card ≤ target.card
  have hm (S : I) : S.val ⊆ A ∧ S.val.card = 3 ∧ IsSumSupport S.val :=
    mem_edges.mp S.property
  have hex (S : I) : ∃ y x z : ℝ,
      S.val = {y, x, z} ∧ x ≠ z ∧ x + z = y + y :=
    three_support_is_progression (hm S).2.1 (hm S).2.2
  choose y x z hshape hne hsum using hex
  have same_support (S T : I)
      (h : (x S = x T ∧ z S = z T) ∨ (x S = z T ∧ z S = x T)) : S = T := by
    have hs := hsum S
    have ht := hsum T
    rcases h with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · have hy : y S = y T := by linarith
      apply Subtype.ext
      rw [hshape S, hshape T, hy, hx, hz]
    · have hy : y S = y T := by linarith
      apply Subtype.ext
      rw [hshape S, hshape T, hy, hx, hz]
      ext u
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  have hpairs (S : I) : (x S, z S) ∈ target ∧ (z S, x S) ∈ target := by
    have hyA : y S ∈ A := (hm S).1 (by rw [hshape S]; simp)
    have hxA : x S ∈ A := (hm S).1 (by rw [hshape S]; simp)
    have hzA : z S ∈ A := (hm S).1 (by rw [hshape S]; simp)
    have hmid : x S + z S ∈ A.image (fun a => a + a) :=
      Finset.mem_image.mpr ⟨y S, hyA, (hsum S).symm⟩
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxA, hzA⟩, hmid⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzA, hxA⟩,
        by simpa only [add_comm] using hmid⟩
  let f : I × Bool → ↥target := fun p =>
    if p.2 then ⟨(z p.1, x p.1), (hpairs p.1).2⟩
    else ⟨(x p.1, z p.1), (hpairs p.1).1⟩
  have hf : Function.Injective f := by
    rintro ⟨S, b⟩ ⟨T, c⟩ h
    have hv := congrArg Subtype.val h
    cases b <;> cases c <;> dsimp [f] at hv
    · have hST := same_support S T
        (Or.inl ⟨congrArg Prod.fst hv, congrArg Prod.snd hv⟩)
      exact Prod.ext hST rfl
    · have hx := congrArg Prod.fst hv
      have hz := congrArg Prod.snd hv
      have hST := same_support S T (Or.inr ⟨hx, hz⟩)
      subst T
      exact (hne S hx).elim
    · have hz := congrArg Prod.fst hv
      have hx := congrArg Prod.snd hv
      have hST := same_support S T (Or.inr ⟨hx, hz⟩)
      subst T
      exact (hne S hx).elim
    · have hST := same_support S T
        (Or.inl ⟨congrArg Prod.snd hv, congrArg Prod.fst hv⟩)
      exact Prod.ext hST rfl
  have hc := Fintype.card_le_of_injective f hf
  simpa only [I, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe,
    Nat.mul_comm] using hc

/-- Three-point Sidon obstructions are controlled by additive energy.
Mathlib's existing restricted-pair Cauchy--Schwarz inequality supplies the analytic step. -/
theorem three_edges_energy_bound (A : Finset ℝ) :
    4 * (edges A 3).card ^ 2 ≤ A.card * Finset.addEnergy A A := by
  classical
  have hdbl : (A.image (fun a => a + a)).card = A.card :=
    Finset.card_image_of_injective A (by intro a b h; linarith)
  have hE := Finset.card_sq_le_card_mul_addEnergy A A (A.image (fun a => a + a))
  rw [hdbl] at hE
  calc
    4 * (edges A 3).card ^ 2 = (2 * (edges A 3).card) ^ 2 := by ring
    _ ≤ ((A ×ˢ A).filter fun p => p.1 + p.2 ∈ A.image (fun a => a + a)).card ^ 2 :=
      Nat.pow_le_pow_left (two_mul_three_edges_le_midpoint_pairs A) 2
    _ ≤ A.card * Finset.addEnergy A A := hE

open scoped BigOperators

theorem four_card_distinct {a b c d : ℝ} (h : ({a, b, c, d} : Finset ℝ).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  simp only [Finset.card_insert_eq_ite, Finset.card_singleton,
    Finset.mem_insert, Finset.mem_singleton] at h
  split_ifs at h <;> simp_all

/-- Each exact four-point sum support accounts for eight ordered energy quadruples. -/
theorem four_edges_energy_bound (A : Finset ℝ) :
    8 * (edges A 4).card ≤ Finset.addEnergy A A := by
  classical
  let Q := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2
  let support : (ℝ × ℝ) × (ℝ × ℝ) → Finset ℝ :=
    fun q => {q.1.1, q.1.2, q.2.1, q.2.2}
  have hfiber (S : Finset ℝ) (hS : S ∈ edges A 4) :
      8 ≤ (Q.filter fun q => support q = S).card := by
    obtain ⟨hSA, hsupport⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSA, hcard⟩ := Finset.mem_powersetCard.mp hSA
    obtain ⟨a, b, c, d, rfl, habcd⟩ := hsupport
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := four_card_distinct hcard
    have ha : a ∈ A := hSA (by simp)
    have hb : b ∈ A := hSA (by simp)
    have hc : c ∈ A := hSA (by simp)
    have hd : d ∈ A := hSA (by simp)
    let T : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
      {((a,b),(c,d)), ((b,a),(c,d)), ((a,b),(d,c)), ((b,a),(d,c)),
       ((c,d),(a,b)), ((d,c),(a,b)), ((c,d),(b,a)), ((d,c),(b,a))}
    have hTcard : T.card = 8 := by
      simp [T, hab, hac, had, hbc, hbd, hcd]
    have hT : T ⊆ Q.filter fun q => support q = {a,b,c,d} := by
      intro q hq
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Q, support, ha, hb, hc, hd, habcd, add_comm, Finset.insert_comm] <;>
          ext x <;> simp [or_assoc, or_left_comm, or_comm]
    exact hTcard ▸ Finset.card_le_card hT
  calc
    8 * (edges A 4).card = ∑ _S ∈ edges A 4, 8 := by simp [mul_comm]
    _ ≤ ∑ S ∈ edges A 4, (Q.filter fun q => support q = S).card :=
      Finset.sum_le_sum hfiber
    _ = (Q.filter fun q => support q ∈ edges A 4).card :=
      Finset.sum_card_fiberwise_eq_card_filter Q (edges A 4) support
    _ ≤ Q.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = Finset.addEnergy A A := (Finset.addEnergy_eq_card_filter A A).symm

/-
Scoped intake: read the current complete local sources before reuse.
SidonObstructions.lean SHA-256:
30535e4280c76e068e5803b0b02fd9b9bfb8277244d72e09cbe3ed1440976369.
Alteration.lean SHA-256:
4b98bda139443fbd647fe779b0acdc8e63c708a10cb2c561ee55a8c31e6a1671.
Both use the already pinned private Mathlib source. This file only specializes
their finite statements; edge-energy estimates remain separate dependencies.
No build or execution is performed by this source-authoring handoff.
-/

open scoped BigOperators


/-- Finite Sidon alteration, counting exact three- and four-point sum supports. -/
theorem exists_sidon_subset_alteration (A : Finset ℝ) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ S ⊆ A, IsSidon S ∧
      p * (A.card : ℝ) - p ^ 3 * ((edges A 3).card : ℝ) -
        p ^ 4 * ((edges A 4).card : ℝ) ≤ (S.card : ℝ) := by
  classical
  have hdisj : Disjoint (edges A 3) (edges A 4) := by
    apply Finset.disjoint_left.mpr
    intro e he3 he4
    have h3 : e.card = 3 := (mem_edges.mp he3).2.1
    have h4 : e.card = 4 := (mem_edges.mp he4).2.1
    exact (by decide : (3 : ℕ) ≠ 4) (h3.symm.trans h4)
  have hH : ∀ e ∈ edges A 3 ∪ edges A 4, e.Nonempty ∧ e ⊆ A := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have hem := mem_edges.mp he
      refine ⟨Finset.card_pos.mp ?_, hem.1⟩
      rw [hem.2.1]
      decide
    · have hem := mem_edges.mp he
      refine ⟨Finset.card_pos.mp ?_, hem.1⟩
      rw [hem.2.1]
      decide
  have hsum (k : ℕ) :
      (∑ e ∈ edges A k, p ^ e.card) = p ^ k * ((edges A k).card : ℝ) := by
    calc
      _ = ∑ e ∈ edges A k, p ^ k := by
        apply Finset.sum_congr rfl
        intro e he
        rw [(mem_edges.mp he).2.1]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  obtain ⟨S, hSA, havoid, hcard⟩ :=
    exists_subset_avoiding_edges A (edges A 3 ∪ edges A 4) p hH hp0 hp1
  refine ⟨S, hSA, isSidon_of_avoids_edges hSA havoid, ?_⟩
  rw [Finset.sum_union hdisj, hsum 3, hsum 4] at hcard
  linarith only [hcard]

/-- The full square-root lower bound for every sufficiently low-energy real set.
The unrestricted high-energy case remains outside this theorem. -/
theorem exists_sidon_of_small_energy (A : Finset ℝ) (hn : 256 ≤ A.card)
    (hE : (Finset.addEnergy A A : ℝ) ≤ (A.card : ℝ) ^ 2 * Real.sqrt A.card / 4) :
    ∃ S : Finset ℝ, S ⊆ A ∧ IsSidon S ∧ Real.sqrt A.card ≤ (S.card : ℝ) := by
  have hnR : (256 : ℝ) ≤ A.card := by exact_mod_cast hn
  have hs16 : (16 : ℝ) ≤ Real.sqrt A.card := Real.le_sqrt_of_sq_le (by norm_num; exact hn)
  have hspos : 0 < Real.sqrt A.card := by linarith
  let p : ℝ := 2 / Real.sqrt A.card
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by
    dsimp [p]
    apply (div_lt_iff₀ hspos).mpr
    linarith
  have hthree : (4 : ℝ) * ((edges A 3).card : ℝ) ^ 2 ≤
      (A.card : ℝ) * Finset.addEnergy A A := by
    exact_mod_cast three_edges_energy_bound A
  have hL : ((edges A 3).card : ℝ) ≤
      Real.sqrt ((A.card : ℝ) * Finset.addEnergy A A) / 2 := by
    have h := Real.le_sqrt_of_sq_le (show (2 * ((edges A 3).card : ℝ)) ^ 2 ≤
        (A.card : ℝ) * Finset.addEnergy A A by nlinarith only [hthree])
    linarith only [h]
  have hfour : (8 : ℝ) * (edges A 4).card ≤ Finset.addEnergy A A := by
    exact_mod_cast four_edges_energy_bound A
  have hM : ((edges A 4).card : ℝ) ≤ (Finset.addEnergy A A : ℝ) / 8 := by
    linarith only [hfour]
  have hbudget := sparse_energy_budget hnR (Nat.cast_nonneg _) hE
    (Nat.cast_nonneg _) hL (Nat.cast_nonneg _) hM
  obtain ⟨S, hSA, hS, hsize⟩ := exists_sidon_subset_alteration A p hp0 hp1
  exact ⟨S, hSA, hS, hbudget.trans hsize⟩

abbrev statement : Prop :=
  ∀ A : Finset ℝ, 256 ≤ A.card →
    (Finset.addEnergy A A : ℝ) ≤ (A.card : ℝ) ^ 2 * Real.sqrt A.card / 4 →
    ∃ S : Finset ℝ, S ⊆ A ∧ IsSidon S ∧ Real.sqrt A.card ≤ (S.card : ℝ)

theorem proof : statement := exists_sidon_of_small_energy

end Submissions.Erdos530SidonLowEnergy.Main
