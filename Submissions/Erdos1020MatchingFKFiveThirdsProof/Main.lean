import Mathlib.Data.Fintype.Sum
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Prod
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Order.Interval.Finset.Nat

-- Source: RainbowShift.lean
namespace Submissions.Erdos1020RainbowShift.Main

variable {α ι : Type*} [DecidableEq α]

private theorem image_swap_of_mem_of_notMem {s : Finset α} {i j : α}
    (hi : i ∈ s) (hj : j ∉ s) :
    s.image (Equiv.swap i j) = insert j s \ {i} := by
  apply Finset.coe_injective
  simpa only [Finset.coe_image, Finset.coe_sdiff, Finset.coe_insert,
    Finset.coe_singleton] using
    (Equiv.image_swap_of_mem_of_notMem (s := (s : Set α)) hi hj)

/-- A disjoint selection from equally shifted families pulls back to a disjoint
selection from the original families. No uniformity or finiteness of the color
type is required. Together with `UV.card_compression` and
`Set.Sized.uvCompression`, this is the ordinary singleton-shift step in HLS. -/
theorem exists_rainbow_of_singleton_compression
    (F : ι → Finset (Finset α)) (i j : α) (e : ι → Finset α)
    (he : ∀ c, e c ∈ UV.compression {j} {i} (F c))
    (hd : Pairwise (fun c d => Disjoint (e c) (e d))) :
    ∃ f : ι → Finset α, (∀ c, f c ∈ F c) ∧
      Pairwise (fun c d => Disjoint (f c) (f d)) := by
  classical
  by_cases hall : ∀ c, e c ∈ F c
  · exact ⟨e, hall, hd⟩
  push Not at hall
  obtain ⟨a, ha⟩ := hall
  have hja : j ∈ e a := Finset.singleton_subset_iff.mp
    (UV.le_of_mem_compression_of_notMem (he a) ha)
  have hia : i ∉ e a := Finset.disjoint_singleton_left.mp
    (UV.disjoint_of_mem_compression_of_notMem (he a) ha)
  refine ⟨fun c => (e c).image (Equiv.swap i j), ?_, ?_⟩
  · intro c
    change (e c).image (Equiv.swap i j) ∈ F c
    by_cases hca : c = a
    · subst c
      rw [Equiv.swap_comm i j, image_swap_of_mem_of_notMem hja hia]
      simpa only [Finset.sup_eq_union, Finset.union_singleton] using
        UV.sup_sdiff_mem_of_mem_compression_of_notMem (he a) ha
    · have hjc : j ∉ e c := Finset.disjoint_left.mp (hd (Ne.symm hca)) hja
      by_cases hic : i ∈ e c
      · rw [image_swap_of_mem_of_notMem hic hjc]
        simpa only [Finset.sup_eq_union, Finset.union_singleton] using
          UV.sup_sdiff_mem_of_mem_compression (he c)
            (Finset.singleton_subset_iff.mpr hic)
            (Finset.disjoint_singleton_left.mpr hjc)
      · have hc : e c ∈ F c := by
          by_contra hbad
          exact hjc (Finset.singleton_subset_iff.mp
            (UV.le_of_mem_compression_of_notMem (he c) hbad))
        have hfix : (e c).image (Equiv.swap i j) = e c := by
          calc
            (e c).image (Equiv.swap i j) = (e c).image id := by
              apply Finset.image_congr
              intro z hz
              exact Equiv.swap_apply_of_ne_of_ne
                (ne_of_mem_of_not_mem hz hic) (ne_of_mem_of_not_mem hz hjc)
            _ = e c := Finset.image_id
        rwa [hfix]
  · intro c d hcd
    exact (Finset.disjoint_image (Equiv.swap i j).injective).mpr (hd hcd)

private theorem isCompressed_iff_closed {F : Finset (Finset α)}
    {u v : Finset α} :
    UV.IsCompressed u v F ↔ ∀ e ∈ F, UV.compress u v e ∈ F := by
  constructor
  · intro h e he
    rw [← h.eq]
    exact UV.compress_mem_compression he
  · intro h
    change UV.compression u v F = F
    ext e
    rw [UV.mem_compression]
    constructor
    · rintro (⟨he, _⟩ | ⟨_, f, hf, rfl⟩)
      · exact he
      · exact h f hf
    · intro he
      exact Or.inl ⟨he, h e he⟩

/-- Shifting away from one source preserves stability under every earlier
shift away from that source. Equal vertices are allowed. -/
theorem isCompressed_singleton_compression_same_source
    {F : Finset (Finset α)} {a b z : α}
    (hF : UV.IsCompressed {a} {z} F) :
    UV.IsCompressed {a} {z} (UV.compression {b} {z} F) := by
  apply isCompressed_iff_closed.mpr
  intro e he
  unfold UV.compress
  split_ifs with h
  · have heF : e ∈ F := UV.mem_of_mem_compression he h.2 (by simp)
    have htF := isCompressed_iff_closed.mp hF e heF
    rw [UV.compress_of_disjoint_of_le h.1 h.2] at htF
    have hfix : UV.compress {b} {z} ((e ⊔ {a}) \ {z}) =
        (e ⊔ {a}) \ {z} := by
      simp [UV.compress, Finset.singleton_subset_iff]
    exact UV.mem_compression.mpr (Or.inl ⟨htF, by rwa [hfix]⟩)
  · exact he

/-- After a finite sequence of shifts away from `z`, every destination used
in the sequence is stable. Repeated destinations and `z` itself are allowed. -/
theorem isCompressed_foldr_singleton_same_source
    (F : Finset (Finset α)) (z : α) (L : List α) :
    ∀ a ∈ L, UV.IsCompressed {a} {z}
      (L.foldr (fun b G => UV.compression {b} {z} G) F) := by
  induction L with
  | nil => simp
  | cons b L ih =>
    intro a ha
    simp only [List.mem_cons] at ha
    simp only [List.foldr_cons]
    rcases ha with rfl | ha
    · exact UV.compression_idem _ _ _
    · exact isCompressed_singleton_compression_same_source (ih a ha)

/-- A finite sequence of equally applied singleton shifts preserves the
absence of a rainbow matching, expressed as the constructive pullback. -/
theorem exists_rainbow_of_foldr_singleton_compression
    (F : ι → Finset (Finset α)) (z : α) (L : List α) (e : ι → Finset α)
    (he : ∀ c, e c ∈ L.foldr (fun b G => UV.compression {b} {z} G) (F c))
    (hd : Pairwise (fun c d => Disjoint (e c) (e d))) :
    ∃ f : ι → Finset α, (∀ c, f c ∈ F c) ∧
      Pairwise (fun c d => Disjoint (f c) (f d)) := by
  induction L generalizing e with
  | nil => exact ⟨e, he, hd⟩
  | cons b L ih =>
    obtain ⟨f, hf, hfd⟩ := exists_rainbow_of_singleton_compression
      (fun c => L.foldr (fun b G => UV.compression {b} {z} G) (F c))
      z b e he hd
    exact ih f hf hfd

end Submissions.Erdos1020RainbowShift.Main

-- Source: ShiftNormalizeBody.lean
namespace Submissions.Erdos1020ShiftNormalize.Main

open Finset

def Uniform {α : Type*} (H : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {α : Type*} (H : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

theorem uniform_singleton_compression {α : Type*} [DecidableEq α]
    {H : Finset (Finset α)} {r : ℕ} (hH : Uniform H r) (i j : α) :
    Uniform (UV.compression {i} {j} H) r :=
  Set.Sized.uvCompression (by simp) hH

/-- Positive uniform families remain matching-free after an ordinary shift. -/
theorem matchingFree_singleton_compression {α : Type*} [DecidableEq α]
    {H : Finset (Finset α)} {r k : ℕ}
    (hr : 0 < r) (hH : Uniform H r) (hfree : MatchingFree H k) (i j : α) :
    MatchingFree (UV.compression {i} {j} H) k := by
  classical
  rintro ⟨M, hM, hcard, hd⟩
  obtain ⟨f, hf, hfd⟩ :=
    Submissions.Erdos1020RainbowShift.Main.exists_rainbow_of_singleton_compression
      (fun _ : M => H) j i (fun c : M => c.val)
      (fun c => hM c.property) (by
        intro c d hcd
        exact hd c.val c.property d.val d.property (fun h => hcd (Subtype.ext h)))
  have hinj : Function.Injective f := by
    intro c d hcd
    by_contra hne
    have hself : Disjoint (f c) (f c) := by simpa only [hcd] using hfd hne
    have hempty : f c = ∅ := disjoint_self.mp hself
    have hc := hH (f c) (hf c)
    rw [hempty, Finset.card_empty] at hc
    omega
  apply hfree
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp he
    exact hf c
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    exact hcard
  · intro e he d hd' hed
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hd'
    exact hfd (fun h => hed (congrArg f h))

/-- The label sum used to terminate downward singleton shifts. -/
def weight {n : ℕ} (H : Finset (Finset (Fin n))) : ℕ :=
  ∑ e ∈ H, ∑ x ∈ e, x.val

theorem edge_weight_compress_lt {n : ℕ} {i j : Fin n} (hij : i < j)
    {e : Finset (Fin n)} (hne : UV.compress {i} {j} e ≠ e) :
    (∑ x ∈ UV.compress {i} {j} e, x.val) < ∑ x ∈ e, x.val := by
  unfold UV.compress at hne ⊢
  split_ifs with h
  · have hi : i ∉ e := Finset.disjoint_singleton_left.mp h.1
    have hj : j ∈ e := Finset.singleton_subset_iff.mp h.2
    have hij' : i ≠ j := ne_of_lt hij
    rw [Finset.sup_eq_union, Finset.union_singleton,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne hij',
      Finset.sum_insert (Finset.notMem_mono (Finset.erase_subset _ _) hi)]
    have heq := Finset.sum_erase_add e (fun x : Fin n => x.val) hj
    have hval : i.val < j.val := hij
    omega
  · exact (hne (if_neg h)).elim

/-- A nontrivial downward shift strictly reduces the family label sum. -/
theorem weight_singleton_compression_lt {n : ℕ} {i j : Fin n} (hij : i < j)
    {H : Finset (Finset (Fin n))} (hne : UV.compression {i} {j} H ≠ H) :
    weight (UV.compression {i} {j} H) < weight H := by
  rw [UV.compression] at hne ⊢
  have hmove : ∀ e ∈ {e ∈ H | UV.compress {i} {j} e ∉ H},
      UV.compress {i} {j} e ≠ e := by
    intro e he heq
    exact (Finset.mem_filter.mp he).2 (heq.symm ▸ (Finset.mem_filter.mp he).1)
  have hpartition : {e ∈ H | UV.compress {i} {j} e ∈ H} ∪
      {e ∈ H | UV.compress {i} {j} e ∉ H} = H :=
    Finset.filter_union_filter_not_eq _ _
  have hnonempty : {e ∈ H | UV.compress {i} {j} e ∉ H}.Nonempty := by
    contrapose! hne
    rw [Finset.filter_image, hne, Finset.image_empty, Finset.union_empty]
    rwa [hne, Finset.union_empty] at hpartition
  rw [weight, weight, Finset.sum_union UV.compress_disjoint]
  conv_rhs => rw [← hpartition]
  rw [Finset.sum_union (Finset.disjoint_filter_filter_not _ _ _),
    add_lt_add_iff_left, Finset.filter_image, Finset.sum_image UV.compress_injOn]
  exact Finset.sum_lt_sum_of_nonempty hnonempty fun e he =>
    edge_weight_compress_lt hij (hmove e he)

private theorem compression_eq_of_uniform_zero {α : Type*} [DecidableEq α]
    {H : Finset (Finset α)} (hH : Uniform H 0) (i j : α) :
    UV.compression {i} {j} H = H := by
  have hfix : ∀ e ∈ H, UV.compress {i} {j} e = e := by
    intro e he
    have heq : e = ∅ := Finset.card_eq_zero.mp (hH e he)
    subst e
    simp [UV.compress]
  ext e
  rw [UV.mem_compression]
  constructor
  · rintro (⟨he, _⟩ | ⟨_, f, hf, rfl⟩)
    · exact he
    · rwa [hfix f hf]
  · intro he
    exact Or.inl ⟨he, by rwa [hfix e he]⟩

/-- Every uniform matching-free family admits a downward-shifted family with
the same cardinality, uniformity and forbidden matching size. -/
theorem exists_shifted {n r k : ℕ} (H : Finset (Finset (Fin n)))
    (hH : Uniform H r) (hfree : MatchingFree H k) :
    ∃ H' : Finset (Finset (Fin n)), H'.card = H.card ∧ Uniform H' r ∧
      MatchingFree H' k ∧ ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H' := by
  classical
  let candidates : Finset (Finset (Finset (Fin n))) :=
    Finset.univ.filter (fun G => G.card = H.card ∧ Uniform G r ∧ MatchingFree G k)
  have hmem : H ∈ candidates := by simp [candidates, hH, hfree]
  obtain ⟨G, hG, hmin⟩ := Finset.exists_min_image candidates weight ⟨H, hmem⟩
  have hprops := (Finset.mem_filter.mp hG).2
  refine ⟨G, hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  intro i j hij
  change UV.compression {i} {j} G = G
  by_contra hne
  have hr : 0 < r := by
    by_contra hz
    have hr0 : r = 0 := by omega
    exact hne (compression_eq_of_uniform_zero (hr0 ▸ hprops.2.1) i j)
  have hcomp : UV.compression {i} {j} G ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_,
      uniform_singleton_compression hprops.2.1 i j,
      matchingFree_singleton_compression hr hprops.2.1 hprops.2.2 i j⟩
    simpa only [UV.card_compression] using hprops.1
  exact (not_lt_of_ge (hmin _ hcomp)) (weight_singleton_compression_lt hij hne)

theorem card_shadow_singleton_compression_le {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (i j : α) :
    (Finset.shadow (UV.compression {i} {j} H)).card ≤ (Finset.shadow H).card := by
  apply UV.card_shadow_compression_le
  intro x hx
  have hx' : x = i := Finset.mem_singleton.mp hx
  subst x
  refine ⟨j, Finset.mem_singleton_self _, ?_⟩
  simpa only [Finset.erase_singleton] using UV.isCompressed_self (∅ : Finset α) H

end Submissions.Erdos1020ShiftNormalize.Main

namespace Submissions.Erdos1020RainbowLift.Main

variable {α ι : Type*} [DecidableEq α]

/-- A stable family permits replacing its distinguished vertex by any fresh
vertex. The replacement may be the distinguished vertex itself. -/
theorem insert_mem_of_singleton_stable {F : Finset (Finset α)} {s : Finset α}
    {x z : α} (hF : UV.IsCompressed {x} {z} F) (hz : z ∉ s) (hx : x ∉ s)
    (hs : insert z s ∈ F) : insert x s ∈ F := by
  by_cases hxz : x = z
  · simpa only [hxz] using hs
  have hcomp : UV.compress {x} {z} (insert z s) = insert x s := by
    rw [UV.compress_of_disjoint_of_le
      (Finset.disjoint_singleton_left.mpr (by simp [hxz, hx]))
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self z s))]
    simp [Finset.sup_eq_union, Finset.union_singleton,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne hxz, hz]
  have hm := UV.compress_mem_compression (u := ({x} : Finset α))
    (v := ({z} : Finset α)) hs
  rwa [hF.eq, hcomp] at hm

/-- Shifted link/deletion representatives lift whenever the ambient type has
enough vertices to insert one distinct fresh vertex for every selected color. -/
theorem exists_rainbow_of_shifted_links
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset α)) (S : Finset ι) (z : α) (e : ι → Finset α)
    (hstable : ∀ c x, UV.IsCompressed {x} {z} (F c))
    (hz : ∀ c, z ∉ e c)
    (hlink : ∀ c ∈ S, insert z (e c) ∈ F c)
    (hdelete : ∀ c ∉ S, e c ∈ F c)
    (hd : Pairwise (fun c d => Disjoint (e c) (e d)))
    (hcapacity : (∑ c, (e c).card) + S.card ≤ Fintype.card α) :
    ∃ f : ι → Finset α, (∀ c, f c ∈ F c) ∧
      Pairwise (fun c d => Disjoint (f c) (f d)) := by
  classical
  let U : Finset α := Finset.univ.biUnion e
  have hU : U.card ≤ ∑ c, (e c).card := Finset.card_biUnion_le
  have hroom : Fintype.card S ≤ Uᶜ.card := by
    rw [Fintype.card_coe]
    have hc := U.card_add_card_compl
    omega
  obtain ⟨g, hg⟩ := Function.Embedding.exists_of_card_le_finset hroom
  have hfresh (c : S) (d : ι) : g c ∉ e d := by
    have hgc : g c ∈ Uᶜ := hg ⟨c, rfl⟩
    intro h
    exact Finset.mem_compl.mp hgc
      (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ d, h⟩)
  let f : ι → Finset α := fun c =>
    if h : c ∈ S then insert (g ⟨c, h⟩) (e c) else e c
  refine ⟨f, ?_, ?_⟩
  · intro c
    by_cases hc : c ∈ S
    · simp only [f, dif_pos hc]
      exact insert_mem_of_singleton_stable (hstable c _) (hz c)
        (hfresh ⟨c, hc⟩ c) (hlink c hc)
    · simpa only [f, dif_neg hc] using hdelete c hc
  · intro c d hcd
    by_cases hc : c ∈ S <;> by_cases hdS : d ∈ S
    · simp only [f, dif_pos hc, dif_pos hdS, Finset.disjoint_insert_left,
        Finset.disjoint_insert_right, Finset.mem_insert, not_or]
      refine ⟨⟨?_, hfresh ⟨d, hdS⟩ c⟩, hfresh ⟨c, hc⟩ d, hd hcd⟩
      intro heq
      exact hcd (congrArg Subtype.val (g.injective heq)).symm
    · simpa only [f, dif_pos hc, dif_neg hdS, Finset.disjoint_insert_left] using
        And.intro (hfresh ⟨c, hc⟩ d) (hd hcd)
    · simpa only [f, dif_neg hc, dif_pos hdS, Finset.disjoint_insert_right] using
        And.intro (hfresh ⟨d, hdS⟩ c) (hd hcd)
    · simpa only [f, dif_neg hc, dif_neg hdS] using hd hcd

end Submissions.Erdos1020RainbowLift.Main

namespace Submissions.Erdos1020MatchingShadowStep.Main

variable {α : Type*} [DecidableEq α]

/-- The rank-one case of the bounded-matching shadow inequality. -/
theorem shadow_bound_rank_one (s : ℕ) (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.card = 1)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ s * H.shadow.card := by
  classical
  have hc : H.card ≤ s := by
    by_contra hc
    obtain ⟨M, hMH, hMc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt (Nat.lt_of_not_ge hc))
    apply hM
    refine ⟨M, hMH, hMc, ?_⟩
    intro e he f hf hef
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hH e (hMH he))
    obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (hH f (hMH hf))
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton]
    exact fun h => hef (congrArg (fun z : α => ({z} : Finset α)) h)
  by_cases h0 : H = ∅
  · simp [h0]
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr h0
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hH e he)
  have hshadow : (∅ : Finset α) ∈ H.shadow := by
    simpa using Finset.erase_mem_shadow he (Finset.mem_singleton_self x)
  exact hc.trans (by simpa using Nat.mul_le_mul_left s (Finset.card_pos.mpr ⟨∅, hshadow⟩))

/-- A shifted link keeps the matching restriction when the original ground
set can accommodate the restored edges. -/
theorem matchingFree_member_of_stable [Fintype α] {r k : ℕ}
    (H : Finset (Finset α)) (z : α) (hr : 1 ≤ r)
    (hH : ∀ e ∈ H, e.card = r) (hcapacity : r * k ≤ Fintype.card α)
    (hstable : ∀ x, UV.IsCompressed {x} {z} H)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ¬ ∃ M : Finset (Finset α), M ⊆ H.memberSubfamily z ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  rintro ⟨M, hMH, hMc, hMd⟩
  let e (c : M) : Finset α := c.1
  have he (c : M) : e c ∈ H.memberSubfamily z := hMH c.2
  have hesize (c : M) : (e c).card = r - 1 := by
    obtain ⟨hc, hz⟩ := Finset.mem_memberSubfamily.mp (he c)
    have hs := hH _ hc
    rw [Finset.card_insert_of_notMem hz] at hs
    omega
  have hcap : (∑ c : M, (e c).card) + (Finset.univ : Finset M).card ≤
      Fintype.card α := by
    simp only [hesize, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      hMc, Nat.nsmul_eq_mul]
    calc
      k * (r - 1) + k = k * ((r - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = k * r := by rw [Nat.sub_add_cancel hr]
      _ = r * k := Nat.mul_comm _ _
      _ ≤ _ := hcapacity
  obtain ⟨f, hf, hfd⟩ :=
    Submissions.Erdos1020RainbowLift.Main.exists_rainbow_of_shifted_links
      (fun _c : M => H) Finset.univ z e (fun _ x => hstable x)
      (fun c => (Finset.mem_memberSubfamily.mp (he c)).2)
      (fun c _ => (Finset.mem_memberSubfamily.mp (he c)).1)
      (fun c hc => (hc (Finset.mem_univ c)).elim)
      (fun c d hcd => hMd _ c.2 _ d.2 (fun h => hcd (Subtype.ext h))) hcap
  have hfi : Function.Injective f := by
    intro c d hcd
    by_contra hne
    have hp : 0 < (f c).card := by rw [hH _ (hf c)]; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
    exact Finset.disjoint_left.mp (hfd hne) hx (hcd ▸ hx)
  apply hM
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    exact hf c
  · rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_coe, hMc]
  · intro a ha b hb hab
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hb
    exact hfd (fun h => hab (congrArg f h))

/-- The two shadow contributions from deletion and link occupy disjoint
parts of the original shadow. -/
theorem card_shadow_parts_le (H : Finset (Finset α)) (z : α) :
    (H.nonMemberSubfamily z).shadow.card + (H.memberSubfamily z).shadow.card ≤
      H.shadow.card := by
  classical
  let D := (H.nonMemberSubfamily z).shadow
  let L := (H.memberSubfamily z).shadow
  have havoidD : ∀ a ∈ D, z ∉ a := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := Finset.exists_subset_of_mem_shadow ha
    exact fun hz => (Finset.mem_nonMemberSubfamily.mp hb).2 (hab hz)
  have havoidL : ∀ a ∈ L, z ∉ a := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := Finset.exists_subset_of_mem_shadow ha
    exact fun hz => (Finset.mem_memberSubfamily.mp hb).2 (hab hz)
  have hinj : Set.InjOn (insert z) (L : Set (Finset α)) := by
    intro a ha b hb hab
    simpa only [Finset.erase_insert (havoidL a ha), Finset.erase_insert (havoidL b hb)]
      using congrArg (fun c : Finset α => c.erase z) hab
  have hd : Disjoint D (L.image (insert z)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hb
    exact havoidD _ ha (Finset.mem_insert_self z b)
  have hsub : D ∪ L.image (insert z) ⊆ H.shadow := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.shadow_mono (fun _ hb => (Finset.mem_nonMemberSubfamily.mp hb).1) ha
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨x, hxb, hxL⟩ := Finset.mem_shadow_iff_insert_mem.mp hb
      obtain ⟨hxH, hz⟩ := Finset.mem_memberSubfamily.mp hxL
      have hxz : x ≠ z := by
        intro h
        exact hz (Finset.mem_insert.mpr (Or.inl h.symm))
      apply Finset.mem_shadow_iff_insert_mem.mpr
      refine ⟨x, by simp [hxz, hxb], ?_⟩
      simpa only [Finset.insert_comm] using hxH
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_union_of_disjoint hd, Finset.card_image_of_injOn hinj] at hc

end Submissions.Erdos1020MatchingShadowStep.Main

namespace Submissions.Erdos1020MatchingShadowBasics.Main

theorem shadow_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Finset (Finset α)) (f : α ↪ β) :
    (H.map (Finset.mapEmbedding f).toEmbedding).shadow =
      H.shadow.map (Finset.mapEmbedding f).toEmbedding := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, b, hb, hst⟩ := Finset.mem_shadow_iff.mp ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    refine Finset.mem_map.mpr ⟨e.erase a, Finset.erase_mem_shadow he ha, ?_⟩
    change (e.erase a).map f = t
    rw [Finset.map_erase]
    exact hst
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨e, he, a, ha, rfl⟩ := Finset.mem_shadow_iff.mp hs
    apply Finset.mem_shadow_iff.mpr
    refine ⟨e.map f, Finset.mem_map.mpr ⟨e, he, rfl⟩,
      f a, Finset.mem_map_of_mem f ha, ?_⟩
    exact (Finset.map_erase f e a).symm

theorem card_shadow_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Finset (Finset α)) (f : α ↪ β) :
    (H.map (Finset.mapEmbedding f).toEmbedding).shadow.card = H.shadow.card := by
  rw [shadow_map, Finset.card_map]

/-- The existing local LYM incidence inequality, in the multiplication order
used by the shadow induction. -/
theorem incidence_bound {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.card = r) :
    r * H.card ≤ (Fintype.card α - r + 1) * H.shadow.card := by
  simpa only [Nat.mul_comm] using
    Finset.card_mul_le_card_shadow_mul (fun e he => hH e he)

/-- The base range of the bounded-matching shadow theorem uses only incidence
counting; the matching hypothesis is needed by its recursive range. -/
theorem base_bound {α : Type*} [Fintype α] [DecidableEq α] {r s : ℕ}
    (hr : 1 ≤ r) (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.card = r)
    (hn : Fintype.card α ≤ (s + 1) * r - 1) :
    H.card ≤ s * H.shadow.card := by
  rcases H.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · simp
  have hrn : r ≤ Fintype.card α := by
    rw [← hH e he]
    exact Finset.card_le_univ e
  have hprod : (s + 1) * r = s * r + r := by rw [Nat.add_mul, Nat.one_mul]
  have hcoeff : Fintype.card α - r + 1 ≤ s * r := by omega
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < r by omega)
  calc
    r * H.card ≤ (Fintype.card α - r + 1) * H.shadow.card := incidence_bound H hH
    _ ≤ (s * r) * H.shadow.card := Nat.mul_le_mul_right _ hcoeff
    _ = r * (s * H.shadow.card) := by ac_rfl

end Submissions.Erdos1020MatchingShadowBasics.Main

namespace Submissions.Erdos1020RainbowSplit.Main

variable {α : Type*} [DecidableEq α]

/-- Pascal's identity selects a large link or deletion. The singleton guard
prevents an empty-edge link from entering the positive-size induction. -/
theorem large_link_or_deletion {n q a : ℕ} (hn : 2 ≤ n) (hq : 1 ≤ q)
    (F : Finset (Finset α)) (z : α) (hF : ∀ e ∈ F, e.card = q)
    (hlarge : a * (n - 1).choose (q - 1) < F.card)
    (hsingle : q = 1 → ({z} : Finset α) ∉ F) :
    a * (n - 2).choose (q - 1) < (F.nonMemberSubfamily z).card ∨
      (2 ≤ q ∧ a * (n - 2).choose (q - 2) < (F.memberSubfamily z).card) := by
  classical
  have hpart := Finset.card_memberSubfamily_add_card_nonMemberSubfamily z F
  by_cases hq1 : q = 1
  · have hempty : F.memberSubfamily z = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heF, hze⟩ := Finset.mem_memberSubfamily.mp he
      have hc := hF (insert z e) heF
      rw [Finset.card_insert_of_notMem hze, hq1] at hc
      have he0 : e = ∅ := Finset.card_eq_zero.mp (by omega)
      exact hsingle hq1 (by simpa [he0] using heF)
    rw [hempty, Finset.card_empty, Nat.zero_add] at hpart
    left
    simpa only [hpart, hq1, Nat.sub_self, Nat.choose_zero_right, Nat.mul_one] using hlarge
  · have hq2 : 2 ≤ q := by omega
    have hp := Nat.choose_eq_choose_pred_add (n := n - 1) (k := q - 1)
      (by omega) (by omega)
    have hn2 : n - 1 - 1 = n - 2 := by omega
    have hq2' : q - 1 - 1 = q - 2 := by omega
    rw [hn2, hq2'] at hp
    rw [hp, Nat.mul_add] at hlarge
    by_cases hd : a * (n - 2).choose (q - 1) < (F.nonMemberSubfamily z).card
    · exact Or.inl hd
    · exact Or.inr ⟨hq2, by omega⟩

/-- An unused vertex can be removed by passing to its complement subtype.
The exact map equation preserves all edge data and gives cardinality equality. -/
theorem exists_subtype_family (F : Finset (Finset α)) (z : α)
    (havoid : ∀ e ∈ F, z ∉ e) :
    ∃ G : Finset (Finset {x : α // x ≠ z}),
      G.map (Finset.mapEmbedding (Function.Embedding.subtype (· ≠ z))).toEmbedding = F := by
  classical
  let E := (Finset.mapEmbedding (Function.Embedding.subtype (· ≠ z))).toEmbedding
  let G := F.preimage E E.injective.injOn
  refine ⟨G, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_preimage.mp he'
  · intro he
    have hm : E (e.subtype (· ≠ z)) = e := by
      exact Finset.subtype_map_of_mem
        (fun x hx h => havoid e he (h ▸ hx))
    exact Finset.mem_map.mpr
      ⟨e.subtype (· ≠ z), Finset.mem_preimage.mpr (hm.symm ▸ he), hm⟩

end Submissions.Erdos1020RainbowSplit.Main

namespace Submissions.Erdos1020MatchingShadow.Main

open Submissions.Erdos1020MatchingShadowBasics.Main
open Submissions.Erdos1020MatchingShadowStep.Main

universe u

private theorem reindex_shadow {α : Type*} [DecidableEq α] {r k : ℕ}
    (H : Finset (Finset α)) (z : α) (havoid : ∀ e ∈ H, z ∉ e)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Finset {x : α // x ≠ z}),
      G.card = H.card ∧ G.shadow.card = H.shadow.card ∧
      (∀ e ∈ G, e.card = r) ∧
      ¬ ∃ M : Finset (Finset {x : α // x ≠ z}), M ⊆ G ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  obtain ⟨G, hGmap⟩ := Submissions.Erdos1020RainbowSplit.Main.exists_subtype_family H z havoid
  let E := Function.Embedding.subtype (fun x : α => x ≠ z)
  let E' := (Finset.mapEmbedding E).toEmbedding
  have hmem (e) (he : e ∈ G) : e.map E ∈ H := by
    rw [← hGmap]
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · simpa only [Finset.card_map] using congrArg Finset.card hGmap
  · rw [← hGmap]
    exact (card_shadow_map G E).symm
  · intro e he
    simpa only [Finset.card_map] using hH _ (hmem e he)
  · rintro ⟨M, hMG, hMc, hMd⟩
    apply hM
    refine ⟨M.map E', ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp ha
      exact hmem e (hMG he)
    · simpa only [Finset.card_map] using hMc
    · intro a ha b hb hab
      obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hb
      exact (Finset.disjoint_map E).mpr (hMd e he f hf (fun h => hab (congrArg E' h)))

private theorem foldr_preserves {α : Type*} [DecidableEq α] {r k : ℕ}
    (H : Finset (Finset α)) (z : α) (L : List α) (hr : 1 ≤ r)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    let G := L.foldr (fun x F => UV.compression {x} {z} F) H
    G.card = H.card ∧ (∀ e ∈ G, e.card = r) ∧
      (¬ ∃ M : Finset (Finset α), M ⊆ G ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
      G.shadow.card ≤ H.shadow.card := by
  classical
  induction L with
  | nil => exact ⟨rfl, hH, hM, le_rfl⟩
  | cons x L ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [List.foldr_cons, UV.card_compression] using ih.1
    · exact Set.Sized.uvCompression (by simp) ih.2.1
    · exact Submissions.Erdos1020ShiftNormalize.Main.matchingFree_singleton_compression
        (by omega) ih.2.1 ih.2.2.1 x z
    · exact (Submissions.Erdos1020ShiftNormalize.Main.card_shadow_singleton_compression_le
        _ x z).trans ih.2.2.2

private theorem shadow_bound_aux (n : ℕ) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = n →
      ∀ s r, 1 ≤ r → ∀ H : Finset (Finset α),
        (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = s + 1 ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ s * H.shadow.card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α _ _ hn s r hr H hH hM
    classical
    by_cases hsmall : Fintype.card α ≤ (s + 1) * r - 1
    · exact base_bound hr H hH hsmall
    by_cases hr1 : r = 1
    · subst r
      exact shadow_bound_rank_one s H hH hM
    have hr2 : 2 ≤ r := by omega
    have hprod : r ≤ (s + 1) * r := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right r (show 1 ≤ s + 1 by omega)
    have hcap : r * (s + 1) ≤ Fintype.card α := by
      rw [Nat.mul_comm]
      omega
    have hnpos : 0 < n := by omega
    obtain ⟨z⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    let L := (Finset.univ : Finset α).toList
    let G := L.foldr (fun x F => UV.compression {x} {z} F) H
    obtain ⟨hGc, hGsize, hGfree, hGshadow⟩ := foldr_preserves H z L hr hH hM
    have hGstable (x : α) : UV.IsCompressed {x} {z} G :=
      Submissions.Erdos1020RainbowShift.Main.isCompressed_foldr_singleton_same_source
        H z L x (by simp [L])
    have hDsize : ∀ e ∈ G.nonMemberSubfamily z, e.card = r :=
      fun _ he => hGsize _ (Finset.mem_nonMemberSubfamily.mp he).1
    have hDfree : ¬ ∃ M : Finset (Finset α), M ⊆ G.nonMemberSubfamily z ∧
        M.card = s + 1 ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
      rintro ⟨M, hMD, hMc, hMd⟩
      exact hGfree ⟨M, fun _ he => (Finset.mem_nonMemberSubfamily.mp (hMD he)).1, hMc, hMd⟩
    have hLsize : ∀ e ∈ G.memberSubfamily z, e.card = r - 1 := by
      intro e he
      obtain ⟨heG, hze⟩ := Finset.mem_memberSubfamily.mp he
      have hc := hGsize _ heG
      rw [Finset.card_insert_of_notMem hze] at hc
      omega
    have hLfree := matchingFree_member_of_stable G z hr hGsize hcap hGstable hGfree
    obtain ⟨D, hDc, hDsh, hDu, hDm⟩ := reindex_shadow (G.nonMemberSubfamily z) z
      (fun _ he => (Finset.mem_nonMemberSubfamily.mp he).2) hDsize hDfree
    obtain ⟨K, hKc, hKsh, hKu, hKm⟩ := reindex_shadow (G.memberSubfamily z) z
      (fun _ he => (Finset.mem_memberSubfamily.mp he).2) hLsize hLfree
    have hAc : Fintype.card {x : α // x ≠ z} = n - 1 := by
      simpa only [Fintype.card_subtype_eq, hn] using
        Fintype.card_subtype_compl (fun x : α => x = z)
    have hlt : n - 1 < n := by omega
    have hDb := ih (n - 1) hlt hAc s r hr D hDu hDm
    have hKb := ih (n - 1) hlt hAc s (r - 1) (by omega) K hKu hKm
    rw [hDc, hDsh] at hDb
    rw [hKc, hKsh] at hKb
    have hpart := Finset.card_memberSubfamily_add_card_nonMemberSubfamily z G
    have hs := card_shadow_parts_le G z
    calc
      H.card = G.card := hGc.symm
      _ = (G.nonMemberSubfamily z).card + (G.memberSubfamily z).card := by omega
      _ ≤ s * (G.nonMemberSubfamily z).shadow.card + s * (G.memberSubfamily z).shadow.card :=
        Nat.add_le_add hDb hKb
      _ = s * ((G.nonMemberSubfamily z).shadow.card + (G.memberSubfamily z).shadow.card) :=
        (Nat.mul_add _ _ _).symm
      _ ≤ s * G.shadow.card := Nat.mul_le_mul_left s hs
      _ ≤ s * H.shadow.card := Nat.mul_le_mul_left s hGshadow

/-- Frankl's bounded-matching shadow inequality, for every positive rank. -/
theorem shadow_bound {α : Type u} [Fintype α] [DecidableEq α]
    (s r : ℕ) (hr : 1 ≤ r) (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ s * H.shadow.card :=
  shadow_bound_aux (Fintype.card α) rfl s r hr H hH hM

end Submissions.Erdos1020MatchingShadow.Main

-- Source: WeightedAverage.lean
-- Source: RainbowAverage.lean
namespace Submissions.Erdos1020MatchingRainbowAverage.Main

/-- Every set of the same size as a fixed block has the same positive number
of permutation preimages. This counts successful relabelings without factorials. -/
theorem permutation_fiber_count {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α) (F : Finset (Finset α))
    (hF : ∀ e ∈ F, e.card = P.card) :
    ∃ d : ℕ, 0 < d ∧
      F.card * d = ((Finset.univ : Finset (Equiv.Perm α)).filter
        (fun σ => P.map σ.toEmbedding ∈ F)).card ∧
      (Fintype.card α).choose P.card * d = Fintype.card (Equiv.Perm α) := by
  classical
  let G := (Finset.univ : Finset (Equiv.Perm α))
  let A := (Finset.univ : Finset α).powersetCard P.card
  let R (e : Finset α) (σ : Equiv.Perm α) : Prop := P.map σ.toEmbedding = e
  let d := (G.bipartiteAbove R P).card
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    refine ⟨Equiv.refl _, (Finset.mem_bipartiteAbove R).mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [R]
  have hdegree (e : Finset α) (he : e.card = P.card) :
      (G.bipartiteAbove R e).card = d := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq P e he.symm
    have hτback : e.map τ.symm.toEmbedding = P := by
      rw [← hτ]
      simp [Finset.map_map]
    change (Finset.univ.filter (fun σ : Equiv.Perm α => P.map σ.toEmbedding = e)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm α => P.map σ.toEmbedding = P)).card
    refine Finset.card_bij' (fun σ _ => σ.trans τ.symm) (fun σ _ => σ.trans τ)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [Equiv.trans_toEmbedding, ← Finset.map_map, (Finset.mem_filter.mp hσ).2, hτback]
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [Equiv.trans_toEmbedding, ← Finset.map_map, (Finset.mem_filter.mp hσ).2, hτ]
    · intro σ _
      simp [Equiv.trans_assoc]
    · intro σ _
      simp [Equiv.trans_assoc]
  have hbelow (E : Finset (Finset α)) (σ : Equiv.Perm α) :
      (E.bipartiteBelow R σ).card = if P.map σ.toEmbedding ∈ E then 1 else 0 := by
    by_cases he : P.map σ.toEmbedding ∈ E <;>
      simp [Finset.bipartiteBelow, R, Finset.filter_eq, he]
  have hcountF : F.card * d = (G.filter (fun σ => P.map σ.toEmbedding ∈ F)).card := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := F) (t := G) R
    have hleft : (∑ e ∈ F, (G.bipartiteAbove R e).card) = F.card * d := by
      calc
        _ = ∑ _e ∈ F, d := Finset.sum_congr rfl (fun e he => hdegree e (hF e he))
        _ = _ := by simp
    rw [hleft] at hc
    simpa only [hbelow, Finset.sum_boole, Nat.cast_id] using hc
  have hcountA : (Fintype.card α).choose P.card * d = G.card := by
    have hc := Finset.card_mul_eq_card_mul (s := A) (t := G) (m := d) (n := 1) R
      (fun e he => hdegree e (Finset.mem_powersetCard_univ.mp he))
      (fun σ _ => by rw [hbelow]; simp [A])
    simpa [A] using hc
  exact ⟨d, hd, hcountF, by simpa [G] using hcountA⟩

/-- The equality base of the varying-size rainbow matching theorem, with the
disjoint blocks supplied. All comparisons use natural-number counts. -/
theorem rainbow_of_disjoint_blocks {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (q : ι → ℕ) (P : ι → Finset α)
    (hq : ∀ i, 0 < q i) (hP : ∀ i, (P i).card = q i)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hsum : ∑ i, q i = Fintype.card α)
    (F : ι → Finset (Finset α)) (hF : ∀ i, ∀ e ∈ F i, e.card = q i)
    (hlarge : ∀ i, (Fintype.card ι - 1) * (Fintype.card α - 1).choose (q i - 1) <
      (F i).card) :
    ∃ e : ι → Finset α, (∀ i, e i ∈ F i) ∧
      Pairwise (fun i j => Disjoint (e i) (e j)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let _ := hι
    refine ⟨P, ?_, ?_⟩
    · intro i
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i
  · let _ := hι
    let n := Fintype.card α
    let k := Fintype.card ι
    let G := (Finset.univ : Finset (Equiv.Perm α))
    let T (i : ι) (σ : Equiv.Perm α) : Prop := (P i).map σ.toEmbedding ∈ F i
    have hqle (i : ι) : q i ≤ n := by
      simpa only [hP i, n] using Finset.card_le_univ (P i)
    have hn : 0 < n := by
      obtain ⟨i⟩ := hι
      exact (hq i).trans_le (hqle i)
    have hsuccess (i : ι) :
        (k - 1) * q i * G.card < n * (G.bipartiteAbove T i).card := by
      obtain ⟨d, hd, hcountF, hcountA⟩ := permutation_fiber_count (P i) (F i)
        (fun e he => (hF i e he).trans (hP i).symm)
      have hcountF' : (F i).card * d = (G.bipartiteAbove T i).card := hcountF
      have hcountA' : n.choose (q i) * d = G.card := by
        simpa only [hP i, n, G, Finset.card_univ] using hcountA
      have hident : n * (n - 1).choose (q i - 1) = q i * n.choose (q i) := by
        have h := Nat.add_one_mul_choose_eq (n - 1) (q i - 1)
        have hn' : n - 1 + 1 = n := by omega
        have hq' : q i - 1 + 1 = q i := by have := hq i; omega
        simpa only [hn', hq', Nat.mul_comm] using h
      have hscale := Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_right (hlarge i) hd) hn
      have heq : n * ((k - 1) * (n - 1).choose (q i - 1) * d) =
          (k - 1) * q i * G.card := by
        calc
          _ = (k - 1) * (n * (n - 1).choose (q i - 1)) * d := by ac_rfl
          _ = (k - 1) * (q i * n.choose (q i)) * d := by rw [hident]
          _ = (k - 1) * q i * (n.choose (q i) * d) := by ac_rfl
          _ = (k - 1) * q i * G.card := by rw [hcountA']
      change n * ((k - 1) * (n - 1).choose (q i - 1) * d) < n * ((F i).card * d) at hscale
      rwa [heq, hcountF'] at hscale
    by_contra hnone
    have hbelow (σ : Equiv.Perm α) :
        ((Finset.univ : Finset ι).bipartiteBelow T σ).card ≤ k - 1 := by
      apply Nat.le_pred_of_lt
      change ((Finset.univ : Finset ι).bipartiteBelow T σ).card <
        (Finset.univ : Finset ι).card
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      apply hnone
      refine ⟨fun i => (P i).map σ.toEmbedding, ?_, ?_⟩
      · intro i
        have hi : i ∈ (Finset.univ : Finset ι).bipartiteBelow T σ := by
          rw [heq]
          exact Finset.mem_univ i
        exact ((Finset.mem_bipartiteBelow T).mp hi).2
      · intro i j hij
        exact (Finset.disjoint_map σ.toEmbedding).mpr (hPd hij)
    have hsumle : (∑ i, (G.bipartiteAbove T i).card) ≤ G.card * (k - 1) := by
      calc
        _ = ∑ σ ∈ G, ((Finset.univ : Finset ι).bipartiteBelow T σ).card :=
          Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow T
        _ ≤ G.card * (k - 1) := by
          simpa only [Nat.nsmul_eq_mul] using
            Finset.sum_le_card_nsmul G
              (fun σ => ((Finset.univ : Finset ι).bipartiteBelow T σ).card)
              (k - 1) (fun σ _ => hbelow σ)
    have hsumlt := Finset.sum_lt_sum_of_nonempty
      (s := (Finset.univ : Finset ι)) Finset.univ_nonempty (fun i _ => hsuccess i)
    have hleft : (∑ i, (k - 1) * q i * G.card) = (k - 1) * n * G.card := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
    rw [hleft, ← Finset.mul_sum] at hsumlt
    have hupper := Nat.mul_le_mul_left n hsumle
    have heq : n * (G.card * (k - 1)) = (k - 1) * n * G.card := by ac_rfl
    rw [heq] at hupper
    exact hsumlt.not_ge hupper

end Submissions.Erdos1020MatchingRainbowAverage.Main

-- Source: WeightedFinite.lean
namespace Submissions.Erdos1020MatchingWeightedFinite.Main

/-- The finite weighted inequality underlying Frankl's nested-family averaging.
The sets are nested in decreasing order and have no injective transversal. -/
theorem weighted_bound {s t : ℕ} (A : Fin (s + 1) → Finset (Fin t))
    (hnested : ∀ i j, i ≤ j → A j ⊆ A i)
    (hno : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A i)
    (ht : 2 * s + 1 ≤ t) :
    (∑ i, (A i).card) + s * (A (Fin.last s)).card ≤ s * t := by
  classical
  have hHall : ¬ ∀ D : Finset (Fin (s + 1)), D.card ≤ (D.biUnion A).card :=
    fun h => hno ((Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp h)
  push_neg at hHall
  obtain ⟨D, hdef⟩ := hHall
  have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
  let i := D.min' hDne
  have hiD : i ∈ D := D.min'_mem hDne
  have hmin : ∀ j ∈ D, i ≤ j := fun j hj => D.min'_le j hj
  have hDcard : D.card ≤ s + 1 - i.val := by
    calc
      _ ≤ (Finset.Ici i).card := Finset.card_le_card (by
        intro j hj
        exact Finset.mem_Ici.mpr (hmin j hj))
      _ = _ := Fin.card_Ici i
  have hAi : (A i).card ≤ s - i.val := by
    have hsub : A i ⊆ D.biUnion A := by
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨i, hiD, hv⟩
    have hsmall := (Finset.card_le_card hsub).trans_lt hdef
    omega
  let x := s - i.val
  have hi : i.val ≤ s := Nat.le_of_lt_succ i.isLt
  have hix : i.val + x = s := Nat.add_sub_of_le hi
  have hxs : x ≤ s := Nat.sub_le _ _
  have hsuffix : ∀ j, i ≤ j → (A j).card ≤ x :=
    fun j hj => (Finset.card_le_card (hnested i j hj)).trans hAi
  have hlast : (A (Fin.last s)).card ≤ x := hsuffix _ (Fin.le_last i)
  have hprefixSum : (∑ j ∈ Finset.Iio i, (A j).card) ≤ i.val * t := by
    calc
      _ ≤ ∑ _j ∈ Finset.Iio i, t := Finset.sum_le_sum (by
        intro j _
        simpa using Finset.card_le_univ (A j))
      _ = _ := by simp
  have hsuffixSum : (∑ j ∈ Finset.Ici i, (A j).card) ≤ (x + 1) * x := by
    calc
      _ ≤ ∑ _j ∈ Finset.Ici i, x := Finset.sum_le_sum (by
        intro j hj
        exact hsuffix j (Finset.mem_Ici.mp hj))
      _ = _ := by
        simp only [Finset.sum_const, Fin.card_Ici, Nat.nsmul_eq_mul]
        congr 1
        omega
  have hcover : Finset.Iio i ∪ Finset.Ici i =
      (Finset.univ : Finset (Fin (s + 1))) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ,
      iff_true]
    exact lt_or_ge j i
  have hdisj : Disjoint (Finset.Iio i) (Finset.Ici i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hi'
    exact (not_lt_of_ge (Finset.mem_Ici.mp hi')) (Finset.mem_Iio.mp hj)
  have hsum : (∑ j, (A j).card) ≤ i.val * t + (x + 1) * x := by
    calc
      _ = ∑ j ∈ Finset.Iio i ∪ Finset.Ici i, (A j).card := by rw [hcover]
      _ = (∑ j ∈ Finset.Iio i, (A j).card) +
          ∑ j ∈ Finset.Ici i, (A j).card := Finset.sum_union hdisj
      _ ≤ _ := Nat.add_le_add hprefixSum hsuffixSum
  calc
    _ ≤ (i.val * t + (x + 1) * x) + s * x :=
      Nat.add_le_add hsum (Nat.mul_le_mul_left s hlast)
    _ = i.val * t + (x + 1 + s) * x := by rw [Nat.add_assoc, ← Nat.add_mul]
    _ ≤ i.val * t + t * x :=
      Nat.add_le_add_left (Nat.mul_le_mul_right x (by omega)) _
    _ = (i.val + x) * t := by rw [Nat.mul_comm t x, ← Nat.add_mul]
    _ = s * t := by rw [hix]

end Submissions.Erdos1020MatchingWeightedFinite.Main

-- Source: WeightedAverageBody.lean
namespace Submissions.Erdos1020WeightedAverage.Main

/-- Frankl's weighted nested-family inequality, with disjoint equal-size
blocks supplied. Indexed rainbow absence also makes rank zero harmless. -/
theorem weighted_bound_of_disjoint_blocks {α : Type*}
    [Fintype α] [DecidableEq α] {s t ℓ : ℕ}
    (P : Fin t → Finset α) (hP : ∀ j, (P j).card = ℓ)
    (hPd : Pairwise (fun j k => Disjoint (P j) (P k)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ℓ)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (ht : 2 * s + 1 ≤ t) :
    (∑ i, (F i).card) + s * (F (Fin.last s)).card ≤
      s * (Fintype.card α).choose ℓ := by
  classical
  let G := (Finset.univ : Finset (Equiv.Perm α))
  let C := (Fintype.card α).choose ℓ
  let R (i : Fin (s + 1)) (j : Fin t) (σ : Equiv.Perm α) : Prop :=
    (P j).map σ.toEmbedding ∈ F i
  let A (σ : Equiv.Perm α) (i : Fin (s + 1)) : Finset (Fin t) :=
    Finset.univ.filter (fun j => R i j σ)
  have hfinite (σ : Equiv.Perm α) :
      (∑ i, (A σ i).card) + s * (A σ (Fin.last s)).card ≤ s * t := by
    apply Submissions.Erdos1020MatchingWeightedFinite.Main.weighted_bound
    · intro i j hij b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hnested i j hij (Finset.mem_filter.mp hb).2⟩
    · rintro ⟨f, hfinj, hf⟩
      apply hno
      refine ⟨fun i => (P (f i)).map σ.toEmbedding, ?_, ?_⟩
      · intro i
        exact (Finset.mem_filter.mp (hf i)).2
      · intro i j hij
        exact (Finset.disjoint_map σ.toEmbedding).mpr (hPd (hfinj.ne hij))
    · exact ht
  have hcount (i : Fin (s + 1)) (j : Fin t) :
      C * (G.bipartiteAbove (R i) j).card = (F i).card * G.card := by
    obtain ⟨d, _, hcountF, hcountA⟩ :=
      Submissions.Erdos1020MatchingRainbowAverage.Main.permutation_fiber_count
        (P j) (F i) (fun e he => (hF i e he).trans (hP j).symm)
    have hcountF' : (F i).card * d = (G.bipartiteAbove (R i) j).card := hcountF
    have hcountA' : C * d = G.card := by
      simpa only [C, G, Finset.card_univ, hP j] using hcountA
    calc
      _ = C * ((F i).card * d) := by rw [hcountF']
      _ = (F i).card * (C * d) := by ac_rfl
      _ = (F i).card * G.card := by rw [hcountA']
  have havg (i : Fin (s + 1)) :
      C * (∑ σ ∈ G, (A σ i).card) = t * ((F i).card * G.card) := by
    have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin t))) (t := G) (R i)
    change (∑ j, (G.bipartiteAbove (R i) j).card) =
      ∑ σ ∈ G, (A σ i).card at hdouble
    calc
      _ = C * (∑ j, (G.bipartiteAbove (R i) j).card) := by rw [hdouble]
      _ = ∑ j, C * (G.bipartiteAbove (R i) j).card := Finset.mul_sum _ _ _
      _ = ∑ _j : Fin t, (F i).card * G.card :=
        Finset.sum_congr rfl (fun j _ => hcount i j)
      _ = t * ((F i).card * G.card) := by simp
  have hsum : (∑ σ ∈ G,
      ((∑ i, (A σ i).card) + s * (A σ (Fin.last s)).card)) ≤ G.card * (s * t) := by
    calc
      _ ≤ ∑ _σ ∈ G, s * t := Finset.sum_le_sum (fun σ _ => hfinite σ)
      _ = _ := by simp
  have hfirst : C * (∑ σ ∈ G, ∑ i, (A σ i).card) =
      (t * G.card) * (∑ i, (F i).card) := by
    calc
      _ = ∑ i, C * (∑ σ ∈ G, (A σ i).card) := by
        rw [Finset.sum_comm, Finset.mul_sum]
      _ = ∑ i, t * ((F i).card * G.card) :=
        Finset.sum_congr rfl (fun i _ => havg i)
      _ = (t * G.card) * (∑ i, (F i).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
  have hlast : C * (∑ σ ∈ G, s * (A σ (Fin.last s)).card) =
      (t * G.card) * (s * (F (Fin.last s)).card) := by
    calc
      _ = s * (C * (∑ σ ∈ G, (A σ (Fin.last s)).card)) := by
        rw [← Finset.mul_sum]
        ac_rfl
      _ = s * (t * ((F (Fin.last s)).card * G.card)) := by rw [havg]
      _ = _ := by ac_rfl
  have hweighted := Nat.mul_le_mul_left C hsum
  rw [Finset.sum_add_distrib, Nat.mul_add, hfirst, hlast, ← Nat.mul_add] at hweighted
  have hright : C * (G.card * (s * t)) = (t * G.card) * (s * C) := by ac_rfl
  rw [hright] at hweighted
  have htpos : 0 < t := by omega
  have hGpos : 0 < G.card := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl _, Finset.mem_univ _⟩
  exact Nat.le_of_mul_le_mul_left hweighted (Nat.mul_pos htpos hGpos)

end Submissions.Erdos1020WeightedAverage.Main

-- Source: UniformBlocks.lean
namespace Submissions.Erdos1020UniformBlocks.Main

/-- A capacity inequality supplies disjoint equal-size blocks, including
empty blocks and an empty block index type. -/
theorem exists_blocks {α : Type*} [Fintype α] (t ℓ : ℕ)
    (hcapacity : t * ℓ ≤ Fintype.card α) :
    ∃ P : Fin t → Finset α, (∀ j, (P j).card = ℓ) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) := by
  classical
  have hc : Fintype.card (Σ _ : Fin t, Fin ℓ) ≤ Fintype.card α := by
    simpa using hcapacity
  obtain ⟨e : (Σ _ : Fin t, Fin ℓ) ↪ α⟩ := Function.Embedding.nonempty_of_card_le hc
  let Q (i : Fin t) : Finset (Σ _ : Fin t, Fin ℓ) :=
    (Finset.univ : Finset (Fin ℓ)).map (Function.Embedding.sigmaMk i)
  refine ⟨fun i => (Q i).map e, ?_, ?_⟩
  · intro i
    simp [Q]
  · intro i j hij
    apply (Finset.disjoint_map e).mpr
    exact Finset.pairwiseDisjoint_map_sigmaMk
      (s := Finset.univ) (t := fun _ : Fin t => (Finset.univ : Finset (Fin ℓ)))
      (Finset.mem_univ i) (Finset.mem_univ j) hij

end Submissions.Erdos1020UniformBlocks.Main

-- Source: WeightedBoundBody.lean
namespace Submissions.Erdos1020WeightedBound.Main

/-- Frankl's weighted bound for nested cross-dependent uniform families. -/
theorem weighted_bound {α : Type*} [Fintype α] [DecidableEq α] {s t ℓ : ℕ}
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ℓ)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (ht : 2 * s + 1 ≤ t) (hcapacity : t * ℓ ≤ Fintype.card α) :
    (∑ i, (F i).card) + s * (F (Fin.last s)).card ≤
      s * (Fintype.card α).choose ℓ := by
  obtain ⟨P, hP, hPd⟩ := Submissions.Erdos1020UniformBlocks.Main.exists_blocks t ℓ hcapacity
  exact Submissions.Erdos1020WeightedAverage.Main.weighted_bound_of_disjoint_blocks
    P hP hPd F hF hnested hno ht

end Submissions.Erdos1020WeightedBound.Main

namespace Submissions.Erdos1020MatchingCleanLinks.Main

/-- Edges meeting the selected vertices only at `v` give an equally large link
on the complement, with exact reconstruction of each original edge. -/
theorem exists_clean_links {α : Type*} [DecidableEq α] {r : ℕ}
    (H : Finset (Finset α)) (T : Finset α) (v : α)
    (hH : ∀ e ∈ H, e.card = r) :
    ∃ L : Finset (Finset {x : α // x ∉ T}),
      L.card = (H.filter (fun e => v ∈ e ∧ Disjoint e (T.erase v))).card ∧
      (∀ e ∈ L, e.card = r - 1) ∧
      ∀ e ∈ L, insert v (e.map (Function.Embedding.subtype (· ∉ T))) ∈ H := by
  classical
  let good := H.filter (fun e => v ∈ e ∧ Disjoint e (T.erase v))
  let shrink (e : Finset α) := (e.erase v).subtype (· ∉ T)
  let E := Function.Embedding.subtype (fun x : α => x ∉ T)
  have hmap : ∀ e ∈ good, (shrink e).map E = e.erase v := by
    intro e he
    obtain ⟨_, _, hd⟩ := Finset.mem_filter.mp he
    apply Finset.subtype_map_of_mem
    intro x hx hxT
    exact Finset.disjoint_left.mp hd (Finset.mem_erase.mp hx).2
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hxT⟩)
  have hlift : ∀ e ∈ good, insert v ((shrink e).map E) = e := by
    intro e he
    rw [hmap e he]
    exact Finset.insert_erase (Finset.mem_filter.mp he).2.1
  refine ⟨good.image shrink, ?_, ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro e he f hf hef
    calc
      e = insert v ((shrink e).map E) := (hlift e he).symm
      _ = insert v ((shrink f).map E) := congrArg (fun s => insert v (s.map E)) hef
      _ = f := hlift f hf
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    have hc := congrArg Finset.card (hmap f hf)
    rw [Finset.card_map, Finset.card_erase_of_mem (Finset.mem_filter.mp hf).2.1,
      hH f (Finset.mem_filter.mp hf).1] at hc
    exact hc
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    change insert v ((shrink f).map E) ∈ H
    rw [hlift f hf]
    exact (Finset.mem_filter.mp hf).1

end Submissions.Erdos1020MatchingCleanLinks.Main

namespace Submissions.Erdos1020MatchingHeadLinks.Main

def tailFamily {n : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (v : Fin n) (r : ℕ) :
    Finset (Finset {x : Fin n // x ∉ T}) :=
  (Finset.univ.powersetCard (r - 1)).filter (fun e =>
    insert v (e.map (Function.Embedding.subtype (fun x : Fin n => x ∉ T))) ∈ H)

theorem tailFamily_uniform {n : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (v : Fin n) (r : ℕ) :
    ∀ e ∈ tailFamily H T v r, e.card = r - 1 := by
  intro e he
  exact Finset.mem_powersetCard_univ.mp (Finset.mem_filter.mp he).1

theorem notMem_map_of_mem_head {n : ℕ} {T : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ T) (e : Finset {x : Fin n // x ∉ T}) :
    v ∉ e.map (Function.Embedding.subtype (fun x : Fin n => x ∉ T)) := by
  intro h
  obtain ⟨x, _, hx⟩ := Finset.mem_map.mp h
  change x.val = v at hx
  exact x.property (hx.symm ▸ hv)

/-- Edges meeting the head exactly at v inject into its complement tail family. -/
theorem singleton_head_le {n : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (v : Fin n) (r : ℕ) (hv : v ∈ T)
    (hH : ∀ e ∈ H, e.card = r) :
    (H.filter (fun e => e ∩ T = {v})).card ≤ (tailFamily H T v r).card := by
  have hfilters : H.filter (fun e => e ∩ T = {v}) =
      H.filter (fun e => v ∈ e ∧ Disjoint e (T.erase v)) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hmeet⟩
      have hve : v ∈ e := (Finset.mem_inter.mp
        (show v ∈ e ∩ T by rw [hmeet]; simp)).1
      refine ⟨he, hve, Finset.disjoint_left.mpr ?_⟩
      intro x hxe hxT
      have hxv : x = v := Finset.mem_singleton.mp (by
        rw [← hmeet]
        exact Finset.mem_inter.mpr ⟨hxe, (Finset.mem_erase.mp hxT).2⟩)
      exact (Finset.mem_erase.mp hxT).1 hxv
    · rintro ⟨he, hve, hd⟩
      refine ⟨he, ?_⟩
      ext x
      rw [Finset.mem_singleton]
      constructor
      · intro hx
        by_contra hne
        exact Finset.disjoint_left.mp hd (Finset.mem_inter.mp hx).1
          (Finset.mem_erase.mpr ⟨hne, (Finset.mem_inter.mp hx).2⟩)
      · rintro rfl
        exact Finset.mem_inter.mpr ⟨hve, hv⟩
  obtain ⟨L, hLcard, hLuniform, hLlift⟩ :=
    Submissions.Erdos1020MatchingCleanLinks.Main.exists_clean_links H T v hH
  rw [hfilters, ← hLcard]
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powersetCard_univ.mpr (hLuniform e he), hLlift e he⟩

/-- Global downward stability makes the singleton-head tail families nested. -/
theorem tailFamily_nested {n s : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (r : ℕ) (J : Fin (s + 1) ↪ Fin n)
    (hJ : ∀ i, J i ∈ T) (hmono : StrictMono J)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    ∀ i j, i ≤ j → tailFamily H T (J j) r ⊆ tailFamily H T (J i) r := by
  intro i j hij e he
  rcases lt_or_eq_of_le hij with hlt | rfl
  · refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, ?_⟩
    exact Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
      (hstable (J i) (J j) (hmono hlt))
      (notMem_map_of_mem_head (hJ j) e) (notMem_map_of_mem_head (hJ i) e)
      (Finset.mem_filter.mp he).2
  · exact he

/-- Disjoint tail representatives would lift to a matching in the original
family. Each lift contains its own head vertex, so no positive-rank guard is needed. -/
theorem no_rainbow {n s : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (r : ℕ) (J : Fin (s + 1) ↪ Fin n)
    (hJ : ∀ i, J i ∈ T)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ¬ ∃ e : Fin (s + 1) → Finset {x : Fin n // x ∉ T},
      (∀ i, e i ∈ tailFamily H T (J i) r) ∧
        Pairwise (fun i j => Disjoint (e i) (e j)) := by
  classical
  rintro ⟨e, he, hd⟩
  let E := Function.Embedding.subtype (fun x : Fin n => x ∉ T)
  let f (i : Fin (s + 1)) : Finset (Fin n) := insert (J i) ((e i).map E)
  have hf : ∀ i, f i ∈ H := fun i => (Finset.mem_filter.mp (he i)).2
  have hfd : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    simp only [f, Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      Finset.mem_insert, not_or]
    refine ⟨⟨?_, notMem_map_of_mem_head (hJ j) (e i)⟩,
      notMem_map_of_mem_head (hJ i) (e j), ?_⟩
    · intro hji
      exact hij (J.injective hji).symm
    · exact (Finset.disjoint_map E).mpr (hd hij)
  have hinj : Function.Injective f := by
    intro i j heq
    by_contra hne
    have hself : Disjoint (f i) (f i) := by simpa only [heq] using hfd hne
    have hhead : J i ∈ f i := Finset.mem_insert_self _ _
    exact Finset.disjoint_left.mp hself hhead hhead
  apply hfree
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hf i
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hfd (fun h => hab (congrArg f h))

end Submissions.Erdos1020MatchingHeadLinks.Main

namespace Submissions.Erdos1020MatchingHeadSlices.Main

open Finset

/-- Partition a finite family by its empty, singleton, or larger intersection with a head. -/
theorem card_partition {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (T : Finset α) :
    H.card = (H.filter (fun e => e ∩ T = ∅)).card +
      (∑ v ∈ T, (H.filter (fun e => e ∩ T = {v})).card) +
      (H.filter (fun e => 2 ≤ (e ∩ T).card)).card := by
  have hd : (T : Set α).PairwiseDisjoint
      (fun v => H.filter (fun e => e ∩ T = {v})) := by
    intro v _ w _ hvw
    apply disjoint_left.mpr
    intro e he hf
    exact hvw (singleton_injective ((mem_filter.mp he).2.symm.trans (mem_filter.mp hf).2))
  have hu : T.biUnion (fun v => H.filter (fun e => e ∩ T = {v})) =
      H.filter (fun e => (e ∩ T).card = 1) := by
    ext e
    simp only [mem_biUnion, mem_filter]
    constructor
    · rintro ⟨v, _, he, h⟩
      exact ⟨he, by simp [h]⟩
    · rintro ⟨he, h⟩
      obtain ⟨v, hv⟩ := card_eq_one.mp h
      have hvT : v ∈ T := (mem_inter.mp (hv.symm ▸ mem_singleton_self v)).2
      exact ⟨v, hvT, he, hv⟩
  have hs : (∑ v ∈ T, (H.filter (fun e => e ∩ T = {v})).card) =
      (H.filter (fun e => (e ∩ T).card = 1)).card := by
    rw [← card_biUnion hd, hu]
  have h0 := card_filter_add_card_filter_not (s := H) (fun e => e ∩ T = ∅)
  have h1 := card_filter_add_card_filter_not
    (s := H.filter (fun e => ¬e ∩ T = ∅)) (fun e => (e ∩ T).card = 1)
  have h01 : (H.filter (fun e => ¬e ∩ T = ∅)).filter
      (fun e => (e ∩ T).card = 1) = H.filter (fun e => (e ∩ T).card = 1) := by
    ext e
    simp only [mem_filter]
    rw [← Finset.card_eq_zero]
    constructor
    · rintro ⟨⟨he, _⟩, hc⟩
      exact ⟨he, hc⟩
    · rintro ⟨he, hc⟩
      exact ⟨⟨he, by omega⟩, hc⟩
  have h02 : (H.filter (fun e => ¬e ∩ T = ∅)).filter
      (fun e => ¬(e ∩ T).card = 1) = H.filter (fun e => 2 ≤ (e ∩ T).card) := by
    ext e
    simp only [mem_filter]
    rw [← Finset.card_eq_zero]
    constructor
    · rintro ⟨⟨he, hne⟩, hc⟩
      exact ⟨he, by omega⟩
    · rintro ⟨he, hc⟩
      exact ⟨⟨he, by omega⟩, by omega⟩
  rw [h01, h02] at h1
  omega

/-- The full uniform level avoiding the head is its complement's uniform level. -/
theorem zero_head_card {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (r : ℕ) :
    (((univ : Finset α).powersetCard r).filter (fun e => e ∩ T = ∅)).card =
      (Fintype.card α - T.card).choose r := by
  have h : ((univ : Finset α).powersetCard r).filter (fun e => e ∩ T = ∅) =
      (univ \ T).powersetCard r := by
    ext e
    simp [mem_powersetCard, subset_sdiff, disjoint_iff_inter_eq_empty, and_comm]
  rw [h, card_powersetCard, card_sdiff_of_subset (subset_univ T), card_univ]

/-- A specified singleton intersection leaves an arbitrary complement subset of size r-1. -/
theorem singleton_head_card {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (v : α) (hv : v ∈ T) {r : ℕ} (hr : 1 ≤ r) :
    (((univ : Finset α).powersetCard r).filter (fun e => e ∩ T = {v})).card =
      (Fintype.card α - T.card).choose (r - 1) := by
  have h : ((univ : Finset α).powersetCard r).filter (fun e => e ∩ T = {v}) =
      ((insert v (univ \ T)).powersetCard r).filter (fun e => {v} ⊆ e) := by
    ext e
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, singleton_subset_iff]
    constructor
    · rintro ⟨he, h⟩
      have hve : v ∈ e := (mem_inter.mp (h.symm ▸ mem_singleton_self v)).1
      refine ⟨⟨?_, he⟩, hve⟩
      intro x hx
      by_cases hxv : x = v
      · simp [hxv]
      · apply mem_insert_of_mem
        apply mem_sdiff.mpr
        refine ⟨mem_univ x, ?_⟩
        intro hxT
        exact hxv (mem_singleton.mp (h ▸ mem_inter.mpr ⟨hx, hxT⟩))
    · rintro ⟨⟨he, her⟩, hve⟩
      refine ⟨her, ?_⟩
      ext x
      simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨hxe, hxT⟩
        rcases mem_insert.mp (he hxe) with hxv | hxY
        · exact hxv
        · exact ((mem_sdiff.mp hxY).2 hxT).elim
      · rintro rfl
        exact ⟨hve, hv⟩
  rw [h, card_filter_powersetCard_subset {v} (insert v (univ \ T)) r
    (singleton_subset_iff.mpr (mem_insert_self _ _)) (by simpa using hr)]
  have hvY : v ∉ (univ : Finset α) \ T := by simp [hv]
  rw [card_singleton, card_insert_of_notMem hvY,
    card_sdiff_of_subset (subset_univ T), card_univ, Nat.add_sub_cancel]

end Submissions.Erdos1020MatchingHeadSlices.Main

namespace Submissions.Erdos1020MatchingHeadComparison.Main

open Finset

/-- A bound on the empty and singleton head slices implies the star bound. -/
theorem star_bound_of_slices {n s r : ℕ}
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n)) (hr : 1 ≤ r)
    (hT : T.card = s + 1) (hH : ∀ e ∈ H, e.card = r) (hhead : s + 1 ≤ n)
    (hbound : (H.filter (fun e => e ∩ T = ∅)).card +
      (∑ v ∈ T, (H.filter (fun e => e ∩ T = {v})).card) ≤
        s * (n - (s + 1)).choose (r - 1)) :
    H.card ≤ n.choose r - (n - s).choose r := by
  let V := (univ : Finset (Fin n)).powersetCard r
  have hsub : H ⊆ V := fun e he => mem_powersetCard.mpr ⟨subset_univ e, hH e he⟩
  have hm := card_le_card (filter_subset_filter (fun e => 2 ≤ (e ∩ T).card) hsub)
  have hV := Erdos1020MatchingHeadSlices.Main.card_partition V T
  have hzero : (V.filter (fun e => e ∩ T = ∅)).card =
      (n - (s + 1)).choose r := by
    simpa only [V, Fintype.card_fin, hT] using
      Erdos1020MatchingHeadSlices.Main.zero_head_card T r
  have hsingle : (∑ v ∈ T, (V.filter (fun e => e ∩ T = {v})).card) =
      (s + 1) * (n - (s + 1)).choose (r - 1) := by
    calc
      _ = ∑ _v ∈ T, (n - (s + 1)).choose (r - 1) := by
        apply sum_congr rfl
        intro v hv
        simpa only [V, Fintype.card_fin, hT] using
          Erdos1020MatchingHeadSlices.Main.singleton_head_card T v hv hr
      _ = _ := by simp [hT]
  have hcardV : V.card = n.choose r := by simp [V]
  rw [hcardV, hzero, hsingle] at hV
  have hpart := Erdos1020MatchingHeadSlices.Main.card_partition H T
  have hPascal := Nat.choose_eq_choose_pred_add
    (n := n - s) (k := r) (by omega) (by omega)
  have hpred : n - s - 1 = n - (s + 1) := by omega
  rw [hpred] at hPascal
  simp only [Nat.add_mul, Nat.one_mul] at hV
  omega

end Submissions.Erdos1020MatchingHeadComparison.Main

namespace Submissions.Erdos1020MatchingZeroHead.Main

open Finset
open Submissions.Erdos1020MatchingHeadLinks.Main

/-- Every shadow of an edge beyond the head extends at its last vertex. -/
theorem shadow_zero_head_le {n r : ℕ}
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n)) (v : Fin n)
    (hv : v ∈ T) (hlower : ∀ x ∉ T, v < x)
    (hH : ∀ e ∈ H, e.card = r)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    (H.filter (fun e => e ∩ T = ∅)).shadow.card ≤ (tailFamily H T v r).card := by
  classical
  let Z := H.filter (fun e => e ∩ T = ∅)
  let shrink (e : Finset (Fin n)) := e.subtype (· ∉ T)
  let E := Function.Embedding.subtype (fun x : Fin n => x ∉ T)
  have havoid : ∀ e ∈ Z, ∀ x ∈ e, x ∉ T := by
    intro e he x hx hxT
    have hm : x ∈ e ∩ T := mem_inter.mpr ⟨hx, hxT⟩
    rw [(mem_filter.mp he).2] at hm
    exact notMem_empty x hm
  have hsa : ∀ a ∈ Z.shadow, ∀ x ∈ a, x ∉ T := by
    intro a ha x hx
    obtain ⟨e, he, hsub⟩ := exists_subset_of_mem_shadow ha
    exact havoid e he x (hsub hx)
  have hmap : ∀ a ∈ Z.shadow, (shrink a).map E = a := by
    intro a ha
    exact subtype_map_of_mem (hsa a ha)
  have hmem : ∀ a ∈ Z.shadow, shrink a ∈ tailFamily H T v r := by
    intro a ha
    obtain ⟨x, hxa, hxe⟩ := mem_shadow_iff_insert_mem.mp ha
    have hxT := havoid _ hxe x (mem_insert_self x a)
    have hva : v ∉ a := fun h => hsa a ha v h hv
    have hsize := hH _ (mem_filter.mp hxe).1
    rw [card_insert_of_notMem hxa] at hsize
    have hcard := congrArg Finset.card (hmap a ha)
    rw [card_map] at hcard
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
    · change (shrink a).card = r - 1
      omega
    · change insert v ((shrink a).map E) ∈ H
      rw [hmap a ha]
      exact Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
        (hstable v x (hlower x hxT)) hxa hva (mem_filter.mp hxe).1
  calc
    Z.shadow.card = (Z.shadow.image shrink).card := by
      symm
      apply card_image_of_injOn
      intro a ha b hb hab
      exact (hmap a ha).symm.trans ((congrArg (fun e => e.map E) hab).trans (hmap b hb))
    _ ≤ (tailFamily H T v r).card := card_le_card (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact hmem b hb)

/-- The matching shadow inequality bounds the empty-head slice. -/
theorem zero_head_le {n r s : ℕ}
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n)) (v : Fin n)
    (hr : 1 ≤ r) (hv : v ∈ T) (hlower : ∀ x ∉ T, v < x)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    (H.filter (fun e => e ∩ T = ∅)).card ≤ s * (tailFamily H T v r).card := by
  have hu : ∀ e ∈ H.filter (fun e => e ∩ T = ∅), e.card = r :=
    fun _ he => hH _ (mem_filter.mp he).1
  have hm : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ H.filter (fun e => e ∩ T = ∅) ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    rintro ⟨M, hMZ, hMc, hMd⟩
    exact hM ⟨M, fun _ he => (mem_filter.mp (hMZ he)).1, hMc, hMd⟩
  exact (Submissions.Erdos1020MatchingShadow.Main.shadow_bound s r hr _ hu hm).trans
    (Nat.mul_le_mul_left s (shadow_zero_head_le H T v hv hlower hH hstable))

end Submissions.Erdos1020MatchingZeroHead.Main

namespace Submissions.Erdos1020MatchingFrankl.Main

open Finset
open Submissions.Erdos1020MatchingHeadLinks.Main

/-- Frankl's linear range for the star extremal bound. -/
theorem star_bound {n r s : ℕ} (hr : 2 ≤ r)
    (hn : (2 * r - 1) * s + r ≤ n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose r - (n - s).choose r := by
  classical
  obtain ⟨G, hGc, hGu, hGm, hGs⟩ :=
    Submissions.Erdos1020ShiftNormalize.Main.exists_shifted H hH hM
  have hrpred : r - 1 + 1 = r := by omega
  have htwopred : 2 * r - 1 + 1 = 2 * r := by omega
  have hpoly : (2 * s + 1) * (r - 1) + (s + 1) = (2 * r - 1) * s + r := by
    nlinarith
  have hhead : s + 1 ≤ n := by
    have := Nat.zero_le ((2 * s + 1) * (r - 1))
    omega
  let J : Fin (s + 1) ↪ Fin n :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hhead⟩,
      fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
  let T : Finset (Fin n) := univ.map J
  have hT : T.card = s + 1 := by simp [T]
  have hJ (i : Fin (s + 1)) : J i ∈ T := mem_map.mpr ⟨i, mem_univ i, rfl⟩
  have hmono : StrictMono J := fun _ _ h => h
  have hcut (x : Fin n) : x ∈ T ↔ x.val < s + 1 := by
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      exact i.isLt
    · intro hx
      exact mem_map.mpr ⟨⟨x.val, hx⟩, mem_univ _, Fin.ext rfl⟩
  have hlower : ∀ x ∉ T, J (Fin.last s) < x := by
    intro x hx
    have hc := (hcut x).not.mp hx
    change s < x.val
    omega
  let F := fun i : Fin (s + 1) => tailFamily G T (J i) r
  have hAc : Fintype.card {x : Fin n // x ∉ T} = n - (s + 1) := by
    simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
      Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
  have hcapacity : (2 * s + 1) * (r - 1) ≤ Fintype.card {x : Fin n // x ∉ T} := by
    rw [hAc]
    omega
  have hweighted := Submissions.Erdos1020WeightedBound.Main.weighted_bound
    (t := 2 * s + 1) F (fun i => tailFamily_uniform G T (J i) r)
    (tailFamily_nested G T r J hJ hmono hGs)
    (no_rainbow G T r J hJ hGm) le_rfl hcapacity
  rw [hAc] at hweighted
  have hzero := Submissions.Erdos1020MatchingZeroHead.Main.zero_head_le
    G T (J (Fin.last s)) (by omega) (hJ _) hlower hGu hGm hGs
  have hsingle : (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
      ∑ i, (F i).card := by
    change (∑ v ∈ univ.map J, (G.filter (fun e => e ∩ T = {v})).card) ≤ _
    rw [sum_map]
    apply sum_le_sum
    intro i _
    exact singleton_head_le G T (J i) r (hJ i) hGu
  have hslices : (G.filter (fun e => e ∩ T = ∅)).card +
      (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
        s * (n - (s + 1)).choose (r - 1) := by
    change _ ≤ s * (n - (s + 1)).choose (r - 1)
    change (G.filter (fun e => e ∩ T = ∅)).card ≤ s * (F (Fin.last s)).card at hzero
    omega
  rw [← hGc]
  exact Submissions.Erdos1020MatchingHeadComparison.Main.star_bound_of_slices
    G T (by omega) hT hGu hhead hslices

end Submissions.Erdos1020MatchingFrankl.Main

namespace Submissions.Erdos1020MatchingFranklProof.Main

/-- The native extremal expression, restricted by the explicit linear guard. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → (2 * r - 1) * (k - 1) + r ≤ n →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hn H hH hM
  have hkpred : k - 1 + 1 = k := by omega
  have hcoeff : 1 ≤ 2 * r - 1 := by omega
  have hkn : k ≤ n := by
    have := Nat.mul_le_mul_right (k - 1) hcoeff
    nlinarith
  have hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = (k - 1) + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    simpa only [hkpred] using hM
  have hb := Submissions.Erdos1020MatchingFrankl.Main.star_bound (by omega) hn H hH hfree
  have hsub : n - (k - 1) = n - k + 1 := by omega
  rw [hsub] at hb
  exact hb.trans (le_max_right _ _)

end Submissions.Erdos1020MatchingFranklProof.Main

namespace Submissions.Erdos1020MatchingShadowLinks.Main

open Finset

/-- Taking a link at z commutes with taking the lower shadow. -/
theorem shadow_memberSubfamily {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (z : α) :
    (H.memberSubfamily z).shadow = H.shadow.memberSubfamily z := by
  ext e
  simp only [mem_shadow_iff_insert_mem, mem_memberSubfamily, mem_insert, not_or]
  constructor
  · rintro ⟨a, ha, hH, hza, hz⟩
    exact ⟨⟨a, ⟨Ne.symm hza, ha⟩, by simpa only [insert_comm] using hH⟩, hz⟩
  · rintro ⟨⟨a, ⟨haz, ha⟩, hH⟩, hz⟩
    exact ⟨a, ha, by simpa only [insert_comm] using hH, Ne.symm haz, hz⟩

/-- A singleton compression's shadow lies in the compressed shadow. -/
theorem shadow_singleton_compression_subset {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (i j : α) :
    (UV.compression {i} {j} H).shadow ⊆ UV.compression {i} {j} H.shadow := by
  apply UV.shadow_compression_subset_compression_shadow
  intro x hx
  have hxi : x = i := mem_singleton.mp hx
  subst x
  refine ⟨j, mem_singleton_self _, ?_⟩
  simpa only [erase_singleton] using UV.isCompressed_self (∅ : Finset α) H

/-- Stability under a singleton compression passes to the shadow. -/
theorem isCompressed_shadow {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (i j : α) (h : UV.IsCompressed {i} {j} H) :
    UV.IsCompressed {i} {j} H.shadow := by
  have hs : H.shadow ⊆ UV.compression {i} {j} H.shadow := by
    simpa only [h.eq] using shadow_singleton_compression_subset H i j
  exact (eq_of_subset_of_card_le hs (UV.card_compression _ _ _).le).symm

/-- A forbidden matching in a positive-rank shadow stays forbidden after a singleton shift. -/
theorem matchingFree_shadow_compression {α : Type*} [DecidableEq α] {r k : ℕ}
    (hr : 2 ≤ r) (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.card = r)
    (hfree : ¬ ∃ M : Finset (Finset α), M ⊆ H.shadow ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) (i j : α) :
    ¬ ∃ M : Finset (Finset α), M ⊆ (UV.compression {i} {j} H).shadow ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  have hshadow : ∀ e ∈ H.shadow, e.card = r - 1 := Set.Sized.shadow hH
  have hm := Submissions.Erdos1020ShiftNormalize.Main.matchingFree_singleton_compression
    (H := H.shadow) (r := r - 1) (k := k) (by omega) hshadow hfree i j
  rintro ⟨M, hM, hMc, hMd⟩
  exact hm ⟨M, fun _ he => shadow_singleton_compression_subset H i j (hM he), hMc, hMd⟩

end Submissions.Erdos1020MatchingShadowLinks.Main

namespace Submissions.Erdos1020MatchingRestrictedShadowRankTwo.Main

/-- In the large-ground-set rank-two branch, a link at a vertex shifted
away from every other vertex is empty if the shadow is matching-free. -/
theorem member_empty {α : Type*} [Fintype α] [DecidableEq α]
    (s : ℕ) (H : Finset (Finset α)) (z : α)
    (hH : ∀ e ∈ H, e.card = 2)
    (hstable : ∀ x, UV.IsCompressed {x} {z} H)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H.shadow ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hcap : s + 1 ≤ Fintype.card α) :
    H.memberSubfamily z = ∅ := by
  classical
  have hSsize : ∀ e ∈ H.shadow, e.card = 1 := by
    intro e he
    exact Set.Sized.shadow hH he
  have hScard : H.shadow.card ≤ s := by
    by_contra hc
    obtain ⟨M, hMH, hMc⟩ :=
      Finset.exists_subset_card_eq (Nat.succ_le_of_lt (Nat.lt_of_not_ge hc))
    apply hM
    refine ⟨M, hMH, hMc, ?_⟩
    intro e he f hf hef
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hSsize e (hMH he))
    obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (hSsize f (hMH hf))
    simp only [Finset.disjoint_singleton_left, Finset.mem_singleton]
    exact fun h => hef (congrArg (fun a : α => ({a} : Finset α)) h)
  have hSstable (x : α) : UV.IsCompressed {x} {z} H.shadow := by
    exact Submissions.Erdos1020MatchingShadowLinks.Main.isCompressed_shadow H x z (hstable x)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heH, hze⟩ := Finset.mem_memberSubfamily.mp he
  have hec : e.card = 1 := by
    have hc := hH _ heH
    rw [Finset.card_insert_of_notMem hze] at hc
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hec
  have haz : a ≠ z := by
    intro h
    exact hze (by simp [h])
  have hz : ({z} : Finset α) ∈ H.shadow := by
    apply Finset.mem_shadow_iff_insert_mem.mpr
    refine ⟨a, by simpa using haz, ?_⟩
    simpa only [Finset.pair_comm a z] using heH
  have hall (x : α) : ({x} : Finset α) ∈ H.shadow := by
    by_cases hxz : x = z
    · simpa only [hxz] using hz
    have hc := UV.compress_mem_compression (u := ({x} : Finset α)) (v := {z}) hz
    rw [(hSstable x).eq] at hc
    simpa [UV.compress, Finset.sup_eq_union, Finset.sdiff_singleton_eq_erase,
      hxz, Ne.symm hxz] using hc
  have hinj : Function.Injective (fun x : α => ({x} : Finset α)) := by
    intro x y hxy
    simpa only [Finset.singleton_inj] using hxy
  have hsub : (Finset.univ.image (fun x : α => ({x} : Finset α))) ⊆ H.shadow := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact hall x
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hc
  omega

end Submissions.Erdos1020MatchingRestrictedShadowRankTwo.Main

namespace Submissions.Erdos1020MatchingRestrictedShadow.Main

open Finset
open Submissions.Erdos1020MatchingShadowBasics.Main
open Submissions.Erdos1020MatchingShadowLinks.Main

universe u

private theorem reindex {α : Type*} [DecidableEq α] {r k : ℕ}
    (H : Finset (Finset α)) (z : α) (havoid : ∀ e ∈ H, z ∉ e)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H.shadow ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Finset {x : α // x ≠ z}),
      G.card = H.card ∧ G.shadow.card = H.shadow.card ∧
      (∀ e ∈ G, e.card = r) ∧
      ¬ ∃ M : Finset (Finset {x : α // x ≠ z}), M ⊆ G.shadow ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  obtain ⟨G, hGmap⟩ := Submissions.Erdos1020RainbowSplit.Main.exists_subtype_family H z havoid
  let E := Function.Embedding.subtype (fun x : α => x ≠ z)
  let E' := (Finset.mapEmbedding E).toEmbedding
  have hmem (e) (he : e ∈ G) : e.map E ∈ H := by
    rw [← hGmap]
    exact mem_map.mpr ⟨e, he, rfl⟩
  have hshmem (e) (he : e ∈ G.shadow) : e.map E ∈ H.shadow := by
    rw [← hGmap, shadow_map]
    exact mem_map.mpr ⟨e, he, rfl⟩
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · simpa only [card_map] using congrArg Finset.card hGmap
  · rw [← hGmap]
    exact (card_shadow_map G E).symm
  · intro e he
    simpa only [card_map] using hH _ (hmem e he)
  · rintro ⟨M, hMG, hMc, hMd⟩
    apply hM
    refine ⟨M.map E', ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨e, he, rfl⟩ := mem_map.mp ha
      exact hshmem e (hMG he)
    · simpa only [card_map] using hMc
    · intro a ha b hb hab
      obtain ⟨e, he, rfl⟩ := mem_map.mp ha
      obtain ⟨f, hf, rfl⟩ := mem_map.mp hb
      exact (disjoint_map E).mpr (hMd e he f hf (fun h => hab (congrArg E' h)))

private theorem fold_preserves {α : Type*} [DecidableEq α] {r k : ℕ}
    (H : Finset (Finset α)) (z : α) (L : List α) (hr : 2 ≤ r)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H.shadow ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    let G := L.foldr (fun x F => UV.compression {x} {z} F) H
    G.card = H.card ∧ (∀ e ∈ G, e.card = r) ∧
      (¬ ∃ M : Finset (Finset α), M ⊆ G.shadow ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
      G.shadow.card ≤ H.shadow.card := by
  classical
  induction L with
  | nil => exact ⟨rfl, hH, hM, le_rfl⟩
  | cons x L ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [List.foldr_cons, UV.card_compression] using ih.1
    · exact Set.Sized.uvCompression (by simp) ih.2.1
    · exact matchingFree_shadow_compression hr _ ih.2.1 ih.2.2.1 x z
    · exact (Submissions.Erdos1020ShiftNormalize.Main.card_shadow_singleton_compression_le
        _ x z).trans ih.2.2.2

private theorem bound_aux (n : ℕ) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = n →
      ∀ s r, 2 ≤ r → ∀ H : Finset (Finset α),
        (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset α), M ⊆ H.shadow ∧ M.card = s + 1 ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        r * H.card ≤ (r - 1) * s * H.shadow.card := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α _ _ hn s r hr H hH hM
    classical
    by_cases hsmall : Fintype.card α ≤ (s + 1) * (r - 1) - 1
    · rcases H.eq_empty_or_nonempty with rfl | ⟨e, he⟩
      · simp
      have hrn : r ≤ Fintype.card α := by
        rw [← hH e he]
        exact card_le_univ e
      have hp : (s + 1) * (r - 1) = s * (r - 1) + (r - 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hc : Fintype.card α - r + 1 ≤ s * (r - 1) := by omega
      exact (incidence_bound H hH).trans (by
        simpa only [Nat.mul_comm s (r - 1)] using Nat.mul_le_mul_right H.shadow.card hc)
    have hcap : (r - 1) * (s + 1) ≤ Fintype.card α := by
      have hp : 1 ≤ (s + 1) * (r - 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      rw [Nat.mul_comm]
      omega
    have hnpos : 0 < n := by
      have hp : 1 ≤ (r - 1) * (s + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      omega
    obtain ⟨z⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    let L := (univ : Finset α).toList
    let G := L.foldr (fun x F => UV.compression {x} {z} F) H
    obtain ⟨hGc, hGu, hGm, hGsh⟩ := fold_preserves H z L hr hH hM
    have hGs (x : α) : UV.IsCompressed {x} {z} G :=
      Submissions.Erdos1020RainbowShift.Main.isCompressed_foldr_singleton_same_source
        H z L x (by simp [L])
    have hDu : ∀ e ∈ G.nonMemberSubfamily z, e.card = r :=
      fun _ he => hGu _ (mem_nonMemberSubfamily.mp he).1
    have hDm : ¬ ∃ M : Finset (Finset α), M ⊆ (G.nonMemberSubfamily z).shadow ∧
        M.card = s + 1 ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
      rintro ⟨M, hMD, hMc, hMd⟩
      exact hGm ⟨M, fun _ he => shadow_mono
        (fun _ hb => (mem_nonMemberSubfamily.mp hb).1) (hMD he), hMc, hMd⟩
    obtain ⟨D, hDc, hDsh, hDU, hDM⟩ := reindex (G.nonMemberSubfamily z) z
      (fun _ he => (mem_nonMemberSubfamily.mp he).2) hDu hDm
    have hAc : Fintype.card {x : α // x ≠ z} = n - 1 := by
      simpa only [Fintype.card_subtype_eq, hn] using
        Fintype.card_subtype_compl (fun x : α => x = z)
    have hlt : n - 1 < n := by omega
    have hDb := ih (n - 1) hlt hAc s r hr D hDU hDM
    rw [hDc, hDsh] at hDb
    have hKb : r * (G.memberSubfamily z).card ≤
        (r - 1) * s * (G.memberSubfamily z).shadow.card := by
      by_cases hr2 : r = 2
      · have hKu : ∀ e ∈ G, e.card = 2 := by simpa only [hr2] using hGu
        have hKempty := Submissions.Erdos1020MatchingRestrictedShadowRankTwo.Main.member_empty
          s G z hKu hGs hGm (by simpa [hr2] using hcap)
        simp [hKempty]
      have hr3 : 3 ≤ r := by omega
      have hKu : ∀ e ∈ G.memberSubfamily z, e.card = r - 1 := by
        intro e he
        obtain ⟨heG, hze⟩ := mem_memberSubfamily.mp he
        have hc := hGu _ heG
        rw [card_insert_of_notMem hze] at hc
        omega
      have hKm := Submissions.Erdos1020MatchingShadowStep.Main.matchingFree_member_of_stable
        G.shadow z (by omega) (Set.Sized.shadow hGu) hcap
        (fun x => isCompressed_shadow G x z (hGs x)) hGm
      rw [← shadow_memberSubfamily] at hKm
      obtain ⟨K, hKc, hKsh, hKU, hKM⟩ := reindex (G.memberSubfamily z) z
        (fun _ he => (mem_memberSubfamily.mp he).2) hKu hKm
      have hb := ih (n - 1) hlt hAc s (r - 1) (by omega) K hKU hKM
      rw [hKc, hKsh] at hb
      have hpred : r - 1 - 1 = r - 2 := by omega
      rw [hpred] at hb
      have hcoef : r * (r - 2) ≤ (r - 1) * (r - 1) := by
        have h1 : r - 1 + 1 = r := by omega
        have h2 : r - 2 + 2 = r := by omega
        nlinarith
      apply Nat.le_of_mul_le_mul_left (c := r - 1) ?_ (by omega)
      calc
        (r - 1) * (r * (G.memberSubfamily z).card) =
            r * ((r - 1) * (G.memberSubfamily z).card) := by ac_rfl
        _ ≤ r * ((r - 2) * s * (G.memberSubfamily z).shadow.card) := Nat.mul_le_mul_left r hb
        _ ≤ (r - 1) * ((r - 1) * s * (G.memberSubfamily z).shadow.card) := by
          simpa only [Nat.mul_assoc] using
            Nat.mul_le_mul_right (s * (G.memberSubfamily z).shadow.card) hcoef
    have hp := card_memberSubfamily_add_card_nonMemberSubfamily z G
    have hsh := Submissions.Erdos1020MatchingShadowStep.Main.card_shadow_parts_le G z
    calc
      r * H.card = r * G.card := by rw [hGc]
      _ = r * (G.nonMemberSubfamily z).card + r * (G.memberSubfamily z).card := by
        rw [← Nat.mul_add]
        congr 1
        omega
      _ ≤ (r - 1) * s * (G.nonMemberSubfamily z).shadow.card +
          (r - 1) * s * (G.memberSubfamily z).shadow.card := Nat.add_le_add hDb hKb
      _ = (r - 1) * s * ((G.nonMemberSubfamily z).shadow.card +
          (G.memberSubfamily z).shadow.card) := (Nat.mul_add _ _ _).symm
      _ ≤ (r - 1) * s * G.shadow.card := Nat.mul_le_mul_left _ hsh
      _ ≤ (r - 1) * s * H.shadow.card := Nat.mul_le_mul_left _ hGsh

/-- A matching restriction on the shadow gives a stronger shadow ratio. -/
theorem shadow_bound {α : Type u} [Fintype α] [DecidableEq α]
    (s r : ℕ) (hr : 2 ≤ r) (H : Finset (Finset α))
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ H.shadow ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    r * H.card ≤ (r - 1) * s * H.shadow.card :=
  bound_aux (Fintype.card α) rfl s r hr H hH hM

end Submissions.Erdos1020MatchingRestrictedShadow.Main

namespace Submissions.Erdos1020MatchingZeroShadow.Main

open Finset

/-- A shadow of the empty-head slice extends at every earlier head vertex. -/
theorem extend_zero_shadow {n : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (v : Fin n) (hv : v ∈ T)
    (hlower : ∀ x ∉ T, v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (a : Finset (Fin n)) (ha : a ∈ (H.filter (fun e => e ∩ T = ∅)).shadow) :
    insert v a ∈ H := by
  obtain ⟨x, hxa, he⟩ := mem_shadow_iff_insert_mem.mp ha
  have havoid : ∀ y ∈ insert x a, y ∉ T := by
    intro y hy hyT
    have hm : y ∈ insert x a ∩ T := mem_inter.mpr ⟨hy, hyT⟩
    rw [(mem_filter.mp he).2] at hm
    exact notMem_empty y hm
  exact Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
    (hstable v x (hlower x (havoid x (mem_insert_self x a)))) hxa
    (fun h => havoid v (mem_insert_of_mem h) hv) (mem_filter.mp he).1

/-- A whole head of earlier vertices lifts any matching in the zero-slice shadow. -/
theorem shadow_zero_matchingFree {n k : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (hT : T.card = k)
    (hlower : ∀ v ∈ T, ∀ x ∉ T, v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ (H.filter (fun e => e ∩ T = ∅)).shadow ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  rintro ⟨M, hMZ, hMc, hMd⟩
  have hcard : Fintype.card M ≤ Fintype.card T := by simp only [Fintype.card_coe, hMc, hT, le_refl]
  obtain ⟨g : M ↪ T⟩ := Function.Embedding.nonempty_of_card_le hcard
  have havoid : ∀ e ∈ M, ∀ x ∈ e, x ∉ T := by
    intro e he x hx hxT
    obtain ⟨a, ha, hsub⟩ := exists_subset_of_mem_shadow (hMZ he)
    have hm : x ∈ a ∩ T := mem_inter.mpr ⟨hsub hx, hxT⟩
    rw [(mem_filter.mp ha).2] at hm
    exact notMem_empty x hm
  let f (c : M) : Finset (Fin n) := insert (g c).val c.val
  have hf (c : M) : f c ∈ H := extend_zero_shadow H T (g c).val (g c).property
    (hlower _ (g c).property) hstable c.val (hMZ c.property)
  have hfresh (c d : M) : (g c).val ∉ d.val :=
    fun h => havoid d.val d.property (g c).val h (g c).property
  have hd : Pairwise (fun c d => Disjoint (f c) (f d)) := by
    intro c d hcd
    simp only [f, disjoint_insert_left, disjoint_insert_right, mem_insert, not_or]
    refine ⟨⟨?_, hfresh d c⟩, hfresh c d, ?_⟩
    · intro hdc
      exact hcd (g.injective (Subtype.ext hdc)).symm
    · exact hMd _ c.property _ d.property (fun h => hcd (Subtype.ext h))
  have hinj : Function.Injective f := by
    intro c d hcd
    by_contra hne
    have hself : Disjoint (f c) (f c) := by simpa only [hcd] using hd hne
    have hhead : (g c).val ∈ f c := mem_insert_self _ _
    exact disjoint_left.mp hself hhead hhead
  apply hM
  refine ⟨univ.image f, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨c, _, rfl⟩ := mem_image.mp ha
    exact hf c
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe, hMc]
  · intro a ha b hb hab
    obtain ⟨c, _, rfl⟩ := mem_image.mp ha
    obtain ⟨d, _, rfl⟩ := mem_image.mp hb
    exact hd (fun h => hab (congrArg f h))

/-- The shadow matching restriction strengthens the zero-head estimate. -/
theorem scaled_zero_head_le {n r s : ℕ} (H : Finset (Finset (Fin n)))
    (T : Finset (Fin n)) (v : Fin n) (hr : 2 ≤ r) (hT : T.card = s + 1)
    (hv : v ∈ T) (hlower : ∀ w ∈ T, ∀ x ∉ T, w < x)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    r * (H.filter (fun e => e ∩ T = ∅)).card ≤
      (r - 1) * s * (Submissions.Erdos1020MatchingHeadLinks.Main.tailFamily H T v r).card := by
  have hu : ∀ e ∈ H.filter (fun e => e ∩ T = ∅), e.card = r :=
    fun _ he => hH _ (mem_filter.mp he).1
  have hm := shadow_zero_matchingFree H T hT hlower hstable hM
  have hb := Submissions.Erdos1020MatchingRestrictedShadow.Main.shadow_bound s r hr _ hu hm
  exact hb.trans (Nat.mul_le_mul_left ((r - 1) * s)
    (Submissions.Erdos1020MatchingZeroHead.Main.shadow_zero_head_le
      H T v hv (hlower v hv) hH hstable))

end Submissions.Erdos1020MatchingZeroShadow.Main

namespace Submissions.Erdos1020WeightedScaledFinite.Main

/-- The scaled finite inequality underlying nested-family averaging.
The sets are nested in decreasing order and have no injective transversal. -/
theorem weighted_bound {s t R a : ℕ} (A : Fin (s + 1) → Finset (Fin t))
    (hnested : ∀ i j, i ≤ j → A j ⊆ A i)
    (hno : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A i)
    (ht : R * (s + 1) + a ≤ R * t) :
    R * (∑ i, (A i).card) + a * (A (Fin.last s)).card ≤ R * s * t := by
  classical
  have hHall : ¬ ∀ D : Finset (Fin (s + 1)), D.card ≤ (D.biUnion A).card :=
    fun h => hno ((Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp h)
  push Not at hHall
  obtain ⟨D, hdef⟩ := hHall
  have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
  let i := D.min' hDne
  have hiD : i ∈ D := D.min'_mem hDne
  have hmin : ∀ j ∈ D, i ≤ j := fun j hj => D.min'_le j hj
  have hDcard : D.card ≤ s + 1 - i.val := by
    calc
      _ ≤ (Finset.Ici i).card := Finset.card_le_card (by
        intro j hj
        exact Finset.mem_Ici.mpr (hmin j hj))
      _ = _ := Fin.card_Ici i
  have hAi : (A i).card ≤ s - i.val := by
    have hsub : A i ⊆ D.biUnion A := by
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨i, hiD, hv⟩
    have hsmall := (Finset.card_le_card hsub).trans_lt hdef
    omega
  let x := s - i.val
  have hi : i.val ≤ s := Nat.le_of_lt_succ i.isLt
  have hix : i.val + x = s := Nat.add_sub_of_le hi
  have hxs : x ≤ s := Nat.sub_le _ _
  have hsuffix : ∀ j, i ≤ j → (A j).card ≤ x :=
    fun j hj => (Finset.card_le_card (hnested i j hj)).trans hAi
  have hlast : (A (Fin.last s)).card ≤ x := hsuffix _ (Fin.le_last i)
  have hprefixSum : (∑ j ∈ Finset.Iio i, (A j).card) ≤ i.val * t := by
    calc
      _ ≤ ∑ _j ∈ Finset.Iio i, t := Finset.sum_le_sum (by
        intro j _
        simpa using Finset.card_le_univ (A j))
      _ = _ := by simp
  have hsuffixSum : (∑ j ∈ Finset.Ici i, (A j).card) ≤ (x + 1) * x := by
    calc
      _ ≤ ∑ _j ∈ Finset.Ici i, x := Finset.sum_le_sum (by
        intro j hj
        exact hsuffix j (Finset.mem_Ici.mp hj))
      _ = _ := by
        simp only [Finset.sum_const, Fin.card_Ici, Nat.nsmul_eq_mul]
        congr 1
        omega
  have hcover : Finset.Iio i ∪ Finset.Ici i =
      (Finset.univ : Finset (Fin (s + 1))) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ,
      iff_true]
    exact lt_or_ge j i
  have hdisj : Disjoint (Finset.Iio i) (Finset.Ici i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hi'
    exact (not_lt_of_ge (Finset.mem_Ici.mp hi')) (Finset.mem_Iio.mp hj)
  have hsum : (∑ j, (A j).card) ≤ i.val * t + (x + 1) * x := by
    calc
      _ = ∑ j ∈ Finset.Iio i ∪ Finset.Ici i, (A j).card := by rw [hcover]
      _ = (∑ j ∈ Finset.Iio i, (A j).card) +
          ∑ j ∈ Finset.Ici i, (A j).card := Finset.sum_union hdisj
      _ ≤ _ := Nat.add_le_add hprefixSum hsuffixSum
  have hcoeff : R * (x + 1) + a ≤ R * t :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left R (by omega)) a).trans ht
  calc
    _ ≤ R * (i.val * t + (x + 1) * x) + a * x :=
      Nat.add_le_add (Nat.mul_le_mul_left R hsum) (Nat.mul_le_mul_left a hlast)
    _ = R * (i.val * t) + x * (R * (x + 1) + a) := by
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl
    _ ≤ R * (i.val * t) + x * (R * t) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left x hcoeff) _
    _ = R * (i.val + x) * t := by
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl
    _ = R * s * t := congrArg (fun z : ℕ => R * z * t) hix

end Submissions.Erdos1020WeightedScaledFinite.Main

namespace Submissions.Erdos1020WeightedScaledAverage.Main

/-- Scaled weighted averaging over supplied disjoint equal-size blocks. -/
theorem weighted_bound_of_disjoint_blocks {α : Type*}
    [Fintype α] [DecidableEq α] {s t ℓ R a : ℕ}
    (P : Fin t → Finset α) (hP : ∀ j, (P j).card = ℓ)
    (hPd : Pairwise (fun j k => Disjoint (P j) (P k)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ℓ)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hR : 0 < R) (ht : R * (s + 1) + a ≤ R * t) :
    R * (∑ i, (F i).card) + a * (F (Fin.last s)).card ≤
      R * s * (Fintype.card α).choose ℓ := by
  classical
  let G := (Finset.univ : Finset (Equiv.Perm α))
  let C := (Fintype.card α).choose ℓ
  let Inc (i : Fin (s + 1)) (j : Fin t) (σ : Equiv.Perm α) : Prop :=
    (P j).map σ.toEmbedding ∈ F i
  let A (σ : Equiv.Perm α) (i : Fin (s + 1)) : Finset (Fin t) :=
    Finset.univ.filter (fun j => Inc i j σ)
  have hfinite (σ : Equiv.Perm α) :
      R * (∑ i, (A σ i).card) + a * (A σ (Fin.last s)).card ≤ R * s * t := by
    apply Submissions.Erdos1020WeightedScaledFinite.Main.weighted_bound
    · intro i j hij b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hnested i j hij (Finset.mem_filter.mp hb).2⟩
    · rintro ⟨f, hfinj, hf⟩
      apply hno
      refine ⟨fun i => (P (f i)).map σ.toEmbedding, ?_, ?_⟩
      · intro i
        exact (Finset.mem_filter.mp (hf i)).2
      · intro i j hij
        exact (Finset.disjoint_map σ.toEmbedding).mpr (hPd (hfinj.ne hij))
    · exact ht
  have hcount (i : Fin (s + 1)) (j : Fin t) :
      C * (G.bipartiteAbove (Inc i) j).card = (F i).card * G.card := by
    obtain ⟨d, _, hcountF, hcountA⟩ :=
      Submissions.Erdos1020MatchingRainbowAverage.Main.permutation_fiber_count
        (P j) (F i) (fun e he => (hF i e he).trans (hP j).symm)
    have hcountF' : (F i).card * d = (G.bipartiteAbove (Inc i) j).card := hcountF
    have hcountA' : C * d = G.card := by
      simpa only [C, G, Finset.card_univ, hP j] using hcountA
    calc
      _ = C * ((F i).card * d) := by rw [hcountF']
      _ = (F i).card * (C * d) := by ac_rfl
      _ = (F i).card * G.card := by rw [hcountA']
  have havg (i : Fin (s + 1)) :
      C * (∑ σ ∈ G, (A σ i).card) = t * ((F i).card * G.card) := by
    have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin t))) (t := G) (Inc i)
    change (∑ j, (G.bipartiteAbove (Inc i) j).card) =
      ∑ σ ∈ G, (A σ i).card at hdouble
    calc
      _ = C * (∑ j, (G.bipartiteAbove (Inc i) j).card) := by rw [hdouble]
      _ = ∑ j, C * (G.bipartiteAbove (Inc i) j).card := Finset.mul_sum _ _ _
      _ = ∑ _j : Fin t, (F i).card * G.card :=
        Finset.sum_congr rfl (fun j _ => hcount i j)
      _ = t * ((F i).card * G.card) := by simp
  have hsum : (∑ σ ∈ G,
      (R * (∑ i, (A σ i).card) + a * (A σ (Fin.last s)).card)) ≤
        G.card * (R * s * t) := by
    calc
      _ ≤ ∑ _σ ∈ G, R * s * t := Finset.sum_le_sum (fun σ _ => hfinite σ)
      _ = _ := by simp
  have hcolors : C * (∑ σ ∈ G, ∑ i, (A σ i).card) =
      (t * G.card) * (∑ i, (F i).card) := by
    calc
      _ = ∑ i, C * (∑ σ ∈ G, (A σ i).card) := by
        rw [Finset.sum_comm, Finset.mul_sum]
      _ = ∑ i, t * ((F i).card * G.card) :=
        Finset.sum_congr rfl (fun i _ => havg i)
      _ = (t * G.card) * (∑ i, (F i).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
  have hfirst : C * (∑ σ ∈ G, R * (∑ i, (A σ i).card)) =
      (t * G.card) * (R * (∑ i, (F i).card)) := by
    calc
      _ = R * (C * (∑ σ ∈ G, ∑ i, (A σ i).card)) := by
        rw [← Finset.mul_sum]
        ac_rfl
      _ = R * ((t * G.card) * (∑ i, (F i).card)) := by rw [hcolors]
      _ = _ := by ac_rfl
  have hlast : C * (∑ σ ∈ G, a * (A σ (Fin.last s)).card) =
      (t * G.card) * (a * (F (Fin.last s)).card) := by
    calc
      _ = a * (C * (∑ σ ∈ G, (A σ (Fin.last s)).card)) := by
        rw [← Finset.mul_sum]
        ac_rfl
      _ = a * (t * ((F (Fin.last s)).card * G.card)) := by rw [havg]
      _ = _ := by ac_rfl
  have hweighted := Nat.mul_le_mul_left C hsum
  rw [Finset.sum_add_distrib, Nat.mul_add, hfirst, hlast, ← Nat.mul_add] at hweighted
  have hright : C * (G.card * (R * s * t)) = (t * G.card) * (R * s * C) := by ac_rfl
  rw [hright] at hweighted
  have hprod : R * (s + 1) ≤ R * t := by omega
  have htpos : 0 < t := (Nat.zero_lt_succ s).trans_le
    (Nat.le_of_mul_le_mul_left hprod hR)
  have hGpos : 0 < G.card := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl _, Finset.mem_univ _⟩
  exact Nat.le_of_mul_le_mul_left hweighted (Nat.mul_pos htpos hGpos)

end Submissions.Erdos1020WeightedScaledAverage.Main

namespace Submissions.Erdos1020WeightedScaled.Main

/-- The scaled nested-family inequality, with an explicit integer coefficient guard. -/
theorem weighted_bound {α : Type*} [Fintype α] [DecidableEq α] {s t ℓ R a : ℕ}
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ℓ)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hR : 0 < R) (ht : R * (s + 1) + a ≤ R * t)
    (hcapacity : t * ℓ ≤ Fintype.card α) :
    R * (∑ i, (F i).card) + a * (F (Fin.last s)).card ≤
      R * s * (Fintype.card α).choose ℓ := by
  obtain ⟨P, hP, hPd⟩ := Submissions.Erdos1020UniformBlocks.Main.exists_blocks t ℓ hcapacity
  exact Submissions.Erdos1020WeightedScaledAverage.Main.weighted_bound_of_disjoint_blocks
    P hP hPd F hF hnested hno hR ht

end Submissions.Erdos1020WeightedScaled.Main

namespace Submissions.Erdos1020MatchingRefined.Main

open Finset
open Submissions.Erdos1020MatchingHeadLinks.Main

/-- The scaled slice estimates imply the star bound under an explicit block-capacity guard. -/
theorem star_bound {n r s t : ℕ} (hr : 2 ≤ r)
    (hw : r * (s + 1) + (r - 1) * s ≤ r * t)
    (hc : (r - 1) * t + s + 1 ≤ n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose r - (n - s).choose r := by
  classical
  obtain ⟨G, hGc, hGu, hGm, hGs⟩ :=
    Submissions.Erdos1020ShiftNormalize.Main.exists_shifted H hH hM
  have hhead : s + 1 ≤ n := by omega
  let J : Fin (s + 1) ↪ Fin n :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hhead⟩,
      fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
  let T : Finset (Fin n) := univ.map J
  have hT : T.card = s + 1 := by simp [T]
  have hJ (i : Fin (s + 1)) : J i ∈ T := mem_map.mpr ⟨i, mem_univ i, rfl⟩
  have hmono : StrictMono J := fun _ _ h => h
  have hcut (x : Fin n) : x ∈ T ↔ x.val < s + 1 := by
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      exact i.isLt
    · intro hx
      exact mem_map.mpr ⟨⟨x.val, hx⟩, mem_univ _, Fin.ext rfl⟩
  have hlower : ∀ v ∈ T, ∀ x ∉ T, v < x := by
    intro v hv x hx
    have hv' := (hcut v).mp hv
    have hx' := (hcut x).not.mp hx
    change v.val < x.val
    omega
  let F := fun i : Fin (s + 1) => tailFamily G T (J i) r
  have hAc : Fintype.card {x : Fin n // x ∉ T} = n - (s + 1) := by
    simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
      Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
  have hcapacity : t * (r - 1) ≤ Fintype.card {x : Fin n // x ∉ T} := by
    rw [hAc, Nat.mul_comm]
    omega
  have hweighted := Submissions.Erdos1020WeightedScaled.Main.weighted_bound
    (t := t) (R := r) (a := (r - 1) * s) F
    (fun i => tailFamily_uniform G T (J i) r)
    (tailFamily_nested G T r J hJ hmono hGs)
    (no_rainbow G T r J hJ hGm) (by omega) hw hcapacity
  rw [hAc] at hweighted
  have hzero := Submissions.Erdos1020MatchingZeroShadow.Main.scaled_zero_head_le
    G T (J (Fin.last s)) hr hT (hJ _) hlower hGu hGm hGs
  have hsingle : (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
      ∑ i, (F i).card := by
    change (∑ v ∈ univ.map J, (G.filter (fun e => e ∩ T = {v})).card) ≤ _
    rw [sum_map]
    apply sum_le_sum
    intro i _
    exact singleton_head_le G T (J i) r (hJ i) hGu
  have hslices : (G.filter (fun e => e ∩ T = ∅)).card +
      (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
        s * (n - (s + 1)).choose (r - 1) := by
    apply Nat.le_of_mul_le_mul_left (c := r) ?_ (by omega)
    change r * (G.filter (fun e => e ∩ T = ∅)).card ≤
      (r - 1) * s * (F (Fin.last s)).card at hzero
    calc
      _ = r * (G.filter (fun e => e ∩ T = ∅)).card +
          r * (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) := Nat.mul_add _ _ _
      _ ≤ (r - 1) * s * (F (Fin.last s)).card + r * (∑ i, (F i).card) :=
        Nat.add_le_add hzero (Nat.mul_le_mul_left r hsingle)
      _ = r * (∑ i, (F i).card) + (r - 1) * s * (F (Fin.last s)).card := Nat.add_comm _ _
      _ ≤ r * s * (n - (s + 1)).choose (r - 1) := hweighted
      _ = _ := Nat.mul_assoc _ _ _
  rw [← hGc]
  exact Submissions.Erdos1020MatchingHeadComparison.Main.star_bound_of_slices
    G T (by omega) hT hGu hhead hslices

end Submissions.Erdos1020MatchingRefined.Main

namespace Submissions.Erdos1020MatchingRefinedProof.Main

/-- The native extremal expression under the explicit scaled integer guard. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k →
      (r - 1) * (((2 * r - 1) * k) / r) + k ≤ n →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hn H hH hM
  let t := ((2 * r - 1) * k) / r
  have hkpred : k - 1 + 1 = k := by omega
  have hkn : k ≤ n := by omega
  have hpoly : r * k + (r - 1) * (k - 1) + (r - 1) = (2 * r - 1) * k := by
    calc
      _ = r * k + (r - 1) * (k - 1 + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      _ = (r + (r - 1)) * k := by rw [hkpred, Nat.add_mul]
      _ = _ := by congr 1; omega
  have hdiv := Nat.div_add_mod ((2 * r - 1) * k) r
  have hmod := Nat.mod_lt ((2 * r - 1) * k) (show 0 < r by omega)
  have hw : r * ((k - 1) + 1) + (r - 1) * (k - 1) ≤ r * t := by
    rw [hkpred]
    dsimp [t]
    omega
  have hc : (r - 1) * t + (k - 1) + 1 ≤ n := by
    dsimp [t]
    omega
  have hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = (k - 1) + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    simpa only [hkpred] using hM
  have hb := Submissions.Erdos1020MatchingRefined.Main.star_bound (by omega) hw hc H hH hfree
  have hsub : n - (k - 1) = n - k + 1 := by omega
  rw [hsub] at hb
  exact hb.trans (le_max_right _ _)

end Submissions.Erdos1020MatchingRefinedProof.Main

namespace Submissions.Erdos1020MatchingPermutationPair.Main

/-- A single permutation transports both members of a disjoint pair. -/
theorem exists_map_disjoint_pair {α : Type*} [DecidableEq α]
    (P Q E D : Finset α) (hPQ : Disjoint P Q) (hED : Disjoint E D)
    (hPE : P.card = E.card) (hQD : Q.card = D.card) :
    ∃ σ : Equiv.Perm α, P.map σ.toEmbedding = E ∧ Q.map σ.toEmbedding = D := by
  classical
  let f : P ⊕ Q → α := Sum.elim Subtype.val Subtype.val
  let g : P ⊕ Q → α := Sum.elim
    (fun x => ((P.equivOfCardEq hPE) x : α))
    (fun x => ((Q.equivOfCardEq hQD) x : α))
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
        change (a : α) = (b : α) at hab
        exact False.elim ((Finset.disjoint_left.mp hPQ) a.property (hab.symm ▸ b.property))
    | inr a =>
      cases b with
      | inl b =>
        change (a : α) = (b : α) at hab
        exact False.elim ((Finset.disjoint_left.mp hPQ) b.property (hab ▸ a.property))
      | inr b => exact congrArg Sum.inr (Subtype.ext hab)
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((P.equivOfCardEq hPE).injective (Subtype.ext hab))
      | inr b =>
        change ((P.equivOfCardEq hPE) a : α) = ((Q.equivOfCardEq hQD) b : α) at hab
        exact False.elim ((Finset.disjoint_left.mp hED)
          ((P.equivOfCardEq hPE) a).property
          (hab.symm ▸ ((Q.equivOfCardEq hQD) b).property))
    | inr a =>
      cases b with
      | inl b =>
        change ((Q.equivOfCardEq hQD) a : α) = ((P.equivOfCardEq hPE) b : α) at hab
        exact False.elim ((Finset.disjoint_left.mp hED)
          ((P.equivOfCardEq hPE) b).property
          (hab ▸ ((Q.equivOfCardEq hQD) a).property))
      | inr b => exact congrArg Sum.inr ((Q.equivOfCardEq hQD).injective (Subtype.ext hab))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le ?_ (by simp [hPE])
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
    have he := hσ (Sum.inl ⟨a, ha⟩)
    change σ a = ((P.equivOfCardEq hPE) ⟨a, ha⟩ : α) at he
    exact he.symm ▸ ((P.equivOfCardEq hPE) ⟨a, ha⟩).property
  · apply Finset.eq_of_subset_of_card_le ?_ (by simp [hQD])
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
    have he := hσ (Sum.inr ⟨a, ha⟩)
    change σ a = ((Q.equivOfCardEq hQD) ⟨a, ha⟩ : α) at he
    exact he.symm ▸ ((Q.equivOfCardEq hQD) ⟨a, ha⟩).property

end Submissions.Erdos1020MatchingPermutationPair.Main

namespace Submissions.Erdos1020MatchingPermutationPairCount.Main

open Finset

def disjointPairs {α : Type*} [Fintype α] [DecidableEq α] (a b : ℕ) :
    Finset (Finset α × Finset α) :=
  ((univ.powersetCard a) ×ˢ (univ.powersetCard b)).filter (fun e => Disjoint e.1 e.2)

theorem mem_disjointPairs {α : Type*} [Fintype α] [DecidableEq α]
    {a b : ℕ} {e : Finset α × Finset α} :
    e ∈ disjointPairs a b ↔ e.1.card = a ∧ e.2.card = b ∧ Disjoint e.1 e.2 := by
  simp only [disjointPairs, mem_filter, mem_product, mem_powersetCard_univ, and_assoc]

/-- Relabelings are uniform on ordered disjoint pairs, including empty blocks. -/
theorem permutation_pair_fiber_count {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : Finset α) (hPQ : Disjoint P Q)
    (F : Finset (Finset α × Finset α))
    (hF : ∀ e ∈ F, e.1.card = P.card ∧ e.2.card = Q.card ∧ Disjoint e.1 e.2) :
    ∃ d : ℕ, 0 < d ∧
      F.card * d = ((univ : Finset (Equiv.Perm α)).filter
        (fun σ => (P.map σ.toEmbedding, Q.map σ.toEmbedding) ∈ F)).card ∧
      (disjointPairs (α := α) P.card Q.card).card * d =
        Fintype.card (Equiv.Perm α) := by
  classical
  let G := (univ : Finset (Equiv.Perm α))
  let R (e : Finset α × Finset α) (σ : Equiv.Perm α) : Prop :=
    (P.map σ.toEmbedding, Q.map σ.toEmbedding) = e
  let d := (G.bipartiteAbove R (P, Q)).card
  have hd : 0 < d := by
    apply card_pos.mpr
    refine ⟨Equiv.refl _, (mem_bipartiteAbove R).mpr ⟨mem_univ _, ?_⟩⟩
    simp [R]
  have hdegree (e : Finset α × Finset α)
      (he : e.1.card = P.card ∧ e.2.card = Q.card ∧ Disjoint e.1 e.2) :
      (G.bipartiteAbove R e).card = d := by
    obtain ⟨τ, hτP, hτQ⟩ :=
      Submissions.Erdos1020MatchingPermutationPair.Main.exists_map_disjoint_pair
        P Q e.1 e.2 hPQ he.2.2 he.1.symm he.2.1.symm
    have hbackP : e.1.map τ.symm.toEmbedding = P := by
      rw [← hτP]
      simp [map_map]
    have hbackQ : e.2.map τ.symm.toEmbedding = Q := by
      rw [← hτQ]
      simp [map_map]
    change (univ.filter (fun σ : Equiv.Perm α =>
      (P.map σ.toEmbedding, Q.map σ.toEmbedding) = e)).card =
        (univ.filter (fun σ : Equiv.Perm α =>
          (P.map σ.toEmbedding, Q.map σ.toEmbedding) = (P, Q))).card
    refine card_bij' (fun σ _ => σ.trans τ.symm) (fun σ _ => σ.trans τ)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      have hp : P.map σ.toEmbedding = e.1 := congrArg Prod.fst (mem_filter.mp hσ).2
      have hq : Q.map σ.toEmbedding = e.2 := congrArg Prod.snd (mem_filter.mp hσ).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      apply Prod.ext
      · simpa only [Equiv.trans_toEmbedding, ← map_map, hp] using hbackP
      · simpa only [Equiv.trans_toEmbedding, ← map_map, hq] using hbackQ
    · intro σ hσ
      have hp : P.map σ.toEmbedding = P := congrArg Prod.fst (mem_filter.mp hσ).2
      have hq : Q.map σ.toEmbedding = Q := congrArg Prod.snd (mem_filter.mp hσ).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      apply Prod.ext
      · simpa only [Equiv.trans_toEmbedding, ← map_map, hp] using hτP
      · simpa only [Equiv.trans_toEmbedding, ← map_map, hq] using hτQ
    · intro σ _
      simp [Equiv.trans_assoc]
    · intro σ _
      simp [Equiv.trans_assoc]
  have hbelow (E : Finset (Finset α × Finset α)) (σ : Equiv.Perm α) :
      (E.bipartiteBelow R σ).card =
        if (P.map σ.toEmbedding, Q.map σ.toEmbedding) ∈ E then 1 else 0 := by
    by_cases he : (P.map σ.toEmbedding, Q.map σ.toEmbedding) ∈ E <;>
      simp [bipartiteBelow, R, filter_eq, he]
  have hcountF : F.card * d = (G.filter
      (fun σ => (P.map σ.toEmbedding, Q.map σ.toEmbedding) ∈ F)).card := by
    have hc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := F) (t := G) R
    have hleft : (∑ e ∈ F, (G.bipartiteAbove R e).card) = F.card * d := by
      calc
        _ = ∑ _e ∈ F, d := sum_congr rfl (fun e he => hdegree e (hF e he))
        _ = _ := by simp
    rw [hleft] at hc
    simpa only [hbelow, sum_boole, Nat.cast_id] using hc
  have hcountA : (disjointPairs (α := α) P.card Q.card).card * d = G.card := by
    have hc := card_mul_eq_card_mul
      (s := disjointPairs (α := α) P.card Q.card) (t := G) (m := d) (n := 1) R
      (fun e he => hdegree e (mem_disjointPairs.mp he))
      (fun σ _ => by
        rw [hbelow]
        have hm : (P.map σ.toEmbedding, Q.map σ.toEmbedding) ∈
            disjointPairs P.card Q.card := mem_disjointPairs.mpr
          ⟨by simp, by simp, (disjoint_map σ.toEmbedding).mpr hPQ⟩
        simp only [hm, if_true])
    simpa only [Nat.mul_one] using hc
  exact ⟨d, hd, hcountF, by simpa only [G, card_univ] using hcountA⟩

end Submissions.Erdos1020MatchingPermutationPairCount.Main

namespace Submissions.Erdos1020MatchingDisjointPairCard.Main

open Finset
open Submissions.Erdos1020MatchingPermutationPairCount.Main

/-- Count ordered disjoint pairs by first choosing the first set and then a
subset of its complement. Zero and oversized ranks require no separate guard. -/
theorem card_disjointPairs {α : Type*} [Fintype α] [DecidableEq α] (a b : ℕ) :
    (disjointPairs (α := α) a b).card =
      (Fintype.card α).choose a * (Fintype.card α - a).choose b := by
  classical
  have hfiber (S : Finset α) (hSa : S.card = a) :
      (disjointPairs a b).filter (fun e => e.1 = S) =
        {S} ×ˢ ((univ \ S).powersetCard b) := by
    ext ⟨R, T⟩
    simp only [mem_filter, mem_disjointPairs, mem_product, mem_singleton,
      mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hTb, hRT⟩, rfl⟩
      exact ⟨rfl, subset_sdiff.mpr ⟨subset_univ _, hRT.symm⟩, hTb⟩
    · rintro ⟨rfl, hTsub, hTb⟩
      exact ⟨⟨hSa, hTb, (subset_sdiff.mp hTsub).2.symm⟩, rfl⟩
  calc
    (disjointPairs (α := α) a b).card =
        ∑ S ∈ (univ : Finset α).powersetCard a,
          ((disjointPairs a b).filter (fun e => e.1 = S)).card :=
      card_eq_sum_card_fiberwise (f := Prod.fst) (fun e he =>
        mem_powersetCard_univ.mpr (mem_disjointPairs.mp he).1)
    _ = ∑ _S ∈ (univ : Finset α).powersetCard a,
        (Fintype.card α - a).choose b := by
      apply sum_congr rfl
      intro S hS
      have hSa : S.card = a := mem_powersetCard_univ.mp hS
      rw [hfiber S hSa, card_product, card_singleton, one_mul, card_powersetCard,
        card_sdiff_of_subset (subset_univ S), card_univ, hSa]
    _ = (Fintype.card α).choose a * (Fintype.card α - a).choose b := by simp

end Submissions.Erdos1020MatchingDisjointPairCard.Main

namespace Submissions.Erdos1020MatchingPairIncidence.Main

open Finset
open Submissions.Erdos1020MatchingPermutationPairCount.Main

/-- Two disjoint block images both belong to F at most as often as unrestricted
ordered pairs in F, after multiplying by the exact ambient pair count. -/
theorem pair_incidence_le {α : Type*} [Fintype α] [DecidableEq α]
    {ℓ : ℕ} (P Q : Finset α) (hP : P.card = ℓ) (hQ : Q.card = ℓ)
    (hPQ : Disjoint P Q) (F : Finset (Finset α))
    (hF : ∀ e ∈ F, e.card = ℓ) :
    (Fintype.card α).choose ℓ * (Fintype.card α - ℓ).choose ℓ *
        ((univ : Finset (Equiv.Perm α)).filter (fun σ =>
          P.map σ.toEmbedding ∈ F ∧ Q.map σ.toEmbedding ∈ F)).card ≤
      F.card * F.card * Fintype.card (Equiv.Perm α) := by
  classical
  let A := (F ×ˢ F).filter (fun e => Disjoint e.1 e.2)
  have hA (e : Finset α × Finset α) (he : e ∈ A) :
      e.1.card = P.card ∧ e.2.card = Q.card ∧ Disjoint e.1 e.2 := by
    obtain ⟨heF, heD⟩ := mem_filter.mp he
    obtain ⟨heP, heQ⟩ := mem_product.mp heF
    exact ⟨(hF _ heP).trans hP.symm, (hF _ heQ).trans hQ.symm, heD⟩
  obtain ⟨d, _, hcount, htotal⟩ := permutation_pair_fiber_count P Q hPQ A hA
  have hfilter : ((univ : Finset (Equiv.Perm α)).filter
      (fun σ => (P.map σ.toEmbedding, Q.map σ.toEmbedding) ∈ A)) =
        univ.filter (fun σ => P.map σ.toEmbedding ∈ F ∧ Q.map σ.toEmbedding ∈ F) := by
    ext σ
    have hd := (disjoint_map σ.toEmbedding).mpr hPQ
    simp only [A, mem_filter, mem_univ, true_and, mem_product, hd, and_true]
  rw [hfilter] at hcount
  rw [Submissions.Erdos1020MatchingDisjointPairCard.Main.card_disjointPairs,
    hP, hQ] at htotal
  have hAc : A.card ≤ F.card * F.card := by
    calc
      _ ≤ (F ×ˢ F).card := card_filter_le _ _
      _ = _ := card_product _ _
  calc
    _ = ((Fintype.card α).choose ℓ * (Fintype.card α - ℓ).choose ℓ) *
        (A.card * d) := by rw [hcount]
    _ = A.card * ((Fintype.card α).choose ℓ *
        (Fintype.card α - ℓ).choose ℓ * d) := by ac_rfl
    _ = A.card * Fintype.card (Equiv.Perm α) := by rw [htotal]
    _ ≤ _ := Nat.mul_le_mul_right _ hAc

end Submissions.Erdos1020MatchingPairIncidence.Main

namespace Submissions.Erdos1020MatchingFiniteMoments.Main

open Finset

/-- The number of events containing a sample. -/
def eventCount {Ω : Type*} [DecidableEq Ω] {t : ℕ}
    (E : Fin t → Finset Ω) (ω : Ω) : ℕ :=
  (univ.filter (fun i => ω ∈ E i)).card

/-- The rational average over a finite sample type. -/
def average {Ω : Type*} [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℚ)

/-- Counting sample-event incidences in either order gives the first moment. -/
theorem sum_eventCount {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {t : ℕ}
    (E : Fin t → Finset Ω) :
    (∑ ω, (eventCount E ω : ℚ)) = ∑ i, ((E i).card : ℚ) := by
  classical
  simp only [eventCount, natCast_card_filter]
  rw [sum_comm]
  simp only [sum_boole, filter_mem_eq_inter, univ_inter]

/-- The squared count enumerates ordered pairs of events, including the diagonal. -/
theorem sum_eventCount_sq {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {t : ℕ}
    (E : Fin t → Finset Ω) :
    (∑ ω, (eventCount E ω : ℚ) ^ 2) =
      ∑ i, ∑ j, ((E i ∩ E j).card : ℚ) := by
  classical
  have hcount (ω : Ω) : (eventCount E ω : ℚ) =
      ∑ i : Fin t, if ω ∈ E i then (1 : ℚ) else 0 :=
    natCast_card_filter _ _
  calc
    _ = ∑ ω, ∑ i : Fin t, ∑ j : Fin t,
        if ω ∈ E i ∩ E j then (1 : ℚ) else 0 := by
      apply sum_congr rfl
      intro ω _
      rw [hcount, pow_two, Fintype.sum_mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hi : ω ∈ E i <;> by_cases hj : ω ∈ E j <;> simp [hi, hj]
    _ = ∑ i : Fin t, ∑ j : Fin t, ∑ ω,
        if ω ∈ E i ∩ E j then (1 : ℚ) else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      simp only [sum_boole, filter_mem_eq_inter, univ_inter]

private theorem sum_diagonal {t : ℕ} (A B : ℚ) (i : Fin t) :
    (∑ j : Fin t, if i = j then A else B) = A + ((t : ℚ) - 1) * B := by
  classical
  calc
    _ = ∑ j : Fin t, ((if i = j then A - B else 0) + B) := by
      apply sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [h]
    _ = A - B + (t : ℚ) * B := by
      simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by ring1

/-- Equal marginals and a common off-diagonal incidence bound give the first two
moments and a variance at most six times the mean. No positive-density assumption
is required; subtraction in the rational t(t-1) factor is rational subtraction. -/
theorem moment_bounds {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {t : ℕ} (E : Fin t → Finset Ω) (α R : ℚ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hR : 1 ≤ R)
    (hsingle : ∀ i, ((E i).card : ℚ) = α * (Fintype.card Ω : ℚ))
    (hpair : ∀ i j, i ≠ j →
      ((E i ∩ E j).card : ℚ) ≤ α ^ 2 * R * (Fintype.card Ω : ℚ))
    (herror : (t : ℚ) * (R - 1) ≤ 5) :
    average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ) ∧
      average (fun ω => (eventCount E ω : ℚ) ^ 2) ≤
        α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R ∧
      average (fun ω => (eventCount E ω : ℚ) ^ 2) -
          (average (fun ω => (eventCount E ω : ℚ))) ^ 2 ≤
        6 * average (fun ω => (eventCount E ω : ℚ)) := by
  classical
  have hN : (0 : ℚ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  have hmean : average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ) := by
    unfold average
    apply (div_eq_iff hN.ne').mpr
    rw [sum_eventCount]
    simp_rw [hsingle]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring1
  have hsum2 : (∑ ω, (eventCount E ω : ℚ) ^ 2) ≤
      (α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R) *
        (Fintype.card Ω : ℚ) := by
    rw [sum_eventCount_sq]
    calc
      _ ≤ ∑ i : Fin t, ∑ j : Fin t,
          if i = j then α * (Fintype.card Ω : ℚ)
          else α ^ 2 * R * (Fintype.card Ω : ℚ) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        by_cases h : i = j
        · subst j
          rw [if_pos rfl, inter_self]
          exact (hsingle i).le
        · simpa only [if_neg h] using hpair i j h
      _ = (t : ℚ) * (α * (Fintype.card Ω : ℚ) +
          ((t : ℚ) - 1) * (α ^ 2 * R * (Fintype.card Ω : ℚ))) := by
        simp_rw [sum_diagonal]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by ring1
  have hsecond : average (fun ω => (eventCount E ω : ℚ) ^ 2) ≤
      α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R := by
    unfold average
    exact (div_le_iff₀ hN).mpr hsum2
  refine ⟨hmean, hsecond, ?_⟩
  rw [hmean]
  by_cases ht0 : t = 0
  · subst t
    simpa using hsecond
  have ht : (1 : ℚ) ≤ t := Nat.one_le_cast_iff_ne_zero.mpr ht0
  have ht_nonneg : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  have hμ : 0 ≤ α * (t : ℚ) := mul_nonneg hα0 ht_nonneg
  have hαsq : α ^ 2 ≤ α := by
    calc
      _ = α * α := pow_two α
      _ ≤ 1 * α := mul_le_mul_of_nonneg_right hα1 hα0
      _ = α := one_mul α
  have hcoeff : 0 ≤ (t : ℚ) * ((t : ℚ) - 1) :=
    mul_nonneg ht_nonneg (sub_nonneg.mpr ht)
  have hprod : (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 ≤ (t : ℚ) * (t : ℚ) * α := by
    calc
      _ ≤ (t : ℚ) * ((t : ℚ) - 1) * α :=
        mul_le_mul_of_nonneg_left hαsq hcoeff
      _ ≤ (t : ℚ) * (t : ℚ) * α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) ht_nonneg) hα0
  have hfirst : (α * (t : ℚ)) * (1 - α) ≤ α * (t : ℚ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (sub_le_self (1 : ℚ) hα0) hμ
  have hrest : (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * (R - 1) ≤
      (α * (t : ℚ)) * ((t : ℚ) * (R - 1)) := by
    calc
      _ ≤ ((t : ℚ) * (t : ℚ) * α) * (R - 1) :=
        mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr hR)
      _ = _ := by ring1
  calc
    _ ≤ (α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R) -
        (α * (t : ℚ)) ^ 2 := sub_le_sub_right hsecond _
    _ = (α * (t : ℚ)) * (1 - α) +
        (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * (R - 1) := by ring1
    _ ≤ α * (t : ℚ) + (α * (t : ℚ)) * ((t : ℚ) * (R - 1)) :=
      add_le_add hfirst hrest
    _ ≤ α * (t : ℚ) + (α * (t : ℚ)) * 5 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left herror hμ)
    _ = _ := by ring1

end Submissions.Erdos1020MatchingFiniteMoments.Main

namespace Submissions.Erdos1020MatchingTripleChoose.Main

/-- The cubic formula is rational arithmetic after the natural subtraction guards. -/
theorem six_mul_choose_three {m : ℕ} (hm : 2 ≤ m) :
    (6 : ℚ) * (m.choose 3 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) := by
  have hm1 : 1 ≤ m := by omega
  have h := congrArg (fun a : ℕ => (a : ℚ))
    (Nat.descFactorial_eq_factorial_mul_choose m 3)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
    Nat.cast_sub hm, Nat.cast_sub hm1] at h
  nlinarith only [h]

theorem choose_sub_three_pos {m : ℕ} (hm : 20 ≤ m) :
    0 < (m - 3).choose 3 := by
  exact Nat.choose_pos (by omega)

/-- A uniform bound for the loss of three vertices in the triple denominator. -/
theorem ratio_bound {m : ℕ} {t : ℚ} (hm : 20 ≤ m)
    (_ht0 : 0 ≤ t) (ht : t ≤ (m : ℚ) / 3) :
    t * ((m.choose 3 : ℚ) / ((m - 3).choose 3 : ℚ) - 1) ≤ 5 := by
  let C : ℚ := m.choose 3
  let D : ℚ := (m - 3).choose 3
  have hD : 0 < D := (Nat.cast_pos (α := ℚ)).mpr (choose_sub_three_pos hm)
  have hDC : D ≤ C :=
    (Nat.cast_le (α := ℚ)).mpr (Nat.choose_le_choose 3 (Nat.sub_le m 3))
  have hC : 6 * C = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) :=
    six_mul_choose_three (by omega)
  have hDm := six_mul_choose_three (m := m - 3) (by omega)
  have hm3 : 3 ≤ m := by omega
  have hDf : 6 * D = ((m : ℚ) - 3) * ((m : ℚ) - 4) * ((m : ℚ) - 5) := by
    norm_num only [Nat.cast_sub hm3, Nat.cast_ofNat] at hDm
    dsimp only [D]
    nlinarith only [hDm]
  have hdiff : 6 * (C - D) = 9 * (m : ℚ) ^ 2 - 45 * (m : ℚ) + 60 := by
    nlinarith only [hC, hDf]
  have hdiffMul := congrArg (fun a : ℚ => (m : ℚ) * a) hdiff
  have hmQ : (20 : ℚ) ≤ m := (Nat.cast_le (α := ℚ)).mpr hm
  have hu : 0 ≤ (m : ℚ) - 20 := sub_nonneg.mpr hmQ
  have hu2 : 0 ≤ ((m : ℚ) - 20) ^ 2 := sq_nonneg _
  have hu3 : 0 ≤ ((m : ℚ) - 20) ^ 2 * ((m : ℚ) - 20) := mul_nonneg hu2 hu
  have hpoly : 0 ≤ 2 * (m : ℚ) ^ 3 - 45 * (m : ℚ) ^ 2 + 215 * (m : ℚ) - 300 := by
    nlinarith only [hu, hu2, hu3]
  have hcore : (m : ℚ) * (C - D) ≤ 15 * D := by
    nlinarith only [hDf, hdiffMul, hpoly]
  have hupper : (m : ℚ) / 3 * (C / D - 1) ≤ 5 := by
    rw [div_sub_one (ne_of_gt hD), ← mul_div_assoc]
    apply (div_le_iff₀ hD).mpr
    nlinarith only [hcore]
  have hratio : 0 ≤ C / D - 1 := sub_nonneg.mpr ((one_le_div₀ hD).mpr hDC)
  exact (mul_le_mul_of_nonneg_right ht hratio).trans hupper

/-- The triple-density comparison remains valid in every larger ambient set. -/
theorem choose_le_two_choose_sub {m s : ℕ} (hs : 14 ≤ s) (hm : 5 * s - 1 ≤ m) :
    m.choose 3 ≤ 2 * (m - s).choose 3 := by
  have hC := six_mul_choose_three (m := m) (by omega)
  have hD := six_mul_choose_three (m := m - s) (by omega)
  have hms : s ≤ m := by omega
  norm_num only [Nat.cast_sub hms, Nat.cast_ofNat] at hD
  have hsQ : (14 : ℚ) ≤ s := (Nat.cast_le (α := ℚ)).mpr hs
  have hs0 : (0 : ℚ) ≤ s := by linarith only [hsQ]
  have hmQ : 5 * (s : ℚ) - 1 ≤ m := by
    have h := (Nat.cast_le (α := ℚ)).mpr hm
    have h5s : 1 ≤ 5 * s := by omega
    norm_num only [Nat.cast_sub h5s, Nat.cast_mul, Nat.cast_ofNat] at h
    exact h
  let v : ℚ := (m : ℚ) - (5 * (s : ℚ) - 1)
  have hv : 0 ≤ v := sub_nonneg.mpr hmQ
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg _
  have hterm1 : 0 ≤ v ^ 2 * v := mul_nonneg hv2 hv
  have hcoeff2 : 0 ≤ 9 * (s : ℚ) - 6 := by linarith only [hsQ]
  have hterm2 : 0 ≤ (9 * (s : ℚ) - 6) * v ^ 2 := mul_nonneg hcoeff2 hv2
  have hss := mul_le_mul_of_nonneg_right hsQ hs0
  have hcoeff3 : 0 ≤ 21 * (s : ℚ) ^ 2 - 36 * (s : ℚ) + 11 := by
    nlinarith only [hss, hsQ]
  have hterm3 : 0 ≤ (21 * (s : ℚ) ^ 2 - 36 * (s : ℚ) + 11) * v :=
    mul_nonneg hcoeff3 hv
  have hbase : 0 ≤ (s : ℚ) ^ 2 * ((s : ℚ) - 14) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsQ)
  dsimp only [v] at hterm1 hterm2 hterm3
  apply (Nat.cast_le (α := ℚ)).mp
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hC, hD, hterm1, hterm2, hterm3, hbase, hsQ]

/-- The boundary triple-density comparison for the rank-four tail. -/
theorem choose_five_le_two_choose_four {s : ℕ} (hs : 14 ≤ s) :
    (5 * s - 1).choose 3 ≤ 2 * (4 * s - 1).choose 3 := by
  have h := choose_le_two_choose_sub (m := 5 * s - 1) hs le_rfl
  simpa only [show 5 * s - 1 - s = 4 * s - 1 by omega] using h

end Submissions.Erdos1020MatchingTripleChoose.Main

namespace Submissions.Erdos1020MatchingPermutationMoments.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main

def blockEvents {α : Type*} [Fintype α] [DecidableEq α] {t : ℕ}
    (P : Fin t → Finset α) (F : Finset (Finset α)) :
    Fin t → Finset (Equiv.Perm α) :=
  fun i => univ.filter (fun σ => (P i).map σ.toEmbedding ∈ F)

/-- Exact marginal for a relabeled block; the whole permutation space is used. -/
theorem single_event_card {α : Type*} [Fintype α] [DecidableEq α]
    {ℓ : ℕ} (P : Finset α) (hP : P.card = ℓ)
    (F : Finset (Finset α)) (hF : ∀ e ∈ F, e.card = ℓ) :
    (((univ : Finset (Equiv.Perm α)).filter
      (fun σ => P.map σ.toEmbedding ∈ F)).card : ℚ) =
      (F.card : ℚ) / ((Fintype.card α).choose ℓ : ℚ) *
        (Fintype.card (Equiv.Perm α) : ℚ) := by
  classical
  obtain ⟨d, _, hcount, htotal⟩ :=
    Submissions.Erdos1020MatchingRainbowAverage.Main.permutation_fiber_count
      P F (fun e he => (hF e he).trans hP.symm)
  rw [hP] at htotal
  have hℓ : ℓ ≤ Fintype.card α := hP ▸ card_le_univ P
  have hC : (0 : ℚ) < (Fintype.card α).choose ℓ :=
    Nat.cast_pos.mpr (Nat.choose_pos hℓ)
  have hn : (Fintype.card α).choose ℓ *
      ((univ : Finset (Equiv.Perm α)).filter
        (fun σ => P.map σ.toEmbedding ∈ F)).card =
      F.card * Fintype.card (Equiv.Perm α) := by
    rw [← hcount, ← htotal]
    ac_rfl
  have hq : ((Fintype.card α).choose ℓ : ℚ) *
      (((univ : Finset (Equiv.Perm α)).filter
        (fun σ => P.map σ.toEmbedding ∈ F)).card : ℚ) =
      (F.card : ℚ) * (Fintype.card (Equiv.Perm α) : ℚ) := by
    exact_mod_cast hn
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hC.ne').mpr
  nlinarith only [hq]

/-- Every family has its exact first moment, including the empty family. -/
theorem block_mean {α : Type*} [Fintype α] [DecidableEq α] {t ℓ : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = ℓ)
    (F : Finset (Finset α)) (hF : ∀ e ∈ F, e.card = ℓ) :
    average (fun σ => (eventCount (blockEvents P F) σ : ℚ)) =
      (F.card : ℚ) / ((Fintype.card α).choose ℓ : ℚ) * (t : ℚ) := by
  classical
  have hN : (0 : ℚ) < Fintype.card (Equiv.Perm α) :=
    Nat.cast_pos.mpr Fintype.card_pos
  unfold average
  apply (div_eq_iff hN.ne').mpr
  rw [sum_eventCount]
  have hsingle (i : Fin t) := single_event_card (P i) (hP i) F hF
  change ∀ i, ((blockEvents P F i).card : ℚ) = _ at hsingle
  simp_rw [hsingle]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring1

/-- Disjoint triples have variance at most six times their mean in every
ambient set of size at least twenty with room for the selected blocks. -/
theorem triple_moments {α : Type*} [Fintype α] [DecidableEq α] {t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = 3)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Finset (Finset α)) (hF : ∀ e ∈ F, e.card = 3)
    (hm : 20 ≤ Fintype.card α) (ht : 3 * t ≤ Fintype.card α) :
    average (fun σ => (eventCount (blockEvents P F) σ : ℚ)) =
        (F.card : ℚ) / ((Fintype.card α).choose 3 : ℚ) * (t : ℚ) ∧
      average (fun σ => (eventCount (blockEvents P F) σ : ℚ) ^ 2) -
          (average (fun σ => (eventCount (blockEvents P F) σ : ℚ))) ^ 2 ≤
        6 * average (fun σ => (eventCount (blockEvents P F) σ : ℚ)) := by
  classical
  let C : ℚ := (Fintype.card α).choose 3
  let D : ℚ := (Fintype.card α - 3).choose 3
  let a : ℚ := (F.card : ℚ) / C
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hD : 0 < D := Nat.cast_pos.mpr
    (Submissions.Erdos1020MatchingTripleChoose.Main.choose_sub_three_pos hm)
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hC.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one₀ hC).mpr
    apply Nat.cast_le.mpr
    calc
      F.card ≤ (univ.powersetCard 3 : Finset (Finset α)).card :=
        card_le_card (fun e he => mem_powersetCard_univ.mpr (hF e he))
      _ = _ := by simp
  have hR : 1 ≤ C / D := (one_le_div₀ hD).mpr
    (Nat.cast_le.mpr (Nat.choose_le_choose 3 (Nat.sub_le _ _)))
  have hsingle (i : Fin t) : ((blockEvents P F i).card : ℚ) =
      a * (Fintype.card (Equiv.Perm α) : ℚ) :=
    single_event_card (P i) (hP i) F hF
  have hpair (i j : Fin t) (hij : i ≠ j) :
      ((blockEvents P F i ∩ blockEvents P F j).card : ℚ) ≤
        a ^ 2 * (C / D) * (Fintype.card (Equiv.Perm α) : ℚ) := by
    have hn := Submissions.Erdos1020MatchingPairIncidence.Main.pair_incidence_le
      (P i) (P j) (hP i) (hP j) (hPd hij) F hF
    have he : blockEvents P F i ∩ blockEvents P F j =
        (univ : Finset (Equiv.Perm α)).filter (fun σ =>
          (P i).map σ.toEmbedding ∈ F ∧ (P j).map σ.toEmbedding ∈ F) := by
      ext σ
      simp [blockEvents]
    rw [← he] at hn
    have hq : C * D * ((blockEvents P F i ∩ blockEvents P F j).card : ℚ) ≤
        (F.card : ℚ) * (F.card : ℚ) * (Fintype.card (Equiv.Perm α) : ℚ) := by
      dsimp only [C, D]
      exact_mod_cast hn
    have hid : a ^ 2 * (C / D) * (Fintype.card (Equiv.Perm α) : ℚ) =
        ((F.card : ℚ) * (F.card : ℚ) * (Fintype.card (Equiv.Perm α) : ℚ)) /
          (C * D) := by
      dsimp only [a]
      field_simp [hC.ne', hD.ne']
    rw [hid]
    apply (le_div_iff₀ (mul_pos hC hD)).mpr
    nlinarith only [hq]
  have herror : (t : ℚ) * (C / D - 1) ≤ 5 := by
    apply Submissions.Erdos1020MatchingTripleChoose.Main.ratio_bound hm (Nat.cast_nonneg _)
    have htq : (3 : ℚ) * t ≤ Fintype.card α := by exact_mod_cast ht
    linarith only [htq]
  have h := moment_bounds (blockEvents P F) a (C / D) ha0 ha1 hR hsingle hpair herror
  exact ⟨h.1, h.2.2⟩

end Submissions.Erdos1020MatchingPermutationMoments.Main

namespace Submissions.Erdos1020MatchingFiniteVariance.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main

private theorem sum_diagonal {t : ℕ} (A B : ℚ) (i : Fin t) :
    (∑ j : Fin t, if i = j then A else B) = A + ((t : ℚ) - 1) * B := by
  classical
  calc
    _ = ∑ j : Fin t, ((if i = j then A - B else 0) + B) := by
      apply sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [h]
    _ = A - B + (t : ℚ) * B := by
      simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by ring1

/-- Equal marginals and a common off-diagonal incidence bound give the first two
moments and a variance at most (β+1) times the mean. No positive-density assumption
is required; subtraction in the rational t(t-1) factor is rational subtraction. -/
theorem moment_bounds_with_error {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {t : ℕ} (E : Fin t → Finset Ω) (α R β : ℚ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hR : 1 ≤ R)
    (hsingle : ∀ i, ((E i).card : ℚ) = α * (Fintype.card Ω : ℚ))
    (hpair : ∀ i j, i ≠ j →
      ((E i ∩ E j).card : ℚ) ≤ α ^ 2 * R * (Fintype.card Ω : ℚ))
    (herror : (t : ℚ) * (R - 1) ≤ β) :
    average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ) ∧
      average (fun ω => (eventCount E ω : ℚ) ^ 2) ≤
        α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R ∧
      average (fun ω => (eventCount E ω : ℚ) ^ 2) -
          (average (fun ω => (eventCount E ω : ℚ))) ^ 2 ≤
        (β + 1) * average (fun ω => (eventCount E ω : ℚ)) := by
  classical
  have hN : (0 : ℚ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  have hmean : average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ) := by
    unfold average
    apply (div_eq_iff hN.ne').mpr
    rw [sum_eventCount]
    simp_rw [hsingle]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring1
  have hsum2 : (∑ ω, (eventCount E ω : ℚ) ^ 2) ≤
      (α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R) *
        (Fintype.card Ω : ℚ) := by
    rw [sum_eventCount_sq]
    calc
      _ ≤ ∑ i : Fin t, ∑ j : Fin t,
          if i = j then α * (Fintype.card Ω : ℚ)
          else α ^ 2 * R * (Fintype.card Ω : ℚ) := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        by_cases h : i = j
        · subst j
          rw [if_pos rfl, inter_self]
          exact (hsingle i).le
        · simpa only [if_neg h] using hpair i j h
      _ = (t : ℚ) * (α * (Fintype.card Ω : ℚ) +
          ((t : ℚ) - 1) * (α ^ 2 * R * (Fintype.card Ω : ℚ))) := by
        simp_rw [sum_diagonal]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = _ := by ring1
  have hsecond : average (fun ω => (eventCount E ω : ℚ) ^ 2) ≤
      α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R := by
    unfold average
    exact (div_le_iff₀ hN).mpr hsum2
  refine ⟨hmean, hsecond, ?_⟩
  rw [hmean]
  by_cases ht0 : t = 0
  · subst t
    simpa using hsecond
  have ht : (1 : ℚ) ≤ t := Nat.one_le_cast_iff_ne_zero.mpr ht0
  have ht_nonneg : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  have hμ : 0 ≤ α * (t : ℚ) := mul_nonneg hα0 ht_nonneg
  have hαsq : α ^ 2 ≤ α := by
    calc
      _ = α * α := pow_two α
      _ ≤ 1 * α := mul_le_mul_of_nonneg_right hα1 hα0
      _ = α := one_mul α
  have hcoeff : 0 ≤ (t : ℚ) * ((t : ℚ) - 1) :=
    mul_nonneg ht_nonneg (sub_nonneg.mpr ht)
  have hprod : (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 ≤ (t : ℚ) * (t : ℚ) * α := by
    calc
      _ ≤ (t : ℚ) * ((t : ℚ) - 1) * α :=
        mul_le_mul_of_nonneg_left hαsq hcoeff
      _ ≤ (t : ℚ) * (t : ℚ) * α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) ht_nonneg) hα0
  have hfirst : (α * (t : ℚ)) * (1 - α) ≤ α * (t : ℚ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (sub_le_self (1 : ℚ) hα0) hμ
  have hrest : (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * (R - 1) ≤
      (α * (t : ℚ)) * ((t : ℚ) * (R - 1)) := by
    calc
      _ ≤ ((t : ℚ) * (t : ℚ) * α) * (R - 1) :=
        mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr hR)
      _ = _ := by ring1
  calc
    _ ≤ (α * (t : ℚ) + (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * R) -
        (α * (t : ℚ)) ^ 2 := sub_le_sub_right hsecond _
    _ = (α * (t : ℚ)) * (1 - α) +
        (t : ℚ) * ((t : ℚ) - 1) * α ^ 2 * (R - 1) := by ring1
    _ ≤ α * (t : ℚ) + (α * (t : ℚ)) * ((t : ℚ) * (R - 1)) :=
      add_le_add hfirst hrest
    _ ≤ α * (t : ℚ) + (α * (t : ℚ)) * β :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left herror hμ)
    _ = _ := by ring1


end Submissions.Erdos1020MatchingFiniteVariance.Main

namespace Submissions.Erdos1020MatchingPermutationVariance.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main
open Submissions.Erdos1020MatchingPermutationMoments.Main

/-- Exact mean and variance from a supplied positive-binomial ratio error.
The later ambient estimate must discharge the error hypothesis. -/
theorem block_moments {α : Type*} [Fintype α] [DecidableEq α] {t ℓ : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = ℓ)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Finset (Finset α)) (hF : ∀ e ∈ F, e.card = ℓ)
    (hm : 2 * ℓ ≤ Fintype.card α) (β : ℚ)
    (herror : (t : ℚ) * (((Fintype.card α).choose ℓ : ℚ) /
      ((Fintype.card α - ℓ).choose ℓ : ℚ) - 1) ≤ β) :
    average (fun σ => (eventCount (blockEvents P F) σ : ℚ)) =
        (F.card : ℚ) / ((Fintype.card α).choose ℓ : ℚ) * (t : ℚ) ∧
      average (fun σ => (eventCount (blockEvents P F) σ : ℚ) ^ 2) -
          (average (fun σ => (eventCount (blockEvents P F) σ : ℚ))) ^ 2 ≤
        (β + 1) * average (fun σ => (eventCount (blockEvents P F) σ : ℚ)) := by
  classical
  let C : ℚ := (Fintype.card α).choose ℓ
  let D : ℚ := (Fintype.card α - ℓ).choose ℓ
  let a : ℚ := (F.card : ℚ) / C
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hD : 0 < D := Nat.cast_pos.mpr
    (Nat.choose_pos (by omega))
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hC.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one₀ hC).mpr
    apply Nat.cast_le.mpr
    calc
      F.card ≤ (univ.powersetCard ℓ : Finset (Finset α)).card :=
        card_le_card (fun e he => mem_powersetCard_univ.mpr (hF e he))
      _ = _ := by simp
  have hR : 1 ≤ C / D := (one_le_div₀ hD).mpr
    (Nat.cast_le.mpr (Nat.choose_le_choose ℓ (Nat.sub_le _ _)))
  have hsingle (i : Fin t) : ((blockEvents P F i).card : ℚ) =
      a * (Fintype.card (Equiv.Perm α) : ℚ) :=
    single_event_card (P i) (hP i) F hF
  have hpair (i j : Fin t) (hij : i ≠ j) :
      ((blockEvents P F i ∩ blockEvents P F j).card : ℚ) ≤
        a ^ 2 * (C / D) * (Fintype.card (Equiv.Perm α) : ℚ) := by
    have hn := Submissions.Erdos1020MatchingPairIncidence.Main.pair_incidence_le
      (P i) (P j) (hP i) (hP j) (hPd hij) F hF
    have he : blockEvents P F i ∩ blockEvents P F j =
        (univ : Finset (Equiv.Perm α)).filter (fun σ =>
          (P i).map σ.toEmbedding ∈ F ∧ (P j).map σ.toEmbedding ∈ F) := by
      ext σ
      simp [blockEvents]
    rw [← he] at hn
    have hq : C * D * ((blockEvents P F i ∩ blockEvents P F j).card : ℚ) ≤
        (F.card : ℚ) * (F.card : ℚ) * (Fintype.card (Equiv.Perm α) : ℚ) := by
      dsimp only [C, D]
      exact_mod_cast hn
    have hid : a ^ 2 * (C / D) * (Fintype.card (Equiv.Perm α) : ℚ) =
        ((F.card : ℚ) * (F.card : ℚ) * (Fintype.card (Equiv.Perm α) : ℚ)) /
          (C * D) := by
      dsimp only [a]
      field_simp [hC.ne', hD.ne']
    rw [hid]
    apply (le_div_iff₀ (mul_pos hC hD)).mpr
    nlinarith only [hq]
  have h := Submissions.Erdos1020MatchingFiniteVariance.Main.moment_bounds_with_error (blockEvents P F) a (C / D) β ha0 ha1 hR hsingle hpair herror
  exact ⟨h.1, h.2.2⟩


end Submissions.Erdos1020MatchingPermutationVariance.Main

namespace Submissions.Erdos1020MatchingFKFinite.Main

open Finset

/-- The Hall-deficient suffix retains an upper bound on the last family and
the unweighted total without imposing a block-count threshold. -/
theorem exists_suffix_bound {s t : ℕ} (A : Fin (s + 1) → Finset (Fin t))
    (hnested : ∀ i j, i ≤ j → A j ⊆ A i)
    (hno : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A i) :
    ∃ u : ℕ, (A (Fin.last s)).card ≤ u ∧ u ≤ s ∧
      (∑ i, (A i).card) ≤ (s - u) * t + (u + 1) * u := by
  classical
  have hHall : ¬ ∀ D : Finset (Fin (s + 1)), D.card ≤ (D.biUnion A).card :=
    fun h => hno ((all_card_le_biUnion_card_iff_existsInjective' A).mp h)
  push Not at hHall
  obtain ⟨D, hdef⟩ := hHall
  have hDne : D.Nonempty := card_pos.mp (by omega)
  let i := D.min' hDne
  have hiD : i ∈ D := D.min'_mem hDne
  have hmin : ∀ j ∈ D, i ≤ j := fun j hj => D.min'_le j hj
  have hDcard : D.card ≤ s + 1 - i.val := by
    calc
      _ ≤ (Ici i).card := card_le_card (by
        intro j hj
        exact mem_Ici.mpr (hmin j hj))
      _ = _ := Fin.card_Ici i
  have hAi : (A i).card ≤ s - i.val := by
    have hsub : A i ⊆ D.biUnion A := by
      intro v hv
      exact mem_biUnion.mpr ⟨i, hiD, hv⟩
    have hsmall := (card_le_card hsub).trans_lt hdef
    omega
  let u := s - i.val
  have hi : i.val ≤ s := Nat.le_of_lt_succ i.isLt
  have hiu : i.val + u = s := Nat.add_sub_of_le hi
  have hus : u ≤ s := Nat.sub_le _ _
  have hsuffix : ∀ j, i ≤ j → (A j).card ≤ u :=
    fun j hj => (card_le_card (hnested i j hj)).trans hAi
  have hlast : (A (Fin.last s)).card ≤ u := hsuffix _ (Fin.le_last i)
  have hprefixSum : (∑ j ∈ Iio i, (A j).card) ≤ i.val * t := by
    calc
      _ ≤ ∑ _j ∈ Iio i, t := sum_le_sum (by
        intro j _
        simpa using card_le_univ (A j))
      _ = _ := by simp
  have hsuffixSum : (∑ j ∈ Ici i, (A j).card) ≤ (u + 1) * u := by
    calc
      _ ≤ ∑ _j ∈ Ici i, u := sum_le_sum (by
        intro j hj
        exact hsuffix j (mem_Ici.mp hj))
      _ = _ := by
        simp only [sum_const, Fin.card_Ici, Nat.nsmul_eq_mul]
        congr 1
        omega
  have hcover : Iio i ∪ Ici i = (univ : Finset (Fin (s + 1))) := by
    ext j
    simp only [mem_union, mem_Iio, mem_Ici, mem_univ, iff_true]
    exact lt_or_ge j i
  have hdisj : Disjoint (Iio i) (Ici i) := by
    apply disjoint_left.mpr
    intro j hj hi'
    exact (not_lt_of_ge (mem_Ici.mp hi')) (mem_Iio.mp hj)
  have hsum : (∑ j, (A j).card) ≤ i.val * t + (u + 1) * u := by
    calc
      _ = ∑ j ∈ Iio i ∪ Ici i, (A j).card := by rw [hcover]
      _ = (∑ j ∈ Iio i, (A j).card) +
          ∑ j ∈ Ici i, (A j).card := sum_union hdisj
      _ ≤ _ := Nat.add_le_add hprefixSum hsuffixSum
  refine ⟨u, hlast, hus, ?_⟩
  have hieq : i.val = s - u := by omega
  simpa only [hieq] using hsum

/-- The two finite weighted estimates of Frankl--Kupavskii Lemma 18.
The sum includes every family once, then adds the extra last-family weight.
All subtractions in the weighted conclusions are rational. -/
theorem weighted_bounds {s t : ℕ} (A : Fin (s + 1) → Finset (Fin t))
    (hnested : ∀ i j, i ≤ j → A j ⊆ A i)
    (hno : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A i)
    (x q : ℚ) (_hx : 1 ≤ x) (_hxs : x ≤ (s : ℚ) + 1)
    (_hq : 1 ≤ q) (hqs : q ≤ (s : ℚ) + 1)
    (ht : (s : ℚ) + x + 1 ≤ (t : ℚ)) :
    (x ≤ ((A (Fin.last s)).card : ℚ) →
      (∑ i, ((A i).card : ℚ)) + (q - 1) * (A (Fin.last s)).card ≤
        (s : ℚ) * t + q * (A (Fin.last s)).card - (s : ℚ) * x) ∧
    (((A (Fin.last s)).card : ℚ) ≤ x →
      (∑ i, ((A i).card : ℚ)) + (q - 1) * (A (Fin.last s)).card ≤
        (s : ℚ) * t - (A (Fin.last s)).card *
          (x - q * (A (Fin.last s)).card / ((s : ℚ) + 1))) := by
  classical
  obtain ⟨u, hzu, hus, hsum⟩ := exists_suffix_bound A hnested hno
  let z : ℚ := (A (Fin.last s)).card
  let W : ℚ := (∑ i, ((A i).card : ℚ)) + (q - 1) * z
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hu : 0 ≤ (u : ℚ) := Nat.cast_nonneg _
  have hzuq : z ≤ (u : ℚ) := Nat.cast_le.mpr hzu
  have husq : (u : ℚ) ≤ (s : ℚ) := Nat.cast_le.mpr hus
  have hsumq : (∑ i, ((A i).card : ℚ)) ≤
      ((s : ℚ) - (u : ℚ)) * t + ((u : ℚ) + 1) * u := by
    have h := (Nat.cast_le (α := ℚ)).mpr hsum
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hus,
      Nat.cast_one] using h
  have hmul := mul_le_mul_of_nonneg_left ht hu
  have hcommon : W + (u : ℚ) * ((s : ℚ) + x - u) ≤
      (s : ℚ) * t + (q - 1) * z := by
    dsimp only [W]
    nlinarith only [hsumq, hmul]
  change (x ≤ z → W ≤ (s : ℚ) * t + q * z - (s : ℚ) * x) ∧
    (z ≤ x → W ≤ (s : ℚ) * t - z * (x - q * z / ((s : ℚ) + 1)))
  constructor
  · intro hxz
    have hprod : 0 ≤ ((u : ℚ) - x) * ((s : ℚ) - u) :=
      mul_nonneg (sub_nonneg.mpr (hxz.trans hzuq)) (sub_nonneg.mpr husq)
    nlinarith only [hcommon, hprod, hz]
  · intro hzx
    have hquadprod : 0 ≤ ((u : ℚ) - z) * ((s : ℚ) + x - u - z) :=
      mul_nonneg (sub_nonneg.mpr hzuq) (by linarith only [husq, hzx])
    have hquad : z * ((s : ℚ) + x - z) ≤
        (u : ℚ) * ((s : ℚ) + x - u) := by
      nlinarith only [hquadprod]
    have hden : 0 < (s : ℚ) + 1 := by
      have hs : (0 : ℚ) ≤ (s : ℚ) := Nat.cast_nonneg s
      linarith only [hs]
    have hprod : 0 ≤ ((s : ℚ) + 1 - q) * ((s : ℚ) + 1 - z) :=
      mul_nonneg (sub_nonneg.mpr hqs) (by linarith only [hzuq, husq])
    have hdiv : q + z - (s : ℚ) - 1 ≤ q * z / ((s : ℚ) + 1) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [hprod]
    have hmuldiv := mul_le_mul_of_nonneg_left hdiv hz
    nlinarith only [hcommon, hquad, hmuldiv]

end Submissions.Erdos1020MatchingFKFinite.Main

namespace Submissions.Erdos1020MatchingFKQuadratic.Main

/-- The Hall suffix deficit gives one quadratic bound, for every coefficient q. -/
theorem quadratic_of_suffix {s x q z u W t : ℚ}
    (hs : 0 < s) (hx : 0 ≤ x) (hxs : x ≤ s)
    (hz : 0 ≤ z) (hzu : z ≤ u) (hus : u ≤ s)
    (hcommon : W + u * (s + x - u) ≤ s * t + (q - 1) * z) :
    W - s * t ≤ (q - 2 * x) * z + (x / s) * z ^ 2 := by
  have hu : 0 ≤ u := hz.trans hzu
  have hzs : z ≤ s := hzu.trans hus
  have hfirst : 0 ≤ u * (s - x) * (s - u) :=
    mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hxs)) (sub_nonneg.mpr hus)
  have hsecond : 0 ≤ x * (u - z) * (2 * s - u - z) :=
    mul_nonneg (mul_nonneg hx (sub_nonneg.mpr hzu)) (by linarith only [hus, hzs])
  have hdeficit : x * z * (2 * s - z) ≤ s * u * (s + x - u) := by
    nlinarith only [hfirst, hsecond]
  have hscaledCommon := mul_le_mul_of_nonneg_left hcommon hs.le
  have hsz : 0 ≤ s * z := mul_nonneg hs.le hz
  have hscaled : s * (W - s * t) ≤ s * q * z - x * z * (2 * s - z) := by
    nlinarith only [hdeficit, hscaledCommon, hsz]
  have heq : (q - 2 * x) * z + (x / s) * z ^ 2 =
      (s * q * z - x * z * (2 * s - z)) / s := by
    field_simp [ne_of_gt hs]
    ring
  rw [heq]
  apply (le_div_iff₀ hs).mpr
  nlinarith only [hscaled]

/-- Coefficients at most x make the quadratic nonpositive pointwise. -/
theorem pointwise_of_small_coefficient {s x q z W t : ℚ}
    (hs : 0 < s) (hx : 0 ≤ x) (hz : 0 ≤ z) (hzs : z ≤ s)
    (hqx : q ≤ x)
    (hbound : W - s * t ≤ (q - 2 * x) * z + (x / s) * z ^ 2) :
    W ≤ s * t := by
  have hratio : z / s ≤ 1 := (div_le_iff₀ hs).mpr (by simpa using hzs)
  have hfirst : (q - x) * z ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqx) hz
  have hsecond : x * z * (z / s - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx hz) (by linarith only [hratio])
  have heq : (q - 2 * x) * z + (x / s) * z ^ 2 =
      (q - x) * z + x * z * (z / s - 1) := by ring
  linarith only [hbound, hfirst, hsecond, heq]

/-- Exact interval estimate for the coefficient after a relative second-moment bound. -/
theorem coefficient_bound {s x q p : ℚ}
    (hs : 400 ≤ s) (hxl : 2 * s / 3 - 2 ≤ x) (hxu : x ≤ 2 * s / 3)
    (hxq : x < q) (hq : q ≤ 1 + 3 * s / 4)
    (hp : p ≤ 5 * s ^ 2 / 8 + 5 * s / 3) :
    q - 2 * x + (x / s) * (p / q + 6) ≤ 0 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hx0 : 0 < x := by linarith only [hs, hxl]
  have hq0 : 0 < q := hx0.trans hxq
  let Q : ℚ := 1 + 3 * s / 4
  have hqQ : q ≤ Q := hq
  have hxQ : x < Q := hxq.trans_le hqQ
  have hL0 : 0 ≤ 2 * s / 3 - 2 := by linarith only [hs]
  have hs184 : 0 ≤ s * (s - 184) :=
    mul_nonneg hs0.le (by linarith only [hs])
  have hs400 : 400 * s ≤ s * s := mul_le_mul_of_nonneg_right hs hs0.le
  have hxlScaled := mul_le_mul_of_nonneg_left hxl hs0.le
  have hleftInner : p - s * x + 6 * x ≤ 0 := by
    nlinarith only [hp, hxlScaled, hxu, hs184]
  have hleft : s * x ^ 2 + (6 * x - 2 * s * x) * x + x * p ≤ 0 := by
    have h := mul_nonpos_of_nonneg_of_nonpos hx0.le hleftInner
    nlinarith only [h]
  have hnegative : p + (6 - 2 * s) * Q ≤ 0 := by
    dsimp only [Q]
    nlinarith only [hp, hs400, hs]
  have hrightX := mul_le_mul_of_nonpos_right hxl hnegative
  have hrightP := mul_le_mul_of_nonneg_left hp hL0
  have hcubic : 0 ≤ s ^ 2 * (3 * s - 868) :=
    mul_nonneg (sq_nonneg s) (by linarith only [hs])
  have hright : s * Q ^ 2 + (6 * x - 2 * s * x) * Q + x * p ≤ 0 := by
    dsimp only [Q] at hrightX ⊢
    nlinarith only [hrightX, hrightP, hcubic, hs0.le]
  have hqx0 : 0 ≤ q - x := sub_nonneg.mpr hxq.le
  have hQq0 : 0 ≤ Q - q := sub_nonneg.mpr hqQ
  have hQx0 : 0 < Q - x := sub_pos.mpr hxQ
  have hleftWeighted := mul_le_mul_of_nonneg_left hleft hQq0
  have hrightWeighted := mul_le_mul_of_nonneg_left hright hqx0
  have herror : 0 ≤ s * (q - x) * (Q - q) * (Q - x) :=
    mul_nonneg (mul_nonneg (mul_nonneg hs0.le hqx0) hQq0) hQx0.le
  have hscaled : (Q - x) *
      (s * q ^ 2 + (6 * x - 2 * s * x) * q + x * p) ≤ 0 := by
    nlinarith only [hleftWeighted, hrightWeighted, herror]
  have hpoly : s * q ^ 2 + (6 * x - 2 * s * x) * q + x * p ≤ 0 := by
    exact nonpos_of_mul_nonpos_right hscaled hQx0
  have heq : q - 2 * x + (x / s) * (p / q + 6) =
      (s * q ^ 2 + (6 * x - 2 * s * x) * q + x * p) / (s * q) := by
    field_simp [ne_of_gt hs0, ne_of_gt hq0]
    ring
  rw [heq]
  apply (div_le_iff₀ (mul_pos hs0 hq0)).mpr
  simpa only [zero_mul] using hpoly

/-- The explicit t-bound supplies the product parameter used by the interval estimate. -/
theorem coefficient_bound_of_t {s t x q : ℚ}
    (hs : 400 ≤ s) (ht : t ≤ 5 * s / 3)
    (hxl : 2 * s / 3 - 2 ≤ x) (hxu : x ≤ 2 * s / 3)
    (hxq : x < q) (hq : q ≤ 1 + 3 * s / 4) :
    q - 2 * x + (x / s) * (((1 + 3 * s / 8) * t) / q + 6) ≤ 0 := by
  apply coefficient_bound hs hxl hxu hxq hq
  have hfactor : 0 ≤ 1 + 3 * s / 8 := by linarith only [hs]
  have h := mul_le_mul_of_nonneg_left ht hfactor
  nlinarith only [h]

end Submissions.Erdos1020MatchingFKQuadratic.Main

namespace Submissions.Erdos1020MatchingNestedQuadratic.Main

open Finset

/-- Exact finite nested-family bound retaining the last-family count quadratically. -/
theorem quadratic_bound {s t : ℕ} (A : Fin (s + 1) → Finset (Fin t))
    (hnested : ∀ i j, i ≤ j → A j ⊆ A i)
    (hno : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A i)
    (hs : 0 < s) (x q : ℚ) (hx : 0 ≤ x) (hxs : x ≤ (s : ℚ))
    (ht : (s : ℚ) + x + 1 ≤ (t : ℚ)) :
    (∑ i, ((A i).card : ℚ)) + (q - 1) * (A (Fin.last s)).card - (s : ℚ) * t ≤
      (q - 2 * x) * (A (Fin.last s)).card +
        (x / s) * ((A (Fin.last s)).card : ℚ) ^ 2 := by
  classical
  obtain ⟨u, hzu, hus, hsum⟩ :=
    Submissions.Erdos1020MatchingFKFinite.Main.exists_suffix_bound A hnested hno
  have hu : (0 : ℚ) ≤ u := Nat.cast_nonneg u
  have hsumq : (∑ i, ((A i).card : ℚ)) ≤
      ((s : ℚ) - u) * t + ((u : ℚ) + 1) * u := by
    have h := (Nat.cast_le (α := ℚ)).mpr hsum
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hus,
      Nat.cast_one] using h
  have hmul := mul_le_mul_of_nonneg_left ht hu
  apply Submissions.Erdos1020MatchingFKQuadratic.Main.quadratic_of_suffix
    (u := (u : ℚ)) (Nat.cast_pos.mpr hs) hx hxs (Nat.cast_nonneg _)
    (Nat.cast_le.mpr hzu) (Nat.cast_le.mpr hus)
  nlinarith only [hsumq, hmul]

/-- The small-coefficient case already holds for each choice of blocks. -/
theorem bound_of_small_coefficient {s t : ℕ} (A : Fin (s + 1) → Finset (Fin t))
    (hnested : ∀ i j, i ≤ j → A j ⊆ A i)
    (hno : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A i)
    (hs : 0 < s) (x q : ℚ) (hx : 0 ≤ x) (hxs : x ≤ (s : ℚ))
    (ht : (s : ℚ) + x + 1 ≤ (t : ℚ)) (hqx : q ≤ x) :
    (∑ i, ((A i).card : ℚ)) + (q - 1) * (A (Fin.last s)).card ≤ (s : ℚ) * t := by
  obtain ⟨u, hzu, hus, _⟩ :=
    Submissions.Erdos1020MatchingFKFinite.Main.exists_suffix_bound A hnested hno
  exact Submissions.Erdos1020MatchingFKQuadratic.Main.pointwise_of_small_coefficient
    (Nat.cast_pos.mpr hs) hx (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (hzu.trans hus)) hqx
    (quadratic_bound A hnested hno hs x q hx hxs ht)

end Submissions.Erdos1020MatchingNestedQuadratic.Main

namespace Submissions.Erdos1020MatchingBinomialProduct.Main

open Finset

private theorem desc_factorial_product (n d : ℕ) :
    n.descFactorial d = ∏ j ∈ range d, (n - j) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.descFactorial_succ, prod_range_succ_comm, ih]

private theorem product_linear (n d : ℕ) :
    (∏ j ∈ range d, ((n : ℚ) - j)) =
      (d.factorial : ℚ) * (n.choose d : ℚ) := by
  rw [prod_range_natCast_sub, ← desc_factorial_product,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

/-- Exact binomial ratio as a product. The explicit room hypothesis makes all
the factor denominators positive, including at the extreme nonempty level. -/
theorem choose_ratio_product {m a ell : ℕ} (h : ell + a ≤ m) :
    ((m - a).choose ell : ℚ) / (m.choose ell : ℚ) =
      ∏ j ∈ range ell, (1 - (a : ℚ) / ((m : ℚ) - j)) := by
  have ha : a ≤ m := by omega
  have hC : (0 : ℚ) < m.choose ell := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hf : (ell.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ell.factorial_ne_zero
  calc
    _ = (∏ j ∈ range ell, (((m - a : ℕ) : ℚ) - j)) /
        (∏ j ∈ range ell, ((m : ℚ) - j)) := by
      rw [product_linear, product_linear]
      field_simp [hf, hC.ne']
    _ = _ := by
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro j hj
      have hjm : j < m := lt_of_lt_of_le (mem_range.mp hj) (by omega)
      have hden : (m : ℚ) - j ≠ 0 := ne_of_gt
        (sub_pos.mpr (Nat.cast_lt.mpr hjm))
      rw [Nat.cast_sub ha]
      field_simp [hden]; ring

/-- First-order finite product bound; no probability or independence premise. -/
theorem one_sub_sum_le_prod {ι : Type*} (S : Finset ι) (f : ι → ℚ)
    (hf0 : ∀ i ∈ S, 0 ≤ f i) (hf1 : ∀ i ∈ S, f i ≤ 1) :
    1 - (∑ i ∈ S, f i) ≤ ∏ i ∈ S, (1 - f i) := by
  classical
  revert hf0 hf1
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
    intro hf0 hf1
    have hi0 := hf0 i (mem_insert_self i S)
    have hi1 := hf1 i (mem_insert_self i S)
    have hS0 : ∀ j ∈ S, 0 ≤ f j := fun j hj => hf0 j (mem_insert_of_mem hj)
    have hS1 : ∀ j ∈ S, f j ≤ 1 := fun j hj => hf1 j (mem_insert_of_mem hj)
    have hs0 : 0 ≤ ∑ j ∈ S, f j := sum_nonneg hS0
    have hp := mul_nonneg hi0 hs0
    have hm := mul_le_mul_of_nonneg_left (ih hS0 hS1) (sub_nonneg.mpr hi1)
    rw [sum_insert hi, prod_insert hi]
    calc
      _ ≤ (1 - f i) * (1 - ∑ j ∈ S, f j) := by nlinarith only [hp]
      _ ≤ _ := hm

/-- Cubic Bonferroni bound, proved by the exact Pascal recurrence. -/
theorem cubic_lower (d : ℕ) (u : ℚ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - (d : ℚ) * u + (d.choose 2 : ℚ) * u ^ 2 -
      (d.choose 3 : ℚ) * u ^ 3 ≤ (1 - u) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hp : 0 ≤ (d.choose 3 : ℚ) * u ^ 4 :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu0 _)
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hu1)
    have heq :
        1 - ((d + 1 : ℕ) : ℚ) * u + ((d + 1).choose 2 : ℚ) * u ^ 2 -
            ((d + 1).choose 3 : ℚ) * u ^ 3 + (d.choose 3 : ℚ) * u ^ 4 =
          (1 - (d : ℚ) * u + (d.choose 2 : ℚ) * u ^ 2 -
            (d.choose 3 : ℚ) * u ^ 3) * (1 - u) := by
      rw [Nat.choose_succ_succ d 1, Nat.choose_succ_succ d 2]
      norm_num only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
      ring
    rw [pow_succ (1 - u) d]
    nlinarith only [hp, hm, heq]

private theorem choose_two_cast {d : ℕ} (hd : 1 ≤ d) :
    (d.choose 2 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) / 2 := by
  have h := congrArg (fun a : ℕ => (a : ℚ))
    (Nat.descFactorial_eq_factorial_mul_choose d 2)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.factorial_succ, Nat.cast_sub hd] at h
  nlinarith only [h]

private theorem choose_three_cast {d : ℕ} (hd : 2 ≤ d) :
    (d.choose 3 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 6 := by
  have hd1 : 1 ≤ d := by omega
  have h := congrArg (fun a : ℕ => (a : ℚ))
    (Nat.descFactorial_eq_factorial_mul_choose d 3)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.factorial_succ, Nat.cast_sub hd, Nat.cast_sub hd1] at h
  nlinarith only [h]

/-- A rational cubic certificate uniform in every positive rank, including one. -/
theorem power_density_bound {ell : ℕ} (hell : 1 ≤ ell) :
    (4 * (ell : ℚ) - 3) / (7 * (ell : ℚ)) ≤
      (1 - 11 / (20 * (ell : ℚ))) ^ ell := by
  by_cases he1 : ell = 1
  · subst ell
    norm_num
  have he2 : 2 ≤ ell := by omega
  have hL : (0 : ℚ) < ell := Nat.cast_pos.mpr (by omega)
  have hL1 : (1 : ℚ) ≤ ell := Nat.cast_le.mpr hell
  let u : ℚ := 11 / (20 * (ell : ℚ))
  have hu0 : 0 ≤ u := div_nonneg (by norm_num) (mul_nonneg (by norm_num) hL.le)
  have hu1 : u ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
    linarith only [hL1]
  have hp := cubic_lower ell u hu0 hu1
  rw [choose_two_cast hell, choose_three_cast he2] at hp
  have heq : 1 - (ell : ℚ) * u +
      ((ell : ℚ) * ((ell : ℚ) - 1) / 2) * u ^ 2 -
      ((ell : ℚ) * ((ell : ℚ) - 1) * ((ell : ℚ) - 2) / 6) * u ^ 3 =
      27529 / 48000 - 121 / (800 * (ell : ℚ)) +
        (11 / 20 : ℚ) ^ 3 * (3 * (ell : ℚ) - 2) / (6 * (ell : ℚ) ^ 2) := by
    dsimp only [u]
    field_simp [hL.ne']; ring
  rw [heq] at hp
  have hc : 0 ≤ (11 / 20 : ℚ) ^ 3 * (3 * (ell : ℚ) - 2) /
      (6 * (ell : ℚ) ^ 2) := by
    apply div_nonneg
    · apply mul_nonneg (by norm_num)
      linarith only [hL1]
    · exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hgap :
      (27529 / 48000 - 121 / (800 * (ell : ℚ))) -
        (4 * (ell : ℚ) - 3) / (7 * (ell : ℚ)) =
      703 / 336000 + 1553 / (5600 * (ell : ℚ)) := by
    field_simp [hL.ne']; ring
  have hg0 : 0 ≤ (703 / 336000 : ℚ) + 1553 / (5600 * (ell : ℚ)) :=
    add_nonneg (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hL.le))
  change (4 * (ell : ℚ) - 3) / (7 * (ell : ℚ)) ≤ (1 - u) ^ ell
  linarith only [hp, hc, hgap, hg0]

/-- The all-rank density comparison follows from an explicit finite-product
certificate. The hypotheses retain the ambient rounding loss of one vertex. -/
theorem density_bound {m s ell : ℕ} (hell : 1 ≤ ell) (hs : 66 ≤ s)
    (hcap : 11 * ell * s ≤ 6 * (m + 1)) :
    (4 * ell - 3) * m.choose ell ≤ 7 * ell * (m - s).choose ell := by
  have hls : 66 * ell ≤ ell * s := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left ell hs
  have hsl : s ≤ ell * s := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right s hell
  have hroom : ell + s ≤ m := by nlinarith only [hcap, hls, hsl, hell]
  have hL : (0 : ℚ) < ell := Nat.cast_pos.mpr (by omega)
  have hC : (0 : ℚ) < m.choose ell := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hcapQ : 11 * (ell : ℚ) * s ≤ 6 * ((m : ℚ) + 1) := by exact_mod_cast hcap
  have hlsQ : 66 * (ell : ℚ) ≤ (ell : ℚ) * s := by exact_mod_cast hls
  let rho : ℚ := 1 - 11 / (20 * (ell : ℚ))
  have hrho : 0 ≤ rho := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
    have hL1 : (1 : ℚ) ≤ ell := Nat.cast_le.mpr hell
    linarith only [hL1]
  have hfactor (j : ℕ) (hj : j ∈ range ell) :
      rho ≤ 1 - (s : ℚ) / ((m : ℚ) - j) := by
    have hjl : j + 1 ≤ ell := mem_range.mp hj
    have hjQ : (j : ℚ) + 1 ≤ ell := by exact_mod_cast hjl
    have hjm : j < m := by omega
    have hden : 0 < (m : ℚ) - j := sub_pos.mpr (Nat.cast_lt.mpr hjm)
    have hdiv : (s : ℚ) / ((m : ℚ) - j) ≤ 11 / (20 * (ell : ℚ)) := by
      apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hL)).mpr
      nlinarith only [hcapQ, hlsQ, hjQ]
    exact sub_le_sub_left hdiv 1
  have hprod : rho ^ ell ≤
      ∏ j ∈ range ell, (1 - (s : ℚ) / ((m : ℚ) - j)) := by
    calc
      _ = ∏ _j ∈ range ell, rho := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => hrho) hfactor
  have hratio : (4 * (ell : ℚ) - 3) / (7 * (ell : ℚ)) ≤
      ((m - s).choose ell : ℚ) / (m.choose ell : ℚ) := by
    rw [choose_ratio_product hroom]
    exact (power_density_bound hell).trans hprod
  have hscaled := (div_le_div_iff₀ (mul_pos (by norm_num) hL) hC).mp hratio
  apply (Nat.cast_le (α := ℚ)).mp
  have h3 : 3 ≤ 4 * ell := by omega
  norm_num only [Nat.cast_mul, Nat.cast_sub h3, Nat.cast_ofNat]
  nlinarith only [hscaled]

end Submissions.Erdos1020MatchingBinomialProduct.Main

namespace Submissions.Erdos1020MatchingBinomialVariance.Main

open Finset
open Submissions.Erdos1020MatchingBinomialProduct.Main

/-- A first-order product estimate controls the pair-incidence ratio in every rank. -/
theorem ratio_bound {m ℓ t : ℕ} (hℓ : 1 ≤ ℓ)
    (hm : 2 * ℓ * ℓ + 2 * ℓ ≤ m) (ht : ℓ * t ≤ m) :
    (t : ℚ) * ((m.choose ℓ : ℚ) / ((m - ℓ).choose ℓ : ℚ) - 1) ≤ 2 * ℓ := by
  classical
  have h2 : 2 * ℓ ≤ m := by nlinarith
  have hlm : ℓ ≤ m := by omega
  have hmq : (2 : ℚ) * ℓ * ℓ + 2 * ℓ ≤ m := by exact_mod_cast hm
  have hlq : (1 : ℚ) ≤ ℓ := by exact_mod_cast hℓ
  have htq : (ℓ : ℚ) * t ≤ m := by exact_mod_cast ht
  let C : ℚ := m.choose ℓ
  let D : ℚ := (m - ℓ).choose ℓ
  let d : ℚ := (m : ℚ) - ℓ + 1
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos hlm)
  have hD : 0 < D := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hDC : D ≤ C := Nat.cast_le.mpr (Nat.choose_le_choose ℓ (Nat.sub_le _ _))
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hhalf : (m : ℚ) ≤ 2 * (d - (ℓ : ℚ) ^ 2) := by dsimp [d]; nlinarith
  let f : ℕ → ℚ := fun j => (ℓ : ℚ) / ((m : ℚ) - j)
  have hfactor (j : ℕ) (hj : j ∈ range ℓ) : 0 ≤ f j ∧ f j ≤ 1 := by
    have hjn : j < ℓ := mem_range.mp hj
    have hjq : (j : ℚ) < ℓ := by exact_mod_cast hjn
    have hden : (0 : ℚ) < (m : ℚ) - j := by nlinarith
    refine ⟨div_nonneg (Nat.cast_nonneg _) hden.le, ?_⟩
    apply (div_le_one₀ hden).mpr
    nlinarith
  have hfactor_bound (j : ℕ) (hj : j ∈ range ℓ) : f j ≤ (ℓ : ℚ) / d := by
    have hjn : j + 1 ≤ ℓ := mem_range.mp hj
    have hjq : (j : ℚ) + 1 ≤ ℓ := by exact_mod_cast hjn
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd
    dsimp [d]
    linarith
  have hsum : (∑ j ∈ range ℓ, f j) ≤ (ℓ : ℚ) ^ 2 / d := by
    calc
      _ ≤ ∑ _j ∈ range ℓ, (ℓ : ℚ) / d := sum_le_sum hfactor_bound
      _ = _ := by simp [pow_two, mul_div_assoc]
  have hprod : 1 - (ℓ : ℚ) ^ 2 / d ≤ D / C := by
    have hu := one_sub_sum_le_prod (range ℓ) f
      (fun j hj => (hfactor j hj).1) (fun j hj => (hfactor j hj).2)
    have hp := choose_ratio_product (m := m) (a := ℓ) (ell := ℓ) (by omega)
    change D / C = ∏ j ∈ range ℓ, (1 - f j) at hp
    rw [hp]
    exact (sub_le_sub_left hsum 1).trans hu
  have hc : (1 - (ℓ : ℚ) ^ 2 / d) * C ≤ D := (le_div_iff₀ hC).mp hprod
  have hcleared : (d - (ℓ : ℚ) ^ 2) * (C - D) ≤ D * (ℓ : ℚ) ^ 2 := by
    have he := mul_le_mul_of_nonneg_right hc hd.le
    have hid : (1 - (ℓ : ℚ) ^ 2 / d) * C * d =
        (d - (ℓ : ℚ) ^ 2) * C := by field_simp [hd.ne']
    rw [hid] at he
    nlinarith only [he]
  have hnum : (m : ℚ) * (C - D) ≤ 2 * D * (ℓ : ℚ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hhalf (sub_nonneg.mpr hDC)
    nlinarith only [hh, hcleared]
  have ht_num : (ℓ : ℚ) * t * (C - D) ≤ 2 * D * (ℓ : ℚ) ^ 2 :=
    (mul_le_mul_of_nonneg_right htq (sub_nonneg.mpr hDC)).trans hnum
  have ht_cancel : (t : ℚ) * (C - D) ≤ 2 * D * ℓ := by
    apply le_of_mul_le_mul_of_pos_left ?_ (show (0 : ℚ) < ℓ by linarith)
    nlinarith only [ht_num]
  change (t : ℚ) * (C / D - 1) ≤ 2 * ℓ
  apply le_of_mul_le_mul_of_pos_right ?_ hD
  have hid : ((t : ℚ) * (C / D - 1)) * D = (t : ℚ) * (C - D) := by
    field_simp [hD.ne']
  rw [hid]
  nlinarith only [ht_cancel]

end Submissions.Erdos1020MatchingBinomialVariance.Main

namespace Submissions.Erdos1020MatchingFKAllRankQuadratic.Main

/-- Endpoint interpolation for the all-rank relative-variance coefficient.
Only an upper bound on p is required; its sign is not assumed. -/
theorem coefficient_bound {ell s x q p : ℚ}
    (hell : 1 ≤ ell) (hs : 1000 * ell ≤ s)
    (hxl : 5 * s / 6 - 3 ≤ x) (hxu : x ≤ 5 * s / 6)
    (hxq : x < q) (hq : q ≤ s + 1)
    (hp : p ≤ 11 * s ^ 2 / 14 + 11 * s / 6) :
    q - 2 * x + (x / s) * (p / q + 3 * ell) ≤ 0 := by
  have hs0 : 0 < s := by linarith only [hell, hs]
  have hell0 : 0 ≤ ell := by linarith only [hell]
  have hx0 : 0 < x := by linarith only [hell, hs, hxl]
  have hq0 : 0 < q := hx0.trans hxq
  let Q : ℚ := s + 1
  have hQ0 : 0 < Q := by dsimp only [Q]; linarith only [hs0]
  have hqQ : q ≤ Q := hq
  have hxQ : x < Q := hxq.trans_le hqQ
  have hleftc : -s / 21 + 29 / 6 + (5 / 2 : ℚ) * ell ≤ 0 := by
    linarith only [hell, hs]
  have hleftScaled := mul_nonpos_of_nonneg_of_nonpos hs0.le hleftc
  have hxlScaled := mul_le_mul_of_nonneg_left hxl hs0.le
  have hxuScaled := mul_le_mul_of_nonneg_left hxu
    (show 0 ≤ 3 * ell by linarith only [hell0])
  have hleftInner : p - s * x + 3 * ell * x ≤ 0 := by
    nlinarith only [hp, hleftScaled, hxlScaled, hxuScaled]
  have hleft : s * x ^ 2 + (3 * ell * x - 2 * s * x) * x + x * p ≤ 0 := by
    have h := mul_nonpos_of_nonneg_of_nonpos hx0.le hleftInner
    nlinarith only [h]
  have hquot : p / Q ≤ 11 * s / 14 + 11 / 6 := by
    apply (div_le_iff₀ hQ0).mpr
    dsimp only [Q]
    nlinarith only [hp, hs0.le]
  have hxs0 : 0 ≤ x / s := div_nonneg hx0.le hs0.le
  have hxs : x / s ≤ 5 / 6 := by
    apply (div_le_iff₀ hs0).mpr
    linarith only [hxu]
  have hupper0 : 0 ≤ 11 * s / 14 + 11 / 6 + 3 * ell := by
    linarith only [hs0.le, hell0]
  have hprod := mul_le_mul_of_nonneg_left (add_le_add hquot (le_refl (3 * ell))) hxs0
  have hprod' := mul_le_mul_of_nonneg_right hxs hupper0
  have hrightc : Q - 2 * x + (x / s) * (p / Q + 3 * ell) ≤ 0 := by
    have hbound : Q - 2 * x + (x / s) * (p / Q + 3 * ell) ≤
        -s / 84 + 307 / 36 + (5 / 2 : ℚ) * ell := by
      dsimp only [Q] at hprod ⊢
      linarith only [hprod, hprod', hxl]
    have hnonpos : -s / 84 + 307 / 36 + (5 / 2 : ℚ) * ell ≤ 0 := by
      linarith only [hell, hs]
    exact hbound.trans hnonpos
  have hid (v : ℚ) (hv : 0 < v) :
      v - 2 * x + (x / s) * (p / v + 3 * ell) =
        (s * v ^ 2 + (3 * ell * x - 2 * s * x) * v + x * p) / (s * v) := by
    field_simp [hs0.ne', hv.ne']
    ring
  have hright : s * Q ^ 2 + (3 * ell * x - 2 * s * x) * Q + x * p ≤ 0 := by
    rw [hid Q hQ0] at hrightc
    have h := (div_le_iff₀ (mul_pos hs0 hQ0)).mp hrightc
    simpa only [zero_mul] using h
  have hqx0 : 0 ≤ q - x := sub_nonneg.mpr hxq.le
  have hQq0 : 0 ≤ Q - q := sub_nonneg.mpr hqQ
  have hQx0 : 0 < Q - x := sub_pos.mpr hxQ
  have hleftWeighted := mul_le_mul_of_nonneg_left hleft hQq0
  have hrightWeighted := mul_le_mul_of_nonneg_left hright hqx0
  have herror : 0 ≤ s * (q - x) * (Q - q) * (Q - x) :=
    mul_nonneg (mul_nonneg (mul_nonneg hs0.le hqx0) hQq0) hQx0.le
  have hscaled : (Q - x) *
      (s * q ^ 2 + (3 * ell * x - 2 * s * x) * q + x * p) ≤ 0 := by
    nlinarith only [hleftWeighted, hrightWeighted, herror]
  have hpoly : s * q ^ 2 + (3 * ell * x - 2 * s * x) * q + x * p ≤ 0 :=
    nonpos_of_mul_nonpos_right hscaled hQx0
  rw [hid q hq0]
  apply (div_le_iff₀ (mul_pos hs0 hq0)).mpr
  simpa only [zero_mul] using hpoly

/-- The fixed-block upper bound supplies the required product parameter. -/
theorem coefficient_bound_of_t {ell s t x q : ℚ}
    (hell : 1 ≤ ell) (hs : 1000 * ell ≤ s) (ht : t ≤ 11 * s / 6)
    (hxl : 5 * s / 6 - 3 ≤ x) (hxu : x ≤ 5 * s / 6)
    (hxq : x < q) (hq : q ≤ s + 1) :
    q - 2 * x + (x / s) * (((1 + 3 * s / 7) * t) / q + 3 * ell) ≤ 0 := by
  apply coefficient_bound hell hs hxl hxu hxq hq
  have hs0 : 0 ≤ s := by linarith only [hell, hs]
  have hfactor : 0 ≤ 1 + 3 * s / 7 := by linarith only [hs0]
  have h := mul_le_mul_of_nonneg_left ht hfactor
  nlinarith only [h]

end Submissions.Erdos1020MatchingFKAllRankQuadratic.Main

namespace Submissions.Erdos1020MatchingFKAllRankAverage.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main

private theorem average_mono {Ω : Type*} [Fintype Ω] (f g : Ω → ℚ)
    (h : ∀ ω, f ω ≤ g ω) : average f ≤ average g := by
  classical
  exact div_le_div_of_nonneg_right (sum_le_sum (fun ω _ => h ω))
    (Nat.cast_nonneg (Fintype.card Ω))

private theorem average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    average (fun _ : Ω => c) = c := by
  classical
  have hN : (0 : ℚ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  unfold average
  apply (div_eq_iff hN.ne').mpr
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

private theorem average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℚ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  classical
  simp only [average, sum_add_distrib, add_div]

private theorem average_const_mul {Ω : Type*} [Fintype Ω] (c : ℚ) (f : Ω → ℚ) :
    average (fun ω => c * f ω) = c * average f := by
  classical
  simp only [average, ← mul_sum, mul_div_assoc]

/-- A rank-dependent relative variance bound controls the actual Hall quadratic average.
The count may have zero density; only the large-coefficient branch divides by q. -/
theorem average_le_of_moments {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {ell s t : ℕ} (E : Fin t → Finset Ω) (W : Ω → ℚ) (α x q : ℚ)
    (hell : 1 ≤ ell) (hs : 1000 * ell ≤ s) (ht : (t : ℚ) ≤ 11 * (s : ℚ) / 6)
    (hxl : 5 * (s : ℚ) / 6 - 3 ≤ x) (hxu : x ≤ 5 * (s : ℚ) / 6)
    (hα0 : 0 ≤ α) (hq : q ≤ (s : ℚ) + 1)
    (hqα : q * α ≤ 1 + 3 * (s : ℚ) / 7)
    (hzs : ∀ ω, eventCount E ω ≤ s)
    (hquad : ∀ ω, W ω - (s : ℚ) * t ≤
      (q - 2 * x) * (eventCount E ω : ℚ) +
        (x / s) * (eventCount E ω : ℚ) ^ 2)
    (hmean : average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ))
    (hvariance : average (fun ω => (eventCount E ω : ℚ) ^ 2) -
      (average (fun ω => (eventCount E ω : ℚ))) ^ 2 ≤
        3 * (ell : ℚ) * average (fun ω => (eventCount E ω : ℚ))) :
    average W ≤ (s : ℚ) * t := by
  classical
  have hellQ : (1 : ℚ) ≤ ell := Nat.cast_le.mpr hell
  have hsQ : 1000 * (ell : ℚ) ≤ s := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℚ)).mpr hs
  have hs0 : (0 : ℚ) < s := by linarith only [hellQ, hsQ]
  have hx0 : 0 < x := by linarith only [hellQ, hsQ, hxl]
  by_cases hqx : q ≤ x
  · calc
      average W ≤ average (fun _ : Ω => (s : ℚ) * t) := by
        apply average_mono
        intro ω
        exact Submissions.Erdos1020MatchingFKQuadratic.Main.pointwise_of_small_coefficient
          hs0 hx0.le (Nat.cast_nonneg _) (Nat.cast_le.mpr (hzs ω)) hqx (hquad ω)
      _ = _ := average_const _
  have hxq : x < q := lt_of_not_ge hqx
  have hq0 : 0 < q := hx0.trans hxq
  have hμ : 0 ≤ α * (t : ℚ) := mul_nonneg hα0 (Nat.cast_nonneg t)
  have hμbound : α * (t : ℚ) ≤ ((1 + 3 * (s : ℚ) / 7) * t) / q := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ = (q * α) * (t : ℚ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hqα (Nat.cast_nonneg t)
  have hxs0 : 0 ≤ x / (s : ℚ) := div_nonneg hx0.le hs0.le
  have hcoefficient : q - 2 * x + (x / s) * (α * (t : ℚ) + 3 * (ell : ℚ)) ≤ 0 := by
    calc
      _ ≤ q - 2 * x + (x / s) *
          (((1 + 3 * (s : ℚ) / 7) * t) / q + 3 * (ell : ℚ)) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (add_le_add hμbound le_rfl) hxs0)
      _ ≤ 0 := Submissions.Erdos1020MatchingFKAllRankQuadratic.Main.coefficient_bound_of_t
        hellQ hsQ ht hxl hxu hxq hq
  have hsecond : average (fun ω => (eventCount E ω : ℚ) ^ 2) ≤
      (α * (t : ℚ)) ^ 2 + 3 * (ell : ℚ) * (α * (t : ℚ)) := by
    rw [hmean] at hvariance
    linarith only [hvariance]
  have hpoint : ∀ ω, W ω ≤ (s : ℚ) * t +
      (q - 2 * x) * (eventCount E ω : ℚ) +
        (x / s) * (eventCount E ω : ℚ) ^ 2 := by
    intro ω
    linarith only [hquad ω]
  have havg := average_mono W _ hpoint
  rw [average_add, average_add, average_const, average_const_mul,
    average_const_mul, hmean] at havg
  calc
    average W ≤ (s : ℚ) * t + (q - 2 * x) * (α * (t : ℚ)) +
        (x / s) * average (fun ω => (eventCount E ω : ℚ) ^ 2) := havg
    _ ≤ (s : ℚ) * t + (q - 2 * x) * (α * (t : ℚ)) +
        (x / s) * ((α * (t : ℚ)) ^ 2 + 3 * (ell : ℚ) * (α * (t : ℚ))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond hxs0)
    _ = (s : ℚ) * t + (α * (t : ℚ)) *
        (q - 2 * x + (x / s) * (α * (t : ℚ) + 3 * (ell : ℚ))) := by ring
    _ ≤ (s : ℚ) * t := by
      have h := mul_nonpos_of_nonneg_of_nonpos hμ hcoefficient
      linarith only [h]

/-- The exact moment outputs and samplewise nested families give the weighted
average bound. The event normalization and pointwise Hall premises remain explicit. -/
theorem average_nested_of_moments {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {ell s t : ℕ} (E : Fin t → Finset Ω)
    (A : Ω → Fin (s + 1) → Finset (Fin t)) (α x q : ℚ)
    (hnested : ∀ ω i j, i ≤ j → A ω j ⊆ A ω i)
    (hno : ∀ ω, ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A ω i)
    (hcount : ∀ ω, (A ω (Fin.last s)).card = eventCount E ω)
    (hell : 1 ≤ ell) (hs : 1000 * ell ≤ s) (ht : (t : ℚ) ≤ 11 * (s : ℚ) / 6)
    (hxl : 5 * (s : ℚ) / 6 - 3 ≤ x) (hxu : x ≤ 5 * (s : ℚ) / 6)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (hα0 : 0 ≤ α)
    (hq : q ≤ (s : ℚ) + 1)
    (hqα : q * α ≤ 1 + 3 * (s : ℚ) / 7)
    (hmean : average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ))
    (hvariance : average (fun ω => (eventCount E ω : ℚ) ^ 2) -
      (average (fun ω => (eventCount E ω : ℚ))) ^ 2 ≤
        3 * (ell : ℚ) * average (fun ω => (eventCount E ω : ℚ))) :
    average (fun ω => (∑ i, ((A ω i).card : ℚ)) +
      (q - 1) * (A ω (Fin.last s)).card) ≤ (s : ℚ) * t := by
  classical
  have hellQ : (1 : ℚ) ≤ ell := Nat.cast_le.mpr hell
  have hsQ : 1000 * (ell : ℚ) ≤ s := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℚ)).mpr hs
  have hspos : 0 < s := (Nat.cast_pos (α := ℚ)).mp (by linarith only [hellQ, hsQ])
  have hx0 : 0 ≤ x := by linarith only [hellQ, hsQ, hxl]
  have hxs : x ≤ (s : ℚ) := by linarith only [hellQ, hsQ, hxu]
  apply average_le_of_moments E _ α x q hell hs ht hxl hxu hα0 hq hqα
    ?_ ?_ hmean hvariance
  · intro ω
    obtain ⟨u, hzu, hus, _⟩ :=
      Submissions.Erdos1020MatchingFKFinite.Main.exists_suffix_bound
        (A ω) (hnested ω) (hno ω)
    rw [← hcount ω]
    exact hzu.trans hus
  · intro ω
    have h := Submissions.Erdos1020MatchingNestedQuadratic.Main.quadratic_bound
      (A ω) (hnested ω) (hno ω) hspos x q hx0 hxs hcapacity
    simpa only [hcount ω] using h

end Submissions.Erdos1020MatchingFKAllRankAverage.Main

namespace Submissions.Erdos1020MatchingGenericTailShadow.Main

open Finset

/-- Reindex an actual family avoiding a finite head, preserving its cardinality,
uniformity and literal matching restriction. -/
theorem reindex_tail {α : Type*} [Fintype α] [DecidableEq α] {m r k : ℕ}
    (F : Finset (Finset α)) (T : Finset α)
    (hc : Fintype.card {x : α // x ∉ T} = m)
    (havoid : ∀ e ∈ F, ∀ x ∈ e, x ∉ T)
    (hF : ∀ e ∈ F, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset α), M ⊆ F ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Finset (Fin m)), G.card = F.card ∧
      (∀ e ∈ G, e.card = r) ∧
      ¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  let c : {x : α // x ∉ T} ≃ Fin m := Fintype.equivFinOfCardEq hc
  let E : Fin m ↪ α := c.symm.toEmbedding.trans (Function.Embedding.subtype (· ∉ T))
  let E' := (Finset.mapEmbedding E).toEmbedding
  let shrink (e : Finset α) := (e.subtype (· ∉ T)).map c.toEmbedding
  have hcomp : c.toEmbedding.trans E = Function.Embedding.subtype (· ∉ T) := by
    apply Function.Embedding.ext
    intro x
    exact congrArg Subtype.val (c.symm_apply_apply x)
  have hmap (e) (he : e ∈ F) : (shrink e).map E = e := by
    change ((e.subtype (· ∉ T)).map c.toEmbedding).map E = e
    rw [Finset.map_map, hcomp]
    exact Finset.subtype_map_of_mem (havoid e he)
  let G := F.image shrink
  have hmem (e) (he : e ∈ G) : e.map E ∈ F := by
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    rwa [hmap f hf]
  refine ⟨G, ?_, ?_, ?_⟩
  · apply card_image_of_injOn
    intro e he f hf hef
    exact (hmap e he).symm.trans ((congrArg (fun a => a.map E) hef).trans (hmap f hf))
  · intro e he
    simpa only [card_map] using hF _ (hmem e he)
  · rintro ⟨M, hMG, hMc, hMd⟩
    apply hM
    refine ⟨M.map E', ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨e, he, rfl⟩ := mem_map.mp ha
      exact hmem e (hMG he)
    · simpa only [card_map] using hMc
    · intro a ha b hb hab
      obtain ⟨e, he, rfl⟩ := mem_map.mp ha
      obtain ⟨f, hf, rfl⟩ := mem_map.mp hb
      exact (disjoint_map E).mpr (hMd e he f hf (fun h => hab (congrArg E' h)))

/-- Apply a supplied lower-rank cover theorem to the actual zero-head shadow.
The lower-rank theorem is an explicit helper premise, to be discharged by rank induction. -/
theorem shadow_bound_of_lower_rank {n r s : ℕ}
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n)) (hT : T.card = s + 1)
    (hlower : ∀ v ∈ T, ∀ x ∉ T, v < x)
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hlowerRank : ∀ G : Finset (Finset (Fin (n - (s + 1)))),
      (∀ e ∈ G, e.card = r - 1) →
      (¬ ∃ M : Finset (Finset (Fin (n - (s + 1)))), M ⊆ G ∧ M.card = s + 1 ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
      G.card ≤ (n - (s + 1)).choose (r - 1) -
        (n - (s + 1) - s).choose (r - 1)) :
    (H.filter (fun e => e ∩ T = ∅)).shadow.card ≤
      (n - (s + 1)).choose (r - 1) - (n - (s + 1) - s).choose (r - 1) := by
  classical
  let Z := H.filter (fun e => e ∩ T = ∅)
  have hZu : ∀ e ∈ Z, e.card = r := fun _ he => hH _ (mem_filter.mp he).1
  have hSu : ∀ e ∈ Z.shadow, e.card = r - 1 := Set.Sized.shadow hZu
  have hSm := Submissions.Erdos1020MatchingZeroShadow.Main.shadow_zero_matchingFree
    H T hT hlower hstable hM
  have havoid : ∀ e ∈ Z.shadow, ∀ x ∈ e, x ∉ T := by
    intro e he x hx hxT
    obtain ⟨f, hf, hef⟩ := exists_subset_of_mem_shadow he
    have hmeet : x ∈ f ∩ T := mem_inter.mpr ⟨hef hx, hxT⟩
    rw [(mem_filter.mp hf).2] at hmeet
    exact notMem_empty x hmeet
  have htail : Fintype.card {x : Fin n // x ∉ T} = n - (s + 1) := by
    simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
      Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
  obtain ⟨G, hGc, hGu, hGm⟩ := reindex_tail Z.shadow T htail havoid hSu hSm
  have hbound := hlowerRank G hGu hGm
  rwa [hGc] at hbound

end Submissions.Erdos1020MatchingGenericTailShadow.Main

namespace Submissions.Erdos1020MatchingFKAllRankParameters.Main

/-- The tail of a head of size s+1 retains the proposed lower-rank ambient guard. -/
theorem induction_parameters {r s n : ℕ}
    (hr : 4 ≤ r) (hs : 1000 * r ≤ s)
    (hn : 6 * s + 11 * (r - 1) * s ≤ 6 * n) :
    3 ≤ r - 1 ∧ 1000 * (r - 1) ≤ s ∧
      6 * s + 11 * ((r - 1) - 1) * s ≤ 6 * (n - s - 1) := by
  have hr1 : 3 ≤ r - 1 := by omega
  have hs0 : 4000 ≤ s := by omega
  have hmul := Nat.mul_le_mul_right s hr1
  have hhead : s + 1 ≤ n := by nlinarith only [hn, hmul, hs0]
  have htail : n - s - 1 + s + 1 = n := by omega
  have hrid : (r - 1) - 1 + 1 = r - 1 := by omega
  have hprod := congrArg (fun a : ℕ => a * s) hrid
  refine ⟨hr1, by omega, ?_⟩
  nlinarith only [hn, htail, hprod, hs0]

/-- A fixed block count works in every larger ambient set. Natural subtraction
and the lost floor remainder are kept explicit before passing to rational bounds. -/
theorem block_parameters {r s n : ℕ}
    (hr : 3 ≤ r) (hs : 1000 * r ≤ s)
    (hn : 6 * s + 11 * (r - 1) * s ≤ 6 * n) :
    let t := 11 * s / 6 - 1
    let m := n - s - 1
    let x : ℚ := (t : ℚ) - (s : ℚ) - 1
    s + 1 ≤ n ∧ 0 < t ∧ (r - 1) * t ≤ m ∧
      11 * (r - 1) * s ≤ 6 * (m + 1) ∧
      2 * (r - 1) ^ 2 + 2 * (r - 1) ≤ m ∧
      11 * (s : ℚ) / 6 - 2 ≤ (t : ℚ) ∧
      (t : ℚ) ≤ 11 * (s : ℚ) / 6 - 1 ∧
      5 * (s : ℚ) / 6 - 3 ≤ x ∧ x ≤ 5 * (s : ℚ) / 6 ∧
      0 ≤ x ∧ x ≤ (s : ℚ) ∧ (t : ℚ) = (s : ℚ) + x + 1 := by
  dsimp only
  have hr1 : 2 ≤ r - 1 := by omega
  have hs0 : 3000 ≤ s := by omega
  have hmul := Nat.mul_le_mul_right s hr1
  have hhead : s + 1 ≤ n := by nlinarith only [hn, hmul, hs0]
  have hm : n - s - 1 + s + 1 = n := by omega
  have htail : 11 * (r - 1) * s ≤ 6 * (n - s - 1 + 1) := by
    nlinarith only [hn, hm]
  have hfloorL : 11 * s ≤ 6 * (11 * s / 6 - 1) + 12 := by omega
  have hfloorU : 6 * (11 * s / 6 - 1 + 1) ≤ 11 * s := by omega
  have hfloorScaled := Nat.mul_le_mul_left (r - 1) hfloorU
  have hblocks : (r - 1) * (11 * s / 6 - 1) ≤ n - s - 1 := by
    nlinarith only [hfloorScaled, htail, hr1]
  have hs3 : 3 * (r - 1) ≤ s := by omega
  have hsScaled := Nat.mul_le_mul_left (r - 1) hs3
  have hsq := Nat.mul_le_mul_left (r - 1) hr1
  have hmoment : 2 * (r - 1) ^ 2 + 2 * (r - 1) ≤ n - s - 1 := by
    nlinarith only [hsScaled, hsq, htail, hr1]
  have hsQ : (3000 : ℚ) ≤ s := (Nat.cast_le (α := ℚ)).mpr hs0
  have hfloorLQ := (Nat.cast_le (α := ℚ)).mpr hfloorL
  have hfloorUQ := (Nat.cast_le (α := ℚ)).mpr hfloorU
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfloorLQ hfloorUQ
  refine ⟨hhead, by omega, hblocks, htail, hmoment, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith only [hsQ, hfloorLQ, hfloorUQ]

/-- Rank three starts the proposed rank induction using the checked Refined theorem. -/
theorem rank_three_base {n s : ℕ} (hs : 13 ≤ s)
    (hn : 6 * s + 11 * (3 - 1) * s ≤ 6 * n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = 3)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose 3 - (n - s).choose 3 := by
  let u := 5 * (s + 1) / 3
  have hw : 3 * (s + 1) + (3 - 1) * s ≤ 3 * u := by dsimp only [u]; omega
  have hu : 3 * u ≤ 5 * (s + 1) := by dsimp only [u]; omega
  have hc : (3 - 1) * u + s + 1 ≤ n := by nlinarith only [hn, hu, hs]
  exact Submissions.Erdos1020MatchingRefined.Main.star_bound (by decide) hw hc H hH hM

end Submissions.Erdos1020MatchingFKAllRankParameters.Main

namespace Submissions.Erdos1020MatchingFKAllRankFamily.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main
open Submissions.Erdos1020MatchingPermutationMoments.Main

/-- The moment and Hall estimates imply the weighted inequality for the actual
nested uniform families. All relabelings of the supplied blocks are averaged. -/
theorem weighted_bound {α : Type*} [Fintype α] [DecidableEq α] {ell s t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = ell)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ell)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hell : 1 ≤ ell) (hs : 1000 * ell ≤ s)
    (hm : 2 * ell * ell + 2 * ell ≤ Fintype.card α)
    (htpos : 0 < t) (hblocks : ell * t ≤ Fintype.card α)
    (x q : ℚ) (ht : (t : ℚ) ≤ 11 * (s : ℚ) / 6)
    (hxl : 5 * (s : ℚ) / 6 - 3 ≤ x) (hxu : x ≤ 5 * (s : ℚ) / 6)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (hq : q ≤ (s : ℚ) + 1)
    (hqα : q * ((F (Fin.last s)).card : ℚ) /
      ((Fintype.card α).choose ell : ℚ) ≤ 1 + 3 * (s : ℚ) / 7) :
    (∑ i, ((F i).card : ℚ)) + (q - 1) * ((F (Fin.last s)).card : ℚ) ≤
      (s : ℚ) * ((Fintype.card α).choose ell : ℚ) := by
  classical
  let C : ℚ := (Fintype.card α).choose ell
  let a : ℚ := ((F (Fin.last s)).card : ℚ) / C
  let A (σ : Equiv.Perm α) (i : Fin (s + 1)) : Finset (Fin t) :=
    univ.filter (fun j => (P j).map σ.toEmbedding ∈ F i)
  have hAnested (σ : Equiv.Perm α) : ∀ i j, i ≤ j → A σ j ⊆ A σ i := by
    intro i j hij b hb
    exact mem_filter.mpr ⟨mem_univ _, hnested i j hij (mem_filter.mp hb).2⟩
  have hAno (σ : Equiv.Perm α) : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A σ i := by
    rintro ⟨f, hfinj, hf⟩
    apply hno
    refine ⟨fun i => (P (f i)).map σ.toEmbedding, ?_, ?_⟩
    · intro i
      exact (mem_filter.mp (hf i)).2
    · intro i j hij
      exact (disjoint_map σ.toEmbedding).mpr (hPd (hfinj.ne hij))
  have hcount (σ : Equiv.Perm α) (i : Fin (s + 1)) :
      (A σ i).card = eventCount (blockEvents P (F i)) σ := by
    simp only [A, eventCount, blockEvents, mem_filter, mem_univ, true_and]
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hC.le
  have hqa : q * a ≤ 1 + 3 * (s : ℚ) / 7 := by
    simpa only [a, C, mul_div_assoc] using hqα
  have hratio := Submissions.Erdos1020MatchingBinomialVariance.Main.ratio_bound hell hm hblocks
  obtain ⟨hmean, hvariance⟩ :=
    Submissions.Erdos1020MatchingPermutationVariance.Main.block_moments
      P hP hPd (F (Fin.last s)) (hF (Fin.last s)) (by omega) (2 * (ell : ℚ)) hratio
  have hmean0 : 0 ≤ average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ)) := by
    rw [hmean]
    exact mul_nonneg ha0 (Nat.cast_nonneg _)
  have hvariance' : average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ) ^ 2) -
      (average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ))) ^ 2 ≤
      3 * (ell : ℚ) * average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ)) := by
    apply hvariance.trans
    apply mul_le_mul_of_nonneg_right _ hmean0
    have he : (1 : ℚ) ≤ ell := Nat.cast_le.mpr hell
    linarith only [he]
  have havg := Submissions.Erdos1020MatchingFKAllRankAverage.Main.average_nested_of_moments
    (blockEvents P (F (Fin.last s))) A a x q hAnested hAno
    (fun σ => hcount σ (Fin.last s)) hell hs ht hxl hxu hcapacity ha0 hq hqa hmean hvariance'
  have hfamily (i : Fin (s + 1)) : average (fun σ => ((A σ i).card : ℚ)) =
      ((F i).card : ℚ) / C * (t : ℚ) := by
    simpa only [hcount] using block_mean P hP (F i) (hF i)
  have hlinear : average (fun σ => (∑ i, ((A σ i).card : ℚ)) +
      (q - 1) * (A σ (Fin.last s)).card) =
      ((∑ i, ((F i).card : ℚ)) + (q - 1) * ((F (Fin.last s)).card : ℚ)) /
        C * (t : ℚ) := by
    calc
      _ = (∑ i, average (fun σ => ((A σ i).card : ℚ))) +
          (q - 1) * average (fun σ => ((A σ (Fin.last s)).card : ℚ)) := by
        unfold average
        rw [sum_add_distrib, sum_comm, ← mul_sum, add_div, mul_div_assoc]
        simp only [div_eq_mul_inv, sum_mul]
      _ = (∑ i, ((F i).card : ℚ) / C * (t : ℚ)) +
          (q - 1) * (((F (Fin.last s)).card : ℚ) / C * (t : ℚ)) := by
        simp_rw [hfamily]
      _ = _ := by
        simp only [div_eq_mul_inv, ← sum_mul]
        ring1
  rw [hlinear] at havg
  have htQ : (0 : ℚ) < t := Nat.cast_pos.mpr htpos
  have hdiv := le_of_mul_le_mul_of_pos_right havg htQ
  exact (div_le_iff₀ hC).mp hdiv

/-- The two actual zero-head estimates can be absorbed into the singleton
families. The empty last-family case is discharged before dividing by its size. -/
theorem slices_le {α : Type*} [Fintype α] [DecidableEq α] {ell s t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = ell)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ell)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hell : 1 ≤ ell) (hs : 1000 * ell ≤ s)
    (hm : 2 * ell * ell + 2 * ell ≤ Fintype.card α)
    (htpos : 0 < t) (hblocks : ell * t ≤ Fintype.card α)
    (x : ℚ) (ht : (t : ℚ) ≤ 11 * (s : ℚ) / 6)
    (hxl : 5 * (s : ℚ) / 6 - 3 ≤ x) (hxu : x ≤ 5 * (s : ℚ) / 6)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (Z : ℕ) (hZa : Z ≤ s * (F (Fin.last s)).card)
    (hZC : 7 * Z ≤ 3 * s * (Fintype.card α).choose ell) :
    Z + (∑ i, (F i).card) ≤ s * (Fintype.card α).choose ell := by
  classical
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  by_cases ha0 : (F (Fin.last s)).card = 0
  · have hZ0 : Z = 0 := by rw [ha0] at hZa; omega
    have hq : (1 : ℚ) ≤ (s : ℚ) + 1 := by linarith only [hs0]
    have hqa : (1 : ℚ) * ((F (Fin.last s)).card : ℚ) /
        ((Fintype.card α).choose ell : ℚ) ≤ 1 + 3 * (s : ℚ) / 7 := by
      rw [ha0]
      simp only [Nat.cast_zero, mul_zero, zero_div]
      linarith only [hs0]
    have h := weighted_bound P hP hPd F hF hnested hno hell hs hm htpos hblocks
      x 1 ht hxl hxu hcapacity hq hqa
    simp only [sub_self, zero_mul, add_zero] at h
    rw [hZ0, zero_add]
    exact_mod_cast h
  · have ha : 0 < (F (Fin.last s)).card := Nat.pos_of_ne_zero ha0
    have haC : (F (Fin.last s)).card ≤ (Fintype.card α).choose ell := by
      calc
        _ ≤ (univ.powersetCard ell : Finset (Finset α)).card :=
          card_le_card (fun e he => mem_powersetCard_univ.mpr (hF _ e he))
        _ = _ := by simp
    have haQpos : (0 : ℚ) < (F (Fin.last s)).card := Nat.cast_pos.mpr ha
    have hCpos : (0 : ℚ) < (Fintype.card α).choose ell :=
      Nat.cast_pos.mpr (lt_of_lt_of_le ha haC)
    have hZaQ : (Z : ℚ) ≤ (s : ℚ) * (F (Fin.last s)).card := by exact_mod_cast hZa
    have hZCQ : (7 : ℚ) * Z ≤ 3 * s * ((Fintype.card α).choose ell : ℚ) := by
      exact_mod_cast hZC
    have hq : 1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ) ≤ (s : ℚ) + 1 := by
      have hd := (div_le_iff₀ haQpos).mpr hZaQ
      linarith only [hd]
    have hα : ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) ≤ 1 :=
      (div_le_one₀ hCpos).mpr (Nat.cast_le.mpr haC)
    have hZdiv : (Z : ℚ) / ((Fintype.card α).choose ell : ℚ) ≤ 3 * (s : ℚ) / 7 := by
      apply (div_le_iff₀ hCpos).mpr
      nlinarith only [hZCQ]
    have hqa' : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) *
        ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) ≤
        1 + 3 * (s : ℚ) / 7 := by
      have hid : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) *
          ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) =
          ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) +
          (Z : ℚ) / ((Fintype.card α).choose ell : ℚ) := by
        field_simp [haQpos.ne', hCpos.ne']
      rw [hid]
      exact add_le_add hα hZdiv
    have h := weighted_bound P hP hPd F hF hnested hno hell hs hm htpos hblocks
      x (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) ht hxl hxu hcapacity hq hqa'
    have haQ : ((F (Fin.last s)).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
    have heq : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ) - 1) *
        ((F (Fin.last s)).card : ℚ) = (Z : ℚ) := by
      rw [add_sub_cancel_left, div_mul_cancel₀ _ haQ]
    rw [heq] at h
    have hnat : (∑ i, (F i).card) + Z ≤ s * (Fintype.card α).choose ell := by
      exact_mod_cast h
    simpa only [Nat.add_comm] using hnat

end Submissions.Erdos1020MatchingFKAllRankFamily.Main

namespace Submissions.Erdos1020MatchingFKAllRank.Main

open Finset
open Submissions.Erdos1020MatchingHeadLinks.Main

/-- A finite all-rank range from the nested-slice and permutation-moment argument. -/
theorem star_bound {r n s : ℕ} (hr : 3 ≤ r) (hs : 1000 * r ≤ s)
    (hn : 6 * s + 11 * (r - 1) * s ≤ 6 * n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose r - (n - s).choose r := by
  classical
  induction r using Nat.strong_induction_on generalizing n s with
  | h r ih =>
    by_cases hr3 : r = 3
    · subst r
      exact Submissions.Erdos1020MatchingFKAllRankParameters.Main.rank_three_base
        (by omega) hn H hH hM
    have hr4 : 4 ≤ r := by omega
    have hrpos : 0 < r := by omega
    have hell : 1 ≤ r - 1 := by omega
    obtain ⟨hrprev, hsprev, hnprev⟩ :=
      Submissions.Erdos1020MatchingFKAllRankParameters.Main.induction_parameters hr4 hs hn
    have hlowerRank : ∀ K : Finset (Finset (Fin (n - (s + 1)))),
        (∀ e ∈ K, e.card = r - 1) →
        (¬ ∃ M : Finset (Finset (Fin (n - (s + 1)))), M ⊆ K ∧ M.card = s + 1 ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        K.card ≤ (n - (s + 1)).choose (r - 1) -
          (n - (s + 1) - s).choose (r - 1) := by
      intro K hK hKM
      apply ih (r - 1) (by omega) hrprev hsprev
      · simpa only [Nat.sub_add_eq] using hnprev
      · exact hK
      · exact hKM
    obtain ⟨G, hGc, hGu, hGm, hGs⟩ :=
      Submissions.Erdos1020ShiftNormalize.Main.exists_shifted H hH hM
    obtain ⟨hhead, htpos, hblocks, htail, hmoment, _, htu, hxl, hxu, _, _, htident⟩ :=
      Submissions.Erdos1020MatchingFKAllRankParameters.Main.block_parameters hr hs hn
    let J : Fin (s + 1) ↪ Fin n :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hhead⟩,
        fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
    let T : Finset (Fin n) := univ.map J
    have hT : T.card = s + 1 := by simp [T]
    have hJ (i : Fin (s + 1)) : J i ∈ T := mem_map.mpr ⟨i, mem_univ i, rfl⟩
    have hmono : StrictMono J := fun _ _ h => h
    have hcut (x : Fin n) : x ∈ T ↔ x.val < s + 1 := by
      constructor
      · intro hx
        obtain ⟨i, _, rfl⟩ := mem_map.mp hx
        exact i.isLt
      · intro hx
        exact mem_map.mpr ⟨⟨x.val, hx⟩, mem_univ _, Fin.ext rfl⟩
    have hlower : ∀ v ∈ T, ∀ x ∉ T, v < x := by
      intro v hv x hx
      have hv' := (hcut v).mp hv
      have hx' := (hcut x).not.mp hx
      change v.val < x.val
      omega
    let F := fun i : Fin (s + 1) => tailFamily G T (J i) r
    have hAc : Fintype.card {x : Fin n // x ∉ T} = n - (s + 1) := by
      simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
        Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
    have hAc' : Fintype.card {x : Fin n // x ∉ T} = n - s - 1 := by omega
    let t := 11 * s / 6 - 1
    let x : ℚ := (t : ℚ) - (s : ℚ) - 1
    rw [← hAc'] at hblocks hmoment
    obtain ⟨P, hP, hPd⟩ := Submissions.Erdos1020UniformBlocks.Main.exists_blocks
      (α := {x : Fin n // x ∉ T}) t (r - 1)
      (by simpa only [t, Nat.mul_comm] using hblocks)
    let Z := G.filter (fun e => e ∩ T = ∅)
    have hzero := Submissions.Erdos1020MatchingZeroShadow.Main.scaled_zero_head_le
      G T (J (Fin.last s)) (by omega : 2 ≤ r) hT (hJ _) hlower hGu hGm hGs
    have hZa : Z.card ≤ s * (F (Fin.last s)).card := by
      have hh : r * Z.card ≤ r * (s * (F (Fin.last s)).card) := by
        calc
          _ ≤ (r - 1) * s * (F (Fin.last s)).card := hzero
          _ ≤ r * (s * (F (Fin.last s)).card) := by
            simpa only [Nat.mul_assoc] using
              Nat.mul_le_mul_right (s * (F (Fin.last s)).card) (Nat.sub_le r 1)
      exact le_of_mul_le_mul_of_pos_left hh hrpos
    have hshadow := Submissions.Erdos1020MatchingGenericTailShadow.Main.shadow_bound_of_lower_rank
      G T hT hlower hGu hGm hGs hlowerRank
    let m := n - (s + 1)
    have htail' : 11 * (r - 1) * s ≤ 6 * (m + 1) := by
      simpa only [m, Nat.sub_add_eq] using htail
    have hdensity := Submissions.Erdos1020MatchingBinomialProduct.Main.density_bound
      hell (by omega : 66 ≤ s) htail'
    have hBC : (m - s).choose (r - 1) ≤ m.choose (r - 1) :=
      Nat.choose_le_choose _ (Nat.sub_le _ _)
    have hsub : m.choose (r - 1) - (m - s).choose (r - 1) +
        (m - s).choose (r - 1) = m.choose (r - 1) := Nat.sub_add_cancel hBC
    have hshadowSum : Z.shadow.card + (m - s).choose (r - 1) ≤ m.choose (r - 1) := by
      exact (Nat.add_le_add_right hshadow _).trans_eq hsub
    have hscaled := Nat.mul_le_mul_left (7 * (r - 1)) hshadowSum
    have hellid : 4 * (r - 1) - 3 + 3 = 4 * (r - 1) := by omega
    have hrid : r - 1 + 1 = r := by omega
    have hshadowDensity : 7 * (r - 1) * Z.shadow.card ≤ 3 * r * m.choose (r - 1) := by
      have hid1 := congrArg (fun a : ℕ => a * m.choose (r - 1)) hellid
      have hid2 := congrArg (fun a : ℕ => 3 * a * m.choose (r - 1)) hrid
      nlinarith only [hdensity, hscaled, hid1, hid2]
    have hZm := Submissions.Erdos1020MatchingZeroShadow.Main.shadow_zero_matchingFree
      G T hT hlower hGs hGm
    have hrestricted := Submissions.Erdos1020MatchingRestrictedShadow.Main.shadow_bound
      s r (by omega) Z (fun e he => hGu e (mem_filter.mp he).1) hZm
    have hZC : 7 * Z.card ≤ 3 * s * (Fintype.card {x : Fin n // x ∉ T}).choose (r - 1) := by
      rw [hAc]
      have hh : r * (7 * Z.card) ≤ r * (3 * s * m.choose (r - 1)) := by
        calc
          _ = 7 * (r * Z.card) := by ring1
          _ ≤ 7 * ((r - 1) * s * Z.shadow.card) := Nat.mul_le_mul_left 7 hrestricted
          _ = s * (7 * (r - 1) * Z.shadow.card) := by ring1
          _ ≤ s * (3 * r * m.choose (r - 1)) := Nat.mul_le_mul_left s hshadowDensity
          _ = _ := by ring1
      exact le_of_mul_le_mul_of_pos_left hh hrpos
    have hweighted := Submissions.Erdos1020MatchingFKAllRankFamily.Main.slices_le
      P hP hPd F (fun i => tailFamily_uniform G T (J i) r)
      (tailFamily_nested G T r J hJ hmono hGs) (no_rainbow G T r J hJ hGm)
      hell hsprev (by simpa only [pow_two, Nat.mul_assoc] using hmoment) htpos hblocks x
      (by linarith only [htu]) hxl hxu htident.symm.le Z.card hZa hZC
    rw [hAc] at hweighted
    have hsingle : (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
        ∑ i, (F i).card := by
      change (∑ v ∈ univ.map J, (G.filter (fun e => e ∩ T = {v})).card) ≤ _
      rw [sum_map]
      apply sum_le_sum
      intro i _
      exact singleton_head_le G T (J i) r (hJ i) hGu
    have hslices : (G.filter (fun e => e ∩ T = ∅)).card +
        (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
          s * (n - (s + 1)).choose (r - 1) := by
      exact (Nat.add_le_add_left hsingle _).trans hweighted
    rw [← hGc]
    exact Submissions.Erdos1020MatchingHeadComparison.Main.star_bound_of_slices
      G T (by omega) hT hGu hhead hslices
end Submissions.Erdos1020MatchingFKAllRank.Main

namespace Submissions.Erdos1020MatchingFKAllRankProof.Main

/-- The original maximum follows from the stronger all-rank star bound. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → 1000 * r ≤ k - 1 →
      6 * (k - 1) + 11 * (r - 1) * (k - 1) ≤ 6 * n →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hs hn H hH hM
  have hkpred : (k - 1) + 1 = k := by omega
  have hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = (k - 1) + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    simpa only [hkpred] using hM
  have hb := Submissions.Erdos1020MatchingFKAllRank.Main.star_bound hr hs hn H hH hfree
  have hhead := (Submissions.Erdos1020MatchingFKAllRankParameters.Main.block_parameters hr hs hn).1
  have hsub : n - (k - 1) = n - k + 1 := by omega
  rw [hsub] at hb
  exact hb.trans (le_max_right _ _)

end Submissions.Erdos1020MatchingFKAllRankProof.Main

namespace Submissions.Erdos1020MatchingFKTailAverage.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main

private theorem average_mono {Ω : Type*} [Fintype Ω] (f g : Ω → ℚ)
    (h : ∀ ω, f ω ≤ g ω) : average f ≤ average g := by
  classical
  exact div_le_div_of_nonneg_right (sum_le_sum (fun ω _ => h ω))
    (Nat.cast_nonneg (Fintype.card Ω))

private theorem average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    average (fun _ : Ω => c) = c := by
  classical
  have hN : (0 : ℚ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  unfold average
  apply (div_eq_iff hN.ne').mpr
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring

private theorem average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℚ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  classical
  simp only [average, sum_add_distrib, add_div]

private theorem average_const_mul {Ω : Type*} [Fintype Ω] (c : ℚ) (f : Ω → ℚ) :
    average (fun ω => c * f ω) = c * average f := by
  classical
  simp only [average, ← mul_sum, mul_div_assoc]

/-- A centered quadratic retains the negative linear contribution below a
threshold separated from the mean. No positivity of the mean is required. -/
theorem pointwise_majorant {s t x q μ d z W : ℚ}
    (hs : 1 ≤ s) (hx : 1 ≤ x) (hxq : x < q) (_hqs : q ≤ s + 1)
    (hμ : 0 ≤ μ) (hd : 0 < d) (hz : 0 ≤ z) (hzs : z ≤ s)
    (hmargin : μ + 2 * d ≤ s * x / q)
    (hlow : z ≤ x → W ≤ s * t - z * (x - q * z / (s + 1)))
    (hhigh : x ≤ z → W ≤ s * t + q * z - s * x) :
    W ≤ s * t + (-(q * d / (s + 1))) * z +
      (3 * q * s / (2 * d ^ 2)) * (z - μ) ^ 2 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hq0 : 0 < q := by linarith only [hx, hxq]
  have hden : 0 < s + 1 := by linarith only [hs]
  let a := s * x / q
  let L := a - d
  let c := q * d / (s + 1)
  let K := 3 * q * s / (2 * d ^ 2)
  have haq : a * q = s * x := div_mul_cancel₀ _ hq0.ne'
  have has : a < s := (div_lt_iff₀ hq0).mpr (mul_lt_mul_of_pos_left hxq hs0)
  have hμL : μ + d ≤ L := by dsimp only [L, a]; linarith only [hmargin]
  have h2d : 2 * d ≤ s := by dsimp only [a] at has; linarith only [has, hmargin, hμ]
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg hq0.le hd.le) hden.le
  have hK0 : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hq0.le) hs0.le)
    (mul_nonneg (by norm_num) (sq_nonneg d))
  have hcq : c ≤ q / 2 := by
    apply (div_le_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left h2d hq0.le
    nlinarith only [h, hq0.le]
  have hcden : c * (s + 1) = q * d := div_mul_cancel₀ _ hden.ne'
  have hKsq : K * d ^ 2 = 3 * q * s / 2 := by
    dsimp only [K]
    field_simp [hd.ne'] <;> ring
  change W ≤ s * t + (-c) * z + K * (z - μ) ^ 2
  by_cases hzL : z ≤ L
  · have hqz : q * z ≤ s * x - q * d := by
      have h := mul_le_mul_of_nonneg_left hzL hq0.le
      dsimp only [L] at h
      nlinarith only [h, haq]
    have hlinear : W ≤ s * t + (-c) * z := by
      by_cases hzx : z ≤ x
      · have hbound : c + q * z / (s + 1) ≤ x := by
          dsimp only [c]
          rw [← add_div]
          apply (div_le_iff₀ hden).mpr
          nlinarith only [hqz, hx0]
        have hmul := mul_le_mul_of_nonneg_left hbound hz
        nlinarith only [hlow hzx, hmul]
      · have hcz := mul_le_mul_of_nonneg_left
          (show z ≤ s + 1 by linarith only [hzs]) hc0
        nlinarith only [hhigh ((lt_of_not_ge hzx).le), hqz, hcz, hcden]
    have hnonneg := mul_nonneg hK0 (sq_nonneg (z - μ))
    linarith only [hlinear, hnonneg]
  · have hcrude : W ≤ s * t + q * z := by
      by_cases hzx : z ≤ x
      · have hqz : q * z / (s + 1) ≤ q := by
          apply (div_le_iff₀ hden).mpr
          have h := mul_le_mul_of_nonneg_left hzs hq0.le
          nlinarith only [h, hq0.le]
        have hmul := mul_le_mul_of_nonneg_left hqz hz
        have hprod := mul_nonneg hz hx0
        nlinarith only [hlow hzx, hmul, hprod]
      · have hprod := mul_nonneg hs0.le hx0
        linarith only [hhigh ((lt_of_not_ge hzx).le), hprod]
    have hdev : d ≤ z - μ := by linarith only [hμL, lt_of_not_ge hzL]
    have hsq : d ^ 2 ≤ (z - μ) ^ 2 := by
      have h := mul_nonneg (sub_nonneg.mpr hdev)
        (show 0 ≤ z - μ + d by linarith only [hdev, hd])
      nlinarith only [h]
    have hquad := mul_le_mul_of_nonneg_left hsq hK0
    have hsum := mul_le_mul_of_nonneg_left hzs (add_nonneg hq0.le hc0)
    have hslope := mul_le_mul_of_nonneg_right (add_le_add (le_refl q) hcq) hs0.le
    nlinarith only [hcrude, hquad, hKsq, hsum, hslope]

/-- The two FK finite branches transfer through a relative variance estimate.
The mean gap and cubic error budget are explicit and contain no density division. -/
theorem average_le_of_two_branches {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (z W : Ω → ℚ) {s t x q μ B d : ℚ}
    (hs : 1 ≤ s) (hx : 1 ≤ x) (hq : 1 ≤ q) (hqs : q ≤ s + 1)
    (_hB : 0 ≤ B) (hd : 0 < d)
    (hz : ∀ ω, 0 ≤ z ω) (hzs : ∀ ω, z ω ≤ s)
    (hmean : average z = μ)
    (hvariance : average (fun ω => (z ω) ^ 2) - μ ^ 2 ≤ B * μ)
    (hmargin : μ + 2 * d ≤ s * x / q)
    (hbudget : 3 * B * s * (s + 1) ≤ 2 * d ^ 3)
    (hlow : ∀ ω, z ω ≤ x → W ω ≤ s * t - z ω * (x - q * z ω / (s + 1)))
    (hhigh : ∀ ω, x ≤ z ω → W ω ≤ s * t + q * z ω - s * x) :
    average W ≤ s * t := by
  classical
  have hs0 : 0 < s := by linarith only [hs]
  have hq0 : 0 < q := by linarith only [hq]
  have hden : 0 < s + 1 := by linarith only [hs]
  by_cases hqx : q ≤ x
  · calc
      average W ≤ average (fun _ : Ω => s * t) := by
        apply average_mono
        intro ω
        by_cases hzx : z ω ≤ x
        · have hqz : q * z ω / (s + 1) ≤ q := by
            apply (div_le_iff₀ hden).mpr
            have h := mul_le_mul_of_nonneg_left (hzs ω) hq0.le
            nlinarith only [h, hq0.le]
          have hprod := mul_nonneg (hz ω)
            (show 0 ≤ x - q * z ω / (s + 1) by linarith only [hqx, hqz])
          linarith only [hlow ω hzx, hprod]
        · have hqz := mul_le_mul_of_nonneg_left (hzs ω) hq0.le
          have hqsx := mul_le_mul_of_nonneg_right hqx hs0.le
          nlinarith only [hhigh ω ((lt_of_not_ge hzx).le), hqz, hqsx]
      _ = _ := average_const _
  have hxq : x < q := lt_of_not_ge hqx
  have hμ : 0 ≤ μ := by
    rw [← hmean]
    exact div_nonneg (sum_nonneg (fun ω _ => hz ω)) (Nat.cast_nonneg _)
  let c := q * d / (s + 1)
  let K := 3 * q * s / (2 * d ^ 2)
  have hK0 : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hq0.le) hs0.le)
    (mul_nonneg (by norm_num) (sq_nonneg d))
  have hKB : K * B ≤ c := by
    let D := 2 * d ^ 2 * (s + 1)
    have hD : 0 < D := mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hd)) hden
    apply le_of_mul_le_mul_of_pos_right (a := D) ?_ hD
    have hleft : K * B * D = 3 * q * s * B * (s + 1) := by
      dsimp only [K, D]
      field_simp [hd.ne']
    have hright : c * D = 2 * q * d ^ 3 := by
      dsimp only [c, D]
      field_simp [hden.ne']
    rw [hleft, hright]
    have h := mul_le_mul_of_nonneg_left hbudget hq0.le
    nlinarith only [h]
  have hcenter : average (fun ω => (z ω - μ) ^ 2) =
      average (fun ω => (z ω) ^ 2) - μ ^ 2 := by
    calc
      _ = average (fun ω => (z ω) ^ 2 + (-2 * μ) * z ω + μ ^ 2) := by
        congr 1
        funext ω
        ring
      _ = _ := by
        rw [average_add, average_add, average_const_mul, average_const, hmean]
        ring
  have hcenterBound : average (fun ω => (z ω - μ) ^ 2) ≤ B * μ := by
    rw [hcenter]
    exact hvariance
  have havg := average_mono W
    (fun ω => s * t + (-c) * z ω + K * (z ω - μ) ^ 2)
    (fun ω => pointwise_majorant hs hx hxq hqs hμ hd (hz ω) (hzs ω)
      hmargin (hlow ω) (hhigh ω))
  rw [average_add, average_add, average_const, average_const_mul,
    average_const_mul, hmean] at havg
  have hcenterMul := mul_le_mul_of_nonneg_left hcenterBound hK0
  have hbudgetMean := mul_le_mul_of_nonneg_right hKB hμ
  nlinarith only [havg, hcenterMul, hbudgetMean]

/-- Samplewise nested families supply the two branches and the bound on z.
Mean, relative variance, separation and error budget remain explicit. -/
theorem average_nested_of_moments {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s t : ℕ} (A : Ω → Fin (s + 1) → Finset (Fin t)) (x q μ B d : ℚ)
    (hnested : ∀ ω i j, i ≤ j → A ω j ⊆ A ω i)
    (hno : ∀ ω, ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A ω i)
    (hs : 1 ≤ s) (hx : 1 ≤ x) (hxs : x ≤ (s : ℚ) + 1)
    (hq : 1 ≤ q) (hqs : q ≤ (s : ℚ) + 1)
    (hcapacity : (s : ℚ) + x + 1 ≤ t) (hB : 0 ≤ B) (hd : 0 < d)
    (hmean : average (fun ω => ((A ω (Fin.last s)).card : ℚ)) = μ)
    (hvariance : average (fun ω => ((A ω (Fin.last s)).card : ℚ) ^ 2) - μ ^ 2 ≤ B * μ)
    (hmargin : μ + 2 * d ≤ (s : ℚ) * x / q)
    (hbudget : 3 * B * (s : ℚ) * ((s : ℚ) + 1) ≤ 2 * d ^ 3) :
    average (fun ω => (∑ i, ((A ω i).card : ℚ)) +
      (q - 1) * (A ω (Fin.last s)).card) ≤ (s : ℚ) * t := by
  classical
  refine average_le_of_two_branches
    (s := (s : ℚ)) (t := (t : ℚ))
    (fun ω => ((A ω (Fin.last s)).card : ℚ)) _
    ((Nat.cast_le (α := ℚ)).mpr hs) hx hq hqs hB hd (fun _ => Nat.cast_nonneg _) ?_
    hmean hvariance hmargin hbudget ?_ ?_
  · intro ω
    obtain ⟨u, hzu, hus, _⟩ :=
      Submissions.Erdos1020MatchingFKFinite.Main.exists_suffix_bound
        (A ω) (hnested ω) (hno ω)
    exact (Nat.cast_le (α := ℚ)).mpr (hzu.trans hus)
  · intro ω hzx
    exact (Submissions.Erdos1020MatchingFKFinite.Main.weighted_bounds
      (A ω) (hnested ω) (hno ω) x q hx hxs hq hqs hcapacity).2 hzx
  · intro ω hxz
    exact (Submissions.Erdos1020MatchingFKFinite.Main.weighted_bounds
      (A ω) (hnested ω) (hno ω) x q hx hxs hq hqs hcapacity).1 hxz

end Submissions.Erdos1020MatchingFKTailAverage.Main

namespace Submissions.Erdos1020MatchingCoordinateShift.Main

open Finset

/-- Singleton downward stability implies closure under coordinatewise lowering
of increasing enumerations. Equal coordinates and the empty enumeration are allowed. -/
theorem image_mem_of_le {α : Type*} [LinearOrder α] {k : ℕ}
    (H : Finset (Finset α)) (f g : Fin k → α)
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} H)
    (hf : StrictMono f) (hg : StrictMono g) (hfg : ∀ i, f i ≤ g i)
    (hmem : univ.image g ∈ H) : univ.image f ∈ H := by
  classical
  let u : ℕ → Fin k → α := fun t i => if i.val < t then f i else g i
  have split (v : Fin k → α) (j : Fin k) :
      univ.image v = insert (v j) ((univ.erase j).image v) := by
    rw [← image_insert, insert_erase (mem_univ j)]
  have step (t : ℕ) (ht : t < k) (hm : univ.image (u t) ∈ H) :
      univ.image (u (t + 1)) ∈ H := by
    let j : Fin k := ⟨t, ht⟩
    let D := (univ.erase j).image (u t)
    have hj : u t j = g j := by simp [u, j]
    have hj' : u (t + 1) j = f j := by simp [u, j]
    have hsep (i : Fin k) (hi : i ∈ univ.erase j) :
        u t i < f j ∨ g j < u t i := by
      have hne : i.val ≠ t := by
        intro heq
        exact (mem_erase.mp hi).1 (Fin.ext heq)
      by_cases hit : i.val < t
      · left
        simpa only [u, if_pos hit] using hf (show i < j from hit)
      · right
        have hti : j < i := by change t < i.val; omega
        simpa only [u, if_neg hit] using hg hti
    have hfj : f j ∉ D := by
      rintro hx
      obtain ⟨i, hi, heq⟩ := mem_image.mp hx
      rcases hsep i hi with h | h
      · exact (ne_of_lt h) heq
      · exact (ne_of_gt ((hfg j).trans_lt h)) heq
    have hgj : g j ∉ D := by
      rintro hx
      obtain ⟨i, hi, heq⟩ := mem_image.mp hx
      rcases hsep i hi with h | h
      · exact (ne_of_lt (h.trans_le (hfg j))) heq
      · exact (ne_of_gt h) heq
    have hkeep : (univ.erase j).image (u (t + 1)) = D := by
      apply image_congr
      intro i hi
      have hne : i.val ≠ t := by
        intro heq
        exact (mem_erase.mp hi).1 (Fin.ext heq)
      by_cases hit : i.val < t
      · have hit' : i.val < t + 1 := by omega
        simp only [u, if_pos hit, if_pos hit']
      · have hit' : ¬ i.val < t + 1 := by omega
        simp only [u, if_neg hit, if_neg hit']
    have hm' : insert (g j) D ∈ H := by
      simpa only [split (u t) j, hj] using hm
    rw [split (u (t + 1)) j, hj', hkeep]
    rcases (hfg j).eq_or_lt with heq | hlt
    · simpa only [heq] using hm'
    · exact Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
        (hstable _ _ hlt) hgj hfj hm'
  have all (t : ℕ) (ht : t ≤ k) : univ.image (u t) ∈ H := by
    induction t with
    | zero => simpa only [u, Nat.not_lt_zero, if_false] using hmem
    | succ t ih => exact step t (by omega) (ih (by omega))
  simpa only [u, Fin.isLt, if_true] using all k le_rfl

end Submissions.Erdos1020MatchingCoordinateShift.Main

namespace Submissions.Erdos1020MatchingFKPrefixWitness.Main

open Finset

/-- A spread increasing edge in a downward-stable family produces the literal
forbidden matching by taking residue classes modulo the matching size. -/
theorem exists_matching_of_spread {m ell k : ℕ} (hell : 0 < ell) (hk : 0 < k)
    (H : Finset (Finset (Fin m))) (g : Fin ell → Fin m)
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} H)
    (hg : StrictMono g) (hmem : univ.image g ∈ H)
    (hlower : ∀ j, (j.val + 1) * k - 1 ≤ (g j).val) :
    ∃ M : Finset (Finset (Fin m)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  let f : Fin k → Fin ell → Fin m := fun c j =>
    ⟨j.val * k + c.val, by
      have hj := hlower j
      have hm := (g j).isLt
      have hc := c.isLt
      rw [Nat.add_mul, one_mul] at hj
      omega⟩
  have hfm (c : Fin k) : StrictMono (f c) := by
    intro i j hij
    change i.val * k + c.val < j.val * k + c.val
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hij hk) _
  have hfg (c : Fin k) (j : Fin ell) : f c j ≤ g j := by
    change j.val * k + c.val ≤ (g j).val
    have hj := hlower j
    have hc := c.isLt
    rw [Nat.add_mul, one_mul] at hj
    omega
  let E : Fin k → Finset (Fin m) := fun c => univ.image (f c)
  have hE (c : Fin k) : E c ∈ H :=
    Submissions.Erdos1020MatchingCoordinateShift.Main.image_mem_of_le
      H (f c) g hstable (hfm c) hg (hfg c) hmem
  have hdis : Pairwise (fun c d => Disjoint (E c) (E d)) := by
    intro c d hcd
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := mem_image.mp hx
    obtain ⟨j, _, hj⟩ := mem_image.mp hy
    have heq := congrArg (fun a : Fin m => a.val % k) (hi.trans hj.symm)
    have hvals : c.val = d.val := by
      simpa only [f, Nat.add_mod, Nat.mul_mod_left, zero_add,
        Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt d.isLt] using heq
    exact hcd (Fin.ext hvals)
  have hinj : Function.Injective E := by
    intro c d heq
    by_contra hcd
    have hself : Disjoint (E c) (E c) := by simpa only [heq] using hdis hcd
    have hempty := disjoint_self.mp hself
    have hx : f c ⟨0, hell⟩ ∈ E c := mem_image.mpr ⟨⟨0, hell⟩, mem_univ _, rfl⟩
    exact (show (E c).Nonempty from ⟨_, hx⟩).ne_empty hempty
  refine ⟨univ.image E, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨c, _, rfl⟩ := mem_image.mp he
    exact hE c
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  · intro e he f hf hef
    obtain ⟨c, _, rfl⟩ := mem_image.mp he
    obtain ⟨d, _, rfl⟩ := mem_image.mp hf
    exact hdis (fun h => hef (congrArg E h))

/-- The j-th order statistic below a cut gives at least j+1 points below it. -/
theorem prefix_card_of_orderEmb_lt {m ell q : ℕ} (e : Finset (Fin m))
    (hc : e.card = ell) (j : Fin ell)
    (hlt : (e.orderEmbOfFin hc j).val < q) :
    j.val + 1 ≤ (e.filter (fun x => x.val < q)).card := by
  let f : Fin (j.val + 1) → Fin m := fun i =>
    e.orderEmbOfFin hc ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
  have hinj : Function.Injective f := by
    intro i l hil
    have h := (e.orderEmbOfFin hc).injective hil
    exact Fin.ext (congrArg (fun z : Fin ell => z.val) h)
  have hsub : univ.image f ⊆ e.filter (fun x => x.val < q) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    apply mem_filter.mpr
    refine ⟨e.orderEmbOfFin_mem hc _, ?_⟩
    have hle : f i ≤ e.orderEmbOfFin hc j :=
      (e.orderEmbOfFin hc).monotone (show (⟨i.val, _⟩ : Fin ell) ≤ j by
        change i.val ≤ j.val
        have := i.isLt
        omega)
    exact lt_of_le_of_lt hle hlt
  simpa only [card_image_of_injective _ hinj, card_univ, Fintype.card_fin] using
    card_le_card hsub

/-- Every positive-size member of a shifted matching-free family is crowded
in at least one initial prefix. Uniformity of the whole family is unnecessary. -/
theorem exists_prefix {m ell k : ℕ} (hell : 0 < ell) (hk : 0 < k)
    (H : Finset (Finset (Fin m))) (e : Finset (Fin m))
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} H)
    (he : e ∈ H) (hc : e.card = ell)
    (hfree : ¬ ∃ M : Finset (Finset (Fin m)), M ⊆ H ∧ M.card = k ∧
      ∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint a b) :
    ∃ i, 1 ≤ i ∧ i ≤ ell ∧
      i ≤ (e.filter (fun x => x.val < i * k - 1)).card := by
  by_contra hno
  apply hfree
  apply exists_matching_of_spread hell hk H (e.orderEmbOfFin hc) hstable
    (e.orderEmbOfFin hc).strictMono (by simpa only [image_orderEmbOfFin_univ] using he)
  intro j
  by_contra hn
  have hlt : (e.orderEmbOfFin hc j).val < (j.val + 1) * k - 1 := by omega
  exact hno ⟨j.val + 1, by omega, by have := j.isLt; omega,
    prefix_card_of_orderEmb_lt e hc j hlt⟩

/-- Shadow matching-freeness forces the precise FK layer prefix witness. -/
theorem exists_shadow_prefix {m r s : ℕ} (hr : 2 ≤ r)
    (G : Finset (Finset (Fin m))) (e : Finset (Fin m))
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} G)
    (he : e ∈ G) (hc : e.card = r)
    (hfree : ¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G.shadow ∧ M.card = s + 1 ∧
      ∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint a b) :
    ∃ i, 1 ≤ i ∧ i < r ∧
      i + 1 ≤ (e.filter (fun x => x.val < i * (s + 1) - 1)).card := by
  have hne : e.Nonempty := Finset.card_pos.mp (by omega)
  let v := e.min' hne
  have hv : v ∈ e := e.min'_mem hne
  have ha : e.erase v ∈ G.shadow := erase_mem_shadow he hv
  have hac : (e.erase v).card = r - 1 := by rw [card_erase_of_mem hv, hc]
  obtain ⟨i, hi, hir, hcount⟩ := exists_prefix (by omega : 0 < r - 1)
    (Nat.succ_pos s) G.shadow (e.erase v)
    (fun x z h => Submissions.Erdos1020MatchingShadowLinks.Main.isCompressed_shadow
      G x z (hstable x z h)) ha hac hfree
  let A := (e.erase v).filter (fun x => x.val < i * (s + 1) - 1)
  have hA : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < i) hcount)
  obtain ⟨x, hx⟩ := hA
  have hxE : x ∈ e := mem_of_mem_erase (mem_filter.mp hx).1
  have hvcut : v.val < i * (s + 1) - 1 :=
    lt_of_le_of_lt (e.min'_le x hxE) (mem_filter.mp hx).2
  have hvA : v ∉ A := fun h => (notMem_erase v e) (mem_filter.mp h).1
  have hsub : insert v A ⊆ e.filter (fun x => x.val < i * (s + 1) - 1) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_filter.mpr ⟨hv, hvcut⟩
    · exact mem_filter.mpr ⟨mem_of_mem_erase (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩
  have hb := card_le_card hsub
  rw [card_insert_of_notMem hvA] at hb
  exact ⟨i, hi, by omega, by change i ≤ A.card at hcount; omega⟩

end Submissions.Erdos1020MatchingFKPrefixWitness.Main

namespace Submissions.Erdos1020MatchingFKLayerDual.Main

open Finset

/-- An exact finite dual bound from explicit layer counts, restricted-shadow
counts and layer capacities. No assertion about a matching family is assumed. -/
theorem four_card_bound (I : Finset ℕ) (s A D : ℕ) (g h U : ℕ → ℕ)
    (hI : ∀ i ∈ I, 1 ≤ i)
    (hA : A = ∑ i ∈ I, g i) (hD : (∑ i ∈ I, h i) ≤ D)
    (hlocal : ∀ i ∈ I, (i + 1) * g i ≤ i * s * h i)
    (hcap : ∀ i ∈ I, g i ≤ U i) :
    4 * (A : ℚ) ≤ 3 * (s : ℚ) * D +
      ∑ i ∈ I, (((i - 3 : ℕ) : ℚ) / (i : ℚ)) * U i := by
  have hpoint (i : ℕ) (hi : i ∈ I) :
      4 * (g i : ℚ) ≤ 3 * (s : ℚ) * h i +
        (((i - 3 : ℕ) : ℚ) / (i : ℚ)) * U i := by
    have hip : (0 : ℚ) < i := Nat.cast_pos.mpr (hI i hi)
    have hg0 : (0 : ℚ) ≤ g i := Nat.cast_nonneg _
    have hl : ((i : ℚ) + 1) * g i ≤ (i : ℚ) * s * h i := by
      exact_mod_cast hlocal i hi
    by_cases hi3 : i ≤ 3
    · have hieq : i - 3 = 0 := Nat.sub_eq_zero_of_le hi3
      simp only [hieq, Nat.cast_zero, zero_div, zero_mul, add_zero]
      apply le_of_mul_le_mul_of_pos_left (a := (i : ℚ)) ?_ hip
      have hiq : (i : ℚ) ≤ 3 := by exact_mod_cast hi3
      have hnonneg := mul_nonneg (sub_nonneg.mpr hiq) hg0
      nlinarith only [hl, hnonneg]
    · have h3i : 3 ≤ i := by omega
      have hu : (g i : ℚ) ≤ U i := Nat.cast_le.mpr (hcap i hi)
      have hrest := mul_le_mul_of_nonneg_left hu
        (show (0 : ℚ) ≤ ((i - 3 : ℕ) : ℚ) from Nat.cast_nonneg _)
      have hiq : ((i - 3 : ℕ) : ℚ) = (i : ℚ) - 3 := by
        rw [Nat.cast_sub h3i]
        norm_num
      have hcancel : (i : ℚ) * ((((i - 3 : ℕ) : ℚ) / (i : ℚ)) * U i) =
          ((i - 3 : ℕ) : ℚ) * U i := by
        rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hip.ne']
      apply le_of_mul_le_mul_of_pos_left (a := (i : ℚ)) ?_ hip
      rw [mul_add, hcancel]
      rw [hiq] at hrest ⊢
      nlinarith only [hl, hrest]
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hAQ : (A : ℚ) = ∑ i ∈ I, (g i : ℚ) := by exact_mod_cast hA
  have hDQ : (∑ i ∈ I, (h i : ℚ)) ≤ (D : ℚ) := by exact_mod_cast hD
  rw [← hAQ] at hsum
  have hscale := mul_le_mul_of_nonneg_left hDQ
    (show (0 : ℚ) ≤ 3 * (s : ℚ) from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  exact hsum.trans (add_le_add hscale le_rfl)

/-- The remaining numerical inequality is exposed as a separate premise. This
lemma neither supplies the layer counts nor asserts a density estimate. -/
theorem card_le_of_numeric (I : Finset ℕ) (s A D L C : ℕ) (g h U : ℕ → ℕ)
    (θ : ℚ) (hI : ∀ i ∈ I, 1 ≤ i)
    (hA : A = ∑ i ∈ I, g i) (hD : (∑ i ∈ I, h i) ≤ D)
    (hlocal : ∀ i ∈ I, (i + 1) * g i ≤ i * s * h i)
    (hcap : ∀ i ∈ I, g i ≤ U i) (hDL : D ≤ L)
    (hnumeric : 3 * (s : ℚ) * L +
      (∑ i ∈ I, (((i - 3 : ℕ) : ℚ) / (i : ℚ)) * U i) ≤
        4 * (θ * s * C)) :
    (A : ℚ) ≤ θ * s * C := by
  have hb := four_card_bound I s A D g h U hI hA hD hlocal hcap
  have hDLQ : (D : ℚ) ≤ L := Nat.cast_le.mpr hDL
  have hscale := mul_le_mul_of_nonneg_left hDLQ
    (show (0 : ℚ) ≤ 3 * (s : ℚ) from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hfinal := hb.trans ((add_le_add hscale le_rfl).trans hnumeric)
  linarith only [hfinal]

end Submissions.Erdos1020MatchingFKLayerDual.Main

namespace Submissions.Erdos1020MatchingOrderedTail.Main

open Finset

/-- Increasing reindexing of the actual zero-head family preserves its shadow,
literal shadow matching restriction, and downward stability. -/
theorem reindex_zero_head {n m r k : ℕ}
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (hc : Tᶜ.card = m) (hH : ∀ e ∈ H, e.card = r)
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ (H.filter (fun e => e ∩ T = ∅)).shadow ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Finset (Fin m)),
      G.card = (H.filter (fun e => e ∩ T = ∅)).card ∧
      G.shadow.card = (H.filter (fun e => e ∩ T = ∅)).shadow.card ∧
      (∀ e ∈ G, e.card = r) ∧
      (¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G.shadow ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
      ∀ x z, x < z → UV.IsCompressed {x} {z} G := by
  classical
  let E : Fin m ↪o Fin n := Tᶜ.orderEmbOfFin hc
  let B := E.toEmbedding
  let B' := (Finset.mapEmbedding B).toEmbedding
  let G := H.preimage B' B'.injective.injOn
  let Z := H.filter (fun e => e ∩ T = ∅)
  have hmem (e : Finset (Fin m)) : e ∈ G ↔ e.map B ∈ H := mem_preimage
  have havoid (e : Finset (Fin m)) : e.map B ∩ T = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨a, _, rfl⟩ := mem_map.mp (mem_inter.mp hx).1
    exact (mem_compl.mp (Tᶜ.orderEmbOfFin_mem hc a)) (mem_inter.mp hx).2
  have hmap : G.map B' = Z := by
    ext e
    constructor
    · intro he
      obtain ⟨a, ha, rfl⟩ := mem_map.mp he
      exact mem_filter.mpr ⟨(hmem a).mp ha, havoid a⟩
    · intro he
      have heH := (mem_filter.mp he).1
      have heT := (mem_filter.mp he).2
      have hsub : e ⊆ univ.map B := by
        rw [show univ.map B = Tᶜ from Tᶜ.map_orderEmbOfFin_univ hc]
        intro x hx
        apply mem_compl.mpr
        intro hxT
        have hm : x ∈ e ∩ T := mem_inter.mpr ⟨hx, hxT⟩
        rw [heT] at hm
        exact notMem_empty x hm
      obtain ⟨a, _, hea⟩ := subset_map_iff.mp hsub
      refine mem_map.mpr ⟨a, (hmem a).mpr ?_, hea.symm⟩
      rwa [← hea]
  have hshadow : G.shadow.map B' = Z.shadow := by
    rw [← Submissions.Erdos1020MatchingShadowBasics.Main.shadow_map G B, hmap]
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [card_map] using congrArg card hmap
  · simpa only [card_map] using congrArg card hshadow
  · intro e he
    simpa only [card_map] using hH _ ((hmem e).mp he)
  · rintro ⟨M, hMG, hMc, hMd⟩
    apply hfree
    refine ⟨M.map B', ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨a, ha, rfl⟩ := mem_map.mp he
      rw [← hshadow]
      exact mem_map.mpr ⟨a, hMG ha, rfl⟩
    · simpa only [card_map] using hMc
    · intro e he f hf hef
      obtain ⟨a, ha, rfl⟩ := mem_map.mp he
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hf
      exact (disjoint_map B).mpr (hMd a ha b hb (fun h => hef (congrArg B' h)))
  · intro x z hxz
    have hclose (e : Finset (Fin m)) (he : e ∈ G) :
        UV.compress {x} {z} e ∈ G := by
      by_cases hx : x ∈ e
      · simpa [UV.compress, disjoint_singleton_left, hx] using he
      by_cases hz : z ∈ e
      · have hcompressed : UV.compress {x} {z} e = insert x (e.erase z) := by
          rw [UV.compress_of_disjoint_of_le (disjoint_singleton_left.mpr hx)
            (singleton_subset_iff.mpr hz), sup_eq_union, union_singleton,
            sdiff_singleton_eq_erase, erase_insert_of_ne hxz.ne]
        rw [hcompressed, hmem, map_insert]
        apply Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
          (hstable (E x) (E z) (E.strictMono hxz))
        · intro h
          exact notMem_erase z e ((mem_map' B).mp h)
        · intro h
          exact hx (mem_of_mem_erase ((mem_map' B).mp h))
        · change insert (B z) ((e.erase z).map B) ∈ H
          rw [← map_insert, insert_erase hz]
          exact (hmem e).mp he
      · simpa [UV.compress, singleton_subset_iff, hz] using he
    change UV.compression {x} {z} G = G
    ext e
    rw [UV.mem_compression]
    constructor
    · rintro (⟨he, _⟩ | ⟨_, f, hf, rfl⟩)
      · exact he
      · exact hclose f hf
    · intro he
      exact Or.inl ⟨he, hclose e he⟩

end Submissions.Erdos1020MatchingOrderedTail.Main

namespace Submissions.Erdos1020MatchingFKLayers.Main

open Finset

/-- The paper's one-based initial segment, expressed on zero-based `Fin m`. -/
def «prefix» {m : ℕ} (s i : ℕ) : Finset (Fin m) :=
  univ.filter (fun x : Fin m => x.val < i * (s + 1) - 1)

theorem prefix_mono {m : ℕ} (s : ℕ) : Monotone («prefix» (m := m) s) := by
  intro i j hij x hx
  have hcut := Nat.sub_le_sub_right (Nat.mul_le_mul_right (s + 1) hij) 1
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hx).2 hcut⟩

theorem card_prefix {m s i : ℕ} (hroom : i * (s + 1) - 1 ≤ m) :
    («prefix» (m := m) s i).card = i * (s + 1) - 1 := by
  simpa only [«prefix», Fin.card_filter_val_lt, min_eq_right hroom]

theorem inter_prefix {m : ℕ} (e : Finset (Fin m)) (s i : ℕ) :
    e ∩ «prefix» s i = e.filter (fun x : Fin m => x.val < i * (s + 1) - 1) := by
  ext x
  simp only [«prefix», mem_inter, mem_filter, mem_univ, true_and]

/-- Edges for which i is the last prefix with at least i+1 vertices. -/
noncomputable def layer {α : Type*} [DecidableEq α] (G : Finset (Finset α))
    (P : ℕ → Finset α) (r i : ℕ) : Finset (Finset α) := by
  classical
  exact G.filter (fun e => i + 1 ≤ (e ∩ P i).card ∧
    ∀ j, i < j → j < r → (e ∩ P j).card ≤ j)

theorem layer_subset {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r i : ℕ) :
    layer G P r i ⊆ G := by
  classical
  exact filter_subset _ _

theorem layers_disjoint {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i j : ℕ}
    (hi : i < r) (hj : j < r) (hne : i ≠ j) :
    Disjoint (layer G P r i) (layer G P r j) := by
  classical
  apply disjoint_left.mpr
  intro e hei hej
  have hei' := (mem_filter.mp hei).2
  have hej' := (mem_filter.mp hej).2
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hupper := hei'.2 j hij hj
    omega
  · have hupper := hej'.2 i hji hi
    omega

/-- A supplied prefix witness puts every edge into one of the actual layers. -/
theorem exists_mem_layer {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r : ℕ)
    (e : Finset α) (he : e ∈ G)
    (hprefix : ∃ i, 1 ≤ i ∧ i < r ∧ i + 1 ≤ (e ∩ P i).card) :
    ∃ i ∈ Icc 1 (r - 1), e ∈ layer G P r i := by
  classical
  let J := (Icc 1 (r - 1)).filter (fun i => i + 1 ≤ (e ∩ P i).card)
  have hJ : J.Nonempty := by
    obtain ⟨i, hi1, hir, hi⟩ := hprefix
    exact ⟨i, mem_filter.mpr ⟨mem_Icc.mpr ⟨hi1, by omega⟩, hi⟩⟩
  let i := J.max' hJ
  have hiJ : i ∈ J := max'_mem J hJ
  have hiI := (mem_filter.mp hiJ).1
  refine ⟨i, hiI, mem_filter.mpr ⟨he, (mem_filter.mp hiJ).2, ?_⟩⟩
  intro j hij hjr
  by_contra hbad
  have hjJ : j ∈ J := by
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, by omega⟩, by omega⟩
    have hi1 := (mem_Icc.mp hiI).1
    omega
  have hji : j ≤ i := le_max' J j hjJ
  omega

theorem biUnion_layers {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r : ℕ)
    (hprefix : ∀ e ∈ G, ∃ i, 1 ≤ i ∧ i < r ∧ i + 1 ≤ (e ∩ P i).card) :
    (Icc 1 (r - 1)).biUnion (layer G P r) = G := by
  classical
  apply Subset.antisymm
  · intro e he
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
    exact layer_subset G P r i hei
  · intro e he
    obtain ⟨i, hi, hei⟩ := exists_mem_layer G P r e he (hprefix e he)
    exact mem_biUnion.mpr ⟨i, hi, hei⟩

theorem card_eq_sum_layers {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r : ℕ)
    (hprefix : ∀ e ∈ G, ∃ i, 1 ≤ i ∧ i < r ∧ i + 1 ≤ (e ∩ P i).card) :
    G.card = ∑ i ∈ Icc 1 (r - 1), (layer G P r i).card := by
  classical
  calc
    _ = ((Icc 1 (r - 1)).biUnion (layer G P r)).card :=
      congrArg Finset.card (biUnion_layers G P r hprefix).symm
    _ = _ := by
      apply card_biUnion
      intro i hi j hj hij
      apply layers_disjoint G P _ _ hij
      · have hi' := mem_Icc.mp hi
        omega
      · have hj' := mem_Icc.mp hj
        omega

/-- Maximality of the prefix index fixes both adjacent prefix cardinalities. -/
theorem layer_inter_cards {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i : ℕ}
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r) (hi : i < r)
    {e : Finset α} (he : e ∈ layer G P r i) :
    (e ∩ P i).card = i + 1 ∧ (e ∩ P (i + 1)).card = i + 1 := by
  classical
  have hp := (mem_filter.mp he).2
  have her := hG e (layer_subset G P r i he)
  have hsub : e ∩ P i ⊆ e ∩ P (i + 1) :=
    inter_subset_inter (Subset.refl _) (hmono (Nat.le_succ i))
  have hle := card_le_card hsub
  have hupper : (e ∩ P (i + 1)).card ≤ i + 1 := by
    by_cases hir : i + 1 < r
    · exact hp.2 (i + 1) (Nat.lt_succ_self _) hir
    · have hb : (e ∩ P (i + 1)).card ≤ r :=
        (card_le_card inter_subset_left).trans_eq her
      omega
  omega

theorem layer_inter_succ_eq {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i : ℕ}
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r) (hi : i < r)
    {e : Finset α} (he : e ∈ layer G P r i) :
    e ∩ P (i + 1) = e ∩ P i := by
  classical
  obtain ⟨hiC, hnC⟩ := layer_inter_cards G P hmono hG hi he
  symm
  exact eq_of_subset_of_card_le
    (inter_subset_inter (Subset.refl _) (hmono (Nat.le_succ i))) (by omega)

/-- Head and tail parts inject a layer into a product of two uniform powersets. -/
theorem card_layer_le {α : Type*} [Fintype α] [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i : ℕ}
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r) (hi : i < r) :
    (layer G P r i).card ≤ (P i).card.choose (i + 1) *
      (Fintype.card α - (P (i + 1)).card).choose (r - i - 1) := by
  classical
  let f (e : Finset α) := (e ∩ P i, e \ P (i + 1))
  have hrec (e) (he : e ∈ layer G P r i) :
      (e ∩ P i) ∪ (e \ P (i + 1)) = e := by
    rw [← layer_inter_succ_eq G P hmono hG hi he]
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_inter.mp hx).1
      · exact (mem_sdiff.mp hx).1
    · intro hx
      by_cases hxP : x ∈ P (i + 1)
      · exact mem_union_left _ (mem_inter.mpr ⟨hx, hxP⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, hxP⟩)
  have hinj : Set.InjOn f (layer G P r i) := by
    intro e he a ha hfa
    have h1 := congrArg Prod.fst hfa
    have h2 := congrArg Prod.snd hfa
    dsimp only [f] at h1 h2
    rw [← hrec e he, ← hrec a ha, h1, h2]
  have hmem (e) (he : e ∈ layer G P r i) :
      f e ∈ (P i).powersetCard (i + 1) ×ˢ
        ((univ : Finset α) \ P (i + 1)).powersetCard (r - i - 1) := by
    obtain ⟨hic, hnc⟩ := layer_inter_cards G P hmono hG hi he
    have her := hG e (layer_subset G P r i he)
    refine mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right, hic⟩,
      mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro x hx
      exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
    · change (e \ P (i + 1)).card = r - i - 1
      have hc := card_sdiff_add_card_inter e (P (i + 1))
      omega
  calc
    _ = ((layer G P r i).image f).card := (card_image_of_injOn hinj).symm
    _ ≤ ((P i).powersetCard (i + 1) ×ˢ
        ((univ : Finset α) \ P (i + 1)).powersetCard (r - i - 1)).card := by
      apply card_le_card
      intro a ha
      obtain ⟨e, he, rfl⟩ := mem_image.mp ha
      exact hmem e he
    _ = _ := by
      rw [card_product, card_powersetCard, card_powersetCard,
        card_sdiff_of_subset (subset_univ _), card_univ]

theorem card_prefix_layer_le {m r s i : ℕ}
    (G : Finset (Finset (Fin m))) (hG : ∀ e ∈ G, e.card = r)
    (hroom : r * (s + 1) - 1 ≤ m) (hi : i < r) :
    (layer G («prefix» s) r i).card ≤
      (i * (s + 1) - 1).choose (i + 1) *
        (m + 1 - (i + 1) * (s + 1)).choose (r - i - 1) := by
  classical
  have hip : i * (s + 1) - 1 ≤ m :=
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hi.le) 1).trans hroom
  have hin : (i + 1) * (s + 1) - 1 ≤ m :=
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hi) 1).trans hroom
  have hnpos : 1 ≤ (i + 1) * (s + 1) := Nat.mul_pos (by omega) (by omega)
  have hsub : m - ((i + 1) * (s + 1) - 1) =
      m + 1 - (i + 1) * (s + 1) := by omega
  have h := card_layer_le G («prefix» s) (prefix_mono s) hG hi
  rw [card_prefix hip, card_prefix hin, Fintype.card_fin, hsub] at h
  exact h

/-- The part of a layer's shadow obtained by removing a head vertex. -/
noncomputable def restrictedShadow {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r i : ℕ) :
    Finset (Finset α) :=
  (layer G P r i).biUnion (fun e => (e ∩ P i).image e.erase)

theorem restrictedShadow_subset {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r i : ℕ) :
    restrictedShadow G P r i ⊆ G.shadow := by
  classical
  intro a ha
  obtain ⟨e, he, ha⟩ := mem_biUnion.mp ha
  obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
  exact erase_mem_shadow (layer_subset G P r i he) (mem_inter.mp hv).1

/-- The shadow edge itself determines the last dense prefix, hence its layer. -/
theorem restrictedShadow_prefix {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i : ℕ}
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r) (hi : i < r)
    {a : Finset α} (ha : a ∈ restrictedShadow G P r i) :
    (a ∩ P i).card = i ∧
      ∀ j, i < j → j < r → (a ∩ P j).card < j := by
  classical
  obtain ⟨e, he, ha⟩ := mem_biUnion.mp ha
  obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
  have hc := (layer_inter_cards G P hmono hG hi he).1
  refine ⟨?_, ?_⟩
  · rw [erase_inter, card_erase_of_mem hv, hc]
    omega
  · intro j hij hj
    have hvj : v ∈ e ∩ P j :=
      mem_inter.mpr ⟨(mem_inter.mp hv).1, hmono hij.le (mem_inter.mp hv).2⟩
    have hmax := (mem_filter.mp he).2.2 j hij hj
    have hpos : 0 < (e ∩ P j).card := card_pos.mpr ⟨v, hvj⟩
    rw [erase_inter, card_erase_of_mem hvj]
    omega

theorem restrictedShadows_disjoint {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i j : ℕ}
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r)
    (hi : i < r) (hj : j < r) (hne : i ≠ j) :
    Disjoint (restrictedShadow G P r i) (restrictedShadow G P r j) := by
  classical
  apply disjoint_left.mpr
  intro a hai haj
  have hpi := restrictedShadow_prefix G P hmono hG hi hai
  have hpj := restrictedShadow_prefix G P hmono hG hj haj
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hc := hpi.2 j hij hj
    omega
  · have hc := hpj.2 i hji hi
    omega

theorem sum_card_restrictedShadow_le {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) (r : ℕ)
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r) :
    (∑ i ∈ Icc 1 (r - 1), (restrictedShadow G P r i).card) ≤ G.shadow.card := by
  classical
  have hd : ((Icc 1 (r - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (restrictedShadow G P r) := by
    intro i hi j hj hij
    apply restrictedShadows_disjoint G P hmono hG _ _ hij
    · have hi' := mem_Icc.mp hi
      omega
    · have hj' := mem_Icc.mp hj
      omega
  rw [← card_biUnion hd]
  apply card_le_card
  intro a ha
  obtain ⟨i, _, hai⟩ := mem_biUnion.mp ha
  exact restrictedShadow_subset G P r i hai

/-- Count head erasures in both directions. A shadow edge has at most
`(P i).card - i` predecessors, because its prefix already contains i vertices. -/
theorem layer_incidence {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (P : ℕ → Finset α) {r i : ℕ}
    (hmono : Monotone P) (hG : ∀ e ∈ G, e.card = r) (hi : i < r) :
    (i + 1) * (layer G P r i).card ≤
      ((P i).card - i) * (restrictedShadow G P r i).card := by
  classical
  let R (e a : Finset α) : Prop := ∃ v ∈ e ∩ P i, e.erase v = a
  have hlow (e) (he : e ∈ layer G P r i) :
      i + 1 ≤ ((restrictedShadow G P r i).bipartiteAbove R e).card := by
    have hinj : Set.InjOn e.erase ↑(e ∩ P i : Finset α) := by
      intro v hv w _ heq
      exact (erase_inj e (mem_inter.mp hv).1).mp heq
    have hc : ((e ∩ P i).image e.erase).card = i + 1 := by
      rw [card_image_of_injOn hinj]
      exact (layer_inter_cards G P hmono hG hi he).1
    rw [← hc]
    apply card_le_card
    intro a ha
    obtain ⟨v, hv, hva⟩ := mem_image.mp ha
    exact (mem_bipartiteAbove R).mpr ⟨mem_biUnion.mpr
      ⟨e, he, mem_image.mpr ⟨v, hv, hva⟩⟩, ⟨v, hv, hva⟩⟩
  have hupp (a) (ha : a ∈ restrictedShadow G P r i) :
      ((layer G P r i).bipartiteBelow R a).card ≤ (P i).card - i := by
    have hs : (layer G P r i).bipartiteBelow R a ⊆
        (P i \ a).image (fun v => insert v a) := by
      intro e he
      obtain ⟨_, v, hv, hva⟩ := (mem_bipartiteBelow R).mp he
      have hva' : v ∉ a := by rw [← hva]; exact notMem_erase _ _
      refine mem_image.mpr ⟨v, mem_sdiff.mpr ⟨(mem_inter.mp hv).2, hva'⟩, ?_⟩
      rw [← hva, insert_erase (mem_inter.mp hv).1]
    calc
      _ ≤ ((P i \ a).image (fun v => insert v a)).card := card_le_card hs
      _ ≤ (P i \ a).card := card_image_le
      _ = _ := by
        rw [card_sdiff, (restrictedShadow_prefix G P hmono hG hi ha).1]
  have h := card_mul_le_card_mul R hlow hupp
  simpa only [Nat.mul_comm] using h

theorem prefix_layer_incidence {m r s i : ℕ}
    (G : Finset (Finset (Fin m))) (hG : ∀ e ∈ G, e.card = r)
    (hroom : r * (s + 1) - 1 ≤ m) (hi : i < r) :
    (i + 1) * (layer G («prefix» s) r i).card ≤
      i * s * (restrictedShadow G («prefix» s) r i).card := by
  have hip : i * (s + 1) - 1 ≤ m :=
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hi.le) 1).trans hroom
  have hcoeff : («prefix» (m := m) s i).card - i ≤ i * s := by
    rw [card_prefix hip]
    have heq : i * (s + 1) = i * s + i := by rw [Nat.mul_add, Nat.mul_one]
    omega
  exact (layer_incidence G («prefix» s) (prefix_mono s) hG hi).trans
    (Nat.mul_le_mul_right _ hcoeff)

/-- Actual layer and restricted-shadow counts supply the finite dual inputs.
The prefix witness is explicit and must be supplied by the shifting argument. -/
theorem exists_layer_counts {m r s : ℕ}
    (G : Finset (Finset (Fin m))) (hG : ∀ e ∈ G, e.card = r)
    (hroom : r * (s + 1) - 1 ≤ m)
    (hprefix : ∀ e ∈ G, ∃ i, 1 ≤ i ∧ i < r ∧
      i + 1 ≤ (e.filter (fun x : Fin m => x.val < i * (s + 1) - 1)).card) :
    ∃ g h : ℕ → ℕ,
      G.card = (∑ i ∈ Icc 1 (r - 1), g i) ∧
      (∑ i ∈ Icc 1 (r - 1), h i) ≤ G.shadow.card ∧
      (∀ i ∈ Icc 1 (r - 1), (i + 1) * g i ≤ i * s * h i) ∧
      (∀ i ∈ Icc 1 (r - 1), g i ≤
        (i * (s + 1) - 1).choose (i + 1) *
          (m + 1 - (i + 1) * (s + 1)).choose (r - i - 1)) := by
  classical
  refine ⟨fun i => (layer G («prefix» s) r i).card,
    fun i => (restrictedShadow G («prefix» s) r i).card, ?_, ?_, ?_, ?_⟩
  · apply card_eq_sum_layers
    intro e he
    obtain ⟨i, hi1, hir, hi⟩ := hprefix e he
    exact ⟨i, hi1, hir, by simpa only [inter_prefix] using hi⟩
  · exact sum_card_restrictedShadow_le G («prefix» s) r (prefix_mono s) hG
  · intro i hi
    have hi' := mem_Icc.mp hi
    exact prefix_layer_incidence G hG hroom (by omega)
  · intro i hi
    have hi' := mem_Icc.mp hi
    exact card_prefix_layer_le G hG hroom (by omega)

end Submissions.Erdos1020MatchingFKLayers.Main

namespace Submissions.Erdos1020MatchingFKLayerBound.Main

open Finset

/-- The actual shifted family and its shadow supply every combinatorial
premise of the finite dual. Only the numerical certificate remains explicit. -/
theorem card_le_of_numeric {m r s L C : ℕ} (hr : 2 ≤ r)
    (G : Finset (Finset (Fin m))) (hG : ∀ e ∈ G, e.card = r)
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} G)
    (hfree : ¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G.shadow ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hroom : r * (s + 1) - 1 ≤ m) (hshadow : G.shadow.card ≤ L) (θ : ℚ)
    (hnumeric : 3 * (s : ℚ) * L +
      (∑ i ∈ Icc 1 (r - 1), (((i - 3 : ℕ) : ℚ) / (i : ℚ)) *
        ((i * (s + 1) - 1).choose (i + 1) *
          (m + 1 - (i + 1) * (s + 1)).choose (r - i - 1) : ℕ)) ≤
        4 * (θ * s * C)) :
    (G.card : ℚ) ≤ θ * s * C := by
  have hp (e) (he : e ∈ G) :=
    Submissions.Erdos1020MatchingFKPrefixWitness.Main.exists_shadow_prefix
      hr G e hstable he (hG e he) hfree
  obtain ⟨g, h, hA, hD, hlocal, hcap⟩ :=
    Submissions.Erdos1020MatchingFKLayers.Main.exists_layer_counts G hG hroom hp
  exact Submissions.Erdos1020MatchingFKLayerDual.Main.card_le_of_numeric
    (Icc 1 (r - 1)) s G.card G.shadow.card L C g h
    (fun i => (i * (s + 1) - 1).choose (i + 1) *
      (m + 1 - (i + 1) * (s + 1)).choose (r - i - 1))
    θ (fun _ hi => (mem_Icc.mp hi).1) hA hD hlocal hcap hshadow hnumeric

/-- Apply the layer bound after increasing reindexing of the actual zero-head
family; no order preservation of an arbitrary equivalence is assumed. -/
theorem zero_head_card_le_of_numeric {n m r s L C : ℕ} (hr : 2 ≤ r)
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (hc : Tᶜ.card = m) (hH : ∀ e ∈ H, e.card = r)
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ (H.filter (fun e => e ∩ T = ∅)).shadow ∧ M.card = s + 1 ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hroom : r * (s + 1) - 1 ≤ m)
    (hshadow : (H.filter (fun e => e ∩ T = ∅)).shadow.card ≤ L) (θ : ℚ)
    (hnumeric : 3 * (s : ℚ) * L +
      (∑ i ∈ Icc 1 (r - 1), (((i - 3 : ℕ) : ℚ) / (i : ℚ)) *
        ((i * (s + 1) - 1).choose (i + 1) *
          (m + 1 - (i + 1) * (s + 1)).choose (r - i - 1) : ℕ)) ≤
        4 * (θ * s * C)) :
    ((H.filter (fun e => e ∩ T = ∅)).card : ℚ) ≤ θ * s * C := by
  obtain ⟨G, hGc, hGs, hGu, hGm, hstableG⟩ :=
    Submissions.Erdos1020MatchingOrderedTail.Main.reindex_zero_head
      H T hc hH hstable hfree
  have hb := card_le_of_numeric hr G hGu hstableG hGm hroom
    (by rwa [hGs]) θ hnumeric
  rwa [hGc] at hb

end Submissions.Erdos1020MatchingFKLayerBound.Main

namespace Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main

/-- The tail retains the finite 5/3 guard with its explicit additive cushion. -/
theorem induction_parameters {r s n : ℕ}
    (hr : 4 ≤ r) (hs : 10000000000000000 * r ≤ s)
    (hn : 3 * s + 5 * (r - 1) * s + 30 * r ≤ 3 * n) :
    3 ≤ r - 1 ∧ 10000000000000000 * (r - 1) ≤ s ∧
      3 * s + 5 * ((r - 1) - 1) * s + 30 * (r - 1) ≤ 3 * (n - s - 1) := by
  have hr1 : 3 ≤ r - 1 := by omega
  have hs0 : 40000000000000000 ≤ s := by omega
  have hmul := Nat.mul_le_mul_right s hr1
  have hhead : s + 1 ≤ n := by nlinarith only [hn, hmul, hs0]
  have htail : n - s - 1 + s + 1 = n := by omega
  have hrid : (r - 1) - 1 + 1 = r - 1 := by omega
  have hrfull : r - 1 + 1 = r := by omega
  have hprod := congrArg (fun a : ℕ => a * s) hrid
  refine ⟨hr1, by omega, ?_⟩
  nlinarith only [hn, htail, hprod, hs0, hrfull]

/-- A fixed block count works in every larger ambient set. Natural subtraction
and the lost floor remainder are kept explicit before passing to rational bounds. -/
theorem block_parameters {r s n : ℕ}
    (hr : 3 ≤ r) (hs : 10000000000000000 * r ≤ s)
    (hn : 3 * s + 5 * (r - 1) * s + 30 * r ≤ 3 * n) :
    let t := 5 * s / 3 - 1
    let m := n - s - 1
    let x : ℚ := (t : ℚ) - (s : ℚ) - 1
    s + 1 ≤ n ∧ 0 < t ∧ (r - 1) * t ≤ m ∧
      5 * (r - 1) * s ≤ 3 * (m + 1) ∧
      2 * (r - 1) ^ 2 + 2 * (r - 1) ≤ m ∧
      5 * (s : ℚ) / 3 - 2 ≤ (t : ℚ) ∧
      (t : ℚ) ≤ 5 * (s : ℚ) / 3 - 1 ∧
      2 * (s : ℚ) / 3 - 3 ≤ x ∧ x ≤ 2 * (s : ℚ) / 3 ∧
      0 ≤ x ∧ x ≤ (s : ℚ) ∧ (t : ℚ) = (s : ℚ) + x + 1 := by
  dsimp only
  have hr1 : 2 ≤ r - 1 := by omega
  have hs0 : 30000000000000000 ≤ s := by omega
  have hmul := Nat.mul_le_mul_right s hr1
  have hhead : s + 1 ≤ n := by nlinarith only [hn, hmul, hs0]
  have hm : n - s - 1 + s + 1 = n := by omega
  have htail : 5 * (r - 1) * s ≤ 3 * (n - s - 1 + 1) := by
    nlinarith only [hn, hm]
  have hfloorL : 5 * s ≤ 3 * (5 * s / 3 - 1) + 6 := by omega
  have hfloorU : 3 * (5 * s / 3 - 1 + 1) ≤ 5 * s := by omega
  have hfloorScaled := Nat.mul_le_mul_left (r - 1) hfloorU
  have hblocks : (r - 1) * (5 * s / 3 - 1) ≤ n - s - 1 := by
    nlinarith only [hfloorScaled, htail, hr1]
  have hs3 : 3 * (r - 1) ≤ s := by omega
  have hsScaled := Nat.mul_le_mul_left (r - 1) hs3
  have hsq := Nat.mul_le_mul_left (r - 1) hr1
  have hmoment : 2 * (r - 1) ^ 2 + 2 * (r - 1) ≤ n - s - 1 := by
    nlinarith only [hsScaled, hsq, htail, hr1]
  have hsQ : (30000000000000000 : ℚ) ≤ s := (Nat.cast_le (α := ℚ)).mpr hs0
  have hfloorLQ := (Nat.cast_le (α := ℚ)).mpr hfloorL
  have hfloorUQ := (Nat.cast_le (α := ℚ)).mpr hfloorU
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfloorLQ hfloorUQ
  refine ⟨hhead, by omega, hblocks, htail, hmoment, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith only [hsQ, hfloorLQ, hfloorUQ]

/-- The tail ambient bound also leaves room for every layer prefix. -/
theorem layer_room {r s m : ℕ} (hr : 3 ≤ r) (hs : 3 * r ≤ s)
    (htail : 5 * (r - 1) * s ≤ 3 * (m + 1)) :
    r * (s + 1) - 1 ≤ m := by
  have hr1 : 2 ≤ r - 1 := by omega
  have hmul := Nat.mul_le_mul_right s hr1
  have hrid : r - 1 + 1 = r := by omega
  have hprod := congrArg (fun a : ℕ => a * s) hrid
  have hpre : r * (s + 1) ≤ m + 1 := by
    nlinarith only [htail, hmul, hprod, hs]
  omega

/-- The additive ambient cushion permits the checked Refined rank-three base. -/
theorem rank_three_base {n s : ℕ} (hs : 100 ≤ s)
    (hn : 3 * s + 5 * (3 - 1) * s + 30 * 3 ≤ 3 * n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = 3)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose 3 - (n - s).choose 3 := by
  let u := 5 * (s + 1) / 3
  have hw : 3 * (s + 1) + (3 - 1) * s ≤ 3 * u := by dsimp only [u]; omega
  have hu : 3 * u ≤ 5 * (s + 1) := by dsimp only [u]; omega
  have hc : (3 - 1) * u + s + 1 ≤ n := by nlinarith only [hn, hu, hs]
  exact Submissions.Erdos1020MatchingRefined.Main.star_bound (by decide) hw hc H hH hM

/-- The density margin and second-moment separation budget follow from explicit rational
bounds; the density may be zero. -/
theorem margin_and_budget {ell s : ℕ} (hell : 1 ≤ ell)
    (hs : 10000000000000000 * ell ≤ s) {α t x q : ℚ}
    (hα : 0 ≤ α) (ht0 : 0 ≤ t) (ht : t ≤ 5 * (s : ℚ) / 3)
    (hx : 2 * (s : ℚ) / 3 - 3 ≤ x) (hq1 : 1 ≤ q) (hqs : q ≤ (s : ℚ) + 1)
    (hqa : q * α ≤ 1 + 333 * (s : ℚ) / 833) :
    α * t + 2 * ((s : ℚ) / 100000) ≤ (s : ℚ) * x / q ∧
      3 * (3 * (ell : ℚ)) * (s : ℚ) * ((s : ℚ) + 1) ≤
        2 * ((s : ℚ) / 100000) ^ 3 := by
  have hL : (1 : ℚ) ≤ ell := by exact_mod_cast hell
  have hsQ : 10000000000000000 * (ell : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
  have hs1 : (1 : ℚ) ≤ s := by linarith only [hL, hsQ]
  have hs0 : (0 : ℚ) ≤ s := by linarith only [hs1]
  have hq0 : 0 < q := by linarith only [hq1]
  have hB0 : 0 ≤ 1 + 333 * (s : ℚ) / 833 := (mul_nonneg hq0.le hα).trans hqa
  have hproduct : q * α * t ≤ (1 + 333 * (s : ℚ) / 833) * (5 * (s : ℚ) / 3) :=
    mul_le_mul hqa ht ht0 hB0
  have hxl := mul_le_mul_of_nonneg_left hx hs0
  have hqmargin := mul_le_mul_of_nonneg_right hqs
    (show 0 ≤ 2 * ((s : ℚ) / 100000) from
      mul_nonneg (by norm_num) (div_nonneg hs0 (by norm_num)))
  have h20000 : (20000 : ℚ) ≤ s := by linarith only [hL, hsQ]
  have hres : 0 ≤ (s : ℚ) * ((s : ℚ) - 20000) :=
    mul_nonneg hs0 (sub_nonneg.mpr h20000)
  refine ⟨?_, ?_⟩
  · apply (le_div_iff₀ hq0).mpr
    nlinarith only [hproduct, hxl, hqmargin, hres]
  · have h9000 : 9000000000000000 * (ell : ℚ) ≤ (s : ℚ) := by linarith only [hL, hsQ]
    have hdouble : (s : ℚ) + 1 ≤ 2 * (s : ℚ) := by linarith only [hs1]
    have hb1 := mul_le_mul_of_nonneg_left hdouble
      (show 0 ≤ 4500000000000000 * (ell : ℚ) from mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    have hb2 := mul_le_mul_of_nonneg_right h9000 hs0
    have hb : 4500000000000000 * (ell : ℚ) * ((s : ℚ) + 1) ≤ (s : ℚ) ^ 2 := by
      nlinarith only [hb1, hb2]
    have hbscaled := mul_le_mul_of_nonneg_right hb hs0
    nlinarith only [hbscaled]

end Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main

namespace Submissions.Erdos1020MatchingFKLayerCapacity.Main

open Finset

/-- The elementary upper bound retains the factorial denominator. -/
theorem choose_le_pow_div (n d : ℕ) :
    (n.choose d : ℚ) ≤ (n : ℚ) ^ d / (d.factorial : ℚ) := by
  have hf : (0 : ℚ) < d.factorial := Nat.cast_pos.mpr d.factorial_pos
  apply (le_div_iff₀ hf).mpr
  have h := Nat.descFactorial_le_pow n d
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hQ : (d.factorial : ℚ) * (n.choose d : ℚ) ≤ (n : ℚ) ^ d := by
    exact_mod_cast h
  simpa only [mul_comm] using hQ

/-- Exact denominator, including d=0 and d>n. -/
theorem factorial_mul_choose (n d : ℕ) :
    (d.factorial : ℚ) * (n.choose d : ℚ) =
      ∏ j ∈ range d, ((n : ℚ) - j) := by
  rw [prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

theorem normalized_choose {m : ℕ} (hm : 0 < m) (ell : ℕ) :
    (ell.factorial : ℚ) * (m.choose ell : ℚ) / (m : ℚ) ^ ell =
      ∏ j ∈ range ell, (1 - (j : ℚ) / m) := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [factorial_mul_choose]
  calc
    _ = (∏ j ∈ range ell, ((m : ℚ) - j)) /
        (∏ _j ∈ range ell, (m : ℚ)) := by simp
    _ = ∏ j ∈ range ell, (((m : ℚ) - j) / m) := (prod_div_distrib ..).symm
    _ = _ := by
      apply prod_congr rfl
      intro j _
      field_simp [hm0]

/-- The exact arithmetic-series value, expressed without natural subtraction. -/
theorem sum_range_rat (ell : ℕ) :
    (∑ j ∈ range ell, (j : ℚ)) = (ell : ℚ) * ((ell : ℚ) - 1) / 2 := by
  induction ell with
  | zero => norm_num
  | succ ell ih =>
    rw [sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem normalized_choose_lower {m ell : ℕ} (hm : 0 < m) (hell : ell ≤ m) :
    1 - (ell : ℚ) * ((ell : ℚ) - 1) / (2 * (m : ℚ)) ≤
      (ell.factorial : ℚ) * (m.choose ell : ℚ) / (m : ℚ) ^ ell := by
  have hmQ : (0 : ℚ) < m := Nat.cast_pos.mpr hm
  rw [normalized_choose hm]
  have h := Submissions.Erdos1020MatchingBinomialProduct.Main.one_sub_sum_le_prod
    (range ell) (fun j => (j : ℚ) / m)
    (fun j _ => div_nonneg (Nat.cast_nonneg _) hmQ.le)
    (fun j hj => (div_le_iff₀ hmQ).mpr (by
      simpa only [one_mul] using
        (Nat.cast_le (α := ℚ)).mpr (le_trans (Nat.le_of_lt (mem_range.mp hj)) hell)))
  rw [show (∑ j ∈ range ell, (j : ℚ) / m) =
      (ell : ℚ) * ((ell : ℚ) - 1) / (2 * (m : ℚ)) by
    simp only [div_eq_mul_inv, ← sum_mul, sum_range_rat]
    ring] at h
  exact h

/-- A finite geometric upper estimate with no infinite-series machinery. -/
theorem power_geometric (d : ℕ) {u : ℚ} (hu : 0 ≤ u) (hdu : (d : ℚ) * u < 1) :
    (1 + u) ^ d ≤ 1 / (1 - (d : ℚ) * u) := by
  have h : ∀ j : ℕ, (1 - (j : ℚ) * u) * (1 + u) ^ j ≤ 1 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have hp : 0 ≤ ((j : ℚ) + 1) * u ^ 2 * (1 + u) ^ j :=
        mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
          (pow_nonneg (by linarith only [hu]) _)
      have heq : (1 - (((j + 1 : ℕ) : ℚ)) * u) * (1 + u) ^ (j + 1) =
          (1 - (j : ℚ) * u) * (1 + u) ^ j -
            ((j : ℚ) + 1) * u ^ 2 * (1 + u) ^ j := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      linarith only [ih, hp, heq]
  apply (le_div_iff₀ (sub_pos.mpr hdu)).mpr
  simpa only [mul_comm] using h d

/-- The denominator error is uniform once s is at least 1000 times the rank. -/
theorem error_factor {ell s : ℚ} (hell : 4 ≤ ell) (hs : 1000 * ell ≤ s) :
    (1 + 1 / s) / ((1 - 5 * ell / (16 * s)) * (1 - 3 / s) *
      (1 - 2 * ell / s)) < 101 / 100 := by
  have hs4 : 4000 ≤ s := by linarith only [hell, hs]
  have hs0 : 0 < s := by linarith only [hs4]
  have ha : 1 + 1 / s ≤ 4001 / 4000 := by
    have h := (div_le_iff₀ hs0).mpr (show (1 : ℚ) ≤ (1 / 4000) * s by linarith only [hs4])
    linarith only [h]
  have hb : 3199 / 3200 ≤ 1 - 5 * ell / (16 * s) := by
    have h := (div_le_iff₀ (show 0 < 16 * s by positivity)).mpr
      (show 5 * ell ≤ (1 / 3200 : ℚ) * (16 * s) by linarith only [hs])
    linarith only [h]
  have hc : 3997 / 4000 ≤ 1 - 3 / s := by
    have h := (div_le_iff₀ hs0).mpr (show (3 : ℚ) ≤ (3 / 4000) * s by linarith only [hs4])
    linarith only [h]
  have hd : 499 / 500 ≤ 1 - 2 * ell / s := by
    have h := (div_le_iff₀ hs0).mpr (show 2 * ell ≤ (1 / 500 : ℚ) * s by linarith only [hs])
    linarith only [h]
  have hb0 : 0 ≤ 1 - 5 * ell / (16 * s) := by linarith only [hb]
  have hc0 : 0 ≤ 1 - 3 / s := by linarith only [hc]
  have hp := mul_le_mul (mul_le_mul hb hc (by norm_num) hb0) hd
    (by norm_num : (0 : ℚ) ≤ 499 / 500) (mul_nonneg hb0 hc0)
  have hp0 : 0 < (1 - 5 * ell / (16 * s)) * (1 - 3 / s) * (1 - 2 * ell / s) := by
    linarith only [hp]
  apply (div_lt_iff₀ hp0).mpr
  nlinarith only [ha, hp]

end Submissions.Erdos1020MatchingFKLayerCapacity.Main

namespace Submissions.Erdos1020MatchingFKCapacityReduction.Main

/-- The additive cushion already present in the rank induction absorbs all
rounding loss in the ambient capacity estimate. -/
theorem cushion_room {r s n : ℕ} (hr : 3 ≤ r)
    (hn : 3 * s + 5 * (r - 1) * s + 30 * r ≤ 3 * n) :
    5 * (r - 1) * (s + 1) ≤ 3 * (n - s - 1) := by
  have hr1 : 2 ≤ r - 1 := by omega
  have hmul := Nat.mul_le_mul_right s hr1
  have hhead : s + 1 ≤ n := by nlinarith only [hn, hmul, hr]
  have hid : n - s - 1 + s + 1 = n := by omega
  have hrid : r - 1 + 1 = r := by omega
  nlinarith only [hn, hid, hrid]

/-- Uniform positive denominators for every active layer. -/
theorem room_arithmetic {L I S M : ℚ} (hI4 : 4 ≤ I) (hIL : I ≤ L)
    (hS : 1000 * L ≤ S) (hcap : 5 * L * (S + 1) ≤ 3 * M) :
    4000 ≤ S ∧ 0 < L ∧ 0 < M ∧ L + S ≤ M ∧
      0 < M - (I + 1) * (S + 1) ∧
      L * S / 3 ≤ M - (I + 1) * (S + 1) ∧
      3199 / 3200 ≤ 1 - L * (L - 1) / (2 * M) ∧
      (L - I) / (M - (I + 1) * (S + 1)) ≤ 3 / S ∧
      3 / S ≤ 3 / 4000 ∧
      (S + 1) / M ≤ 3 / (5 * L) ∧
      (I + 1) * (3 / (5 * L)) < 1 ∧
      L * (I + 1) * (3 / (5 * L)) ≤ I := by
  have hL4 : 4 ≤ L := hI4.trans hIL
  have hS4 : 4000 ≤ S := by linarith only [hL4, hS]
  have hS0 : 0 < S := by linarith only [hS4]
  have hL0 : 0 < L := by linarith only [hL4]
  have hLS := mul_le_mul_of_nonneg_right hL4 hS0.le
  have hsq := mul_le_mul_of_nonneg_left hS hL0.le
  have hIS := mul_le_mul_of_nonneg_right hIL (show 0 ≤ S + 1 by linarith only [hS4])
  have hM0 : 0 < M := by nlinarith only [hcap, hLS, hL4, hS4]
  have hroom : L + S ≤ M := by nlinarith only [hcap, hLS, hL4, hS4]
  have hb : L * S / 3 ≤ M - (I + 1) * (S + 1) := by
    nlinarith only [hcap, hIS, hLS, hL4, hS4]
  have hb0 : 0 < M - (I + 1) * (S + 1) :=
    lt_of_lt_of_le (div_pos (mul_pos hL0 hS0) (by norm_num)) hb
  have hD : 3199 / 3200 ≤ 1 - L * (L - 1) / (2 * M) := by
    have hquot : L * (L - 1) / (2 * M) ≤ 1 / 3200 := by
      apply (div_le_iff₀ (show 0 < 2 * M by positivity)).mpr
      nlinarith only [hcap, hsq, hLS, hL4]
    linarith only [hquot]
  have hratio : (L - I) / (M - (I + 1) * (S + 1)) ≤ 3 / S := by
    apply (div_le_div_iff₀ hb0 hS0).mpr
    have hiS : 0 ≤ I * S := mul_nonneg (by linarith only [hI4]) hS0.le
    nlinarith only [hb, hiS]
  have hsmall : 3 / S ≤ (3 : ℚ) / 4000 := by
    apply (div_le_iff₀ hS0).mpr
    linarith only [hS4]
  have hx : (S + 1) / M ≤ 3 / (5 * L) := by
    apply (div_le_div_iff₀ hM0 (show 0 < 5 * L by positivity)).mpr
    nlinarith only [hcap]
  have hmode : L * (I + 1) * (3 / (5 * L)) ≤ I := by
    have heq : L * (I + 1) * (3 / (5 * L)) = 3 * (I + 1) / 5 := by
      field_simp [hL0.ne'] <;> ring
    rw [heq]
    linarith only [hI4]
  have hbase : (I + 1) * (3 / (5 * L)) < 1 := by
    rw [show (I + 1) * (3 / (5 * L)) = 3 * (I + 1) / (5 * L) by ring]
    apply (div_lt_iff₀ (show 0 < 5 * L by positivity)).mpr
    linarith only [hIL, hI4]
  exact ⟨hS4, hL0, hM0, hroom, hb0, hb, hD, hratio, hsmall, hx, hbase, hmode⟩

/-- Exact factorial cancellation in the ratio of two layer capacities to the
ambient binomial coefficient. The denominator estimate remains explicit here. -/
theorem two_choose_ratio {a b m ell i : ℕ} (hi : i ≤ ell) (hell : ell ≤ m)
    (hm : 0 < m) {D : ℚ} (hD0 : 0 < D)
    (hD : D ≤ (ell.factorial : ℚ) * (m.choose ell : ℚ) / (m : ℚ) ^ ell) :
    ((a.choose (i + 1) : ℚ) * (b.choose (ell - i) : ℚ)) / (m.choose ell : ℚ) ≤
      (ell.descFactorial i : ℚ) / ((i + 1).factorial : ℚ) *
        (a : ℚ) ^ (i + 1) * (b : ℚ) ^ (ell - i) / ((m : ℚ) ^ ell * D) := by
  have hC : (0 : ℚ) < m.choose ell := Nat.cast_pos.mpr (Nat.choose_pos hell)
  have hmQ : (0 : ℚ) < m := Nat.cast_pos.mpr hm
  have hf1 : (0 : ℚ) < (i + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hfd : (0 : ℚ) < (ell - i).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hmD : 0 < (m : ℚ) ^ ell * D := mul_pos (pow_pos hmQ _) hD0
  have hinv : 1 / (m.choose ell : ℚ) ≤
      (ell.factorial : ℚ) / ((m : ℚ) ^ ell * D) := by
    apply (div_le_div_iff₀ hC hmD).mpr
    have h := (le_div_iff₀ (pow_pos hmQ ell)).mp hD
    nlinarith only [h]
  have ha := Submissions.Erdos1020MatchingFKLayerCapacity.Main.choose_le_pow_div a (i + 1)
  have hb := Submissions.Erdos1020MatchingFKLayerCapacity.Main.choose_le_pow_div b (ell - i)
  have hnum := mul_le_mul ha hb (Nat.cast_nonneg _)
    (div_nonneg (pow_nonneg (Nat.cast_nonneg a) _) hf1.le)
  have hfac : (ell.factorial : ℚ) =
      ((ell - i).factorial : ℚ) * (ell.descFactorial i : ℚ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hi).symm
  calc
    _ = ((a.choose (i + 1) : ℚ) * (b.choose (ell - i) : ℚ)) *
        (1 / (m.choose ell : ℚ)) := by ring
    _ ≤ ((a : ℚ) ^ (i + 1) / ((i + 1).factorial : ℚ) *
        ((b : ℚ) ^ (ell - i) / ((ell - i).factorial : ℚ))) *
        ((ell.factorial : ℚ) / ((m : ℚ) ^ ell * D)) :=
      mul_le_mul hnum hinv (div_nonneg (by norm_num) hC.le)
        (mul_nonneg (div_nonneg (pow_nonneg (Nat.cast_nonneg a) _) hf1.le)
          (div_nonneg (pow_nonneg (Nat.cast_nonneg b) _) hfd.le))
    _ = _ := by
      rw [hfac]
      field_simp [hf1.ne', hfd.ne', hmQ.ne', hD0.ne']

/-- Adding one point to the tail costs this fixed finite factor. -/
theorem tail_power {d : ℕ} {b : ℚ} (hb : 0 < b)
    (hratio : (d : ℚ) / b ≤ 3 / 4000) :
    (b + 1) ^ d ≤ (4000 / 3997 : ℚ) * b ^ d := by
  have hdu : (d : ℚ) * (1 / b) < 1 := by
    rw [mul_one_div]
    linarith only [hratio]
  have hp := Submissions.Erdos1020MatchingFKLayerCapacity.Main.power_geometric d
    (div_nonneg (by norm_num) hb.le) hdu
  have hden : 0 < 1 - (d : ℚ) * (1 / b) := sub_pos.mpr hdu
  have hg : 1 / (1 - (d : ℚ) * (1 / b)) ≤ (4000 / 3997 : ℚ) := by
    apply (div_le_iff₀ hden).mpr
    rw [mul_one_div]
    linarith only [hratio]
  have hmul := mul_le_mul_of_nonneg_right (hp.trans hg) (pow_nonneg hb.le d)
  have heq : (1 + 1 / b) ^ d * b ^ d = (b + 1) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp [hb.ne']
  rwa [heq] at hmul

end Submissions.Erdos1020MatchingFKCapacityReduction.Main

namespace Submissions.Erdos1020MatchingFKBetaMonotone.Main

/-- Monotonicity up to the mode, proved with two finite logarithm inequalities.
The zero base and zero exponent cases are included explicitly. -/
theorem pow_mul_one_sub_pow_le {i ell : ℕ} {x y c : ℝ}
    (hi : i ≤ ell) (hx0 : 0 ≤ x) (hxy : x ≤ y) (hc0 : 0 ≤ c)
    (hcy : c * y < 1) (hmode : (ell : ℝ) * c * y ≤ i) :
    x ^ i * (1 - c * x) ^ (ell - i) ≤
      y ^ i * (1 - c * y) ^ (ell - i) := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  by_cases hy : y = 0
  · have hx : x = 0 := by linarith
    simp only [hy, hx, le_refl]
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  by_cases hi0 : i = 0
  · subst i
    have hz : (ell : ℝ) * c * y = 0 := by
      apply le_antisymm
      · simpa only [Nat.cast_zero] using hmode
      · positivity
    rcases mul_eq_zero.mp hz with hzc | hzy
    · rcases mul_eq_zero.mp hzc with hell | hc
      · have hell0 : ell = 0 := Nat.cast_eq_zero.mp hell
        simp [hell0]
      · simp [hc]
    · exact (hy hzy).elim
  have hbase : 0 < 1 - c * y := by linarith
  by_cases hx : x = 0
  · simp only [hx, zero_pow hi0, zero_mul]
    exact mul_nonneg (pow_nonneg hy0 _) (pow_nonneg hbase.le _)
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hcx : 0 < 1 - c * x := by
    have h := mul_le_mul_of_nonneg_left hxy hc0
    linarith
  have hp := Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
  have hq := Real.log_le_sub_one_of_pos (div_pos hcx hbase)
  have hp' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
  have hq' := mul_le_mul_of_nonneg_left hq
    (Nat.cast_nonneg (ell - i) : (0 : ℝ) ≤ ((ell - i : ℕ) : ℝ))
  have hcast : ((ell - i : ℕ) : ℝ) = (ell : ℝ) - i := Nat.cast_sub hi
  have heq : (i : ℝ) * (x / y - 1) +
      ((ell - i : ℕ) : ℝ) * ((1 - c * x) / (1 - c * y) - 1) =
      (y - x) * ((ell : ℝ) * c * y - i) / (y * (1 - c * y)) := by
    rw [hcast]
    have hbase' : 1 - y * c ≠ 0 := by simpa only [mul_comm] using hbase.ne'
    field_simp [hypos.ne', hbase.ne', hbase']
    ring
  have hrhs : (i : ℝ) * (x / y - 1) +
      ((ell - i : ℕ) : ℝ) * ((1 - c * x) / (1 - c * y) - 1) ≤ 0 := by
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) (sub_nonpos.mpr hmode))
      (mul_nonneg hy0 hbase.le)
  rw [Real.log_div hxpos.ne' hypos.ne'] at hp'
  rw [Real.log_div hcx.ne' hbase.ne'] at hq'
  apply (Real.log_le_log_iff
    (mul_pos (pow_pos hxpos _) (pow_pos hcx _))
    (mul_pos (pow_pos hypos _) (pow_pos hbase _))).mp
  rw [Real.log_mul (pow_pos hxpos _).ne' (pow_pos hcx _).ne',
    Real.log_mul (pow_pos hypos _).ne' (pow_pos hbase _).ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  linarith only [hp', hq', hrhs]

end Submissions.Erdos1020MatchingFKBetaMonotone.Main

namespace Submissions.Erdos1020MatchingFKActualCapacity.Main

private theorem beta_rat {i ell : ℕ} {x y c : ℚ} (hi : i ≤ ell)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hc0 : 0 ≤ c)
    (hcy : c * y < 1) (hmode : (ell : ℚ) * c * y ≤ i) :
    x ^ i * (1 - c * x) ^ (ell - i) ≤ y ^ i * (1 - c * y) ^ (ell - i) := by
  have h := Submissions.Erdos1020MatchingFKBetaMonotone.Main.pow_mul_one_sub_pow_le
    (x := (x : ℝ)) (y := (y : ℝ)) (c := (c : ℝ)) hi
    (by exact_mod_cast hx0) (by exact_mod_cast hxy) (by exact_mod_cast hc0)
    (by exact_mod_cast hcy) (by exact_mod_cast hmode)
  exact_mod_cast h

/-- Each actual finite capacity is bounded by its rank-only beta term.
The stronger room premise is supplied by the existing induction cushion. -/
theorem unweighted_ratio_bound {m s ell i : ℕ} (hi4 : 4 ≤ i) (hi : i ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * (s + 1) ≤ 3 * m) :
    (((i * (s + 1) - 1).choose (i + 1) : ℚ) *
      ((m + 1 - (i + 1) * (s + 1)).choose (ell - i) : ℚ)) /
        ((s : ℚ) * (m.choose ell : ℚ)) ≤
      (101 / 100 : ℚ) * ((ell.descFactorial i : ℚ) / ((i + 1).factorial : ℚ)) *
        (i : ℚ) ^ (i + 1) * (3 / (5 * (ell : ℚ))) ^ i *
          (1 - 3 * ((i : ℚ) + 1) / (5 * (ell : ℚ))) ^ (ell - i) := by
  have hiQ : (4 : ℚ) ≤ i := by exact_mod_cast hi4
  have hiL : (i : ℚ) ≤ ell := by exact_mod_cast hi
  obtain ⟨hs4, hL0, hm0, hroom, hb0, hb, hD, hdb, hsmall, hx, hbase, hmode⟩ :=
    Submissions.Erdos1020MatchingFKCapacityReduction.Main.room_arithmetic
      (S := (s : ℚ)) (M := (m : ℚ)) hiQ hiL
      (by exact_mod_cast hs) (by exact_mod_cast hcap)
  have hs0 : (0 : ℚ) < s := by linarith only [hs4]
  have hmNat : 0 < m := Nat.cast_pos.mp hm0
  have hroomNat : ell + s ≤ m := by exact_mod_cast hroom
  have hellm : ell ≤ m := by omega
  have htailNat : (i + 1) * (s + 1) ≤ m := by
    have h : (((i + 1) * (s + 1) : ℕ) : ℚ) ≤ (m : ℚ) := by
      push_cast
      linarith only [hb0]
    exact_mod_cast h
  let b : ℚ := (m : ℚ) - ((i : ℚ) + 1) * ((s : ℚ) + 1)
  let a : ℕ := i * (s + 1) - 1
  let t : ℕ := m + 1 - (i + 1) * (s + 1)
  let C : ℚ := (ell.descFactorial i : ℚ) / ((i + 1).factorial : ℚ)
  have hbcast : (t : ℚ) = b + 1 := by
    dsimp only [t, b]
    rw [Nat.cast_sub (by omega : (i + 1) * (s + 1) ≤ m + 1)]
    push_cast
    ring
  have hapos : 0 ≤ (a : ℚ) := Nat.cast_nonneg a
  have hap : (a : ℚ) ≤ (i : ℚ) * ((s : ℚ) + 1) := by
    dsimp only [a]
    exact_mod_cast (Nat.sub_le (i * (s + 1)) 1)
  have hhead := pow_le_pow_left₀ hapos hap (i + 1)
  have htail : (t : ℚ) ^ (ell - i) ≤ (4000 / 3997 : ℚ) * b ^ (ell - i) := by
    rw [hbcast]
    apply Submissions.Erdos1020MatchingFKCapacityReduction.Main.tail_power hb0
    rw [Nat.cast_sub hi]
    exact hdb.trans hsmall
  have hC0 : 0 ≤ C := div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)
  have hden := Submissions.Erdos1020MatchingFKLayerCapacity.Main.normalized_choose_lower hmNat hellm
  have hratio := Submissions.Erdos1020MatchingFKCapacityReduction.Main.two_choose_ratio
    (a := a) (b := t) hi hellm hmNat (D := (3199 / 3200 : ℚ)) (by norm_num) (hD.trans hden)
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hhead hC0) htail
    (pow_nonneg (Nat.cast_nonneg t) _) (mul_nonneg hC0 (pow_nonneg (hapos.trans hap) _))
  have hupper : ((a.choose (i + 1) : ℚ) * (t.choose (ell - i) : ℚ)) / (m.choose ell : ℚ) ≤
      C * ((i : ℚ) * ((s : ℚ) + 1)) ^ (i + 1) *
        ((4000 / 3997 : ℚ) * b ^ (ell - i)) / ((m : ℚ) ^ ell * (3199 / 3200)) :=
    hratio.trans (div_le_div_of_nonneg_right hprod
      (mul_nonneg (pow_nonneg hm0.le _) (by norm_num)))
  have hscaled := mul_le_mul_of_nonneg_right hupper (div_nonneg (by norm_num : (0 : ℚ) ≤ 1) hs0.le)
  have hMpow : (m : ℚ) ^ ell = (m : ℚ) ^ i * (m : ℚ) ^ (ell - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  have hform :
      (C * ((i : ℚ) * ((s : ℚ) + 1)) ^ (i + 1) *
        ((4000 / 3997 : ℚ) * b ^ (ell - i)) / ((m : ℚ) ^ ell * (3199 / 3200))) * (1 / s) =
      ((3200 / 3199 : ℚ) * (4000 / 3997)) * (C * (i : ℚ) ^ (i + 1)) *
        (((s : ℚ) + 1) / s) *
          ((((s : ℚ) + 1) / m) ^ i *
            (1 - ((i : ℚ) + 1) * (((s : ℚ) + 1) / m)) ^ (ell - i)) := by
    have hbaseeq : 1 - ((i : ℚ) + 1) * (((s : ℚ) + 1) / m) = b / m := by
      dsimp only [b]
      field_simp [hm0.ne'] <;> ring
    rw [hbaseeq, hMpow]
    simp only [mul_pow, div_pow, pow_succ]
    field_simp [hm0.ne', hs0.ne'] <;> ring
  rw [hform] at hscaled
  have hx0 : 0 ≤ ((s : ℚ) + 1) / m := div_nonneg (by positivity) hm0.le
  have hmono := beta_rat hi hx0 hx (show (0 : ℚ) ≤ (i : ℚ) + 1 by positivity) hbase hmode
  have hfrac : ((s : ℚ) + 1) / s ≤ (4001 / 4000 : ℚ) := by
    apply (div_le_iff₀ hs0).mpr
    linarith only [hs4]
  have hfx0 : 0 ≤ (((s : ℚ) + 1) / m) ^ i *
      (1 - ((i : ℚ) + 1) * (((s : ℚ) + 1) / m)) ^ (ell - i) := by
    apply mul_nonneg (pow_nonneg hx0 _)
    apply pow_nonneg
    have h : ((i : ℚ) + 1) * (((s : ℚ) + 1) / m) ≤
        ((i : ℚ) + 1) * (3 / (5 * (ell : ℚ))) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    linarith only [h, hbase]
  have hmult := mul_le_mul hfrac hmono hfx0 (by norm_num : (0 : ℚ) ≤ 4001 / 4000)
  have hK0 : 0 ≤ C * (i : ℚ) ^ (i + 1) := mul_nonneg hC0 (pow_nonneg (Nat.cast_nonneg _) _)
  have hgamma0 : 0 ≤ ((3200 / 3199 : ℚ) * (4000 / 3997)) * (C * (i : ℚ) ^ (i + 1)) :=
    mul_nonneg (by norm_num) hK0
  have hbound := mul_le_mul_of_nonneg_left hmult hgamma0
  have hFy0 : 0 ≤ (3 / (5 * (ell : ℚ))) ^ i *
      (1 - ((i : ℚ) + 1) * (3 / (5 * (ell : ℚ)))) ^ (ell - i) :=
    mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (sub_nonneg.mpr hbase.le) _)
  have hconst := mul_le_mul_of_nonneg_right
    (show ((3200 / 3199 : ℚ) * (4000 / 3997)) * (4001 / 4000) ≤ 101 / 100 by norm_num)
    (mul_nonneg hK0 hFy0)
  have hfinal := hscaled.trans (by
    calc
      _ = (((3200 / 3199 : ℚ) * (4000 / 3997)) * (C * (i : ℚ) ^ (i + 1))) *
          ((((s : ℚ) + 1) / s) *
            ((((s : ℚ) + 1) / m) ^ i *
              (1 - ((i : ℚ) + 1) * (((s : ℚ) + 1) / m)) ^ (ell - i))) := by ring
      _ ≤ _ := hbound)
  have hbaseeq : ((i : ℚ) + 1) * (3 / (5 * (ell : ℚ))) =
      3 * ((i : ℚ) + 1) / (5 * (ell : ℚ)) := by ring
  dsimp only [a, t] at hfinal
  dsimp only [C] at hconst hfinal
  rw [hbaseeq] at hconst hfinal
  have hres := hfinal.trans (by convert hconst using 1 <;> ring)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm,
    mul_one, one_mul] using hres

end Submissions.Erdos1020MatchingFKActualCapacity.Main

namespace Submissions.Erdos1020MatchingFKLayerTable.Main

open Finset

/-- The common rational layer envelope used by both the analytic estimate and
the exact integer table. Active indices are i=4,...,ell. -/
def phi (ell : ℕ) : ℚ :=
  ∑ j ∈ range (ell - 3),
    let i := j + 4
    (((i - 3 : ℕ) : ℚ) * (i : ℚ) ^ i / ((i + 1).factorial : ℚ)) *
      (∏ a ∈ range i, (1 - (a : ℚ) / ell)) * ((3 : ℚ) / 5) ^ i *
        (1 - 3 * ((i : ℚ) + 1) / (5 * ell)) ^ (ell - i)

/-- Integer numerator of the exact finite layer envelope. The range is empty
at ell=2,3. `fast_choose` has the same kernel-proved value as `Nat.choose`. -/
def numerator (ell : ℕ) : ℕ :=
  ∑ j ∈ range (ell - 3),
    let i := j + 4
    (i - 3) * i ^ i * Nat.fast_choose (ell + 1) (i + 1) * 3 ^ i *
      (5 * ell - 3 * i - 3) ^ (ell - i)

def denominator (ell : ℕ) : ℕ := (ell + 1) * (5 * ell) ^ ell

def densityDenominator (ell : ℕ) : ℕ := (1000 * ell) ^ ell

def densityNumerator (ell : ℕ) : ℕ := (1000 * ell - 601) ^ ell

/-- The additive form of the exact certificate avoids truncated subtraction
when expressing the comparison that each finite row has to establish. -/
def Row (ell : ℕ) : Prop :=
  281 * densityDenominator ell * denominator ell +
      202 * numerator ell * densityDenominator ell ≤
    600 * densityNumerator ell * denominator ell

instance (ell : ℕ) : Decidable (Row ell) := inferInstanceAs (Decidable (_ ≤ _))

theorem numerator_eq_choose (ell : ℕ) : numerator ell =
    ∑ j ∈ range (ell - 3),
      let i := j + 4
      (i - 3) * i ^ i * (ell + 1).choose (i + 1) * 3 ^ i *
        (5 * ell - 3 * i - 3) ^ (ell - i) := by
  simp only [numerator, Nat.fast_choose, ← Nat.choose_eq_descFactorial_div_factorial]

theorem denominator_pos {ell : ℕ} (hell : 2 ≤ ell) : 0 < denominator ell := by
  have hL : 0 < ell := by omega
  unfold denominator
  positivity

theorem density_denominator_pos {ell : ℕ} (hell : 2 ≤ ell) :
    0 < densityDenominator ell := by
  have hL : 0 < ell := by omega
  unfold densityDenominator
  positivity

theorem density_ratio_eq {ell : ℕ} (hell : 2 ≤ ell) :
    (densityNumerator ell : ℚ) / (densityDenominator ell : ℚ) =
      (1 - 601 / (1000 * (ell : ℚ))) ^ ell := by
  have hsub : 601 ≤ 1000 * ell := by omega
  have hL : (0 : ℚ) < ell := Nat.cast_pos.mpr (by omega)
  have hden : (1000 : ℚ) * ell ≠ 0 := by positivity
  simp only [densityNumerator, densityDenominator, Nat.cast_pow,
    Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_ofNat]
  rw [← div_pow]
  congr 1
  field_simp [hden]

/-- Kernel proof of the denominator-clearing step, independent of how a row
is established. This does not assume a density estimate for an actual family. -/
theorem rational_bound_of_row {ell : ℕ} (hell : 2 ≤ ell) (hrow : Row ell) :
    (3 : ℚ) * (1 - (1 - 601 / (1000 * (ell : ℚ))) ^ ell) +
      ((101 : ℚ) / 100) * ((numerator ell : ℚ) / (denominator ell : ℚ)) ≤
        319 / 200 := by
  have hD : (0 : ℚ) < denominator ell := Nat.cast_pos.mpr (denominator_pos hell)
  have hP : (0 : ℚ) < densityDenominator ell :=
    Nat.cast_pos.mpr (density_denominator_pos hell)
  dsimp only [Row] at hrow
  have hrowQ : (281 : ℚ) * densityDenominator ell * denominator ell +
      202 * numerator ell * densityDenominator ell ≤
        600 * densityNumerator ell * denominator ell := by
    exact_mod_cast hrow
  rw [← density_ratio_eq hell]
  apply le_of_mul_le_mul_of_pos_right
    (a := (200 : ℚ) * densityDenominator ell * denominator ell) ?_ (by positivity)
  calc
    (3 * (1 - (densityNumerator ell : ℚ) / densityDenominator ell) +
          (101 / 100) * ((numerator ell : ℚ) / denominator ell)) *
        (200 * densityDenominator ell * denominator ell) =
      600 * densityDenominator ell * denominator ell -
        600 * densityNumerator ell * denominator ell +
          202 * numerator ell * densityDenominator ell := by
            field_simp [hD.ne', hP.ne'] <;> ring
    _ ≤ 319 * densityDenominator ell * denominator ell := by
      linarith only [hrowQ]
    _ = (319 / 200 : ℚ) * (200 * densityDenominator ell * denominator ell) := by ring

end Submissions.Erdos1020MatchingFKLayerTable.Main

namespace Submissions.Erdos1020MatchingFKLayerTable.Main

open Finset

private theorem desc_factorial_product (n d : ℕ) :
    n.descFactorial d = ∏ j ∈ range d, (n - j) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Nat.descFactorial_succ, prod_range_succ_comm, ih]

private theorem normalized_product {ell i : ℕ} (hell : 0 < ell) :
    (∏ a ∈ range i, (1 - (a : ℚ) / ell)) =
      (ell.descFactorial i : ℚ) / (ell : ℚ) ^ i := by
  have hL : (ell : ℚ) ≠ 0 := by exact_mod_cast hell.ne'
  calc
    _ = ∏ a ∈ range i, (((ell : ℚ) - a) / ell) := by
      apply prod_congr rfl
      intro a ha
      field_simp [hL]
    _ = (∏ a ∈ range i, ((ell : ℚ) - a)) / (ell : ℚ) ^ i := by
      rw [prod_div_distrib]
      simp
    _ = _ := by rw [prod_range_natCast_sub, ← desc_factorial_product]

private theorem descending_choose_quotient (ell i : ℕ) :
    (ell.descFactorial i : ℚ) / ((i + 1).factorial : ℚ) =
      ((ell + 1).choose (i + 1) : ℚ) / ((ell : ℚ) + 1) := by
  have hfac : ((i + 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hL : (ell : ℚ) + 1 ≠ 0 := by positivity
  have hnat : (ell + 1) * ell.descFactorial i =
      (i + 1).factorial * (ell + 1).choose (i + 1) := by
    rw [← Nat.succ_descFactorial_succ,
      Nat.descFactorial_eq_factorial_mul_choose]
  have hcast : ((ell : ℚ) + 1) * (ell.descFactorial i : ℚ) =
      ((i + 1).factorial : ℚ) * ((ell + 1).choose (i + 1) : ℚ) := by
    exact_mod_cast hnat
  apply (div_eq_div_iff hfac hL).mpr
  nlinarith only [hcast]

private theorem phi_term_eq {ell i : ℕ} (hi4 : 4 ≤ i) (hi : i ≤ ell) :
    (((i - 3 : ℕ) : ℚ) * (i : ℚ) ^ i / ((i + 1).factorial : ℚ)) *
      (∏ a ∈ range i, (1 - (a : ℚ) / ell)) * ((3 : ℚ) / 5) ^ i *
        (1 - 3 * ((i : ℚ) + 1) / (5 * ell)) ^ (ell - i) =
      (((i - 3) * i ^ i * (ell + 1).choose (i + 1) * 3 ^ i *
        (5 * ell - 3 * i - 3) ^ (ell - i) : ℕ) : ℚ) /
          (denominator ell : ℚ) := by
  have hL : (0 : ℚ) < ell := Nat.cast_pos.mpr (by omega)
  have hLp : (ell : ℚ) + 1 ≠ 0 := by positivity
  have hfac : ((i + 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs1 : 3 * i ≤ 5 * ell := by omega
  have hs2 : 3 ≤ 5 * ell - 3 * i := by omega
  have hcast : ((5 * ell - 3 * i - 3 : ℕ) : ℚ) =
      5 * (ell : ℚ) - 3 * (i : ℚ) - 3 := by
    rw [Nat.cast_sub hs2, Nat.cast_sub hs1]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hbase : 1 - 3 * ((i : ℚ) + 1) / (5 * ell) =
      ((5 * ell - 3 * i - 3 : ℕ) : ℚ) / (5 * ell) := by
    rw [hcast]
    field_simp [hL.ne'] <;> ring
  have hpower : ((5 : ℚ) * ell) ^ ell =
      (5 : ℚ) ^ i * (ell : ℚ) ^ i * ((5 : ℚ) * ell) ^ (ell - i) := by
    calc
      ((5 : ℚ) * ell) ^ ell = ((5 : ℚ) * ell) ^ (i + (ell - i)) := by
        congr 1
        omega
      _ = _ := by rw [pow_add, mul_pow]
  rw [normalized_product (by omega : 0 < ell), hbase]
  calc
    _ = (((i - 3 : ℕ) : ℚ) * (i : ℚ) ^ i * (3 : ℚ) ^ i *
        ((5 * ell - 3 * i - 3 : ℕ) : ℚ) ^ (ell - i) /
          ((5 : ℚ) ^ i * (ell : ℚ) ^ i * ((5 : ℚ) * ell) ^ (ell - i))) *
            ((ell.descFactorial i : ℚ) / ((i + 1).factorial : ℚ)) := by
      rw [div_pow, div_pow]
      field_simp [hL.ne', hfac] <;> ring
    _ = _ := by
      rw [descending_choose_quotient]
      simp only [denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one, Nat.cast_ofNat]
      rw [hpower]
      field_simp [hL.ne', hLp] <;> ring

/-- Exact equality between the analytic product envelope and the integer
numerator/denominator used in the immutable finite certificate. -/
theorem phi_eq_numerator_div {ell : ℕ} (hell : 2 ≤ ell) :
    phi ell = (numerator ell : ℚ) / (denominator ell : ℚ) := by
  rw [phi, numerator_eq_choose, Nat.cast_sum]
  simp_rw [div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  have hji : j + 4 ≤ ell := by have := mem_range.mp hj; omega
  simpa only [div_eq_mul_inv] using phi_term_eq (by omega : 4 ≤ j + 4) hji

theorem phi_bound_of_row {ell : ℕ} (hell : 2 ≤ ell) (hrow : Row ell) :
    (3 : ℚ) * (1 - (1 - 601 / (1000 * (ell : ℚ))) ^ ell) +
      ((101 : ℚ) / 100) * phi ell ≤ 319 / 200 := by
  rw [phi_eq_numerator_div hell]
  exact rational_bound_of_row hell hrow

end Submissions.Erdos1020MatchingFKLayerTable.Main

namespace Submissions.Erdos1020MatchingFKLayerTable.Main

/-- Isolated kernel-reduction entry point for all 798 exact rows. This source
has not been compiled; its bounded runtime is a separate verification question. -/
theorem finite_rows_checked : ∀ j : Fin 798, Row (j.val + 2) := by
  decide +kernel

theorem finite_row {ell : ℕ} (hell : 2 ≤ ell) (hell800 : ell < 800) : Row ell := by
  have h := finite_rows_checked ⟨ell - 2, by omega⟩
  simpa only [Nat.sub_add_cancel hell] using h

theorem finite_rational_bound {ell : ℕ} (hell : 2 ≤ ell) (hell800 : ell < 800) :
    (3 : ℚ) * (1 - (1 - 601 / (1000 * (ell : ℚ))) ^ ell) +
      ((101 : ℚ) / 100) * ((numerator ell : ℚ) / (denominator ell : ℚ)) ≤
        319 / 200 :=
  rational_bound_of_row hell (finite_row hell hell800)

end Submissions.Erdos1020MatchingFKLayerTable.Main

namespace Submissions.Erdos1020MatchingFKLayerDensity.Main

open Finset
open Submissions.Erdos1020MatchingBinomialProduct.Main

/-- Exact exponential constant used in the rational layer envelope. -/
theorem exp_neg_three_fifths_le : Real.exp (-(3 : ℝ) / 5) ≤ 549 / 1000 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ) / 5) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hi := one_div_le_one_div_of_le
    (show (0 : ℝ) < 56939 / 31250 by norm_num) h
  calc
    Real.exp (-(3 : ℝ) / 5) = 1 / Real.exp ((3 : ℝ) / 5) := by
      rw [show -(3 : ℝ) / 5 = -((3 : ℝ) / 5) by ring, Real.exp_neg]
      simp only [one_div]
    _ ≤ 1 / (56939 / 31250 : ℝ) := hi
    _ ≤ 549 / 1000 := by norm_num

/-- A slightly coarse library Taylor remainder suffices for this fixed bound. -/
theorem exp_301_fivehundred_le : Real.exp ((301 : ℝ) / 500) ≤ 1000 / 547 := by
  calc
    Real.exp ((301 : ℝ) / 500) ≤
        (∑ j ∈ range 5, ((301 : ℝ) / 500) ^ j / j.factorial) +
          ((301 : ℝ) / 500) ^ 5 * (5 + 1) / ((5 : ℕ).factorial * 5) :=
      Real.exp_bound' (by norm_num) (by norm_num) (by decide)
    _ ≤ 1000 / 547 := by norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_neg_301_fivehundred_ge : (547 : ℝ) / 1000 ≤
    Real.exp (-(301 : ℝ) / 500) := by
  calc
    (547 : ℝ) / 1000 = 1 / (1000 / 547 : ℝ) := by norm_num
    _ ≤ 1 / Real.exp ((301 : ℝ) / 500) :=
      one_div_le_one_div_of_le (Real.exp_pos _) exp_301_fivehundred_le
    _ = Real.exp (-(301 : ℝ) / 500) := by
      rw [show -(301 : ℝ) / 500 = -((301 : ℝ) / 500) by ring, Real.exp_neg]
      simp only [one_div]

/-- The lower reciprocal bound for log is enough at the fixed large-rank cutoff. -/
theorem power_lower_real {ell : ℕ} (hell : 800 ≤ ell) :
    (547 : ℝ) / 1000 ≤ (1 - 601 / (1000 * (ell : ℝ))) ^ ell := by
  let L : ℝ := ell
  let rho : ℝ := 1 - 601 / (1000 * L)
  have hL800 : (800 : ℝ) ≤ L := by dsimp only [L]; exact_mod_cast hell
  have hL : 0 < L := by linarith
  have hden : 0 < 1000 * L := mul_pos (by norm_num) hL
  have hsmall : 601 / (1000 * L) ≤ (1 : ℝ) / 602 := by
    apply (div_le_div_iff₀ hden (by norm_num)).mpr
    nlinarith only [hL800]
  have hrho : 0 < rho := by dsimp only [rho]; linarith only [hsmall]
  have hlog := Real.one_sub_inv_le_log_of_pos hrho
  have hscale := mul_le_mul_of_nonneg_left hlog hL.le
  have hid : L * (rho - 1) = -(601 : ℝ) / 1000 := by
    dsimp only [rho]
    field_simp [hL.ne'] <;> ring
  have hlo : -(301 : ℝ) / 500 ≤ L * (1 - rho⁻¹) := by
    have heq : L * (1 - rho⁻¹) = (L * (rho - 1)) / rho := by
      field_simp [hrho.ne']
    rw [heq]
    apply (le_div_iff₀ hrho).mpr
    rw [hid]
    dsimp only [rho]
    nlinarith only [hsmall]
  have he := Real.exp_le_exp.mpr (hlo.trans hscale)
  have hpow : Real.exp (L * Real.log rho) = rho ^ ell := by
    dsimp only [L]
    rw [Real.exp_nat_mul, Real.exp_log hrho]
  rw [hpow] at he
  have hfinal := exp_neg_301_fivehundred_ge.trans he
  simpa only [rho, L] using hfinal

theorem power_lower {ell : ℕ} (hell : 800 ≤ ell) :
    (547 : ℚ) / 1000 ≤ (1 - 601 / (1000 * (ell : ℚ))) ^ ell := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_one, Rat.cast_mul, Rat.cast_natCast] using power_lower_real hell

/-- Actual rounded room, with no symbolic shadow-density premise. -/
theorem choose_ratio_lower {m s ell : ℕ} (hell : 2 ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * s ≤ 3 * (m + 1)) :
    (1 - 601 / (1000 * (ell : ℚ))) ^ ell ≤
      ((m - s).choose ell : ℚ) / (m.choose ell : ℚ) := by
  have hs1000 : 1000 ≤ s := by omega
  have hls : 1000 * ell ≤ ell * s := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left ell hs1000
  have hsl : s ≤ ell * s := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right s (show 1 ≤ ell by omega)
  have hroom : ell + s ≤ m := by nlinarith only [hcap, hls, hsl, hell]
  have hL : (0 : ℚ) < ell := Nat.cast_pos.mpr (by omega)
  have hL2 : (2 : ℚ) ≤ ell := by exact_mod_cast hell
  have hcapQ : 5 * (ell : ℚ) * s ≤ 3 * ((m : ℚ) + 1) := by exact_mod_cast hcap
  have hlsQ : 1000 * (ell : ℚ) ≤ (ell : ℚ) * s := by exact_mod_cast hls
  let rho : ℚ := 1 - 601 / (1000 * (ell : ℚ))
  have hrho : 0 ≤ rho := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
    nlinarith only [hL2]
  have hfactor (j : ℕ) (hj : j ∈ range ell) :
      rho ≤ 1 - (s : ℚ) / ((m : ℚ) - j) := by
    have hjl : j + 1 ≤ ell := mem_range.mp hj
    have hjQ : (j : ℚ) + 1 ≤ ell := by exact_mod_cast hjl
    have hjm : j < m := by omega
    have hden : 0 < (m : ℚ) - j := sub_pos.mpr (Nat.cast_lt.mpr hjm)
    have hdiv : (s : ℚ) / ((m : ℚ) - j) ≤ 601 / (1000 * (ell : ℚ)) := by
      apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hL)).mpr
      nlinarith only [hcapQ, hlsQ, hjQ]
    exact sub_le_sub_left hdiv 1
  rw [choose_ratio_product hroom]
  calc
    rho ^ ell = ∏ _j ∈ range ell, rho := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => hrho) hfactor

/-- Large-rank shadow comparison in natural arithmetic. -/
theorem choose_density {m s ell : ℕ} (hell : 800 ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * s ≤ 3 * (m + 1)) :
    547 * m.choose ell ≤ 1000 * (m - s).choose ell := by
  have hr := choose_ratio_lower (by omega : 2 ≤ ell) hs hcap
  have hh := (power_lower hell).trans hr
  have hls : ell ≤ ell * s := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left ell (show 1 ≤ s by omega)
  have hm : ell ≤ m := by nlinarith only [hell, hls, hcap]
  have hC : (0 : ℚ) < m.choose ell := Nat.cast_pos.mpr (Nat.choose_pos hm)
  have hscaled := (le_div_iff₀ hC).mp hh
  apply (Nat.cast_le (α := ℚ)).mp
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hscaled]

end Submissions.Erdos1020MatchingFKLayerDensity.Main

namespace Submissions.Erdos1020MatchingFKLayerRational.Main

open Finset

/-- The exact rational majorant from the finite layer certificate. -/
def envelope (i : ℕ) : ℚ :=
  ((i - 3 : ℕ) : ℚ) * (i : ℚ) ^ i / ((i + 1).factorial : ℚ) *
    ((3 : ℚ) / 5) ^ i * ((549 : ℚ) / 1000) ^ (i + 1)

theorem envelope_nonneg (i : ℕ) : 0 ≤ envelope i := by
  unfold envelope
  positivity

/-- The library's finite Taylor remainder already gives the required constant. -/
theorem exp_one_le : Real.exp 1 ≤ (68 : ℝ) / 25 := by
  calc
    Real.exp 1 ≤ (∑ j ∈ range 6, (1 : ℝ) ^ j / j.factorial) +
        (1 : ℝ) ^ 6 * (6 + 1) / ((6 : ℕ).factorial * 6) :=
      Real.exp_bound' (by norm_num) (by norm_num) (by decide)
    _ ≤ (68 : ℝ) / 25 := by norm_num [Finset.sum_range_succ, Nat.factorial]

theorem one_add_inv_pow_le {i : ℕ} (hi : 1 ≤ i) :
    (1 + 1 / (i : ℚ)) ^ i ≤ (68 : ℚ) / 25 := by
  have hI : (0 : ℝ) < i := Nat.cast_pos.mpr (by omega)
  have hbase : 1 + 1 / (i : ℝ) ≤ Real.exp (1 / (i : ℝ)) := by
    simpa only [add_comm] using Real.add_one_le_exp (1 / (i : ℝ))
  have hp := pow_le_pow_left₀
    (show (0 : ℝ) ≤ 1 + 1 / (i : ℝ) by positivity) hbase i
  have he : Real.exp (1 / (i : ℝ)) ^ i = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [hI.ne']
  rw [he] at hp
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat] using hp.trans exp_one_le

theorem envelope_succ_le {i : ℕ} (hi : 40 ≤ i) :
    envelope (i + 1) ≤ (9 : ℚ) / 10 * envelope i := by
  have hI40 : (40 : ℚ) ≤ i := by exact_mod_cast hi
  have hI : (0 : ℚ) < i := by linarith
  have hI3 : (0 : ℚ) < (i : ℚ) - 3 := by linarith
  have hI2 : (0 : ℚ) < (i : ℚ) + 2 := by linarith
  have hfac : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  let A : ℚ := ((i : ℚ) - 2) / ((i : ℚ) - 3) *
    (((i : ℚ) + 1) / ((i : ℚ) + 2))
  have hA : A ≤ (779 : ℚ) / 777 := by
    dsimp only [A]
    rw [div_mul_div_comm]
    apply (div_le_iff₀ (mul_pos hI3 hI2)).mpr
    have hsq : 0 ≤ ((i : ℚ) - 40) ^ 2 := sq_nonneg _
    nlinarith only [hI40, hsq]
  have heq : envelope (i + 1) =
      (A * (1 + 1 / (i : ℚ)) ^ i * ((3 : ℚ) / 5) *
        ((549 : ℚ) / 1000)) * envelope i := by
    have hbase : 1 + 1 / (i : ℚ) = ((i : ℚ) + 1) / (i : ℚ) := by
      field_simp [hI.ne']
    rw [hbase, div_pow]
    simp only [envelope, A, Nat.cast_sub (show 3 ≤ i by omega),
      Nat.cast_sub (show 3 ≤ i + 1 by omega), Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp [hI.ne', hI3.ne', hI2.ne', hfac] <;> ring
  have hpow := one_add_inv_pow_le (show 1 ≤ i by omega)
  have hAP := mul_le_mul hA hpow
    (show (0 : ℚ) ≤ (1 + 1 / (i : ℚ)) ^ i by positivity)
    (show (0 : ℚ) ≤ 779 / 777 by norm_num)
  have hc : A * (1 + 1 / (i : ℚ)) ^ i * ((3 : ℚ) / 5) *
      ((549 : ℚ) / 1000) ≤ (9 : ℚ) / 10 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAP (show (0 : ℚ) ≤ 3 / 5 by norm_num))
      (show (0 : ℚ) ≤ 549 / 1000 by norm_num)
    norm_num at h ⊢
    linarith only [h]
  rw [heq]
  exact mul_le_mul_of_nonneg_right hc (envelope_nonneg i)

/-- A finite geometric tail potential avoids any infinite-series dependency. -/
theorem tail_potential {a : ℕ} (ha : 40 ≤ a) (n : ℕ) :
    (∑ j ∈ range n, envelope (a + j)) + 10 * envelope (a + n) ≤
      10 * envelope a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.add_succ]
    have hstep := envelope_succ_le (i := a + n) (by omega)
    linarith only [ih, hstep]

theorem tail_sum_le {a : ℕ} (ha : 40 ≤ a) (n : ℕ) :
    (∑ j ∈ range n, envelope (a + j)) ≤ 10 * envelope a := by
  have hp := tail_potential ha n
  have hn := envelope_nonneg (a + n)
  linarith only [hp, hn]

theorem prefix_constant :
    (∑ j ∈ range 37, envelope (4 + j)) + 10 * envelope 41 ≤ (7 : ℚ) / 30 := by
  norm_num [envelope, Finset.sum_range_succ, Nat.factorial]

theorem envelope_41_le : envelope 41 ≤ (1 : ℚ) / 3000 := by
  norm_num [envelope, Nat.factorial]

theorem envelope_81_le : envelope 81 ≤ (1 : ℚ) / 100000 := by
  norm_num [envelope, Nat.factorial]

theorem envelope_sum_le (n : ℕ) :
    (∑ j ∈ range n, envelope (4 + j)) ≤ (7 : ℚ) / 30 := by
  by_cases hn : n ≤ 37
  · have hmono : (∑ j ∈ range n, envelope (4 + j)) ≤
        ∑ j ∈ range 37, envelope (4 + j) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hn)
        (fun j _ _ => envelope_nonneg (4 + j))
    have hnonneg := envelope_nonneg 41
    linarith only [hmono, prefix_constant, hnonneg]
  · have hsplit : n = 37 + (n - 37) := by omega
    rw [hsplit, sum_range_add]
    have ht := tail_sum_le (a := 41) (by omega) (n - 37)
    have ht' : (∑ j ∈ range (n - 37), envelope (4 + (37 + j))) ≤
        10 * envelope 41 := by simpa only [← Nat.add_assoc] using ht
    linarith only [ht', prefix_constant]

theorem tail_41_le (n : ℕ) :
    (∑ j ∈ range n, envelope (41 + j)) ≤ (1 : ℚ) / 300 := by
  have h := tail_sum_le (a := 41) (by omega) n
  linarith only [h, envelope_41_le]

theorem tail_81_le (n : ℕ) :
    (∑ j ∈ range n, envelope (81 + j)) ≤ (1 : ℚ) / 10000 := by
  have h := tail_sum_le (a := 81) (by omega) n
  linarith only [h, envelope_81_le]

theorem bulk_tail_constant :
    (320 : ℚ) / 319 * (7 / 30) + 4 / 10000 < 235 / 1000 := by norm_num

theorem large_dual_constant :
    (3 : ℚ) * (1 - 547 / 1000) + (101 / 100) * (235 / 1000) =
      31927 / 20000 := by norm_num

theorem finite_dual_constant : (319 : ℚ) / 200 ≤ 31927 / 20000 := by norm_num

theorem strict_dual_constant : (31927 : ℚ) / 20000 < 1332 / 833 := by norm_num

/-- The exponential envelope is bounded by the same fixed rational sequence.
The exact exponential constant is supplied by the separate density body. -/
theorem exponential_term_le_envelope (i : ℕ) :
    ((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i / ((i + 1).factorial : ℝ) *
      ((3 : ℝ) / 5) ^ i * Real.exp (-(3 * ((i : ℝ) + 1) / 5)) ≤
        (envelope i : ℝ) := by
  have hpow := pow_le_pow_left₀ (Real.exp_pos (-(3 : ℝ) / 5)).le
    Submissions.Erdos1020MatchingFKLayerDensity.Main.exp_neg_three_fifths_le (i + 1)
  have heq : Real.exp (-(3 * ((i : ℝ) + 1) / 5)) =
      Real.exp (-(3 : ℝ) / 5) ^ (i + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hpow
    (show (0 : ℝ) ≤ ((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i /
      ((i + 1).factorial : ℝ) * ((3 : ℝ) / 5) ^ i by positivity)
  simpa only [envelope, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] using h

end Submissions.Erdos1020MatchingFKLayerRational.Main

namespace Submissions.Erdos1020MatchingFKCapacityEnvelope.Main

open Finset

/-- A quadratic upper bound obtained from the rational lower bound for log(1+u). -/
theorem log_one_sub_le_quadratic {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  have hpos : 0 < 1 - x := by linarith
  have hden : 0 < 2 - x := by linarith
  have hu := Real.le_log_one_add_of_nonneg (div_nonneg hx hpos.le)
  have heq : 1 + x / (1 - x) = (1 - x)⁻¹ := by
    field_simp [hpos.ne']
    ring
  have hfrac : 2 * (x / (1 - x)) / (x / (1 - x) + 2) =
      2 * x / (2 - x) := by
    field_simp [hpos.ne', hden.ne']
    ring
  rw [heq, Real.log_inv, hfrac] at hu
  have hrat : x + x ^ 2 / 2 ≤ 2 * x / (2 - x) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [mul_nonneg hx (sq_nonneg x)]
  linarith only [hu, hrat]

/-- A finite telescoping substitute for the decreasing-log sum/integral bound.
The final term is at n<L, including n=L-1 when L is a positive integer. -/
theorem sum_log_le_entropy (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : (n : ℝ) < L) :
    (∑ j ∈ range (n + 1), Real.log (1 - (j : ℝ) / L)) ≤
      -(L - n) * Real.log (1 - (n : ℝ) / L) - n := by
  revert hn
  induction n with
  | zero => intro hn; simp
  | succ n ih =>
    intro hn
    have hn' : (n : ℝ) + 1 < L := by exact_mod_cast hn
    have hn0 : (n : ℝ) < L := by linarith
    have hp : 0 < L - n := by linarith
    have hq : 0 < L - ((n : ℝ) + 1) := by linarith
    have hprev : 0 < 1 - (n : ℝ) / L := by
      rw [sub_pos, div_lt_one hL]
      exact hn0
    have hnext : 0 < 1 - ((n : ℝ) + 1) / L := by
      rw [sub_pos, div_lt_one hL]
      exact hn'
    have heq : (L - n) / (L - ((n : ℝ) + 1)) =
        (1 - (n : ℝ) / L) / (1 - ((n : ℝ) + 1) / L) := by
      field_simp [hL.ne', hq.ne']
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hp hq)
    have hscale := mul_le_mul_of_nonneg_left hlog hp.le
    have hcancel : (L - n) * (1 - ((L - n) / (L - ((n : ℝ) + 1)))⁻¹) = 1 := by
      field_simp [hp.ne', hq.ne']
      ring
    rw [hcancel, heq, Real.log_div hprev.ne' hnext.ne'] at hscale
    have hi := ih hn0
    rw [sum_range_succ]
    simp only [Nat.cast_succ] at hi ⊢
    nlinarith only [hi, hscale]

private theorem sum_range_cast (n : ℕ) :
    (∑ j ∈ range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_succ]
    ring

private theorem log_product_eq {ell i : ℕ} {a : ℝ}
    (hi : i ≤ ell) (ha : a < ell) (hell : 0 < ell) :
    Real.log ((∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
      (1 - a / ell) ^ (ell - i)) =
      (∑ j ∈ range i, Real.log (1 - (j : ℝ) / ell)) +
        ((ell : ℝ) - i) * Real.log (1 - a / ell) := by
  have hL : (0 : ℝ) < ell := Nat.cast_pos.mpr hell
  have hp (j : ℕ) (hj : j ∈ range i) : 0 < 1 - (j : ℝ) / ell := by
    rw [sub_pos, div_lt_one hL]
    exact_mod_cast lt_of_lt_of_le (mem_range.mp hj) hi
  have hA : 0 < 1 - a / ell := by
    rw [sub_pos, div_lt_one hL]
    exact ha
  rw [Real.log_mul (prod_pos hp).ne' (pow_pos hA _).ne',
    Real.log_prod (fun j hj => (hp j hj).ne'), Real.log_pow, Nat.cast_sub hi]

/-- The direct finite product envelope, valid even when i=ell. -/
theorem product_le_four_exp {ell i : ℕ} (hi4 : 4 ≤ i) (hi : i ≤ ell) :
    (∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
      (1 - (3 * ((i : ℝ) + 1) / 5) / ell) ^ (ell - i) ≤
        4 * Real.exp (-(3 * ((i : ℝ) + 1) / 5)) := by
  let L : ℝ := ell
  let I : ℝ := i
  let a : ℝ := 3 * (I + 1) / 5
  let b : ℝ := I - 1
  have hi1 : 1 ≤ i := by omega
  have hL : 0 < L := by dsimp [L]; exact_mod_cast (show 0 < ell by omega)
  have hI4 : 4 ≤ I := by dsimp [I]; exact_mod_cast hi4
  have hIL : I ≤ L := by dsimp [I, L]; exact_mod_cast hi
  have hbL : b < L := by dsimp [b]; linarith
  have haL : a < L := by dsimp [a]; linarith
  have hA : 0 < 1 - a / L := by rw [sub_pos, div_lt_one hL]; exact haL
  have hB : 0 < 1 - b / L := by rw [sub_pos, div_lt_one hL]; exact hbL
  have hLb : 0 < L - b := sub_pos.mpr hbL
  have hb : ((i - 1 : ℕ) : ℝ) = b := by
    dsimp [b, I]
    rw [Nat.cast_sub hi1, Nat.cast_one]
  have hs := sum_log_le_entropy L hL (i - 1) (by rw [hb]; exact hbL)
  rw [Nat.sub_add_cancel hi1, hb] at hs
  have hc := Real.log_le_sub_one_of_pos (div_pos hA hB)
  have hc' := mul_le_mul_of_nonneg_left hc hLb.le
  have hcancel : (L - b) * ((1 - a / L) / (1 - b / L) - 1) = b - a := by
    field_simp [hL.ne', hLb.ne']
    ring
  rw [Real.log_div hA.ne' hB.ne', hcancel] at hc'
  have hlog :
      Real.log ((∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
        (1 - a / ell) ^ (ell - i)) ≤ -a - Real.log (1 - a / L) := by
    rw [log_product_eq hi haL (by omega)]
    change (∑ j ∈ range i, Real.log (1 - (j : ℝ) / L)) +
      (L - I) * Real.log (1 - a / L) ≤ -a - Real.log (1 - a / L)
    dsimp [b] at hs hc'
    nlinarith only [hs, hc']
  have hquarter : (1 : ℝ) / 4 ≤ 1 - a / L := by
    have ha : a ≤ 3 * L / 4 := by dsimp [a]; linarith
    have hdiv : a / L ≤ (3 : ℝ) / 4 := (div_le_iff₀ hL).mpr (by linarith)
    linarith
  have hbound := Real.le_exp_of_log_le hlog
  rw [Real.exp_sub, Real.exp_log hA] at hbound
  have hratio : Real.exp (-a) / (1 - a / L) ≤ 4 * Real.exp (-a) := by
    apply (div_le_iff₀ hA).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hquarter (Real.exp_nonneg (-a))]
  exact hbound.trans hratio

private theorem bulk_polynomial_bound {L I : ℝ} (hL : 0 < L) (hIL : 10 * I ≤ L) :
    -(I * (I - 1) / (2 * L)) +
      (L - I) * (-(3 * (I + 1) / 5) / L -
        ((3 * (I + 1) / 5) / L) ^ 2 / 2) + 3 * (I + 1) / 5 ≤
          5 / (2 * L) := by
  have hpoly : -31 * I ^ 2 + 388 * I - 81 ≤ 1250 := by
    nlinarith only [sq_nonneg (31 * I - 194)]
  have hpolyL := mul_le_mul_of_nonneg_left hpoly hL.le
  have hsmall := mul_le_mul_of_nonneg_right hIL (sq_nonneg (I + 1))
  have heq : 50 * L ^ 2 *
      (-(I * (I - 1) / (2 * L)) +
        (L - I) * (-(3 * (I + 1) / 5) / L -
          ((3 * (I + 1) / 5) / L) ^ 2 / 2) + 3 * (I + 1) / 5) =
      L * (-4 * I ^ 2 + 37 * I - 9) + 9 * I * (I + 1) ^ 2 := by
    field_simp [hL.ne']
    ring
  have heq' : 50 * L ^ 2 * (5 / (2 * L)) = 125 * L := by
    field_simp [hL.ne']
    ring
  apply le_of_mul_le_mul_of_pos_left (a := 50 * L ^ 2) ?_ (by positivity)
  rw [heq, heq']
  nlinarith only [hpolyL, hsmall]

/-- The sharper bulk envelope has an explicit finite cutoff and no asymptotic term. -/
theorem product_le_bulk_exp {ell i : ℕ} (hi4 : 4 ≤ i)
    (hell : 800 ≤ ell) (hsmall : 10 * i ≤ ell) :
    (∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
      (1 - (3 * ((i : ℝ) + 1) / 5) / ell) ^ (ell - i) ≤
        (320 / 319 : ℝ) * Real.exp (-(3 * ((i : ℝ) + 1) / 5)) := by
  let L : ℝ := ell
  let I : ℝ := i
  let a : ℝ := 3 * (I + 1) / 5
  have hL800 : 800 ≤ L := by dsimp [L]; exact_mod_cast hell
  have hL : 0 < L := by linarith
  have hI4 : 4 ≤ I := by dsimp [I]; exact_mod_cast hi4
  have hIL10 : 10 * I ≤ L := by dsimp [I, L]; exact_mod_cast hsmall
  have hi : i ≤ ell := by omega
  have hIL : I ≤ L := by dsimp [I, L]; exact_mod_cast hi
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have haL : a < L := by dsimp [a]; linarith
  have hA0 : 0 ≤ a / L := div_nonneg ha0 hL.le
  have hA1 : a / L < 1 := (div_lt_one hL).mpr haL
  have hs : (∑ j ∈ range i, Real.log (1 - (j : ℝ) / L)) ≤
      -(I * (I - 1) / (2 * L)) := by
    have hpoint (j : ℕ) (hj : j ∈ range i) :
        Real.log (1 - (j : ℝ) / L) ≤ -(j : ℝ) / L := by
      have hjL : (j : ℝ) < L := by
        dsimp [L]
        exact_mod_cast lt_of_lt_of_le (mem_range.mp hj) hi
      have hp : 0 < 1 - (j : ℝ) / L := by
        rw [sub_pos, div_lt_one hL]
        exact hjL
      calc
        _ ≤ 1 - (j : ℝ) / L - 1 := Real.log_le_sub_one_of_pos hp
        _ = -(j : ℝ) / L := by ring
    have hsum := sum_le_sum hpoint
    have hsumval : (∑ j ∈ range i, -(j : ℝ) / L) =
        -(I * (I - 1) / (2 * L)) := by
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul, sum_neg_distrib, sum_range_cast]
      dsimp [I]
      field_simp [hL.ne']
    rwa [hsumval] at hsum
  have ht := mul_le_mul_of_nonneg_left (log_one_sub_le_quadratic hA0 hA1)
    (sub_nonneg.mpr hIL)
  have hp := bulk_polynomial_bound hL hIL10
  have hlog :
      Real.log ((∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
        (1 - a / ell) ^ (ell - i)) ≤ -a + 5 / (2 * L) := by
    rw [log_product_eq hi haL (by omega)]
    change (∑ j ∈ range i, Real.log (1 - (j : ℝ) / L)) +
      (L - I) * Real.log (1 - a / L) ≤ -a + 5 / (2 * L)
    dsimp [a] at ht ⊢
    simp only [neg_div] at hp
    linarith only [hs, ht, hp]
  have hc : 5 / (2 * L) ≤ (1 : ℝ) / 320 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mpr
    linarith
  have hexp : Real.exp (5 / (2 * L)) ≤ (320 / 319 : ℝ) := by
    have he := Real.exp_le_exp.mpr hc
    have hb := Real.exp_bound_div_one_sub_of_interval
      (x := (1 : ℝ) / 320) (by norm_num) (by norm_num)
    norm_num at hb
    exact he.trans hb
  have hbound := Real.le_exp_of_log_le hlog
  rw [Real.exp_add] at hbound
  exact hbound.trans (by
    simpa only [a, I, mul_comm] using
      mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (-a)))

end Submissions.Erdos1020MatchingFKCapacityEnvelope.Main

namespace Submissions.Erdos1020MatchingFKPhiLarge.Main

open Finset
open Submissions.Erdos1020MatchingFKCapacityEnvelope.Main
open Submissions.Erdos1020MatchingFKLayerRational.Main

/-- The literal summand of the shared rational Phi after casting to the reals. -/
private noncomputable def realTerm (ell i : ℕ) : ℝ :=
  (((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i / ((i + 1).factorial : ℝ)) *
    (∏ a ∈ range i, (1 - (a : ℝ) / ell)) * ((3 : ℝ) / 5) ^ i *
      (1 - 3 * ((i : ℝ) + 1) / (5 * ell)) ^ (ell - i)

private theorem phi_cast (ell : ℕ) :
    (Submissions.Erdos1020MatchingFKLayerTable.Main.phi ell : ℝ) =
      ∑ j ∈ range (ell - 3), realTerm ell (j + 4) := by
  simp only [Submissions.Erdos1020MatchingFKLayerTable.Main.phi, realTerm,
    Rat.cast_sum, Rat.cast_prod, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]

private theorem term_le_of_product {ell i : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hp : (∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
      (1 - (3 * ((i : ℝ) + 1) / 5) / ell) ^ (ell - i) ≤
        c * Real.exp (-(3 * ((i : ℝ) + 1) / 5))) :
    realTerm ell i ≤ c * (envelope i : ℝ) := by
  have hcoef : (0 : ℝ) ≤
      ((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i / ((i + 1).factorial : ℝ) *
        ((3 : ℝ) / 5) ^ i := by positivity
  calc
    realTerm ell i =
        (((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i / ((i + 1).factorial : ℝ) *
          ((3 : ℝ) / 5) ^ i) *
            ((∏ j ∈ range i, (1 - (j : ℝ) / ell)) *
              (1 - (3 * ((i : ℝ) + 1) / 5) / ell) ^ (ell - i)) := by
      simp only [realTerm, div_div]
      ring
    _ ≤ (((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i / ((i + 1).factorial : ℝ) *
          ((3 : ℝ) / 5) ^ i) *
            (c * Real.exp (-(3 * ((i : ℝ) + 1) / 5))) :=
      mul_le_mul_of_nonneg_left hp hcoef
    _ = c * (((i - 3 : ℕ) : ℝ) * (i : ℝ) ^ i / ((i + 1).factorial : ℝ) *
          ((3 : ℝ) / 5) ^ i * Real.exp (-(3 * ((i : ℝ) + 1) / 5))) := by ring
    _ ≤ c * (envelope i : ℝ) :=
      mul_le_mul_of_nonneg_left (exponential_term_le_envelope i) hc

/-- Outside the sharp-product range the index is at least 81. The two
nonnegative majorants may overlap; this only increases their finite sum. -/
private theorem term_le_bulk_add_tail {ell j : ℕ} (hell : 800 ≤ ell)
    (hj : j ∈ range (ell - 3)) :
    realTerm ell (j + 4) ≤
      (320 / 319 : ℝ) * (envelope (j + 4) : ℝ) +
        4 * (if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) := by
  have hi4 : 4 ≤ j + 4 := by omega
  have hi : j + 4 ≤ ell := by have := mem_range.mp hj; omega
  have he : (0 : ℝ) ≤ (envelope (j + 4) : ℝ) := by
    exact_mod_cast envelope_nonneg (j + 4)
  by_cases hsmall : 10 * (j + 4) ≤ ell
  · have hp := term_le_of_product (c := (320 / 319 : ℝ)) (by norm_num)
      (product_le_bulk_exp hi4 hell hsmall)
    have ht : (0 : ℝ) ≤
        4 * (if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) := by
      split_ifs <;> positivity
    exact hp.trans (le_add_of_nonneg_right ht)
  · have hj77 : 77 ≤ j := by omega
    rw [if_pos hj77]
    have hp := term_le_of_product (c := (4 : ℝ)) (by norm_num)
      (product_le_four_exp hi4 hi)
    have hb : (0 : ℝ) ≤ (320 / 319 : ℝ) * (envelope (j + 4) : ℝ) := by
      positivity
    linarith only [hp, hb]

private theorem tail_sum_le {n : ℕ} (hn : 77 ≤ n) :
    (∑ j ∈ range n, if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) ≤
      (1 : ℝ) / 10000 := by
  have hsplit : n = 77 + (n - 77) := by omega
  have hz : (∑ j ∈ range 77,
      if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [if_neg (not_le.mpr (mem_range.mp hj))]
  have heq : (∑ j ∈ range n,
      if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) =
        ∑ j ∈ range (n - 77), (envelope (81 + j) : ℝ) := by
    calc
      _ = (∑ j ∈ range 77,
            if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) +
          ∑ j ∈ range (n - 77),
            if 77 ≤ 77 + j then (envelope ((77 + j) + 4) : ℝ) else 0 := by
        conv_lhs => rw [hsplit]
        exact sum_range_add _ 77 (n - 77)
      _ = _ := by
        rw [hz, zero_add]
        apply sum_congr rfl
        intro j _hj
        rw [if_pos (by omega : 77 ≤ 77 + j)]
        rw [show (77 + j) + 4 = 81 + j by omega]
  rw [heq]
  have h := (Rat.cast_le (K := ℝ)).mpr (tail_81_le (n - 77))
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

/-- The analytic large-rank part of the common finite layer certificate.
This is a numerical bound for the exact rational Phi, with no family premise. -/
theorem phi_le_real {ell : ℕ} (hell : 800 ≤ ell) :
    (Submissions.Erdos1020MatchingFKLayerTable.Main.phi ell : ℝ) ≤
      (235 : ℝ) / 1000 := by
  have hb : (∑ j ∈ range (ell - 3), (envelope (j + 4) : ℝ)) ≤
      (7 : ℝ) / 30 := by
    have h : (∑ j ∈ range (ell - 3), (envelope (4 + j) : ℝ)) ≤
        (7 : ℝ) / 30 := by
      have hh := (Rat.cast_le (K := ℝ)).mpr (envelope_sum_le (ell - 3))
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hh
    simpa only [Nat.add_comm] using h
  have ht := tail_sum_le (n := ell - 3) (by omega)
  have hc : (320 / 319 : ℝ) * (7 / 30) + 4 / 10000 < 235 / 1000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr bulk_tail_constant
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] using h
  calc
    (Submissions.Erdos1020MatchingFKLayerTable.Main.phi ell : ℝ) =
        ∑ j ∈ range (ell - 3), realTerm ell (j + 4) := phi_cast ell
    _ ≤ ∑ j ∈ range (ell - 3),
        ((320 / 319 : ℝ) * (envelope (j + 4) : ℝ) +
          4 * (if 77 ≤ j then (envelope (j + 4) : ℝ) else 0)) :=
      sum_le_sum (fun _ hj => term_le_bulk_add_tail hell hj)
    _ = (320 / 319 : ℝ) * (∑ j ∈ range (ell - 3), (envelope (j + 4) : ℝ)) +
        4 * (∑ j ∈ range (ell - 3),
          if 77 ≤ j then (envelope (j + 4) : ℝ) else 0) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ (320 / 319 : ℝ) * (7 / 30) + 4 * (1 / 10000) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
        (mul_le_mul_of_nonneg_left ht (by norm_num))
    _ ≤ (235 : ℝ) / 1000 := by linarith only [hc]

theorem phi_le {ell : ℕ} (hell : 800 ≤ ell) :
    Submissions.Erdos1020MatchingFKLayerTable.Main.phi ell ≤ (235 : ℚ) / 1000 := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_ofNat] using phi_le_real hell

end Submissions.Erdos1020MatchingFKPhiLarge.Main

namespace Submissions.Erdos1020MatchingFKCapacitySum.Main

open Finset
open Submissions.Erdos1020MatchingFKLayerTable.Main

private theorem product_desc {ell i : ℕ} (hell : 0 < ell) :
    (∏ j ∈ range i, (1 - (j : ℚ) / ell)) =
      (ell.descFactorial i : ℚ) / (ell : ℚ) ^ i := by
  rw [← Submissions.Erdos1020MatchingFKLayerCapacity.Main.normalized_choose hell]
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose]

theorem weighted_ratio_bound {m s ell i : ℕ} (hi4 : 4 ≤ i) (hi : i ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * (s + 1) ≤ 3 * m) :
    (((i - 3 : ℕ) : ℚ) / i * ((i * (s + 1) - 1).choose (i + 1) : ℚ) *
      ((m + 1 - (i + 1) * (s + 1)).choose (ell - i) : ℚ)) /
        ((s : ℚ) * (m.choose ell : ℚ)) ≤
      (101 / 100 : ℚ) *
        ((((i - 3 : ℕ) : ℚ) * (i : ℚ) ^ i / ((i + 1).factorial : ℚ)) *
          (∏ j ∈ range i, (1 - (j : ℚ) / ell)) * ((3 : ℚ) / 5) ^ i *
            (1 - 3 * ((i : ℚ) + 1) / (5 * ell)) ^ (ell - i)) := by
  have hi0 : (0 : ℚ) < i := Nat.cast_pos.mpr (by omega)
  have hL0 : (0 : ℚ) < ell := Nat.cast_pos.mpr (by omega)
  have hfac : ((i + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h := mul_le_mul_of_nonneg_left
    (Submissions.Erdos1020MatchingFKActualCapacity.Main.unweighted_ratio_bound hi4 hi hs hcap)
    (show (0 : ℚ) ≤ ((i - 3 : ℕ) : ℚ) / i from div_nonneg (Nat.cast_nonneg _) hi0.le)
  convert h using 1 <;> first
    | rfl
    | (rw [product_desc (by omega : 0 < ell)]
       simp only [div_pow, mul_pow, pow_succ]
       field_simp [hi0.ne', hL0.ne', hfac] <;> ring)
    | ring

/-- The first three dual coefficients vanish, leaving exactly the active
indices used by the shared Phi definition. -/
theorem sum_active {ell : ℕ} (hell : 2 ≤ ell) (f : ℕ → ℚ)
    (hzero : ∀ i, 1 ≤ i → i ≤ 3 → f i = 0) :
    (∑ i ∈ Icc 1 ell, f i) = ∑ j ∈ range (ell - 3), f (j + 4) := by
  have hsub : Icc 4 ell ⊆ Icc 1 ell := by
    intro i hi
    have hi' := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega, hi'.2⟩
  have hsum : (∑ i ∈ Icc 4 ell, f i) = ∑ i ∈ Icc 1 ell, f i :=
    sum_subset hsub (by
      intro i hi hnot
      have hi' := mem_Icc.mp hi
      have hi3 : i ≤ 3 := by
        by_contra h
        exact hnot (mem_Icc.mpr ⟨by omega, hi'.2⟩)
      exact hzero i hi'.1 hi3)
  rw [← hsum]
  symm
  apply sum_bij (fun j _ => j + 4)
  · intro j hj
    have hj' := mem_range.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj k hk h
    omega
  · intro i hi
    have hi' := mem_Icc.mp hi
    refine ⟨i - 4, mem_range.mpr (by omega), by omega⟩
  · intro j hj
    rfl

/-- The full actual capacity sum is bounded by the one shared rational Phi. -/
theorem capacity_sum_bound {m s ell : ℕ} (hell : 2 ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * (s + 1) ≤ 3 * m) :
    (∑ i ∈ Icc 1 ell,
      (((i - 3 : ℕ) : ℚ) / i) * ((i * (s + 1) - 1).choose (i + 1) : ℚ) *
        ((m + 1 - (i + 1) * (s + 1)).choose (ell - i) : ℚ)) ≤
      (101 / 100 : ℚ) * s * m.choose ell * phi ell := by
  have hs0 : (0 : ℚ) < s := Nat.cast_pos.mpr (by omega)
  have hls : ell ≤ ell * (s + 1) := by nlinarith only [Nat.zero_le (ell * s)]
  have hm : ell ≤ m := by nlinarith only [hcap, hls]
  have hC0 : (0 : ℚ) < m.choose ell := Nat.cast_pos.mpr (Nat.choose_pos hm)
  have hden : (0 : ℚ) < (s : ℚ) * m.choose ell := mul_pos hs0 hC0
  rw [sum_active hell _ (by
    intro i hi1 hi3
    have hiz : i - 3 = 0 := by omega
    simp only [hiz, Nat.cast_zero, zero_div, zero_mul])]
  calc
    _ ≤ ∑ j ∈ range (ell - 3),
        ((101 / 100 : ℚ) *
          (((((j + 4) - 3 : ℕ) : ℚ) * ((j + 4 : ℕ) : ℚ) ^ (j + 4) /
              ((j + 4 + 1).factorial : ℚ)) *
            (∏ a ∈ range (j + 4), (1 - (a : ℚ) / ell)) * ((3 : ℚ) / 5) ^ (j + 4) *
              (1 - 3 * (((j + 4 : ℕ) : ℚ) + 1) / (5 * ell)) ^ (ell - (j + 4)))) *
                ((s : ℚ) * m.choose ell) := by
      apply sum_le_sum
      intro j hj
      have hi : j + 4 ≤ ell := by have := mem_range.mp hj; omega
      exact (div_le_iff₀ hden).mp (weighted_ratio_bound (by omega : 4 ≤ j + 4) hi hs hcap)
    _ = _ := by
      unfold phi
      simp only [← sum_mul, ← mul_sum]
      ring

end Submissions.Erdos1020MatchingFKCapacitySum.Main

namespace Submissions.Erdos1020MatchingFKLayerNumeric.Main

open Submissions.Erdos1020MatchingFKLayerTable.Main
open Submissions.Erdos1020MatchingFKLayerDensity.Main
open Submissions.Erdos1020MatchingFKLayerRational.Main

/-- The exact finite and large-rank certificates cover all ranks ell>=2.
No shadow-density premise is introduced: the binomial ratio follows from room. -/
theorem normalized_dual {m s ell : ℕ} (hell : 2 ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * s ≤ 3 * (m + 1)) :
    (3 : ℚ) * (1 - ((m - s).choose ell : ℚ) / (m.choose ell : ℚ)) +
      ((101 : ℚ) / 100) * phi ell ≤ 31927 / 20000 := by
  have hratio := choose_ratio_lower hell hs hcap
  by_cases hlarge : 800 ≤ ell
  · have hd := power_lower hlarge
    have hp := Submissions.Erdos1020MatchingFKPhiLarge.Main.phi_le hlarge
    have hc := large_dual_constant
    linarith only [hratio, hd, hp, hc]
  · have hf := phi_bound_of_row hell (finite_row hell (by omega))
    have hc := finite_dual_constant
    linarith only [hratio, hf, hc]

theorem normalized_dual_lt {m s ell : ℕ} (hell : 2 ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * s ≤ 3 * (m + 1)) :
    (3 : ℚ) * (1 - ((m - s).choose ell : ℚ) / (m.choose ell : ℚ)) +
      ((101 : ℚ) / 100) * phi ell < 1332 / 833 :=
  (normalized_dual hell hs hcap).trans_lt strict_dual_constant

/-- The capacity estimate is explicit in this assembly helper. Root supplies
it from the actual binomial layer counts, before any matching theorem is stated. -/
theorem dual_bound_of_capacity {m s ell : ℕ} (hell : 2 ≤ ell)
    (hs : 1000 * ell ≤ s) (hcap : 5 * ell * s ≤ 3 * (m + 1))
    (K : ℚ) (hK : K ≤ ((101 : ℚ) / 100) * s * m.choose ell * phi ell) :
    (3 : ℚ) * s * ((m.choose ell : ℚ) - ((m - s).choose ell : ℚ)) + K ≤
      (31927 : ℚ) / 20000 * s * m.choose ell := by
  have hls : ell ≤ ell * s := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ell (show 1 ≤ s by omega)
  have hm : ell ≤ m := by nlinarith only [hell, hls, hcap]
  have hC : (0 : ℚ) < m.choose ell := Nat.cast_pos.mpr (Nat.choose_pos hm)
  have hnum := normalized_dual hell hs hcap
  have hscaled := mul_le_mul_of_nonneg_right hnum
    (show (0 : ℚ) ≤ (s : ℚ) * m.choose ell by positivity)
  have heq :
      (3 * (1 - ((m - s).choose ell : ℚ) / m.choose ell) +
          ((101 : ℚ) / 100) * phi ell) * ((s : ℚ) * m.choose ell) =
        3 * s * ((m.choose ell : ℚ) - ((m - s).choose ell : ℚ)) +
          ((101 : ℚ) / 100) * s * m.choose ell * phi ell := by
    field_simp [hC.ne'] <;> ring
  rw [heq] at hscaled
  nlinarith only [hscaled, hK]

end Submissions.Erdos1020MatchingFKLayerNumeric.Main

namespace Submissions.Erdos1020MatchingFKFiveThirdsFamily.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main
open Submissions.Erdos1020MatchingPermutationMoments.Main

/-- The moment and Hall estimates imply the weighted inequality for the actual
nested uniform families. All relabelings of the supplied blocks are averaged. -/
theorem weighted_bound {α : Type*} [Fintype α] [DecidableEq α] {ell s t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = ell)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ell)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hell : 1 ≤ ell) (hs : 10000000000000000 * ell ≤ s)
    (hm : 2 * ell * ell + 2 * ell ≤ Fintype.card α)
    (htpos : 0 < t) (hblocks : ell * t ≤ Fintype.card α)
    (x q : ℚ) (ht : (t : ℚ) ≤ 5 * (s : ℚ) / 3)
    (hxl : 2 * (s : ℚ) / 3 - 3 ≤ x) (hxu : x ≤ 2 * (s : ℚ) / 3)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (hq1 : 1 ≤ q) (hq : q ≤ (s : ℚ) + 1)
    (hqα : q * ((F (Fin.last s)).card : ℚ) /
      ((Fintype.card α).choose ell : ℚ) ≤ 1 + 333 * (s : ℚ) / 833) :
    (∑ i, ((F i).card : ℚ)) + (q - 1) * ((F (Fin.last s)).card : ℚ) ≤
      (s : ℚ) * ((Fintype.card α).choose ell : ℚ) := by
  classical
  let C : ℚ := (Fintype.card α).choose ell
  let a : ℚ := ((F (Fin.last s)).card : ℚ) / C
  let A (σ : Equiv.Perm α) (i : Fin (s + 1)) : Finset (Fin t) :=
    univ.filter (fun j => (P j).map σ.toEmbedding ∈ F i)
  have hAnested (σ : Equiv.Perm α) : ∀ i j, i ≤ j → A σ j ⊆ A σ i := by
    intro i j hij b hb
    exact mem_filter.mpr ⟨mem_univ _, hnested i j hij (mem_filter.mp hb).2⟩
  have hAno (σ : Equiv.Perm α) : ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A σ i := by
    rintro ⟨f, hfinj, hf⟩
    apply hno
    refine ⟨fun i => (P (f i)).map σ.toEmbedding, ?_, ?_⟩
    · intro i
      exact (mem_filter.mp (hf i)).2
    · intro i j hij
      exact (disjoint_map σ.toEmbedding).mpr (hPd (hfinj.ne hij))
  have hcount (σ : Equiv.Perm α) (i : Fin (s + 1)) :
      (A σ i).card = eventCount (blockEvents P (F i)) σ := by
    simp only [A, eventCount, blockEvents, mem_filter, mem_univ, true_and]
  have hC : 0 < C := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hC.le
  have hqa : q * a ≤ 1 + 333 * (s : ℚ) / 833 := by
    simpa only [a, C, mul_div_assoc] using hqα
  have hratio := Submissions.Erdos1020MatchingBinomialVariance.Main.ratio_bound hell hm hblocks
  obtain ⟨hmean, hvariance⟩ :=
    Submissions.Erdos1020MatchingPermutationVariance.Main.block_moments
      P hP hPd (F (Fin.last s)) (hF (Fin.last s)) (by omega) (2 * (ell : ℚ)) hratio
  have hmean0 : 0 ≤ average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ)) := by
    rw [hmean]
    exact mul_nonneg ha0 (Nat.cast_nonneg _)
  have hvariance' : average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ) ^ 2) -
      (average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ))) ^ 2 ≤
      3 * (ell : ℚ) * average (fun σ => (eventCount (blockEvents P (F (Fin.last s))) σ : ℚ)) := by
    apply hvariance.trans
    apply mul_le_mul_of_nonneg_right _ hmean0
    have he : (1 : ℚ) ≤ ell := Nat.cast_le.mpr hell
    linarith only [he]
  have hsQ : 10000000000000000 * (ell : ℚ) ≤ s := by exact_mod_cast hs
  have hellQ : (1 : ℚ) ≤ ell := by exact_mod_cast hell
  have hs1 : 1 ≤ s := by omega
  have hx1 : 1 ≤ x := by linarith only [hsQ, hellQ, hxl]
  have hxs : x ≤ (s : ℚ) + 1 := by
    have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
    linarith only [hxu, hs0]
  have hd : (0 : ℚ) < (s : ℚ) / 100000 := by
    have hsp : (0 : ℚ) < s := Nat.cast_pos.mpr (by omega)
    exact div_pos hsp (by norm_num)
  obtain ⟨hmargin, hbudget⟩ :=
    Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main.margin_and_budget
      hell hs ha0 (Nat.cast_nonneg t) ht hxl hq1 hq hqa
  have hmeanA : average (fun σ => ((A σ (Fin.last s)).card : ℚ)) = a * (t : ℚ) := by
    simpa only [hcount] using hmean
  have hvarA : average (fun σ => ((A σ (Fin.last s)).card : ℚ) ^ 2) -
      (a * (t : ℚ)) ^ 2 ≤ 3 * (ell : ℚ) * (a * (t : ℚ)) := by
    simpa only [hcount, hmean] using hvariance'
  have havg := Submissions.Erdos1020MatchingFKTailAverage.Main.average_nested_of_moments
    A x q (a * (t : ℚ)) (3 * (ell : ℚ)) ((s : ℚ) / 100000)
    hAnested hAno hs1 hx1 hxs hq1 hq hcapacity
    (mul_nonneg (by norm_num) (Nat.cast_nonneg ell)) hd hmeanA hvarA hmargin hbudget
  have hfamily (i : Fin (s + 1)) : average (fun σ => ((A σ i).card : ℚ)) =
      ((F i).card : ℚ) / C * (t : ℚ) := by
    simpa only [hcount] using block_mean P hP (F i) (hF i)
  have hlinear : average (fun σ => (∑ i, ((A σ i).card : ℚ)) +
      (q - 1) * (A σ (Fin.last s)).card) =
      ((∑ i, ((F i).card : ℚ)) + (q - 1) * ((F (Fin.last s)).card : ℚ)) /
        C * (t : ℚ) := by
    calc
      _ = (∑ i, average (fun σ => ((A σ i).card : ℚ))) +
          (q - 1) * average (fun σ => ((A σ (Fin.last s)).card : ℚ)) := by
        unfold average
        rw [sum_add_distrib, sum_comm, ← mul_sum, add_div, mul_div_assoc]
        simp only [div_eq_mul_inv, sum_mul]
      _ = (∑ i, ((F i).card : ℚ) / C * (t : ℚ)) +
          (q - 1) * (((F (Fin.last s)).card : ℚ) / C * (t : ℚ)) := by
        simp_rw [hfamily]
      _ = _ := by
        simp only [div_eq_mul_inv, ← sum_mul]
        ring1
  rw [hlinear] at havg
  have htQ : (0 : ℚ) < t := Nat.cast_pos.mpr htpos
  have hdiv := le_of_mul_le_mul_of_pos_right havg htQ
  exact (div_le_iff₀ hC).mp hdiv

/-- The two actual zero-head estimates can be absorbed into the singleton
families. The empty last-family case is discharged before dividing by its size. -/
theorem slices_le {α : Type*} [Fintype α] [DecidableEq α] {ell s t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = ell)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = ell)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hell : 1 ≤ ell) (hs : 10000000000000000 * ell ≤ s)
    (hm : 2 * ell * ell + 2 * ell ≤ Fintype.card α)
    (htpos : 0 < t) (hblocks : ell * t ≤ Fintype.card α)
    (x : ℚ) (ht : (t : ℚ) ≤ 5 * (s : ℚ) / 3)
    (hxl : 2 * (s : ℚ) / 3 - 3 ≤ x) (hxu : x ≤ 2 * (s : ℚ) / 3)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (Z : ℕ) (hZa : Z ≤ s * (F (Fin.last s)).card)
    (hZC : 833 * Z ≤ 333 * s * (Fintype.card α).choose ell) :
    Z + (∑ i, (F i).card) ≤ s * (Fintype.card α).choose ell := by
  classical
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  by_cases ha0 : (F (Fin.last s)).card = 0
  · have hZ0 : Z = 0 := by rw [ha0] at hZa; omega
    have hq : (1 : ℚ) ≤ (s : ℚ) + 1 := by linarith only [hs0]
    have hqa : (1 : ℚ) * ((F (Fin.last s)).card : ℚ) /
        ((Fintype.card α).choose ell : ℚ) ≤ 1 + 333 * (s : ℚ) / 833 := by
      rw [ha0]
      simp only [Nat.cast_zero, mul_zero, zero_div]
      linarith only [hs0]
    have h := weighted_bound P hP hPd F hF hnested hno hell hs hm htpos hblocks
      x 1 ht hxl hxu hcapacity (by norm_num) hq hqa
    simp only [sub_self, zero_mul, add_zero] at h
    rw [hZ0, zero_add]
    exact_mod_cast h
  · have ha : 0 < (F (Fin.last s)).card := Nat.pos_of_ne_zero ha0
    have haC : (F (Fin.last s)).card ≤ (Fintype.card α).choose ell := by
      calc
        _ ≤ (univ.powersetCard ell : Finset (Finset α)).card :=
          card_le_card (fun e he => mem_powersetCard_univ.mpr (hF _ e he))
        _ = _ := by simp
    have haQpos : (0 : ℚ) < (F (Fin.last s)).card := Nat.cast_pos.mpr ha
    have hCpos : (0 : ℚ) < (Fintype.card α).choose ell :=
      Nat.cast_pos.mpr (lt_of_lt_of_le ha haC)
    have hZaQ : (Z : ℚ) ≤ (s : ℚ) * (F (Fin.last s)).card := by exact_mod_cast hZa
    have hZCQ : (833 : ℚ) * Z ≤ 333 * s * ((Fintype.card α).choose ell : ℚ) := by
      exact_mod_cast hZC
    have hq : 1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ) ≤ (s : ℚ) + 1 := by
      have hd := (div_le_iff₀ haQpos).mpr hZaQ
      linarith only [hd]
    have hα : ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) ≤ 1 :=
      (div_le_one₀ hCpos).mpr (Nat.cast_le.mpr haC)
    have hZdiv : (Z : ℚ) / ((Fintype.card α).choose ell : ℚ) ≤ 333 * (s : ℚ) / 833 := by
      apply (div_le_iff₀ hCpos).mpr
      nlinarith only [hZCQ]
    have hqa' : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) *
        ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) ≤
        1 + 333 * (s : ℚ) / 833 := by
      have hid : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) *
          ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) =
          ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose ell : ℚ) +
          (Z : ℚ) / ((Fintype.card α).choose ell : ℚ) := by
        field_simp [haQpos.ne', hCpos.ne']
      rw [hid]
      exact add_le_add hα hZdiv
    have h := weighted_bound P hP hPd F hF hnested hno hell hs hm htpos hblocks
      x (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) ht hxl hxu hcapacity (by
        have hnonneg : (0 : ℚ) ≤ (Z : ℚ) / ((F (Fin.last s)).card : ℚ) :=
          div_nonneg (Nat.cast_nonneg _) haQpos.le
        linarith only [hnonneg]) hq hqa'
    have haQ : ((F (Fin.last s)).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
    have heq : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ) - 1) *
        ((F (Fin.last s)).card : ℚ) = (Z : ℚ) := by
      rw [add_sub_cancel_left, div_mul_cancel₀ _ haQ]
    rw [heq] at h
    have hnat : (∑ i, (F i).card) + Z ≤ s * (Fintype.card α).choose ell := by
      exact_mod_cast h
    simpa only [Nat.add_comm] using hnat

end Submissions.Erdos1020MatchingFKFiveThirdsFamily.Main

namespace Submissions.Erdos1020MatchingFKFiveThirds.Main

open Finset
open Submissions.Erdos1020MatchingHeadLinks.Main

/-- A finite all-rank range from the nested-slice and permutation-moment argument. -/
theorem star_bound {r n s : ℕ} (hr : 3 ≤ r) (hs : 10000000000000000 * r ≤ s)
    (hn : 3 * s + 5 * (r - 1) * s + 30 * r ≤ 3 * n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose r - (n - s).choose r := by
  classical
  induction r using Nat.strong_induction_on generalizing n s with
  | h r ih =>
    by_cases hr3 : r = 3
    · subst r
      exact Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main.rank_three_base
        (by omega) hn H hH hM
    have hr4 : 4 ≤ r := by omega
    have hrpos : 0 < r := by omega
    have hell : 1 ≤ r - 1 := by omega
    obtain ⟨hrprev, hsprev, hnprev⟩ :=
      Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main.induction_parameters hr4 hs hn
    have hlowerRank : ∀ K : Finset (Finset (Fin (n - (s + 1)))),
        (∀ e ∈ K, e.card = r - 1) →
        (¬ ∃ M : Finset (Finset (Fin (n - (s + 1)))), M ⊆ K ∧ M.card = s + 1 ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        K.card ≤ (n - (s + 1)).choose (r - 1) -
          (n - (s + 1) - s).choose (r - 1) := by
      intro K hK hKM
      apply ih (r - 1) (by omega) hrprev hsprev
      · simpa only [Nat.sub_add_eq] using hnprev
      · exact hK
      · exact hKM
    obtain ⟨G, hGc, hGu, hGm, hGs⟩ :=
      Submissions.Erdos1020ShiftNormalize.Main.exists_shifted H hH hM
    obtain ⟨hhead, htpos, hblocks, htail, hmoment, _, htu, hxl, hxu, _, _, htident⟩ :=
      Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main.block_parameters hr hs hn
    let J : Fin (s + 1) ↪ Fin n :=
      ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hhead⟩,
        fun _ _ h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
    let T : Finset (Fin n) := univ.map J
    have hT : T.card = s + 1 := by simp [T]
    have hJ (i : Fin (s + 1)) : J i ∈ T := mem_map.mpr ⟨i, mem_univ i, rfl⟩
    have hmono : StrictMono J := fun _ _ h => h
    have hcut (x : Fin n) : x ∈ T ↔ x.val < s + 1 := by
      constructor
      · intro hx
        obtain ⟨i, _, rfl⟩ := mem_map.mp hx
        exact i.isLt
      · intro hx
        exact mem_map.mpr ⟨⟨x.val, hx⟩, mem_univ _, Fin.ext rfl⟩
    have hlower : ∀ v ∈ T, ∀ x ∉ T, v < x := by
      intro v hv x hx
      have hv' := (hcut v).mp hv
      have hx' := (hcut x).not.mp hx
      change v.val < x.val
      omega
    let F := fun i : Fin (s + 1) => tailFamily G T (J i) r
    have hAc : Fintype.card {x : Fin n // x ∉ T} = n - (s + 1) := by
      simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
        Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
    have hAc' : Fintype.card {x : Fin n // x ∉ T} = n - s - 1 := by omega
    let t := 5 * s / 3 - 1
    let x : ℚ := (t : ℚ) - (s : ℚ) - 1
    rw [← hAc'] at hblocks hmoment
    obtain ⟨P, hP, hPd⟩ := Submissions.Erdos1020UniformBlocks.Main.exists_blocks
      (α := {x : Fin n // x ∉ T}) t (r - 1)
      (by simpa only [t, Nat.mul_comm] using hblocks)
    let Z := G.filter (fun e => e ∩ T = ∅)
    have hzero := Submissions.Erdos1020MatchingZeroShadow.Main.scaled_zero_head_le
      G T (J (Fin.last s)) (by omega : 2 ≤ r) hT (hJ _) hlower hGu hGm hGs
    have hZa : Z.card ≤ s * (F (Fin.last s)).card := by
      have hh : r * Z.card ≤ r * (s * (F (Fin.last s)).card) := by
        calc
          _ ≤ (r - 1) * s * (F (Fin.last s)).card := hzero
          _ ≤ r * (s * (F (Fin.last s)).card) := by
            simpa only [Nat.mul_assoc] using
              Nat.mul_le_mul_right (s * (F (Fin.last s)).card) (Nat.sub_le r 1)
      exact le_of_mul_le_mul_of_pos_left hh hrpos
    have hshadow := Submissions.Erdos1020MatchingGenericTailShadow.Main.shadow_bound_of_lower_rank
      G T hT hlower hGu hGm hGs hlowerRank
    let m := n - (s + 1)
    have hstrong : 5 * (r - 1) * (s + 1) ≤ 3 * m := by
      simpa only [m, Nat.sub_add_eq] using
        Submissions.Erdos1020MatchingFKCapacityReduction.Main.cushion_room hr hn
    have htail' : 5 * (r - 1) * s ≤ 3 * (m + 1) := by
      simpa only [m, Nat.sub_add_eq] using htail
    have hell2 : 2 ≤ r - 1 := by omega
    have hs1000 : 1000 * (r - 1) ≤ s := by omega
    have hK := Submissions.Erdos1020MatchingFKCapacitySum.Main.capacity_sum_bound
      hell2 hs1000 hstrong
    have hdual := Submissions.Erdos1020MatchingFKLayerNumeric.Main.dual_bound_of_capacity
      hell2 hs1000 htail' _ hK
    have hBC : (m - s).choose (r - 1) ≤ m.choose (r - 1) :=
      Nat.choose_le_choose _ (Nat.sub_le _ _)
    have hid (i : ℕ) : r - i - 1 = (r - 1) - i := by omega
    have hnumeric : 3 * (s : ℚ) * (m.choose (r - 1) - (m - s).choose (r - 1) : ℕ) +
        (∑ i ∈ Icc 1 (r - 1), (((i - 3 : ℕ) : ℚ) / i) *
          ((i * (s + 1) - 1).choose (i + 1) *
            (m + 1 - (i + 1) * (s + 1)).choose (r - i - 1) : ℕ)) ≤
          4 * (((333 : ℚ) / 833) * s * m.choose (r - 1)) := by
      simp only [Nat.cast_sub hBC, Nat.cast_mul, hid, mul_assoc] at hdual ⊢
      have hcoef : (31927 : ℚ) / 20000 ≤ 4 * (333 / 833) := by norm_num
      have hscaled := mul_le_mul_of_nonneg_right hcoef
        (show (0 : ℚ) ≤ (s : ℚ) * m.choose (r - 1) by positivity)
      nlinarith only [hdual, hscaled]
    have hZm := Submissions.Erdos1020MatchingZeroShadow.Main.shadow_zero_matchingFree
      G T hT hlower hGs hGm
    have hTc : Tᶜ.card = m := by
      simp only [Finset.card_compl, Fintype.card_fin, hT, m]
    have hlayerRoom := Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main.layer_room
      hr (by omega : 3 * r ≤ s) htail'
    have hZQ := Submissions.Erdos1020MatchingFKLayerBound.Main.zero_head_card_le_of_numeric
      (by omega : 2 ≤ r) G T hTc hGu hGs hZm hlayerRoom hshadow
      ((333 : ℚ) / 833) hnumeric
    have hZC : 833 * Z.card ≤ 333 * s *
        (Fintype.card {x : Fin n // x ∉ T}).choose (r - 1) := by
      rw [hAc]
      apply (Nat.cast_le (α := ℚ)).mp
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      change 833 * (Z.card : ℚ) ≤ 333 * (s : ℚ) * m.choose (r - 1)
      change (Z.card : ℚ) ≤ (333 / 833 : ℚ) * s * m.choose (r - 1) at hZQ
      nlinarith only [hZQ]
    have hweighted := Submissions.Erdos1020MatchingFKFiveThirdsFamily.Main.slices_le
      P hP hPd F (fun i => tailFamily_uniform G T (J i) r)
      (tailFamily_nested G T r J hJ hmono hGs) (no_rainbow G T r J hJ hGm)
      hell hsprev (by simpa only [pow_two, Nat.mul_assoc] using hmoment) htpos hblocks x
      (by linarith only [htu]) hxl hxu htident.symm.le Z.card hZa hZC
    rw [hAc] at hweighted
    have hsingle : (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
        ∑ i, (F i).card := by
      change (∑ v ∈ univ.map J, (G.filter (fun e => e ∩ T = {v})).card) ≤ _
      rw [sum_map]
      apply sum_le_sum
      intro i _
      exact singleton_head_le G T (J i) r (hJ i) hGu
    have hslices : (G.filter (fun e => e ∩ T = ∅)).card +
        (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
          s * (n - (s + 1)).choose (r - 1) := by
      exact (Nat.add_le_add_left hsingle _).trans hweighted
    rw [← hGc]
    exact Submissions.Erdos1020MatchingHeadComparison.Main.star_bound_of_slices
      G T (by omega) hT hGu hhead hslices
end Submissions.Erdos1020MatchingFKFiveThirds.Main

namespace Submissions.Erdos1020MatchingFKFiveThirdsProof.Main

/-- The original maximum follows from the stronger all-rank star bound. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → 10000000000000000 * r ≤ k - 1 →
      3 * (k - 1) + 5 * (r - 1) * (k - 1) + 30 * r ≤ 3 * n →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hs hn H hH hM
  have hkpred : (k - 1) + 1 = k := by omega
  have hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = (k - 1) + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    simpa only [hkpred] using hM
  have hb := Submissions.Erdos1020MatchingFKFiveThirds.Main.star_bound hr hs hn H hH hfree
  have hhead := (Submissions.Erdos1020MatchingFKFiveThirdsParameters.Main.block_parameters hr hs hn).1
  have hsub : n - (k - 1) = n - k + 1 := by omega
  rw [hsub] at hb
  exact hb.trans (le_max_right _ _)

end Submissions.Erdos1020MatchingFKFiveThirdsProof.Main
