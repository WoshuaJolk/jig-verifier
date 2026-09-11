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

namespace Submissions.Erdos1020MatchingFKAverage.Main

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

/-- A relative variance bound controls the average of the Hall quadratic.
The count may have zero density; only the large-coefficient branch divides by q. -/
theorem average_le_of_moments {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {s t : ℕ} (E : Fin t → Finset Ω) (W : Ω → ℚ) (α x q : ℚ)
    (hs : 400 ≤ s) (ht : (t : ℚ) ≤ 5 * (s : ℚ) / 3)
    (hxl : 2 * (s : ℚ) / 3 - 2 ≤ x) (hxu : x ≤ 2 * (s : ℚ) / 3)
    (hα0 : 0 ≤ α) (hq : q ≤ 1 + 3 * (s : ℚ) / 4)
    (hqα : q * α ≤ 1 + 3 * (s : ℚ) / 8)
    (hzs : ∀ ω, eventCount E ω ≤ s)
    (hquad : ∀ ω, W ω - (s : ℚ) * t ≤
      (q - 2 * x) * (eventCount E ω : ℚ) +
        (x / s) * (eventCount E ω : ℚ) ^ 2)
    (hmean : average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ))
    (hvariance : average (fun ω => (eventCount E ω : ℚ) ^ 2) -
      (average (fun ω => (eventCount E ω : ℚ))) ^ 2 ≤
        6 * average (fun ω => (eventCount E ω : ℚ))) :
    average W ≤ (s : ℚ) * t := by
  classical
  have hsQ : (400 : ℚ) ≤ s := Nat.cast_le.mpr hs
  have hs0 : (0 : ℚ) < s := by linarith only [hsQ]
  have hx0 : 0 < x := by linarith only [hsQ, hxl]
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
  have hμbound : α * (t : ℚ) ≤ ((1 + 3 * (s : ℚ) / 8) * t) / q := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ = (q * α) * (t : ℚ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hqα (Nat.cast_nonneg t)
  have hxs0 : 0 ≤ x / (s : ℚ) := div_nonneg hx0.le hs0.le
  have hcoefficient : q - 2 * x + (x / s) * (α * (t : ℚ) + 6) ≤ 0 := by
    calc
      _ ≤ q - 2 * x + (x / s) *
          (((1 + 3 * (s : ℚ) / 8) * t) / q + 6) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (add_le_add hμbound le_rfl) hxs0)
      _ ≤ 0 := Submissions.Erdos1020MatchingFKQuadratic.Main.coefficient_bound_of_t
        hsQ ht hxl hxu hxq hq
  have hsecond : average (fun ω => (eventCount E ω : ℚ) ^ 2) ≤
      (α * (t : ℚ)) ^ 2 + 6 * (α * (t : ℚ)) := by
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
        (x / s) * ((α * (t : ℚ)) ^ 2 + 6 * (α * (t : ℚ))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond hxs0)
    _ = (s : ℚ) * t + (α * (t : ℚ)) *
        (q - 2 * x + (x / s) * (α * (t : ℚ) + 6)) := by ring
    _ ≤ (s : ℚ) * t := by
      have h := mul_nonpos_of_nonneg_of_nonpos hμ hcoefficient
      linarith only [h]

/-- The exact moment outputs and samplewise nested families give the weighted
average bound. The event normalization and pointwise Hall premises remain explicit. -/
theorem average_nested_of_moments {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {s t : ℕ} (E : Fin t → Finset Ω)
    (A : Ω → Fin (s + 1) → Finset (Fin t)) (α x q : ℚ)
    (hnested : ∀ ω i j, i ≤ j → A ω j ⊆ A ω i)
    (hno : ∀ ω, ¬ ∃ f : Fin (s + 1) → Fin t,
      Function.Injective f ∧ ∀ i, f i ∈ A ω i)
    (hcount : ∀ ω, (A ω (Fin.last s)).card = eventCount E ω)
    (hs : 400 ≤ s) (ht : (t : ℚ) ≤ 5 * (s : ℚ) / 3)
    (hxl : 2 * (s : ℚ) / 3 - 2 ≤ x) (hxu : x ≤ 2 * (s : ℚ) / 3)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (hα0 : 0 ≤ α)
    (hq : q ≤ 1 + 3 * (s : ℚ) / 4)
    (hqα : q * α ≤ 1 + 3 * (s : ℚ) / 8)
    (hmean : average (fun ω => (eventCount E ω : ℚ)) = α * (t : ℚ))
    (hvariance : average (fun ω => (eventCount E ω : ℚ) ^ 2) -
      (average (fun ω => (eventCount E ω : ℚ))) ^ 2 ≤
        6 * average (fun ω => (eventCount E ω : ℚ))) :
    average (fun ω => (∑ i, ((A ω i).card : ℚ)) +
      (q - 1) * (A ω (Fin.last s)).card) ≤ (s : ℚ) * t := by
  classical
  have hspos : 0 < s := lt_of_lt_of_le (by decide : 0 < 400) hs
  have hsQ : (400 : ℚ) ≤ s := Nat.cast_le.mpr hs
  have hx0 : 0 ≤ x := by linarith only [hsQ, hxl]
  have hxs : x ≤ (s : ℚ) := by linarith only [hsQ, hxu]
  apply average_le_of_moments E _ α x q hs ht hxl hxu hα0 hq hqα
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

end Submissions.Erdos1020MatchingFKAverage.Main

namespace Submissions.Erdos1020MatchingFKParameters.Main

/-- Fixed block count at the rank-four boundary, valid in every larger ambient set.
The block count uses natural division; all displayed fractional bounds are rational. -/
theorem block_parameters {s n : ℕ} (hs : 400 ≤ s) (hn : 6 * s ≤ n) :
    let t := (5 * s - 1) / 3
    let m := n - s - 1
    let x : ℚ := (t : ℚ) - (s : ℚ) - 1
    0 < t ∧ 3 * t ≤ m ∧ 20 ≤ m ∧ 5 * s - 1 ≤ m ∧
      5 * (s : ℚ) / 3 - 1 ≤ (t : ℚ) ∧ (t : ℚ) ≤ 5 * (s : ℚ) / 3 ∧
      2 * (s : ℚ) / 3 - 2 ≤ x ∧ x ≤ 2 * (s : ℚ) / 3 ∧
      0 ≤ x ∧ x ≤ (s : ℚ) ∧ (t : ℚ) = (s : ℚ) + x + 1 := by
  dsimp only
  have hsQ : (400 : ℚ) ≤ s := (Nat.cast_le (α := ℚ)).mpr hs
  have hfloorL : 5 * s ≤ 3 * ((5 * s - 1) / 3) + 3 := by omega
  have hfloorU : 3 * ((5 * s - 1) / 3) ≤ 5 * s := by omega
  have hfloorLQ := (Nat.cast_le (α := ℚ)).mpr hfloorL
  have hfloorUQ := (Nat.cast_le (α := ℚ)).mpr hfloorU
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hfloorLQ hfloorUQ
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals linarith only [hsQ, hfloorLQ, hfloorUQ]

/-- The two integer slice bounds give the density and coefficient hypotheses.
The last slice is nonempty, and no division by the zero-head cardinality occurs. -/
theorem slice_parameters {s Z a C : ℕ}
    (ha : 0 < a) (haC : a ≤ C)
    (hZa : 4 * Z ≤ 3 * s * a) (hZC : 8 * Z ≤ 3 * s * C) :
    let α : ℚ := (a : ℚ) / (C : ℚ)
    let q : ℚ := 1 + (Z : ℚ) / (a : ℚ)
    0 ≤ α ∧ α ≤ 1 ∧ 1 ≤ q ∧ q ≤ 1 + 3 * (s : ℚ) / 4 ∧
      q * α ≤ 1 + 3 * (s : ℚ) / 8 := by
  dsimp only
  have haQ : (0 : ℚ) < a := (Nat.cast_pos (α := ℚ)).mpr ha
  have hCQ : (0 : ℚ) < C := (Nat.cast_pos (α := ℚ)).mpr (ha.trans_le haC)
  have haCQ : (a : ℚ) ≤ C := (Nat.cast_le (α := ℚ)).mpr haC
  have hZaQ := (Nat.cast_le (α := ℚ)).mpr hZa
  have hZCQ := (Nat.cast_le (α := ℚ)).mpr hZC
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hZaQ hZCQ
  have hα1 : (a : ℚ) / (C : ℚ) ≤ 1 := by
    apply (div_le_iff₀ hCQ).mpr
    simpa only [one_mul] using haCQ
  have hq0 : 0 ≤ (Z : ℚ) / (a : ℚ) :=
    div_nonneg (Nat.cast_nonneg Z) haQ.le
  have hqa : (Z : ℚ) / (a : ℚ) ≤ 3 * (s : ℚ) / 4 := by
    apply (div_le_iff₀ haQ).mpr
    nlinarith only [hZaQ]
  have hqC : (Z : ℚ) / (C : ℚ) ≤ 3 * (s : ℚ) / 8 := by
    apply (div_le_iff₀ hCQ).mpr
    nlinarith only [hZCQ]
  have hproduct : (1 + (Z : ℚ) / (a : ℚ)) * ((a : ℚ) / (C : ℚ)) =
      (a : ℚ) / (C : ℚ) + (Z : ℚ) / (C : ℚ) := by
    rw [add_mul, one_mul, ← mul_div_assoc, div_mul_cancel₀ _ haQ.ne']
  refine ⟨div_nonneg haQ.le hCQ.le, hα1, le_add_of_nonneg_right hq0,
    add_le_add le_rfl hqa, ?_⟩
  rw [hproduct]
  exact add_le_add hα1 hqC

end Submissions.Erdos1020MatchingFKParameters.Main

namespace Submissions.Erdos1020MatchingTailShadowDensity.Main

open Finset

private theorem reindex_tail {n m r k : ℕ}
    (F : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (hc : Fintype.card {x : Fin n // x ∉ T} = m)
    (havoid : ∀ e ∈ F, ∀ x ∈ e, x ∉ T)
    (hF : ∀ e ∈ F, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ F ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Finset (Fin m)), G.card = F.card ∧
      (∀ e ∈ G, e.card = r) ∧
      ¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  let c : {x : Fin n // x ∉ T} ≃ Fin m := Fintype.equivFinOfCardEq hc
  let E : Fin m ↪ Fin n := c.symm.toEmbedding.trans (Function.Embedding.subtype (· ∉ T))
  let E' := (Finset.mapEmbedding E).toEmbedding
  let shrink (e : Finset (Fin n)) := (e.subtype (· ∉ T)).map c.toEmbedding
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

/-- The actual empty-head shadow has at most half of the tail triples, and
its rank-four parent inherits the corresponding restricted-shadow estimate. -/
theorem zero_head_density {n s : ℕ} (hs : 400 ≤ s) (hn : 6 * s ≤ n)
    (H : Finset (Finset (Fin n))) (T : Finset (Fin n)) (hT : T.card = s + 1)
    (hlower : ∀ v ∈ T, ∀ x ∉ T, v < x)
    (hH : ∀ e ∈ H, e.card = 4)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    2 * (H.filter (fun e => e ∩ T = ∅)).shadow.card ≤ (n - (s + 1)).choose 3 ∧
      8 * (H.filter (fun e => e ∩ T = ∅)).card ≤ 3 * s * (n - (s + 1)).choose 3 := by
  classical
  let Z := H.filter (fun e => e ∩ T = ∅)
  let m := n - (s + 1)
  have hZu : ∀ e ∈ Z, e.card = 4 := fun _ he => hH _ (mem_filter.mp he).1
  have hSu : ∀ e ∈ Z.shadow, e.card = 3 := Set.Sized.shadow hZu
  have hSm := Submissions.Erdos1020MatchingZeroShadow.Main.shadow_zero_matchingFree
    H T hT hlower hstable hM
  have havoid : ∀ e ∈ Z.shadow, ∀ x ∈ e, x ∉ T := by
    intro e he x hx hxT
    obtain ⟨f, hf, hef⟩ := exists_subset_of_mem_shadow he
    have hmeet : x ∈ f ∩ T := mem_inter.mpr ⟨hef hx, hxT⟩
    rw [(mem_filter.mp hf).2] at hmeet
    exact notMem_empty x hmeet
  have htail : Fintype.card {x : Fin n // x ∉ T} = m := by
    simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
      Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
  obtain ⟨G, hGc, hGu, hGm⟩ := reindex_tail Z.shadow T htail havoid hSu hSm
  have hm : 5 * s - 1 ≤ m := by dsimp only [m]; omega
  let u := 5 * (s + 1) / 3
  have hw : 3 * (s + 1) + (3 - 1) * s ≤ 3 * u := by dsimp only [u]; omega
  have hc : (3 - 1) * u + s + 1 ≤ m := by dsimp only [u]; omega
  have hstar := Submissions.Erdos1020MatchingRefined.Main.star_bound
    (by decide : 2 ≤ 3) hw hc G hGu hGm
  rw [hGc] at hstar
  have hchoose := Submissions.Erdos1020MatchingTripleChoose.Main.choose_le_two_choose_sub
    (by omega : 14 ≤ s) hm
  have hmono := Nat.choose_le_choose 3 (Nat.sub_le m s)
  have hhalf : 2 * Z.shadow.card ≤ m.choose 3 := by omega
  have hrestricted : 4 * Z.card ≤ 3 * s * Z.shadow.card :=
    Submissions.Erdos1020MatchingRestrictedShadow.Main.shadow_bound s 4 (by decide) Z hZu hSm
  refine ⟨hhalf, ?_⟩
  have hscaled := Nat.mul_le_mul_left (3 * s) hhalf
  change 8 * Z.card ≤ 3 * s * m.choose 3
  nlinarith only [hrestricted, hscaled]

end Submissions.Erdos1020MatchingTailShadowDensity.Main

namespace Submissions.Erdos1020MatchingFKFamily.Main

open Finset
open Submissions.Erdos1020MatchingFiniteMoments.Main
open Submissions.Erdos1020MatchingPermutationMoments.Main

/-- The moment and Hall estimates imply the weighted inequality for the actual
nested triple families. All relabelings of the supplied blocks are averaged. -/
theorem weighted_bound {α : Type*} [Fintype α] [DecidableEq α] {s t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = 3)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = 3)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hs : 400 ≤ s) (hm : 20 ≤ Fintype.card α)
    (htpos : 0 < t) (hblocks : 3 * t ≤ Fintype.card α)
    (x q : ℚ) (ht : (t : ℚ) ≤ 5 * (s : ℚ) / 3)
    (hxl : 2 * (s : ℚ) / 3 - 2 ≤ x) (hxu : x ≤ 2 * (s : ℚ) / 3)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (hq : q ≤ 1 + 3 * (s : ℚ) / 4)
    (hqα : q * ((F (Fin.last s)).card : ℚ) /
      ((Fintype.card α).choose 3 : ℚ) ≤ 1 + 3 * (s : ℚ) / 8) :
    (∑ i, ((F i).card : ℚ)) + (q - 1) * ((F (Fin.last s)).card : ℚ) ≤
      (s : ℚ) * ((Fintype.card α).choose 3 : ℚ) := by
  classical
  let C : ℚ := (Fintype.card α).choose 3
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
  have hqa : q * a ≤ 1 + 3 * (s : ℚ) / 8 := by
    simpa only [a, C, mul_div_assoc] using hqα
  obtain ⟨hmean, hvariance⟩ := triple_moments P hP hPd (F (Fin.last s))
    (hF (Fin.last s)) hm hblocks
  have havg := Submissions.Erdos1020MatchingFKAverage.Main.average_nested_of_moments
    (blockEvents P (F (Fin.last s))) A a x q hAnested hAno
    (fun σ => hcount σ (Fin.last s)) hs ht hxl hxu hcapacity ha0 hq hqa hmean hvariance
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
theorem slices_le {α : Type*} [Fintype α] [DecidableEq α] {s t : ℕ}
    (P : Fin t → Finset α) (hP : ∀ i, (P i).card = 3)
    (hPd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (F : Fin (s + 1) → Finset (Finset α))
    (hF : ∀ i, ∀ e ∈ F i, e.card = 3)
    (hnested : ∀ i j, i ≤ j → F j ⊆ F i)
    (hno : ¬ ∃ e : Fin (s + 1) → Finset α,
      (∀ i, e i ∈ F i) ∧ Pairwise (fun i j => Disjoint (e i) (e j)))
    (hs : 400 ≤ s) (hm : 20 ≤ Fintype.card α)
    (htpos : 0 < t) (hblocks : 3 * t ≤ Fintype.card α)
    (x : ℚ) (ht : (t : ℚ) ≤ 5 * (s : ℚ) / 3)
    (hxl : 2 * (s : ℚ) / 3 - 2 ≤ x) (hxu : x ≤ 2 * (s : ℚ) / 3)
    (hcapacity : (s : ℚ) + x + 1 ≤ (t : ℚ))
    (Z : ℕ) (hZa : 4 * Z ≤ 3 * s * (F (Fin.last s)).card)
    (hZC : 8 * Z ≤ 3 * s * (Fintype.card α).choose 3) :
    Z + (∑ i, (F i).card) ≤ s * (Fintype.card α).choose 3 := by
  classical
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  by_cases ha0 : (F (Fin.last s)).card = 0
  · have hZ0 : Z = 0 := by rw [ha0] at hZa; omega
    have hq : (1 : ℚ) ≤ 1 + 3 * (s : ℚ) / 4 := by linarith only [hs0]
    have hqa : (1 : ℚ) * ((F (Fin.last s)).card : ℚ) /
        ((Fintype.card α).choose 3 : ℚ) ≤ 1 + 3 * (s : ℚ) / 8 := by
      rw [ha0]
      simp only [Nat.cast_zero, mul_zero, zero_div]
      linarith only [hs0]
    have h := weighted_bound P hP hPd F hF hnested hno hs hm htpos hblocks
      x 1 ht hxl hxu hcapacity hq hqa
    simp only [sub_self, zero_mul, add_zero] at h
    rw [hZ0, zero_add]
    exact_mod_cast h
  · have ha : 0 < (F (Fin.last s)).card := Nat.pos_of_ne_zero ha0
    have haC : (F (Fin.last s)).card ≤ (Fintype.card α).choose 3 := by
      calc
        _ ≤ (univ.powersetCard 3 : Finset (Finset α)).card :=
          card_le_card (fun e he => mem_powersetCard_univ.mpr (hF _ e he))
        _ = _ := by simp
    obtain ⟨_, _, _, hq, hqa⟩ :=
      Submissions.Erdos1020MatchingFKParameters.Main.slice_parameters ha haC hZa hZC
    have hqa' : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) *
        ((F (Fin.last s)).card : ℚ) / ((Fintype.card α).choose 3 : ℚ) ≤
        1 + 3 * (s : ℚ) / 8 := by
      simpa only [mul_div_assoc] using hqa
    have h := weighted_bound P hP hPd F hF hnested hno hs hm htpos hblocks
      x (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ)) ht hxl hxu hcapacity hq hqa'
    have haQ : ((F (Fin.last s)).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
    have heq : (1 + (Z : ℚ) / ((F (Fin.last s)).card : ℚ) - 1) *
        ((F (Fin.last s)).card : ℚ) = (Z : ℚ) := by
      rw [add_sub_cancel_left, div_mul_cancel₀ _ haQ]
    rw [heq] at h
    have hnat : (∑ i, (F i).card) + Z ≤ s * (Fintype.card α).choose 3 := by
      exact_mod_cast h
    simpa only [Nat.add_comm] using hnat

end Submissions.Erdos1020MatchingFKFamily.Main

namespace Submissions.Erdos1020MatchingFKRankFour.Main

open Finset
open Submissions.Erdos1020MatchingHeadLinks.Main

/-- An explicit rank-four range obtained from the fixed-block second moment
argument. The bound holds in every ambient set with n at least 6s. -/
theorem star_bound {n s : ℕ} (hs : 400 ≤ s) (hn : 6 * s ≤ n)
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = 4)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ n.choose 4 - (n - s).choose 4 := by
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
  let F := fun i : Fin (s + 1) => tailFamily G T (J i) 4
  have hAc : Fintype.card {x : Fin n // x ∉ T} = n - (s + 1) := by
    simpa only [Fintype.card_fin, Fintype.card_coe, hT] using
      Fintype.card_subtype_compl (fun x : Fin n => x ∈ T)
  have hAc' : Fintype.card {x : Fin n // x ∉ T} = n - s - 1 := by omega
  let t := (5 * s - 1) / 3
  let x : ℚ := (t : ℚ) - (s : ℚ) - 1
  obtain ⟨htpos, hblocks, hm, _, _, htu, hxl, hxu, _, _, htident⟩ :=
    Submissions.Erdos1020MatchingFKParameters.Main.block_parameters hs hn
  rw [← hAc'] at hblocks hm
  obtain ⟨P, hP, hPd⟩ := Submissions.Erdos1020UniformBlocks.Main.exists_blocks
    (α := {x : Fin n // x ∉ T}) t 3 (by simpa only [t, Nat.mul_comm] using hblocks)
  have hzero := Submissions.Erdos1020MatchingZeroShadow.Main.scaled_zero_head_le
    G T (J (Fin.last s)) (by decide : 2 ≤ 4) hT (hJ _) hlower hGu hGm hGs
  have hdensity := (Submissions.Erdos1020MatchingTailShadowDensity.Main.zero_head_density
    hs hn G T hT hlower hGu hGm hGs).2
  have hZC : 8 * (G.filter (fun e => e ∩ T = ∅)).card ≤
      3 * s * (Fintype.card {x : Fin n // x ∉ T}).choose 3 := by
    rwa [hAc]
  have hweighted := Submissions.Erdos1020MatchingFKFamily.Main.slices_le
    P hP hPd F (fun i => tailFamily_uniform G T (J i) 4)
    (tailFamily_nested G T 4 J hJ hmono hGs) (no_rainbow G T 4 J hJ hGm)
    hs hm htpos hblocks x htu hxl hxu htident.symm.le
    (G.filter (fun e => e ∩ T = ∅)).card hzero hZC
  rw [hAc] at hweighted
  have hsingle : (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
      ∑ i, (F i).card := by
    change (∑ v ∈ univ.map J, (G.filter (fun e => e ∩ T = {v})).card) ≤ _
    rw [sum_map]
    apply sum_le_sum
    intro i _
    exact singleton_head_le G T (J i) 4 (hJ i) hGu
  have hslices : (G.filter (fun e => e ∩ T = ∅)).card +
      (∑ v ∈ T, (G.filter (fun e => e ∩ T = {v})).card) ≤
        s * (n - (s + 1)).choose (4 - 1) := by
    change _ ≤ s * (n - (s + 1)).choose 3
    exact (Nat.add_le_add_left hsingle _).trans hweighted
  rw [← hGc]
  exact Submissions.Erdos1020MatchingHeadComparison.Main.star_bound_of_slices
    G T (by decide) hT hGu hhead hslices

end Submissions.Erdos1020MatchingFKRankFour.Main

namespace Submissions.Erdos1020MatchingFKRankFourProof.Main

/-- The original maximum follows from the stronger rank-four star bound. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → r = 4 → 401 ≤ k → 6 * (k - 1) ≤ n →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hrank hklarge hn H hH hM
  subst r
  have hs : 400 ≤ k - 1 := by omega
  have hkpred : (k - 1) + 1 = k := by omega
  have hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = (k - 1) + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    simpa only [hkpred] using hM
  have hb := Submissions.Erdos1020MatchingFKRankFour.Main.star_bound hs hn H hH hfree
  have hsub : n - (k - 1) = n - k + 1 := by omega
  rw [hsub] at hb
  exact hb.trans (le_max_right _ _)

end Submissions.Erdos1020MatchingFKRankFourProof.Main
