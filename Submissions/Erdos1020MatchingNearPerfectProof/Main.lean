import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

-- Source: TraceMatching.lean


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


namespace Submissions.Erdos1020MatchingTraceGap.Main

/-- Two distinct colors sharing an outside vertex leave a head vertex unused
when the head has one fewer vertex than the total edge-incidence count. -/
theorem exists_head_vertex_avoiding_family {α ι : Type*}
    [DecidableEq α] [Fintype ι] {r k : ℕ}
    (A : Finset α) (f : ι → Finset α) (hf : ∀ i, (f i).card = r)
    (hι : Fintype.card ι = k) (hA : A.card + 1 = r * k)
    {c d : ι} (hcd : c ≠ d) {x : α}
    (hxA : x ∉ A) (hxc : x ∈ f c) (hxd : x ∈ f d) :
    ∃ v ∈ A, ∀ i, v ∉ f i := by
  classical
  let I : Finset (Σ _ : ι, α) := (Finset.univ : Finset ι).sigma f
  let π : (Σ _ : ι, α) → α := fun z => z.2
  let U : Finset α := I.image π
  have hIc : (⟨c, x⟩ : Σ _ : ι, α) ∈ I :=
    Finset.mem_sigma.mpr ⟨Finset.mem_univ c, hxc⟩
  have hId : (⟨d, x⟩ : Σ _ : ι, α) ∈ I :=
    Finset.mem_sigma.mpr ⟨Finset.mem_univ d, hxd⟩
  have hIcard : I.card = r * k := by
    calc
      _ = ∑ i, (f i).card := Finset.card_sigma _ _
      _ = k * r := by simp [hf, hι]
      _ = r * k := Nat.mul_comm _ _
  have hUne : U.card ≠ I.card := by
    intro h
    have hinj : Set.InjOn π (I : Set (Σ _ : ι, α)) := Finset.card_image_iff.mp h
    exact hcd (congrArg (fun z : Σ _ : ι, α => z.1) (hinj hIc hId rfl))
  have hUle : U.card ≤ I.card := Finset.card_image_le
  have hUlt : U.card < r * k := by omega
  by_contra hnone
  have hcover : A ⊆ U := by
    intro v hv
    by_contra hvU
    apply hnone
    refine ⟨v, hv, ?_⟩
    intro i hvi
    apply hvU
    exact Finset.mem_image.mpr ⟨⟨i, v⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hvi⟩, rfl⟩
  have hinsert : insert x A ⊆ U := Finset.insert_subset
    (Finset.mem_image.mpr ⟨⟨c, x⟩, hIc, rfl⟩) hcover
  have hbound := Finset.card_le_card hinsert
  rw [Finset.card_insert_of_notMem hxA, hA] at hbound
  exact hUlt.not_ge hbound

end Submissions.Erdos1020MatchingTraceGap.Main

namespace Submissions.Erdos1020MatchingTrace.Main

open Finset

/-- Indexed shifted families lift disjoint traces on a head with one fewer
vertex than the total uniform edge size to disjoint original edges. -/
theorem exists_disjoint_of_disjoint_traces {n r k : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hF : ∀ c e, e ∈ F c → e.card = r)
    (hι : Fintype.card ι = k) (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ c i j, i < j → UV.IsCompressed {i} {j} (F c))
    (f : ι → Finset (Fin n)) (hf : ∀ c, f c ∈ F c)
    (hd : Pairwise (fun c d => Disjoint (f c ∩ A) (f d ∩ A))) :
    ∃ g : ι → Finset (Fin n), (∀ c, g c ∈ F c) ∧
      Pairwise (fun c d => Disjoint (g c) (g d)) := by
  classical
  let W : (ι → Finset (Fin n)) → ℕ := fun g => ∑ c, ∑ x ∈ g c, x.val
  let candidates : Finset (ι → Finset (Fin n)) := univ.filter (fun g =>
    (∀ c, g c ∈ F c) ∧ Pairwise (fun c d => Disjoint (g c ∩ A) (g d ∩ A)))
  have hfc : f ∈ candidates := by simp [candidates, hf, hd]
  obtain ⟨g, hg, hmin⟩ := exists_min_image candidates W ⟨f, hfc⟩
  have hgm := (mem_filter.mp hg).2.1
  have hgd := (mem_filter.mp hg).2.2
  refine ⟨g, hgm, ?_⟩
  intro c d hcd
  by_contra hbad
  obtain ⟨x, hxc, hxd⟩ := not_disjoint_iff.mp hbad
  have hxA : x ∉ A := by
    intro hx
    exact disjoint_left.mp (hgd hcd) (mem_inter.mpr ⟨hxc, hx⟩)
      (mem_inter.mpr ⟨hxd, hx⟩)
  obtain ⟨v, hvA, hv⟩ :=
    Submissions.Erdos1020MatchingTraceGap.Main.exists_head_vertex_avoiding_family
      A g (fun i => hF i _ (hgm i)) hι hA hcd hxA hxc hxd
  let e := insert v ((g c).erase x)
  have hev : v ∉ (g c).erase x := notMem_mono (erase_subset _ _) (hv c)
  have hex : x ∉ (g c).erase x := notMem_erase _ _
  have heF : e ∈ F c :=
    Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
      (hstable c v x (hcut v hvA x hxA)) hex hev (by simpa only [Finset.insert_erase hxc] using hgm c)
  let g' := Function.update g c e
  have hedis (i : ι) (hic : i ≠ c) : Disjoint (e ∩ A) (g i ∩ A) := by
    apply disjoint_left.mpr
    intro y hy hyi
    rcases mem_inter.mp hy with ⟨hye, hyA⟩
    rcases mem_insert.mp hye with rfl | hyold
    · exact hv i (mem_inter.mp hyi).1
    · exact disjoint_left.mp (hgd (Ne.symm hic))
        (mem_inter.mpr ⟨mem_of_mem_erase hyold, hyA⟩) hyi
  have hg' : g' ∈ candidates := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro i
      by_cases hi : i = c
      · subst i
        simpa [g'] using heF
      · simpa [g', hi] using hgm i
    · intro i j hij
      by_cases hi : i = c
      · subst i
        simpa [g', Ne.symm hij] using hedis j (Ne.symm hij)
      · by_cases hj : j = c
        · subst j
          simpa [g', hi] using (hedis i hi).symm
        · simpa [g', hi, hj] using hgd hij
  have hweight : (∑ y ∈ e, y.val) < ∑ y ∈ g c, y.val := by
    dsimp [e]
    rw [sum_insert hev]
    have hsum := sum_erase_add (g c) (fun y : Fin n => y.val) hxc
    have hlt : v.val < x.val := hcut v hvA x hxA
    omega
  have hless : W g' < W g := by
    apply sum_lt_sum
    · intro i _
      by_cases hi : i = c
      · subst i
        simpa [g'] using hweight.le
      · simp [g', hi]
    · exact ⟨c, mem_univ _, by simpa [g'] using hweight⟩
  exact (not_lt_of_ge (hmin g' hg')) hless

/-- Matching-freeness also excludes indexed disjoint traces, including repeated
empty traces, so this form can be used for upward completions. -/
theorem no_indexed_trace_matching {n r k : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hι : Fintype.card ι = k)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (f : ι → Finset (Fin n)) (hf : ∀ c, f c ∈ H) :
    ¬ Pairwise (fun c d => Disjoint (f c ∩ A) (f d ∩ A)) := by
  classical
  intro hd
  obtain ⟨g, hg, hgd⟩ := exists_disjoint_of_disjoint_traces
    (fun _ : ι => H) A (fun _ => hH) hι hA hcut (fun _ => hstable) f hf hd
  have hinj : Function.Injective g := by
    intro c d hcd
    by_contra hne
    have hs : Disjoint (g c) (g c) := by simpa only [hcd] using hgd hne
    have hz := card_eq_zero.mpr (disjoint_self.mp hs)
    have hp := hH (g c) (hg c)
    omega
  apply hfree
  refine ⟨univ.image g, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨c, _, rfl⟩ := mem_image.mp he
    exact hg c
  · rw [card_image_of_injective _ hinj, card_univ, hι]
  · intro e he f hf' hef
    obtain ⟨c, _, rfl⟩ := mem_image.mp he
    obtain ⟨d, _, rfl⟩ := mem_image.mp hf'
    exact hgd (fun h => hef (congrArg g h))

/-- The trace on an initial head of size r*k-1 cannot acquire a k-matching. -/
theorem trace_matchingFree {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H.image (fun e => e ∩ A) ∧
      M.card = k ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  rintro ⟨M, hM, hMk, hMd⟩
  have hw : ∀ t : M, ∃ e, e ∈ H ∧ e ∩ A = t.val := by
    intro t
    exact mem_image.mp (hM t.property)
  choose f hf hfa using hw
  apply no_indexed_trace_matching hr H A hH (by simpa using hMk) hA hcut hstable hfree f hf
  intro c d hcd
  rw [hfa c, hfa d]
  exact hMd c.val c.property d.val d.property (fun h => hcd (Subtype.ext h))

end Submissions.Erdos1020MatchingTrace.Main

-- Source: BlockSupportBody.lean
namespace Submissions.Erdos1020MatchingBlockSupport.Main

open Finset

def support {α : Type*} [DecidableEq α] {s : ℕ}
    (B : Fin s → Finset α) (S : Finset α) : Finset (Fin s) :=
  univ.filter (fun i => (S ∩ B i).Nonempty)

def region {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α) (M : Finset (Fin s)) : Finset α :=
  G ∪ M.biUnion B

@[simp] theorem mem_support {α : Type*} [DecidableEq α] {s : ℕ}
    (B : Fin s → Finset α) (S : Finset α) (i : Fin s) :
    i ∈ support B S ↔ (S ∩ B i).Nonempty := by simp [support]

theorem support_card_le_card {α : Type*} [DecidableEq α] {s : ℕ}
    (B : Fin s → Finset α) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (S : Finset α) : (support B S).card ≤ S.card := by
  classical
  have hex : ∀ i : support B S, ∃ x, x ∈ S ∧ x ∈ B i.val := by
    intro i
    obtain ⟨x, hx⟩ := (mem_support B S i).mp i.property
    exact ⟨x, (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
  choose f hfS hfB using hex
  let g : support B S → S := fun i => ⟨f i, hfS i⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hval : f i = f j := congrArg Subtype.val hij
    exact disjoint_left.mp (hB hne) (hfB i) (hval.symm ▸ hfB j)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

theorem subset_region_iff {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i))
    (S : Finset α) (hS : S ⊆ G ∪ univ.biUnion B) (M : Finset (Fin s)) :
    S ⊆ region G B M ↔ support B S ⊆ M := by
  constructor
  · intro hSM i hi
    obtain ⟨x, hx⟩ := (mem_support B S i).mp hi
    have hxS := (mem_inter.mp hx).1
    have hxB := (mem_inter.mp hx).2
    rcases mem_union.mp (hSM hxS) with hxG | hxU
    · exact (disjoint_left.mp (hG i) hxG hxB).elim
    · obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hxU
      by_cases hij : i = j
      · exact hij.symm ▸ hj
      · exact (disjoint_left.mp (hB hij) hxB hxj).elim
  · intro hCM x hxS
    rcases mem_union.mp (hS hxS) with hxG | hxU
    · exact mem_union_left _ hxG
    · obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxU
      have hi : i ∈ support B S := (mem_support B S i).mpr
        ⟨x, mem_inter.mpr ⟨hxS, hxi⟩⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, hCM hi, hxi⟩)

theorem region_card {α : Type*} [DecidableEq α] {s r : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (hBc : ∀ i, (B i).card = r)
    (M : Finset (Fin s)) : (region G B M).card = G.card + r * M.card := by
  have hd : Disjoint G (M.biUnion B) := by
    apply disjoint_left.mpr
    intro x hxG hxU
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxU
    exact disjoint_left.mp (hG i) hxG hxi
  rw [region, card_union_of_disjoint hd, card_biUnion (fun i _ j _ hij => hB hij)]
  simp [hBc, Nat.mul_comm]

theorem local_multiplicity_card {α : Type*} [DecidableEq α] {s r : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i))
    (S : Finset α) (hS : S ⊆ G ∪ univ.biUnion B) (hSr : S.card ≤ r) :
    (((univ : Finset (Fin s)).powersetCard r).filter
      (fun M => S ⊆ region G B M)).card =
        (s - (support B S).card).choose (r - (support B S).card) := by
  classical
  have heq : ((univ : Finset (Fin s)).powersetCard r).filter
      (fun M => S ⊆ region G B M) =
      ((univ : Finset (Fin s)).powersetCard r).filter (fun M => support B S ⊆ M) := by
    ext M
    simp only [mem_filter, subset_region_iff G B hB hG S hS M]
  rw [heq, card_filter_powersetCard_subset (support B S) univ r
    (subset_univ _) ((support_card_le_card B hB S).trans hSr), card_univ, Fintype.card_fin]

theorem support_pos_of_large_card {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i))
    (S : Finset α) (hS : S ⊆ G ∪ univ.biUnion B) (hcard : G.card < S.card) :
    0 < (support B S).card := by
  by_contra h
  have hzero : support B S = ∅ := card_eq_zero.mp (by omega)
  have hsub := (subset_region_iff G B hB hG S hS ∅).mpr (by simp [hzero])
  have hSG : S ⊆ G := by simpa [region] using hsub
  exact (not_le_of_gt hcard) (card_le_card hSG)

end Submissions.Erdos1020MatchingBlockSupport.Main

-- Source: ShortTransversalBody.lean
namespace Submissions.Erdos1020MatchingShortTransversal.Main

open Finset

/-- Lower chosen representatives independently in disjoint blocks. The fixed
remainder need only avoid the blocks whose representatives are being changed. -/
theorem lower_transversal {n : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset (Finset (Fin n)))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} F)
    (B : ι → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (a b : ι → Fin n) (ha : ∀ i, a i ∈ B i) (hb : ∀ i, b i ∈ B i)
    (hle : ∀ i, a i ≤ b i) (I : Finset ι) (R : Finset (Fin n))
    (hR : ∀ i ∈ I, Disjoint R (B i)) (hmem : R ∪ I.image b ∈ F) :
    R ∪ I.image a ∈ F := by
  classical
  induction I using Finset.induction_on generalizing R with
  | empty => simpa only [image_empty, union_empty] using hmem
  | @insert i I hi ih =>
    have hRi : Disjoint R (B i) := hR i (mem_insert_self _ _)
    have hR' : ∀ j ∈ I, Disjoint (insert (b i) R) (B j) := by
      intro j hj
      apply disjoint_insert_left.mpr
      refine ⟨?_, hR j (mem_insert_of_mem hj)⟩
      intro hbj
      exact disjoint_left.mp (hB (ne_of_mem_of_not_mem hj hi).symm) (hb i) hbj
    have hmem' : insert (b i) R ∪ I.image b ∈ F := by
      simpa only [image_insert, union_insert, insert_union] using hmem
    have hlow := ih (insert (b i) R) hR' hmem'
    have hfresh (v : Fin n) (hv : v ∈ B i) : v ∉ R ∪ I.image a := by
      intro hvU
      rcases mem_union.mp hvU with hvR | hvI
      · exact disjoint_left.mp hRi hvR hv
      · obtain ⟨j, hj, hjv⟩ := mem_image.mp hvI
        exact disjoint_left.mp (hB (ne_of_mem_of_not_mem hj hi).symm)
          hv (hjv ▸ ha j)
    have hlow' : insert (b i) (R ∪ I.image a) ∈ F := by
      simpa only [insert_union] using hlow
    have hfinal : insert (a i) (R ∪ I.image a) ∈ F := by
      by_cases heq : a i = b i
      · simpa only [heq] using hlow'
      · exact Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
          (hstable (a i) (b i) (lt_of_le_of_ne (hle i) heq))
          (hfresh (b i) (hb i)) (hfresh (a i) (ha i)) hlow'
    simpa only [image_insert, union_insert] using hfinal

/-- A trace selecting at most one point per block can be lowered to the set
of the minima of exactly its occupied blocks. No order comparison between
different blocks is needed. -/
theorem lower_trace_to_minima {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (B : Fin s → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hBA : ∀ i, B i ⊆ A)
    (a : Fin s → Fin n) (ha : ∀ i, a i ∈ B i)
    (hmin : ∀ i, ∀ x ∈ B i, a i ≤ x)
    (T : Finset (Fin n)) (hT : T ∈ H.image (fun e => e ∩ A))
    (hTU : T ⊆ univ.biUnion B)
    (htrans : ∀ i, (T ∩ B i).card ≤ 1) :
    (Submissions.Erdos1020MatchingBlockSupport.Main.support B T).image a ∈
      H.image (fun e => e ∩ A) := by
  classical
  let C := Submissions.Erdos1020MatchingBlockSupport.Main.support B T
  have hrep : ∀ i : C, ∃ x, x ∈ T ∧ x ∈ B i.val := by
    intro i
    obtain ⟨x, hx⟩ :=
      (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B T i).mp i.property
    exact ⟨x, (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
  choose b hbT hbB using hrep
  have hbimage : (univ : Finset C).image b = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact hbT i
    · intro hx
      obtain ⟨i, _, hxi⟩ := mem_biUnion.mp (hTU hx)
      have hi : i ∈ C :=
        (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B T i).mpr
          ⟨x, mem_inter.mpr ⟨hx, hxi⟩⟩
      refine mem_image.mpr ⟨⟨i, hi⟩, mem_univ _, ?_⟩
      exact card_le_one.mp (htrans i) (b ⟨i, hi⟩)
        (mem_inter.mpr ⟨hbT ⟨i, hi⟩, hbB ⟨i, hi⟩⟩) x (mem_inter.mpr ⟨hx, hxi⟩)
  have haimage : (univ : Finset C).image (fun i => a i.val) = C.image a := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨i.val, i.property, rfl⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨⟨i, hi⟩, mem_univ _, rfl⟩
  obtain ⟨e, heH, heT⟩ := mem_image.mp hT
  have hmem : (e \ A) ∪ (univ : Finset C).image b ∈ H := by
    rw [hbimage, ← heT, sdiff_union_inter]
    exact heH
  have hR : ∀ i ∈ (univ : Finset C), Disjoint (e \ A) (B i.val) := by
    intro i _
    apply disjoint_left.mpr
    intro x hx hxB
    exact (mem_sdiff.mp hx).2 (hBA i.val hxB)
  have hlow := lower_transversal H hstable (fun i : C => B i.val)
    (fun i j hij => hB (fun h => hij (Subtype.ext h)))
    (fun i : C => a i.val) b (fun i => ha i.val) hbB
    (fun i => hmin i.val (b i) (hbB i)) univ (e \ A) hR hmem
  rw [haimage] at hlow
  refine mem_image.mpr ⟨(e \ A) ∪ C.image a, hlow, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxU, hxA⟩ := mem_inter.mp hx
    rcases mem_union.mp hxU with hxR | hxC
    · exact ((mem_sdiff.mp hxR).2 hxA).elim
    · exact hxC
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_inter.mpr ⟨mem_union_right _ (mem_image.mpr ⟨i, hi, rfl⟩),
      hBA i (ha i)⟩

/-- An unmarked rectangular version of the transversal partition: there may
be any number of blocks, each of the same size q. -/
theorem rectangular_partition {α ι : Type*} [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (q : ℕ)
    (P : ι → Finset α) (hP : ∀ i, (P i).card = q)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ∃ Q : Fin q → Finset α,
      (∀ j, (Q j).card = Fintype.card ι) ∧
      Pairwise (fun j j' => Disjoint (Q j) (Q j')) ∧
      (∀ j i, (Q j ∩ P i).card = 1) ∧
      univ.biUnion Q = univ.biUnion P := by
  classical
  let L : ∀ i, P i ≃ Fin q := fun i => Finset.equivFinOfCardEq (hP i)
  let p : ι → Fin q → α := fun i j => ((L i).symm j).val
  have hp (i : ι) (j : Fin q) : p i j ∈ P i := ((L i).symm j).property
  have hp_eq (i i' : ι) (j j' : Fin q) (h : p i j = p i' j') :
      i = i' ∧ j = j' := by
    have hii : i = i' := by
      by_contra hne
      exact disjoint_left.mp (hdisj hne) (hp i j) (h.symm ▸ hp i' j')
    subst i'
    exact ⟨rfl, (L i).symm.injective (Subtype.ext h)⟩
  let Q : Fin q → Finset α := fun j => univ.image (fun i => p i j)
  have hQcard (j : Fin q) : (Q j).card = Fintype.card ι := by
    have hinj : Function.Injective (fun i => p i j) :=
      fun i i' h => (hp_eq i i' j j h).1
    simp only [Q, card_image_of_injective _ hinj, card_univ]
  have hQdisj : Pairwise (fun j j' => Disjoint (Q j) (Q j')) := by
    intro j j' hjj
    apply disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, _, hix⟩ := mem_image.mp hx
    obtain ⟨i', _, hi'x⟩ := mem_image.mp hx'
    exact hjj (hp_eq i i' j j' (hix.trans hi'x.symm)).2
  have hQblock (j : Fin q) (i : ι) : (Q j ∩ P i).card = 1 := by
    apply card_eq_one.mpr
    refine ⟨p i j, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, hxP⟩ := mem_inter.mp hx
      obtain ⟨i', _, hi'x⟩ := mem_image.mp hxQ
      have hii : i' = i := by
        by_contra hne
        exact disjoint_left.mp (hdisj hne) (hi'x ▸ hp i' j) hxP
      subst i'
      exact mem_singleton.mpr hi'x.symm
    · intro hx
      have hx' := mem_singleton.mp hx
      subst x
      exact mem_inter.mpr ⟨mem_image.mpr ⟨i, mem_univ _, rfl⟩, hp i j⟩
  refine ⟨Q, hQcard, hQdisj, hQblock, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, hxj⟩ := mem_biUnion.mp hx
    obtain ⟨i, _, hix⟩ := mem_image.mp hxj
    exact mem_biUnion.mpr ⟨i, mem_univ _, hix ▸ hp i j⟩
  · intro hx
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
    refine mem_biUnion.mpr ⟨(L i) ⟨x, hxi⟩, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨i, mem_univ _, ?_⟩
    simp [p]

/-- A short member, even the empty set, is distinct from every positive-rank
member of an indexed disjoint family, so adjoining it creates one extra edge. -/
theorem not_matchingFree_of_short_and_indexed {α ι : Type*}
    [DecidableEq α] [Fintype ι] [DecidableEq ι] {r s : ℕ}
    (hr : 0 < r) (F : Finset (Finset α)) (T : Finset α)
    (hT : T ∈ F) (hTc : T.card < r)
    (f : ι → Finset α) (hf : ∀ i, f i ∈ F) (hfc : ∀ i, (f i).card = r)
    (hfd : Pairwise (fun i j => Disjoint (f i) (f j)))
    (hTf : ∀ i, Disjoint T (f i)) (hι : Fintype.card ι = s) :
    ¬ (¬ ∃ K : Finset (Finset α), K ⊆ F ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e') := by
  classical
  intro hfree
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hz : (f i).card = 0 := card_eq_zero.mpr
      (disjoint_self.mp (by simpa only [hij] using hfd hne))
    have hp := hfc i
    omega
  have hTnot : T ∉ univ.image f := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_image.mp h
    have hc := hfc i
    rw [hi] at hc
    omega
  apply hfree
  refine ⟨insert T (univ.image f), ?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hT
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      exact hf i
  · rw [card_insert_of_notMem hTnot, card_image_of_injective _ hinj, card_univ, hι]
  · intro e he e' he' hee
    rcases mem_insert.mp he with rfl | he
    · rcases mem_insert.mp he' with rfl | he'
      · exact (hee rfl).elim
      · obtain ⟨j, _, rfl⟩ := mem_image.mp he'
        exact hTf j
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      rcases mem_insert.mp he' with rfl | he'
      · exact (hTf i).symm
      · obtain ⟨j, _, rfl⟩ := mem_image.mp he'
        exact hfd (fun h => hee (congrArg f h))

/-- If all full transversals of r local blocks are present, a short set of
their designated representatives cannot also be present. This finite lemma
contains no shiftedness or maximality premise; those supply its hub and
representative memberships when applied to the head trace. -/
theorem short_minima_impossible {α : Type*} [DecidableEq α] {r s : ℕ}
    (hr : 0 < r) (F : Finset (Finset α))
    (hfree : ¬ ∃ K : Finset (Finset α), K ⊆ F ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e')
    (G : Finset α) (hGc : G.card = r - 1)
    (B : Fin s → Finset α) (hBc : ∀ i, (B i).card = r)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (hBF : ∀ i, B i ∈ F)
    (a : Fin s → α) (ha : ∀ i, a i ∈ B i)
    (hhub : ∀ i, insert (a i) G ∈ F)
    (M C : Finset (Fin s)) (hMc : M.card = r)
    (hCM : C ⊆ M) (hCc : C.card < r) (hCF : C.image a ∈ F)
    (hfull : ∀ Q : Finset α, Q.card = r → Q ⊆ M.biUnion B →
      (∀ i ∈ M, (Q ∩ B i).card = 1) → Q ∈ F) : False := by
  classical
  obtain ⟨j, hjM, hjC⟩ : ∃ j, j ∈ M ∧ j ∉ C := by
    by_contra h
    have hMC : M ⊆ C := by
      intro j hj
      by_contra hj'
      exact h ⟨j, hj, hj'⟩
    have hc := card_le_card hMC
    omega
  let P : M → Finset α := fun i => (B i.val).erase (a i.val)
  have hPc (i : M) : (P i).card = r - 1 := by
    dsimp only [P]
    rw [card_erase_of_mem (ha i.val), hBc]
  have hPd : Pairwise (fun i j : M => Disjoint (P i) (P j)) := by
    intro i j hij
    exact (hBd (fun h => hij (Subtype.ext h))).mono (erase_subset _ _) (erase_subset _ _)
  obtain ⟨Q, hQc, hQd, hQPi, hQU⟩ := rectangular_partition (r - 1) P hPc hPd
  have hQpoint (l : Fin (r - 1)) {x : α} (hx : x ∈ Q l) :
      ∃ i : M, x ∈ (B i.val).erase (a i.val) := by
    have hxU : x ∈ univ.biUnion P := by
      rw [← hQU]
      exact mem_biUnion.mpr ⟨l, mem_univ _, hx⟩
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxU
    exact ⟨i, hxi⟩
  have hQsub (l : Fin (r - 1)) : Q l ⊆ M.biUnion B := by
    intro x hx
    obtain ⟨i, hxi⟩ := hQpoint l hx
    exact mem_biUnion.mpr ⟨i.val, i.property, mem_of_mem_erase hxi⟩
  have hQno (l : Fin (r - 1)) (i : Fin s) : a i ∉ Q l := by
    intro hx
    obtain ⟨i', hxi'⟩ := hQpoint l hx
    by_cases heq : i = i'.val
    · exact (mem_erase.mp hxi').1 (congrArg a heq)
    · exact disjoint_left.mp (hBd heq) (ha i) (mem_of_mem_erase hxi')
  have hQG (l : Fin (r - 1)) : Disjoint (Q l) G := by
    apply disjoint_left.mpr
    intro x hx hxG
    obtain ⟨i, hxi⟩ := hQpoint l hx
    exact disjoint_left.mp (hGB i.val) hxG (mem_of_mem_erase hxi)
  have hQout (l : Fin (r - 1)) (i : Fin s) (hi : i ∉ M) :
      Disjoint (Q l) (B i) := by
    apply disjoint_left.mpr
    intro x hx hxi
    obtain ⟨i', hxi'⟩ := hQpoint l hx
    exact disjoint_left.mp (hBd (fun h : i'.val = i => hi (h ▸ i'.property)))
      (mem_of_mem_erase hxi') hxi
  have hQF (l : Fin (r - 1)) : Q l ∈ F := by
    apply hfull (Q l) (by simpa only [Fintype.card_coe, hMc] using hQc l) (hQsub l)
    intro i hi
    have heq : Q l ∩ B i = Q l ∩ P ⟨i, hi⟩ := by
      ext x
      simp only [P, mem_inter, mem_erase]
      constructor
      · rintro ⟨hxQ, hxB⟩
        exact ⟨hxQ, (fun h => hQno l i (h ▸ hxQ)), hxB⟩
      · rintro ⟨hxQ, _, hxB⟩
        exact ⟨hxQ, hxB⟩
    rw [heq]
    exact hQPi l ⟨i, hi⟩
  let O := (univ : Finset (Fin s)) \ M
  let f₀ : Fin (r - 1) ⊕ O → Finset α := Sum.elim Q (fun i => B i.val)
  have hf₀ : ∀ i, f₀ i ∈ F := by
    intro i
    rcases i with l | i
    · exact hQF l
    · exact hBF i.val
  have hfc₀ : ∀ i, (f₀ i).card = r := by
    intro i
    rcases i with l | i
    · change (Q l).card = r
      simpa only [Fintype.card_coe, hMc] using hQc l
    · exact hBc i.val
  have hfd₀ : Pairwise (fun i i' => Disjoint (f₀ i) (f₀ i')) := by
    intro i i' hii
    rcases i with l | i <;> rcases i' with l' | i'
    · exact hQd (fun h => hii (congrArg Sum.inl h))
    · exact hQout l i'.val (mem_sdiff.mp i'.property).2
    · exact (hQout l' i.val (mem_sdiff.mp i.property).2).symm
    · exact hBd (fun h => hii (congrArg Sum.inr (Subtype.ext h)))
  let hub := insert (a j) G
  have hhubc : hub.card = r := by
    have hjG : a j ∉ G := fun h => disjoint_left.mp (hGB j) h (ha j)
    dsimp only [hub]
    rw [card_insert_of_notMem hjG, hGc]
    omega
  have hhubf₀ : ∀ i, Disjoint hub (f₀ i) := by
    intro i
    rcases i with l | i
    · exact disjoint_insert_left.mpr ⟨hQno l j, (hQG l).symm⟩
    · apply disjoint_insert_left.mpr
      refine ⟨?_, hGB i.val⟩
      intro hji
      exact disjoint_left.mp
        (hBd (fun h : j = i.val => (mem_sdiff.mp i.property).2 (h ▸ hjM))) (ha j) hji
  have hTaG : Disjoint (C.image a) G := by
    apply disjoint_left.mpr
    intro x hx hxG
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB i) hxG (ha i)
  have hTahub : Disjoint (C.image a) hub := by
    apply disjoint_insert_right.mpr
    refine ⟨?_, hTaG⟩
    intro h
    obtain ⟨i, hi, hij⟩ := mem_image.mp h
    by_cases heq : i = j
    · exact hjC (heq ▸ hi)
    · exact disjoint_left.mp (hBd heq) (ha i) (hij.symm ▸ ha j)
  have hTaf₀ : ∀ i, Disjoint (C.image a) (f₀ i) := by
    intro i
    rcases i with l | i
    · apply disjoint_left.mpr
      intro x hx hxQ
      obtain ⟨j', _, rfl⟩ := mem_image.mp hx
      exact hQno l j' hxQ
    · apply disjoint_left.mpr
      intro x hx hxi
      obtain ⟨j', hj', rfl⟩ := mem_image.mp hx
      exact disjoint_left.mp
        (hBd (fun h : j' = i.val => (mem_sdiff.mp i.property).2 (h ▸ hCM hj')))
        (ha j') hxi
  let f : Option (Fin (r - 1) ⊕ O) → Finset α :=
    fun i => match i with | none => hub | some i => f₀ i
  have hf : ∀ i, f i ∈ F := by
    intro i
    cases i with
    | none => exact hhub j
    | some i => exact hf₀ i
  have hfc : ∀ i, (f i).card = r := by
    intro i
    cases i with
    | none => exact hhubc
    | some i => exact hfc₀ i
  have hfd : Pairwise (fun i i' => Disjoint (f i) (f i')) := by
    intro i i' hii
    cases i with
    | none =>
      cases i' with
      | none => exact (hii rfl).elim
      | some i' => exact hhubf₀ i'
    | some i =>
      cases i' with
      | none => exact (hhubf₀ i).symm
      | some i' => exact hfd₀ (fun h => hii (congrArg some h))
  have hTf : ∀ i, Disjoint (C.image a) (f i) := by
    intro i
    cases i with
    | none => exact hTahub
    | some i => exact hTaf₀ i
  have hι : Fintype.card (Option (Fin (r - 1) ⊕ O)) = s := by
    have hrs : r ≤ s := by
      simpa only [hMc, card_univ, Fintype.card_fin] using card_le_card (subset_univ M)
    have hOc : O.card = s - r := by
      dsimp only [O]
      rw [card_sdiff_of_subset (subset_univ M), card_univ, Fintype.card_fin, hMc]
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_coe, hOc]
    omega
  exact not_matchingFree_of_short_and_indexed hr F (C.image a) hCF
    ((card_image_le).trans_lt hCc) f hf hfc hfd hTf hι hfree

/-- The local short-transversal exclusion. The local containment premise is
essential: a short transversal using blocks outside M is not excluded by
full transversals on M alone. Hub membership is supplied by the separate
minimum-gap lemma. -/
theorem short_transversal_not_mem {n r s : ℕ} (hr : 2 ≤ r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e')
    (G : Finset (Fin n)) (hGA : G ⊆ A) (hGc : G.card = r - 1)
    (B : Fin s → Finset (Fin n)) (hBH : ∀ i, B i ∈ H)
    (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i))
    (a : Fin s → Fin n) (ha : ∀ i, a i ∈ B i)
    (hmin : ∀ i, ∀ x ∈ B i, a i ≤ x)
    (hhub : ∀ i, insert (a i) G ∈ H)
    (M : Finset (Fin s)) (hMc : M.card = r)
    (hfull : ∀ Q : Finset (Fin n), Q.card = r → Q ⊆ M.biUnion B →
      (∀ i ∈ M, (Q ∩ B i).card = 1) → Q ∈ H.image (fun e => e ∩ A))
    (T : Finset (Fin n)) (hlocal : T ⊆ G ∪ M.biUnion B)
    (hTG : Disjoint T G) (htrans : ∀ i, (T ∩ B i).card ≤ 1)
    (hTc : T.card < r) : T ∉ H.image (fun e => e ∩ A) := by
  classical
  intro hT
  let C := Submissions.Erdos1020MatchingBlockSupport.Main.support B T
  have hTlocal : T ⊆ M.biUnion B := by
    intro x hx
    rcases mem_union.mp (hlocal hx) with hxG | hxM
    · exact (disjoint_left.mp hTG hx hxG).elim
    · exact hxM
  have hTU : T ⊆ univ.biUnion B := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp (hTlocal hx)
    exact mem_biUnion.mpr ⟨i, mem_univ _, hxi⟩
  have hCM : C ⊆ M := by
    intro i hi
    obtain ⟨x, hx⟩ :=
      (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B T i).mp hi
    obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp (hTlocal (mem_inter.mp hx).1)
    by_cases hij : i = j
    · exact hij.symm ▸ hj
    · exact (disjoint_left.mp (hBd hij) (mem_inter.mp hx).2 hxj).elim
  have hCc : C.card < r :=
    (Submissions.Erdos1020MatchingBlockSupport.Main.support_card_le_card B hBd T).trans_lt hTc
  have hCF : C.image a ∈ H.image (fun e => e ∩ A) :=
    lower_trace_to_minima H A hstable B hBd hBA a ha hmin T hT hTU htrans
  have hBtrace (i : Fin s) : B i ∈ H.image (fun e => e ∩ A) :=
    mem_image.mpr ⟨B i, hBH i, inter_eq_left.mpr (hBA i)⟩
  have hhubtrace (i : Fin s) : insert (a i) G ∈ H.image (fun e => e ∩ A) :=
    mem_image.mpr ⟨insert (a i) G, hhub i,
      inter_eq_left.mpr (insert_subset (hBA i (ha i)) hGA)⟩
  exact short_minima_impossible (by omega) (H.image (fun e => e ∩ A))
    (Submissions.Erdos1020MatchingTrace.Main.trace_matchingFree
      (by omega) H A hH hA hcut hstable hfree)
    G hGc B (fun i => hH (B i) (hBH i)) hBd hGB hBtrace
    a ha hhubtrace M C hMc hCM hCc hCF hfull

end Submissions.Erdos1020MatchingShortTransversal.Main


namespace Submissions.Erdos1020TransversalPartition.Main

open Finset

/-- Partition equally sized disjoint blocks into transversals, separating every
marked vertex when there are at most as many marks as transversals. -/
theorem exists_partition {α : Type*} [DecidableEq α] (r : ℕ)
    (B : Fin r → Finset α) (hB : ∀ i, (B i).card = r)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (T : Finset α) (hT : T.card ≤ r) :
    ∃ Q : Fin r → Finset α, (∀ j, (Q j).card = r) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
      (∀ j i, (Q j ∩ B i).card = 1) ∧
      (∀ j, (Q j ∩ T).card ≤ 1) ∧
      univ.biUnion Q = univ.biUnion B := by
  classical
  obtain ⟨l⟩ := Function.Embedding.nonempty_of_card_le (α := T) (β := Fin r)
    (by simpa only [Fintype.card_coe, Fintype.card_fin] using hT)
  have hlabels : ∀ i, ∃ L : B i ≃ Fin r,
      ∀ x : B i, ∀ hx : x.val ∈ T, L x = l ⟨x.val, hx⟩ := by
    intro i
    let e : B i ≃ Fin r := Finset.equivFinOfCardEq (hB i)
    let f : ↥(B i ∩ T) → Fin r := fun x => e ⟨x.val, (mem_inter.mp x.property).1⟩
    let g : ↥(B i ∩ T) → Fin r := fun x => l ⟨x.val, (mem_inter.mp x.property).2⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : B i => z.val) (e.injective h)
    have hg : Function.Injective g := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : T => z.val) (l.injective h)
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    refine ⟨e.trans σ, ?_⟩
    intro x hx
    exact hσ ⟨x.val, mem_inter.mpr ⟨x.property, hx⟩⟩
  choose L hL using hlabels
  let p : Fin r → Fin r → α := fun i j => ((L i).symm j).val
  have hp (i j : Fin r) : p i j ∈ B i := ((L i).symm j).property
  have hp_eq (i i' j j' : Fin r) (h : p i j = p i' j') : i = i' ∧ j = j' := by
    have hii : i = i' := by
      by_contra hne
      exact disjoint_left.mp (hdisj hne) (hp i j) (h.symm ▸ hp i' j')
    subst i'
    exact ⟨rfl, (L i).symm.injective (Subtype.ext h)⟩
  let Q : Fin r → Finset α := fun j => univ.image (fun i => p i j)
  have hQcard (j : Fin r) : (Q j).card = r := by
    have hinj : Function.Injective (fun i => p i j) :=
      fun i i' h => (hp_eq i i' j j h).1
    simp only [Q, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hQdisj : Pairwise (fun j j' => Disjoint (Q j) (Q j')) := by
    intro j j' hjj
    apply disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, _, hix⟩ := mem_image.mp hx
    obtain ⟨i', _, hi'x⟩ := mem_image.mp hx'
    exact hjj (hp_eq i i' j j' (hix.trans hi'x.symm)).2
  have hQblock (j i : Fin r) : (Q j ∩ B i).card = 1 := by
    apply card_eq_one.mpr
    refine ⟨p i j, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ, hxB⟩ := mem_inter.mp hx
      obtain ⟨i', _, hi'x⟩ := mem_image.mp hxQ
      have hii : i' = i := by
        by_contra hne
        exact disjoint_left.mp (hdisj hne) (hi'x ▸ hp i' j) hxB
      subst i'
      exact mem_singleton.mpr hi'x.symm
    · intro hx
      have hx' := mem_singleton.mp hx
      subst x
      exact mem_inter.mpr ⟨mem_image.mpr ⟨i, mem_univ _, rfl⟩, hp i j⟩
  have hQmarked (j : Fin r) : (Q j ∩ T).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxQ, hxT⟩ := mem_inter.mp hx
    obtain ⟨hyQ, hyT⟩ := mem_inter.mp hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hxQ
    obtain ⟨i', _, rfl⟩ := mem_image.mp hyQ
    have hlx : l ⟨p i j, hxT⟩ = j := by
      rw [← hL i ((L i).symm j) hxT]
      exact (L i).apply_symm_apply j
    have hly : l ⟨p i' j, hyT⟩ = j := by
      rw [← hL i' ((L i').symm j) hyT]
      exact (L i').apply_symm_apply j
    exact congrArg Subtype.val (l.injective (hlx.trans hly.symm))
  refine ⟨Q, hQcard, hQdisj, hQblock, hQmarked, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, hxj⟩ := mem_biUnion.mp hx
    obtain ⟨i, _, hix⟩ := mem_image.mp hxj
    exact mem_biUnion.mpr ⟨i, mem_univ _, hix ▸ hp i j⟩
  · intro hx
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
    refine mem_biUnion.mpr ⟨(L i) ⟨x, hxi⟩, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨i, mem_univ _, ?_⟩
    simp [p]

end Submissions.Erdos1020TransversalPartition.Main

namespace Submissions.Erdos1020GapFilling.Main

open Finset

/-- Replace the unique marked point of each transversal by a distinct unused
gap point, obtaining disjoint rank-r sets that avoid the marked set. -/
theorem exists_filling {α : Type*} [DecidableEq α] (r : ℕ)
    (B : Fin r → Finset α) (hB : ∀ i, (B i).card = r)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (G : Finset α) (hG : G.card = r - 1)
    (hGB : ∀ i, Disjoint G (B i)) (T : Finset α) (hT : T.card < r) :
    ∃ Q E : Fin r → Finset α, (∀ j, (Q j).card = r) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
      (∀ j i, (Q j ∩ B i).card = 1) ∧
      (∀ j, (Q j ∩ T).card ≤ 1) ∧
      univ.biUnion Q = univ.biUnion B ∧
      (∀ j, (E j).card = r) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (∀ j, Disjoint T (E j)) ∧
      (∀ j, E j = Q j ∨ ∃ x ∈ Q j ∩ T, ∃ y ∈ G \ T,
        E j = insert y ((Q j).erase x)) := by
  classical
  obtain ⟨Q, hQc, hQd, hQB, hQT, hQU⟩ :=
    Submissions.Erdos1020TransversalPartition.Main.exists_partition
      r B hB hdisj T hT.le
  have hcap : (T \ G).card ≤ (G \ T).card :=
    card_sdiff_le_card_sdiff_iff.mpr (by omega)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := ↥(T \ G)) (β := ↥(G \ T))
    (by simpa only [Fintype.card_coe] using hcap)
  have hGQ (j : Fin r) : Disjoint G (Q j) := by
    apply disjoint_left.mpr
    intro x hxG hxQ
    have hxU : x ∈ univ.biUnion Q := mem_biUnion.mpr ⟨j, mem_univ _, hxQ⟩
    rw [hQU] at hxU
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxU
    exact disjoint_left.mp (hGB i) hxG hxi
  have hnew (j : Fin r) (a : ↥(T \ G)) : (f a).val ∉ Q j := by
    intro h
    exact disjoint_left.mp (hGQ j) (mem_sdiff.mp (f a).property).1 h
  have hmake : ∀ j : Fin r, ∃ e : Finset α, e.card = r ∧ Disjoint T e ∧
      (e = Q j ∨ ∃ a : ↥(T \ G), a.val ∈ Q j ∧
        e = insert (f a).val ((Q j).erase a.val)) := by
    intro j
    by_cases h : (Q j ∩ T).Nonempty
    · obtain ⟨x, hx⟩ := h
      have hxQ := (mem_inter.mp hx).1
      have hxT := (mem_inter.mp hx).2
      have hxG : x ∉ G := fun h => disjoint_left.mp (hGQ j) h hxQ
      let a : ↥(T \ G) := ⟨x, mem_sdiff.mpr ⟨hxT, hxG⟩⟩
      refine ⟨insert (f a).val ((Q j).erase x), ?_, ?_, Or.inr ⟨a, hxQ, rfl⟩⟩
      · rw [card_insert_of_notMem (notMem_mono (erase_subset _ _) (hnew j a)),
          card_erase_of_mem hxQ, hQc j]
        omega
      · refine disjoint_insert_right.mpr ⟨(mem_sdiff.mp (f a).property).2, ?_⟩
        apply disjoint_left.mpr
        intro z hzT hz
        have hzx : z = x := card_le_one.mp (hQT j) z
          (mem_inter.mpr ⟨mem_of_mem_erase hz, hzT⟩) x hx
        exact (mem_erase.mp hz).1 hzx
    · refine ⟨Q j, hQc j, ?_, Or.inl rfl⟩
      exact disjoint_left.mpr fun x hxT hxQ => h ⟨x, mem_inter.mpr ⟨hxQ, hxT⟩⟩
  choose E hEc hET hErule using hmake
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    rcases hErule i with hi | ⟨a, ha, hi⟩
    · rcases hErule j with hj | ⟨b, hb, hj⟩
      · rw [hi, hj]
        exact hQd hij
      · rw [hi, hj]
        exact disjoint_insert_right.mpr ⟨hnew i b,
          (hQd hij).mono (Subset.refl _) (erase_subset _ _)⟩
    · rcases hErule j with hj | ⟨b, hb, hj⟩
      · rw [hi, hj]
        exact disjoint_insert_left.mpr ⟨hnew j a,
          (hQd hij).mono (erase_subset _ _) (Subset.refl _)⟩
      · have hab : (f a).val ≠ (f b).val := by
          intro hab
          have hab' : a = b := f.injective (Subtype.ext hab)
          exact disjoint_left.mp (hQd hij) ha (hab'.symm ▸ hb)
        rw [hi, hj]
        apply disjoint_insert_left.mpr
        refine ⟨?_, disjoint_insert_right.mpr ⟨?_,
          (hQd hij).mono (erase_subset _ _) (erase_subset _ _)⟩⟩
        · simpa only [mem_insert, not_or] using
            And.intro hab (notMem_mono (erase_subset _ _) (hnew j a))
        · exact notMem_mono (erase_subset _ _) (hnew i b)
  refine ⟨Q, E, hQc, hQd, hQB, hQT, hQU, hEc, hEd, hET, ?_⟩
  intro j
  rcases hErule j with h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a.val, mem_inter.mpr ⟨ha, (mem_sdiff.mp a.property).1⟩,
      (f a).val, (f a).property, h⟩

end Submissions.Erdos1020GapFilling.Main


namespace Submissions.Erdos1020MatchingSupportTransversal.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

theorem card_eq_gap_add_sum {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (S : Finset α)
    (hS : S ⊆ G ∪ univ.biUnion B) :
    S.card = (S ∩ G).card + ∑ i ∈ support B S, (S ∩ B i).card := by
  have hp : S = (S ∩ G) ∪ (support B S).biUnion (fun i => S ∩ B i) := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp (hS hx) with hxG | hxU
      · exact mem_union_left _ (mem_inter.mpr ⟨hx, hxG⟩)
      · obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxU
        have hi := (mem_support B S i).mpr ⟨x, mem_inter.mpr ⟨hx, hxi⟩⟩
        exact mem_union_right _ (mem_biUnion.mpr ⟨i, hi, mem_inter.mpr ⟨hx, hxi⟩⟩)
    · intro hx
      rcases mem_union.mp hx with hxG | hxU
      · exact (mem_inter.mp hxG).1
      · obtain ⟨_, _, hxi⟩ := mem_biUnion.mp hxU
        exact (mem_inter.mp hxi).1
  have hd : Disjoint (S ∩ G) ((support B S).biUnion (fun i => S ∩ B i)) := by
    apply disjoint_left.mpr
    intro x hxG hxU
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxU
    exact disjoint_left.mp (hG i) (mem_inter.mp hxG).2 (mem_inter.mp hxi).2
  calc
    S.card = ((S ∩ G) ∪ (support B S).biUnion (fun i => S ∩ B i)).card := congrArg card hp
    _ = _ := by
      rw [card_union_of_disjoint hd,
        card_biUnion (fun i _ j _ hij => (hB hij).mono inter_subset_right inter_subset_right)]

theorem transversal_of_support_card_eq {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (S : Finset α)
    (hS : S ⊆ G ∪ univ.biUnion B) (heq : (support B S).card = S.card) :
    Disjoint S G ∧ ∀ i, (S ∩ B i).card ≤ 1 := by
  have hcard := card_eq_gap_add_sum G B hB hG S hS
  have hpos (i : Fin s) (hi : i ∈ support B S) : 1 ≤ (S ∩ B i).card :=
    card_pos.mpr ((mem_support B S i).mp hi)
  have hsum : (support B S).card ≤ ∑ i ∈ support B S, (S ∩ B i).card := by
    calc
      _ = ∑ i ∈ support B S, (1 : ℕ) := by simp
      _ ≤ _ := sum_le_sum hpos
  have hzero : (S ∩ G).card = 0 := by omega
  refine ⟨disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hzero), ?_⟩
  intro i
  by_cases hi : i ∈ support B S
  · by_contra hlarge
    have hlt : (∑ j ∈ support B S, (1 : ℕ)) <
        ∑ j ∈ support B S, (S ∩ B j).card :=
      sum_lt_sum hpos ⟨i, hi, by omega⟩
    simp at hlt
    omega
  · have hempty : S ∩ B i = ∅ := by
      by_contra hne
      exact hi ((mem_support B S i).mpr (nonempty_iff_ne_empty.mpr hne))
    simp [hempty]

theorem support_card_eq_of_transversal {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (S : Finset α)
    (hS : S ⊆ G ∪ univ.biUnion B)
    (hSG : Disjoint S G) (htrans : ∀ i, (S ∩ B i).card ≤ 1) :
    (support B S).card = S.card := by
  have hcard := card_eq_gap_add_sum G B hB hG S hS
  rw [disjoint_iff_inter_eq_empty.mp hSG, card_empty, zero_add] at hcard
  have hc : ∀ i ∈ support B S, (S ∩ B i).card = 1 := by
    intro i hi
    have hp := card_pos.mpr ((mem_support B S i).mp hi)
    exact Nat.le_antisymm (htrans i) hp
  have hs : (∑ i ∈ support B S, (S ∩ B i).card) = (support B S).card := by
    calc
      _ = ∑ i ∈ support B S, (1 : ℕ) := sum_congr rfl hc
      _ = _ := by simp
  exact hs.symm.trans hcard.symm

theorem support_eq_of_full {α : Type*} [DecidableEq α] {s : ℕ}
    (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (M : Finset (Fin s)) (Q : Finset α) (hQ : Q ⊆ M.biUnion B)
    (hfull : ∀ i ∈ M, (Q ∩ B i).card = 1) : support B Q = M := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx⟩ := (mem_support B Q i).mp hi
    obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp (hQ (mem_inter.mp hx).1)
    by_cases hij : i = j
    · exact hij.symm ▸ hj
    · exact (disjoint_left.mp (hB hij) (mem_inter.mp hx).2 hxj).elim
  · intro hi
    exact (mem_support B Q i).mpr (card_pos.mp (by rw [hfull i hi]; omega))

end Submissions.Erdos1020MatchingSupportTransversal.Main

namespace Submissions.Erdos1020MatchingGapSupport.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingSupportTransversal.Main

/-- Replacing one point of a full transversal by a gap point removes exactly
its block from the support. -/
theorem support_replace_eq_erase {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i))
    (M : Finset (Fin s)) (Q : Finset α) (hQ : Q ⊆ M.biUnion B)
    (hfull : ∀ i ∈ M, (Q ∩ B i).card = 1)
    (i : Fin s) (x y : α) (hxQ : x ∈ Q) (hxi : x ∈ B i) (hyG : y ∈ G) :
    support B (insert y (Q.erase x)) = M.erase i := by
  have hQM := support_eq_of_full B hB M Q hQ hfull
  have hiM : i ∈ M := by
    rw [← hQM]
    exact (mem_support B Q i).mpr ⟨x, mem_inter.mpr ⟨hxQ, hxi⟩⟩
  ext j
  constructor
  · intro hj
    obtain ⟨z, hz⟩ := (mem_support B (insert y (Q.erase x)) j).mp hj
    have hzB := (mem_inter.mp hz).2
    have hzE : z ∈ Q.erase x := by
      rcases mem_insert.mp (mem_inter.mp hz).1 with hzy | hzE
      · exact (disjoint_left.mp (hG j) (hzy.symm ▸ hyG) hzB).elim
      · exact hzE
    have hjM : j ∈ M := by
      rw [← hQM]
      exact (mem_support B Q j).mpr ⟨z, mem_inter.mpr ⟨mem_of_mem_erase hzE, hzB⟩⟩
    refine mem_erase.mpr ⟨?_, hjM⟩
    intro hji
    subst j
    have hzx : z = x := card_le_one.mp (le_of_eq (hfull i hiM)) z
      (mem_inter.mpr ⟨mem_of_mem_erase hzE, hzB⟩) x (mem_inter.mpr ⟨hxQ, hxi⟩)
    exact (mem_erase.mp hzE).1 hzx
  · intro hj
    obtain ⟨hji, hjM⟩ := mem_erase.mp hj
    have hjQ : j ∈ support B Q := by rwa [hQM]
    obtain ⟨z, hz⟩ := (mem_support B Q j).mp hjQ
    have hzx : z ≠ x := by
      intro hzx
      exact disjoint_left.mp (hB hji) (hzx ▸ (mem_inter.mp hz).2) hxi
    exact (mem_support B (insert y (Q.erase x)) j).mpr
      ⟨z, mem_inter.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨hzx, (mem_inter.mp hz).1⟩),
        (mem_inter.mp hz).2⟩⟩

end Submissions.Erdos1020MatchingGapSupport.Main

namespace Submissions.Erdos1020MatchingGapExclusion.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingSupportTransversal.Main
open Submissions.Erdos1020MatchingGapSupport.Main

/-- If every local rank-r set of width r or r-1 is present, no short local
member can remain in a family with no matching of size s+1. -/
theorem short_not_mem {α : Type*} [DecidableEq α] {r s : ℕ}
    (F : Finset (Finset α))
    (hfree : ¬ ∃ K : Finset (Finset α), K ⊆ F ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e')
    (G : Finset α) (hGc : G.card = r - 1)
    (B : Fin s → Finset α) (hBc : ∀ i, (B i).card = r)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (hBF : ∀ i, B i ∈ F)
    (M : Finset (Fin s)) (hMc : M.card = r)
    (hfull : ∀ S : Finset α, S.card = r → S ⊆ G ∪ M.biUnion B →
      (support B S).card = r → S ∈ F)
    (hgap : ∀ S : Finset α, S.card = r → S ⊆ G ∪ M.biUnion B →
      (support B S).card = r - 1 → S ∈ F)
    (T : Finset α) (hlocal : T ⊆ G ∪ M.biUnion B) (hTc : T.card < r) :
    T ∉ F := by
  classical
  intro hT
  let L : M ≃ Fin r := Finset.equivFinOfCardEq hMc
  let b : Fin r → Finset α := fun i => B (L.symm i).val
  have hbc (i : Fin r) : (b i).card = r := hBc (L.symm i).val
  have hbd : Pairwise (fun i j => Disjoint (b i) (b j)) := by
    intro i j hij
    exact hBd (fun h => hij (L.symm.injective (Subtype.ext h)))
  have hGb (i : Fin r) : Disjoint G (b i) := hGB (L.symm i).val
  have hbu : univ.biUnion b = M.biUnion B := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨(L.symm i).val, (L.symm i).property, hxi⟩
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
      refine mem_biUnion.mpr ⟨L ⟨i, hi⟩, mem_univ _, ?_⟩
      simpa only [b, Equiv.symm_apply_apply] using hxi
  obtain ⟨Q, E, hQc, hQd, hQB, hQT, hQU, hEc, hEd, hET, hErule⟩ :=
    Submissions.Erdos1020GapFilling.Main.exists_filling
      r b hbc hbd G hGc hGb T hTc
  have hQsub (j : Fin r) : Q j ⊆ M.biUnion B := by
    intro x hx
    have hxU : x ∈ univ.biUnion Q := mem_biUnion.mpr ⟨j, mem_univ _, hx⟩
    rwa [hQU, hbu] at hxU
  have hQfull (j : Fin r) (i : Fin s) (hi : i ∈ M) : (Q j ∩ B i).card = 1 := by
    simpa only [b, Equiv.symm_apply_apply] using hQB j (L ⟨i, hi⟩)
  have hQsupport (j : Fin r) : support B (Q j) = M :=
    support_eq_of_full B hBd M (Q j) (hQsub j) (hQfull j)
  have hElocal (j : Fin r) : E j ⊆ G ∪ M.biUnion B := by
    intro z hz
    rcases hErule j with h | ⟨x, hx, y, hy, h⟩
    · rw [h] at hz
      exact mem_union_right _ (hQsub j hz)
    · rw [h] at hz
      rcases mem_insert.mp hz with hzy | hz
      · exact mem_union_left _ (hzy.symm ▸ (mem_sdiff.mp hy).1)
      · exact mem_union_right _ (hQsub j (mem_of_mem_erase hz))
  have hEF (j : Fin r) : E j ∈ F := by
    rcases hErule j with h | ⟨x, hx, y, hy, h⟩
    · apply hfull (E j) (hEc j) (hElocal j)
      rw [h, hQsupport j, hMc]
    · have hxQ := (mem_inter.mp hx).1
      obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp (hQsub j hxQ)
      have hs := support_replace_eq_erase G B hBd hGB M (Q j)
        (hQsub j) (hQfull j) i x y hxQ hxi (mem_sdiff.mp hy).1
      apply hgap (E j) (hEc j) (hElocal j)
      rw [h, hs, card_erase_of_mem hi, hMc]
  have hlocalout (i : Fin s) (hi : i ∉ M) : Disjoint (G ∪ M.biUnion B) (B i) := by
    apply disjoint_union_left.mpr
    refine ⟨hGB i, disjoint_left.mpr ?_⟩
    intro x hx hxi
    obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
    exact disjoint_left.mp (hBd (fun h : j = i => hi (h ▸ hj))) hxj hxi
  have hEout (j : Fin r) (i : Fin s) (hi : i ∉ M) : Disjoint (E j) (B i) :=
    (hlocalout i hi).mono (hElocal j) (Subset.refl _)
  have hTout (i : Fin s) (hi : i ∉ M) : Disjoint T (B i) :=
    (hlocalout i hi).mono hlocal (Subset.refl _)
  let O := (univ : Finset (Fin s)) \ M
  let f : Fin r ⊕ O → Finset α := Sum.elim E (fun i => B i.val)
  have hf : ∀ i, f i ∈ F := by
    intro i
    rcases i with j | i
    · exact hEF j
    · exact hBF i.val
  have hfc : ∀ i, (f i).card = r := by
    intro i
    rcases i with j | i
    · exact hEc j
    · exact hBc i.val
  have hfd : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    rcases i with l | i <;> rcases j with l' | j
    · exact hEd (fun h => hij (congrArg Sum.inl h))
    · exact hEout l j.val (mem_sdiff.mp j.property).2
    · exact (hEout l' i.val (mem_sdiff.mp i.property).2).symm
    · exact hBd (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
  have hTf : ∀ i, Disjoint T (f i) := by
    intro i
    rcases i with j | i
    · exact hET j
    · exact hTout i.val (mem_sdiff.mp i.property).2
  have hι : Fintype.card (Fin r ⊕ O) = s := by
    have hrs : r ≤ s := by
      simpa only [hMc, card_univ, Fintype.card_fin] using card_le_card (subset_univ M)
    have hOc : O.card = s - r := by
      dsimp only [O]
      rw [card_sdiff_of_subset (subset_univ M), card_univ, Fintype.card_fin, hMc]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hOc]
    omega
  exact Submissions.Erdos1020MatchingShortTransversal.Main.not_matchingFree_of_short_and_indexed
    (by omega) F T hT hTc f hf hfc hfd hTf hι hfree

end Submissions.Erdos1020MatchingGapExclusion.Main

namespace Submissions.Erdos1020MatchingTraceLocalStructure.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingSupportTransversal.Main

/-- Full local rank-r width-r traces force every short local trace to have
strictly smaller width than cardinality. -/
theorem short_width_lt {n r s : ℕ} (hr : 2 ≤ r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e')
    (G : Finset (Fin n)) (hGA : G ⊆ A) (hGc : G.card = r - 1)
    (B : Fin s → Finset (Fin n)) (hBH : ∀ i, B i ∈ H)
    (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i))
    (a : Fin s → Fin n) (ha : ∀ i, a i ∈ B i)
    (hmin : ∀ i, ∀ x ∈ B i, a i ≤ x)
    (hhub : ∀ i, insert (a i) G ∈ H)
    (M : Finset (Fin s)) (hMc : M.card = r)
    (hfull : ∀ S : Finset (Fin n), S.card = r → S ⊆ region G B M →
      (support B S).card = r → S ∈ H.image (fun e => e ∩ A))
    (T : Finset (Fin n)) (hT : T ∈ H.image (fun e => e ∩ A))
    (hlocal : T ⊆ region G B M) (hTc : T.card < r) :
    (support B T).card < T.card := by
  have hle := support_card_le_card B hBd T
  by_contra hnlt
  have heq : (support B T).card = T.card := by omega
  have hTU : T ⊆ G ∪ univ.biUnion B := by
    intro x hx
    rcases mem_union.mp (hlocal hx) with hxG | hxM
    · exact mem_union_left _ hxG
    · obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxM
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, hxi⟩)
  obtain ⟨hTG, htrans⟩ := transversal_of_support_card_eq G B hBd hGB T hTU heq
  have hfull' : ∀ Q : Finset (Fin n), Q.card = r → Q ⊆ M.biUnion B →
      (∀ i ∈ M, (Q ∩ B i).card = 1) → Q ∈ H.image (fun e => e ∩ A) := by
    intro Q hQc hQsub hQtrans
    apply hfull Q hQc (fun x hx => mem_union_right _ (hQsub hx))
    rw [support_eq_of_full B hBd M Q hQsub hQtrans, hMc]
  exact Submissions.Erdos1020MatchingShortTransversal.Main.short_transversal_not_mem
    hr H A hH hA hcut hstable hfree G hGA hGc B hBH hBA hBd hGB
    a ha hmin hhub M hMc hfull' T hlocal hTG htrans hTc hT

/-- The two full-rank width classes together exclude every short local trace. -/
theorem short_not_mem {n r s : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e')
    (G : Finset (Fin n)) (hGc : G.card = r - 1)
    (B : Fin s → Finset (Fin n)) (hBH : ∀ i, B i ∈ H)
    (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i))
    (M : Finset (Fin s)) (hMc : M.card = r)
    (hfull : ∀ S : Finset (Fin n), S.card = r → S ⊆ region G B M →
      (support B S).card = r → S ∈ H.image (fun e => e ∩ A))
    (hgap : ∀ S : Finset (Fin n), S.card = r → S ⊆ region G B M →
      (support B S).card = r - 1 → S ∈ H.image (fun e => e ∩ A))
    (T : Finset (Fin n)) (hlocal : T ⊆ region G B M) (hTc : T.card < r) :
    T ∉ H.image (fun e => e ∩ A) := by
  have htrace := Submissions.Erdos1020MatchingTrace.Main.trace_matchingFree
    hr H A hH hA hcut hstable hfree
  have hBtrace (i : Fin s) : B i ∈ H.image (fun e => e ∩ A) :=
    mem_image.mpr ⟨B i, hBH i, inter_eq_left.mpr (hBA i)⟩
  exact Submissions.Erdos1020MatchingGapExclusion.Main.short_not_mem
    (H.image (fun e => e ∩ A)) htrace G hGc B (fun i => hH (B i) (hBH i))
    hBd hGB hBtrace M hMc hfull hgap T hlocal hTc

end Submissions.Erdos1020MatchingTraceLocalStructure.Main

namespace Submissions.Erdos1020NearPerfectWeights.Main

/-- The first short-trace weight estimate with its denominator cleared. -/
theorem short_weight_bound {N t h : ℕ} (hh : 1 ≤ h) (hNt : N ≤ t) :
    t * N.choose h ≤ N * (t + h - 1).choose h := by
  induction h, hh using Nat.le_induction with
  | base =>
    simpa only [Nat.add_sub_cancel, Nat.choose_one_right] using
      (le_of_eq (Nat.mul_comm t N))
  | succ h hh ih =>
    have hnum := Nat.choose_succ_right_eq N h
    have htop : t + h - 1 + 1 = t + h := by omega
    have hnext : t + (h + 1) - 1 = t + h := by omega
    have hden : (t + h) * (t + h - 1).choose h =
        (t + (h + 1) - 1).choose (h + 1) * (h + 1) := by
      simpa only [htop, hnext] using Nat.add_one_mul_choose_eq (t + h - 1) h
    have hcoeff : N - h ≤ t + h := by omega
    apply Nat.le_of_mul_le_mul_right (c := h + 1) ?_ (by omega)
    calc
      (t * N.choose (h + 1)) * (h + 1) =
          (t * N.choose h) * (N - h) := by
        rw [Nat.mul_assoc, hnum, ← Nat.mul_assoc]
      _ ≤ (N * (t + h - 1).choose h) * (N - h) :=
        Nat.mul_le_mul_right _ ih
      _ ≤ (N * (t + h - 1).choose h) * (t + h) :=
        Nat.mul_le_mul_left _ hcoeff
      _ = N * ((t + h) * (t + h - 1).choose h) := by ac_rfl
      _ = (N * (t + (h + 1) - 1).choose (h + 1)) * (h + 1) := by
        rw [hden, ← Nat.mul_assoc]

/-- The short nontransversal weight estimate with its denominator cleared. -/
theorem short_nontransversal_weight_bound {N t h : ℕ} (hh : 1 ≤ h)
    (hNt : 2 * N ≤ t) :
    t * (t + 1) * N.choose h ≤ 2 * N * (t + h).choose (h + 1) := by
  induction h, hh using Nat.le_induction with
  | base =>
    have hden : (t + 1) * t = (t + 1).choose 2 * 2 := by
      simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq t 1
    simp only [Nat.choose_one_right]
    apply le_of_eq
    calc
      t * (t + 1) * N = N * ((t + 1) * t) := by ac_rfl
      _ = N * ((t + 1).choose 2 * 2) := by rw [hden]
      _ = 2 * N * (t + 1).choose 2 := by ac_rfl
  | succ h hh ih =>
    have hnum := Nat.choose_succ_right_eq N h
    have hden : (t + h + 1) * (t + h).choose (h + 1) =
        (t + (h + 1)).choose (h + 2) * (h + 2) := by
      simpa only [Nat.add_assoc] using Nat.add_one_mul_choose_eq (t + h) (h + 1)
    have hcoeff : (N - h) * (h + 2) ≤ (h + 1) * (t + h + 1) := by
      calc
        (N - h) * (h + 2) ≤ N * (2 * (h + 1)) :=
          Nat.mul_le_mul (Nat.sub_le N h) (by omega)
        _ = (2 * N) * (h + 1) := by ac_rfl
        _ ≤ t * (h + 1) := Nat.mul_le_mul_right _ hNt
        _ ≤ (t + h + 1) * (h + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = (h + 1) * (t + h + 1) := by ac_rfl
    apply Nat.le_of_mul_le_mul_right (c := (h + 1) * (h + 2)) ?_
      (Nat.mul_pos (by omega) (by omega))
    calc
      (t * (t + 1) * N.choose (h + 1)) * ((h + 1) * (h + 2)) =
          (t * (t + 1)) * (N.choose (h + 1) * (h + 1)) * (h + 2) := by ac_rfl
      _ = (t * (t + 1) * N.choose h) * ((N - h) * (h + 2)) := by
        rw [hnum]
        ac_rfl
      _ ≤ (2 * N * (t + h).choose (h + 1)) * ((N - h) * (h + 2)) :=
        Nat.mul_le_mul_right _ ih
      _ ≤ (2 * N * (t + h).choose (h + 1)) * ((h + 1) * (t + h + 1)) :=
        Nat.mul_le_mul_left _ hcoeff
      _ = (2 * N) * ((t + h + 1) * (t + h).choose (h + 1)) * (h + 1) := by
        ac_rfl
      _ = (2 * N * (t + (h + 1)).choose (h + 2)) * ((h + 1) * (h + 2)) := by
        rw [hden]
        ac_rfl

end Submissions.Erdos1020NearPerfectWeights.Main

namespace Submissions.Erdos1020TraceWeights.Main

/-- Every trace multiplicity denominator is positive when the rank fits. -/
theorem denominator_pos {s r c : ℕ} (hrs : r ≤ s) :
    0 < (s - c).choose (r - c) :=
  Nat.choose_pos (Nat.sub_le_sub_right hrs c)

/-- Increasing the support size decreases the trace multiplicity denominator. -/
theorem denominator_antitone {s r c d : ℕ} (hcd : c ≤ d) (hdr : d ≤ r)
    (hrs : r ≤ s) :
    (s - d).choose (r - d) ≤ (s - c).choose (r - c) := by
  have hd : s - d = (r - d) + (s - r) := by omega
  have hc : s - c = (r - c) + (s - r) := by omega
  calc
    (s - d).choose (r - d) = (s - d).choose (s - r) :=
      Nat.choose_symm_of_eq_add hd
    _ ≤ (s - c).choose (s - r) := Nat.choose_le_choose _ (by omega)
    _ = (s - c).choose (r - c) := (Nat.choose_symm_of_eq_add hc).symm

/-- The short-trace estimate using the actual support denominator. -/
theorem short_weight_mul_bound {N s r c d : ℕ} (hcd : c ≤ d)
    (hdr : d < r) (hrs : r ≤ s) (hN : N ≤ s - r + 1) :
    (s - r + 1) * N.choose (r - d) ≤ N * (s - c).choose (r - c) := by
  have h := Submissions.Erdos1020NearPerfectWeights.Main.short_weight_bound
    (N := N) (t := s - r + 1) (h := r - d) (by omega) hN
  have heq : s - r + 1 + (r - d) - 1 = s - d := by omega
  rw [heq] at h
  exact h.trans (Nat.mul_le_mul_left N (denominator_antitone hcd hdr.le hrs))

/-- The short nontransversal estimate using the actual support denominator. -/
theorem short_nontransversal_weight_mul_bound {N s r c d : ℕ} (hcd : c < d)
    (hdr : d < r) (hrs : r ≤ s) (hN : 2 * N ≤ s - r + 1) :
    (s - r + 1) * (s - r + 1 + 1) * N.choose (r - d) ≤
      2 * N * (s - c).choose (r - c) := by
  have h := Submissions.Erdos1020NearPerfectWeights.Main.short_nontransversal_weight_bound
    (N := N) (t := s - r + 1) (h := r - d) (by omega) hN
  have htop : s - r + 1 + (r - d) = s - (d - 1) := by omega
  have hbot : r - d + 1 = r - (d - 1) := by omega
  rw [htop, hbot] at h
  have hden := denominator_antitone (s := s) (r := r) (c := c) (d := d - 1)
    (by omega) (by omega) hrs
  exact h.trans (Nat.mul_le_mul_left (2 * N) hden)

/-- Rational form of the short-trace weight bound; all subtractions remain natural. -/
theorem short_weight_bound_rat {N s r c d : ℕ} (hcd : c ≤ d)
    (hdr : d < r) (hrs : r ≤ s) (hN : N ≤ s - r + 1) :
    (N.choose (r - d) : ℚ) / ((s - c).choose (r - c) : ℚ) ≤
      (N : ℚ) / ((s - r + 1 : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < ((s - c).choose (r - c) : ℚ) :=
    Nat.cast_pos.mpr (denominator_pos hrs)
  have ht : (0 : ℚ) < ((s - r + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
  apply (div_le_div_iff₀ hD ht).mpr
  have hn : N.choose (r - d) * (s - r + 1) ≤ N * (s - c).choose (r - c) := by
    rw [Nat.mul_comm]
    exact short_weight_mul_bound hcd hdr hrs hN
  have hq : ((N.choose (r - d) * (s - r + 1) : ℕ) : ℚ) ≤
      ((N * (s - c).choose (r - c) : ℕ) : ℚ) := Nat.cast_le.mpr hn
  simpa only [Nat.cast_mul] using hq

/-- Rational form of the short nontransversal weight bound. -/
theorem short_nontransversal_weight_bound_rat {N s r c d : ℕ} (hcd : c < d)
    (hdr : d < r) (hrs : r ≤ s) (hN : 2 * N ≤ s - r + 1) :
    (N.choose (r - d) : ℚ) / ((s - c).choose (r - c) : ℚ) ≤
      ((2 * N : ℕ) : ℚ) / (((s - r + 1) * (s - r + 1 + 1) : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < ((s - c).choose (r - c) : ℚ) :=
    Nat.cast_pos.mpr (denominator_pos hrs)
  have ht : (0 : ℚ) < (((s - r + 1) * (s - r + 1 + 1) : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
  apply (div_le_div_iff₀ hD ht).mpr
  have hn : N.choose (r - d) * ((s - r + 1) * (s - r + 1 + 1)) ≤
      (2 * N) * (s - c).choose (r - c) := by
    rw [Nat.mul_comm]
    exact short_nontransversal_weight_mul_bound hcd hdr hrs hN
  have hq : ((N.choose (r - d) * ((s - r + 1) * (s - r + 1 + 1)) : ℕ) : ℚ) ≤
      (((2 * N) * (s - c).choose (r - c) : ℕ) : ℚ) := Nat.cast_le.mpr hn
  simpa only [Nat.cast_mul] using hq

end Submissions.Erdos1020TraceWeights.Main

namespace Submissions.Erdos1020ShortWeightTotals.Main

/-- A bounded number of short weights has total at most one half. -/
theorem short_sum_bound {ι : Type*} (I : Finset ι) (w : ι → ℚ)
    {N t C : ℕ} (ht : 0 < t) (hcard : I.card ≤ C) (hguard : 2 * C * N ≤ t)
    (hw : ∀ i ∈ I, w i ≤ (N : ℚ) / (t : ℚ)) :
    (∑ i ∈ I, w i) ≤ (1 / 2 : ℚ) ∧ (∑ i ∈ I, w i) < 1 := by
  have htq : (0 : ℚ) < t := Nat.cast_pos.mpr ht
  have hcq : (I.card : ℚ) ≤ C := Nat.cast_le.mpr hcard
  have hgq : (2 : ℚ) * (C : ℚ) * (N : ℚ) ≤ t := by exact_mod_cast hguard
  have hsum : (∑ i ∈ I, w i) ≤ (I.card : ℚ) * ((N : ℚ) / (t : ℚ)) := by
    simpa only [nsmul_eq_mul] using I.sum_le_card_nsmul w ((N : ℚ) / (t : ℚ)) hw
  have hcount : (I.card : ℚ) * ((N : ℚ) / (t : ℚ)) ≤
      (C : ℚ) * ((N : ℚ) / (t : ℚ)) :=
    mul_le_mul_of_nonneg_right hcq (div_nonneg (Nat.cast_nonneg N) htq.le)
  have hhalf : (C : ℚ) * ((N : ℚ) / (t : ℚ)) ≤ (1 / 2 : ℚ) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ htq (by norm_num)).mpr
    nlinarith only [hgq]
  have htotal := hsum.trans (hcount.trans hhalf)
  exact ⟨htotal, htotal.trans_lt (by norm_num)⟩

/-- The stronger pointwise estimate gives a total strictly below the gap weight. -/
theorem short_nontransversal_sum_bound {ι : Type*} (I : Finset ι) (w : ι → ℚ)
    {N t C : ℕ} (ht : 0 < t) (hcard : I.card ≤ C) (hguard : 2 * C * N ≤ t)
    (hw : ∀ i ∈ I, w i ≤ (2 * (N : ℚ)) / ((t : ℚ) * ((t : ℚ) + 1))) :
    (∑ i ∈ I, w i) ≤ 1 / ((t : ℚ) + 1) ∧ (∑ i ∈ I, w i) < 1 / (t : ℚ) := by
  have htq : (0 : ℚ) < t := Nat.cast_pos.mpr ht
  have ht1q : (0 : ℚ) < (t : ℚ) + 1 := by linarith
  have hcq : (I.card : ℚ) ≤ C := Nat.cast_le.mpr hcard
  have hgq : (2 : ℚ) * (C : ℚ) * (N : ℚ) ≤ t := by exact_mod_cast hguard
  have hsum : (∑ i ∈ I, w i) ≤
      (I.card : ℚ) * ((2 * (N : ℚ)) / ((t : ℚ) * ((t : ℚ) + 1))) := by
    simpa only [nsmul_eq_mul] using
      I.sum_le_card_nsmul w ((2 * (N : ℚ)) / ((t : ℚ) * ((t : ℚ) + 1))) hw
  have hcount :
      (I.card : ℚ) * ((2 * (N : ℚ)) / ((t : ℚ) * ((t : ℚ) + 1))) ≤
        (C : ℚ) * ((2 * (N : ℚ)) / ((t : ℚ) * ((t : ℚ) + 1))) :=
    mul_le_mul_of_nonneg_right hcq
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N)) (mul_pos htq ht1q).le)
  have hupper : (C : ℚ) * ((2 * (N : ℚ)) / ((t : ℚ) * ((t : ℚ) + 1))) ≤
      1 / ((t : ℚ) + 1) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos htq ht1q) ht1q).mpr
    have hmul := mul_le_mul_of_nonneg_right hgq ht1q.le
    nlinarith only [hmul]
  have htotal := hsum.trans (hcount.trans hupper)
  have hstrict : (1 : ℚ) / ((t : ℚ) + 1) < 1 / (t : ℚ) := by
    apply (div_lt_div_iff₀ ht1q htq).mpr
    linarith
  exact ⟨htotal, htotal.trans_lt hstrict⟩

end Submissions.Erdos1020ShortWeightTotals.Main

namespace Submissions.Erdos1020MatchingShortFamilyCount.Main

open Finset

/-- The exact binomial-level bound for a family of subsets of size below r.
No ambient finiteness assumption or positive-rank guard is needed. -/
theorem short_family_card_le {α : Type*} [DecidableEq α]
    (U : Finset α) (r : ℕ) (F : Finset (Finset α))
    (hFU : ∀ S ∈ F, S ⊆ U) (hFr : ∀ S ∈ F, S.card < r) :
    F.card ≤ ∑ d ∈ range r, U.card.choose d := by
  have hsub : F ⊆ (range r).biUnion (fun d => U.powersetCard d) := by
    intro S hSF
    exact mem_biUnion.mpr ⟨S.card, mem_range.mpr (hFr S hSF),
      mem_powersetCard.mpr ⟨hFU S hSF, rfl⟩⟩
  calc
    F.card ≤ ((range r).biUnion (fun d => U.powersetCard d)).card := card_le_card hsub
    _ = ∑ d ∈ range r, U.card.choose d := by
      rw [card_biUnion (fun i _ j _ hij => (pairwise_disjoint_powersetCard U) hij)]
      simp only [card_powersetCard]

end Submissions.Erdos1020MatchingShortFamilyCount.Main

namespace Submissions.Erdos1020MatchingLocalWeightComparison.Main

open Finset

/-- A missing point contributes its full weight to the gap between two
finite sums when every weight in the larger set is nonnegative. -/
theorem sum_add_weight_le_of_missing {β : Type*} [DecidableEq β]
    (F P : Finset β) (w : β → ℚ) (hFP : F ⊆ P)
    (hnonneg : ∀ x ∈ P, 0 ≤ w x) (x : β) (hxP : x ∈ P) (hxF : x ∉ F) :
    (∑ y ∈ F, w y) + w x ≤ ∑ y ∈ P, w y := by
  have hsub : insert x F ⊆ P := insert_subset hxP hFP
  have hle : (∑ y ∈ insert x F, w y) ≤ ∑ y ∈ P, w y :=
    sum_le_sum_of_subset_of_nonneg hsub (fun y hy _ => hnonneg y hy)
  rw [sum_insert hxF] at hle
  simpa only [add_comm] using hle

/-- A finite local comparison with all weight and structural hypotheses
explicit. The width function and weights are arbitrary; the hypotheses
must be supplied independently for a concrete trace family. -/
theorem local_weight_le {α : Type*} [DecidableEq α]
    (U : Finset α) (r : ℕ) (F : Finset (Finset α))
    (hFU : ∀ S ∈ F, S ⊆ U) (hFr : ∀ S ∈ F, S.card ≤ r)
    (w : Finset α → ℚ) (c : Finset α → ℕ) (δ : ℚ) (_hδ : 0 < δ)
    (hnonneg : ∀ S ∈ U.powersetCard r, 0 ≤ w S)
    (hfullweight : ∀ S ∈ U.powersetCard r, c S = r → w S = 1)
    (hnearweight : ∀ S ∈ U.powersetCard r, c S = r - 1 → w S = δ)
    (hshort : (∑ S ∈ F.filter (fun S => S.card < r), w S) < 1)
    (hshort_of_full :
      (∀ S ∈ U.powersetCard r, c S = r → S ∈ F) →
        (∑ S ∈ F.filter (fun S => S.card < r), w S) < δ)
    (hno_short_of_full_near :
      (∀ S ∈ U.powersetCard r, c S = r → S ∈ F) →
      (∀ S ∈ U.powersetCard r, c S = r - 1 → S ∈ F) →
        F.filter (fun S => S.card < r) = ∅) :
    (∑ S ∈ F, w S) ≤ ∑ S ∈ U.powersetCard r, w S := by
  classical
  let L := F.filter (fun S => ¬ S.card < r)
  have hLP : L ⊆ U.powersetCard r := by
    intro S hS
    obtain ⟨hSF, hSr⟩ := mem_filter.mp hS
    exact mem_powersetCard.mpr ⟨hFU S hSF, le_antisymm (hFr S hSF) (le_of_not_gt hSr)⟩
  have hsplit : (∑ S ∈ F.filter (fun S => S.card < r), w S) +
      (∑ S ∈ L, w S) = ∑ S ∈ F, w S :=
    sum_filter_add_sum_filter_not F (fun S => S.card < r) w
  have hmissing (S : Finset α) (hSP : S ∈ U.powersetCard r) (hSF : S ∉ F) :
      (∑ T ∈ L, w T) + w S ≤ ∑ T ∈ U.powersetCard r, w T :=
    sum_add_weight_le_of_missing L (U.powersetCard r) w hLP hnonneg S hSP
      (fun h => hSF (mem_filter.mp h).1)
  by_cases hfull : ∀ S ∈ U.powersetCard r, c S = r → S ∈ F
  · by_cases hnear : ∀ S ∈ U.powersetCard r, c S = r - 1 → S ∈ F
    · have hempty := hno_short_of_full_near hfull hnear
      have hFP : F ⊆ U.powersetCard r := by
        intro S hSF
        have hnlt : ¬ S.card < r := by
          intro hlt
          have hmem : S ∈ F.filter (fun S => S.card < r) :=
            mem_filter.mpr ⟨hSF, hlt⟩
          rw [hempty] at hmem
          exact notMem_empty S hmem
        exact mem_powersetCard.mpr ⟨hFU S hSF, le_antisymm (hFr S hSF) (le_of_not_gt hnlt)⟩
      exact sum_le_sum_of_subset_of_nonneg hFP (fun S hS _ => hnonneg S hS)
    · obtain ⟨S, hSP, hcS, hSF⟩ :
          ∃ S, S ∈ U.powersetCard r ∧ c S = r - 1 ∧ S ∉ F := by
        by_contra h
        apply hnear
        intro S hSP hcS
        by_contra hSF
        exact h ⟨S, hSP, hcS, hSF⟩
      have hloss := hmissing S hSP hSF
      rw [hnearweight S hSP hcS] at hloss
      rw [← hsplit]
      have hlt := add_lt_add_right (hshort_of_full hfull) (∑ S ∈ L, w S)
      simpa only [add_comm] using (hlt.trans_le hloss).le
  · obtain ⟨S, hSP, hcS, hSF⟩ :
        ∃ S, S ∈ U.powersetCard r ∧ c S = r ∧ S ∉ F := by
      by_contra h
      apply hfull
      intro S hSP hcS
      by_contra hSF
      exact h ⟨S, hSP, hcS, hSF⟩
    have hloss := hmissing S hSP hSF
    rw [hfullweight S hSP hcS] at hloss
    rw [← hsplit]
    have hlt := add_lt_add_right hshort (∑ S ∈ L, w S)
    simpa only [add_comm] using (hlt.trans_le hloss).le

end Submissions.Erdos1020MatchingLocalWeightComparison.Main

namespace Submissions.Erdos1020MatchingLocalTraceWeight.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- Concrete local trace-weight comparison with both structural implications
explicit. The counting and numerical estimates require no additional hypothesis. -/
theorem local_weight_bound {α : Type*} [DecidableEq α] {s r N : ℕ}
    (hr : 1 ≤ r) (hrs : r ≤ s)
    (G : Finset α) (hGc : G.card = r - 1) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (hBc : ∀ i, (B i).card = r)
    (M : Finset (Fin s)) (hMc : M.card = r) (F : Finset (Finset α))
    (hFU : ∀ S ∈ F, S ⊆ region G B M) (hFr : ∀ S ∈ F, S.card ≤ r)
    (hguard : 2 * (∑ d ∈ range r, (r * r + r - 1).choose d) * N ≤ s - r + 1)
    (hshort_nondiag :
      (∀ S ∈ (region G B M).powersetCard r, (support B S).card = r → S ∈ F) →
        ∀ S ∈ F, S.card < r → (support B S).card < S.card)
    (hno_short :
      (∀ S ∈ (region G B M).powersetCard r, (support B S).card = r → S ∈ F) →
      (∀ S ∈ (region G B M).powersetCard r, (support B S).card = r - 1 → S ∈ F) →
        F.filter (fun S => S.card < r) = ∅) :
    (∑ S ∈ F, (N.choose (r - S.card) : ℚ) /
      ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) ≤
      ∑ S ∈ (region G B M).powersetCard r, (N.choose (r - S.card) : ℚ) /
        ((s - (support B S).card).choose (r - (support B S).card) : ℚ) := by
  classical
  let U := region G B M
  let C := ∑ d ∈ range r, (r * r + r - 1).choose d
  let t := s - r + 1
  let I := F.filter (fun S => S.card < r)
  let w : Finset α → ℚ := fun S => (N.choose (r - S.card) : ℚ) /
    ((s - (support B S).card).choose (r - (support B S).card) : ℚ)
  have hUc : U.card = r * r + r - 1 := by
    dsimp only [U]
    rw [region_card G B hB hG hBc M, hGc, hMc]
    omega
  have hC : 1 ≤ C := by
    calc
      1 = (r * r + r - 1).choose 0 := by simp
      _ ≤ C := single_le_sum (fun d _ => Nat.zero_le ((r * r + r - 1).choose d))
        (mem_range.mpr (by omega))
  have ht : 0 < t := by dsimp only [t]; omega
  have h2N : 2 * N ≤ t := by
    calc
      2 * N = (2 * 1) * N := by omega
      _ ≤ (2 * C) * N := Nat.mul_le_mul_right N (Nat.mul_le_mul_left 2 hC)
      _ ≤ t := hguard
  have hN : N ≤ s - r + 1 := by dsimp only [t] at h2N; omega
  have hIcard : I.card ≤ C := by
    have h := Submissions.Erdos1020MatchingShortFamilyCount.Main.short_family_card_le
      U r I (fun S hS => hFU S (mem_filter.mp hS).1)
        (fun _ hS => (mem_filter.mp hS).2)
    simpa only [hUc, C] using h
  have hshort : (∑ S ∈ I, w S) < 1 := by
    apply (Submissions.Erdos1020ShortWeightTotals.Main.short_sum_bound
      I w (N := N) (t := t) (C := C) ht hIcard hguard ?_).2
    intro S hS
    exact Submissions.Erdos1020TraceWeights.Main.short_weight_bound_rat
      (support_card_le_card B hB S) (mem_filter.mp hS).2 hrs hN
  have hshort_full :
      (∀ S ∈ U.powersetCard r, (support B S).card = r → S ∈ F) →
        (∑ S ∈ I, w S) < (1 : ℚ) / (t : ℚ) := by
    intro hfull
    apply (Submissions.Erdos1020ShortWeightTotals.Main.short_nontransversal_sum_bound
      I w (N := N) (t := t) (C := C) ht hIcard hguard ?_).2
    intro S hS
    have hSc : S.card < r := (mem_filter.mp hS).2
    have h := Submissions.Erdos1020TraceWeights.Main.short_nontransversal_weight_bound_rat
      (hshort_nondiag hfull S (mem_filter.mp hS).1 hSc) hSc hrs h2N
    simpa only [w, t, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h
  have hnonneg : ∀ S ∈ U.powersetCard r, 0 ≤ w S := by
    intro S _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfullweight : ∀ S ∈ U.powersetCard r, (support B S).card = r → w S = 1 := by
    intro S hS hc
    have hSr := (mem_powersetCard.mp hS).2
    simp only [w, hSr, hc, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, div_one]
  have hnearweight : ∀ S ∈ U.powersetCard r,
      (support B S).card = r - 1 → w S = (1 : ℚ) / (t : ℚ) := by
    intro S hS hc
    have hSr := (mem_powersetCard.mp hS).2
    have hbot : r - (r - 1) = 1 := by omega
    have htop : s - (r - 1) = t := by dsimp only [t]; omega
    simp only [w, hSr, hc, Nat.sub_self, Nat.choose_zero_right, hbot, htop,
      Nat.choose_one_right, Nat.cast_one]
  have hdelta : (0 : ℚ) < 1 / (t : ℚ) := div_pos zero_lt_one (Nat.cast_pos.mpr ht)
  change (∑ S ∈ F, w S) ≤ ∑ S ∈ U.powersetCard r, w S
  exact Submissions.Erdos1020MatchingLocalWeightComparison.Main.local_weight_le
    U r F hFU hFr w (fun S => (support B S).card) (1 / (t : ℚ)) hdelta
    hnonneg hfullweight hnearweight hshort hshort_full hno_short

end Submissions.Erdos1020MatchingLocalTraceWeight.Main

namespace Submissions.Erdos1020MatchingNearPerfectLocal.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- The concrete local comparison for actual traces; all combinatorial
implications are discharged by the checked trace structure lemmas. -/
theorem local_bound {n r s : ℕ} (hr : 2 ≤ r) (hrs : r ≤ s)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e')
    (G : Finset (Fin n)) (hGA : G ⊆ A) (hGc : G.card = r - 1)
    (B : Fin s → Finset (Fin n)) (hBH : ∀ i, B i ∈ H)
    (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i))
    (a : Fin s → Fin n) (ha : ∀ i, a i ∈ B i)
    (hmin : ∀ i, ∀ x ∈ B i, a i ≤ x)
    (hhub : ∀ i, insert (a i) G ∈ H)
    (M : Finset (Fin s)) (hMc : M.card = r)
    (hguard : 2 * (∑ d ∈ range r, (r * r + r - 1).choose d) *
      (n - A.card) ≤ s - r + 1) :
    (∑ S ∈ (H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M),
      ((n - A.card).choose (r - S.card) : ℚ) /
        ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) ≤
      ∑ S ∈ (region G B M).powersetCard r,
        ((n - A.card).choose (r - S.card) : ℚ) /
          ((s - (support B S).card).choose (r - (support B S).card) : ℚ) := by
  classical
  let F := (H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M)
  have hFU : ∀ S ∈ F, S ⊆ region G B M := fun _ hS => (mem_filter.mp hS).2
  have hFr : ∀ S ∈ F, S.card ≤ r := by
    intro S hS
    obtain ⟨e, he, rfl⟩ := mem_image.mp (mem_filter.mp hS).1
    exact (card_le_card inter_subset_left).trans_eq (hH e he)
  apply Submissions.Erdos1020MatchingLocalTraceWeight.Main.local_weight_bound
    (by omega) hrs G hGc B hBd hGB (fun i => hH (B i) (hBH i))
    M hMc F hFU hFr hguard
  · intro hfull S hS hSc
    have hfull' : ∀ Q : Finset (Fin n), Q.card = r → Q ⊆ region G B M →
        (support B Q).card = r → Q ∈ H.image (fun e => e ∩ A) := by
      intro Q hQc hQU hc
      exact (mem_filter.mp (hfull Q (mem_powersetCard.mpr ⟨hQU, hQc⟩) hc)).1
    exact Submissions.Erdos1020MatchingTraceLocalStructure.Main.short_width_lt
      hr H A hH hA hcut hstable hfree G hGA hGc B hBH hBA hBd hGB
      a ha hmin hhub M hMc hfull' S (mem_filter.mp hS).1 (hFU S hS) hSc
  · intro hfull hgap
    apply filter_eq_empty_iff.mpr
    intro S hS hSc
    have hfull' : ∀ Q : Finset (Fin n), Q.card = r → Q ⊆ region G B M →
        (support B Q).card = r → Q ∈ H.image (fun e => e ∩ A) := by
      intro Q hQc hQU hc
      exact (mem_filter.mp (hfull Q (mem_powersetCard.mpr ⟨hQU, hQc⟩) hc)).1
    have hgap' : ∀ Q : Finset (Fin n), Q.card = r → Q ⊆ region G B M →
        (support B Q).card = r - 1 → Q ∈ H.image (fun e => e ∩ A) := by
      intro Q hQc hQU hc
      exact (mem_filter.mp (hgap Q (mem_powersetCard.mpr ⟨hQU, hQc⟩) hc)).1
    exact Submissions.Erdos1020MatchingTraceLocalStructure.Main.short_not_mem
      (by omega) H A hH hA hcut hstable hfree G hGc B hBH hBA hBd hGB
      M hMc hfull' hgap' S (hFU S hS) hSc (mem_filter.mp hS).1

end Submissions.Erdos1020MatchingNearPerfectLocal.Main

namespace Submissions.Erdos1020MatchingMaximalShift.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- A uniform matching-free family is bounded in size by a globally largest such
family that is stable under every downward singleton shift. -/
theorem exists_maximal_shifted {n r k : ℕ}
    (H : Finset (Finset (Fin n))) (hH : Uniform H r) (hM : MatchingFree H k) :
    ∃ G : Finset (Finset (Fin n)), H.card ≤ G.card ∧ Uniform G r ∧ MatchingFree G k ∧
      (∀ K : Finset (Finset (Fin n)), Uniform K r → MatchingFree K k → K.card ≤ G.card) ∧
      (∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} G) := by
  classical
  let candidates : Finset (Finset (Finset (Fin n))) :=
    univ.filter (fun K => Uniform K r ∧ MatchingFree K k)
  have hmem : H ∈ candidates := by simp [candidates, hH, hM]
  obtain ⟨K, hK, hmax⟩ := exists_max_image candidates Finset.card ⟨H, hmem⟩
  have hprops := (mem_filter.mp hK).2
  obtain ⟨G, hGc, hGu, hGm, hGs⟩ := exists_shifted K hprops.1 hprops.2
  refine ⟨G, ?_, hGu, hGm, ?_, hGs⟩
  · rw [hGc]
    exact hmax H hmem
  · intro F hFu hFm
    rw [hGc]
    exact hmax F (by simp [candidates, hFu, hFm])

/-- Adding a missing uniform edge to a cardinal-maximal family creates a matching. -/
theorem matching_of_insert {α : Type*} [DecidableEq α] {r k : ℕ}
    (G : Finset (Finset α)) (hG : Uniform G r)
    (hmax : ∀ K : Finset (Finset α), Uniform K r → MatchingFree K k → K.card ≤ G.card)
    (e : Finset α) (her : e.card = r) (he : e ∉ G) :
    ∃ M : Finset (Finset α), M ⊆ insert e G ∧ M.card = k ∧
      ∀ f ∈ M, ∀ g ∈ M, f ≠ g → Disjoint f g := by
  classical
  by_contra hnone
  have hu : Uniform (insert e G) r := by
    intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact her
    · exact hG f hf
  have hle := hmax (insert e G) hu hnone
  rw [card_insert_of_notMem he] at hle
  omega

/-- A missing edge has a disjoint matching of size k-1 in a saturated family. -/
theorem saturating_matching {α : Type*} [DecidableEq α] {r k : ℕ}
    (G : Finset (Finset α)) (hG : Uniform G r) (hGm : MatchingFree G k)
    (hmax : ∀ K : Finset (Finset α), Uniform K r → MatchingFree K k → K.card ≤ G.card)
    (e : Finset α) (her : e.card = r) (he : e ∉ G) :
    ∃ M : Finset (Finset α), M ⊆ G ∧ M.card = k - 1 ∧
      (∀ f ∈ M, ∀ g ∈ M, f ≠ g → Disjoint f g) ∧
      (∀ f ∈ M, Disjoint e f) := by
  obtain ⟨N, hNG, hNc, hNd⟩ := matching_of_insert G hG hmax e her he
  have heN : e ∈ N := by
    by_contra heN
    apply hGm
    refine ⟨N, ?_, hNc, hNd⟩
    intro f hf
    rcases mem_insert.mp (hNG hf) with hfe | hfG
    · exact (heN (hfe ▸ hf)).elim
    · exact hfG
  refine ⟨N.erase e, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rcases mem_insert.mp (hNG (mem_of_mem_erase hf)) with hfe | hfG
    · exact ((mem_erase.mp hf).1 hfe).elim
    · exact hfG
  · rw [card_erase_of_mem heN, hNc]
  · intro f hf g hg hfg
    exact hNd f (mem_of_mem_erase hf) g (mem_of_mem_erase hg) hfg
  · intro f hf
    exact hNd e heN f (mem_of_mem_erase hf) (Ne.symm (mem_erase.mp hf).1)

end Submissions.Erdos1020MatchingMaximalShift.Main

namespace Submissions.Erdos1020MatchingTraceCompletion.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- A cardinal-maximal shifted family contains every uniform edge that contains
the head trace of one of its members, when the head has size r*k-1. -/
theorem mem_of_trace_subset {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Finset (Fin n)) (her : e.card = r)
    (htrace : ∃ f ∈ H, f ∩ A ⊆ e) : e ∈ H := by
  classical
  by_contra he
  obtain ⟨f, hf, hfa⟩ := htrace
  obtain ⟨N, hN, hNk, hNd⟩ :=
    Submissions.Erdos1020MatchingMaximalShift.Main.matching_of_insert
      H hH hmax e her he
  let g : N → Finset (Fin n) := fun c => if c.val = e then f else c.val
  have hg : ∀ c, g c ∈ H := by
    intro c
    by_cases hc : c.val = e
    · simpa only [g, if_pos hc] using hf
    · have hcH : c.val ∈ H := (mem_insert.mp (hN c.property)).resolve_left hc
      simpa only [g, if_neg hc] using hcH
  have hsub : ∀ c, g c ∩ A ⊆ c.val := by
    intro c
    by_cases hc : c.val = e
    · change (if c.val = e then f else c.val) ∩ A ⊆ c.val
      rw [if_pos hc, hc]
      exact hfa
    · simpa only [g, if_neg hc] using
        (inter_subset_left : c.val ∩ A ⊆ c.val)
  have hgd : Pairwise (fun c d => Disjoint (g c ∩ A) (g d ∩ A)) := by
    intro c d hcd
    apply disjoint_left.mpr
    intro x hxc hxd
    exact disjoint_left.mp
      (hNd c.val c.property d.val d.property (fun h => hcd (Subtype.ext h)))
      (hsub c hxc) (hsub d hxd)
  exact Submissions.Erdos1020MatchingTrace.Main.no_indexed_trace_matching
    hr H A hH (by simpa only [Fintype.card_coe] using hNk)
    hA hcut hstable hfree g hg hgd

end Submissions.Erdos1020MatchingTraceCompletion.Main

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

namespace Submissions.Erdos1020MatchingGapSelection.Main

open Finset

/-- Some (r-1)-subset of the initial rk-1 head is absent from the trace. -/
theorem exists_missing_head_set {n r k : ℕ} (hr : 0 < r) (hk : 1 ≤ k)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Fin n), G ⊆ A ∧ G.card = r - 1 ∧
      G ∉ H.image (fun e => e ∩ A) := by
  classical
  have hproduct : k * (r - 1) + k = r * k := by
    calc
      _ = k * ((r - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = k * r := by rw [Nat.sub_add_cancel hr]
      _ = r * k := Nat.mul_comm _ _
  have hcap : k * (r - 1) ≤ Fintype.card A := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨B, hBc, hBd⟩ :=
    Submissions.Erdos1020UniformBlocks.Main.exists_blocks (α := A) k (r - 1) hcap
  let emb : A ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub (i : Fin k) : (B i).map emb ⊆ A := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := mem_map.mp hx
    exact a.property
  by_contra hnone
  have hmem (i : Fin k) : (B i).map emb ∈ H.image (fun e => e ∩ A) := by
    by_contra hi
    exact hnone ⟨(B i).map emb, hsub i, by simpa using hBc i, hi⟩
  have hw : ∀ i : Fin k, ∃ e, e ∈ H ∧ e ∩ A = (B i).map emb := by
    intro i
    exact mem_image.mp (hmem i)
  choose f hf hfa using hw
  apply Submissions.Erdos1020MatchingTrace.Main.no_indexed_trace_matching
    hr H A hH (Fintype.card_fin k) hA hcut hstable hfree f hf
  intro i j hij
  rw [hfa i, hfa j]
  exact (disjoint_map emb).mpr (hBd hij)

/-- Choose the missing head set with minimum vertex-label sum. -/
theorem exists_minimum_gap {n r k : ℕ} (hr : 0 < r) (hk : 1 ≤ k)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ G : Finset (Fin n), G ⊆ A ∧ G.card = r - 1 ∧
      G ∉ H.image (fun e => e ∩ A) ∧
      ∀ R : Finset (Fin n), R ⊆ A → R.card = r - 1 →
        R ∉ H.image (fun e => e ∩ A) →
          (∑ x ∈ G, x.val) ≤ ∑ x ∈ R, x.val := by
  classical
  let candidates := (A.powersetCard (r - 1)).filter
    (fun G => G ∉ H.image (fun e => e ∩ A))
  obtain ⟨R, hRA, hRc, hR⟩ := exists_missing_head_set hr hk H A hH hA hcut hstable hfree
  have hmem : R ∈ candidates := by
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hRA, hRc⟩, hR⟩
  obtain ⟨G, hG, hmin⟩ := exists_min_image candidates
    (fun R : Finset (Fin n) => ∑ x ∈ R, x.val) ⟨R, hmem⟩
  have hp := mem_filter.mp hG
  have hpc := mem_powersetCard.mp hp.1
  refine ⟨G, hpc.1, hpc.2, hp.2, ?_⟩
  intro R hRA hRc hR
  exact hmin R (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hRA, hRc⟩, hR⟩)

end Submissions.Erdos1020MatchingGapSelection.Main

namespace Submissions.Erdos1020MatchingPack.Main

open Finset

/-- A shifted matching avoiding R can be packed into an initial head, still
avoiding R, whenever that head has enough remaining vertices. -/
theorem exists_packed_matching {n r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Finset (Finset (Fin n))) (A R : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r)
    (hcap : r * Fintype.card ι ≤ (A \ R).card)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (f : ι → Finset (Fin n)) (hf : ∀ c, f c ∈ H)
    (hd : Pairwise (fun c d => Disjoint (f c) (f d)))
    (hR : ∀ c, Disjoint R (f c)) :
    ∃ g : ι → Finset (Fin n), (∀ c, g c ∈ H) ∧
      Pairwise (fun c d => Disjoint (g c) (g d)) ∧
      (∀ c, Disjoint R (g c)) ∧ (∀ c, g c ⊆ A) := by
  classical
  let W : (ι → Finset (Fin n)) → ℕ := fun g => ∑ c, ∑ x ∈ g c, x.val
  let candidates : Finset (ι → Finset (Fin n)) := univ.filter (fun g =>
    (∀ c, g c ∈ H) ∧ Pairwise (fun c d => Disjoint (g c) (g d)) ∧
      ∀ c, Disjoint R (g c))
  have hfc : f ∈ candidates := by simp [candidates, hf, hd, hR]
  obtain ⟨g, hg, hmin⟩ := exists_min_image candidates W ⟨f, hfc⟩
  have hgm := (mem_filter.mp hg).2.1
  have hgd := (mem_filter.mp hg).2.2.1
  have hgR := (mem_filter.mp hg).2.2.2
  refine ⟨g, hgm, hgd, hgR, ?_⟩
  intro c x hxc
  by_contra hxA
  let U := univ.biUnion g
  have hgc (i : ι) : (g i).card = r := hH _ (hgm i)
  have hUcard : U.card = r * Fintype.card ι := by
    rw [card_biUnion (fun i _ j _ hij => hgd hij)]
    simp [hgc, Nat.mul_comm]
  have hxU : x ∈ U := mem_biUnion.mpr ⟨c, mem_univ _, hxc⟩
  have hgap : ¬ A \ R ⊆ U := by
    intro hcover
    have heq := eq_of_subset_of_card_le hcover (hUcard.le.trans hcap)
    exact hxA (mem_sdiff.mp (heq.symm ▸ hxU)).1
  obtain ⟨v, hvAR, hvU⟩ := not_subset.mp hgap
  have hvA := (mem_sdiff.mp hvAR).1
  have hvR := (mem_sdiff.mp hvAR).2
  have hv (i : ι) : v ∉ g i := by
    intro hvi
    exact hvU (mem_biUnion.mpr ⟨i, mem_univ _, hvi⟩)
  let e := insert v ((g c).erase x)
  have hev : v ∉ (g c).erase x := notMem_mono (erase_subset _ _) (hv c)
  have heH : e ∈ H :=
    Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
      (hstable v x (hcut v hvA x hxA)) (notMem_erase _ _) hev
      (by simpa only [insert_erase hxc] using hgm c)
  have hedis (i : ι) (hic : i ≠ c) : Disjoint e (g i) :=
    disjoint_insert_left.mpr ⟨hv i,
      (hgd (Ne.symm hic)).mono (erase_subset _ _) (Subset.refl _)⟩
  have heR : Disjoint R e := disjoint_insert_right.mpr
    ⟨hvR, (hgR c).mono (Subset.refl _) (erase_subset _ _)⟩
  let g' := Function.update g c e
  have hg' : g' ∈ candidates := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = c
      · subst i
        simpa [g'] using heH
      · simpa [g', hi] using hgm i
    · intro i j hij
      by_cases hi : i = c
      · subst i
        simpa [g', Ne.symm hij] using hedis j (Ne.symm hij)
      · by_cases hj : j = c
        · subst j
          simpa [g', hi] using (hedis i hi).symm
        · simpa [g', hi, hj] using hgd hij
    · intro i
      by_cases hi : i = c
      · subst i
        simpa [g'] using heR
      · simpa [g', hi] using hgR i
  have hweight : (∑ y ∈ e, y.val) < ∑ y ∈ g c, y.val := by
    dsimp [e]
    rw [sum_insert hev]
    have hsum := sum_erase_add (g c) (fun y : Fin n => y.val) hxc
    have hlt : v.val < x.val := hcut v hvA x hxA
    omega
  have hless : W g' < W g := by
    apply sum_lt_sum
    · intro i _
      by_cases hi : i = c
      · subst i
        simpa [g'] using hweight.le
      · simp [g', hi]
    · exact ⟨c, mem_univ _, by simpa [g'] using hweight⟩
  exact (not_lt_of_ge (hmin g' hg')) hless

end Submissions.Erdos1020MatchingPack.Main

namespace Submissions.Erdos1020MatchingGapPartition.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- A missing (r-1)-trace leaves a partition of the remaining head into k-1
members of a cardinal-maximal shifted family. -/
theorem exists_partition_of_gap {n r k : ℕ} (hr : 0 < r) (hk : 1 ≤ k)
    (hn : r * k ≤ n) (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (G : Finset (Fin n)) (hGA : G ⊆ A) (hGc : G.card = r - 1)
    (hgap : G ∉ H.image (fun e => e ∩ A)) :
    ∃ B : Fin (k - 1) → Finset (Fin n), (∀ i, B i ∈ H) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, Disjoint G (B i)) ∧ (∀ i, B i ⊆ A) ∧
      G ∪ univ.biUnion B = A := by
  classical
  have hnot : ¬ (univ : Finset (Fin n)) ⊆ A := by
    intro h
    have hc := card_le_card h
    simp only [card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨y, _, hy⟩ := not_subset.mp hnot
  have hyG : y ∉ G := fun h => hy (hGA h)
  have her : (insert y G).card = r := by
    rw [card_insert_of_notMem hyG, hGc]
    omega
  have htrace : insert y G ∩ A = G := by
    ext x
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨hxy | hxG, hxA⟩
      · exact (hy (hxy ▸ hxA)).elim
      · exact hxG
    · intro hxG
      exact ⟨Or.inr hxG, hGA hxG⟩
  have heH : insert y G ∉ H := by
    intro he
    exact hgap (mem_image.mpr ⟨insert y G, he, htrace⟩)
  obtain ⟨M, hMH, hMc, hMd, hMe⟩ :=
    Submissions.Erdos1020MatchingMaximalShift.Main.saturating_matching
      H hH hfree hmax (insert y G) her heH
  let E : M ≃ Fin (k - 1) := Finset.equivFinOfCardEq hMc
  let f : Fin (k - 1) → Finset (Fin n) := fun i => (E.symm i).val
  have hf (i : Fin (k - 1)) : f i ∈ H := hMH (E.symm i).property
  have hd : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    exact hMd _ (E.symm i).property _ (E.symm j).property
      (fun h => hij (E.symm.injective (Subtype.ext h)))
  have hGf (i : Fin (k - 1)) : Disjoint G (f i) :=
    (hMe _ (E.symm i).property).mono (subset_insert _ _) (Subset.refl _)
  have hproduct : r * (k - 1) + r = r * k := by
    calc
      _ = r * ((k - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = r * k := by rw [Nat.sub_add_cancel hk]
  have hdiff : (A \ G).card = r * (k - 1) := by
    have hc := card_sdiff_add_card_eq_card hGA
    rw [hGc] at hc
    omega
  obtain ⟨B, hBH, hBd, hBG, hBA⟩ :=
    Submissions.Erdos1020MatchingPack.Main.exists_packed_matching
      (ι := Fin (k - 1)) H A G hH
      (by simpa only [Fintype.card_fin, hdiff] using (le_refl (r * (k - 1))))
      hcut hstable f hf hd hGf
  have hBc (i : Fin (k - 1)) : (B i).card = r := hH _ (hBH i)
  have hBUc : (univ.biUnion B).card = r * (k - 1) := by
    rw [card_biUnion (fun i _ j _ hij => hBd hij)]
    simp [hBc, Nat.mul_comm]
  have hBUsub : univ.biUnion B ⊆ A \ G := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
    exact mem_sdiff.mpr ⟨hBA i hxi, fun hxG => disjoint_left.mp (hBG i) hxG hxi⟩
  have hBUeq : univ.biUnion B = A \ G :=
    eq_of_subset_of_card_le hBUsub (by rw [hdiff, hBUc])
  refine ⟨B, hBH, hBd, hBG, hBA, ?_⟩
  rw [hBUeq, union_sdiff_of_subset hGA]

/-- Minimum-sum missing head trace together with an indexed partition of its complement. -/
theorem exists_minimum_gap_partition {n r k : ℕ} (hr : 0 < r) (hk : 1 ≤ k)
    (hn : r * k ≤ n) (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    ∃ G : Finset (Fin n), G ⊆ A ∧ G.card = r - 1 ∧
      G ∉ H.image (fun e => e ∩ A) ∧
      (∀ R : Finset (Fin n), R ⊆ A → R.card = r - 1 →
        R ∉ H.image (fun e => e ∩ A) →
          (∑ x ∈ G, x.val) ≤ ∑ x ∈ R, x.val) ∧
      ∃ B : Fin (k - 1) → Finset (Fin n), (∀ i, B i ∈ H) ∧
        Pairwise (fun i j => Disjoint (B i) (B j)) ∧
        (∀ i, Disjoint G (B i)) ∧ (∀ i, B i ⊆ A) ∧
        G ∪ univ.biUnion B = A := by
  obtain ⟨G, hGA, hGc, hgap, hmin⟩ :=
    Submissions.Erdos1020MatchingGapSelection.Main.exists_minimum_gap
      hr hk H A hH hA hcut hstable hfree
  exact ⟨G, hGA, hGc, hgap, hmin,
    exists_partition_of_gap hr hk hn H A hH hfree hmax hA hcut hstable G hGA hGc hgap⟩

end Submissions.Erdos1020MatchingGapPartition.Main

namespace Submissions.Erdos1020MatchingLowerReplace.Main

open Finset

/-- A stable family permits simultaneous replacement by equally many fresh lower vertices. -/
theorem replace_lower {n : ℕ} (H : Finset (Finset (Fin n)))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e U V : Finset (Fin n)) (he : e ∈ H) (hU : U ⊆ e) (hV : Disjoint V e)
    (hcard : U.card = V.card) (hlower : ∀ v ∈ V, ∀ u ∈ U, v < u) :
    (e \ U) ∪ V ∈ H := by
  induction U using Finset.induction_on generalizing e V with
  | empty =>
    have hV0 : V = ∅ := card_eq_zero.mp (by simpa only [card_empty] using hcard.symm)
    simpa only [hV0, sdiff_empty, union_empty] using he
  | @insert u U hu ih =>
    have hue : u ∈ e := hU (mem_insert_self _ _)
    rw [card_insert_of_notMem hu] at hcard
    obtain ⟨v, hv⟩ : V.Nonempty := card_pos.mp (by omega)
    have hve : v ∉ e := disjoint_left.mp hV hv
    have hvU : v ∉ U := fun h => hve (hU (mem_insert_of_mem h))
    have he' : insert v (e.erase u) ∈ H :=
      Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
        (hstable v u (hlower v hv u (mem_insert_self _ _)))
        (notMem_erase _ _) (notMem_mono (erase_subset _ _) hve)
        (by simpa only [insert_erase hue] using he)
    have hU' : U ⊆ insert v (e.erase u) := by
      intro x hx
      exact mem_insert_of_mem (mem_erase.mpr
        ⟨ne_of_mem_of_not_mem hx hu, hU (mem_insert_of_mem hx)⟩)
    have hV' : Disjoint (V.erase v) (insert v (e.erase u)) :=
      disjoint_insert_right.mpr ⟨notMem_erase _ _,
        hV.mono (erase_subset _ _) (erase_subset _ _)⟩
    have hcard' : U.card = (V.erase v).card := by
      rw [card_erase_of_mem hv]
      omega
    have hlower' : ∀ y ∈ V.erase v, ∀ x ∈ U, y < x :=
      fun y hy x hx => hlower y (mem_of_mem_erase hy) x (mem_insert_of_mem hx)
    have hstep := ih (insert v (e.erase u)) (V.erase v) he' hU' hV' hcard' hlower'
    have heq : (insert v (e.erase u) \ U) ∪ V.erase v = (e \ insert u U) ∪ V := by
      rw [insert_sdiff_of_notMem _ hvU, erase_sdiff_comm, insert_union_comm,
        insert_erase hv, sdiff_insert]
    rwa [heq] at hstep

end Submissions.Erdos1020MatchingLowerReplace.Main

namespace Submissions.Erdos1020MatchingBlockMinimum.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- Adjoining a disjoint block's minimum to a minimum-weight missing head set
gives an edge of a cardinal-maximal shifted family. The explicit minimum
property suffices; the set itself need not be assumed missing again. -/
theorem insert_min_mem {n r k : ℕ} (hr : 2 ≤ r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (G : Finset (Fin n)) (hGA : G ⊆ A) (hGc : G.card = r - 1)
    (hmin : ∀ D : Finset (Fin n), D ⊆ A → D.card = r - 1 →
      D ∉ H.image (fun e => e ∩ A) → (∑ x ∈ G, x.val) ≤ ∑ x ∈ D, x.val)
    (B : Finset (Fin n)) (hBH : B ∈ H) (hBA : B ⊆ A) (hGB : Disjoint G B)
    (b : Fin n) (hb : b ∈ B) (hbmin : ∀ x ∈ B, b ≤ x) :
    insert b G ∈ H := by
  classical
  have hbG : b ∉ G := fun h => disjoint_left.mp hGB h hb
  have her : (insert b G).card = r := by
    rw [card_insert_of_notMem hbG, hGc]
    omega
  have hGne : G.Nonempty := card_pos.mp (by omega)
  let g := G.max' hGne
  have hgG : g ∈ G := G.max'_mem hGne
  by_cases hbg : b < g
  · let D := insert b (G.erase g)
    have hbE : b ∉ G.erase g := notMem_mono (erase_subset _ _) hbG
    have hDA : D ⊆ A := insert_subset (hBA hb) ((erase_subset _ _).trans hGA)
    have hDc : D.card = r - 1 := by
      dsimp only [D]
      rw [card_insert_of_notMem hbE, card_erase_of_mem hgG, hGc]
      omega
    have hsmall : (∑ x ∈ D, x.val) < ∑ x ∈ G, x.val := by
      dsimp only [D]
      rw [sum_insert hbE]
      have hsum := sum_erase_add G (fun x : Fin n => x.val) hgG
      have hval : b.val < g.val := hbg
      omega
    have hDtrace : D ∈ H.image (fun e => e ∩ A) := by
      by_contra hDnot
      exact (not_le_of_gt hsmall) (hmin D hDA hDc hDnot)
    obtain ⟨f, hf, hfD⟩ := mem_image.mp hDtrace
    apply Submissions.Erdos1020MatchingTraceCompletion.Main.mem_of_trace_subset
      (by omega) H A hH hfree hmax hA hcut hstable (insert b G) her
    refine ⟨f, hf, ?_⟩
    rw [hfD]
    exact insert_subset (mem_insert_self _ _)
      (fun _ hx => mem_insert_of_mem (mem_of_mem_erase hx))
  · have hgb : g < b := lt_of_le_of_ne (le_of_not_gt hbg)
      (ne_of_mem_of_not_mem hgG hbG)
    have hcard : (B.erase b).card = G.card := by
      rw [card_erase_of_mem hb, hH B hBH, hGc]
    have hlower : ∀ v ∈ G, ∀ u ∈ B.erase b, v < u := by
      intro v hv u hu
      have hvg : v ≤ g := G.le_max' v hv
      exact (hvg.trans_lt hgb).trans_le (hbmin u (mem_of_mem_erase hu))
    have hshift := Submissions.Erdos1020MatchingLowerReplace.Main.replace_lower
      H hstable B (B.erase b) G hBH (erase_subset _ _) hGB hcard hlower
    simpa only [sdiff_erase_self hb, singleton_union] using hshift

end Submissions.Erdos1020MatchingBlockMinimum.Main

namespace Submissions.Erdos1020MatchingTraceCounts.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- The number of uniform sets with a specified intersection with A. -/
theorem full_fiber_card {α : Type*} [Fintype α] [DecidableEq α]
    (A S : Finset α) {r : ℕ} (hSA : S ⊆ A) (hSr : S.card ≤ r) :
    (((univ : Finset α).powersetCard r).filter (fun e => e ∩ A = S)).card =
      (Fintype.card α - A.card).choose (r - S.card) := by
  have h : ((univ : Finset α).powersetCard r).filter (fun e => e ∩ A = S) =
      ((S ∪ (univ \ A)).powersetCard r).filter (fun e => S ⊆ e) := by
    ext e
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨her, heA⟩
      refine ⟨⟨?_, her⟩, ?_⟩
      · intro x hx
        by_cases hxA : x ∈ A
        · exact mem_union_left _ (heA ▸ mem_inter.mpr ⟨hx, hxA⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _, hxA⟩)
      · intro x hx
        exact (mem_inter.mp (heA.symm ▸ hx)).1
    · rintro ⟨⟨he, her⟩, hSe⟩
      refine ⟨her, ?_⟩
      ext x
      constructor
      · intro hx
        rcases mem_union.mp (he (mem_inter.mp hx).1) with hxS | hxY
        · exact hxS
        · exact ((mem_sdiff.mp hxY).2 (mem_inter.mp hx).2).elim
      · intro hx
        exact mem_inter.mpr ⟨hSe hx, hSA hx⟩
  rw [h, card_filter_powersetCard_subset S (S ∪ (univ \ A)) r subset_union_left hSr]
  have hd : Disjoint S ((univ : Finset α) \ A) := by
    apply disjoint_left.mpr
    intro x hxS hxY
    exact (mem_sdiff.mp hxY).2 (hSA hxS)
  rw [card_union_of_disjoint hd, Nat.add_sub_cancel_left,
    card_sdiff_of_subset (subset_univ A), card_univ]

/-- Maximality fills every uniform completion of a trace, so each fiber is exact. -/
theorem fiber_card {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (S : Finset (Fin n)) (hS : S ∈ H.image (fun e => e ∩ A)) :
    (H.filter (fun e => e ∩ A = S)).card = (n - A.card).choose (r - S.card) := by
  classical
  obtain ⟨f, hf, hfS⟩ := mem_image.mp hS
  have hSA : S ⊆ A := hfS ▸ inter_subset_right
  have hSr : S.card ≤ r := by
    rw [← hfS, ← hH f hf]
    exact card_le_card inter_subset_left
  have heq : H.filter (fun e => e ∩ A = S) =
      ((univ : Finset (Fin n)).powersetCard r).filter (fun e => e ∩ A = S) := by
    ext e
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨he, heS⟩
      exact ⟨hH e he, heS⟩
    · rintro ⟨her, heS⟩
      refine ⟨?_, heS⟩
      apply Submissions.Erdos1020MatchingTraceCompletion.Main.mem_of_trace_subset
        hr H A hH hfree hmax hA hcut hstable e her
      exact ⟨f, hf, by rw [hfS, ← heS]; exact inter_subset_left⟩
  rw [heq, full_fiber_card A S hSA hSr, Fintype.card_fin]

/-- Partition the family by its head traces and count the exact completions. -/
theorem card_eq_trace_sum {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    H.card = ∑ S ∈ H.image (fun e => e ∩ A), (n - A.card).choose (r - S.card) := by
  classical
  rw [card_eq_sum_card_image (fun e => e ∩ A) H]
  apply sum_congr rfl
  intro S hS
  exact fiber_card hr H A hH hfree hmax hA hcut hstable S hS

end Submissions.Erdos1020MatchingTraceCounts.Main

namespace Submissions.Erdos1020MatchingWeightedIncidence.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- Count each weight once for every selected block set that contains its support. -/
theorem weighted_incidence {α : Type*} [DecidableEq α] {s r : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (F : Finset (Finset α))
    (hF : ∀ S ∈ F, S ⊆ G ∪ univ.biUnion B)
    (hFr : ∀ S ∈ F, S.card ≤ r) (w : Finset α → ℚ) :
    (∑ M ∈ (univ : Finset (Fin s)).powersetCard r,
      ∑ S ∈ F.filter (fun S => S ⊆ region G B M), w S) =
      ∑ S ∈ F, ((s - (support B S).card).choose (r - (support B S).card) : ℚ) * w S := by
  classical
  calc
    _ = ∑ S ∈ F, ∑ M ∈ ((univ : Finset (Fin s)).powersetCard r).filter
        (fun M => S ⊆ region G B M), w S := by
      simp only [sum_filter]
      exact sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      rw [sum_const, nsmul_eq_mul,
        local_multiplicity_card G B hB hG S (hF S hS) (hFr S hS)]

/-- Dividing by the positive support multiplicity distributes each numerator exactly once. -/
theorem normalized_incidence {α : Type*} [DecidableEq α] {s r : ℕ} (hrs : r ≤ s)
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (F : Finset (Finset α))
    (hF : ∀ S ∈ F, S ⊆ G ∪ univ.biUnion B)
    (hFr : ∀ S ∈ F, S.card ≤ r) (a : Finset α → ℚ) :
    (∑ M ∈ (univ : Finset (Fin s)).powersetCard r,
      ∑ S ∈ F.filter (fun S => S ⊆ region G B M),
        a S / ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) =
      ∑ S ∈ F, a S := by
  classical
  rw [weighted_incidence G B hB hG F hF hFr]
  apply sum_congr rfl
  intro S hS
  have hc : (support B S).card ≤ r := (support_card_le_card B hB S).trans (hFr S hS)
  have hpos : 0 < (s - (support B S).card).choose (r - (support B S).card) :=
    Nat.choose_pos (by omega)
  have hne : ((s - (support B S).card).choose (r - (support B S).card) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hpos.ne'
  exact mul_div_cancel₀ (a S) hne

end Submissions.Erdos1020MatchingWeightedIncidence.Main

namespace Submissions.Erdos1020MatchingTraceIncidence.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingWeightedIncidence.Main

/-- The exact local trace weights sum to the cardinality of the original family. -/
theorem trace_weight_sum {n r k s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (hpart : G ∪ univ.biUnion B = A) :
    (∑ M ∈ (univ : Finset (Fin s)).powersetCard r,
      ∑ S ∈ (H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M),
        ((n - A.card).choose (r - S.card) : ℚ) /
          ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) =
      (H.card : ℚ) := by
  classical
  have hF : ∀ S ∈ H.image (fun e => e ∩ A), S ⊆ G ∪ univ.biUnion B := by
    intro S hS
    obtain ⟨f, _, rfl⟩ := mem_image.mp hS
    rw [hpart]
    exact inter_subset_right
  have hFr : ∀ S ∈ H.image (fun e => e ∩ A), S.card ≤ r := by
    intro S hS
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hS
    exact (card_le_card inter_subset_left).trans_eq (hH f hf)
  rw [normalized_incidence hrs G B hB hG _ hF hFr]
  rw [← Nat.cast_sum,
    ← Submissions.Erdos1020MatchingTraceCounts.Main.card_eq_trace_sum
      hr H A hH hfree hmax hA hcut hstable]

/-- The comparison weights of all rank-r head sets sum to the clique cardinality. -/
theorem clique_weight_sum {α : Type*} [DecidableEq α] {s r : ℕ} (hrs : r ≤ s)
    (A G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (hpart : G ∪ univ.biUnion B = A) :
    (∑ M ∈ (univ : Finset (Fin s)).powersetCard r,
      ∑ S ∈ (A.powersetCard r).filter (fun S => S ⊆ region G B M),
        (1 : ℚ) / ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) =
      (A.card.choose r : ℚ) := by
  classical
  have hF : ∀ S ∈ A.powersetCard r, S ⊆ G ∪ univ.biUnion B := by
    intro S hS
    rw [hpart]
    exact (mem_powersetCard.mp hS).1
  have hFr : ∀ S ∈ A.powersetCard r, S.card ≤ r := by
    intro S hS
    exact (mem_powersetCard.mp hS).2.le
  rw [normalized_incidence hrs G B hB hG _ hF hFr]
  simp only [sum_const, nsmul_eq_mul, mul_one, card_powersetCard]

end Submissions.Erdos1020MatchingTraceIncidence.Main

namespace Submissions.Erdos1020MatchingTraceGlobalBound.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingTraceIncidence.Main

/-- Sum the local trace comparisons using their exact multiplicities. -/
theorem card_le_of_local {n r k s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hmax : ∀ K : Finset (Finset (Fin n)),
      Uniform K r → MatchingFree K k → K.card ≤ H.card)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (hpart : G ∪ univ.biUnion B = A)
    (hlocal : ∀ M ∈ (univ : Finset (Fin s)).powersetCard r,
      (∑ S ∈ (H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M),
        ((n - A.card).choose (r - S.card) : ℚ) /
          ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) ≤
      ∑ S ∈ (region G B M).powersetCard r,
        ((n - A.card).choose (r - S.card) : ℚ) /
          ((s - (support B S).card).choose (r - (support B S).card) : ℚ)) :
    H.card ≤ A.card.choose r := by
  classical
  have hregion (M : Finset (Fin s)) : region G B M ⊆ A := by
    intro x hx
    rw [← hpart]
    rcases mem_union.mp hx with hxG | hxB
    · exact mem_union_left _ hxG
    · obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hxB
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, hxi⟩)
  have hsets (M : Finset (Fin s)) :
      (region G B M).powersetCard r =
        (A.powersetCard r).filter (fun S => S ⊆ region G B M) := by
    ext S
    constructor
    · intro hS
      obtain ⟨hSU, hSr⟩ := mem_powersetCard.mp hS
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hSU.trans (hregion M), hSr⟩, hSU⟩
    · intro hS
      obtain ⟨hSA, hSU⟩ := mem_filter.mp hS
      exact mem_powersetCard.mpr ⟨hSU, (mem_powersetCard.mp hSA).2⟩
  apply (Nat.cast_le (α := ℚ)).mp
  calc
    (H.card : ℚ) = _ :=
      (trace_weight_sum hr hrs H A hH hfree hmax hA hcut hstable G B hB hG hpart).symm
    _ ≤ _ := sum_le_sum hlocal
    _ = ∑ M ∈ (univ : Finset (Fin s)).powersetCard r,
        ∑ S ∈ (A.powersetCard r).filter (fun S => S ⊆ region G B M),
          (1 : ℚ) / ((s - (support B S).card).choose (r - (support B S).card) : ℚ) := by
      apply sum_congr rfl
      intro M _
      rw [hsets M]
      apply sum_congr rfl
      intro S hS
      have hSr := (mem_powersetCard.mp (mem_filter.mp hS).1).2
      simp only [hSr, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
    _ = (A.card.choose r : ℚ) := clique_weight_sum hrs A G B hB hG hpart

end Submissions.Erdos1020MatchingTraceGlobalBound.Main

namespace Submissions.Erdos1020MatchingNearPerfect.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- The clique bound in the explicit conservative near-perfect range. -/
theorem clique_bound {n r k : ℕ} (hr : 3 ≤ r) (hk : 1 ≤ k)
    (hn : r * k ≤ n)
    (hguard : 2 * (∑ d ∈ range r, (r * r + r - 1).choose d) *
      (n - (r * k - 1)) ≤ k - r)
    (H : Finset (Finset (Fin n))) (hH : Uniform H r)
    (hfree : MatchingFree H k) : H.card ≤ (r * k - 1).choose r := by
  classical
  let C := ∑ d ∈ range r, (r * r + r - 1).choose d
  let N := n - (r * k - 1)
  have hrkpos : 0 < r * k := Nat.mul_pos (by omega) (by omega)
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hC : 1 ≤ C := by
    have hs : (r * r + r - 1).choose 0 ≤
        ∑ d ∈ range r, (r * r + r - 1).choose d :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
    simpa only [Nat.choose_zero_right] using hs
  change 2 * C * N ≤ k - r at hguard
  have htwo : 2 ≤ 2 * C * N := calc
    2 = 2 * 1 * 1 := by decide
    _ ≤ 2 * C * N := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hC) hN
  have hkr : 2 ≤ k - r := htwo.trans hguard
  have hrs : r ≤ k - 1 := by omega
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hmle : r * k - 1 ≤ n := (Nat.sub_le _ _).trans hn
  let emb : Fin (r * k - 1) ↪ Fin n :=
    ⟨fun v => ⟨v.val, lt_of_lt_of_le v.isLt hmle⟩,
      fun _ _ h => Fin.ext (congrArg (fun v : Fin n => v.val) h)⟩
  let A : Finset (Fin n) := univ.map emb
  have hAc : A.card = r * k - 1 := by simp [A]
  have hAmem (v : Fin n) : v ∈ A ↔ v.val < r * k - 1 := by
    constructor
    · intro hv
      obtain ⟨w, _, rfl⟩ := mem_map.mp hv
      exact w.isLt
    · intro hv
      exact mem_map.mpr ⟨⟨v.val, hv⟩, mem_univ _, Fin.ext rfl⟩
  have hA : A.card + 1 = r * k := by rw [hAc]; omega
  have hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x := by
    intro v hv x hx
    have hv' := (hAmem v).mp hv
    have hx' : ¬ x.val < r * k - 1 := fun h => hx ((hAmem x).mpr h)
    change v.val < x.val
    omega
  obtain ⟨F, hHF, hFu, hFm, hmax, hstable⟩ :=
    Submissions.Erdos1020MatchingMaximalShift.Main.exists_maximal_shifted H hH hfree
  obtain ⟨G, hGA, hGc, _hgap, hGmin, B, hBF, hBd, hGB, hBA, hpart⟩ :=
    Submissions.Erdos1020MatchingGapPartition.Main.exists_minimum_gap_partition
      (by omega) hk hn F A hFu hFm hmax hA hcut hstable
  have hBne (i : Fin (k - 1)) : (B i).Nonempty :=
    card_pos.mp (by rw [hFu (B i) (hBF i)]; omega)
  let a : Fin (k - 1) → Fin n := fun i => (B i).min' (hBne i)
  have ha (i : Fin (k - 1)) : a i ∈ B i := (B i).min'_mem (hBne i)
  have hamin (i : Fin (k - 1)) (x : Fin n) (hx : x ∈ B i) : a i ≤ x :=
    (B i).min'_le x hx
  have hhub (i : Fin (k - 1)) : insert (a i) G ∈ F :=
    Submissions.Erdos1020MatchingBlockMinimum.Main.insert_min_mem
      (by omega) F A hFu hFm hmax hA hcut hstable G hGA hGc hGmin
      (B i) (hBF i) (hBA i) (hGB i) (a i) (ha i) (hamin i)
  have hguard' : 2 * C * (n - A.card) ≤ (k - 1) - r + 1 := by
    rw [hAc]
    change 2 * C * N ≤ (k - 1) - r + 1
    omega
  have hAk : A.card + 1 = r * ((k - 1) + 1) := by
    simpa only [hkpred] using hA
  have hFm' : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ F ∧ K.card = (k - 1) + 1 ∧
      ∀ e ∈ K, ∀ e' ∈ K, e ≠ e' → Disjoint e e' := by
    simpa only [MatchingFree, hkpred] using hFm
  have hbound : F.card ≤ A.card.choose r :=
    Submissions.Erdos1020MatchingTraceGlobalBound.Main.card_le_of_local
      (by omega) hrs F A hFu hFm hmax hA hcut hstable G B hBd hGB hpart (by
        intro M hM
        exact Submissions.Erdos1020MatchingNearPerfectLocal.Main.local_bound
          (by omega) hrs F A hFu hAk hcut hstable hFm' G hGA hGc
          B hBF hBA hBd hGB a ha hamin hhub M (mem_powersetCard.mp hM).2 hguard')
  exact hHF.trans (by simpa only [hAc] using hbound)

end Submissions.Erdos1020MatchingNearPerfect.Main

namespace Submissions.Erdos1020MatchingNearPerfectProof.Main

/-- The original extremal expression follows from the stronger near-perfect clique bound. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → r * k ≤ n →
      2 * (∑ d ∈ Finset.range r, (r * r + r - 1).choose d) *
        (n - (r * k - 1)) ≤ k - r →
      ∀ H : Finset (Finset (Fin n)), (∀ e ∈ H, e.card = r) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  intro n r k hr hk hn hguard H hH hM
  exact (Submissions.Erdos1020MatchingNearPerfect.Main.clique_bound
    hr hk hn hguard H hH hM).trans (le_max_left _ _)

end Submissions.Erdos1020MatchingNearPerfectProof.Main
