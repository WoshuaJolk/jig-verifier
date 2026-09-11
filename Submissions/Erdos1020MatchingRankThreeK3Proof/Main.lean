import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Finset.Preimage
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Logic.Equiv.Fin.Basic

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

end Submissions.Erdos1020RainbowShift.Main

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

end Submissions.Erdos1020ShiftNormalize.Main

namespace Submissions.Erdos1020MatchingRankThreeMaxExtension.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- A compression of an extension retains a subfamily already stable under it. -/
theorem subset_singleton_compression {α : Type*} [DecidableEq α]
    (H K : Finset (Finset α)) (i j : α)
    (hHK : H ⊆ K) (hstable : UV.IsCompressed {i} {j} H) :
    H ⊆ UV.compression {i} {j} K := by
  intro e he
  have hce : UV.compress {i} {j} e ∈ H := by
    rw [← hstable.eq]
    exact UV.compress_mem_compression he
  exact UV.mem_compression.mpr (Or.inl ⟨hHK he, hHK hce⟩)

/-- Maximize cardinality among extensions of the given shifted family, then
minimize the label sum. The comparison is restricted to extensions of `H`. -/
theorem exists_maximal_shifted_extension {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (hH : Uniform H r)
    (hfree : MatchingFree H k)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    ∃ K : Finset (Finset (Fin n)), H ⊆ K ∧ Uniform K r ∧ MatchingFree K k ∧
      (∀ L : Finset (Finset (Fin n)), H ⊆ L → Uniform L r →
        MatchingFree L k → L.card ≤ K.card) ∧
      (∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} K) := by
  classical
  let candidates : Finset (Finset (Finset (Fin n))) :=
    univ.filter (fun K => H ⊆ K ∧ Uniform K r ∧ MatchingFree K k)
  have hmem : H ∈ candidates := by simp [candidates, hH, hfree]
  obtain ⟨M, hM, hmax⟩ := exists_max_image candidates Finset.card ⟨H, hmem⟩
  let fixed : Finset (Finset (Finset (Fin n))) :=
    candidates.filter (fun K => K.card = M.card)
  have hMfixed : M ∈ fixed := by simp [fixed, hM]
  obtain ⟨K, hK, hmin⟩ := exists_min_image fixed weight ⟨M, hMfixed⟩
  have hKcand : K ∈ candidates := (mem_filter.mp hK).1
  have hKcard : K.card = M.card := (mem_filter.mp hK).2
  have hprops : H ⊆ K ∧ Uniform K r ∧ MatchingFree K k :=
    (mem_filter.mp hKcand).2
  refine ⟨K, hprops.1, hprops.2.1, hprops.2.2, ?_, ?_⟩
  · intro L hHL hL hLm
    rw [hKcard]
    exact hmax L (mem_filter.mpr ⟨mem_univ _, hHL, hL, hLm⟩)
  · intro i j hij
    change UV.compression {i} {j} K = K
    by_contra hne
    have hcompcand : UV.compression {i} {j} K ∈ candidates := by
      apply mem_filter.mpr
      exact ⟨mem_univ _,
        subset_singleton_compression H K i j hprops.1 (hstable i j hij),
        uniform_singleton_compression hprops.2.1 i j,
        matchingFree_singleton_compression hr hprops.2.1 hprops.2.2 i j⟩
    have hcomp : UV.compression {i} {j} K ∈ fixed := by
      apply mem_filter.mpr
      refine ⟨hcompcand, ?_⟩
      simpa only [UV.card_compression] using hKcard
    exact (not_lt_of_ge (hmin _ hcomp)) (weight_singleton_compression_lt hij hne)

/-- An optimal extension is saturated: adding a missing uniform edge creates
a forbidden matching. No comparison with families outside the extensions is used. -/
theorem not_matchingFree_insert_of_extension_maximal {α : Type*} [DecidableEq α]
    {r k : ℕ} (H K : Finset (Finset α)) (hHK : H ⊆ K) (hK : Uniform K r)
    (hmax : ∀ L : Finset (Finset α), H ⊆ L → Uniform L r →
      MatchingFree L k → L.card ≤ K.card)
    (e : Finset α) (her : e.card = r) (he : e ∉ K) :
    ¬ MatchingFree (insert e K) k := by
  intro hfree
  have hu : Uniform (insert e K) r := by
    intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact her
    · exact hK f hf
  have hle := hmax (insert e K) (fun f hf => mem_insert_of_mem (hHK hf)) hu hfree
  rw [card_insert_of_notMem he] at hle
  omega

/-- A positive-rank shifted family has a containing shifted, saturated extension. -/
theorem exists_saturated_shifted_extension {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (hH : Uniform H r)
    (hfree : MatchingFree H k)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) :
    ∃ K : Finset (Finset (Fin n)), H ⊆ K ∧ Uniform K r ∧ MatchingFree K k ∧
      (∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} K) ∧
      (∀ e : Finset (Fin n), e.card = r → e ∉ K →
        ¬ MatchingFree (insert e K) k) := by
  obtain ⟨K, hHK, hK, hKm, hmax, hKs⟩ :=
    exists_maximal_shifted_extension hr H hH hfree hstable
  exact ⟨K, hHK, hK, hKm, hKs,
    not_matchingFree_insert_of_extension_maximal H K hHK hK hmax⟩

end Submissions.Erdos1020MatchingRankThreeMaxExtension.Main

-- Source: verification/rank-three-gap-lift.lean
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


end Submissions.Erdos1020RainbowLift.Main

-- Source: TraceGapBody.lean
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

-- Source: verification/rank-three-gap-trace-core.lean
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


end Submissions.Erdos1020MatchingTrace.Main

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

namespace Submissions.Erdos1020MatchingRankThreeGap.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- Packing an actual matching that avoids the least head vertex leaves a
missing two-point trace containing that vertex. -/
theorem exists_missing_pair {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H (s + 1))
    (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hMv : ∀ e ∈ M, v ∉ e) :
    ∃ d ∈ A, v < d ∧ {v, d} ∉ H.image (fun e => e ∩ A) := by
  classical
  have hcap : 3 * Fintype.card M ≤ (A \ {v}).card := by
    rw [Fintype.card_coe, hMc, sdiff_singleton_eq_erase, card_erase_of_mem hvA]
    omega
  obtain ⟨B, hBH, hBd, hBv, hBA⟩ :=
    Submissions.Erdos1020MatchingPack.Main.exists_packed_matching H A {v} hH hcap
      hcut hstable (fun c : M => c.val) (fun c => hMH c.property)
      (fun c d hcd => hMd c.val c.property d.val d.property
        (fun h => hcd (Subtype.ext h)))
      (fun c => disjoint_singleton_left.mpr (hMv c.val c.property))
  let U := univ.biUnion B
  have hBc (i : M) : (B i).card = 3 := hH _ (hBH i)
  have hUc : U.card = 3 * s := by
    dsimp only [U]
    rw [card_biUnion (fun i _ j _ hij => hBd hij)]
    simp [hBc, hMc, Nat.mul_comm]
  have hUA : U ⊆ A := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
    exact hBA i hxi
  have hvU : v ∉ U := by
    intro hv
    obtain ⟨i, _, hvi⟩ := mem_biUnion.mp hv
    exact disjoint_singleton_left.mp (hBv i) hvi
  let G := A \ U
  have hGA : G ⊆ A := sdiff_subset
  have hGc : G.card = 2 := by
    dsimp only [G]
    rw [card_sdiff_of_subset hUA, hUc]
    omega
  have hvG : v ∈ G := mem_sdiff.mpr ⟨hvA, hvU⟩
  have hGB (i : M) : Disjoint G (B i) := by
    apply disjoint_left.mpr
    intro x hxG hxB
    exact (mem_sdiff.mp hxG).2 (mem_biUnion.mpr ⟨i, mem_univ _, hxB⟩)
  have hgap : G ∉ H.image (fun e => e ∩ A) := by
    intro htrace
    obtain ⟨e, he, heA⟩ := mem_image.mp htrace
    let f : Option M → Finset (Fin n) :=
      fun i => match i with | none => e | some c => B c
    have hf : ∀ i, f i ∈ H := by
      intro i
      cases i with
      | none => exact he
      | some c => exact hBH c
    apply Submissions.Erdos1020MatchingTrace.Main.no_indexed_trace_matching
      (by decide) H A hH
      (by simp only [Fintype.card_option, Fintype.card_coe, hMc])
      hA hcut hstable hfree f hf
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some c =>
        change Disjoint (e ∩ A) (B c ∩ A)
        rw [heA]
        exact (hGB c).mono (Subset.refl _) inter_subset_left
    | some c =>
      cases j with
      | none =>
        change Disjoint (B c ∩ A) (e ∩ A)
        rw [heA]
        exact ((hGB c).mono (Subset.refl _) inter_subset_left).symm
      | some d =>
        exact (hBd (fun h => hij (congrArg some h))).mono
          inter_subset_left inter_subset_left
  have hec : (G.erase v).card = 1 := by rw [card_erase_of_mem hvG, hGc]
  obtain ⟨d, hd⟩ := card_eq_one.mp hec
  have hde : d ∈ G.erase v := by rw [hd]; exact mem_singleton_self _
  have hdG : d ∈ G := mem_of_mem_erase hde
  have hGpair : G = {v, d} := by
    calc
      G = insert v (G.erase v) := (insert_erase hvG).symm
      _ = {v, d} := by rw [hd]
  refine ⟨d, hGA hdG, lt_of_le_of_ne (hleast d (hGA hdG))
    (Ne.symm (mem_erase.mp hde).1), ?_⟩
  simpa only [hGpair] using hgap

/-- Minimize only the second endpoint among missing pairs containing v.
This is not minimization of the sum over all missing pairs. -/
theorem exists_minimum_pair {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H (s + 1))
    (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hMv : ∀ e ∈ M, v ∉ e) :
    ∃ d ∈ A, v < d ∧ {v, d} ∉ H.image (fun e => e ∩ A) ∧
      ∀ x ∈ A, v < x → {v, x} ∉ H.image (fun e => e ∩ A) → d ≤ x := by
  classical
  let C := A.filter (fun d => v < d ∧ {v, d} ∉ H.image (fun e => e ∩ A))
  obtain ⟨d₀, hd₀A, hvd₀, hd₀⟩ := exists_missing_pair
    H A hH hfree hA hcut hstable v hvA hleast M hMH hMc hMd hMv
  obtain ⟨d, hd, hmin⟩ := exists_min_image C (fun x : Fin n => x.val)
    ⟨d₀, mem_filter.mpr ⟨hd₀A, hvd₀, hd₀⟩⟩
  have hp := mem_filter.mp hd
  refine ⟨d, hp.1, hp.2.1, hp.2.2, ?_⟩
  intro x hx hvx hnot
  exact hmin x (mem_filter.mpr ⟨hx, hvx, hnot⟩)

end Submissions.Erdos1020MatchingRankThreeGap.Main

namespace Submissions.Erdos1020MatchingRankThreeSaturated.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

/-- Saturation supplies a forbidden matching after a missing uniform edge is inserted. -/
theorem matching_of_insert {α : Type*} [DecidableEq α] {r k : ℕ}
    (G : Finset (Finset α))
    (hsat : ∀ e : Finset α, e.card = r → e ∉ G → ¬ MatchingFree (insert e G) k)
    (e : Finset α) (her : e.card = r) (he : e ∉ G) :
    ∃ M : Finset (Finset α), M ⊆ insert e G ∧ M.card = k ∧
      ∀ f ∈ M, ∀ g ∈ M, f ≠ g → Disjoint f g := by
  classical
  by_contra hnone
  exact hsat e her he hnone

/-- A missing edge has a disjoint matching of size k-1 in a saturated family. -/
theorem saturating_matching {α : Type*} [DecidableEq α] {r k : ℕ}
    (G : Finset (Finset α)) (hGm : MatchingFree G k)
    (hsat : ∀ e : Finset α, e.card = r → e ∉ G → ¬ MatchingFree (insert e G) k)
    (e : Finset α) (her : e.card = r) (he : e ∉ G) :
    ∃ M : Finset (Finset α), M ⊆ G ∧ M.card = k - 1 ∧
      (∀ f ∈ M, ∀ g ∈ M, f ≠ g → Disjoint f g) ∧
      (∀ f ∈ M, Disjoint e f) := by
  obtain ⟨N, hNG, hNc, hNd⟩ := matching_of_insert G hsat e her he
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

/-- A saturated shifted family contains every uniform edge that contains
the head trace of one of its members, when the head has size r*k-1. -/
theorem mem_of_trace_subset {n r k : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hsat : ∀ e : Finset (Fin n), e.card = r → e ∉ H →
      ¬ MatchingFree (insert e H) k)
    (hA : A.card + 1 = r * k)
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Finset (Fin n)) (her : e.card = r)
    (htrace : ∃ f ∈ H, f ∩ A ⊆ e) : e ∈ H := by
  classical
  by_contra he
  obtain ⟨f, hf, hfa⟩ := htrace
  obtain ⟨N, hN, hNk, hNd⟩ :=
    matching_of_insert H hsat e her he
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

/-- A missing (r-1)-trace leaves a partition of the remaining head into k-1
members of a saturated shifted family. -/
theorem exists_partition_of_gap {n r k : ℕ} (hr : 0 < r) (hk : 1 ≤ k)
    (hn : r * k ≤ n) (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H r) (hfree : MatchingFree H k)
    (hsat : ∀ e : Finset (Fin n), e.card = r → e ∉ H →
      ¬ MatchingFree (insert e H) k)
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
    saturating_matching H hfree hsat (insert y G) her heH
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

/-- The middle vertex of every disjoint ordered head block completes the
minimal missing pair to an actual full edge (the short paper's Fact 9). -/
theorem insert_middle_mem {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H (s + 1))
    (hsat : ∀ e : Finset (Fin n), e.card = 3 → e ∉ H →
      ¬ MatchingFree (insert e H) (s + 1))
    (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v d : Fin n) (hvA : v ∈ A) (hdA : d ∈ A) (hvd : v < d)
    (hleast : ∀ x ∈ A, v ≤ x)
    (hmin : ∀ x ∈ A, v < x →
      {v, x} ∉ H.image (fun e => e ∩ A) → d ≤ x)
    (a b c : Fin n) (hab : a < b) (hbc : b < c)
    (he : ({a, b, c} : Finset (Fin n)) ∈ H)
    (heA : ({a, b, c} : Finset (Fin n)) ⊆ A)
    (hdis : Disjoint ({v, d} : Finset (Fin n)) {a, b, c}) :
    insert b ({v, d} : Finset (Fin n)) ∈ H := by
  classical
  have ha : a ∈ ({a, b, c} : Finset (Fin n)) := by simp
  have hb : b ∈ ({a, b, c} : Finset (Fin n)) := by simp
  have hc : c ∈ ({a, b, c} : Finset (Fin n)) := by simp
  have hvnot : v ∉ ({a, b, c} : Finset (Fin n)) :=
    disjoint_left.mp hdis (by simp)
  have hdnot : d ∉ ({a, b, c} : Finset (Fin n)) :=
    disjoint_left.mp hdis (by simp)
  have hva : v < a := lt_of_le_of_ne (hleast a (heA ha))
    (fun h => hvnot (h.symm ▸ ha))
  have hvb : v < b := hva.trans hab
  have hbdne : b ≠ d := fun h => hdnot (h ▸ hb)
  by_cases hbd : b < d
  · have hpair : ({v, b} : Finset (Fin n)) ∈ H.image (fun e => e ∩ A) := by
      by_contra hnot
      exact (not_le_of_gt hbd) (hmin b (heA hb) hvb hnot)
    obtain ⟨e, heH, heTrace⟩ := mem_image.mp hpair
    apply mem_of_trace_subset
      (by decide) H A hH hfree hsat hA hcut hstable (insert b {v, d})
      (by rw [card_insert_of_notMem (by simp [hvb.ne', hbdne]), card_pair hvd.ne])
    refine ⟨e, heH, ?_⟩
    rw [heTrace]
    intro x hx
    rcases mem_insert.mp hx with hxv | hxb
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl hxv))
    · exact mem_insert.mpr (Or.inl (mem_singleton.mp hxb))
  · have hdb : d < b := lt_of_le_of_ne (le_of_not_gt hbd) hbdne.symm
    have hvc : v ≠ c := (hvb.trans hbc).ne
    have hdc : d < c := hdb.trans hbc
    have hfirst : ({v, b, c} : Finset (Fin n)) ∈ H :=
      Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
        (hstable v a hva) (by simp [hab.ne, (hab.trans hbc).ne])
        (by simp [hvb.ne, hvc]) he
    have hcab : insert c ({v, b} : Finset (Fin n)) = {v, b, c} := by
      rw [insert_comm c v, pair_comm c b]
    have hsecond : insert d ({v, b} : Finset (Fin n)) ∈ H :=
      Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
        (hstable d c hdc) (by simp [hvc.symm, hbc.ne'])
        (by simp [hvd.ne', hdb.ne]) (by rwa [hcab])
    rw [insert_comm d v, pair_comm d b, ← insert_comm b v] at hsecond
    exact hsecond

private theorem exists_ordered_triple {n : ℕ} (B : Finset (Fin n)) (hBc : B.card = 3) :
    ∃ a b c, a < b ∧ b < c ∧ B = {a, b, c} := by
  classical
  have hBne : B.Nonempty := card_pos.mp (by omega)
  let a := B.min' hBne
  have ha : a ∈ B := B.min'_mem hBne
  have hec : (B.erase a).card = 2 := by rw [card_erase_of_mem ha, hBc]
  obtain ⟨b, c, hbc, heq⟩ := card_eq_two.mp hec
  have hb : b ∈ B.erase a := by rw [heq]; simp
  have hc : c ∈ B.erase a := by rw [heq]; simp
  have hab : a < b := min'_lt_of_mem_erase_min' B hBne hb
  have hac : a < c := min'_lt_of_mem_erase_min' B hBne hc
  have hB : B = {a, b, c} := by
    calc
      B = insert a (B.erase a) := (insert_erase ha).symm
      _ = {a, b, c} := by rw [heq]
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · exact ⟨a, b, c, hab, hlt, hB⟩
  · refine ⟨a, c, b, hac, hgt, ?_⟩
    simpa only [pair_comm b c] using hB

/-- A minimum missing pair containing the least vertex, its head partition,
and the actual middle-completion edge for each block. No row optimization is used. -/
theorem exists_minimum_pair_partition {n s : ℕ} (hn : 3 * (s + 1) ≤ n)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H (s + 1))
    (hsat : ∀ e : Finset (Fin n), e.card = 3 → e ∉ H →
      ¬ MatchingFree (insert e H) (s + 1))
    (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hMv : ∀ e ∈ M, v ∉ e) :
    ∃ d ∈ A, v < d ∧ {v, d} ∉ H.image (fun e => e ∩ A) ∧
      (∀ x ∈ A, v < x → {v, x} ∉ H.image (fun e => e ∩ A) → d ≤ x) ∧
      ∃ B : Fin s → Finset (Fin n), (∀ i, B i ∈ H) ∧
        Pairwise (fun i j => Disjoint (B i) (B j)) ∧
        (∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i)) ∧
        (∀ i, B i ⊆ A) ∧ {v, d} ∪ univ.biUnion B = A ∧
        ∀ i, ∃ a b c, a < b ∧ b < c ∧ B i = {a, b, c} ∧
          insert b ({v, d} : Finset (Fin n)) ∈ H := by
  classical
  obtain ⟨d, hdA, hvd, hgap, hmin⟩ := Submissions.Erdos1020MatchingRankThreeGap.Main.exists_minimum_pair
    H A hH hfree hA hcut hstable v hvA hleast M hMH hMc hMd hMv
  have hpart : ∃ B : Fin s → Finset (Fin n), (∀ i, B i ∈ H) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i)) ∧
      (∀ i, B i ⊆ A) ∧ {v, d} ∪ univ.biUnion B = A := by
    have hp := exists_partition_of_gap
        (r := 3) (k := s + 1)
        (by decide) (by omega) hn H A hH hfree hsat hA hcut hstable
        {v, d} (insert_subset hvA (singleton_subset_iff.mpr hdA))
        (by simpa using card_pair hvd.ne) hgap
    rw [Nat.add_sub_cancel] at hp
    exact hp
  obtain ⟨B, hBH, hBd, hBG, hBA, hcover⟩ := hpart
  refine ⟨d, hdA, hvd, hgap, hmin, B, hBH, hBd, hBG, hBA, hcover, ?_⟩
  intro i
  obtain ⟨a, b, c, hab, hbc, hB⟩ := exists_ordered_triple (B i) (hH _ (hBH i))
  refine ⟨a, b, c, hab, hbc, hB, ?_⟩
  exact insert_middle_mem H A hH hfree hsat hA hcut hstable v d hvA hdA hvd
    hleast hmin a b c hab hbc (by simpa only [hB] using hBH i)
    (by simpa only [hB] using hBA i) (by simpa only [hB] using hBG i)

end Submissions.Erdos1020MatchingRankThreeSaturated.Main

namespace Submissions.Erdos1020MatchingRankThreeLocal.Main

open Finset

/-- Lower one vertex of an actual trace within the head, by lowering a witnessing edge. -/
theorem replace_mem_trace {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (T : Finset (Fin n)) (hT : T ∈ H.image (fun e => e ∩ A))
    (x y : Fin n) (hxA : x ∈ A) (hxy : x < y) (hyT : y ∈ T) (hxT : x ∉ T) :
    insert x (T.erase y) ∈ H.image (fun e => e ∩ A) := by
  classical
  obtain ⟨e, he, heT⟩ := mem_image.mp hT
  have hyE : y ∈ e := (mem_inter.mp (heT.symm ▸ hyT)).1
  have hxE : x ∉ e := by
    intro hx
    exact hxT (heT ▸ mem_inter.mpr ⟨hx, hxA⟩)
  have he' : insert x (e.erase y) ∈ H :=
    Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
      (hstable x y hxy) (notMem_erase _ _)
      (notMem_mono (erase_subset _ _) hxE) (by simpa only [insert_erase hyE] using he)
  apply mem_image.mpr
  refine ⟨insert x (e.erase y), he', ?_⟩
  rw [insert_inter_of_mem hxA, erase_inter, heT]

end Submissions.Erdos1020MatchingRankThreeLocal.Main

namespace Submissions.Erdos1020MatchingRankThreeOne.Main

open Finset

/-- An actual matching avoiding v cannot coexist with one further edge whose
head trace is contained in {v}. The indexed trace theorem allows empty traces. -/
private theorem not_trace_subset_singleton {n r s : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (v : Fin n) (M : Finset (Finset (Fin n)))
    (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hMv : ∀ e ∈ M, v ∉ e) (e : Finset (Fin n)) (he : e ∈ H) :
    ¬ e ∩ A ⊆ {v} := by
  classical
  intro hsub
  let f : Option M → Finset (Fin n) :=
    fun c => match c with | none => e | some b => b.val
  have hf : ∀ c, f c ∈ H := by
    intro c
    cases c with
    | none => exact he
    | some b => exact hMH b.property
  have hdis (b : M) : Disjoint (e ∩ A) (b.val ∩ A) := by
    apply disjoint_left.mpr
    intro x hx hxb
    have hxv : x = v := mem_singleton.mp (hsub hx)
    exact hMv b.val b.property (hxv ▸ (mem_inter.mp hxb).1)
  apply Submissions.Erdos1020MatchingTrace.Main.no_indexed_trace_matching hr H A hH
    (by simp only [Fintype.card_option, Fintype.card_coe, hMc])
    hA hcut hstable hfree f hf
  intro c d hcd
  cases c with
  | none =>
    cases d with
    | none => exact (hcd rfl).elim
    | some b => exact hdis b
  | some b =>
    cases d with
    | none => exact (hdis b).symm
    | some b' =>
      exact (hMd b.val b.property b'.val b'.property
        (fun h => hcd (congrArg some (Subtype.ext h)))).mono
        inter_subset_left inter_subset_left

/-- If an actual s-matching avoids the smallest head vertex, every head trace
has size at least two. Matching edges need not lie inside the head. -/
theorem trace_card_two_le_of_avoiding_matching {n r s : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (v : Fin n) (hvA : v ∈ A) (hmin : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hMv : ∀ e ∈ M, v ∉ e) : ∀ e ∈ H, 2 ≤ (e ∩ A).card := by
  classical
  intro e he
  have hno := not_trace_subset_singleton hr H A hH hA hcut hstable hfree
    v M hMH hMc hMd hMv
  by_contra hbad
  have hc : (e ∩ A).card ≤ 1 := by omega
  by_cases hve : v ∈ e
  · apply hno e he
    intro x hx
    exact mem_singleton.mpr
      ((card_le_one_iff.mp hc) hx (mem_inter.mpr ⟨hve, hvA⟩))
  · by_cases hne : (e ∩ A).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxe := (mem_inter.mp hx).1
      have hxA := (mem_inter.mp hx).2
      have hvx : v ≠ x := fun h => hve (h.symm ▸ hxe)
      have hvlt : v < x := lt_of_le_of_ne (hmin x hxA) hvx
      have he' : insert v (e.erase x) ∈ H :=
        Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
          (hstable v x hvlt) (notMem_erase _ _)
          (notMem_mono (erase_subset _ _) hve)
          (by simpa only [insert_erase hxe] using he)
      apply hno _ he'
      intro y hy
      obtain ⟨hye, hyA⟩ := mem_inter.mp hy
      rcases mem_insert.mp hye with hyv | hyold
      · exact mem_singleton.mpr hyv
      · have hyx : y = x := (card_le_one_iff.mp hc)
          (mem_inter.mpr ⟨mem_of_mem_erase hyold, hyA⟩) hx
        exact ((mem_erase.mp hyold).1 hyx).elim
    · apply hno e he
      intro x hx
      exact (hne ⟨x, hx⟩).elim

end Submissions.Erdos1020MatchingRankThreeOne.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoRows.Main

open Finset

/-- Two disjoint triples admit ordered rows with the first row minimum smaller.
The permutation records the possible swap of the original two blocks. -/
theorem exists_rows {α : Type*} [LinearOrder α]
    (B : Fin 2 → Finset α) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcard : ∀ i, (B i).card = 3) :
    ∃ (J : Equiv.Perm (Fin 2)) (e : Fin 2 × Fin 3 ↪ α),
      (∀ i a, e (i, a) ∈ B (J i)) ∧
      (∀ i, StrictMono (fun a : Fin 3 => e (i, a))) ∧
      (∀ i, univ.image (fun a : Fin 3 => e (i, a)) = B (J i)) ∧
      e (0, 0) < e (1, 0) := by
  classical
  let row (i : Fin 2) : Fin 3 ↪o α := (B i).orderEmbOfFin (hcard i)
  have hrow (i : Fin 2) (a : Fin 3) : row i a ∈ B i :=
    (B i).orderEmbOfFin_mem (hcard i) a
  have hinj : Function.Injective (fun p : Fin 2 × Fin 3 => row p.1 p.2) := by
    intro p q hpq
    dsimp only at hpq
    have hi : p.1 = q.1 := by
      by_contra hne
      exact disjoint_left.mp (hB hne) (hrow p.1 p.2) (hpq.symm ▸ hrow q.1 q.2)
    apply Prod.ext hi
    rw [hi] at hpq
    exact (row q.1).injective hpq
  have hne : row 0 0 ≠ row 1 0 := by
    intro h
    have hp := @hinj (0, 0) (1, 0) h
    have : (0 : Fin 2) = 1 := congrArg Prod.fst hp
    exact (by decide : (0 : Fin 2) ≠ 1) this
  have hperm : ∃ J : Equiv.Perm (Fin 2), row (J 0) 0 < row (J 1) 0 := by
    by_cases hlt : row 0 0 < row 1 0
    · exact ⟨Equiv.refl _, hlt⟩
    · refine ⟨Equiv.swap 0 1, ?_⟩
      simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
  obtain ⟨J, hJ⟩ := hperm
  let e : Fin 2 × Fin 3 ↪ α :=
    ⟨fun p => row (J p.1) p.2, by
      intro p q hpq
      have h := @hinj (J p.1, p.2) (J q.1, q.2) hpq
      have hfirst : J p.1 = J q.1 := congrArg (fun x : Fin 2 × Fin 3 => x.1) h
      have hsecond := congrArg (fun x : Fin 2 × Fin 3 => x.2) h
      exact Prod.ext (J.injective hfirst) hsecond⟩
  refine ⟨J, e, ?_, ?_, ?_, hJ⟩
  · intro i a
    exact hrow (J i) a
  · intro i
    exact (row (J i)).strictMono
  · intro i
    exact (B (J i)).image_orderEmbOfFin_univ (hcard (J i))

end Submissions.Erdos1020MatchingRankThreeTwoRows.Main

namespace Submissions.Erdos1020MatchingTraceCounts.Main

open Finset

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

end Submissions.Erdos1020MatchingTraceCounts.Main

namespace Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main

open Finset

/-- Each trace fiber is bounded by all uniform completions. No saturation,
shifting, head-size or matching hypothesis is needed for this upper bound. -/
theorem card_le_trace_sum {n r : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = r) :
    H.card ≤ ∑ S ∈ H.image (fun E => E ∩ A), (n - A.card).choose (r - S.card) := by
  classical
  rw [card_eq_sum_card_image (fun E => E ∩ A) H]
  apply sum_le_sum
  intro S hS
  obtain ⟨E, hE, hEA⟩ := mem_image.mp hS
  have hSA : S ⊆ A := hEA ▸ inter_subset_right
  have hSr : S.card ≤ r := by
    rw [← hEA, ← hH E hE]
    exact card_le_card inter_subset_left
  have hsub : H.filter (fun E => E ∩ A = S) ⊆
      ((univ : Finset (Fin n)).powersetCard r).filter (fun E => E ∩ A = S) := by
    intro F hF
    obtain ⟨hFH, hFA⟩ := mem_filter.mp hF
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hH F hFH⟩, hFA⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ = _ := by
      rw [Submissions.Erdos1020MatchingTraceCounts.Main.full_fiber_card A S hSA hSr,
        Fintype.card_fin]

end Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main

namespace Submissions.Erdos1020MatchingRankThreeNarrow.Main

open Finset

/-- Complementation injects present fixed-size sets into missing complementary sets. -/
theorem card_le_missing_complements {α : Type*} [DecidableEq α]
    (U : Finset α) (r : ℕ) (P F : Finset (Finset α))
    (hPU : ∀ S ∈ P, S ⊆ U) (hPc : ∀ S ∈ P, S.card = r)
    (hmissing : ∀ S ∈ P, U \ S ∉ F) :
    P.card ≤ (U.powersetCard (U.card - r) \ F).card := by
  classical
  have hinj : Set.InjOn (fun S => U \ S) (P : Set (Finset α)) := by
    intro S hS T hT heq
    have h := congrArg (fun W => U \ W) heq
    rwa [Finset.sdiff_sdiff_eq_self (hPU S hS), Finset.sdiff_sdiff_eq_self (hPU T hT)] at h
  have hsub : P.image (fun S => U \ S) ⊆ U.powersetCard (U.card - r) \ F := by
    intro W hW
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hW
    refine mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset, ?_⟩, hmissing S hS⟩
    rw [card_sdiff_of_subset (hPU S hS), hPc S hS]
  calc
    P.card = (P.image (fun S => U \ S)).card := (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub

/-- An intersecting family of pairs on four vertices has at most three members,
by pairing each pair with its missing complement. -/
theorem pairs_four_card_le_three {α : Type*} [DecidableEq α]
    (U : Finset α) (hUc : U.card = 4) (P : Finset (Finset α))
    (hPU : ∀ S ∈ P, S ⊆ U) (hPc : ∀ S ∈ P, S.card = 2)
    (hinter : ∀ S ∈ P, ∀ T ∈ P, ¬ Disjoint S T) : P.card ≤ 3 := by
  have hchoose : Nat.choose 4 2 = 6 := by decide
  have hmissing : ∀ S ∈ P, U \ S ∉ P := by
    intro S hS hC
    exact hinter S hS (U \ S) hC disjoint_sdiff
  have h := card_le_missing_complements U 2 P P hPU hPc hmissing
  have hsub : P ⊆ U.powersetCard 2 := fun S hS =>
    mem_powersetCard.mpr ⟨hPU S hS, hPc S hS⟩
  have hc : (U.powersetCard 2 \ P).card = 6 - P.card := by
    rw [card_sdiff_of_subset hsub, card_powersetCard, hUc, hchoose]
  have h' : P.card ≤ 6 - P.card := by simpa only [hUc, hc] using h
  have hle : P.card ≤ 6 := by
    have hle := card_le_card hsub
    simpa only [card_powersetCard, hUc, hchoose] using hle
  omega

/-- The fixed five-vertex region gives one missing triple per pair and at most
three pairs, whenever one designated vertex is absent from all pairs. -/
theorem narrow_bounds {α : Type*} [DecidableEq α]
    (U : Finset α) (hUc : U.card = 5) (d : α) (hdU : d ∈ U)
    (F : Finset (Finset α))
    (havoid : ∀ S ∈ F, S.card = 2 → d ∉ S)
    (hinter : ∀ S ∈ F, S ⊆ U → ∀ T ∈ F, T ⊆ U → ¬ Disjoint S T) :
    (F.filter (fun S => S ⊆ U ∧ S.card = 2)).card ≤ (U.powersetCard 3 \ F).card ∧
      (F.filter (fun S => S ⊆ U ∧ S.card = 2)).card ≤ 3 := by
  classical
  let P := F.filter (fun S => S ⊆ U ∧ S.card = 2)
  have hPF : ∀ S ∈ P, S ∈ F := fun _ hS => (mem_filter.mp hS).1
  have hPU : ∀ S ∈ P, S ⊆ U := fun _ hS => (mem_filter.mp hS).2.1
  have hPc : ∀ S ∈ P, S.card = 2 := fun _ hS => (mem_filter.mp hS).2.2
  have hmissing : ∀ S ∈ P, U \ S ∉ F := by
    intro S hS hC
    exact hinter S (hPF S hS) (hPU S hS) (U \ S) hC sdiff_subset disjoint_sdiff
  constructor
  · have h := card_le_missing_complements U 2 P F hPU hPc hmissing
    simpa only [hUc] using h
  · have hVc : (U.erase d).card = 4 := by rw [card_erase_of_mem hdU, hUc]
    apply pairs_four_card_le_three (U.erase d) hVc P
      (fun S hS x hx => mem_erase.mpr
        ⟨fun h => havoid S (hPF S hS) (hPc S hS) (h ▸ hx), hPU S hS hx⟩)
      hPc
    intro S hS T hT
    exact hinter S (hPF S hS) (hPU S hS) T (hPF T hT) (hPU T hT)

end Submissions.Erdos1020MatchingRankThreeNarrow.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main

open Finset

variable {α : Type*} [LinearOrder α]

/-- The actual cross-row pairs, recorded by their two heights. -/
def crossPairs (F : Finset (Finset α)) (e : Fin 2 × Fin 3 ↪ α) :
    Finset (Fin 3 × Fin 3) :=
  univ.filter (fun p => ({e (0, p.1), e (1, p.2)} : Finset α) ∈ F)

@[simp] theorem mem_crossPairs (F : Finset (Finset α))
    (e : Fin 2 × Fin 3 ↪ α) (i j : Fin 3) :
    (i, j) ∈ crossPairs F e ↔ ({e (0, i), e (1, j)} : Finset α) ∈ F := by
  simp [crossPairs]

private theorem no_three (F : Finset (Finset α))
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (P Q R : Finset α) (hP : P ∈ F) (hQ : Q ∈ F) (hR : R ∈ F)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R) : False := by
  let f : Fin 3 → Finset α := fun i => if i = 0 then P else if i = 1 then Q else R
  have hc (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hf : ∀ i, f i ∈ F := by
    intro i
    rcases hc i with rfl | rfl | rfl
    · simpa [f] using hP
    · simpa [f] using hQ
    · simpa [f] using hR
  apply hno f hf
  intro i j hij
  rcases hc i with rfl | rfl | rfl <;> rcases hc j with rfl | rfl | rfl
  all_goals first
    | exact (hij rfl).elim
    | simpa [f] using hPQ
    | simpa [f] using hPR
    | simpa [f] using hQR
    | simpa [f] using hPQ.symm
    | simpa [f] using hPR.symm
    | simpa [f] using hQR.symm

private theorem lower_pair (F : Finset (Finset α)) (A : Finset α)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (x y z : α) (hxA : x ∈ A) (hxy : x < y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hP : ({y, z} : Finset α) ∈ F) : ({x, z} : Finset α) ∈ F := by
  have h := hshift {y, z} hP x y hxA hxy (by simp) (by simp [hxy.ne, hxz])
  simpa [hyz] using h

/-- Lower either coordinate of an actual cross-row pair. -/
theorem coordinate_downward (F : Finset (Finset α)) (A : Finset α)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun j : Fin 3 => e (i, j))) :
    ∀ i j, (i, j) ∈ crossPairs F e → ∀ i' j',
      i' ≤ i → j' ≤ j → (i', j') ∈ crossPairs F e := by
  intro i j hP i' j' hi hj
  have hne (a b : Fin 3) : e (0, a) ≠ e (1, b) := by
    intro h
    have hp := e.injective h
    have hf := congrArg Prod.fst hp
    exact (by decide : (0 : Fin 2) ≠ 1) hf
  have hfirst : ({e (0, i'), e (1, j)} : Finset α) ∈ F := by
    rcases hi.eq_or_lt with hi | hi
    · simpa only [hi] using (mem_crossPairs F e i j).mp hP
    · exact lower_pair F A hshift _ _ _ (heA _) (hrow 0 hi) (hne _ _) (hne _ _)
        ((mem_crossPairs F e i j).mp hP)
  apply (mem_crossPairs F e i' j').mpr
  rcases hj.eq_or_lt with hj | hj
  · simpa only [hj] using hfirst
  · have h := lower_pair F A hshift (e (1, j')) (e (1, j)) (e (0, i'))
      (heA _) (hrow 1 hj) (Ne.symm (hne _ _)) (Ne.symm (hne _ _))
      (by simpa only [pair_comm] using hfirst)
    simpa only [pair_comm] using h

/-- The bottom/top pair in either row would leave a disjoint least/middle
pair and the entire other row, producing three disjoint members. -/
theorem internal_pair_missing (F : Finset (Finset α)) (A : Finset α)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun j : Fin 3 => e (i, j)))
    (v : α) (hvA : v ∈ A) (hv : ∀ p, v < e p)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (i j : Fin 2) (hij : i ≠ j)
    (hB : ({e (j, 0), e (j, 1), e (j, 2)} : Finset α) ∈ F) :
    ({e (i, 0), e (i, 2)} : Finset α) ∉ F := by
  have heq (p q : Fin 2 × Fin 3) : e p = e q ↔ p = q :=
    ⟨fun h => e.injective h, fun h => congrArg e h⟩
  have hvne (p : Fin 2 × Fin 3) : v ≠ e p := (hv p).ne
  have henv (p : Fin 2 × Fin 3) : e p ≠ v := (hv p).ne'
  intro hP
  have hvc : ({v, e (i, 2)} : Finset α) ∈ F :=
    lower_pair F A hshift _ _ _ hvA (hv _) (by simp [heq]) (hvne _) hP
  have hvb : ({v, e (i, 1)} : Finset α) ∈ F := by
    have h := lower_pair F A hshift (e (i, 1)) (e (i, 2)) v (heA _)
      (hrow i (by decide)) (henv _) (henv _) (by simpa only [pair_comm] using hvc)
    simpa only [pair_comm] using h
  apply no_three F hno {e (i, 0), e (i, 2)} {v, e (i, 1)}
    {e (j, 0), e (j, 1), e (j, 2)} hP hvb hB
  · simp [heq, hvne, henv]
  · simp [heq, hij, Ne.symm hij]
  · simp [heq, hij, Ne.symm hij, hvne, henv]

/-- Ordered row minima exclude the whole last first-coordinate fiber. -/
theorem first_top_absent (F : Finset (Finset α)) (A : Finset α)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun j : Fin 3 => e (i, j)))
    (hmin : e (0, 0) < e (1, 0))
    (v : α) (hvA : v ∈ A) (hv : ∀ p, v < e p)
    (hB : ({e (1, 0), e (1, 1), e (1, 2)} : Finset α) ∈ F)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    ∀ j, (2, j) ∉ crossPairs F e := by
  intro j hP
  have heq (p q : Fin 2 × Fin 3) : e p = e q ↔ p = q :=
    ⟨fun h => e.injective h, fun h => congrArg e h⟩
  have h20 := coordinate_downward F A hshift e heA hrow 2 j hP 2 0 (by decide) (by omega)
  have hpair := (mem_crossPairs F e 2 0).mp h20
  have hint : ({e (0, 0), e (0, 2)} : Finset α) ∈ F :=
    lower_pair F A hshift _ _ _ (heA _) hmin (by simp [heq]) (by simp [heq])
      (by simpa only [pair_comm] using hpair)
  exact internal_pair_missing F A hshift e heA hrow v hvA hv hno 0 1 (by decide) hB hint

/-- The two indicated cross pairs leave the lowered pair {v,b₁} disjoint
from both, contradicting the actual indexed matching prohibition. -/
theorem corner_incompatible (F : Finset (Finset α)) (A : Finset α)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun j : Fin 3 => e (i, j)))
    (v : α) (hvA : v ∈ A) (hv : ∀ p, v < e p)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    (0, 2) ∈ crossPairs F e → (1, 0) ∉ crossPairs F e := by
  intro hP hQ
  have heq (p q : Fin 2 × Fin 3) : e p = e q ↔ p = q :=
    ⟨fun h => e.injective h, fun h => congrArg e h⟩
  have hvne (p : Fin 2 × Fin 3) : v ≠ e p := (hv p).ne
  have henv (p : Fin 2 × Fin 3) : e p ≠ v := (hv p).ne'
  have hP' := (mem_crossPairs F e 0 2).mp hP
  have hQ' := (mem_crossPairs F e 1 0).mp hQ
  have hvc : ({v, e (1, 2)} : Finset α) ∈ F :=
    lower_pair F A hshift _ _ _ hvA (hv _) (by simp [heq]) (hvne _) hP'
  have hvb : ({v, e (1, 1)} : Finset α) ∈ F := by
    have h := lower_pair F A hshift (e (1, 1)) (e (1, 2)) v (heA _)
      (hrow 1 (by decide)) (henv _) (henv _) (by simpa only [pair_comm] using hvc)
    simpa only [pair_comm] using h
  apply no_three F hno {e (0, 0), e (1, 2)} {e (0, 1), e (1, 0)}
    {v, e (1, 1)} hP' hQ' hvb
  · simp [heq]
  · simp [heq, hvne, henv]
  · simp [heq, hvne, henv]

/-- All three pure-classifier premises for the actual cross-pair family.
The later cardinal premise is deliberately not included here. -/
theorem classifier_premises (F : Finset (Finset α)) (A : Finset α)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun j : Fin 3 => e (i, j)))
    (hmin : e (0, 0) < e (1, 0))
    (v : α) (hvA : v ∈ A) (hv : ∀ p, v < e p)
    (hB : ∀ i : Fin 2, ({e (i, 0), e (i, 1), e (i, 2)} : Finset α) ∈ F)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    (∀ i j, (i, j) ∈ crossPairs F e → ∀ i' j',
      i' ≤ i → j' ≤ j → (i', j') ∈ crossPairs F e) ∧
    (∀ j, (2, j) ∉ crossPairs F e) ∧
    ((0, 2) ∈ crossPairs F e → (1, 0) ∉ crossPairs F e) := by
  exact ⟨coordinate_downward F A hshift e heA hrow,
    first_top_absent F A hshift e heA hrow hmin v hvA hv (hB 1) hno,
    corner_incompatible F A hshift e heA hrow v hvA hv hno⟩

end Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoRowCounts.Main

open Finset

variable {α : Type*} [LinearOrder α]

def row (e : Fin 2 × Fin 3 ↪ α) (i : Fin 2) : Finset α :=
  univ.image (fun j : Fin 3 => e (i, j))

def narrowPairs (F : Finset (Finset α)) (v d : α)
    (e : Fin 2 × Fin 3 ↪ α) (i : Fin 2) : Finset (Finset α) :=
  F.filter (fun S => S ⊆ {v, d} ∪ row e i ∧ S.card = 2)

private theorem no_three (F : Finset (Finset α))
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (P Q R : Finset α) (hP : P ∈ F) (hQ : Q ∈ F) (hR : R ∈ F)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R) : False := by
  let f : Fin 3 → Finset α := fun i => if i = 0 then P else if i = 1 then Q else R
  apply hno f
  · intro i
    dsimp only [f]
    split_ifs
    · exact hP
    · exact hQ
    · exact hR
  · intro i j hij
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · exact (hij rfl).elim
    · exact hPQ
    · exact hPR
    · exact hPQ.symm
    · exact (hij rfl).elim
    · exact hQR
    · exact hPR.symm
    · exact hQR.symm
    · exact (hij rfl).elim

/-- Exact pair partition into the two narrow subfamilies and the actual
cross-row pairs, together with the two narrow bounds. No ordering of the
rows or rank restriction on other members of the family is needed. -/
theorem pair_counts (F : Finset (Finset α)) (A : Finset α)
    (hFA : ∀ S ∈ F, S ⊆ A)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (v d : α)
    (hhead : A = ({v, d} ∪ row e 0) ∪ row e 1)
    (hvd : v < d) (hleast : ∀ x ∈ A, v ≤ x)
    (hgap : ({v, d} : Finset α) ∉ F)
    (hGB : ∀ i : Fin 2, Disjoint ({v, d} : Finset α) (row e i))
    (hB : ∀ i : Fin 2, row e i ∈ F)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    (F.filter (fun S => S.card = 2)).card =
      (narrowPairs F v d e 0).card + (narrowPairs F v d e 1).card +
        (Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main.crossPairs F e).card ∧
      ∀ i : Fin 2, (narrowPairs F v d e i).card ≤ 3 := by
  classical
  let U := fun i : Fin 2 => ({v, d} : Finset α) ∪ row e i
  let N := fun i : Fin 2 => narrowPairs F v d e i
  let P := Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main.crossPairs F e
  let pair := fun p : Fin 3 × Fin 3 => ({e (0, p.1), e (1, p.2)} : Finset α)
  let C := P.image pair
  have hcross (i j : Fin 3) : e (0, i) ≠ e (1, j) := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst (e.injective h))
  have hpoint (i : Fin 2) (j : Fin 3) : e (i, j) ∈ row e i :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have hrowcard (i : Fin 2) : (row e i).card = 3 := by
    have hinj : Function.Injective (fun j : Fin 3 => e (i, j)) := by
      intro j k h
      exact congrArg Prod.snd (e.injective h)
    simpa only [row, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hrows : Disjoint (row e 0) (row e 1) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := mem_image.mp hx
    obtain ⟨j, _, hj⟩ := mem_image.mp hy
    exact hcross i j (hi.trans hj.symm)
  have hU0B1 : Disjoint (U 0) (row e 1) := disjoint_union_left.mpr ⟨hGB 1, hrows⟩
  have hU1B0 : Disjoint (U 1) (row e 0) := disjoint_union_left.mpr ⟨hGB 0, hrows.symm⟩
  have hUcard (i : Fin 2) : (U i).card = 5 := by
    dsimp only [U]
    rw [card_union_of_disjoint (hGB i), card_pair hvd.ne, hrowcard]
  have hvA : v ∈ A := by rw [hhead]; simp
  have havoid : ∀ S ∈ F, S.card = 2 → d ∉ S := by
    intro S hS hSc hdS
    have hec : (S.erase d).card = 1 := by rw [card_erase_of_mem hdS, hSc]
    obtain ⟨x, hx⟩ := card_eq_one.mp hec
    have hxe : x ∈ S.erase d := by rw [hx]; simp
    have hxd : x ≠ d := (mem_erase.mp hxe).1
    have hpair : S = {x, d} := by
      calc
        S = insert d (S.erase d) := (insert_erase hdS).symm
        _ = {d, x} := by rw [hx]
        _ = {x, d} := pair_comm _ _
    have hpairF : ({x, d} : Finset α) ∈ F := hpair ▸ hS
    by_cases hxv : x = v
    · exact hgap (hxv ▸ hpairF)
    have hvx : v < x :=
      lt_of_le_of_ne (hleast x (hFA S hS (mem_of_mem_erase hxe))) (Ne.symm hxv)
    have hnew := hshift {x, d} hpairF v x hvA hvx
      (by simp) (by simp [Ne.symm hxv, hvd.ne])
    apply hgap
    simpa [hxd] using hnew
  have hNbound (i : Fin 2) : (N i).card ≤ 3 := by
    apply (Submissions.Erdos1020MatchingRankThreeNarrow.Main.narrow_bounds
      (U i) (hUcard i) d (by simp [U]) F havoid ?_).2
    intro S hS hSU T hT hTU hST
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact no_three F hno S T (row e 1) hS hT (hB 1) hST
        (disjoint_of_subset_left hSU hU0B1) (disjoint_of_subset_left hTU hU0B1)
    · exact no_three F hno S T (row e 0) hS hT (hB 0) hST
        (disjoint_of_subset_left hSU hU1B0) (disjoint_of_subset_left hTU hU1B0)
  have hNF (i : Fin 2) (S : Finset α) (hS : S ∈ N i) :
      S ∈ F ∧ S ⊆ U i ∧ S.card = 2 := mem_filter.mp hS
  have hCF (S : Finset α) (hS : S ∈ C) : S ∈ F ∧ S.card = 2 := by
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := mem_image.mp hS
    exact ⟨(Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main.mem_crossPairs F e i j).mp hp,
      card_pair (hcross i j)⟩
  have hNN : Disjoint (N 0) (N 1) := by
    apply disjoint_left.mpr
    intro S hS0 hS1
    obtain ⟨hSF, hSU0, hSc⟩ := hNF 0 S hS0
    have hSU1 := (hNF 1 S hS1).2.1
    have hSG : S ⊆ {v, d} := by
      intro x hx
      rcases mem_union.mp (hSU0 hx) with hxG | hx0
      · exact hxG
      rcases mem_union.mp (hSU1 hx) with hxG | hx1
      · exact hxG
      exact (disjoint_left.mp hrows hx0 hx1).elim
    have hSG' : S = {v, d} := eq_of_subset_of_card_le hSG (by rw [card_pair hvd.ne, hSc])
    exact hgap (hSG' ▸ hSF)
  have hN0C : Disjoint (N 0) C := by
    apply disjoint_left.mpr
    intro S hS hC
    obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hC
    have hxU : e (1, j) ∈ U 0 := (hNF 0 _ hS).2.1 (by simp [pair])
    exact disjoint_left.mp hU0B1 hxU (hpoint 1 j)
  have hN1C : Disjoint (N 1) C := by
    apply disjoint_left.mpr
    intro S hS hC
    obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hC
    have hxU : e (0, i) ∈ U 1 := (hNF 1 _ hS).2.1 (by simp [pair])
    exact disjoint_left.mp hU1B0 hxU (hpoint 0 i)
  have hpartition : F.filter (fun S => S.card = 2) = (N 0 ∪ N 1) ∪ C := by
    apply Subset.antisymm
    · intro S hS
      obtain ⟨hSF, hSc⟩ := mem_filter.mp hS
      by_cases hSU0 : S ⊆ U 0
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hSF, hSU0, hSc⟩))
      by_cases hSU1 : S ⊆ U 1
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hSF, hSU1, hSc⟩))
      obtain ⟨x, hxS, hxU0⟩ := not_subset.mp hSU0
      obtain ⟨y, hyS, hyU1⟩ := not_subset.mp hSU1
      have hxB1 : x ∈ row e 1 := by
        have hxA := hFA S hSF hxS
        rw [hhead] at hxA
        exact (mem_union.mp hxA).resolve_left hxU0
      have hyB0 : y ∈ row e 0 := by
        have hyA := hFA S hSF hyS
        rw [hhead] at hyA
        rcases mem_union.mp hyA with hyU0 | hyB1
        · rcases mem_union.mp hyU0 with hyG | hyB0
          · exact (hyU1 (mem_union_left _ hyG)).elim
          · exact hyB0
        · exact (hyU1 (mem_union_right _ hyB1)).elim
      obtain ⟨i, _, hi⟩ := mem_image.mp hyB0
      obtain ⟨j, _, hj⟩ := mem_image.mp hxB1
      have hpS : pair (i, j) = S := by
        apply eq_of_subset_of_card_le
        · apply insert_subset
          · exact hi.symm ▸ hyS
          · exact singleton_subset_iff.mpr (hj.symm ▸ hxS)
        · simpa only [pair, card_pair (hcross i j), hSc] using (le_refl 2)
      have hpP : (i, j) ∈ P :=
        (Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main.mem_crossPairs F e i j).mpr
          (show pair (i, j) ∈ F from hpS.symm ▸ hSF)
      exact mem_union_right _ (mem_image.mpr ⟨(i, j), hpP, hpS⟩)
    · intro S hS
      rcases mem_union.mp hS with hN | hC
      · rcases mem_union.mp hN with hN0 | hN1
        · exact mem_filter.mpr ⟨(hNF 0 S hN0).1, (hNF 0 S hN0).2.2⟩
        · exact mem_filter.mpr ⟨(hNF 1 S hN1).1, (hNF 1 S hN1).2.2⟩
      · exact mem_filter.mpr (hCF S hC)
  have hpairinj : Function.Injective pair := by
    intro p q hpq
    have hfst : p.1 = q.1 := by
      have hm : e (0, p.1) ∈ pair q := hpq ▸ (by simp [pair])
      rcases (show e (0, p.1) = e (0, q.1) ∨ e (0, p.1) = e (1, q.2) by
        simpa only [pair, mem_insert, mem_singleton] using hm) with h | h
      · exact congrArg Prod.snd (e.injective h)
      · exact (hcross _ _ h).elim
    have hsnd : p.2 = q.2 := by
      have hm : e (1, p.2) ∈ pair q := hpq ▸ (by simp [pair])
      rcases (show e (1, p.2) = e (0, q.1) ∨ e (1, p.2) = e (1, q.2) by
        simpa only [pair, mem_insert, mem_singleton] using hm) with h | h
      · exact (hcross _ _ h.symm).elim
      · exact congrArg (fun z : Fin 2 × Fin 3 => z.2) (e.injective h)
    exact Prod.ext hfst hsnd
  have hCc : C.card = P.card := card_image_of_injective P hpairinj
  constructor
  · change (F.filter (fun S => S.card = 2)).card = (N 0).card + (N 1).card + P.card
    rw [hpartition, card_union_of_disjoint (disjoint_union_left.mpr ⟨hN0C, hN1C⟩),
      card_union_of_disjoint hNN, hCc]
  · exact hNbound

end Submissions.Erdos1020MatchingRankThreeTwoRowCounts.Main

namespace Submissions.Erdos1020MatchingRankThreeBaselinePair.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeTwoRowCounts.Main (row)

variable {α : Type*} [LinearOrder α]

/-- A nonempty actual pair subfamily contains the baseline pair. The
available endpoint minimum is derived from the exact head and row order. -/
theorem baseline_pair_mem (F : Finset (Finset α)) (A : Finset α)
    (hFA : ∀ S ∈ F, S ⊆ A)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (e : Fin 2 × Fin 3 ↪ α) (v d : α)
    (hhead : A = ({v, d} ∪ row e 0) ∪ row e 1)
    (hvd : v < d) (hleast : ∀ x ∈ A, v ≤ x)
    (hgap : ({v, d} : Finset α) ∉ F)
    (hGB : ∀ i : Fin 2, Disjoint ({v, d} : Finset α) (row e i))
    (hrow : ∀ i : Fin 2, StrictMono (fun j : Fin 3 => e (i, j)))
    (hmin : e (0, 0) < e (1, 0))
    (hpos : 0 < (F.filter (fun S => S.card = 2)).card) :
    ({v, e (0, 0)} : Finset α) ∈ F := by
  classical
  let a := e (0, 0)
  have hpoint (i : Fin 2) (j : Fin 3) : e (i, j) ∈ row e i :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have hvA : v ∈ A := by rw [hhead]; simp
  have haA : a ∈ A := by
    rw [hhead]
    exact mem_union_left _ (mem_union_right _ (hpoint 0 0))
  have haG : a ∉ ({v, d} : Finset α) :=
    disjoint_right.mp (hGB 0) (hpoint 0 0)
  have hav : a ≠ v := by
    intro h
    apply haG
    simp [h]
  have havoid : ∀ S ∈ F, S.card = 2 → d ∉ S := by
    intro S hS hSc hdS
    have hec : (S.erase d).card = 1 := by rw [card_erase_of_mem hdS, hSc]
    obtain ⟨x, hx⟩ := card_eq_one.mp hec
    have hxe : x ∈ S.erase d := by rw [hx]; simp
    have hxd : x ≠ d := (mem_erase.mp hxe).1
    have hpair : S = {x, d} := by
      calc
        S = insert d (S.erase d) := (insert_erase hdS).symm
        _ = {d, x} := by rw [hx]
        _ = {x, d} := pair_comm _ _
    have hpairF : ({x, d} : Finset α) ∈ F := hpair ▸ hS
    by_cases hxv : x = v
    · exact hgap (hxv ▸ hpairF)
    have hvx : v < x :=
      lt_of_le_of_ne (hleast x (hFA S hS (mem_of_mem_erase hxe))) (Ne.symm hxv)
    have hnew := hshift {x, d} hpairF v x hvA hvx
      (by simp) (by simp [Ne.symm hxv, hvd.ne])
    apply hgap
    simpa [hxd] using hnew
  have ha_lower : ∀ x ∈ A, x ≠ v → x ≠ d → a ≤ x := by
    intro x hx hxv hxd
    rw [hhead] at hx
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hx | hx
      · rcases mem_insert.mp hx with hx | hx
        · exact (hxv hx).elim
        · exact (hxd (mem_singleton.mp hx)).elim
      · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
        exact (hrow 0).monotone (by omega : (0 : Fin 3) ≤ j)
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact hmin.le.trans ((hrow 1).monotone (by omega : (0 : Fin 3) ≤ j))
  obtain ⟨S, hS⟩ := card_pos.mp hpos
  obtain ⟨hSF, hSc⟩ := mem_filter.mp hS
  have hdS : d ∉ S := havoid S hSF hSc
  have hstar : ∃ y, y ∈ A ∧ y ≠ v ∧ y ≠ d ∧ ({v, y} : Finset α) ∈ F := by
    by_cases hvS : v ∈ S
    · have hec : (S.erase v).card = 1 := by rw [card_erase_of_mem hvS, hSc]
      obtain ⟨y, hy⟩ := card_eq_one.mp hec
      have hye : y ∈ S.erase v := by rw [hy]; simp
      have hyS : y ∈ S := mem_of_mem_erase hye
      have hyv : y ≠ v := (mem_erase.mp hye).1
      have hyd : y ≠ d := by
        intro h
        exact hdS (h ▸ hyS)
      have hpair : S = {v, y} := by
        calc
          S = insert v (S.erase v) := (insert_erase hvS).symm
          _ = {v, y} := by rw [hy]
      exact ⟨y, hFA S hSF hyS, hyv, hyd, hpair ▸ hSF⟩
    · obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp hSc
      have hpairF : ({x, y} : Finset α) ∈ F := hpair ▸ hSF
      have hxA : x ∈ A := hFA _ hpairF (by simp)
      have hyA : y ∈ A := hFA _ hpairF (by simp)
      have hvP : v ∉ ({x, y} : Finset α) := hpair ▸ hvS
      have hdP : d ∉ ({x, y} : Finset α) := hpair ▸ hdS
      have hxv : x ≠ v := by
        intro h
        exact hvP (by simp [h])
      have hyv : y ≠ v := by
        intro h
        exact hvP (by simp [h])
      have hyd : y ≠ d := by
        intro h
        exact hdP (by simp [h])
      have hvx : v < x := lt_of_le_of_ne (hleast x hxA) (Ne.symm hxv)
      have hnew := hshift {x, y} hpairF v x hvA hvx (by simp) hvP
      refine ⟨y, hyA, hyv, hyd, ?_⟩
      simpa [hxy] using hnew
  obtain ⟨y, hyA, hyv, hyd, hpair⟩ := hstar
  have hay : a ≤ y := ha_lower y hyA hyv hyd
  by_cases hya : y = a
  · simpa only [hya, a] using hpair
  have hlt : a < y := lt_of_le_of_ne hay (Ne.symm hya)
  have hpair' : ({y, v} : Finset α) ∈ F := by
    simpa only [pair_comm] using hpair
  have hnew := hshift {y, v} hpair' a y haA hlt
    (by simp) (by simp [Ne.symm hya, hav])
  have hnew' : ({a, v} : Finset α) ∈ F := by
    simpa [hyv] using hnew
  simpa only [a, pair_comm] using hnew'

end Submissions.Erdos1020MatchingRankThreeBaselinePair.Main

namespace Submissions.Erdos1020MatchingRankThreeTenBaseline.Main

open Finset

/-- A present pair on eight vertices leaves at least ten missing triples on
its complement, when no three indexed members are pairwise disjoint. -/
theorem ten_le_missing_triples {α : Type*} [DecidableEq α]
    (A : Finset α) (hA : A.card = 8) (F : Finset (Finset α))
    (L : Finset α) (hLA : L ⊆ A) (hLc : L.card = 2) (hL : L ∈ F)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    10 ≤ ((A \ L).powersetCard 3 \ F).card := by
  classical
  let U := A \ L
  let P := U.powersetCard 3 ∩ F
  have hUc : U.card = 6 := by
    dsimp only [U]
    rw [card_sdiff_of_subset hLA, hA, hLc]
  have hPU : ∀ S ∈ P, S ⊆ U := fun S hS =>
    (mem_powersetCard.mp (mem_inter.mp hS).1).1
  have hPc : ∀ S ∈ P, S.card = 3 := fun S hS =>
    (mem_powersetCard.mp (mem_inter.mp hS).1).2
  have hmissing : ∀ S ∈ P, U \ S ∉ F := by
    intro S hS hC
    have hSF : S ∈ F := (mem_inter.mp hS).2
    have hLU : Disjoint L U := disjoint_sdiff
    have hLS : Disjoint L S := disjoint_of_subset_right (hPU S hS) hLU
    have hLC : Disjoint L (U \ S) := disjoint_of_subset_right sdiff_subset hLU
    have hSC : Disjoint S (U \ S) := disjoint_sdiff
    let f : Fin 3 → Finset α := fun i => if i = 0 then L else if i = 1 then S else U \ S
    apply hno f
    · intro i
      dsimp only [f]
      split_ifs
      · exact hL
      · exact hSF
      · exact hC
    · intro i j hij
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      · exact (hij rfl).elim
      · exact hLS
      · exact hLC
      · exact hLS.symm
      · exact (hij rfl).elim
      · exact hSC
      · exact hLC.symm
      · exact hSC.symm
      · exact (hij rfl).elim
  have hbound := Submissions.Erdos1020MatchingRankThreeNarrow.Main.card_le_missing_complements
    U 3 P F hPU hPc hmissing
  have hhalf : P.card ≤ (U.powersetCard 3 \ F).card := by
    simpa only [hUc] using hbound
  have hchoose : Nat.choose 6 3 = 20 := by decide
  have hsum : P.card + (U.powersetCard 3 \ F).card = 20 := by
    have h := card_inter_add_card_sdiff (U.powersetCard 3) F
    simpa only [card_powersetCard, hUc, hchoose] using h
  change 10 ≤ (U.powersetCard 3 \ F).card
  omega

/-- If all members lie in the eight-vertex head, the ten missing triples
give an upper bound of forty-six present triples, regardless of other ranks. -/
theorem triples_card_le_forty_six {α : Type*} [DecidableEq α]
    (A : Finset α) (hA : A.card = 8) (F : Finset (Finset α))
    (hFA : ∀ S ∈ F, S ⊆ A)
    (L : Finset α) (hLA : L ⊆ A) (hLc : L.card = 2) (hL : L ∈ F)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    (F.filter (fun S => S.card = 3)).card ≤ 46 := by
  classical
  have hten := ten_le_missing_triples A hA F L hLA hLc hL hno
  have hsub : (A \ L).powersetCard 3 \ F ⊆ A.powersetCard 3 \ F := by
    intro S hS
    obtain ⟨hSU, hSF⟩ := mem_sdiff.mp hS
    exact mem_sdiff.mpr ⟨powersetCard_mono sdiff_subset hSU, hSF⟩
  have hmissing : 10 ≤ (A.powersetCard 3 \ F).card := hten.trans (card_le_card hsub)
  have htriple : F.filter (fun S => S.card = 3) = A.powersetCard 3 ∩ F := by
    ext S
    simp only [mem_filter, mem_inter, mem_powersetCard]
    constructor
    · rintro ⟨hSF, hSc⟩
      exact ⟨⟨hFA S hSF, hSc⟩, hSF⟩
    · rintro ⟨⟨_, hSc⟩, hSF⟩
      exact ⟨hSF, hSc⟩
  have hchoose : Nat.choose 8 3 = 56 := by decide
  have hsum : (F.filter (fun S => S.card = 3)).card + (A.powersetCard 3 \ F).card = 56 := by
    rw [htriple]
    have h := card_inter_add_card_sdiff (A.powersetCard 3) F
    simpa only [card_powersetCard, hA, hchoose] using h
  omega

end Submissions.Erdos1020MatchingRankThreeTenBaseline.Main

namespace Submissions.Erdos1020MatchingRankThreeExtraMissing.Main

open Finset

/-- Two present pairs in a five-vertex region give a missing complementary
triple outside the complement of any fixed pair in that region, provided a
present set is disjoint from the region and indexed three-matchings are absent.
The fixed pair need not itself belong to the family. -/
theorem exists_missing_triple_outside {α : Type*} [DecidableEq α]
    (A U L : Finset α) (hUA : U ⊆ A) (hUc : U.card = 5)
    (hLU : L ⊆ U) (hLc : L.card = 2)
    (F N : Finset (Finset α)) (hNF : N ⊆ F)
    (hNP : N ⊆ U.powersetCard 2) (hN : 2 ≤ N.card)
    (B : Finset α) (hB : B ∈ F) (hUB : Disjoint U B)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    ∃ T, T ∈ A.powersetCard 3 ∧ T ∉ F ∧ ¬ T ⊆ A \ L := by
  classical
  have hex : ∃ R ∈ N, R ≠ L := by
    by_contra hnone
    have hsub : N ⊆ {L} := by
      intro R hR
      apply mem_singleton.mpr
      by_contra hne
      exact hnone ⟨R, hR, hne⟩
    have hcard : N.card ≤ 1 := by
      simpa only [card_singleton] using card_le_card hsub
    omega
  obtain ⟨R, hRN, hRL⟩ := hex
  obtain ⟨hRU, hRc⟩ := mem_powersetCard.mp (hNP hRN)
  let T := U \ R
  have hTc : T.card = 3 := by
    dsimp only [T]
    rw [card_sdiff_of_subset hRU, hUc, hRc]
  have hTU : T ⊆ U := sdiff_subset
  have hTF : T ∉ F := by
    intro hT
    have hRT : Disjoint R T := disjoint_sdiff
    have hRB : Disjoint R B := disjoint_of_subset_left hRU hUB
    have hTB : Disjoint T B := disjoint_of_subset_left hTU hUB
    let f : Fin 3 → Finset α :=
      fun i => if i = 0 then R else if i = 1 then T else B
    apply hno f
    · intro i
      dsimp only [f]
      split_ifs
      · exact hNF hRN
      · exact hT
      · exact hB
    · intro i j hij
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      · exact (hij rfl).elim
      · exact hRT
      · exact hRB
      · exact hRT.symm
      · exact (hij rfl).elim
      · exact hTB
      · exact hRB.symm
      · exact hTB.symm
      · exact (hij rfl).elim
  refine ⟨T, mem_powersetCard.mpr ⟨hTU.trans hUA, hTc⟩, hTF, ?_⟩
  intro hbase
  have hLR : L ⊆ R := by
    intro x hx
    by_contra hxR
    have hxT : x ∈ T := mem_sdiff.mpr ⟨hLU hx, hxR⟩
    exact (mem_sdiff.mp (hbase hxT)).2 hx
  have heq : L = R := eq_of_subset_of_card_le hLR (by omega)
  exact hRL heq.symm

end Submissions.Erdos1020MatchingRankThreeExtraMissing.Main

namespace Submissions.Erdos1020MatchingRankThreeElevenMissing.Main

open Finset

/-- Ten missing triples in a baseline complement and one missing triple
outside it leave at most forty-five present triples on eight vertices. -/
theorem triples_card_le_forty_five_of_extra {α : Type*} [DecidableEq α]
    (A : Finset α) (hA : A.card = 8) (F : Finset (Finset α))
    (hFA : ∀ S ∈ F, S ⊆ A) (L : Finset α)
    (hten : 10 ≤ ((A \ L).powersetCard 3 \ F).card)
    (T : Finset α) (hTA : T ∈ A.powersetCard 3) (hTF : T ∉ F)
    (hout : ¬ T ⊆ A \ L) :
    (F.filter (fun S => S.card = 3)).card ≤ 45 := by
  classical
  let D := (A \ L).powersetCard 3 \ F
  have hnot : T ∉ D := by
    intro hT
    exact hout (mem_powersetCard.mp (mem_sdiff.mp hT).1).1
  have hsub : insert T D ⊆ A.powersetCard 3 \ F := by
    apply insert_subset (mem_sdiff.mpr ⟨hTA, hTF⟩)
    intro S hS
    obtain ⟨hSU, hSF⟩ := mem_sdiff.mp hS
    exact mem_sdiff.mpr ⟨powersetCard_mono sdiff_subset hSU, hSF⟩
  have hmissing : 11 ≤ (A.powersetCard 3 \ F).card := by
    have hc := card_le_card hsub
    rw [card_insert_of_notMem hnot] at hc
    change 10 ≤ D.card at hten
    omega
  have htriple : F.filter (fun S => S.card = 3) = A.powersetCard 3 ∩ F := by
    ext S
    simp only [mem_filter, mem_inter, mem_powersetCard]
    constructor
    · rintro ⟨hSF, hSc⟩
      exact ⟨⟨hFA S hSF, hSc⟩, hSF⟩
    · rintro ⟨⟨_, hSc⟩, hSF⟩
      exact ⟨hSF, hSc⟩
  have hchoose : Nat.choose 8 3 = 56 := by decide
  have hsum : (F.filter (fun S => S.card = 3)).card +
      (A.powersetCard 3 \ F).card = 56 := by
    rw [htriple]
    have h := card_inter_add_card_sdiff (A.powersetCard 3) F
    simpa only [card_powersetCard, hA, hchoose] using h
  omega

/-- A present baseline pair and two present pairs in its five-vertex region
produce all eleven missing triples from explicit indexed no-three premises. -/
theorem triples_card_le_forty_five {α : Type*} [DecidableEq α]
    (A : Finset α) (hA : A.card = 8) (F : Finset (Finset α))
    (hFA : ∀ S ∈ F, S ⊆ A)
    (U L : Finset α) (hUA : U ⊆ A) (hUc : U.card = 5)
    (hLU : L ⊆ U) (hLc : L.card = 2) (hL : L ∈ F)
    (N : Finset (Finset α)) (hNF : N ⊆ F)
    (hNP : N ⊆ U.powersetCard 2) (hN : 2 ≤ N.card)
    (B : Finset α) (hB : B ∈ F) (hUB : Disjoint U B)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) :
    (F.filter (fun S => S.card = 3)).card ≤ 45 := by
  have hten := Submissions.Erdos1020MatchingRankThreeTenBaseline.Main.ten_le_missing_triples
    A hA F L (hLU.trans hUA) hLc hL hno
  obtain ⟨T, hTA, hTF, hout⟩ :=
    Submissions.Erdos1020MatchingRankThreeExtraMissing.Main.exists_missing_triple_outside
      A U L hUA hUc hLU hLc F N hNF hNP hN B hB hUB hno
  exact triples_card_le_forty_five_of_extra A hA F hFA L hten T hTA hTF hout

end Submissions.Erdos1020MatchingRankThreeElevenMissing.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoOfFive.Main

open Finset

/-- Two disjoint present sets avoiding the least head vertex force every
present set to meet their union together with that vertex at least twice.
No set-size hypotheses are needed here. When the two sets are pairs, the
distinguished union has five elements. -/
theorem two_le_inter_insert_union {α : Type*} [LinearOrder α]
    (F : Finset (Finset α)) (A : Finset α)
    (hdown : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (hno : ∀ f : Fin 3 → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (v : α) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (R₀ R₁ : Finset α) (hR₀ : R₀ ∈ F) (hR₁ : R₁ ∈ F)
    (hR₀A : R₀ ⊆ A) (hR₁A : R₁ ⊆ A) (hdis : Disjoint R₀ R₁)
    (hvR₀ : v ∉ R₀) (hvR₁ : v ∉ R₁)
    (S : Finset α) (hS : S ∈ F) :
    2 ≤ (S ∩ insert v (R₀ ∪ R₁)).card := by
  classical
  let U := R₀ ∪ R₁
  have hUA : U ⊆ A := union_subset hR₀A hR₁A
  have hvU : v ∉ U := notMem_union.mpr ⟨hvR₀, hvR₁⟩
  have hhit (T : Finset α) (hT : T ∈ F) : ¬ Disjoint T U := by
    intro hd
    have hR₀T : Disjoint R₀ T :=
      (disjoint_of_subset_right (show R₀ ⊆ U from subset_union_left) hd).symm
    have hR₁T : Disjoint R₁ T :=
      (disjoint_of_subset_right (show R₁ ⊆ U from subset_union_right) hd).symm
    let f : Fin 3 → Finset α :=
      fun i => if i = 0 then R₀ else if i = 1 then R₁ else T
    apply hno f
    · intro i
      dsimp only [f]
      split_ifs
      · exact hR₀
      · exact hR₁
      · exact hT
    · intro i j hij
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      · exact (hij rfl).elim
      · exact hdis
      · exact hR₀T
      · exact hdis.symm
      · exact (hij rfl).elim
      · exact hR₁T
      · exact hR₀T.symm
      · exact hR₁T.symm
      · exact (hij rfl).elim
  change 2 ≤ (S ∩ insert v U).card
  by_contra hbad
  have hc : (S ∩ insert v U).card ≤ 1 := by omega
  obtain ⟨x, hxS, hxU⟩ := not_disjoint_iff.mp (hhit S hS)
  have hxI : x ∈ S ∩ insert v U :=
    mem_inter.mpr ⟨hxS, mem_insert_of_mem hxU⟩
  have hvx : v ≠ x := by
    intro h
    subst x
    exact hvU hxU
  have hvlt : v < x := lt_of_le_of_ne (hleast x (hUA hxU)) hvx
  have hvS : v ∉ S := by
    intro hvS
    have hvI : v ∈ S ∩ insert v U :=
      mem_inter.mpr ⟨hvS, mem_insert_self _ _⟩
    exact hvx ((card_le_one_iff.mp hc) hvI hxI)
  have hnew : insert v (S.erase x) ∈ F := hdown S hS v x hvA hvlt hxS hvS
  apply hhit _ hnew
  apply disjoint_left.mpr
  intro y hy hyU
  rcases mem_insert.mp hy with hyv | hy
  · subst y
    exact hvU hyU
  · have hyI : y ∈ S ∩ insert v U :=
      mem_inter.mpr ⟨mem_of_mem_erase hy, mem_insert_of_mem hyU⟩
    exact (mem_erase.mp hy).1 ((card_le_one_iff.mp hc) hyI hxI)

end Submissions.Erdos1020MatchingRankThreeTwoOfFive.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoRowClassifier.Main

open Finset

/-- A downward family of grid positions with the last first-coordinate fiber
absent and the indicated incompatible corner positions has only two relevant
possibilities once it has at least three entries. This is a pure finite
classifier; no actual trace-family premise is discharged here. -/
theorem classify (P : Finset (Fin 3 × Fin 3))
    (hdown : ∀ i j, (i, j) ∈ P → ∀ i' j',
      i' ≤ i → j' ≤ j → (i', j') ∈ P)
    (htop : ∀ j, (2, j) ∉ P)
    (hincompatible : (0, 2) ∈ P → (1, 0) ∉ P)
    (hcard : 3 ≤ P.card) :
    ((0, 1) ∈ P ∧ (1, 0) ∈ P) ∨
      P = {(0, 0), (0, 1), (0, 2)} := by
  classical
  by_cases h02 : (0, 2) ∈ P
  · right
    apply Finset.Subset.antisymm
    · rintro ⟨i, j⟩ hij
      have hi2 : i ≠ 2 := by
        intro hi
        subst i
        exact htop j hij
      have hi0 : i = 0 := by
        by_contra hi
        have hi1 : i = 1 := by omega
        exact hincompatible h02 (hdown i j hij 1 0 (by omega) (by omega))
      subst i
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl | rfl <;> simp
    · intro q hq
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hdown 0 2 h02 0 0 (by decide) (by decide)
      · exact hdown 0 2 h02 0 1 (by decide) (by decide)
      · exact h02
  · have hcoords (i j : Fin 3) (hij : (i, j) ∈ P) :
        (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) := by
      have hi2 : i ≠ 2 := by
        intro hi
        subst i
        exact htop j hij
      have hj2 : j ≠ 2 := by
        intro hj
        exact h02 (hdown i j hij 0 2 (by omega) (by omega))
      constructor <;> omega
    have h01 : (0, 1) ∈ P := by
      by_contra hnot
      have hsub : P ⊆ ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin 3)) := by
        rintro ⟨i, j⟩ hij
        obtain ⟨hi, hj⟩ := hcoords i j hij
        have hj0 : j = 0 := by
          rcases hj with hj | hj
          · exact hj
          · exact (hnot (hdown i j hij 0 1 (by omega) (by omega))).elim
        rcases hi with rfl | rfl <;> subst j <;> simp
      have hle : P.card ≤ 2 := (card_le_card hsub).trans card_le_two
      omega
    have h10 : (1, 0) ∈ P := by
      by_contra hnot
      have hsub : P ⊆ ({(0, 0), (0, 1)} : Finset (Fin 3 × Fin 3)) := by
        rintro ⟨i, j⟩ hij
        obtain ⟨hi, hj⟩ := hcoords i j hij
        have hi0 : i = 0 := by
          rcases hi with hi | hi
          · exact hi
          · exact (hnot (hdown i j hij 1 0 (by omega) (by omega))).elim
        rcases hj with rfl | rfl <;> subst i <;> simp
      have hle : P.card ≤ 2 := (card_le_card hsub).trans card_le_two
      omega
    exact Or.inl ⟨h01, h10⟩

end Submissions.Erdos1020MatchingRankThreeTwoRowClassifier.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoTailCount.Main

open Finset

/-- With two tail vertices and traces of size two or three, the completion
upper count is one per head triple plus two per trace pair. -/
theorem card_le_triples_add_twice_pairs {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ E ∈ H, E.card = 3) (htail : n - A.card = 2)
    (htrace : ∀ S ∈ H.image (fun E => E ∩ A), 2 ≤ S.card ∧ S.card ≤ 3) :
    H.card ≤ ((H.image (fun E => E ∩ A)).filter (fun S => S.card = 3)).card +
      2 * ((H.image (fun E => E ∩ A)).filter (fun S => S.card = 2)).card := by
  classical
  let T := H.image (fun E => E ∩ A)
  have hnotthree : T.filter (fun S => ¬ S.card = 3) =
      T.filter (fun S => S.card = 2) := by
    ext S
    simp only [mem_filter]
    constructor
    · rintro ⟨hST, hS⟩
      have hc := htrace S hST
      exact ⟨hST, by omega⟩
    · rintro ⟨hST, hS⟩
      exact ⟨hST, by omega⟩
  have hthree : (∑ S ∈ T.filter (fun S => S.card = 3),
      (n - A.card).choose (3 - S.card)) = (T.filter (fun S => S.card = 3)).card := by
    have h := sum_const_nat (s := T.filter (fun S => S.card = 3)) (m := 1)
      (f := fun S => (n - A.card).choose (3 - S.card)) (by
        intro S hS
        rw [htail, (mem_filter.mp hS).2]
        decide)
    simpa only [Nat.mul_one] using h
  have htwo : (∑ S ∈ T.filter (fun S => S.card = 2),
      (n - A.card).choose (3 - S.card)) =
      2 * (T.filter (fun S => S.card = 2)).card := by
    have h := sum_const_nat (s := T.filter (fun S => S.card = 2)) (m := 2)
      (f := fun S => (n - A.card).choose (3 - S.card)) (by
        intro S hS
        rw [htail, (mem_filter.mp hS).2]
        decide)
    exact h.trans (Nat.mul_comm _ _)
  have hsum := sum_filter_add_sum_filter_not T (fun S => S.card = 3)
    (fun S => (n - A.card).choose (3 - S.card))
  rw [hnotthree, hthree, htwo] at hsum
  exact (Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main.card_le_trace_sum
    H A hH).trans_eq hsum.symm

end Submissions.Erdos1020MatchingRankThreeTwoTailCount.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoOfFiveCount.Main

open Finset

/-- A rank-three family on ten vertices has at most sixty members if every
member meets one fixed five-element set in at least two vertices. -/
theorem card_le_sixty
    (H : Finset (Finset (Fin 10))) (hH : ∀ E ∈ H, E.card = 3)
    (Y : Finset (Fin 10)) (hY : Y.card = 5)
    (hmeet : ∀ E ∈ H, 2 ≤ (E ∩ Y).card) : H.card ≤ 60 := by
  classical
  let T := H.image (fun E => E ∩ Y)
  have htrace : ∀ S ∈ T, 2 ≤ S.card ∧ S.card ≤ 3 := by
    intro S hS
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hS
    exact ⟨hmeet E hE, (card_le_card inter_subset_left).trans_eq (hH E hE)⟩
  have hTY : ∀ S ∈ T, S ⊆ Y := by
    intro S hS
    obtain ⟨E, _, rfl⟩ := mem_image.mp hS
    exact inter_subset_right
  have hlevel (d : ℕ) : (T.filter (fun S => S.card = d)).card ≤ Y.card.choose d := by
    have hsub : T.filter (fun S => S.card = d) ⊆ Y.powersetCard d := by
      intro S hS
      exact mem_powersetCard.mpr ⟨hTY S (mem_filter.mp hS).1, (mem_filter.mp hS).2⟩
    simpa only [card_powersetCard] using card_le_card hsub
  have hc3 : Nat.choose 5 3 = 10 := by decide
  have hc2 : Nat.choose 5 2 = 10 := by decide
  have hthree_le : (T.filter (fun S => S.card = 3)).card ≤ 10 := by
    simpa only [hY, hc3] using hlevel 3
  have htwo_le : (T.filter (fun S => S.card = 2)).card ≤ 10 := by
    simpa only [hY, hc2] using hlevel 2
  have htail : 10 - Y.card = 5 := by rw [hY]
  have hnotthree : T.filter (fun S => ¬ S.card = 3) =
      T.filter (fun S => S.card = 2) := by
    ext S
    simp only [mem_filter]
    constructor
    · rintro ⟨hST, hS⟩
      have hc := htrace S hST
      exact ⟨hST, by omega⟩
    · rintro ⟨hST, hS⟩
      exact ⟨hST, by omega⟩
  have hthree : (∑ S ∈ T.filter (fun S => S.card = 3),
      (10 - Y.card).choose (3 - S.card)) = (T.filter (fun S => S.card = 3)).card := by
    have h := sum_const_nat (s := T.filter (fun S => S.card = 3)) (m := 1)
      (f := fun S => (10 - Y.card).choose (3 - S.card)) (by
        intro S hS
        rw [htail, (mem_filter.mp hS).2]
        decide)
    simpa only [Nat.mul_one] using h
  have htwo : (∑ S ∈ T.filter (fun S => S.card = 2),
      (10 - Y.card).choose (3 - S.card)) =
      5 * (T.filter (fun S => S.card = 2)).card := by
    have h := sum_const_nat (s := T.filter (fun S => S.card = 2)) (m := 5)
      (f := fun S => (10 - Y.card).choose (3 - S.card)) (by
        intro S hS
        rw [htail, (mem_filter.mp hS).2]
        decide)
    exact h.trans (Nat.mul_comm _ _)
  have hsum := sum_filter_add_sum_filter_not T (fun S => S.card = 3)
    (fun S => (10 - Y.card).choose (3 - S.card))
  rw [hnotthree, hthree, htwo] at hsum
  have hupper : H.card ≤ (T.filter (fun S => S.card = 3)).card +
      5 * (T.filter (fun S => S.card = 2)).card :=
    (Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main.card_le_trace_sum
      H Y hH).trans_eq hsum.symm
  omega

end Submissions.Erdos1020MatchingRankThreeTwoOfFiveCount.Main

namespace Submissions.Erdos1020MatchingRankThreeTenOneCount.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeTwoRowCounts.Main (row narrowPairs)
open Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main (crossPairs mem_crossPairs)

/-- The actual ten-vertex family has at most sixty-three edges once its
eight-vertex trace has the explicit two-row packet. All counting and
classifier premises are derived; no desired cardinal bound is assumed. -/
theorem card_le_sixty_three
    (H : Finset (Finset (Fin 10))) (A : Finset (Fin 10))
    (hH : ∀ E ∈ H, E.card = 3) (hA : A.card = 8)
    (F : Finset (Finset (Fin 10))) (hF : F = H.image (fun E => E ∩ A))
    (htrace : ∀ S ∈ F, 2 ≤ S.card ∧ S.card ≤ 3)
    (hshift : ∀ S ∈ F, ∀ x y, x ∈ A → x < y → y ∈ S → x ∉ S →
      insert x (S.erase y) ∈ F)
    (hno : ∀ f : Fin 3 → Finset (Fin 10), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (v d : Fin 10) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (e : Fin 2 × Fin 3 ↪ Fin 10)
    (hvd : v < d) (hhead : A = ({v, d} ∪ row e 0) ∪ row e 1)
    (hgap : ({v, d} : Finset (Fin 10)) ∉ F)
    (hGB : ∀ i : Fin 2, Disjoint ({v, d} : Finset (Fin 10)) (row e i))
    (hB : ∀ i : Fin 2, row e i ∈ F)
    (hrow : ∀ i : Fin 2, StrictMono (fun j : Fin 3 => e (i, j)))
    (hmin : e (0, 0) < e (1, 0)) : H.card ≤ 63 := by
  classical
  let t := (F.filter (fun S => S.card = 3)).card
  let p := (F.filter (fun S => S.card = 2)).card
  let N := fun i : Fin 2 => narrowPairs F v d e i
  let P := crossPairs F e
  have hFA : ∀ S ∈ F, S ⊆ A := by
    intro S hS
    rw [hF] at hS
    obtain ⟨E, _, rfl⟩ := mem_image.mp hS
    exact inter_subset_right
  have hupper : H.card ≤ t + 2 * p := by
    have ht : ∀ S ∈ H.image (fun E => E ∩ A), 2 ≤ S.card ∧ S.card ≤ 3 := by
      simpa only [← hF] using htrace
    have h := Submissions.Erdos1020MatchingRankThreeTwoTailCount.Main.card_le_triples_add_twice_pairs
      H A hH (by omega) ht
    rw [← hF] at h
    exact h
  have ht56 : t ≤ 56 := by
    have hsub : F.filter (fun S => S.card = 3) ⊆ A.powersetCard 3 := by
      intro S hS
      obtain ⟨hSF, hSc⟩ := mem_filter.mp hS
      exact mem_powersetCard.mpr ⟨hFA S hSF, hSc⟩
    have hc : Nat.choose 8 3 = 56 := by decide
    simpa only [t, card_powersetCard, hA, hc] using card_le_card hsub
  by_contra hbad
  have h64 : 64 ≤ H.card := by omega
  have hp4 : 4 ≤ p := by omega
  have hpoint (i : Fin 2) (j : Fin 3) : e (i, j) ∈ row e i :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have heA (q : Fin 2 × Fin 3) : e q ∈ A :=
    hFA (row e q.1) (hB q.1) (hpoint q.1 q.2)
  have hvne (q : Fin 2 × Fin 3) : v ≠ e q := by
    intro h
    have hvrow : v ∈ row e q.1 := h.symm ▸ hpoint q.1 q.2
    exact disjoint_left.mp (hGB q.1) (by simp) hvrow
  have hv (q : Fin 2 × Fin 3) : v < e q :=
    lt_of_le_of_ne (hleast _ (heA q)) (hvne q)
  have heq (q q' : Fin 2 × Fin 3) : e q = e q' ↔ q = q' :=
    ⟨fun h => e.injective h, fun h => congrArg e h⟩
  have hrowcard (i : Fin 2) : (row e i).card = 3 := by
    have hinj : Function.Injective (fun j : Fin 3 => e (i, j)) := by
      intro j k h
      exact congrArg Prod.snd (e.injective h)
    simpa only [row, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hrows : Disjoint (row e 0) (row e 1) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, hi⟩ := mem_image.mp hx
    obtain ⟨j, _, hj⟩ := mem_image.mp hy
    have hp := e.injective (hi.trans hj.symm)
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst hp)
  let L : Finset (Fin 10) := {v, e (0, 0)}
  have hL : L ∈ F :=
    Submissions.Erdos1020MatchingRankThreeBaselinePair.Main.baseline_pair_mem
      F A hFA hshift e v d hhead hvd hleast hgap hGB hrow hmin (by omega)
  have hLc : L.card = 2 := card_pair (hvne (0, 0))
  have hLA : L ⊆ A := insert_subset hvA (singleton_subset_iff.mpr (heA (0, 0)))
  have ht46 : t ≤ 46 :=
    Submissions.Erdos1020MatchingRankThreeTenBaseline.Main.triples_card_le_forty_six
      A hA F hFA L hLA hLc hL hno
  have hp9 : 9 ≤ p := by omega
  obtain ⟨hpartition, hNb⟩ :=
    Submissions.Erdos1020MatchingRankThreeTwoRowCounts.Main.pair_counts
      F A hFA hshift e v d hhead hvd hleast hgap hGB hB hno
  change p = (N 0).card + (N 1).card + P.card at hpartition
  have hN0 : (N 0).card ≤ 3 := hNb 0
  have hN1 : (N 1).card ≤ 3 := hNb 1
  have hP3 : 3 ≤ P.card := by omega
  have hBexplicit : ∀ i : Fin 2,
      ({e (i, 0), e (i, 1), e (i, 2)} : Finset (Fin 10)) ∈ F := by
    intro i
    have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    simpa only [row, hu, image_insert, image_singleton] using hB i
  obtain ⟨hdown, htop, hinc⟩ :=
    Submissions.Erdos1020MatchingRankThreeTwoRowActual.Main.classifier_premises
      F A hshift e heA hrow hmin v hvA hv hBexplicit hno
  rcases Submissions.Erdos1020MatchingRankThreeTwoRowClassifier.Main.classify
    P hdown htop hinc hP3 with hcorner | hstar
  · let R0 : Finset (Fin 10) := {e (0, 0), e (1, 1)}
    let R1 : Finset (Fin 10) := {e (0, 1), e (1, 0)}
    have hR0 : R0 ∈ F := (mem_crossPairs F e 0 1).mp hcorner.1
    have hR1 : R1 ∈ F := (mem_crossPairs F e 1 0).mp hcorner.2
    have hdis : Disjoint R0 R1 := by simp [R0, R1, heq]
    have hvR0 : v ∉ R0 := by simp [R0, hvne]
    have hvR1 : v ∉ R1 := by simp [R1, hvne]
    have hR0c : R0.card = 2 := by simp [R0, heq]
    have hR1c : R1.card = 2 := by simp [R1, heq]
    let Y := insert v (R0 ∪ R1)
    have hYc : Y.card = 5 := by
      rw [card_insert_of_notMem (notMem_union.mpr ⟨hvR0, hvR1⟩),
        card_union_of_disjoint hdis, hR0c, hR1c]
    have hYA : Y ⊆ A := insert_subset hvA (union_subset (hFA R0 hR0) (hFA R1 hR1))
    have hmeet : ∀ E ∈ H, 2 ≤ (E ∩ Y).card := by
      intro E hE
      have hEA : E ∩ A ∈ F := by
        rw [hF]
        exact mem_image.mpr ⟨E, hE, rfl⟩
      have h := Submissions.Erdos1020MatchingRankThreeTwoOfFive.Main.two_le_inter_insert_union
        F A hshift hno v hvA hleast R0 R1 hR0 hR1 (hFA R0 hR0) (hFA R1 hR1)
          hdis hvR0 hvR1 (E ∩ A) hEA
      change 2 ≤ ((E ∩ A) ∩ Y).card at h
      simpa only [inter_assoc, inter_eq_right.mpr hYA] using h
    have hc := Submissions.Erdos1020MatchingRankThreeTwoOfFiveCount.Main.card_le_sixty
      H hH Y hYc hmeet
    omega
  · have hPc : P.card = 3 := by rw [hstar]; decide
    have hp : p = 9 := by omega
    have hN0c : (N 0).card = 3 := by omega
    let U : Finset (Fin 10) := {v, d} ∪ row e 0
    have hUA : U ⊆ A := by
      rw [hhead]
      exact subset_union_left
    have hUc : U.card = 5 := by
      rw [card_union_of_disjoint (hGB 0), card_pair hvd.ne, hrowcard]
    have hLU : L ⊆ U := by
      apply insert_subset
      · exact mem_union_left _ (by simp)
      · exact singleton_subset_iff.mpr (mem_union_right _ (hpoint 0 0))
    have hNF : N 0 ⊆ F := filter_subset _ _
    have hNP : N 0 ⊆ U.powersetCard 2 := by
      intro S hS
      obtain ⟨_, hSU, hSc⟩ := mem_filter.mp hS
      exact mem_powersetCard.mpr ⟨hSU, hSc⟩
    have hUB : Disjoint U (row e 1) := disjoint_union_left.mpr ⟨hGB 1, hrows⟩
    have ht45 : t ≤ 45 :=
      Submissions.Erdos1020MatchingRankThreeElevenMissing.Main.triples_card_le_forty_five
        A hA F hFA U L hUA hUc hLU hLc hL (N 0) hNF hNP (by omega)
          (row e 1) (hB 1) hUB hno
    omega

end Submissions.Erdos1020MatchingRankThreeTenOneCount.Main

namespace Submissions.Erdos1020MatchingRankThreeTwoHead.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main (Uniform MatchingFree)
open Submissions.Erdos1020MatchingRankThreeTwoRowCounts.Main (row)

/-- Saturation and an actual two-matching avoiding the least vertex give
the ordered two-row head used in the small matching case. -/
theorem exists_ordered_head {n : ℕ} (hn : 9 ≤ n)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H 3)
    (hsat : ∀ E : Finset (Fin n), E.card = 3 → E ∉ H →
      ¬ MatchingFree (insert E H) 3)
    (hA : A.card = 8)
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = 2)
    (hMd : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hMv : ∀ E ∈ M, v ∉ E) :
    ∃ (d : Fin n) (e : Fin 2 × Fin 3 ↪ Fin n),
      v < d ∧ A = ({v, d} ∪ row e 0) ∪ row e 1 ∧
      ({v, d} : Finset (Fin n)) ∉ H.image (fun E => E ∩ A) ∧
      (∀ i : Fin 2, Disjoint ({v, d} : Finset (Fin n)) (row e i)) ∧
      (∀ i : Fin 2, row e i ∈ H.image (fun E => E ∩ A)) ∧
      (∀ i : Fin 2, StrictMono (fun j : Fin 3 => e (i, j))) ∧
      e (0, 0) < e (1, 0) := by
  classical
  obtain ⟨d, _, hvd, hgap, _, B, hBH, hBd, hGB, hBA, hpart, _⟩ :=
    Submissions.Erdos1020MatchingRankThreeSaturated.Main.exists_minimum_pair_partition
      (s := 2) hn H A hH hfree hsat (by omega) hcut hstable
      v hvA hleast M hMH hMc hMd hMv
  obtain ⟨J, e, _, hrow, heB, hmin⟩ :=
    Submissions.Erdos1020MatchingRankThreeTwoRows.Main.exists_rows
      B hBd (fun i => hH _ (hBH i))
  have heq (i : Fin 2) : row e i = B (J i) := heB i
  have hcover : univ.biUnion B = row e 0 ∪ row e 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
      obtain ⟨j, rfl⟩ := J.surjective i
      have hj : j = 0 ∨ j = 1 := by omega
      rcases hj with rfl | rfl
      · exact mem_union_left _ ((heq 0).symm ▸ hxi)
      · exact mem_union_right _ ((heq 1).symm ▸ hxi)
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact mem_biUnion.mpr ⟨J 0, mem_univ _, heq 0 ▸ hx⟩
      · exact mem_biUnion.mpr ⟨J 1, mem_univ _, heq 1 ▸ hx⟩
  refine ⟨d, e, hvd, ?_, hgap, ?_, ?_, hrow, hmin⟩
  · rw [hcover, ← union_assoc] at hpart
    exact hpart.symm
  · intro i
    rw [heq]
    exact hGB (J i)
  · intro i
    apply mem_image.mpr
    refine ⟨B (J i), hBH (J i), ?_⟩
    rw [inter_eq_left.mpr (hBA (J i)), heq]

/-- The actual head traces satisfy containment, singleton downward closure,
the indexed three-matching prohibition, and ranks two or three. -/
theorem trace_premises {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H 3) (hA : A.card = 8)
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = 2)
    (hMd : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hMv : ∀ E ∈ M, v ∉ E) :
    (∀ S ∈ H.image (fun E => E ∩ A), S ⊆ A) ∧
    (∀ S ∈ H.image (fun E => E ∩ A), ∀ x y, x ∈ A → x < y →
      y ∈ S → x ∉ S → insert x (S.erase y) ∈ H.image (fun E => E ∩ A)) ∧
    (∀ f : Fin 3 → Finset (Fin n),
      (∀ i, f i ∈ H.image (fun E => E ∩ A)) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) ∧
    (∀ S ∈ H.image (fun E => E ∩ A), 2 ≤ S.card ∧ S.card ≤ 3) := by
  classical
  have hA' : A.card + 1 = 3 * (2 + 1) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨E, _, rfl⟩ := mem_image.mp hS
    exact inter_subset_right
  · intro S hS x y hx hxy hy hn
    exact Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable S hS x y hx hxy hy hn
  · intro f hf
    have hw : ∀ i, ∃ E, E ∈ H ∧ E ∩ A = f i := fun i => mem_image.mp (hf i)
    choose g hg hgf using hw
    intro hd
    apply Submissions.Erdos1020MatchingTrace.Main.no_indexed_trace_matching
      (by decide) H A hH (by simp) hA' hcut hstable hfree g hg
    intro i j hij
    rw [hgf i, hgf j]
    exact hd hij
  · have hmin :=
      Submissions.Erdos1020MatchingRankThreeOne.Main.trace_card_two_le_of_avoiding_matching
        (s := 2) (by decide) H A hH hA' hcut hstable hfree
        v hvA hleast M hMH hMc hMd hMv
    intro S hS
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hS
    exact ⟨hmin E hE, (card_le_card inter_subset_left).trans_eq (hH E hE)⟩

end Submissions.Erdos1020MatchingRankThreeTwoHead.Main

namespace Submissions.Erdos1020MatchingRankThreeTenOne.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main (Uniform MatchingFree)

/-- The actual saturated ten-vertex ONE case, with no trace count premise. -/
theorem saturated_bound
    (H : Finset (Finset (Fin 10))) (A : Finset (Fin 10))
    (hH : Uniform H 3) (hfree : MatchingFree H 3)
    (hsat : ∀ E : Finset (Fin 10), E.card = 3 → E ∉ H →
      ¬ MatchingFree (insert E H) 3)
    (hA : A.card = 8)
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin 10, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin 10) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin 10))) (hMH : M ⊆ H) (hMc : M.card = 2)
    (hMd : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hMv : ∀ E ∈ M, v ∉ E) : H.card ≤ 63 := by
  obtain ⟨d, e, hvd, hhead, hgap, hGB, hB, hrow, hmin⟩ :=
    Submissions.Erdos1020MatchingRankThreeTwoHead.Main.exists_ordered_head
      (by decide) H A hH hfree hsat hA hcut hstable v hvA hleast M hMH hMc hMd hMv
  obtain ⟨_, hshift, hno, htrace⟩ :=
    Submissions.Erdos1020MatchingRankThreeTwoHead.Main.trace_premises
      H A hH hfree hA hcut hstable v hvA hleast M hMH hMc hMd hMv
  exact Submissions.Erdos1020MatchingRankThreeTenOneCount.Main.card_le_sixty_three
    H A hH hA (H.image (fun E => E ∩ A)) rfl htrace hshift hno
    v d hvA hleast e hvd hhead hgap hGB hB hrow hmin

/-- A containing saturated shifted extension preserves the actual avoiding
two-matching and transfers the ten-vertex ONE bound to the original family. -/
theorem bound
    (H : Finset (Finset (Fin 10))) (A : Finset (Fin 10))
    (hH : Uniform H 3) (hfree : MatchingFree H 3) (hA : A.card = 8)
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin 10, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin 10) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin 10))) (hMH : M ⊆ H) (hMc : M.card = 2)
    (hMd : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hMv : ∀ E ∈ M, v ∉ E) : H.card ≤ 63 := by
  obtain ⟨K, hHK, hK, hKm, hKs, hsat⟩ :=
    Submissions.Erdos1020MatchingRankThreeMaxExtension.Main.exists_saturated_shifted_extension
      (by decide) H hH hfree hstable
  exact (card_le_card hHK).trans
    (saturated_bound K A hK hKm hsat hA hcut hKs v hvA hleast
      M (hMH.trans hHK) hMc hMd hMv)

end Submissions.Erdos1020MatchingRankThreeTenOne.Main



namespace Submissions.Erdos1020RainbowShift.Main

variable {α ι : Type*} [DecidableEq α]

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

end Submissions.Erdos1020RainbowShift.Main

namespace Submissions.Erdos1020ShiftNormalize.Main

open Finset

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

end Submissions.Erdos1020MatchingRainbowAverage.Main

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

end Submissions.Erdos1020MatchingZeroHead.Main

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

namespace Submissions.Erdos1020MatchingDegree.Main

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

theorem card_containing_le {n r : ℕ} {H : Finset (Finset (Fin n))}
    (hH : Uniform H r) {s : Finset (Fin n)} (hsr : s.card ≤ r) :
    (H.filter (s ⊆ ·)).card ≤ (n - s.card).choose (r - s.card) := by
  classical
  have hsub : H.filter (s ⊆ ·) ⊆
      ((Finset.univ : Finset (Fin n)).powersetCard r).filter (s ⊆ ·) := by
    intro e he
    obtain ⟨heH, hse⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hH e heH⟩, hse⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_filter_powersetCard_subset s Finset.univ r
    (Finset.subset_univ s) hsr] at hcard
  simpa using hcard

end Submissions.Erdos1020MatchingDegree.Main

namespace Submissions.Erdos1020MatchingDeleteVertex.Main

/-- Relabel a family avoiding one vertex onto `Fin n`, preserving its edge count,
uniformity and the literal absence of a `k`-edge matching. -/
theorem reindex {n r k : ℕ} (H : Finset (Finset (Fin (n + 1))))
    (v : Fin (n + 1)) (hv : ∀ e ∈ H, v ∉ e)
    (hH : ∀ e ∈ H, e.card = r)
    (hf : ¬ ∃ M : Finset (Finset (Fin (n + 1))), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    ∃ H' : Finset (Finset (Fin n)), H'.card = H.card ∧
      (∀ e ∈ H', e.card = r) ∧
      ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H' ∧ M.card = k ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  let f := v.succAboveEmb
  let F := (Finset.mapEmbedding f).toEmbedding
  let H' := H.preimage F F.injective.injOn
  have hsurj : ∀ e ∈ H, ∃ e', F e' = e := by
    intro e he
    refine ⟨e.preimage f f.injective.injOn, ?_⟩
    change (e.preimage f f.injective.injOn).map f = e
    ext x
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_preimage.mp hy
    · intro hx
      have hxv : x ≠ v := fun h => hv e he (h ▸ hx)
      obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hxv
      exact Finset.mem_map.mpr ⟨y, Finset.mem_preimage.mpr (by change v.succAbove y ∈ e; rwa [hy]), hy⟩
  have hmap : H'.map F = H := by
    ext e
    constructor
    · rintro he
      obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
      exact Finset.mem_preimage.mp he'
    · intro he
      obtain ⟨e', he'⟩ := hsurj e he
      exact Finset.mem_map.mpr ⟨e', Finset.mem_preimage.mpr (he'.symm ▸ he), he'⟩
  refine ⟨H', ?_, ?_, ?_⟩
  · simpa using congrArg Finset.card hmap
  · intro e he
    simpa [F] using hH (F e) (Finset.mem_preimage.mp he)
  · rintro ⟨M, hMH, hMk, hMd⟩
    apply hf
    refine ⟨M.map F, ?_, by simpa using hMk, ?_⟩
    · rw [← hmap]
      exact Finset.map_subset_map.mpr hMH
    · intro e he g hg heg
      obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
      obtain ⟨g', hg', rfl⟩ := Finset.mem_map.mp hg
      exact (Finset.disjoint_map f).mpr
        (hMd e' he' g' hg' (fun h => heg (congrArg F h)))

end Submissions.Erdos1020MatchingDeleteVertex.Main

namespace Submissions.Erdos1020MatchingRankThreeRecurrence.Main

/-- A telescoping lower bound using the smallest adjacent binomial coefficient. -/
theorem choose_drop_lower {m r : ℕ} (hr : 0 < r) :
    ∀ a, a ≤ m →
      (m - a).choose r + a * (m - a).choose (r - 1) ≤ m.choose r := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    have hi := ih (by omega)
    have hp := Nat.choose_eq_choose_pred_add
      (n := m - a) (k := r) (by omega) hr
    have he : m - a - 1 = m - (a + 1) := by omega
    rw [he] at hp
    have hm := Nat.choose_le_choose (r - 1)
      (show m - (a + 1) ≤ m - a by omega)
    have hmul := Nat.mul_le_mul_left a hm
    simp only [Nat.add_mul, Nat.one_mul]
    omega

private theorem two_mul_choose_two {m : ℕ} (hm : 1 ≤ m) :
    (2 : ℚ) * (m.choose 2 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) := by
  have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_succ_right_eq m 1)
  norm_num [Nat.choose_one_right, Nat.cast_sub hm] at h
  nlinarith only [h]

/-- Three new clique vertices absorb the indicated degree bound. -/
theorem clique_step {s : ℕ} (hs : 1 ≤ s) :
    (3 * s - 1).choose 3 + (4 * s - 3).choose 2 ≤ (3 * s + 2).choose 3 := by
  have hsQ : (1 : ℚ) ≤ s := Nat.cast_le.mpr hs
  have h3s : 1 ≤ 3 * s := by omega
  have h4s : 3 ≤ 4 * s := by omega
  have ha := two_mul_choose_two (m := 3 * s - 1) (by omega)
  have hb := two_mul_choose_two (m := 4 * s - 3) (by omega)
  norm_num only [Nat.cast_sub h3s, Nat.cast_mul, Nat.cast_ofNat] at ha
  norm_num only [Nat.cast_sub h4s, Nat.cast_mul, Nat.cast_ofNat] at hb
  have hpoly : 0 ≤ 2 * (s : ℚ) ^ 2 + 10 * (s : ℚ) - 8 := by
    nlinarith only [hsQ, sq_nonneg (s : ℚ)]
  have hq : ((4 * s - 3).choose 2 : ℚ) ≤ 2 * ((3 * s - 1).choose 2 : ℚ) := by
    nlinarith only [ha, hb, hpoly]
  have hsmall : (4 * s - 3).choose 2 ≤ 2 * (3 * s - 1).choose 2 := by
    exact_mod_cast hq
  have hmono := Nat.choose_le_choose 2 (show 3 * s - 1 ≤ 3 * s by omega)
  have hp₁ := Nat.choose_succ_succ (3 * s - 1) 2
  have hp₂ := Nat.choose_succ_succ (3 * s) 2
  have hp₃ := Nat.choose_succ_succ (3 * s + 1) 2
  change (3 * s - 1 + 1).choose 3 =
    (3 * s - 1).choose 2 + (3 * s - 1).choose 3 at hp₁
  change (3 * s + 1).choose 3 = (3 * s).choose 2 + (3 * s).choose 3 at hp₂
  change (3 * s + 1 + 1).choose 3 =
    (3 * s + 1).choose 2 + (3 * s + 1).choose 3 at hp₃
  rw [show 3 * s - 1 + 1 = 3 * s by omega] at hp₁
  rw [show 3 * s + 1 + 1 = 3 * s + 2 by omega] at hp₃
  omega

private theorem previous_clique {s : ℕ} (hs : 1 ≤ s) :
    (3 * s - 1).choose 3 = (s - 1) * (3 * s - 1).choose 2 := by
  have h := Nat.choose_succ_right_eq (3 * s - 1) 2
  have he : 3 * s - 1 - 2 = 3 * (s - 1) := by omega
  rw [he] at h
  nlinarith only [h]

private theorem cover_step {n s : ℕ} (hs : 1 ≤ s) (hn : s ≤ n) :
    ((n - 1).choose 3 - (n - s).choose 3) + (n - 1).choose 2 =
      n.choose 3 - (n - s).choose 3 := by
  have hp := Nat.choose_eq_choose_pred_add (n := n) (k := 3) (by omega) (by decide)
  change n.choose 3 = (n - 1).choose 2 + (n - 1).choose 3 at hp
  have hm := Nat.choose_le_choose 3 (show n - s ≤ n - 1 by omega)
  have hc := Nat.sub_add_cancel hm
  omega

/-- The exact rank-three maximum is compatible with deleting one vertex and
reducing the matching parameter by one. This is only a binomial recurrence. -/
theorem max_step {n s : ℕ} (hs : 1 ≤ s) (hn : 3 * (s + 1) ≤ n) :
    max ((3 * (s - 1) + 2).choose 3)
        ((n - 1).choose 3 - (n - 1 - (s - 1)).choose 3) +
      (n - 1).choose 2 ≤
    max ((3 * s + 2).choose 3) (n.choose 3 - (n - s).choose 3) := by
  have hclique : 3 * (s - 1) + 2 = 3 * s - 1 := by omega
  have hindex : n - 1 - (s - 1) = n - s := by omega
  rw [hclique, hindex]
  have hcover := cover_step hs (show s ≤ n by omega)
  -- Here the previous parameter is zero: its clique and cover are both zero.
  by_cases hsone : s = 1
  · have hz : (3 * s - 1).choose 3 = 0 := by rw [hsone]; norm_num
    rw [hz, max_eq_right (Nat.zero_le _), hcover]
    exact le_max_right _ _
  by_cases hstar : (3 * s - 1).choose 3 ≤ (n - 1).choose 3 - (n - s).choose 3
  · rw [max_eq_right hstar, hcover]
    exact le_max_right _ _
  have hstrict : (n - 1).choose 3 - (n - s).choose 3 < (3 * s - 1).choose 3 :=
    lt_of_not_ge hstar
  have hlow : (s - 1) * (n - s).choose 2 ≤
      (n - 1).choose 3 - (n - s).choose 3 := by
    have h := choose_drop_lower (m := n - 1) (r := 3) (by decide)
      (s - 1) (by omega)
    rw [hindex] at h
    change (n - s).choose 3 + (s - 1) * (n - s).choose 2 ≤ (n - 1).choose 3 at h
    have hm := Nat.choose_le_choose 3 (show n - s ≤ n - 1 by omega)
    have hc := Nat.sub_add_cancel hm
    omega
  have hsmalln : n ≤ 4 * s - 2 := by
    by_contra hbad
    have hm := Nat.choose_le_choose 2 (show 3 * s - 1 ≤ n - s by omega)
    have hcontr : (3 * s - 1).choose 3 ≤
        (n - 1).choose 3 - (n - s).choose 3 := by
      calc
        _ = (s - 1) * (3 * s - 1).choose 2 := previous_clique hs
        _ ≤ (s - 1) * (n - s).choose 2 := Nat.mul_le_mul_left _ hm
        _ ≤ _ := hlow
    exact (not_lt_of_ge hcontr) hstrict
  rw [max_eq_left hstrict.le]
  calc
    _ ≤ (3 * s - 1).choose 3 + (4 * s - 3).choose 2 :=
      Nat.add_le_add_left (Nat.choose_le_choose 2 (by omega)) _
    _ ≤ (3 * s + 2).choose 3 := clique_step hs
    _ ≤ _ := le_max_left _ _

end Submissions.Erdos1020MatchingRankThreeRecurrence.Main

namespace Submissions.Erdos1020MatchingRankThreeOne.Main

open Finset

/-- The lower matching-parameter bound and the exact maximum recurrence force
an s-matching avoiding every designated vertex of a rank-three counterexample.
The lower-parameter induction hypothesis is retained explicitly. -/
theorem exists_matching_avoiding {n s : ℕ} (hs : 1 ≤ s) (hn : 3 * (s + 1) ≤ n)
    (hIH : ∀ m, 3 * s ≤ m → ∀ G : Finset (Finset (Fin m)),
      (∀ e ∈ G, e.card = 3) →
      (¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G ∧ M.card = s ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
      G.card ≤ max ((3 * (s - 1) + 2).choose 3)
        (m.choose 3 - (m - (s - 1)).choose 3))
    (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, e.card = 3)
    (hcounter : max ((3 * s + 2).choose 3)
      (n.choose 3 - (n - s).choose 3) < H.card) (v : Fin n) :
    ∃ M : Finset (Finset (Fin n)), M ⊆ H.filter (v ∉ ·) ∧ M.card = s ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
  classical
  by_contra hnone
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let D := H.filter (v ∉ ·)
  have hD : ∀ e ∈ D, e.card = 3 :=
    fun e he => hH e (mem_filter.mp he).1
  obtain ⟨G, hGc, hG, hGM⟩ :=
    Submissions.Erdos1020MatchingDeleteVertex.Main.reindex D v
      (fun e he => (mem_filter.mp he).2) hD hnone
  have hbound := hIH m (by omega) G hG hGM
  rw [hGc] at hbound
  have hdegree : (H.filter (v ∈ ·)).card ≤ m.choose 2 := by
    simpa using
      (Submissions.Erdos1020MatchingDegree.Main.card_containing_le hH
        (s := {v}) (by simp))
  have hpart := card_filter_add_card_filter_not (s := H) (fun e => v ∈ e)
  change (H.filter (v ∈ ·)).card + D.card = H.card at hpart
  have hstep := Submissions.Erdos1020MatchingRankThreeRecurrence.Main.max_step hs hn
  simp only [Nat.add_sub_cancel] at hstep
  omega

end Submissions.Erdos1020MatchingRankThreeOne.Main

namespace Submissions.Erdos1020MatchingRankThreeThreshold.Main

private theorem choose_three_cast {d : ℕ} (hd : 2 ≤ d) :
    (d.choose 3 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 6 := by
  have hd1 : 1 ≤ d := by omega
  have h := congrArg (fun a : ℕ => (a : ℚ))
    (Nat.descFactorial_eq_factorial_mul_choose d 3)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.factorial_succ, Nat.cast_sub hd, Nat.cast_sub hd1] at h
  nlinarith only [h]

/-- At the explicit ambient cap the star term reaches the clique term.
The factorization below avoids a real-valued root or asymptotic estimate. -/
theorem clique_le_star_of_ambient {s n : ℕ} (hs : 1 ≤ s)
    (hn : 7 * s + 5 ≤ 2 * n) :
    (3 * s + 2).choose 3 ≤ n.choose 3 - (n - s).choose 3 := by
  have hsn : s ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hm2 : 2 ≤ n - s := by omega
  have hsQ : (1 : ℚ) ≤ s := by exact_mod_cast hs
  have hnQ : 7 * (s : ℚ) + 5 ≤ 2 * (n : ℚ) := by exact_mod_cast hn
  have hprod : 0 ≤ (2 * (n : ℚ) - 7 * (s : ℚ) - 5) *
      (2 * (n : ℚ) + 5 * (s : ℚ) + 1) :=
    mul_nonneg (by linarith only [hnQ]) (by linarith only [hnQ, hsQ])
  have hquadratic : 0 ≤ 3 * ((n : ℚ) - (s : ℚ)) ^ 2 +
      3 * ((s : ℚ) - 2) * ((n : ℚ) - (s : ℚ)) -
        (26 * (s : ℚ) ^ 2 + 30 * (s : ℚ) + 4) := by
    nlinarith only [hprod, hsQ, sq_nonneg ((s : ℚ) - 1)]
  have hscaled := mul_nonneg (show (0 : ℚ) ≤ s by linarith only [hsQ]) hquadratic
  have hchoose : ((3 * s + 2).choose 3 : ℚ) + ((n - s).choose 3 : ℚ) ≤
      (n.choose 3 : ℚ) := by
    rw [choose_three_cast (d := 3 * s + 2) (by omega),
      choose_three_cast hm2, choose_three_cast hn2]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hsn]
    nlinarith only [hscaled]
  have hnat : (3 * s + 2).choose 3 + (n - s).choose 3 ≤ n.choose 3 := by
    exact_mod_cast hchoose
  omega

/-- The usual integer cap is sufficient, including both parities of s. -/
theorem clique_le_star_at_cap {s : ℕ} (hs : 1 ≤ s) :
    (3 * s + 2).choose 3 ≤ (7 * s / 2 + 3).choose 3 -
      (7 * s / 2 + 3 - s).choose 3 :=
  clique_le_star_of_ambient hs (by omega)

/-- If the previous ambient has not reached the clique term, the next one
satisfies exactly the tail-size guard used in the local case comparisons. -/
theorem critical_ambient_cap {s n : ℕ} (hs : 1 ≤ s)
    (hprev : (n - 1).choose 3 - (n - 1 - s).choose 3 < (3 * s + 2).choose 3) :
    2 * (n - (3 * s + 2)) ≤ s + 2 := by
  have hlt : 2 * (n - 1) < 7 * s + 5 := by
    by_contra h
    exact (not_le_of_gt hprev) (clique_le_star_of_ambient hs (by omega))
  omega

end Submissions.Erdos1020MatchingRankThreeThreshold.Main

namespace Submissions.Erdos1020MatchingRankThreeAmbient.Main

open Finset

/-- Once the previous ambient is star-dominant, its full bound extends to a
shifted family by deletion and the rank-two last-vertex link. The previous-
ambient induction hypothesis remains explicit. -/
theorem last_vertex_star_step {n s : ℕ} (hs : 1 ≤ s)
    (hn : 3 * (s + 1) ≤ n + 1)
    (hprev : (3 * s + 2).choose 3 ≤ n.choose 3 - (n - s).choose 3)
    (hIH : ∀ G : Finset (Finset (Fin n)),
      (∀ e ∈ G, e.card = 3) →
      (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ G ∧ M.card = s + 1 ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
      G.card ≤ max ((3 * s + 2).choose 3)
        (n.choose 3 - (n - s).choose 3))
    (H : Finset (Finset (Fin (n + 1)))) (hH : ∀ e ∈ H, e.card = 3)
    (hstable : ∀ i j : Fin (n + 1), i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin (n + 1))), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ (n + 1).choose 3 - (n + 1 - s).choose 3 := by
  classical
  let z : Fin (n + 1) := Fin.last n
  have hzstable : ∀ x, UV.IsCompressed {x} {z} H := by
    intro x
    by_cases hx : x = z
    · subst x
      exact UV.isCompressed_self _ _
    · exact hstable x z (lt_of_le_of_ne (Fin.le_last x) hx)
  have hDuniform : ∀ e ∈ H.nonMemberSubfamily z, e.card = 3 :=
    fun e he => hH e (mem_nonMemberSubfamily.mp he).1
  have hDfree : ¬ ∃ M : Finset (Finset (Fin (n + 1))),
      M ⊆ H.nonMemberSubfamily z ∧ M.card = s + 1 ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f := by
    rintro ⟨M, hMD, hMc, hMd⟩
    exact hfree ⟨M, fun e he => (mem_nonMemberSubfamily.mp (hMD he)).1, hMc, hMd⟩
  obtain ⟨D, hDc, hDu, hDm⟩ :=
    Submissions.Erdos1020MatchingDeleteVertex.Main.reindex (H.nonMemberSubfamily z) z
      (fun e he => (mem_nonMemberSubfamily.mp he).2) hDuniform hDfree
  have hD := hIH D hDu hDm
  rw [max_eq_right hprev, hDc] at hD
  have hLuniform : ∀ e ∈ H.memberSubfamily z, e.card = 2 := by
    intro e he
    obtain ⟨heH, hze⟩ := mem_memberSubfamily.mp he
    have hc := hH _ heH
    rw [card_insert_of_notMem hze] at hc
    omega
  have hLfree :=
    Submissions.Erdos1020MatchingShadowStep.Main.matchingFree_member_of_stable
      H z (by decide : 1 ≤ 3) hH (by simpa only [Fintype.card_fin] using hn)
      hzstable hfree
  obtain ⟨L, hLc, hLu, hLm⟩ :=
    Submissions.Erdos1020MatchingDeleteVertex.Main.reindex (H.memberSubfamily z) z
      (fun e he => (mem_memberSubfamily.mp he).2) hLuniform hLfree
  have hL := Submissions.Erdos1020MatchingRefined.Main.star_bound
    (r := 2) (s := s) (t := 2 * s + 1) (by decide) (by omega) (by omega)
    L hLu hLm
  rw [hLc] at hL
  have hpart := card_memberSubfamily_add_card_nonMemberSubfamily z H
  have hmono₂ := Nat.choose_le_choose 2 (show n - s ≤ n by omega)
  have hmono₃ := Nat.choose_le_choose 3 (show n - s ≤ n by omega)
  have hcancel₂ := Nat.sub_add_cancel hmono₂
  have hcancel₃ := Nat.sub_add_cancel hmono₃
  have hp := Nat.choose_succ_succ n 2
  change (n + 1).choose 3 = n.choose 2 + n.choose 3 at hp
  have hq := Nat.choose_succ_succ (n - s) 2
  change (n - s + 1).choose 3 = (n - s).choose 2 + (n - s).choose 3 at hq
  have hindex : n - s + 1 = n + 1 - s := by omega
  rw [hindex] at hq
  omega

end Submissions.Erdos1020MatchingRankThreeAmbient.Main

namespace Submissions.Erdos1020MatchingBoundary.Main

def Uniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- The Erdős matching bound when `k ≤ 2` or the ground set is too small for a
`k`-matching. The nontrivial case reuses Mathlib's Erdős–Ko–Rado theorem. -/
theorem proof :
    ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → (k ≤ 2 ∨ n < r * k) →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r) := by
  classical
  intro n r k hr hk hboundary H hU hM
  have hsized : (H : Set (Finset (Fin n))).Sized r := fun _ he => hU _ he
  have hcard : H.card ≤ n.choose r := by simpa using hsized.card_le
  by_cases hsmall : n < r * k
  · exact hcard.trans ((Nat.choose_le_choose r (by omega)).trans (le_max_left _ _))
  have hk2 : k ≤ 2 := hboundary.resolve_right hsmall
  have hcases : k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl
  · have hHempty : H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      apply hM
      refine ⟨{e}, Finset.singleton_subset_iff.mpr he, by simp, ?_⟩
      simp
    rw [hHempty, Finset.card_empty]
    exact Nat.zero_le _
  · have hinter : (H : Set (Finset (Fin n))).Intersecting := by
      intro e he f hf hdisj
      have hne : e ≠ f := by
        intro hef
        subst f
        have heempty : e = ∅ := (Finset.disjoint_self_iff_empty e).mp hdisj
        have hecard := hU e he
        rw [heempty, Finset.card_empty] at hecard
        omega
      apply hM
      refine ⟨{e, f}, Finset.insert_subset he (Finset.singleton_subset_iff.mpr hf), Finset.card_pair hne, ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hdisj
      · exact hdisj.symm
      · exact False.elim (hab rfl)
    have hekr := Finset.erdos_ko_rado hinter hsized (show r ≤ n / 2 by omega)
    have hidx : n - 2 + 1 = n - 1 := by omega
    have hpascal := Nat.choose_eq_choose_pred_add
      (show 0 < n by omega) (show 0 < r by omega)
    have hright : n.choose r - (n - 2 + 1).choose r = (n - 1).choose (r - 1) := by
      rw [hidx, hpascal, Nat.add_sub_cancel]
    rw [← hright] at hekr
    exact hekr.trans (le_max_right _ _)

/-- After the proved boundary cases, exactly the interior parameters remain. -/
theorem reduction :
    (∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r)) ↔
    (∀ (n r k : ℕ), 3 ≤ r → 3 ≤ k → r * k ≤ n →
      ∀ H : Finset (Finset (Fin n)), Uniform H r → MatchingFree H k →
        H.card ≤ max ((r * k - 1).choose r)
          (n.choose r - (n - k + 1).choose r)) := by
  constructor
  · intro h n r k hr hk _ H hU hM
    exact h n r k hr (by omega) H hU hM
  · intro h n r k hr hk H hU hM
    by_cases hb : k ≤ 2 ∨ n < r * k
    · exact proof n r k hr hk hb H hU hM
    · exact h n r k hr (by omega) (by omega) H hU hM

end Submissions.Erdos1020MatchingBoundary.Main

namespace Submissions.Erdos1020MatchingBoundary.PartitionAverage

/-- Average a matching-free uniform family over all relabelings of a fixed
matching. The fixed matching is supplied separately; no factorial is evaluated. -/
theorem bound {n r k : ℕ} (H P : Finset (Finset (Fin n)))
    (hk : 0 < k)
    (hH : ∀ e ∈ H, e.card = r)
    (hP : ∀ e ∈ P, e.card = r)
    (hPk : P.card = k)
    (hPd : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f)
    (hM : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card * k ≤ (k - 1) * n.choose r := by
  classical
  let A := (Finset.univ : Finset (Fin n)).powersetCard r
  let G := (Finset.univ : Finset (Equiv.Perm (Fin n)))
  let R (e : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
    e.map σ.toEmbedding ∈ P
  have hPne : P.Nonempty := Finset.card_pos.mp (by simpa [hPk] using hk)
  obtain ⟨e₀, he₀⟩ := hPne
  let d := (G.bipartiteAbove R e₀).card
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    refine ⟨Equiv.refl _, (Finset.mem_bipartiteAbove R).mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [R] using he₀
  have hdegree (e : Finset (Fin n)) (he : e.card = r) :
      (G.bipartiteAbove R e).card = d := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq e₀ e ((hP _ he₀).trans he.symm)
    have hτback : e.map τ.symm.toEmbedding = e₀ := by
      rw [← hτ]
      simp [Finset.map_map]
    change (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      e.map σ.toEmbedding ∈ P)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        e₀.map σ.toEmbedding ∈ P)).card
    refine Finset.card_bij' (fun σ _ => τ.trans σ) (fun σ _ => τ.symm.trans σ)
      ?_ ?_ ?_ ?_
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.trans_toEmbedding, ← Finset.map_map, hτ] using
        (Finset.mem_filter.mp hσ).2
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.trans_toEmbedding, ← Finset.map_map, hτback] using
        (Finset.mem_filter.mp hσ).2
    · intro σ _
      simp [← Equiv.trans_assoc]
    · intro σ _
      simp [← Equiv.trans_assoc]
  have hright (σ : Equiv.Perm (Fin n)) : (A.bipartiteBelow R σ).card = k := by
    calc
      (A.bipartiteBelow R σ).card = P.card := by
        apply Finset.card_equiv σ.finsetCongr
        intro e
        simp only [A, R, Finset.mem_bipartiteBelow, Finset.mem_powersetCard_univ,
          Equiv.finsetCongr_apply]
        constructor
        · exact And.right
        · intro he
          exact ⟨by simpa only [Finset.card_map] using hP _ he, he⟩
      _ = k := hPk
  have hrightH (σ : Equiv.Perm (Fin n)) :
      (H.bipartiteBelow R σ).card ≤ k - 1 := by
    apply Nat.le_pred_of_lt
    apply Nat.lt_of_not_ge
    intro hc
    obtain ⟨M, hMH, hMk⟩ := Finset.exists_subset_card_eq hc
    apply hM
    refine ⟨M, fun e he => ((Finset.mem_bipartiteBelow R).mp (hMH he)).1, hMk, ?_⟩
    intro e he f hf hef
    apply (Finset.disjoint_map σ.toEmbedding).mp
    exact hPd _ ((Finset.mem_bipartiteBelow R).mp (hMH he)).2
      _ ((Finset.mem_bipartiteBelow R).mp (hMH hf)).2
      (fun h => hef (Finset.map_injective σ.toEmbedding h))
  have hcount : n.choose r * d = G.card * k := by
    have hc := Finset.card_mul_eq_card_mul (s := A) (t := G) (m := d) (n := k) R
      (fun e he => hdegree e (Finset.mem_powersetCard_univ.mp he))
      (fun σ _ => hright σ)
    simpa [A] using hc
  have hbound : H.card * d ≤ G.card * (k - 1) :=
    Finset.card_mul_le_card_mul (s := H) (t := G) (m := d) (n := k - 1) R
      (fun e he => (hdegree e (hH e he)).ge) (fun σ _ => hrightH σ)
  apply Nat.le_of_mul_le_mul_right (c := d) ?_ hd
  calc
    H.card * k * d = H.card * d * k := by ac_rfl
    _ ≤ G.card * (k - 1) * k := Nat.mul_le_mul_right k hbound
    _ = (G.card * k) * (k - 1) := by ac_rfl
    _ = (n.choose r * d) * (k - 1) := by rw [hcount]
    _ = ((k - 1) * n.choose r) * d := by ac_rfl

end Submissions.Erdos1020MatchingBoundary.PartitionAverage

namespace Submissions.Erdos1020MatchingEndpoint.Main

/-- The exact clique bound at the divisible endpoint n = r*k. -/
theorem endpoint {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (H : Finset (Finset (Fin (r * k))))
    (hH : ∀ e ∈ H, e.card = r)
    (hM : ¬ ∃ M : Finset (Finset (Fin (r * k))), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ (r * k - 1).choose r := by
  classical
  let block (j : Fin k) : Finset (Fin (r * k)) :=
    ((Finset.univ : Finset (Fin r)) ×ˢ {j}).map finProdFinEquiv.toEmbedding
  have hbcard (j : Fin k) : (block j).card = r := by simp [block]
  have hbdisj (i j : Fin k) (hij : i ≠ j) : Disjoint (block i) (block j) := by
    apply (Finset.disjoint_map finProdFinEquiv.toEmbedding).mpr
    exact Finset.disjoint_product.mpr (Or.inr (Finset.disjoint_singleton.mpr hij))
  have hbinj : Function.Injective block := by
    intro i j heq
    by_contra hij
    have hd := hbdisj i j hij
    rw [heq] at hd
    have hempty := (Finset.disjoint_self_iff_empty (block j)).mp hd
    have hc := hbcard j
    rw [hempty, Finset.card_empty] at hc
    omega
  let P := Finset.univ.image block
  have hPk : P.card = k := by simp [P, Finset.card_image_of_injective _ hbinj]
  have hPU : ∀ e ∈ P, e.card = r := by
    intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    exact hbcard j
  have hPd : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f := by
    intro e he f hf hef
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hf
    exact hbdisj i j (fun hij => hef (congrArg block hij))
  have havg := Submissions.Erdos1020MatchingBoundary.PartitionAverage.bound
    H P hk hH hPU hPk hPd hM
  let C := (r * k).choose r
  let L := (r * k - 1).choose (r - 1)
  let R := (r * k - 1).choose r
  have hchoose : C = k * L := by
    simpa only [C, L, Nat.mul_comm] using
      (Nat.choose_mul_right (m := k) (n := r) (Nat.ne_of_gt hr))
  have hpascal : C = L + R := Nat.choose_eq_choose_pred_add (Nat.mul_pos hr hk) hr
  have hbinom : (k - 1) * C = R * k := by
    have heq : k * L + (k - 1) * C = k * L + R * k := by
      calc
        _ = C + (k - 1) * C := by rw [hchoose]
        _ = (1 + (k - 1)) * C := by rw [Nat.add_mul, Nat.one_mul]
        _ = k * C := by congr 1; omega
        _ = k * (L + R) := by rw [← hpascal]
        _ = k * L + R * k := by rw [Nat.mul_add, Nat.mul_comm k R]
    exact Nat.add_left_cancel heq
  exact Nat.le_of_mul_le_mul_right (havg.trans_eq hbinom) hk

end Submissions.Erdos1020MatchingEndpoint.Main

namespace Submissions.Erdos1020MatchingRankThreeThreeMatching.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main (Uniform MatchingFree)

/-- The ten-vertex counterexample supplies an avoiding two-matching by the
checked k=2 boundary theorem, so the actual ten-vertex ONE bound applies. -/
private theorem ten_bound
    (H : Finset (Finset (Fin 10))) (hH : Uniform H 3)
    (hfree : MatchingFree H 3)
    (hstable : ∀ i j : Fin 10, i < j → UV.IsCompressed {i} {j} H) :
    H.card ≤ 64 := by
  classical
  by_contra hbad
  have hcounter : max ((3 * 2 + 2).choose 3)
      ((10 : ℕ).choose 3 - (10 - 2).choose 3) < H.card := by
    change 64 < H.card
    omega
  have hIH : ∀ m, 3 * 2 ≤ m → ∀ G : Finset (Finset (Fin m)),
      (∀ e ∈ G, e.card = 3) →
      (¬ ∃ M : Finset (Finset (Fin m)), M ⊆ G ∧ M.card = 2 ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
      G.card ≤ max ((3 * (2 - 1) + 2).choose 3)
        (m.choose 3 - (m - (2 - 1)).choose 3) := by
    intro m hm G hG hGm
    have hb := Submissions.Erdos1020MatchingBoundary.Main.proof m 3 2
      (by decide) (by decide) (Or.inl (by decide)) G hG hGm
    have hindex : m - 2 + 1 = m - 1 := by omega
    simpa only [hindex] using hb
  obtain ⟨M, hMH, hMc, hMd⟩ :=
    Submissions.Erdos1020MatchingRankThreeOne.Main.exists_matching_avoiding
      (s := 2) (by decide) (by decide) hIH H hH hcounter (0 : Fin 10)
  let A : Finset (Fin 10) := univ.filter (fun x => x.val < 8)
  have hA : A.card = 8 := by decide
  have hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x := by
    intro a ha x hx
    have ha8 : a.val < 8 := (mem_filter.mp ha).2
    have hx8 : ¬ x.val < 8 := by
      intro h
      exact hx (mem_filter.mpr ⟨mem_univ x, h⟩)
    change a.val < x.val
    omega
  have hvA : (0 : Fin 10) ∈ A := by decide
  have hleast : ∀ x ∈ A, (0 : Fin 10) ≤ x := by
    intro x _
    exact Fin.zero_le x
  have hcount := Submissions.Erdos1020MatchingRankThreeTenOne.Main.bound
    H A hH hfree hA hcut hstable 0 hvA hleast
    M (fun E hE => (mem_filter.mp (hMH hE)).1) hMc hMd
    (fun E hE => (mem_filter.mp (hMH hE)).2)
  omega

/-- The original matching-conjecture maximum for rank three and forbidden
matching size three, for every ambient size. -/
theorem proof (n : ℕ) (H : Finset (Finset (Fin n)))
    (hH : Uniform H 3) (hfree : MatchingFree H 3) :
    H.card ≤ max ((3 * 3 - 1).choose 3)
      (n.choose 3 - (n - 3 + 1).choose 3) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 9
    · exact Submissions.Erdos1020MatchingBoundary.Main.proof n 3 3
        (by decide) (by decide) (Or.inr hsmall) H hH hfree
    by_cases h9 : n = 9
    · subst n
      exact (Submissions.Erdos1020MatchingEndpoint.Main.endpoint
        (r := 3) (k := 3) (by decide) (by decide) H hH hfree).trans
        (le_max_left _ _)
    obtain ⟨K, hKc, hK, hKm, hstable⟩ :=
      Submissions.Erdos1020ShiftNormalize.Main.exists_shifted H hH hfree
    have hindex : n - 3 + 1 = n - 2 := by omega
    rw [hindex, ← hKc]
    by_cases h10 : n = 10
    · subst n
      exact ten_bound K hK hKm hstable
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 10 ≤ m := by omega
    have hprev : (3 * 2 + 2).choose 3 ≤
        m.choose 3 - (m - 2).choose 3 :=
      Submissions.Erdos1020MatchingRankThreeThreshold.Main.clique_le_star_of_ambient
        (s := 2) (by decide) (by omega)
    have hstep := Submissions.Erdos1020MatchingRankThreeAmbient.Main.last_vertex_star_step
      (n := m) (s := 2) (by decide) (by omega) hprev
      (by
        intro G hG hGm
        have hb := ih m (by omega) G hG hGm
        have hidx : m - 3 + 1 = m - 2 := by omega
        simpa only [hidx] using hb)
      K hK hstable hKm
    exact hstep.trans (le_max_right _ _)

end Submissions.Erdos1020MatchingRankThreeThreeMatching.Main

namespace Submissions.Erdos1020MatchingRankThreeK3Proof.Main

/-- Original signature and natural maximum at r=3,k=3. -/
theorem proof : ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → r = 3 → k = 3 →
    ∀ H : Finset (Finset (Fin n)), (∀ E ∈ H, E.card = r) →
      (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
        ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) →
      H.card ≤ max ((r * k - 1).choose r)
        (n.choose r - (n - k + 1).choose r) := by
  intro n r k _ _ hr hk H hH hfree
  subst r
  subst k
  exact Submissions.Erdos1020MatchingRankThreeThreeMatching.Main.proof n H hH hfree

end Submissions.Erdos1020MatchingRankThreeK3Proof.Main
