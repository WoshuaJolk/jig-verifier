import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Finset.Preimage
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Fin.Embedding

namespace Submissions.Erdos1020MatchingRankThreeLowGraph.Main

open Finset

attribute [local instance 2000] Finset.decidableDforallFinset

/-- The six bottom/middle vertices on the existing three-by-three board. -/
def lowVertices : Finset (Fin 3 × Fin 3) :=
  univ.filter (fun p => p.2 < 2)

/-- The twelve AA, AB and BB pairs joining different columns. -/
def lowPairs : Finset (Finset (Fin 3 × Fin 3)) :=
  lowVertices.powersetCard 2 |>.filter (fun Q => (Q.image Prod.fst).card = 2)

/-- Bottom i is active when two disjoint present low edges avoid it. -/
def active (P : Finset (Finset (Fin 3 × Fin 3))) : Finset (Fin 3) :=
  univ.filter (fun i => ∃ Q ∈ P, ∃ R ∈ P,
    Disjoint Q R ∧ (i, 0) ∉ Q ∪ R)

theorem lowPairs_card : lowPairs.card = 12 := by decide

theorem mem_lowPairs (Q : Finset (Fin 3 × Fin 3)) :
    Q ∈ lowPairs ↔ Q.card = 2 ∧ (Q.image Prod.fst).card = 2 ∧
      ∀ p ∈ Q, p.2 < 2 := by
  simp only [lowPairs, mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hwidth⟩
    exact ⟨hcard, hwidth, fun p hp => (mem_filter.mp (hsub hp)).2⟩
  · rintro ⟨hcard, hwidth, hheight⟩
    exact ⟨⟨fun p hp => mem_filter.mpr ⟨mem_univ p, hheight p hp⟩, hcard⟩, hwidth⟩

@[simp] theorem mem_active (P : Finset (Finset (Fin 3 × Fin 3))) (i : Fin 3) :
    i ∈ active P ↔ ∃ Q ∈ P, ∃ R ∈ P,
      Disjoint Q R ∧ (i, 0) ∉ Q ∪ R := by
  simp only [active, mem_filter, mem_univ, true_and]

theorem active_mono {P Q : Finset (Finset (Fin 3 × Fin 3))} (hPQ : P ⊆ Q) :
    active P ⊆ active Q := by
  intro i hi
  obtain ⟨E, hE, F, hF, hdis, hav⟩ := (mem_active P i).mp hi
  exact (mem_active Q i).mpr ⟨E, hPQ hE, F, hPQ hF, hdis, hav⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- Closed finite certificates enumerate only the exact-size subfamilies of
this twelve-edge carrier. The kernel checks each decision procedure directly. -/
private theorem six_certificate :
    ∀ P ∈ lowPairs.powersetCard 6, 1 ≤ (active P).card := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
private theorem eight_certificate :
    ∀ P ∈ lowPairs.powersetCard 8, 2 ≤ (active P).card := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
private theorem nine_certificate :
    ∀ P ∈ lowPairs.powersetCard 9, 3 ≤ (active P).card := by decide +kernel

theorem one_le_active_card (P : Finset (Finset (Fin 3 × Fin 3)))
    (hP : P ⊆ lowPairs) (hcard : 6 ≤ P.card) : 1 ≤ (active P).card := by
  obtain ⟨Q, hQP, hQc⟩ := exists_subset_card_eq hcard
  exact (six_certificate Q (mem_powersetCard.mpr ⟨hQP.trans hP, hQc⟩)).trans
    (card_le_card (active_mono hQP))

theorem two_le_active_card (P : Finset (Finset (Fin 3 × Fin 3)))
    (hP : P ⊆ lowPairs) (hcard : 8 ≤ P.card) : 2 ≤ (active P).card := by
  obtain ⟨Q, hQP, hQc⟩ := exists_subset_card_eq hcard
  exact (eight_certificate Q (mem_powersetCard.mpr ⟨hQP.trans hP, hQc⟩)).trans
    (card_le_card (active_mono hQP))

theorem three_le_active_card (P : Finset (Finset (Fin 3 × Fin 3)))
    (hP : P ⊆ lowPairs) (hcard : 9 ≤ P.card) : 3 ≤ (active P).card := by
  obtain ⟨Q, hQP, hQc⟩ := exists_subset_card_eq hcard
  exact (nine_certificate Q (mem_powersetCard.mpr ⟨hQP.trans hP, hQc⟩)).trans
    (card_le_card (active_mono hQP))

theorem active_eq_univ_of_nine (P : Finset (Finset (Fin 3 × Fin 3)))
    (hP : P ⊆ lowPairs) (hcard : 9 ≤ P.card) : active P = univ := by
  apply eq_of_subset_of_card_le (subset_univ _)
  simpa only [card_univ, Fintype.card_fin] using three_le_active_card P hP hcard

end Submissions.Erdos1020MatchingRankThreeLowGraph.Main

-- Source: RankThreeNarrow.lean
-- Source: RankThreeLocal.lean
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

-- Source: RankThreeLocalBody.lean
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

/-- A missing pair containing the least head vertex rules out every genuine
pair containing its other endpoint. The repeated-endpoint singleton is excluded explicitly. -/
theorem pair_not_mem {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun e => e ∩ A))
    (x : Fin n) (hxA : x ∈ A) (hxd : x ≠ d) :
    ({x, d} : Finset (Fin n)) ∉ H.image (fun e => e ∩ A) := by
  intro hpair
  by_cases hxv : x = v
  · subst x
    exact hgap hpair
  have hvx : v < x := lt_of_le_of_ne (hleast x hxA) (Ne.symm hxv)
  have h := replace_mem_trace H A hstable {x, d} hpair v x hvA hvx
    (by simp) (by simp [Ne.symm hxv, hvd.ne])
  apply hgap
  simpa [hxd] using h

/-- Every two-point actual trace avoids the second endpoint of the missing pair. -/
theorem pair_avoids_second {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun e => e ∩ A))
    (T : Finset (Fin n)) (hT : T ∈ H.image (fun e => e ∩ A)) (hTc : T.card = 2) :
    d ∉ T := by
  classical
  intro hdT
  have hec : (T.erase d).card = 1 := by rw [card_erase_of_mem hdT, hTc]
  obtain ⟨x, hx⟩ := card_eq_one.mp hec
  have hxe : x ∈ T.erase d := by rw [hx]; simp
  have hxd : x ≠ d := (mem_erase.mp hxe).1
  have hTA : T ⊆ A := by
    obtain ⟨e, _, heT⟩ := mem_image.mp hT
    rw [← heT]
    exact inter_subset_right
  have hpair : T = {x, d} := by
    calc
      T = insert d (T.erase d) := (insert_erase hdT).symm
      _ = {d, x} := by rw [hx]
      _ = {x, d} := pair_comm _ _
  exact pair_not_mem H A hstable v d hvA hleast hvd hgap x
    (hTA (mem_of_mem_erase hxe)) hxd (hpair ▸ hT)

/-- A local indexed matching with one more member than its selected blocks,
including repeated empty traces, would extend by all outside blocks to a forbidden
indexed trace matching. No cardinal maximality or ONE assumption is used here. -/
theorem no_indexed_local_trace_matching {n r s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i))
    (M : Finset (Fin s)) (hι : Fintype.card ι = M.card + 1)
    (T : ι → Finset (Fin n)) (hT : ∀ i, T i ∈ H.image (fun e => e ∩ A))
    (hTU : ∀ i, T i ⊆ G ∪ M.biUnion B) :
    ¬ Pairwise (fun i j => Disjoint (T i) (T j)) := by
  classical
  intro hTd
  have hw : ∀ i, ∃ e, e ∈ H ∧ e ∩ A = T i := fun i => mem_image.mp (hT i)
  choose f hf hfA using hw
  have hlocalout (i : Fin s) (hi : i ∉ M) : Disjoint (G ∪ M.biUnion B) (B i) := by
    apply disjoint_union_left.mpr
    refine ⟨hGB i, disjoint_left.mpr ?_⟩
    intro x hx hxi
    obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hx
    exact disjoint_left.mp (hBd (fun h : j = i => hi (h ▸ hj))) hxj hxi
  have hTout (j : ι) (i : Fin s) (hi : i ∉ M) : Disjoint (T j) (B i) :=
    (hlocalout i hi).mono (hTU j) (Subset.refl _)
  let O := (univ : Finset (Fin s)) \ M
  let g : ι ⊕ O → Finset (Fin n) := Sum.elim f (fun i => B i.val)
  have hg : ∀ i, g i ∈ H := by
    intro i
    rcases i with j | i
    · exact hf j
    · exact hBH i.val
  have hMc : M.card ≤ s := by
    simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ M)
  have hOc : O.card = s - M.card := by
    dsimp only [O]
    rw [card_sdiff_of_subset (subset_univ M), card_univ, Fintype.card_fin]
  have hcard : Fintype.card (ι ⊕ O) = s + 1 := by
    rw [Fintype.card_sum, Fintype.card_coe, hι, hOc]
    omega
  apply Submissions.Erdos1020MatchingTrace.Main.no_indexed_trace_matching
    hr H A hH hcard hA hcut hstable hfree g hg
  intro i j hij
  rcases i with l | i <;> rcases j with l' | j
  · change Disjoint (f l ∩ A) (f l' ∩ A)
    rw [hfA l, hfA l']
    exact hTd (fun h => hij (congrArg Sum.inl h))
  · change Disjoint (f l ∩ A) (B j.val ∩ A)
    rw [hfA l, inter_eq_left.mpr (hBA j.val)]
    exact hTout l j.val (mem_sdiff.mp j.property).2
  · change Disjoint (B i.val ∩ A) (f l' ∩ A)
    rw [inter_eq_left.mpr (hBA i.val), hfA l']
    exact (hTout l' i.val (mem_sdiff.mp i.property).2).symm
  · change Disjoint (B i.val ∩ A) (B j.val ∩ A)
    exact (hBd (fun h => hij (congrArg Sum.inr (Subtype.ext h)))).mono
      inter_subset_left inter_subset_left

/-- Literal local matching-freeness. In rank three, selecting three blocks
specializes this conclusion to the absence of a four-matching in the actual local family. -/
theorem local_trace_matchingFree {n r s : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (M : Finset (Fin s)) :
    ¬ ∃ K : Finset (Finset (Fin n)),
      K ⊆ (H.image (fun e => e ∩ A)).filter (fun T => T ⊆ G ∪ M.biUnion B) ∧
      K.card = M.card + 1 ∧ ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f := by
  classical
  rintro ⟨K, hK, hKc, hKd⟩
  apply no_indexed_local_trace_matching (ι := K) hr H A hH hA hcut hstable hfree
    G B hBH hBA hBd hGB M (by simpa only [Fintype.card_coe] using hKc)
    (fun i : K => i.val) (fun i => (mem_filter.mp (hK i.property)).1)
    (fun i => (mem_filter.mp (hK i.property)).2)
  intro i j hij
  exact hKd i.val i.property j.val j.property (fun h => hij (Subtype.ext h))

end Submissions.Erdos1020MatchingRankThreeLocal.Main

-- Source: RankThreeNarrowBody.lean
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

/-- Any two actual traces contained in one gap-and-block region intersect:
otherwise all remaining blocks extend them to a forbidden indexed trace matching. -/
theorem traces_intersect_on_block {n r s : ℕ} (hr : 0 < r)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = r) (hA : A.card + 1 = r * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (i : Fin s)
    (S T : Finset (Fin n)) (hS : S ∈ H.image (fun e => e ∩ A))
    (hT : T ∈ H.image (fun e => e ∩ A))
    (hSU : S ⊆ G ∪ B i) (hTU : T ⊆ G ∪ B i) : ¬ Disjoint S T := by
  intro hdis
  let f : Bool → Finset (Fin n) := fun b => cond b S T
  apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
    (ι := Bool) hr H A hH hA hcut hstable hfree G B hBH hBA hBd hGB {i}
    (by simp only [Fintype.card_bool, card_singleton]) f
    (by intro b; cases b; exact hT; exact hS)
    (by
      intro b
      cases b
      · change T ⊆ G ∪ ({i} : Finset (Fin s)).biUnion B
        simpa only [singleton_biUnion] using hTU
      · change S ⊆ G ∪ ({i} : Finset (Fin s)).biUnion B
        simpa only [singleton_biUnion] using hSU)
  intro b c hbc
  cases b <;> cases c
  · exact (hbc rfl).elim
  · exact hdis.symm
  · exact hdis
  · exact (hbc rfl).elim

/-- Actual fixed-block narrow-pair bounds under the checked gap and block
properties. This is only the narrow contribution to the eleven-vertex comparison. -/
theorem actual_narrow_bounds {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun e => e ∩ A))
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i)) (i : Fin s) :
    ((H.image (fun e => e ∩ A)).filter (fun S => S ⊆ {v, d} ∪ B i ∧ S.card = 2)).card ≤
        (({v, d} ∪ B i).powersetCard 3 \ H.image (fun e => e ∩ A)).card ∧
      ((H.image (fun e => e ∩ A)).filter (fun S => S ⊆ {v, d} ∪ B i ∧ S.card = 2)).card ≤ 3 := by
  apply narrow_bounds ({v, d} ∪ B i)
    (by rw [card_union_of_disjoint (hGB i), card_pair hvd.ne, hH _ (hBH i)])
    d (by simp) (H.image (fun e => e ∩ A))
  · exact Submissions.Erdos1020MatchingRankThreeLocal.Main.pair_avoids_second
      H A hstable v d hvA hleast hvd hgap
  · intro S hS hSU T hT hTU
    exact traces_intersect_on_block (by decide) H A hH hA hcut hstable hfree
      {v, d} B hBH hBA hBd hGB i S T hS hT hSU hTU

end Submissions.Erdos1020MatchingRankThreeNarrow.Main

-- Source: BlockSupport.lean
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

-- Source: RankThreeWidthOneBody.lean
namespace Submissions.Erdos1020MatchingRankThreeWidthOne.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- A set in one block region that is not contained in the gap has exactly that support. -/
theorem support_singleton_of_local {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (S : Finset α) (hnotG : ¬ S ⊆ G)
    (i : Fin s) (hSi : S ⊆ G ∪ B i) : support B S = {i} := by
  apply Subset.antisymm
  · intro j hj
    obtain ⟨x, hx⟩ := (mem_support B S j).mp hj
    rcases mem_union.mp (hSi (mem_inter.mp hx).1) with hxG | hxi
    · exact (disjoint_left.mp (hG j) hxG (mem_inter.mp hx).2).elim
    · apply mem_singleton.mpr
      by_contra hji
      exact disjoint_left.mp (hB hji) (mem_inter.mp hx).2 hxi
  · apply singleton_subset_iff.mpr
    obtain ⟨x, hxS, hxG⟩ := not_subset.mp hnotG
    have hxi : x ∈ B i := (mem_union.mp (hSi hxS)).resolve_left hxG
    exact (mem_support B S i).mpr ⟨x, mem_inter.mpr ⟨hxS, hxi⟩⟩

/-- Sets of width one are partitioned by their unique supporting block. -/
theorem width_one_card_eq_sum {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i))
    (D : Finset (Finset α)) (hnotG : ∀ S ∈ D, ¬ S ⊆ G) (M : Finset (Fin s)) :
    (D.filter (fun S => S ⊆ region G B M ∧ (support B S).card = 1)).card =
      ∑ i ∈ M, (D.filter (fun S => S ⊆ G ∪ B i)).card := by
  classical
  let C := fun i : Fin s => D.filter (fun S => S ⊆ G ∪ B i)
  have hfull : region G B M ⊆ G ∪ univ.biUnion B :=
    union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ M))
  have heq : D.filter (fun S => S ⊆ region G B M ∧ (support B S).card = 1) =
      M.biUnion C := by
    ext S
    constructor
    · intro hS
      obtain ⟨hSD, hSM, hSc⟩ := mem_filter.mp hS
      obtain ⟨i, hi⟩ := card_eq_one.mp hSc
      have hsM := (subset_region_iff G B hB hG S (hSM.trans hfull) M).mp hSM
      have hiM : i ∈ M := hsM (by rw [hi]; simp)
      have hSi : S ⊆ G ∪ B i := by
        have h := (subset_region_iff G B hB hG S (hSM.trans hfull) {i}).mpr
          (by rw [hi])
        simpa only [region, singleton_biUnion] using h
      exact mem_biUnion.mpr ⟨i, hiM, mem_filter.mpr ⟨hSD, hSi⟩⟩
    · intro hS
      obtain ⟨i, hiM, hiS⟩ := mem_biUnion.mp hS
      have hSD := (mem_filter.mp hiS).1
      have hSi := (mem_filter.mp hiS).2
      have hs := support_singleton_of_local G B hB hG S (hnotG S hSD) i hSi
      have hSM : S ⊆ region G B M := hSi.trans
        (union_subset_union (Subset.refl _) (subset_biUnion_of_mem B hiM))
      exact mem_filter.mpr ⟨hSD, hSM, by rw [hs]; simp⟩
  rw [heq]
  apply card_biUnion
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro S hSi hSj
  have hiS := support_singleton_of_local G B hB hG S
    (hnotG S (mem_filter.mp hSi).1) i (mem_filter.mp hSi).2
  have hjS := support_singleton_of_local G B hB hG S
    (hnotG S (mem_filter.mp hSj).1) j (mem_filter.mp hSj).2
  have he : ({i} : Finset (Fin s)) = {j} := hiS.symm.trans hjS
  exact hij (mem_singleton.mp (he ▸ mem_singleton_self i))

private theorem missing_filter {α : Type*} [DecidableEq α]
    (U V : Finset α) (hVU : V ⊆ U) (F : Finset (Finset α)) (r : ℕ) :
    ((U.powersetCard r \ F).filter (fun S => S ⊆ V)) = V.powersetCard r \ F := by
  classical
  ext S
  simp only [mem_filter, mem_sdiff, mem_powersetCard]
  constructor
  · rintro ⟨⟨⟨_, hSr⟩, hSF⟩, hSV⟩
    exact ⟨⟨hSV, hSr⟩, hSF⟩
  · rintro ⟨⟨hSV, hSr⟩, hSF⟩
    exact ⟨⟨⟨hSV.trans hVU, hSr⟩, hSF⟩, hSV⟩

/-- Aggregate the exact one-block bounds: all width-one pairs injectively charge
missing width-one triples, and there are at most three pairs per selected block. -/
theorem width_one_bounds {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (hGc : G.card = 2) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (F : Finset (Finset α)) (hgap : G ∉ F)
    (M : Finset (Fin s))
    (hpoint : ∀ i ∈ M,
      (F.filter (fun S => S ⊆ G ∪ B i ∧ S.card = 2)).card ≤
        ((G ∪ B i).powersetCard 3 \ F).card ∧
      (F.filter (fun S => S ⊆ G ∪ B i ∧ S.card = 2)).card ≤ 3) :
    (F.filter (fun S => S ⊆ region G B M ∧ S.card = 2 ∧ (support B S).card = 1)).card ≤
        (((region G B M).powersetCard 3 \ F).filter (fun S => (support B S).card = 1)).card ∧
      (F.filter (fun S => S ⊆ region G B M ∧ S.card = 2 ∧ (support B S).card = 1)).card ≤
        3 * M.card := by
  classical
  let P := F.filter (fun S => S.card = 2)
  have hnotP : ∀ S ∈ P, ¬ S ⊆ G := by
    intro S hS hSG
    have hc := (mem_filter.mp hS).2
    have he : S = G := eq_of_subset_of_card_le hSG (by rw [hGc, hc])
    exact hgap (he ▸ (mem_filter.mp hS).1)
  have hPcount :
      (F.filter (fun S => S ⊆ region G B M ∧ S.card = 2 ∧ (support B S).card = 1)).card =
        ∑ i ∈ M, (F.filter (fun S => S ⊆ G ∪ B i ∧ S.card = 2)).card := by
    have h := width_one_card_eq_sum G B hB hG P hnotP M
    simpa only [P, filter_filter, and_assoc, and_left_comm, and_comm] using h
  let R := G ∪ univ.biUnion B
  let D := R.powersetCard 3 \ F
  have hnotD : ∀ S ∈ D, ¬ S ⊆ G := by
    intro S hS hSG
    have hc := (mem_powersetCard.mp (mem_sdiff.mp hS).1).2
    have hle := card_le_card hSG
    omega
  have hMR : region G B M ⊆ R :=
    union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ M))
  have hiR (i : Fin s) : G ∪ B i ⊆ R :=
    union_subset_union (Subset.refl _) (subset_biUnion_of_mem B (mem_univ i))
  have hDcount :
      (((region G B M).powersetCard 3 \ F).filter (fun S => (support B S).card = 1)).card =
        ∑ i ∈ M, ((G ∪ B i).powersetCard 3 \ F).card := by
    have h := width_one_card_eq_sum G B hB hG D hnotD M
    have heq : D.filter (fun S => S ⊆ region G B M ∧ (support B S).card = 1) =
        ((region G B M).powersetCard 3 \ F).filter (fun S => (support B S).card = 1) := by
      dsimp only [D]
      rw [← filter_filter, missing_filter R (region G B M) hMR F 3]
    rw [heq] at h
    calc
      _ = ∑ i ∈ M, (D.filter (fun S => S ⊆ G ∪ B i)).card := h
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        exact congrArg Finset.card (missing_filter R (G ∪ B i) (hiR i) F 3)
  constructor
  · rw [hPcount, hDcount]
    exact sum_le_sum (fun i hi => (hpoint i hi).1)
  · rw [hPcount]
    calc
      _ ≤ ∑ i ∈ M, 3 := sum_le_sum (fun i hi => (hpoint i hi).2)
      _ = 3 * M.card := by simp [Nat.mul_comm]

/-- The actual three-block local trace has p1≤d1 and p1≤9, with no weighted
comparison assumed. The one-block narrow helper supplies every counting premise. -/
theorem actual_width_one_bounds {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ e ∈ H, e.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun e => e ∩ A))
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (M : Finset (Fin s)) (hMc : M.card = 3) :
    ((H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region {v, d} B M ∧
      S.card = 2 ∧ (support B S).card = 1)).card ≤
        (((region {v, d} B M).powersetCard 3 \ H.image (fun e => e ∩ A)).filter
          (fun S => (support B S).card = 1)).card ∧
      ((H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region {v, d} B M ∧
        S.card = 2 ∧ (support B S).card = 1)).card ≤ 9 := by
  have h := width_one_bounds {v, d} (card_pair hvd.ne) B hBd hGB
    (H.image (fun e => e ∩ A)) hgap M (fun i _ =>
      Submissions.Erdos1020MatchingRankThreeNarrow.Main.actual_narrow_bounds
        H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB i)
  simpa only [hMc] using h

end Submissions.Erdos1020MatchingRankThreeWidthOne.Main

namespace Submissions.Erdos1020ShiftNormalize.Main

open Finset

def Uniform {α : Type*} (H : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def MatchingFree {α : Type*} (H : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f


end Submissions.Erdos1020ShiftNormalize.Main

namespace Submissions.Erdos1020MatchingMaximalShift.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main

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

namespace Submissions.Erdos1020MatchingRankThreeBC.Main

open Finset

/-- The four labeled sets used in the first BC obstruction. Coordinates are
(column, height), numbered 0,1,2 in each direction. -/
def upperPair : Finset (Fin 3 × Fin 3) := {(0, 2), (1, 1)}
def lowerPair : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0)}
def hub : Finset (Fin 3 × Fin 3) := {(2, 1)}
def seed : Finset (Fin 3 × Fin 3) := {(0, 0), (1, 2), (2, 0)}

/-- Three disjoint members exclude any fourth member disjoint from them, in
an indexed matching-free family. Empty or repeated sets are not discarded. -/
theorem missing_of_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (P Q R T : Finset α) (hP : P ∈ F) (hQ : Q ∈ F) (hR : R ∈ F)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R)
    (hPT : Disjoint P T) (hQT : Disjoint Q T) (hRT : Disjoint R T) : T ∉ F := by
  intro hT
  let f : Bool × Bool → Finset α := fun i =>
    if i.1 then (if i.2 then T else R) else (if i.2 then Q else P)
  have hf : ∀ i, f i ∈ F := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    · exact hP
    · exact hQ
    · exact hR
    · exact hT
  apply hno f hf
  rintro ⟨a, b⟩ ⟨c, d⟩ hne
  cases a <;> cases b <;> cases c <;> cases d
  all_goals first
    | exact (hne rfl).elim
    | exact hPQ
    | exact hPR
    | exact hPT
    | exact hPQ.symm
    | exact hQR
    | exact hQT
    | exact hPR.symm
    | exact hQR.symm
    | exact hRT
    | exact hPT.symm
    | exact hQT.symm
    | exact hRT.symm

/-- The BC seed is missing once the two indicated pairs and the hub edge are
present. Only the exact finite pattern and indexed no-four-matching are used. -/
theorem seed_missing {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hP : upperPair.image e ∈ F) (hQ : lowerPair.image e ∈ F)
    (hR : G ∪ hub.image e ∈ F) : seed.image e ∉ F := by
  have hd (X Y : Finset (Fin 3 × Fin 3)) (h : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr h
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  apply missing_of_three F hno (upperPair.image e) (lowerPair.image e)
    (G ∪ hub.image e) (seed.image e) hP hQ hR
  · exact hd _ _ (by decide)
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ (by decide)⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ (by decide)⟩
  · exact hd _ _ (by decide)
  · exact hd _ _ (by decide)
  · exact disjoint_union_left.mpr ⟨hdG _, hd _ _ (by decide)⟩

/-- Lower the BC pair {c1,b2} to {b1,a2} in the actual trace, by two
within-column shifts of witnessing original edges. -/
theorem lower_pair_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A)) :
    lowerPair.image e ∈ H.image (fun S => S ∩ A) := by
  have hne (p q : Fin 3 × Fin 3) (h : p ≠ q) : e p ≠ e q := fun h' => h (he h')
  have h1 := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
    H A hstable (upperPair.image e) hP (e (0, 1)) (e (0, 2)) (heA _)
    (hrow 0 (by decide)) (by simp [upperPair])
    (by simp [upperPair, hne (0, 1) (0, 2) (by decide), hne (0, 1) (1, 1) (by decide)])
  have h1' : ({e (0, 1), e (1, 1)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) := by
    simpa [upperPair, hne (0, 2) (1, 1) (by decide)] using h1
  have h2 := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
    H A hstable {e (0, 1), e (1, 1)} h1' (e (1, 0)) (e (1, 1)) (heA _)
    (hrow 1 (by decide)) (by simp)
    (by simp [hne (1, 0) (0, 1) (by decide), hne (1, 0) (1, 1) (by decide)])
  simpa [lowerPair, hne (1, 1) (0, 1) (by decide), pair_comm] using h2

/-- Actual local BC seed exclusion. The hub trace remains an explicit premise
supplied upstream by the minimum-gap middle-completion theorem; no (A) is assumed. -/
theorem actual_seed_missing {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (M : Finset (Fin s)) (hMc : M.card = 3)
    (j : Fin 3 → Fin s) (hjM : ∀ i, j i ∈ M)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A))
    (hR : G ∪ hub.image e ∈ H.image (fun S => S ∩ A)) :
    seed.image e ∉ H.image (fun S => S ∩ A) := by
  classical
  let U := G ∪ M.biUnion B
  let F := (H.image (fun S => S ∩ A)).filter (fun S => S ⊆ U)
  have heA (p : Fin 3 × Fin 3) : e p ∈ A := hBA _ (heB p.1 p.2)
  have hsub (X : Finset (Fin 3 × Fin 3)) : X.image e ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr ⟨j i, hjM i, heB i a⟩)
  have hdG : Disjoint G (univ.image e) := by
    apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (j i)) hxG (heB i a)
  have hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro f hf
    apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree G B hBH hBA hBd hGB M
      (by simp only [Fintype.card_prod, Fintype.card_bool, hMc]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  have hQ := lower_pair_trace H A hstable e he heA hrow hP
  have hseed := seed_missing e he G hdG F hno
    (mem_filter.mpr ⟨hP, hsub _⟩) (mem_filter.mpr ⟨hQ, hsub _⟩)
    (mem_filter.mpr ⟨hR, union_subset (subset_union_left) (hsub _)⟩)
  intro hT
  exact hseed (mem_filter.mpr ⟨hT, hsub _⟩)

end Submissions.Erdos1020MatchingRankThreeBC.Main

namespace Submissions.Erdos1020MatchingRankThreeBCMajorants.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeBC.Main

/-- The nine grid triples above the BC seed, with the middle column fixed at c2. -/
def majorant (p : Fin 3 × Fin 3) : Finset (Fin 3 × Fin 3) :=
  {(0, p.1), (1, 2), (2, p.2)}

theorem majorant_injective : Function.Injective majorant := by decide

theorem majorant_card (p : Fin 3 × Fin 3) : (majorant p).card = 3 := by
  simp [majorant]

theorem majorant_meets (p : Fin 3 × Fin 3) (i : Fin 3) :
    ∃ a : Fin 3, (i, a) ∈ majorant p := by
  have h : ∀ (p : Fin 3 × Fin 3) (i : Fin 3), ∃ a : Fin 3, (i, a) ∈ majorant p := by decide
  exact h p i

theorem nine_card {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) :
    (univ.image (fun p => (majorant p).image e)).card = 9 := by
  have hi : Function.Injective (fun p => (majorant p).image e) :=
    (image_injective he).comp majorant_injective
  rw [card_image_of_injective _ hi, card_univ, Fintype.card_prod,
    Fintype.card_fin]

/-- An actual trace on any one of the nine triples lowers to the missing seed.
Only the first and third columns move; all equality cases are retained. -/
theorem majorant_missing_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hseed : seed.image e ∉ H.image (fun S => S ∩ A))
    (p : Fin 3 × Fin 3) : (majorant p).image e ∉ H.image (fun S => S ∩ A) := by
  intro hP
  have hne (u v : Fin 3 × Fin 3) (h : u ≠ v) : e u ≠ e v := fun h' => h (he h')
  have hfirst : ({e (0, 0), e (1, 2), e (2, p.2)} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) := by
    by_cases hp : p.1 = 0
    · simpa [majorant, hp] using hP
    · have hlt : (0 : Fin 3) < p.1 := by omega
      have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable ((majorant p).image e) hP (e (0, 0)) (e (0, p.1)) (heA _)
        (hrow 0 hlt) (by simp [majorant])
        (by simp [majorant, hne (0, 0) (0, p.1) (by simp [Ne.symm hp]),
          hne (0, 0) (1, 2) (by decide), hne (0, 0) (2, p.2) (by simp)])
      simpa [majorant, hne (0, p.1) (1, 2) (by simp),
        hne (0, p.1) (2, p.2) (by simp)] using h
  by_cases hp : p.2 = 0
  · apply hseed
    simpa [seed, hp] using hfirst
  · have hlt : (0 : Fin 3) < p.2 := by omega
    have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable {e (0, 0), e (1, 2), e (2, p.2)} hfirst (e (2, 0)) (e (2, p.2)) (heA _)
      (hrow 2 hlt) (by simp)
      (by simp [hne (2, 0) (0, 0) (by decide), hne (2, 0) (1, 2) (by decide),
        hne (2, 0) (2, p.2) (by simp [Ne.symm hp])])
    have hlast : insert (e (2, 0)) ({e (0, 0), e (1, 2)} : Finset (Fin n)) ∈
        H.image (fun S => S ∩ A) := by
      simpa only [erase_insert_of_ne (hne (0, 0) (2, p.2) (by simp)),
        erase_insert_of_ne (hne (1, 2) (2, p.2) (by simp)), erase_singleton, Finset.insert_empty] using h
    have heq : insert (e (2, 0)) ({e (0, 0), e (1, 2)} : Finset (Fin n)) = seed.image e := by
      simp only [seed, image_insert, image_singleton]
      rw [insert_comm (e (2, 0)) (e (0, 0)), pair_comm (e (2, 0)) (e (1, 2))]
    exact hseed (heq ▸ hlast)

/-- Nine distinct absent grid triples are nine actual missing width-three
triples in the selected block region, with no weighted conclusion assumed. -/
theorem nine_missing_width_three {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (F : Finset (Finset α))
    (hmissing : ∀ p, (majorant p).image e ∉ F) :
    9 ≤ (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image j)).powersetCard 3
      \ F).filter (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 3)).card := by
  classical
  have hsub : univ.image (fun p => (majorant p).image e) ⊆
      (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image j)).powersetCard 3
      \ F).filter (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 3)) := by
    intro S hS
    obtain ⟨p, _, rfl⟩ := mem_image.mp hS
    have hsupport : Submissions.Erdos1020MatchingBlockSupport.Main.support B ((majorant p).image e) =
        univ.image j := by
      ext i
      constructor
      · intro hi
        obtain ⟨x, hx⟩ := (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ i).mp hi
        obtain ⟨⟨a, b⟩, _, hax⟩ := mem_image.mp (mem_inter.mp hx).1
        have hei : e (a, b) ∈ B i := hax.symm ▸ (mem_inter.mp hx).2
        have hji : j a = i := by
          by_contra hne
          exact disjoint_left.mp (hB hne) (heB a b) hei
        exact mem_image.mpr ⟨a, mem_univ _, hji⟩
      · intro hi
        obtain ⟨a, _, rfl⟩ := mem_image.mp hi
        obtain ⟨b, hb⟩ := majorant_meets p a
        exact (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ _).mpr
          ⟨e (a, b), mem_inter.mpr ⟨mem_image.mpr ⟨(a, b), hb, rfl⟩, heB a b⟩⟩
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, hmissing p⟩, ?_⟩
    · intro x hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    · rw [card_image_of_injective _ he, majorant_card]
    · rw [hsupport, card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have h := card_le_card hsub
  rwa [nine_card e he] at h

/-- The actual BC subcase has at least nine missing wide triples. All structural
premises come from the original family, its three selected blocks and the hub trace. -/
theorem actual_nine_missing {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A))
    (hR : G ∪ hub.image e ∈ H.image (fun S => S ∩ A)) :
    9 ≤ (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image j)).powersetCard 3
      \ H.image (fun S => S ∩ A)).filter
        (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 3)).card := by
  have hseed := actual_seed_missing H A hH hA hcut hstable hfree G B hBH hBA hBd hGB
    (univ.image j) (by rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin])
    j (fun i => mem_image.mpr ⟨i, mem_univ _, rfl⟩) e he heB hrow hP hR
  apply nine_missing_width_three G B hBd j hj e he heB (H.image (fun S => S ∩ A))
  exact majorant_missing_trace H A hstable e he (fun p => hBA _ (heB p.1 p.2)) hrow hseed

end Submissions.Erdos1020MatchingRankThreeBCMajorants.Main

namespace Submissions.Erdos1020MatchingRankThreeBCPairs.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeBC.Main
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- All 27 grid pairs using two different columns. -/
def widePairs : Finset (Finset (Fin 3 × Fin 3)) :=
  univ.powersetCard 2 |>.filter (fun P => (P.image Prod.fst).card = 2)

/-- The nine column-1/column-3 pairs and the two three-pair fans at c2. -/
def forbiddenPairs : Finset (Finset (Fin 3 × Fin 3)) :=
  (univ.image (fun p : Fin 3 × Fin 3 => ({(0, p.1), (2, p.2)} : Finset (Fin 3 × Fin 3))) ∪
    univ.image (fun a : Fin 3 => ({(0, a), (1, 2)} : Finset (Fin 3 × Fin 3)))) ∪
    univ.image (fun b : Fin 3 => ({(1, 2), (2, b)} : Finset (Fin 3 × Fin 3)))

theorem widePairs_card : widePairs.card = 27 := by decide

theorem forbiddenPairs_card : forbiddenPairs.card = 15 := by decide

theorem forbiddenPairs_subset : forbiddenPairs ⊆ widePairs := by decide

theorem remainingPairs_card : (widePairs \ forbiddenPairs).card = 12 := by
  rw [card_sdiff_of_subset forbiddenPairs_subset, widePairs_card, forbiddenPairs_card]

/-- Lower two actual trace vertices within distinct grid columns, retaining
coordinate equality cases and all fresh-vertex guards. -/
theorem lower_grid_pair_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (i j : Fin 3) (hij : i ≠ j) (a a' b b' : Fin 3) (ha : a ≤ a') (hb : b ≤ b')
    (hP : ({e (i, a'), e (j, b')} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A)) :
    ({e (i, a), e (j, b)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) := by
  have hne (p q : Fin 3 × Fin 3) (h : p ≠ q) : e p ≠ e q := fun h' => h (he h')
  have hfirst : ({e (i, a), e (j, b')} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) := by
    rcases ha.eq_or_lt with ha | ha
    · simpa only [ha] using hP
    · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable {e (i, a'), e (j, b')} hP (e (i, a)) (e (i, a')) (heA _)
        (hrow i ha) (by simp)
        (by simp [hne (i, a) (i, a') (by simp [ha.ne]), hne (i, a) (j, b') (by simp [hij])])
      simpa [hne (i, a') (j, b') (by simp [hij])] using h
  rcases hb.eq_or_lt with hb | hb
  · simpa only [hb] using hfirst
  · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable {e (i, a), e (j, b')} hfirst (e (j, b)) (e (j, b')) (heA _)
      (hrow j hb) (by simp)
      (by simp [hne (j, b) (i, a) (by simp [Ne.symm hij]), hne (j, b) (j, b') (by simp [hb.ne])])
    simpa [hne (j, b') (i, a) (by simp [Ne.symm hij]), pair_comm] using h

/-- Every subtrace of a missing head triple is absent in a cardinal-maximal
family: trace completion would otherwise put that triple in H. -/
theorem seed_subpair_missing {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hmax : ∀ K : Finset (Finset (Fin n)), (∀ S ∈ K, S.card = 3) →
      (¬ ∃ L : Finset (Finset (Fin n)), L ⊆ K ∧ L.card = s + 1 ∧
        ∀ S ∈ L, ∀ T ∈ L, S ≠ T → Disjoint S T) → K.card ≤ H.card)
    (hA : A.card + 1 = 3 * (s + 1)) (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e) (heA : ∀ p, e p ∈ A)
    (hseed : seed.image e ∉ H.image (fun S => S ∩ A))
    (P : Finset (Fin 3 × Fin 3)) (hP : P ⊆ seed) :
    P.image e ∉ H.image (fun S => S ∩ A) := by
  intro htrace
  obtain ⟨f, hf, hfA⟩ := mem_image.mp htrace
  have hSc : (seed.image e).card = 3 := by
    rw [card_image_of_injective _ he]
    decide
  have hSA : seed.image e ⊆ A := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := mem_image.mp hx
    exact heA p
  have hSH := Submissions.Erdos1020MatchingTraceCompletion.Main.mem_of_trace_subset
    (by decide) H A hH hfree hmax hA hcut hstable (seed.image e) hSc
    ⟨f, hf, by rw [hfA]; exact image_subset_image hP⟩
  exact hseed (mem_image.mpr ⟨seed.image e, hSH, inter_eq_left.mpr hSA⟩)

/-- The three missing seed pairs force the displayed 9+3+3 grid pairs to be
absent, using only within-column lowering of actual traces. -/
theorem forbidden_missing {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (h02 : ({e (0, 0), e (2, 0)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (h01 : ({e (0, 0), e (1, 2)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (h12 : ({e (1, 2), e (2, 0)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A)) :
    ∀ P ∈ forbiddenPairs, P.image e ∉ H.image (fun S => S ∩ A) := by
  intro P hP hmem
  rcases mem_union.mp hP with hP | hP
  · rcases mem_union.mp hP with hP | hP
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hP
      apply h02
      exact lower_grid_pair_trace H A hstable e he heA hrow 0 2 (by decide)
        0 p.1 0 p.2 (by omega) (by omega) (by simpa using hmem)
    · obtain ⟨a, _, rfl⟩ := mem_image.mp hP
      apply h01
      exact lower_grid_pair_trace H A hstable e he heA hrow 0 1 (by decide)
        0 a 2 2 (by omega) le_rfl (by simpa using hmem)
  · obtain ⟨b, _, rfl⟩ := mem_image.mp hP
    apply h12
    exact lower_grid_pair_trace H A hstable e he heA hrow 1 2 (by decide)
      2 2 0 b le_rfl (by omega) (by simpa using hmem)

/-- The support of any labeled grid subset is exactly the image of its used columns. -/
theorem support_grid_image {α : Type*} [DecidableEq α] {s : ℕ}
    (B : Fin s → Finset α) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (e : Fin 3 × Fin 3 → α)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (P : Finset (Fin 3 × Fin 3)) :
    support B (P.image e) = (P.image Prod.fst).image j := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx⟩ := (mem_support B _ i).mp hi
    obtain ⟨⟨a, b⟩, hab, heq⟩ := mem_image.mp (mem_inter.mp hx).1
    have hei : e (a, b) ∈ B i := heq.symm ▸ (mem_inter.mp hx).2
    have hji : j a = i := by
      by_contra hne
      exact disjoint_left.mp (hB hne) (heB a b) hei
    exact mem_image.mpr ⟨a, mem_image.mpr ⟨(a, b), hab, rfl⟩, hji⟩
  · intro hi
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hi
    obtain ⟨⟨c, b⟩, hcb, hca⟩ := mem_image.mp ha
    change c = a at hca
    subst c
    exact (mem_support B _ _).mpr
      ⟨e (a, b), mem_inter.mpr ⟨mem_image.mpr ⟨(a, b), hcb, rfl⟩, heB a b⟩⟩

/-- An exact finite transfer to the actual local width-two pair filter. The
full grid representation of each selected block is an explicit premise. -/
theorem width_two_le_twelve {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hBe : ∀ i, B (j i) = univ.image (fun a => e (i, a)))
    (F : Finset (Finset α)) (hmissing : ∀ P ∈ forbiddenPairs, P.image e ∉ F) :
    (F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2)).card ≤ 12 := by
  classical
  have hsub : F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2) ⊆ (widePairs \ forbiddenPairs).image (fun P => P.image e) := by
    intro S hS
    obtain ⟨hSF, hSU, hSc, hSw⟩ := mem_filter.mp hS
    have hSall : S ⊆ G ∪ univ.biUnion B := hSU.trans
      (union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ _)))
    have hSG := (Submissions.Erdos1020MatchingSupportTransversal.Main.transversal_of_support_card_eq
      G B hB hGB S hSall (by omega)).1
    have hSgrid : S ⊆ univ.image e := by
      intro x hx
      rcases mem_union.mp (hSU hx) with hxG | hxB
      · exact (disjoint_left.mp hSG hx hxG).elim
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxB
        obtain ⟨a, _, rfl⟩ := mem_image.mp hi
        rw [hBe a] at hxi
        obtain ⟨b, _, rfl⟩ := mem_image.mp hxi
        exact mem_image.mpr ⟨(a, b), mem_univ _, rfl⟩
    obtain ⟨P, hPe⟩ := subset_univ_image_iff.mp hSgrid
    have hPc : P.card = 2 := by
      have h := congrArg Finset.card hPe
      rw [card_image_of_injective _ he, hSc] at h
      exact h
    have hPw : (P.image Prod.fst).card = 2 := by
      have h := support_grid_image B hB j e heB P
      rw [hPe] at h
      have hc := congrArg Finset.card h
      rw [hSw, card_image_of_injective _ hj] at hc
      exact hc.symm
    have hwide : P ∈ widePairs := mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨subset_univ _, hPc⟩, hPw⟩
    have hforbid : P ∉ forbiddenPairs := by
      intro hP
      exact hmissing P hP (hPe.symm ▸ hSF)
    exact mem_image.mpr ⟨P, mem_sdiff.mpr ⟨hwide, hforbid⟩, hPe⟩
  calc
    _ ≤ ((widePairs \ forbiddenPairs).image (fun P => P.image e)).card := card_le_card hsub
    _ ≤ (widePairs \ forbiddenPairs).card := card_image_le
    _ = 12 := remainingPairs_card

/-- The actual BC subcase has at most twelve wide pairs. Cardinal maximality
is retained exactly where the missing seed triple excludes its subpairs. -/
theorem actual_width_two_le_twelve {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hmax : ∀ K : Finset (Finset (Fin n)), (∀ S ∈ K, S.card = 3) →
      (¬ ∃ L : Finset (Finset (Fin n)), L ⊆ K ∧ L.card = s + 1 ∧
        ∀ S ∈ L, ∀ T ∈ L, S ≠ T → Disjoint S T) → K.card ≤ H.card)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A))
    (hR : G ∪ hub.image e ∈ H.image (fun S => S ∩ A)) :
    ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region G B (univ.image j) ∧
      S.card = 2 ∧ (support B S).card = 2)).card ≤ 12 := by
  have heA (p : Fin 3 × Fin 3) : e p ∈ A := hBA _ (heB p.1 p.2)
  have hseed := actual_seed_missing H A hH hA hcut hstable hfree G B hBH hBA hBd hGB
    (univ.image j) (by rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin])
    j (fun i => mem_image.mpr ⟨i, mem_univ _, rfl⟩) e he heB hrow hP hR
  have h02 := seed_subpair_missing H A hH hfree hmax hA hcut hstable e he heA hseed
    {(0, 0), (2, 0)} (by decide)
  have h01 := seed_subpair_missing H A hH hfree hmax hA hcut hstable e he heA hseed
    {(0, 0), (1, 2)} (by decide)
  have h12 := seed_subpair_missing H A hH hfree hmax hA hcut hstable e he heA hseed
    {(1, 2), (2, 0)} (by decide)
  have hmissing := forbidden_missing H A hstable e he heA hrow
    (by simpa using h02) (by simpa using h01) (by simpa using h12)
  have hBe (i : Fin 3) : B (j i) = univ.image (fun a => e (i, a)) := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      exact heB i a
    · have hi : Function.Injective (fun a => e (i, a)) :=
        fun a b h => congrArg Prod.snd (he h)
      rw [hH _ (hBH _), card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  exact width_two_le_twelve G B hBd hGB j hj e he heB hBe (H.image (fun S => S ∩ A)) hmissing

end Submissions.Erdos1020MatchingRankThreeBCPairs.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseNumeric.Main

/-- The explicit BC counts discharge the local weighted comparison. All
combinatorial bounds remain visible premises of this arithmetic helper. -/
theorem bc_weighted_comparison {s N p1 p2 d1 d2 d3 : ℕ}
    (hs : 14 ≤ s) (hN : 2 * N ≤ s + 2)
    (hp1 : p1 ≤ 9) (hp2 : p2 ≤ 12) (hd3 : 9 ≤ d3) :
    N * ((s - 1) * p2 + 2 * p1) ≤
      (s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1 := by
  have hs1 : s - 1 + 1 = s := by omega
  have hs2 : s - 2 + 2 = s := by omega
  have hcount : (s - 1) * p2 + 2 * p1 ≤ 12 * (s - 1) + 18 := by
    nlinarith only [hp1, Nat.mul_le_mul_left (s - 1) hp2]
  have hbase : (s + 2) * (12 * (s - 1) + 18) ≤ 18 * (s - 1) * (s - 2) := by
    have hss : 14 * s ≤ s * s := Nat.mul_le_mul_right s hs
    nlinarith only [hs1, hs2, hss]
  have hdeficit := Nat.mul_le_mul_left ((s - 1) * (s - 2)) hd3
  have htwice : 2 * (N * ((s - 1) * p2 + 2 * p1)) ≤
      2 * ((s - 1) * (s - 2) * d3) := by
    calc
      _ ≤ 2 * (N * (12 * (s - 1) + 18)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left N hcount)
      _ = (2 * N) * (12 * (s - 1) + 18) := by ring
      _ ≤ (s + 2) * (12 * (s - 1) + 18) := Nat.mul_le_mul_right _ hN
      _ ≤ 18 * (s - 1) * (s - 2) := hbase
      _ ≤ 2 * ((s - 1) * (s - 2) * d3) := by nlinarith only [hdeficit]
  omega


/-- The complementary-cover case uses its exact narrow-to-medium count. -/
theorem case_one_weighted_comparison {s N p1 p2 d1 d2 d3 : ℕ}
    (hs : 3 ≤ s) (hN : 2 * N ≤ s + 2)
    (hp2 : p2 = 0) (hmedium : 3 * p1 ≤ d2) (hnarrow : p1 ≤ d1) :
    N * ((s - 1) * p2 + 2 * p1) ≤
      (s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1 := by
  subst p2
  have hs1 : s - 1 + 1 = s := by omega
  have hscaled := Nat.mul_le_mul_right p1 hN
  have hm := Nat.mul_le_mul_left (s - 1) hmedium
  have hroom : (s + 2) * p1 ≤ (s - 1) * (3 * p1) + 2 * p1 := by
    have hcoeff : s + 2 ≤ 3 * (s - 1) + 2 := by omega
    nlinarith only [Nat.mul_le_mul_right p1 hcoeff]
  have hbound : N * (2 * p1) ≤ (s - 1) * d2 + 2 * d1 := by
    nlinarith only [hscaled, hm, hroom, hnarrow]
  simp only [Nat.mul_zero, Nat.zero_add]
  omega

end Submissions.Erdos1020MatchingRankThreeCaseNumeric.Main

namespace Submissions.Erdos1020MatchingRankThreeBCComparison.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeBC.Main

/-- The literal local comparison (A) in the actual BC subcase. Every count is
obtained from the original family; no local comparison or numerical count is a premise.
The parameter N is explicit for the later substitution N=n-(3*s+2). -/
theorem actual_weighted_comparison {n s N : ℕ}
    (hs : 14 ≤ s) (hN : 2 * N ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hmax : ∀ K : Finset (Finset (Fin n)), (∀ S ∈ K, S.card = 3) →
      (¬ ∃ L : Finset (Finset (Fin n)), L ⊆ K ∧ L.card = s + 1 ∧
        ∀ S ∈ L, ∀ T ∈ L, S ≠ T → Disjoint S T) → K.card ≤ H.card)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A))
    (hR : {v, d} ∪ hub.image e ∈ H.image (fun S => S ∩ A)) :
    N * ((s - 1) *
        ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
          S.card = 2 ∧ (support B S).card = 2)).card +
      2 * ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
        S.card = 2 ∧ (support B S).card = 1)).card) ≤
      (s - 1) * (s - 2) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 3)).card +
      (s - 1) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 2)).card +
      2 * (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 1)).card := by
  have hMc : (univ.image j).card = 3 := by
    rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have hp1 := (Submissions.Erdos1020MatchingRankThreeWidthOne.Main.actual_width_one_bounds
    H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB
    (univ.image j) hMc).2
  have hp2 := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.actual_width_two_le_twelve
    H A hH hA hcut hstable hfree hmax {v, d} B hBH hBA hBd hGB j hj e he heB hrow hP hR
  have hd3 := Submissions.Erdos1020MatchingRankThreeBCMajorants.Main.actual_nine_missing
    H A hH hA hcut hstable hfree {v, d} B hBH hBA hBd hGB j hj e he heB hrow hP hR
  exact Submissions.Erdos1020MatchingRankThreeCaseNumeric.Main.bc_weighted_comparison
    hs hN hp1 hp2 hd3

end Submissions.Erdos1020MatchingRankThreeBCComparison.Main

namespace Submissions.Erdos1020MatchingRankThreeWideBase.Main

open Finset

/-- One vertex from each of the three labeled pairs. -/
def transversal {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) (f : Fin 3 → Bool) : Finset α :=
  univ.image (fun i => e (i, f i))

/-- The eight candidate triples; injectivity of the labeling is required for counting them. -/
def transversals {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) : Finset (Finset α) :=
  univ.image (transversal e)

theorem transversal_injective {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) (he : Function.Injective e) :
    Function.Injective (transversal e) := by
  classical
  intro f g hfg
  funext i
  have hm : e (i, f i) ∈ transversal e g :=
    hfg ▸ mem_image.mpr ⟨i, mem_univ i, rfl⟩
  obtain ⟨j, _, hji⟩ := mem_image.mp hm
  have hpair := he hji
  have hj : j = i := congrArg Prod.fst hpair
  subst j
  exact (congrArg Prod.snd hpair).symm

theorem transversal_card {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) (he : Function.Injective e) (f : Fin 3 → Bool) :
    (transversal e f).card = 3 := by
  have hi : Function.Injective (fun i => e (i, f i)) :=
    fun i j h => congrArg Prod.fst (he h)
  rw [transversal, card_image_of_injective _ hi, card_univ, Fintype.card_fin]

theorem transversals_card {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) (he : Function.Injective e) :
    (transversals e).card = 8 := by
  rw [transversals, card_image_of_injective _ (transversal_injective e he),
    card_univ, Fintype.card_pi_const, Fintype.card_bool]
  decide

/-- Opposite Boolean choices cover exactly the six labeled vertices. -/
theorem transversal_union_opposite {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) (f : Fin 3 → Bool) :
    transversal e f ∪ transversal e (fun i => !(f i)) = univ.image e := by
  classical
  ext x
  constructor
  · intro hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨(i, f i), mem_univ _, rfl⟩
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨(i, !(f i)), mem_univ _, rfl⟩
  · intro hx
    obtain ⟨⟨i, b⟩, _, rfl⟩ := mem_image.mp hx
    have hb : b = f i ∨ b = !(f i) := by
      cases b <;> cases h : f i <;> simp
    rcases hb with hb | hb
    · exact mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, by rw [hb]⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, by rw [hb]⟩)

/-- The Case II complement count: if two members of F never cover the six
vertices, at least four of their eight binary transversals are missing from F. -/
theorem four_missing_of_no_union {α : Type*} [DecidableEq α]
    (e : Fin 3 × Bool → α) (he : Function.Injective e)
    (F : Finset (Finset α))
    (hno : ∀ S ∈ F, ∀ T ∈ F, S ∪ T ≠ univ.image e) :
    4 ≤ (transversals e \ F).card := by
  classical
  let P : Finset (Fin 3 → Bool) := univ.filter (fun f => transversal e f ∈ F)
  let Q : Finset (Fin 3 → Bool) := univ.filter (fun f => transversal e f ∉ F)
  let opposite : (Fin 3 → Bool) → (Fin 3 → Bool) := fun f i => !(f i)
  have hop : Function.Injective opposite := by
    intro f g hfg
    funext i
    have h := congrFun hfg i
    change (!(f i)) = (!(g i)) at h
    cases hf : f i <;> cases hg : g i <;> simp_all
  have hsub : P.image opposite ⊆ Q := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hg
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro hother
    exact hno _ (mem_filter.mp hf).2 _ hother (transversal_union_opposite e f)
  have hPQ : P.card ≤ Q.card := by
    calc
      P.card = (P.image opposite).card := (card_image_of_injective _ hop).symm
      _ ≤ Q.card := card_le_card hsub
  have hsum : P.card + Q.card = 8 := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin 3 → Bool)))
      (fun f => transversal e f ∈ F)
    have hpow : (2 : ℕ) ^ 3 = 8 := by decide
    simpa only [P, Q, card_univ, Fintype.card_pi_const, Fintype.card_bool, hpow] using h
  have hmissing : Q.image (transversal e) = transversals e \ F := by
    ext S
    constructor
    · intro hS
      obtain ⟨f, hf, rfl⟩ := mem_image.mp hS
      exact mem_sdiff.mpr ⟨mem_image.mpr ⟨f, mem_univ _, rfl⟩, (mem_filter.mp hf).2⟩
    · intro hS
      obtain ⟨hS, hSF⟩ := mem_sdiff.mp hS
      obtain ⟨f, _, rfl⟩ := mem_image.mp hS
      exact mem_image.mpr ⟨f, mem_filter.mpr ⟨mem_univ _, hSF⟩, rfl⟩
  have hcard : (transversals e \ F).card = Q.card := by
    rw [← hmissing, card_image_of_injective _ (transversal_injective e he)]
  omega

/-- The complement count transfers to the actual width-three missing-triple
filter on the selected block region. The no-union case premise remains explicit. -/
theorem four_missing_width_three {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Bool → α) (he : Function.Injective e)
    (heB : ∀ i b, e (i, b) ∈ B (j i)) (F : Finset (Finset α))
    (hno : ∀ S ∈ F, ∀ T ∈ F, S ∪ T ≠ univ.image e) :
    4 ≤ (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image j)).powersetCard 3
      \ F).filter (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 3)).card := by
  classical
  have hsub : transversals e \ F ⊆
      (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image j)).powersetCard 3
      \ F).filter (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 3)) := by
    intro S hS
    obtain ⟨hS, hSF⟩ := mem_sdiff.mp hS
    obtain ⟨f, _, rfl⟩ := mem_image.mp hS
    have hsupport : Submissions.Erdos1020MatchingBlockSupport.Main.support B (transversal e f) =
        univ.image j := by
      ext i
      constructor
      · intro hi
        obtain ⟨x, hx⟩ := (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ i).mp hi
        obtain ⟨a, _, hax⟩ := mem_image.mp (mem_inter.mp hx).1
        have hei : e (a, f a) ∈ B i := hax.symm ▸ (mem_inter.mp hx).2
        have hji : j a = i := by
          by_contra hne
          exact disjoint_left.mp (hB hne) (heB a (f a)) hei
        exact mem_image.mpr ⟨a, mem_univ _, hji⟩
      · intro hi
        obtain ⟨a, _, rfl⟩ := mem_image.mp hi
        exact (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ _).mpr
          ⟨e (a, f a), mem_inter.mpr ⟨mem_image.mpr ⟨a, mem_univ _, rfl⟩, heB a (f a)⟩⟩
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_, transversal_card e he f⟩, hSF⟩, ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i (f i)⟩)
    · rw [hsupport, card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  exact (four_missing_of_no_union e he F hno).trans (card_le_card hsub)

end Submissions.Erdos1020MatchingRankThreeWideBase.Main

namespace Submissions.Erdos1020MatchingRankThreeActiveWide.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeWideBase.Main
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- The bottom vertex in column i and the top vertices in the other columns. -/
def bottomSeed (i : Fin 3) : Finset (Fin 3 × Fin 3) :=
  univ.image (fun j => (j, if j = i then 0 else 2))

def upperBoard (p : Fin 3 × Bool) : Fin 3 × Fin 3 :=
  (p.1, if p.2 then 2 else 1)

theorem bottomSeed_injective : Function.Injective bottomSeed := by decide

theorem bottomSeed_card (i : Fin 3) : (bottomSeed i).card = 3 := by
  have h : ∀ i : Fin 3, (bottomSeed i).card = 3 := by decide
  exact h i

theorem bottomSeed_columns (i : Fin 3) : (bottomSeed i).image Prod.fst = univ := by
  have h : ∀ i : Fin 3, (bottomSeed i).image Prod.fst = univ := by decide
  exact h i

theorem upperBoard_injective : Function.Injective upperBoard := by decide

theorem bottomSeed_not_upper (i : Fin 3) : bottomSeed i ∉ transversals upperBoard := by
  have h : ∀ i : Fin 3, bottomSeed i ∉ transversals upperBoard := by decide
  exact h i

private theorem upper_transversal_image {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (f : Fin 3 → Bool) :
    transversal (e ∘ upperBoard) f = (transversal upperBoard f).image e := by
  simp only [transversal, image_image, Function.comp_def]

/-- Each absent bottom seed adds a distinct triple outside the eight upper
transversals. The Case II complement argument supplies four missing upper ones. -/
theorem four_plus_missing_width_three {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (F : Finset (Finset α))
    (hno : ∀ S ∈ F, ∀ T ∈ F, S ∪ T ≠ univ.image (e ∘ upperBoard))
    (I : Finset (Fin 3)) (hmissing : ∀ i ∈ I, (bottomSeed i).image e ∉ F) :
    4 + I.card ≤ (((region G B (univ.image j)).powersetCard 3 \ F).filter
      (fun S => (support B S).card = 3)).card := by
  classical
  let D := ((region G B (univ.image j)).powersetCard 3 \ F).filter
    (fun S => (support B S).card = 3)
  let C := transversals (e ∘ upperBoard) \ F
  let E := I.image (fun i => (bottomSeed i).image e)
  have hC : 4 ≤ C.card := four_missing_of_no_union _
    (he.comp upperBoard_injective) F hno
  have hE : E.card = I.card := card_image_of_injective _
    ((image_injective he).comp bottomSeed_injective)
  have hgrid (P : Finset (Fin 3 × Fin 3)) : P.image e ⊆ region G B (univ.image j) := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hES : E ⊆ D := by
    intro S hS
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hS
    have hsup := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image
      B hB j e heB (bottomSeed i)
    rw [bottomSeed_columns] at hsup
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr
      ⟨hgrid _, ?_⟩, hmissing i hi⟩, ?_⟩
    · rw [card_image_of_injective _ he, bottomSeed_card]
    · rw [hsup, card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have hCS : C ⊆ D := by
    intro S hS
    obtain ⟨hS, hSF⟩ := mem_sdiff.mp hS
    obtain ⟨f, _, rfl⟩ := mem_image.mp hS
    have hcols : (transversal upperBoard f).image Prod.fst = univ := by
      have h : ∀ f : Fin 3 → Bool, (transversal upperBoard f).image Prod.fst = univ := by decide
      exact h f
    have hsup := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image
      B hB j e heB (transversal upperBoard f)
    rw [hcols] at hsup
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_,
      transversal_card _ (he.comp upperBoard_injective) f⟩, hSF⟩, ?_⟩
    · rw [upper_transversal_image]
      exact hgrid _
    · rw [upper_transversal_image, hsup, card_image_of_injective _ hj,
        card_univ, Fintype.card_fin]
  have hCE : Disjoint C E := by
    apply disjoint_left.mpr
    intro S hSC hSE
    obtain ⟨i, _, rfl⟩ := mem_image.mp hSE
    obtain ⟨f, _, hf⟩ := mem_image.mp (mem_sdiff.mp hSC).1
    rw [upper_transversal_image] at hf
    have heq := image_injective he hf
    exact bottomSeed_not_upper i (mem_image.mpr ⟨f, mem_univ _, heq⟩)
  have hcard := card_le_card (union_subset hCS hES)
  rw [card_union_of_disjoint hCE, hE] at hcard
  exact (Nat.add_le_add_right hC _).trans hcard

end Submissions.Erdos1020MatchingRankThreeActiveWide.Main

namespace Submissions.Erdos1020MatchingRankThreeActiveTrace.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeLowGraph.Main
open Submissions.Erdos1020MatchingRankThreeActiveWide.Main
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- A low set avoiding bottom i is disjoint from its bottom/top seed. -/
theorem low_disjoint_seed (Q : Finset (Fin 3 × Fin 3)) (hQ : Q ⊆ lowVertices)
    (i : Fin 3) (hav : (i, 0) ∉ Q) : Disjoint Q (bottomSeed i) := by
  apply disjoint_left.mpr
  intro p hpQ hpS
  obtain ⟨a, _, rfl⟩ := mem_image.mp hpS
  by_cases hai : a = i
  · exact hav (by simpa [hai] using hpQ)
  · have hh := (mem_filter.mp (hQ hpQ)).2
    simp only [if_neg hai] at hh
    exact (lt_irrefl (2 : Fin 3)) hh

/-- Two disjoint low pairs avoiding a bottom leave a sixth low vertex for a
hub, so an indexed no-four-matching family cannot contain that bottom seed. -/
theorem active_seed_missing {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (P : Finset (Finset (Fin 3 × Fin 3))) (hP : P ⊆ lowPairs)
    (hPF : ∀ Q ∈ P, Q.image e ∈ F) (i : Fin 3) (hi : i ∈ active P) :
    (bottomSeed i).image e ∉ F := by
  classical
  obtain ⟨Q, hQP, R, hRP, hQR, hav⟩ := (mem_active P i).mp hi
  have hQ := (mem_powersetCard.mp (mem_filter.mp (hP hQP)).1)
  have hR := (mem_powersetCard.mp (mem_filter.mp (hP hRP)).1)
  have hc : (insert (i, 0) (Q ∪ R)).card = 5 := by
    rw [card_insert_of_notMem hav, card_union_of_disjoint hQR, hQ.2, hR.2]
  have hlow : lowVertices.card = 6 := by decide
  obtain ⟨x, hxlow, hx⟩ := exists_mem_notMem_of_card_lt_card (show
      (insert (i, 0) (Q ∪ R)).card < lowVertices.card by omega)
  have hxQR : x ∉ Q ∪ R := fun h => hx (mem_insert_of_mem h)
  have hxi : x ≠ (i, 0) := by
    intro h
    subst x
    exact hx (mem_insert_self _ _)
  have hQseed := low_disjoint_seed Q hQ.1 i (fun h => hav (mem_union_left _ h))
  have hRseed := low_disjoint_seed R hR.1 i (fun h => hav (mem_union_right _ h))
  have hxseed : Disjoint ({x} : Finset (Fin 3 × Fin 3)) (bottomSeed i) :=
    low_disjoint_seed {x} (singleton_subset_iff.mpr hxlow) i
      (by simpa only [mem_singleton] using Ne.symm hxi)
  have hd (X Y : Finset (Fin 3 × Fin 3)) (h : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr h
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  apply Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    (Q.image e) (R.image e) (G ∪ ({x} : Finset (Fin 3 × Fin 3)).image e)
    ((bottomSeed i).image e) (hPF Q hQP) (hPF R hRP) (by simpa using hhub x hxlow)
  · exact hd _ _ hQR
  · exact disjoint_union_right.mpr ⟨(hdG _).symm,
      hd _ _ (disjoint_singleton_right.mpr (fun h => hxQR (mem_union_left _ h)))⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm,
      hd _ _ (disjoint_singleton_right.mpr (fun h => hxQR (mem_union_right _ h)))⟩
  · exact hd _ _ hQseed
  · exact hd _ _ hRseed
  · exact disjoint_union_left.mpr ⟨hdG _, hd _ _ hxseed⟩

/-- Actual local matching exclusion supplies every active-bottom seed. The
six hub traces and the Case II no-cover alternative remain explicit. -/
theorem actual_four_plus_active {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ H.image (fun S => S ∩ A))
    (hcover : ∀ S ∈ H.image (fun S => S ∩ A), ∀ T ∈ H.image (fun S => S ∩ A),
      S ∪ T ≠ univ.image (e ∘ upperBoard))
    (P : Finset (Finset (Fin 3 × Fin 3))) (hP : P ⊆ lowPairs)
    (hPT : ∀ Q ∈ P, Q.image e ∈ H.image (fun S => S ∩ A)) :
    4 + (active P).card ≤
      (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 3)).card := by
  classical
  let U := region G B (univ.image j)
  let F := (H.image (fun S => S ∩ A)).filter (fun S => S ⊆ U)
  have hsub (X : Finset (Fin 3 × Fin 3)) : X.image e ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hdG : Disjoint G (univ.image e) := by
    apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (j i)) hxG (heB i a)
  have hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro f hf
    apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree G B hBH hBA hBd hGB (univ.image j)
      (by rw [Fintype.card_prod, Fintype.card_bool, card_image_of_injective _ hj,
        card_univ, Fintype.card_fin]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  apply four_plus_missing_width_three G B hBd j hj e he heB
    (H.image (fun S => S ∩ A)) hcover (active P)
  intro i hi hseed
  apply active_seed_missing e he G hdG F hno
    (fun x hx => mem_filter.mpr ⟨hhub x hx,
      union_subset subset_union_left (by simpa using hsub {x})⟩)
    P hP (fun Q hQ => mem_filter.mpr ⟨hPT Q hQ, hsub Q⟩) i hi
  exact mem_filter.mpr ⟨hseed, hsub _⟩

end Submissions.Erdos1020MatchingRankThreeActiveTrace.Main

namespace Submissions.Erdos1020MatchingRankThreeGridPairs.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeBCPairs.Main

/-- The finite board pairs whose images occur in the actual local family. -/
def presentPairs {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (F : Finset (Finset α)) : Finset (Finset (Fin 3 × Fin 3)) :=
  widePairs.filter (fun P => P.image e ∈ F)

/-- Every local width-two pair has a unique pair on the fully labeled board. -/
theorem local_pairs_eq_image {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hBe : ∀ i, B (j i) = univ.image (fun a => e (i, a))) (F : Finset (Finset α)) :
    F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2) = (presentPairs e F).image (fun P => P.image e) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨hSF, hSU, hSc, hSw⟩ := mem_filter.mp hS
    have hSall : S ⊆ G ∪ univ.biUnion B := hSU.trans
      (union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ _)))
    have hSG := (Submissions.Erdos1020MatchingSupportTransversal.Main.transversal_of_support_card_eq
      G B hB hGB S hSall (by omega)).1
    have hSgrid : S ⊆ univ.image e := by
      intro x hx
      rcases mem_union.mp (hSU hx) with hxG | hxB
      · exact (disjoint_left.mp hSG hx hxG).elim
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxB
        obtain ⟨a, _, rfl⟩ := mem_image.mp hi
        rw [hBe a] at hxi
        obtain ⟨b, _, rfl⟩ := mem_image.mp hxi
        exact mem_image.mpr ⟨(a, b), mem_univ _, rfl⟩
    obtain ⟨P, hPe⟩ := subset_univ_image_iff.mp hSgrid
    have hPc : P.card = 2 := by
      have h := congrArg Finset.card hPe
      rw [card_image_of_injective _ he, hSc] at h
      exact h
    have hPw : (P.image Prod.fst).card = 2 := by
      have h := support_grid_image B hB j e heB P
      rw [hPe] at h
      have hc := congrArg Finset.card h
      rw [hSw, card_image_of_injective _ hj] at hc
      exact hc.symm
    exact mem_image.mpr ⟨P, mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨subset_univ _, hPc⟩, hPw⟩, hPe.symm ▸ hSF⟩, hPe⟩
  · intro hS
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hS
    obtain ⟨hPW, hPF⟩ := mem_filter.mp hP
    obtain ⟨hPc, hPw⟩ := mem_filter.mp hPW
    refine mem_filter.mpr ⟨hPF, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    · rw [card_image_of_injective _ he]
      exact (mem_powersetCard.mp hPc).2
    · rw [support_grid_image B hB j e heB P, card_image_of_injective _ hj, hPw]

theorem local_pairs_card {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hBe : ∀ i, B (j i) = univ.image (fun a => e (i, a))) (F : Finset (Finset α)) :
    (F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2)).card = (presentPairs e F).card := by
  rw [local_pairs_eq_image G B hB hGB j hj e he heB hBe F,
    card_image_of_injective _ (image_injective he)]

/-- In the no-AC/no-BC branch every present wide pair is a low graph edge. -/
theorem presentPairs_subset_lowPairs {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (F : Finset (Finset α))
    (hnotop : ∀ i j : Fin 3, i ≠ j → ∀ a b : Fin 3, a = 2 ∨ b = 2 →
      ({e (i, a), e (j, b)} : Finset α) ∉ F) :
    presentPairs e F ⊆ Submissions.Erdos1020MatchingRankThreeLowGraph.Main.lowPairs := by
  intro P hP
  obtain ⟨hPW, hPF⟩ := mem_filter.mp hP
  obtain ⟨hPc, hPw⟩ := mem_filter.mp hPW
  have hcard := (mem_powersetCard.mp hPc).2
  apply (Submissions.Erdos1020MatchingRankThreeLowGraph.Main.mem_lowPairs P).mpr
  refine ⟨hcard, hPw, ?_⟩
  obtain ⟨⟨i, a⟩, ⟨j, b⟩, _, rfl⟩ := card_eq_two.mp hcard
  have hij : i ≠ j := by
    intro h
    simp [h] at hPw
  have htop : ¬ (a = 2 ∨ b = 2) := by
    intro h
    exact hnotop i j hij a b h (by simpa using hPF)
  have ha : a < 2 := by omega
  have hb : b < 2 := by omega
  intro p hp
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ha
  · exact hb

end Submissions.Erdos1020MatchingRankThreeGridPairs.Main

namespace Submissions.Erdos1020MatchingRankThreeACTwo.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- A bottom/top pair; columns need not be distinct for the seed obstruction. -/
def acPair (i j : Fin 3) : Finset (Fin 3 × Fin 3) := {(i, 0), (j, 2)}

/-- The triple excluded by two disjoint AC pairs on bottom columns zero and one. -/
def seed : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 1), (2, 0)}

/-- The twelve coordinate majorants of the seed. -/
def majorant (p : Fin 2 × Fin 2 × Fin 3) : Finset (Fin 3 × Fin 3) :=
  {(0, p.1.succ), (1, p.2.1.succ), (2, p.2.2)}

/-- The nine wide BC or CC pairs. -/
def barredBC : Finset (Finset (Fin 3 × Fin 3)) :=
  Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs.filter
    (fun P => (∀ p ∈ P, 1 ≤ p.2) ∧ ∃ p ∈ P, p.2 = 2)

theorem barredBC_card : barredBC.card = 9 := by decide

theorem remainingPairs_card :
    (Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs \ barredBC).card = 18 := by
  have hsub : barredBC ⊆
      Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs := filter_subset _ _
  rw [card_sdiff_of_subset hsub,
    Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs_card, barredBC_card]

theorem majorant_injective : Function.Injective majorant := by decide

theorem majorant_card (p : Fin 2 × Fin 2 × Fin 3) : (majorant p).card = 3 := by
  simp [majorant]

theorem majorant_columns (p : Fin 2 × Fin 2 × Fin 3) :
    (majorant p).image Prod.fst = univ := by
  have h : ∀ p : Fin 2 × Fin 2 × Fin 3, (majorant p).image Prod.fst = univ := by decide
  exact h p

theorem twelve_card {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) :
    (univ.image (fun p => (majorant p).image e)).card = 12 := by
  have hi : Function.Injective (fun p => (majorant p).image e) :=
    (image_injective he).comp majorant_injective
  rw [card_image_of_injective _ hi, card_univ, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- Two AC pairs with different top vertices and the third-middle hub exclude
the seed in any indexed no-four-matching family. -/
theorem seed_missing {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (p q : Fin 3) (hpq : p ≠ q)
    (hP : (acPair 0 p).image e ∈ F) (hQ : (acPair 1 q).image e ∈ F)
    (hR : G ∪ {e (2, 1)} ∈ F) : seed.image e ∉ F := by
  have hd (X Y : Finset (Fin 3 × Fin 3)) (h : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr h
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  have hPQ : Disjoint (acPair 0 p) (acPair 1 q) := by
    have h : ∀ p q : Fin 3, p ≠ q → Disjoint (acPair 0 p) (acPair 1 q) := by decide
    exact h p q hpq
  have hPZ : Disjoint (acPair 0 p) ({(2, 1)} : Finset (Fin 3 × Fin 3)) := by
    have h : ∀ p : Fin 3, Disjoint (acPair 0 p) ({(2, 1)} : Finset (Fin 3 × Fin 3)) := by decide
    exact h p
  have hQZ : Disjoint (acPair 1 q) ({(2, 1)} : Finset (Fin 3 × Fin 3)) := by
    have h : ∀ q : Fin 3, Disjoint (acPair 1 q) ({(2, 1)} : Finset (Fin 3 × Fin 3)) := by decide
    exact h q
  have hPT : Disjoint (acPair 0 p) seed := by
    have h : ∀ p : Fin 3, Disjoint (acPair 0 p) seed := by decide
    exact h p
  have hQT : Disjoint (acPair 1 q) seed := by
    have h : ∀ q : Fin 3, Disjoint (acPair 1 q) seed := by decide
    exact h q
  apply Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    ((acPair 0 p).image e) ((acPair 1 q).image e)
    (G ∪ ({(2, 1)} : Finset (Fin 3 × Fin 3)).image e) (seed.image e)
    hP hQ (by simpa using hR)
  · exact hd _ _ hPQ
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ hPZ⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ hQZ⟩
  · exact hd _ _ hPT
  · exact hd _ _ hQT
  · exact disjoint_union_left.mpr ⟨hdG _, hd _ _ (by decide)⟩

/-- Every coordinate majorant of the missing seed is absent from the actual
trace, using three within-column replacements and retaining equality cases. -/
theorem majorant_missing_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hseed : seed.image e ∉ H.image (fun S => S ∩ A))
    (p : Fin 2 × Fin 2 × Fin 3) : (majorant p).image e ∉ H.image (fun S => S ∩ A) := by
  intro hP
  have hne (u v : Fin 3 × Fin 3) (h : u ≠ v) : e u ≠ e v := fun h' => h (he h')
  have hfirst : ({e (0, 1), e (1, p.2.1.succ), e (2, p.2.2)} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) := by
    have hp : (1 : Fin 3) ≤ p.1.succ := by
      change 1 ≤ p.1.val + 1
      omega
    rcases hp.eq_or_lt with hp | hp
    · simpa [majorant, ← hp] using hP
    · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable ((majorant p).image e) hP (e (0, 1)) (e (0, p.1.succ)) (heA _)
        (hrow 0 hp) (by simp [majorant])
        (by simp [majorant, hne (0, 1) (0, p.1.succ) (by simp [hp.ne]),
          hne (0, 1) (1, p.2.1.succ) (by simp), hne (0, 1) (2, p.2.2) (by simp)])
      simpa [majorant, hne (0, p.1.succ) (1, p.2.1.succ) (by simp),
        hne (0, p.1.succ) (2, p.2.2) (by simp)] using h
  have hsecond : ({e (0, 1), e (1, 1), e (2, p.2.2)} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) := by
    have hp : (1 : Fin 3) ≤ p.2.1.succ := by
      change 1 ≤ p.2.1.val + 1
      omega
    rcases hp.eq_or_lt with hp | hp
    · simpa only [← hp] using hfirst
    · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable {e (0, 1), e (1, p.2.1.succ), e (2, p.2.2)} hfirst
        (e (1, 1)) (e (1, p.2.1.succ)) (heA _) (hrow 1 hp) (by simp)
        (by simp [hne (1, 1) (0, 1) (by decide),
          hne (1, 1) (1, p.2.1.succ) (by simp [hp.ne]),
          hne (1, 1) (2, p.2.2) (by simp)])
      have hm : insert (e (1, 1)) ({e (0, 1), e (2, p.2.2)} : Finset (Fin n)) ∈
          H.image (fun S => S ∩ A) := by
        simpa only [erase_insert_of_ne (hne (0, 1) (1, p.2.1.succ) (by simp)),
          erase_insert (show e (1, p.2.1.succ) ∉ ({e (2, p.2.2)} : Finset (Fin n)) from by
            simpa only [mem_singleton] using
              hne (1, p.2.1.succ) (2, p.2.2) (by simp))] using h
      rwa [insert_comm (e (1, 1)) (e (0, 1))] at hm
  by_cases hp : p.2.2 = 0
  · apply hseed
    simpa [seed, hp] using hsecond
  · have hlt : (0 : Fin 3) < p.2.2 := by omega
    have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable {e (0, 1), e (1, 1), e (2, p.2.2)} hsecond
      (e (2, 0)) (e (2, p.2.2)) (heA _) (hrow 2 hlt) (by simp)
      (by simp [hne (2, 0) (0, 1) (by decide), hne (2, 0) (1, 1) (by decide),
        hne (2, 0) (2, p.2.2) (by simp [Ne.symm hp])])
    have hlast : insert (e (2, 0)) ({e (0, 1), e (1, 1)} : Finset (Fin n)) ∈
        H.image (fun S => S ∩ A) := by
      simpa only [erase_insert_of_ne (hne (0, 1) (2, p.2.2) (by simp)),
        erase_insert_of_ne (hne (1, 1) (2, p.2.2) (by simp)),
        erase_singleton, Finset.insert_empty] using h
    have heq : insert (e (2, 0)) ({e (0, 1), e (1, 1)} : Finset (Fin n)) = seed.image e := by
      simp only [seed, image_insert, image_singleton]
      rw [insert_comm (e (2, 0)) (e (0, 1)), pair_comm (e (2, 0)) (e (1, 1))]
    exact hseed (heq ▸ hlast)

/-- The twelve absent labeled triples are twelve actual missing width-three
triples in the selected region. -/
theorem twelve_missing_width_three {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (F : Finset (Finset α))
    (hmissing : ∀ p, (majorant p).image e ∉ F) :
    12 ≤ (((region G B (univ.image j)).powersetCard 3 \ F).filter
      (fun S => (support B S).card = 3)).card := by
  classical
  have hsub : univ.image (fun p => (majorant p).image e) ⊆
      (((region G B (univ.image j)).powersetCard 3 \ F).filter
        (fun S => (support B S).card = 3)) := by
    intro S hS
    obtain ⟨p, _, rfl⟩ := mem_image.mp hS
    have hs := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image
      B hB j e heB (majorant p)
    rw [majorant_columns] at hs
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, hmissing p⟩, ?_⟩
    · intro x hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    · rw [card_image_of_injective _ he, majorant_card]
    · rw [hs, card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have h := card_le_card hsub
  rwa [twelve_card e he] at h

/-- Translate literal cross-column BC/CC absence to the nine-candidate filter. -/
theorem barredBC_missing {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (F : Finset (Finset α))
    (hno : ∀ i j : Fin 3, i ≠ j → ∀ a b : Fin 3,
      1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 → ({e (i, a), e (j, b)} : Finset α) ∉ F) :
    ∀ P ∈ barredBC, P.image e ∉ F := by
  intro P hP
  obtain ⟨hwide, hhi, htop⟩ := mem_filter.mp hP
  obtain ⟨hPc, hPw⟩ := mem_filter.mp hwide
  obtain ⟨⟨i, a⟩, ⟨j, b⟩, _, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hPc).2
  have hij : i ≠ j := by
    intro hij
    simp [hij] at hPw
  have ha : (1 : Fin 3) ≤ a := hhi (i, a) (by simp)
  have hb : (1 : Fin 3) ≤ b := hhi (j, b) (by simp)
  have ht : a = 2 ∨ b = 2 := by
    obtain ⟨p, hp, hpt⟩ := htop
    rcases mem_insert.mp hp with hp | hp
    · subst p
      exact Or.inl hpt
    · have hp' := mem_singleton.mp hp
      subst p
      exact Or.inr hpt
  simpa using hno i j hij a b ha hb ht

/-- Transfer the eighteen remaining grid candidates to actual local pairs.
This generic finite step assumes only the exact nine absences. -/
theorem width_two_le_eighteen {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hBe : ∀ i, B (j i) = univ.image (fun a => e (i, a)))
    (F : Finset (Finset α)) (hmissing : ∀ P ∈ barredBC, P.image e ∉ F) :
    (F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2)).card ≤ 18 := by
  classical
  let W := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs
  have hsub : F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2) ⊆ (W \ barredBC).image (fun P => P.image e) := by
    intro S hS
    obtain ⟨hSF, hSU, hSc, hSw⟩ := mem_filter.mp hS
    have hSall : S ⊆ G ∪ univ.biUnion B := hSU.trans
      (union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ _)))
    have hSG := (Submissions.Erdos1020MatchingSupportTransversal.Main.transversal_of_support_card_eq
      G B hB hGB S hSall (by omega)).1
    have hSgrid : S ⊆ univ.image e := by
      intro x hx
      rcases mem_union.mp (hSU hx) with hxG | hxB
      · exact (disjoint_left.mp hSG hx hxG).elim
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxB
        obtain ⟨a, _, rfl⟩ := mem_image.mp hi
        rw [hBe a] at hxi
        obtain ⟨b, _, rfl⟩ := mem_image.mp hxi
        exact mem_image.mpr ⟨(a, b), mem_univ _, rfl⟩
    obtain ⟨P, hPe⟩ := subset_univ_image_iff.mp hSgrid
    have hPc : P.card = 2 := by
      have h := congrArg Finset.card hPe
      rw [card_image_of_injective _ he, hSc] at h
      exact h
    have hPw : (P.image Prod.fst).card = 2 := by
      have h := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image B hB j e heB P
      rw [hPe] at h
      have hc := congrArg Finset.card h
      rw [hSw, card_image_of_injective _ hj] at hc
      exact hc.symm
    have hwide : P ∈ W := mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨subset_univ _, hPc⟩, hPw⟩
    have hforbid : P ∉ barredBC := by
      intro hP
      exact hmissing P hP (hPe.symm ▸ hSF)
    exact mem_image.mpr ⟨P, mem_sdiff.mpr ⟨hwide, hforbid⟩, hPe⟩
  calc
    _ ≤ ((W \ barredBC).image (fun P => P.image e)).card := card_le_card hsub
    _ ≤ (W \ barredBC).card := card_image_le
    _ = 18 := remainingPairs_card

/-- The actual Case II.2(i) counts. The third-middle hub is an explicit actual
trace premise supplied by minimum-gap completion upstream; no count or weighted
inequality is assumed. No maximality or ONE premise is needed by this theorem. -/
theorem actual_counts {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (p q : Fin 3) (hpq : p ≠ q)
    (hP : ({e (0, 0), e (p, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hQ : ({e (1, 0), e (q, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hR : G ∪ {e (2, 1)} ∈ H.image (fun S => S ∩ A)) :
    ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region G B (univ.image j) ∧
      S.card = 2 ∧ (support B S).card = 2)).card ≤ 18 ∧
      12 ≤ (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 3)).card := by
  classical
  let U := region G B (univ.image j)
  let F := (H.image (fun S => S ∩ A)).filter (fun S => S ⊆ U)
  have heA (p : Fin 3 × Fin 3) : e p ∈ A := hBA _ (heB p.1 p.2)
  have hsub (X : Finset (Fin 3 × Fin 3)) : X.image e ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hdG : Disjoint G (univ.image e) := by
    apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (j i)) hxG (heB i a)
  have hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro f hf
    apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree G B hBH hBA hBd hGB (univ.image j)
      (by rw [Fintype.card_prod, Fintype.card_bool, card_image_of_injective _ hj,
        card_univ, Fintype.card_fin]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  have hlocal : seed.image e ∉ F := seed_missing e he G hdG F hno p q hpq
    (mem_filter.mpr ⟨by simpa [acPair] using hP, hsub _⟩)
    (mem_filter.mpr ⟨by simpa [acPair] using hQ, hsub _⟩)
    (mem_filter.mpr ⟨hR, union_subset subset_union_left (by simpa using hsub {(2, 1)})⟩)
  have hseed : seed.image e ∉ H.image (fun S => S ∩ A) :=
    fun h => hlocal (mem_filter.mpr ⟨h, hsub _⟩)
  have hBe (i : Fin 3) : B (j i) = univ.image (fun a => e (i, a)) := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      exact heB i a
    · have hi : Function.Injective (fun a => e (i, a)) :=
        fun a b h => congrArg Prod.snd (he h)
      rw [hH _ (hBH _), card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  refine ⟨width_two_le_eighteen G B hBd hGB j hj e he heB hBe
    (H.image (fun S => S ∩ A)) (barredBC_missing e _ hbar), ?_⟩
  apply twelve_missing_width_three G B hBd j hj e he heB (H.image (fun S => S ∩ A))
  exact majorant_missing_trace H A hstable e he heA hrow hseed

end Submissions.Erdos1020MatchingRankThreeACTwo.Main

namespace Submissions.Erdos1020MatchingRankThreeACCommon.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- A full transversal in the three selected columns. -/
def triple (a b c : Fin 3) : Finset (Fin 3 × Fin 3) := {(0, a), (1, b), (2, c)}

/-- The union of the two four-element upper cones, with their two overlaps counted once. -/
def six : Finset (Finset (Fin 3 × Fin 3)) :=
  {triple 2 1 1, triple 2 1 2, triple 2 2 1, triple 2 2 2, triple 1 1 2, triple 1 2 2}

/-- The four AC pairs excluded by the exact common-top case assumption. -/
def otherAC : Finset (Finset (Fin 3 × Fin 3)) :=
  {{(0, 0), (2, 2)}, {(1, 0), (0, 2)}, {(1, 0), (2, 2)}, {(2, 0), (0, 2)}}

/-- The four low pairs excluded by matching and subsequent within-column lowering. -/
def lowFour : Finset (Finset (Fin 3 × Fin 3)) :=
  {{(0, 1), (1, 0)}, {(1, 0), (2, 1)}, {(0, 1), (1, 1)}, {(1, 1), (2, 1)}}

def forbidden : Finset (Finset (Fin 3 × Fin 3)) :=
  (Submissions.Erdos1020MatchingRankThreeACTwo.Main.barredBC ∪ otherAC) ∪ lowFour

theorem six_card : six.card = 6 := by decide

theorem six_properties (P : Finset (Fin 3 × Fin 3)) (hP : P ∈ six) :
    P.card = 3 ∧ P.image Prod.fst = univ := by
  simp only [six, mem_insert, mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem remaining_card :
    (Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs \ forbidden).card = 10 := by
  decide

/-- The reusable finite four-matching obstruction, with one actual gap hub. -/
theorem missing_grid_of_pairs {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (P Q : Finset (Fin 3 × Fin 3)) (i : Fin 3) (T : Finset (Fin 3 × Fin 3))
    (hP : P.image e ∈ F) (hQ : Q.image e ∈ F) (hR : G ∪ {e (i, 1)} ∈ F)
    (hPQ : Disjoint P Q) (hPR : Disjoint P {(i, 1)}) (hQR : Disjoint Q {(i, 1)})
    (hPT : Disjoint P T) (hQT : Disjoint Q T) (hRT : Disjoint {(i, 1)} T) :
    T.image e ∉ F := by
  have hd (X Y : Finset (Fin 3 × Fin 3)) (h : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr h
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  apply Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    (P.image e) (Q.image e) (G ∪ ({(i, 1)} : Finset (Fin 3 × Fin 3)).image e)
    (T.image e) hP hQ (by simpa using hR)
  · exact hd _ _ hPQ
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ hPR⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ hQR⟩
  · exact hd _ _ hPT
  · exact hd _ _ hQT
  · exact disjoint_union_left.mpr ⟨hdG _, hd _ _ hRT⟩

/-- Lower the three coordinates of an actual full-transversal trace.
Targets in distinct columns remain fresh; equality cases are retained. -/
theorem lower_grid_triple_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (a a' b b' c c' : Fin 3) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hP : (triple a' b' c').image e ∈ H.image (fun S => S ∩ A)) :
    (triple a b c).image e ∈ H.image (fun S => S ∩ A) := by
  have hne (u v : Fin 3 × Fin 3) (h : u ≠ v) : e u ≠ e v := fun h' => h (he h')
  have hfirst : ({e (0, a), e (1, b'), e (2, c')} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) := by
    rcases ha.eq_or_lt with ha | ha
    · simpa [triple, ha] using hP
    · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable ((triple a' b' c').image e) hP (e (0, a)) (e (0, a')) (heA _)
        (hrow 0 ha) (by simp [triple])
        (by simp [triple, hne (0, a) (0, a') (by simp [ha.ne]),
          hne (0, a) (1, b') (by simp), hne (0, a) (2, c') (by simp)])
      simpa [triple, hne (0, a') (1, b') (by simp),
        hne (0, a') (2, c') (by simp)] using h
  have hsecond : ({e (0, a), e (1, b), e (2, c')} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) := by
    rcases hb.eq_or_lt with hb | hb
    · simpa only [hb] using hfirst
    · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable {e (0, a), e (1, b'), e (2, c')} hfirst
        (e (1, b)) (e (1, b')) (heA _) (hrow 1 hb) (by simp)
        (by simp [hne (1, b) (0, a) (by simp), hne (1, b) (1, b') (by simp [hb.ne]),
          hne (1, b) (2, c') (by simp)])
      have hm : insert (e (1, b)) ({e (0, a), e (2, c')} : Finset (Fin n)) ∈
          H.image (fun S => S ∩ A) := by
        simpa only [erase_insert_of_ne (hne (0, a) (1, b') (by simp)),
          erase_insert (show e (1, b') ∉ ({e (2, c')} : Finset (Fin n)) from by
            simpa only [mem_singleton] using hne (1, b') (2, c') (by simp))] using h
      rwa [insert_comm (e (1, b)) (e (0, a))] at hm
  rcases hc.eq_or_lt with hc | hc
  · simpa [triple, hc] using hsecond
  · have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable {e (0, a), e (1, b), e (2, c')} hsecond
      (e (2, c)) (e (2, c')) (heA _) (hrow 2 hc) (by simp)
      (by simp [hne (2, c) (0, a) (by simp), hne (2, c) (1, b) (by simp),
        hne (2, c) (2, c') (by simp [hc.ne])])
    have hlast : insert (e (2, c)) ({e (0, a), e (1, b)} : Finset (Fin n)) ∈
        H.image (fun S => S ∩ A) := by
      simpa only [erase_insert_of_ne (hne (0, a) (2, c') (by simp)),
        erase_insert_of_ne (hne (1, b) (2, c') (by simp)),
        erase_singleton, Finset.insert_empty] using h
    simpa only [triple, image_insert, image_singleton,
      insert_comm (e (2, c)) (e (0, a)), pair_comm (e (2, c)) (e (1, b))] using hlast

/-- Six distinct upper triples follow from the two missing seeds. -/
theorem six_missing_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hleft : (triple 2 1 1).image e ∉ H.image (fun S => S ∩ A))
    (hright : (triple 1 1 2).image e ∉ H.image (fun S => S ∩ A)) :
    ∀ P ∈ six, P.image e ∉ H.image (fun S => S ∩ A) := by
  intro P hP hmem
  simp only [six, mem_insert, mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hleft hmem
  · exact hleft (lower_grid_triple_trace H A hstable e he heA hrow
      2 2 1 1 1 2 (by decide) (by decide) (by decide) hmem)
  · exact hleft (lower_grid_triple_trace H A hstable e he heA hrow
      2 2 1 2 1 1 (by decide) (by decide) (by decide) hmem)
  · exact hleft (lower_grid_triple_trace H A hstable e he heA hrow
      2 2 1 2 1 2 (by decide) (by decide) (by decide) hmem)
  · exact hright hmem
  · exact hright (lower_grid_triple_trace H A hstable e he heA hrow
      1 1 1 2 2 2 (by decide) (by decide) (by decide) hmem)

/-- Convert the six distinct absent grid triples into the literal actual count. -/
theorem six_missing_width_three {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (F : Finset (Finset α))
    (hmissing : ∀ P ∈ six, P.image e ∉ F) :
    6 ≤ (((region G B (univ.image j)).powersetCard 3 \ F).filter
      (fun S => (support B S).card = 3)).card := by
  classical
  have hsub : six.image (fun P => P.image e) ⊆
      (((region G B (univ.image j)).powersetCard 3 \ F).filter
        (fun S => (support B S).card = 3)) := by
    intro S hS
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hS
    obtain ⟨hPc, hPcols⟩ := six_properties P hP
    have hs := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image B hB j e heB P
    rw [hPcols] at hs
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, hmissing P hP⟩, ?_⟩
    · intro x hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    · rw [card_image_of_injective _ he, hPc]
    · rw [hs, card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have h := card_le_card hsub
  rwa [card_image_of_injective _ (image_injective he), six_card] at h

/-- The exact AC-support restriction supplies four absences; the other
thirteen absences come from barred BC and the four proved low obstructions. -/
theorem forbidden_missing {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (F : Finset (Finset α))
    (hbar : ∀ P ∈ Submissions.Erdos1020MatchingRankThreeACTwo.Main.barredBC, P.image e ∉ F)
    (hAC : ∀ i l : Fin 3, i ≠ l →
      ({e (i, 0), e (l, 2)} : Finset α) ∈ F → (i = 0 ∨ i = 2) ∧ l = 1)
    (hlow : ∀ P ∈ lowFour, P.image e ∉ F) : ∀ P ∈ forbidden, P.image e ∉ F := by
  intro P hP hmem
  rcases mem_union.mp hP with hP | hP
  · rcases mem_union.mp hP with hP | hP
    · exact hbar P hP hmem
    · simp only [otherAC, mem_insert, mem_singleton] at hP
      rcases hP with rfl | rfl | rfl | rfl
      · have h := hAC 0 2 (by decide) (by simpa using hmem)
        exact (by decide : (2 : Fin 3) ≠ 1) h.2
      · have h := hAC 1 0 (by decide) (by simpa using hmem)
        exact (by decide : (0 : Fin 3) ≠ 1) h.2
      · have h := hAC 1 2 (by decide) (by simpa using hmem)
        exact (by decide : (2 : Fin 3) ≠ 1) h.2
      · have h := hAC 2 0 (by decide) (by simpa using hmem)
        exact (by decide : (0 : Fin 3) ≠ 1) h.2
  · exact hlow P hP hmem

/-- Exact transfer of the ten remaining grid pairs to the actual local pair filter. -/
theorem width_two_le_ten {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hBe : ∀ i, B (j i) = univ.image (fun a => e (i, a)))
    (F : Finset (Finset α)) (hmissing : ∀ P ∈ forbidden, P.image e ∉ F) :
    (F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2)).card ≤ 10 := by
  classical
  let W := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.widePairs
  have hsub : F.filter (fun S => S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧
      (support B S).card = 2) ⊆ (W \ forbidden).image (fun P => P.image e) := by
    intro S hS
    obtain ⟨hSF, hSU, hSc, hSw⟩ := mem_filter.mp hS
    have hSall : S ⊆ G ∪ univ.biUnion B := hSU.trans
      (union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ _)))
    have hSG := (Submissions.Erdos1020MatchingSupportTransversal.Main.transversal_of_support_card_eq
      G B hB hGB S hSall (by omega)).1
    have hSgrid : S ⊆ univ.image e := by
      intro x hx
      rcases mem_union.mp (hSU hx) with hxG | hxB
      · exact (disjoint_left.mp hSG hx hxG).elim
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxB
        obtain ⟨a, _, rfl⟩ := mem_image.mp hi
        rw [hBe a] at hxi
        obtain ⟨b, _, rfl⟩ := mem_image.mp hxi
        exact mem_image.mpr ⟨(a, b), mem_univ _, rfl⟩
    obtain ⟨P, hPe⟩ := subset_univ_image_iff.mp hSgrid
    have hPc : P.card = 2 := by
      have h := congrArg Finset.card hPe
      rw [card_image_of_injective _ he, hSc] at h
      exact h
    have hPw : (P.image Prod.fst).card = 2 := by
      have h := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image B hB j e heB P
      rw [hPe] at h
      have hc := congrArg Finset.card h
      rw [hSw, card_image_of_injective _ hj] at hc
      exact hc.symm
    have hwide : P ∈ W := mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨subset_univ _, hPc⟩, hPw⟩
    have hforbid : P ∉ forbidden := by
      intro hP
      exact hmissing P hP (hPe.symm ▸ hSF)
    exact mem_image.mpr ⟨P, mem_sdiff.mpr ⟨hwide, hforbid⟩, hPe⟩
  calc
    _ ≤ ((W \ forbidden).image (fun P => P.image e)).card := card_le_card hsub
    _ ≤ (W \ forbidden).card := card_image_le
    _ = 10 := remaining_card

/-- Actual Case II.2(ii): the only AC pairs are a0-c1 and a2-c1. The two
positive pairs and actual middle hubs force the four low absences and six
missing wide triples; neither local count is a premise. -/
theorem actual_counts {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (hAC : ∀ i l : Fin 3, i ≠ l →
      ({e (i, 0), e (l, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) →
        (i = 0 ∨ i = 2) ∧ l = 1)
    (hP : ({e (0, 0), e (1, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hQ : ({e (2, 0), e (1, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hR : ∀ i : Fin 3, G ∪ {e (i, 1)} ∈ H.image (fun S => S ∩ A)) :
    ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region G B (univ.image j) ∧
      S.card = 2 ∧ (support B S).card = 2)).card ≤ 10 ∧
      6 ≤ (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 3)).card := by
  classical
  let U := region G B (univ.image j)
  let F := (H.image (fun S => S ∩ A)).filter (fun S => S ⊆ U)
  have heA (p : Fin 3 × Fin 3) : e p ∈ A := hBA _ (heB p.1 p.2)
  have hsub (X : Finset (Fin 3 × Fin 3)) : X.image e ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hdG : Disjoint G (univ.image e) := by
    apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (j i)) hxG (heB i a)
  have hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro f hf
    apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree G B hBH hBA hBd hGB (univ.image j)
      (by rw [Fintype.card_prod, Fintype.card_bool, card_image_of_injective _ hj,
        card_univ, Fintype.card_fin]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  have hmiss (P Q : Finset (Fin 3 × Fin 3)) (i : Fin 3) (T : Finset (Fin 3 × Fin 3))
      (hP : P.image e ∈ H.image (fun S => S ∩ A))
      (hQ : Q.image e ∈ H.image (fun S => S ∩ A))
      (hPQ : Disjoint P Q) (hPR : Disjoint P {(i, 1)}) (hQR : Disjoint Q {(i, 1)})
      (hPT : Disjoint P T) (hQT : Disjoint Q T) (hRT : Disjoint {(i, 1)} T) :
      T.image e ∉ H.image (fun S => S ∩ A) := by
    have h := missing_grid_of_pairs e he G hdG F hno P Q i T
      (mem_filter.mpr ⟨hP, hsub _⟩) (mem_filter.mpr ⟨hQ, hsub _⟩)
      (mem_filter.mpr ⟨hR i, union_subset subset_union_left (by simpa using hsub {(i, 1)})⟩)
      hPQ hPR hQR hPT hQT hRT
    exact fun hT => h (mem_filter.mpr ⟨hT, hsub _⟩)
  have hP0 := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
    H A hstable e he heA hrow 0 1 (by decide) 0 0 0 2 (by decide) (by decide) hP
  have hQ0 := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
    H A hstable e he heA hrow 2 1 (by decide) 0 0 0 2 (by decide) (by decide) hQ
  have hP1 := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
    H A hstable e he heA hrow 0 1 (by decide) 0 0 1 2 (by decide) (by decide) hP
  have hQ1 := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
    H A hstable e he heA hrow 2 1 (by decide) 0 0 1 2 (by decide) (by decide) hQ
  have hleft := hmiss {(0, 0), (1, 2)} {(2, 0), (1, 0)} 0 (triple 2 1 1)
    (by simpa using hP) (by simpa using hQ0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hright := hmiss {(2, 0), (1, 2)} {(0, 0), (1, 0)} 2 (triple 1 1 2)
    (by simpa using hQ) (by simpa using hP0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlow01 := hmiss {(2, 0), (1, 2)} {(0, 0), (1, 1)} 2 {(0, 1), (1, 0)}
    (by simpa using hQ) (by simpa using hP1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlow12 := hmiss {(0, 0), (1, 2)} {(2, 0), (1, 1)} 0 {(1, 0), (2, 1)}
    (by simpa using hP) (by simpa using hQ1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlow : ∀ P ∈ lowFour, P.image e ∉ H.image (fun S => S ∩ A) := by
    intro P hP hmem
    simp only [lowFour, mem_insert, mem_singleton] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact hlow01 hmem
    · exact hlow12 hmem
    · apply hlow01
      simpa using Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
        H A hstable e he heA hrow 0 1 (by decide) 1 1 0 1 (by decide) (by decide)
        (by simpa using hmem)
    · apply hlow12
      simpa using Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
        H A hstable e he heA hrow 1 2 (by decide) 0 1 1 1 (by decide) (by decide)
        (by simpa using hmem)
  have hBe (i : Fin 3) : B (j i) = univ.image (fun a => e (i, a)) := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      exact heB i a
    · have hi : Function.Injective (fun a => e (i, a)) :=
        fun a b h => congrArg Prod.snd (he h)
      rw [hH _ (hBH _), card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  refine ⟨width_two_le_ten G B hBd hGB j hj e he heB hBe (H.image (fun S => S ∩ A))
    (forbidden_missing e _
      (Submissions.Erdos1020MatchingRankThreeACTwo.Main.barredBC_missing e _ hbar) hAC hlow), ?_⟩
  exact six_missing_width_three G B hBd j hj e he heB (H.image (fun S => S ∩ A))
    (six_missing_trace H A hstable e he heA hrow hleft hright)

end Submissions.Erdos1020MatchingRankThreeACCommon.Main

namespace Submissions.Erdos1020MatchingRankThreeACFew.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeBCPairs.Main
open Submissions.Erdos1020MatchingRankThreeACTwo.Main
open Submissions.Erdos1020MatchingRankThreeLowGraph.Main
open Submissions.Erdos1020MatchingRankThreeGridPairs.Main
open Submissions.Erdos1020MatchingRankThreeActiveWide.Main
open Submissions.Erdos1020MatchingRankThreeActiveTrace.Main

/-- The six cross-column bottom/top pairs. -/
def acPairs : Finset (Finset (Fin 3 × Fin 3)) :=
  (univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2)).image
    (fun p => acPair p.1 p.2)

private theorem wide_split : widePairs ⊆ (lowPairs ∪ acPairs) ∪ barredBC := by decide

private theorem ac_subset_bottomSeed (i j : Fin 3) (hij : i ≠ j) :
    acPair i j ⊆ bottomSeed i := by
  have h : ∀ i j : Fin 3, i ≠ j → acPair i j ⊆ bottomSeed i := by decide
  exact h i j hij

/-- A present AC edge excludes activity of its bottom: the two witnessing
low pairs and the sixth-low-vertex hub would be disjoint from that AC edge. -/
theorem ac_missing_of_active {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (P : Finset (Finset (Fin 3 × Fin 3))) (hP : P ⊆ lowPairs)
    (hPF : ∀ Q ∈ P, Q.image e ∈ F) (i j : Fin 3) (hij : i ≠ j)
    (hi : i ∈ active P) : (acPair i j).image e ∉ F := by
  classical
  obtain ⟨Q, hQP, R, hRP, hQR, hav⟩ := (mem_active P i).mp hi
  have hQ := mem_powersetCard.mp (mem_filter.mp (hP hQP)).1
  have hR := mem_powersetCard.mp (mem_filter.mp (hP hRP)).1
  have hc : (insert (i, 0) (Q ∪ R)).card = 5 := by
    rw [card_insert_of_notMem hav, card_union_of_disjoint hQR, hQ.2, hR.2]
  have hlow : lowVertices.card = 6 := by decide
  obtain ⟨x, hxlow, hx⟩ := exists_mem_notMem_of_card_lt_card (show
      (insert (i, 0) (Q ∪ R)).card < lowVertices.card by omega)
  have hxQR : x ∉ Q ∪ R := fun h => hx (mem_insert_of_mem h)
  have hxi : x ≠ (i, 0) := by
    intro h
    subst x
    exact hx (mem_insert_self _ _)
  have hQseed := (low_disjoint_seed Q hQ.1 i
    (fun h => hav (mem_union_left _ h))).mono_right (ac_subset_bottomSeed i j hij)
  have hRseed := (low_disjoint_seed R hR.1 i
    (fun h => hav (mem_union_right _ h))).mono_right (ac_subset_bottomSeed i j hij)
  have hxseed : Disjoint ({x} : Finset (Fin 3 × Fin 3)) (acPair i j) :=
    (low_disjoint_seed {x} (singleton_subset_iff.mpr hxlow) i
      (by simpa only [mem_singleton] using Ne.symm hxi)).mono_right
        (ac_subset_bottomSeed i j hij)
  have hd (X Y : Finset (Fin 3 × Fin 3)) (h : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr h
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  apply Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    (Q.image e) (R.image e) (G ∪ ({x} : Finset (Fin 3 × Fin 3)).image e)
    ((acPair i j).image e) (hPF Q hQP) (hPF R hRP) (by simpa using hhub x hxlow)
  · exact hd _ _ hQR
  · exact disjoint_union_right.mpr ⟨(hdG _).symm,
      hd _ _ (disjoint_singleton_right.mpr (fun h => hxQR (mem_union_left _ h)))⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm,
      hd _ _ (disjoint_singleton_right.mpr (fun h => hxQR (mem_union_right _ h)))⟩
  · exact hd _ _ hQseed
  · exact hd _ _ hRseed
  · exact disjoint_union_left.mpr ⟨hdG _, hd _ _ hxseed⟩

theorem low_card_le_eight {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (P : Finset (Finset (Fin 3 × Fin 3))) (hP : P ⊆ lowPairs)
    (hPF : ∀ Q ∈ P, Q.image e ∈ F) (i j : Fin 3) (hij : i ≠ j)
    (hac : (acPair i j).image e ∈ F) : P.card ≤ 8 := by
  by_contra h
  have hi : i ∈ active P := by
    rw [active_eq_univ_of_nine P hP (by omega)]
    exact mem_univ _
  exact ac_missing_of_active e he G hG F hno hhub P hP hPF i j hij hi hac

/-- Count the present wide pairs by their low part and an explicit allowed AC
carrier. The carrier restricts actual pair memberships, not their unknown count. -/
theorem present_card_le_eight_add {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (hBC : ∀ Q ∈ barredBC, Q.image e ∉ F)
    (C : Finset (Finset (Fin 3 × Fin 3)))
    (hAC : ∀ i j : Fin 3, i ≠ j → (acPair i j).image e ∈ F → acPair i j ∈ C)
    (i j : Fin 3) (hij : i ≠ j) (hac : (acPair i j).image e ∈ F) :
    (presentPairs e F).card ≤ 8 + C.card := by
  let L := (presentPairs e F).filter (fun Q => Q ∈ lowPairs)
  have hL : L.card ≤ 8 := low_card_le_eight e he G hG F hno hhub L
    (fun Q hQ => (mem_filter.mp hQ).2)
    (fun Q hQ => (mem_filter.mp (mem_filter.mp hQ).1).2) i j hij hac
  have hsub : presentPairs e F ⊆ L ∪ C := by
    intro Q hQ
    obtain ⟨hwide, hQF⟩ := mem_filter.mp hQ
    rcases mem_union.mp (wide_split hwide) with hlowAC | hbc
    · rcases mem_union.mp hlowAC with hlow | hacQ
      · exact mem_union_left _ (mem_filter.mpr ⟨hQ, hlow⟩)
      · obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.mp hacQ
        exact mem_union_right _ (hAC a b (mem_filter.mp hab).2 hQF)
    · exact (hBC Q hbc hQF).elim
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right hL _))

/-- The common-bottom two-AC branch has at most ten present wide pairs. -/
theorem common_bottom_pairs_le_ten {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (hBC : ∀ Q ∈ barredBC, Q.image e ∉ F)
    (hAC : ∀ i j : Fin 3, i ≠ j → (acPair i j).image e ∈ F →
      i = 1 ∧ (j = 0 ∨ j = 2))
    (hac : (acPair 1 0).image e ∈ F) : (presentPairs e F).card ≤ 10 := by
  have h := present_card_le_eight_add e he G hG F hno hhub hBC
    {acPair 1 0, acPair 1 2} (fun i j hij hmem => by
      obtain ⟨rfl, rfl | rfl⟩ := hAC i j hij hmem <;> simp) 1 0 (by decide) hac
  have hc : ({acPair 1 0, acPair 1 2} : Finset (Finset (Fin 3 × Fin 3))).card = 2 := by decide
  simpa only [hc] using h

/-- A sole AC edge gives at most nine present wide pairs. This is stronger
than the ten-pair estimate needed by the missing-test branch. -/
theorem sole_ac_pairs_le_nine {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (hBC : ∀ Q ∈ barredBC, Q.image e ∉ F)
    (hAC : ∀ i j : Fin 3, i ≠ j → (acPair i j).image e ∈ F → i = 0 ∧ j = 1)
    (hac : (acPair 0 1).image e ∈ F) : (presentPairs e F).card ≤ 9 := by
  have h := present_card_le_eight_add e he G hG F hno hhub hBC
    {acPair 0 1} (fun i j hij hmem => by
      obtain ⟨rfl, rfl⟩ := hAC i j hij hmem
      simp) 0 1 (by decide) hac
  simpa only [card_singleton] using h

open Submissions.Erdos1020MatchingRankThreeACCommon.Main

/-- All six permutations of heights zero, one and two give an exhaustive
finer test split for both AC branches. -/
def testHeights : Finset (Fin 3 × Fin 3 × Fin 3) :=
  univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)

def testCone (p : Fin 3 × Fin 3 × Fin 3) : Finset (Finset (Fin 3 × Fin 3)) :=
  (univ.filter (fun q : Fin 3 × Fin 3 × Fin 3 =>
    p.1 ≤ q.1 ∧ p.2.1 ≤ q.2.1 ∧ p.2.2 ≤ q.2.2)).image
      (fun q => triple q.1 q.2.1 q.2.2)

private theorem testCone_properties (p : Fin 3 × Fin 3 × Fin 3) (hp : p ∈ testHeights) :
    (testCone p).card = 6 ∧ ∀ Q ∈ testCone p, Q.card = 3 ∧ Q.image Prod.fst = univ := by
  have h : ∀ p ∈ testHeights, (testCone p).card = 6 ∧
      ∀ Q ∈ testCone p, Q.card = 3 ∧ Q.image Prod.fst = univ := by decide +kernel
  exact h p hp

/-- Any missing one of the listed test triples supplies all six of its
coordinate majorants as absent actual traces. -/
theorem testCone_missing_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (p : Fin 3 × Fin 3 × Fin 3)
    (hmissing : (triple p.1 p.2.1 p.2.2).image e ∉ H.image (fun S => S ∩ A)) :
    ∀ Q ∈ testCone p, Q.image e ∉ H.image (fun S => S ∩ A) := by
  intro Q hQ hmem
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hQ
  obtain ⟨ha, hb, hc⟩ := (mem_filter.mp hq).2
  exact hmissing (lower_grid_triple_trace H A hstable e he heA hrow
    p.1 q.1 p.2.1 q.2.1 p.2.2 q.2.2 ha hb hc hmem)

/-- Six distinct test-cone images lie in the literal missing-width-three filter. -/
theorem testCone_six_missing {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (F : Finset (Finset α))
    (p : Fin 3 × Fin 3 × Fin 3) (hp : p ∈ testHeights)
    (hmissing : ∀ Q ∈ testCone p, Q.image e ∉ F) :
    6 ≤ (((region G B (univ.image j)).powersetCard 3 \ F).filter
      (fun S => (support B S).card = 3)).card := by
  have hprop := testCone_properties p hp
  have hsub : (testCone p).image (fun Q => Q.image e) ⊆
      (((region G B (univ.image j)).powersetCard 3 \ F).filter
        (fun S => (support B S).card = 3)) := by
    intro S hS
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hS
    obtain ⟨hQc, hQcol⟩ := hprop.2 Q hQ
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩,
      hmissing Q hQ⟩, ?_⟩
    · intro x hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    · rw [card_image_of_injective _ he, hQc]
    · rw [support_grid_image B hB j e heB Q, hQcol,
        card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have hc : ((testCone p).image (fun Q => Q.image e)).card = 6 := by
    rw [card_image_of_injective _ (image_injective he), hprop.1]
  exact hc ▸ card_le_card hsub

/-- The six-wide count uses actual trace stability and a missing listed test;
it is independent of the AC pair count and of the desired weighted inequality. -/
theorem six_missing_of_test {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (p : Fin 3 × Fin 3 × Fin 3) (hp : p ∈ testHeights)
    (hmissing : (triple p.1 p.2.1 p.2.2).image e ∉ H.image (fun S => S ∩ A)) :
    6 ≤ (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
      (fun S => (support B S).card = 3)).card :=
  testCone_six_missing G B hB j hj e he heB (H.image (fun S => S ∩ A)) p hp
    (testCone_missing_trace H A hstable e he heA hrow p hmissing)

/-- The common-bottom positive branch retains only the three AA pairs. -/
def commonAllowed : Finset (Finset (Fin 3 × Fin 3)) :=
  lowPairs.filter (fun P => ∀ p ∈ P, p.2 = 0)

/-- The sole-AC positive branch also allows a0b1 and a0b2. -/
def soleAllowed : Finset (Finset (Fin 3 × Fin 3)) :=
  commonAllowed ∪ {{(0, 0), (1, 1)}, {(0, 0), (2, 1)}}

def allTests : Finset (Finset (Fin 3 × Fin 3)) :=
  testHeights.image (fun p => triple p.1 p.2.1 p.2.2)

def commonKnown : Finset (Finset (Fin 3 × Fin 3)) :=
  {acPair 1 0, acPair 1 2} ∪ allTests

def soleKnown : Finset (Finset (Fin 3 × Fin 3)) :=
  {acPair 0 1} ∪ allTests

/-- The AC top hubs are explicit in the common-bottom positive branch. -/
def commonHubs : Finset (Fin 3 × Fin 3) := lowVertices ∪ {(0, 2), (2, 2)}

private theorem allowed_cards : commonAllowed.card = 3 ∧ soleAllowed.card = 5 := by decide

private theorem common_obstructions : ∀ P ∈ lowPairs \ commonAllowed,
    ∃ Q ∈ commonKnown, ∃ R ∈ commonKnown, ∃ x ∈ commonHubs,
      Disjoint P Q ∧ Disjoint P R ∧ Disjoint Q R ∧ x ∉ (P ∪ Q) ∪ R := by
  decide +kernel

private theorem sole_obstructions : ∀ P ∈ lowPairs \ soleAllowed,
    ∃ Q ∈ soleKnown, ∃ R ∈ soleKnown, ∃ x ∈ lowVertices,
      Disjoint P Q ∧ Disjoint P R ∧ Disjoint Q R ∧ x ∉ (P ∪ Q) ∪ R := by
  decide +kernel

/-- Transfer a finite three-set obstruction with one available hub. -/
private theorem missing_of_two_known {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (P Q R : Finset (Fin 3 × Fin 3)) (x : Fin 3 × Fin 3)
    (hQ : Q.image e ∈ F) (hR : R.image e ∈ F) (hx : G ∪ {e x} ∈ F)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R)
    (hav : x ∉ (P ∪ Q) ∪ R) : P.image e ∉ F := by
  have hd (X Y : Finset (Fin 3 × Fin 3)) (h : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr h
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  have hxP : x ∉ P := fun h => hav (mem_union_left _ (mem_union_left _ h))
  have hxQ : x ∉ Q := fun h => hav (mem_union_left _ (mem_union_right _ h))
  have hxR : x ∉ R := fun h => hav (mem_union_right _ h)
  apply Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    (Q.image e) (R.image e) (G ∪ ({x} : Finset (Fin 3 × Fin 3)).image e)
    (P.image e) hQ hR (by simpa using hx)
  · exact hd _ _ hQR
  · exact disjoint_union_right.mpr ⟨(hdG _).symm,
      hd _ _ (disjoint_singleton_right.mpr hxQ)⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm,
      hd _ _ (disjoint_singleton_right.mpr hxR)⟩
  · exact hd _ _ hPQ.symm
  · exact hd _ _ hPR.symm
  · exact disjoint_union_left.mpr ⟨hdG _,
      hd _ _ (disjoint_singleton_left.mpr hxP)⟩

private theorem present_card_le_carriers {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (F : Finset (Finset α))
    (L C : Finset (Finset (Fin 3 × Fin 3)))
    (hLow : ∀ Q ∈ lowPairs, Q.image e ∈ F → Q ∈ L)
    (hBC : ∀ Q ∈ barredBC, Q.image e ∉ F)
    (hAC : ∀ i j : Fin 3, i ≠ j → (acPair i j).image e ∈ F → acPair i j ∈ C) :
    (presentPairs e F).card ≤ L.card + C.card := by
  have hsub : presentPairs e F ⊆ L ∪ C := by
    intro Q hQ
    obtain ⟨hwide, hQF⟩ := mem_filter.mp hQ
    rcases mem_union.mp (wide_split hwide) with hlowAC | hbc
    · rcases mem_union.mp hlowAC with hlow | hacQ
      · exact mem_union_left _ (hLow Q hlow hQF)
      · obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.mp hacQ
        exact mem_union_right _ (hAC i j (mem_filter.mp hij).2 hQF)
    · exact (hBC Q hbc hQF).elim
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- If all six permutation tests are present, the common-bottom branch has
at most five present wide pairs. Its two AC-top hubs remain explicit. -/
theorem common_bottom_all_tests_le_five {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ commonHubs, G ∪ {e x} ∈ F)
    (hBC : ∀ Q ∈ barredBC, Q.image e ∉ F)
    (hAC : ∀ i j : Fin 3, i ≠ j → (acPair i j).image e ∈ F →
      i = 1 ∧ (j = 0 ∨ j = 2))
    (hac0 : (acPair 1 0).image e ∈ F) (hac2 : (acPair 1 2).image e ∈ F)
    (htests : ∀ p ∈ testHeights, (triple p.1 p.2.1 p.2.2).image e ∈ F) :
    (presentPairs e F).card ≤ 5 := by
  have hknown : ∀ Q ∈ commonKnown, Q.image e ∈ F := by
    intro Q hQ
    rcases mem_union.mp hQ with hac | ht
    · simp only [mem_insert, mem_singleton] at hac
      rcases hac with rfl | rfl
      · exact hac0
      · exact hac2
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
      exact htests p hp
  have h := present_card_le_carriers e F commonAllowed {acPair 1 0, acPair 1 2}
    (fun P hP hPF => by
      by_contra hn
      obtain ⟨Q, hQ, R, hR, x, hx, hPQ, hPR, hQR, hav⟩ :=
        common_obstructions P (mem_sdiff.mpr ⟨hP, hn⟩)
      exact missing_of_two_known e he G hG F hno P Q R x
        (hknown Q hQ) (hknown R hR) (hhub x hx) hPQ hPR hQR hav hPF)
    hBC (fun i j hij hmem => by
      obtain ⟨rfl, rfl | rfl⟩ := hAC i j hij hmem <;> simp)
  have hc : ({acPair 1 0, acPair 1 2} : Finset (Finset (Fin 3 × Fin 3))).card = 2 := by decide
  simpa only [allowed_cards.1, hc] using h

/-- If all six permutation tests are present, the sole-AC branch has at most
six present wide pairs. Only the six low hubs are needed in this branch. -/
theorem sole_ac_all_tests_le_six {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F)
    (hBC : ∀ Q ∈ barredBC, Q.image e ∉ F)
    (hAC : ∀ i j : Fin 3, i ≠ j → (acPair i j).image e ∈ F → i = 0 ∧ j = 1)
    (hac : (acPair 0 1).image e ∈ F)
    (htests : ∀ p ∈ testHeights, (triple p.1 p.2.1 p.2.2).image e ∈ F) :
    (presentPairs e F).card ≤ 6 := by
  have hknown : ∀ Q ∈ soleKnown, Q.image e ∈ F := by
    intro Q hQ
    rcases mem_union.mp hQ with hq | ht
    · rcases mem_singleton.mp hq with rfl
      exact hac
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
      exact htests p hp
  have h := present_card_le_carriers e F soleAllowed {acPair 0 1}
    (fun P hP hPF => by
      by_contra hn
      obtain ⟨Q, hQ, R, hR, x, hx, hPQ, hPR, hQR, hav⟩ :=
        sole_obstructions P (mem_sdiff.mpr ⟨hP, hn⟩)
      exact missing_of_two_known e he G hG F hno P Q R x
        (hknown Q hQ) (hknown R hR) (hhub x hx) hPQ hPR hQR hav hPF)
    hBC (fun i j hij hmem => by
      obtain ⟨rfl, rfl⟩ := hAC i j hij hmem
      simp)
  simpa only [allowed_cards.2, card_singleton] using h

/-- Localizing the actual trace family preserves every board set and hub.
The no-four premise is derived from the original matching exclusion. -/
private theorem actual_local_data {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) :
    let T := H.image (fun S => S ∩ A)
    let U := region G B (univ.image j)
    let F := T.filter (fun S => S ⊆ U)
    (∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j))) ∧
    Disjoint G (univ.image e) ∧
    (∀ P : Finset (Fin 3 × Fin 3), P.image e ∈ F ↔ P.image e ∈ T) ∧
    (∀ x : Fin 3 × Fin 3, G ∪ {e x} ∈ F ↔ G ∪ {e x} ∈ T) ∧
    (presentPairs e F).card = (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧
      (support B S).card = 2)).card := by
  classical
  let T := H.image (fun S => S ∩ A)
  let U := region G B (univ.image j)
  let F := T.filter (fun S => S ⊆ U)
  have hsub (X : Finset (Fin 3 × Fin 3)) : X.image e ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hgrid (P : Finset (Fin 3 × Fin 3)) : P.image e ∈ F ↔ P.image e ∈ T :=
    ⟨fun h => (mem_filter.mp h).1, fun h => mem_filter.mpr ⟨h, hsub P⟩⟩
  have hBe (i : Fin 3) : B (j i) = univ.image (fun a => e (i, a)) := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      exact heB i a
    · have hi : Function.Injective (fun a => e (i, a)) :=
        fun a b h => congrArg Prod.snd (he h)
      rw [hH _ (hBH _), card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  refine ⟨?_, ?_, hgrid, ?_, ?_⟩
  · intro f hf
    apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree G B hBH hBA hBd hGB (univ.image j)
      (by rw [Fintype.card_prod, Fintype.card_bool, card_image_of_injective _ hj,
        card_univ, Fintype.card_fin]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  · apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (j i)) hxG (heB i a)
  · intro x
    exact ⟨fun h => (mem_filter.mp h).1, fun h => mem_filter.mpr
      ⟨h, union_subset subset_union_left (by simpa using hsub {x})⟩⟩
  · have hEq : presentPairs e F = presentPairs e T := by
      ext P
      simp only [presentPairs, mem_filter, hgrid]
    rw [hEq]
    exact (local_pairs_card G B hBd hGB j hj e he heB hBe T).symm

/-- Actual Case II.2(iii), with its eight available hubs explicit. The six
permutation tests are split exhaustively, never assumed in the conclusion. -/
theorem common_bottom_actual_counts {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (hAC : ∀ i l : Fin 3, i ≠ l →
      ({e (i, 0), e (l, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) →
        i = 1 ∧ (l = 0 ∨ l = 2))
    (hP : ({e (1, 0), e (0, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hQ : ({e (1, 0), e (2, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hhub : ∀ x ∈ commonHubs, G ∪ {e x} ∈ H.image (fun S => S ∩ A))
    (hcover : ∀ S ∈ H.image (fun S => S ∩ A), ∀ T ∈ H.image (fun S => S ∩ A),
      S ∪ T ≠ univ.image (e ∘ upperBoard)) :
    let p₂ := ((H.image (fun S => S ∩ A)).filter (fun S =>
      S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧ (support B S).card = 2)).card
    let d₃ := (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
      (fun S => (support B S).card = 3)).card
    (p₂ ≤ 10 ∧ 6 ≤ d₃) ∨ (p₂ ≤ 5 ∧ 4 ≤ d₃) := by
  classical
  let T := H.image (fun S => S ∩ A)
  let F := T.filter (fun S => S ⊆ region G B (univ.image j))
  obtain ⟨hno, hdG, hgrid, hhubLocal, hcard⟩ :=
    actual_local_data H A hH hA hcut hstable hfree G B hBH hBA hBd hGB j hj e he heB
  have hhubF : ∀ x ∈ commonHubs, G ∪ {e x} ∈ F :=
    fun x hx => (hhubLocal x).mpr (hhub x hx)
  have hlowF : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F :=
    fun x hx => hhubF x (mem_union_left _ hx)
  have hbarF : ∀ Q ∈ barredBC, Q.image e ∉ F := by
    intro Q hQ hmem
    exact barredBC_missing e T hbar Q hQ ((hgrid Q).mp hmem)
  have hACF : ∀ i l : Fin 3, i ≠ l → (acPair i l).image e ∈ F →
      i = 1 ∧ (l = 0 ∨ l = 2) := by
    intro i l hil hmem
    exact hAC i l hil (by simpa only [acPair, image_insert, image_singleton] using (hgrid _).mp hmem)
  have hPF : (acPair 1 0).image e ∈ F :=
    (hgrid _).mpr (by simpa only [acPair, image_insert, image_singleton] using hP)
  have hQF : (acPair 1 2).image e ∈ F :=
    (hgrid _).mpr (by simpa only [acPair, image_insert, image_singleton] using hQ)
  by_cases ht : ∀ p ∈ testHeights, (triple p.1 p.2.1 p.2.2).image e ∈ T
  · right
    constructor
    · have h := common_bottom_all_tests_le_five e he G hdG F hno hhubF hbarF
        hACF hPF hQF (fun p hp => (hgrid _).mpr (ht p hp))
      rwa [hcard] at h
    · exact Submissions.Erdos1020MatchingRankThreeWideBase.Main.four_missing_width_three
        G B hBd j hj (e ∘ upperBoard) (he.comp upperBoard_injective)
        (fun i b => heB i _) T hcover
  · push_neg at ht
    obtain ⟨p, hp, hmissing⟩ := ht
    left
    constructor
    · have h := common_bottom_pairs_le_ten e he G hdG F hno hlowF hbarF hACF hPF
      rwa [hcard] at h
    · exact six_missing_of_test H A hstable G B hBd j hj e he heB
        (fun p => hBA _ (heB p.1 p.2)) hrow p hp hmissing

/-- Actual Case II.2(iv). Only the six low hubs are supplied; either a test
is missing, giving the stronger nine/six counts, or all tests give six/four. -/
theorem sole_ac_actual_counts {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (hAC : ∀ i l : Fin 3, i ≠ l →
      ({e (i, 0), e (l, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) → i = 0 ∧ l = 1)
    (hP : ({e (0, 0), e (1, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ H.image (fun S => S ∩ A))
    (hcover : ∀ S ∈ H.image (fun S => S ∩ A), ∀ T ∈ H.image (fun S => S ∩ A),
      S ∪ T ≠ univ.image (e ∘ upperBoard)) :
    let p₂ := ((H.image (fun S => S ∩ A)).filter (fun S =>
      S ⊆ region G B (univ.image j) ∧ S.card = 2 ∧ (support B S).card = 2)).card
    let d₃ := (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
      (fun S => (support B S).card = 3)).card
    (p₂ ≤ 9 ∧ 6 ≤ d₃) ∨ (p₂ ≤ 6 ∧ 4 ≤ d₃) := by
  classical
  let T := H.image (fun S => S ∩ A)
  let F := T.filter (fun S => S ⊆ region G B (univ.image j))
  obtain ⟨hno, hdG, hgrid, hhubLocal, hcard⟩ :=
    actual_local_data H A hH hA hcut hstable hfree G B hBH hBA hBd hGB j hj e he heB
  have hhubF : ∀ x ∈ lowVertices, G ∪ {e x} ∈ F :=
    fun x hx => (hhubLocal x).mpr (hhub x hx)
  have hbarF : ∀ Q ∈ barredBC, Q.image e ∉ F := by
    intro Q hQ hmem
    exact barredBC_missing e T hbar Q hQ ((hgrid Q).mp hmem)
  have hACF : ∀ i l : Fin 3, i ≠ l → (acPair i l).image e ∈ F → i = 0 ∧ l = 1 := by
    intro i l hil hmem
    exact hAC i l hil (by simpa only [acPair, image_insert, image_singleton] using (hgrid _).mp hmem)
  have hPF : (acPair 0 1).image e ∈ F :=
    (hgrid _).mpr (by simpa only [acPair, image_insert, image_singleton] using hP)
  by_cases ht : ∀ p ∈ testHeights, (triple p.1 p.2.1 p.2.2).image e ∈ T
  · right
    constructor
    · have h := sole_ac_all_tests_le_six e he G hdG F hno hhubF hbarF hACF hPF
        (fun p hp => (hgrid _).mpr (ht p hp))
      rwa [hcard] at h
    · exact Submissions.Erdos1020MatchingRankThreeWideBase.Main.four_missing_width_three
        G B hBd j hj (e ∘ upperBoard) (he.comp upperBoard_injective)
        (fun i b => heB i _) T hcover
  · push_neg at ht
    obtain ⟨p, hp, hmissing⟩ := ht
    left
    constructor
    · have h := sole_ac_pairs_le_nine e he G hdG F hno hhubF hbarF hACF hPF
      rwa [hcard] at h
    · exact six_missing_of_test H A hstable G B hBd j hj e he heB
        (fun p => hBA _ (heB p.1 p.2)) hrow p hp hmissing

end Submissions.Erdos1020MatchingRankThreeACFew.Main

namespace Submissions.Erdos1020MatchingRankThreeTwelveMedium.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- A directed cross-column bottom/middle pair. -/
def abPair (i j : Fin 3) : Finset (Fin 3 × Fin 3) := {(i, 0), (j, 1)}

/-- A low point and the top in its column, together with another column's top. -/
def mediumTriple (p : (Fin 3 × Fin 3) × Fin 3) : Finset (Fin 3 × Fin 3) :=
  {p.1, (p.1.1, 2), (p.2, 2)}

/-- The twelve medium triples in the final all-low-pairs case. -/
def mediumFamily : Finset (Finset (Fin 3 × Fin 3)) :=
  (univ.filter (fun p : (Fin 3 × Fin 3) × Fin 3 => p.1.1 ≠ p.2 ∧ p.1.2 < 2)).image
    mediumTriple

theorem mediumFamily_card : mediumFamily.card = 12 := by decide

theorem mediumFamily_geometry (S : Finset (Fin 3 × Fin 3)) (hS : S ∈ mediumFamily) :
    S.card = 3 ∧ (S.image Prod.fst).card = 2 := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hS
  have h : ∀ p : (Fin 3 × Fin 3) × Fin 3, p.1.1 ≠ p.2 ∧ p.1.2 < 2 →
      (mediumTriple p).card = 3 ∧ ((mediumTriple p).image Prod.fst).card = 2 := by decide
  exact h p (mem_filter.mp hp).2

/-- An exact labeled certificate: the other two columns supply two AB pairs;
the unused low point in the repeated column supplies the hub. -/
private theorem medium_obstruction :
    ∀ p : (Fin 3 × Fin 3) × Fin 3, p.1.1 ≠ p.2 ∧ p.1.2 < 2 →
      ∃ i j : Fin 3, i ≠ j ∧ ∃ h : Fin 3 × Fin 3, h.2 < 2 ∧
        Disjoint (abPair i j) (abPair j i) ∧
        Disjoint (abPair i j) {h} ∧ Disjoint (abPair j i) {h} ∧
        Disjoint (abPair i j) (mediumTriple p) ∧
        Disjoint (abPair j i) (mediumTriple p) ∧
        Disjoint ({h} : Finset (Fin 3 × Fin 3)) (mediumTriple p) := by decide

/-- Six directed AB pair memberships and six low hub memberships exclude
all twelve medium triples. No shifting or cross-column order is used here. -/
theorem mediumFamily_missing {α : Type*} [DecidableEq α]
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e) (G : Finset α)
    (hG : Disjoint G (univ.image e)) (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (hAB : ∀ i j : Fin 3, i ≠ j → (abPair i j).image e ∈ F)
    (hhub : ∀ h : Fin 3 × Fin 3, h.2 < 2 → G ∪ {e h} ∈ F)
    (S : Finset (Fin 3 × Fin 3)) (hS : S ∈ mediumFamily) : S.image e ∉ F := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hS
  obtain ⟨i, j, hij, h, hh, hPQ, hPh, hQh, hPS, hQS, hhS⟩ :=
    medium_obstruction p (mem_filter.mp hp).2
  have hd (X Y : Finset (Fin 3 × Fin 3)) (hXY : Disjoint X Y) :
      Disjoint (X.image e) (Y.image e) := (disjoint_image he).mpr hXY
  have hdG (X : Finset (Fin 3 × Fin 3)) : Disjoint G (X.image e) :=
    hG.mono (Subset.refl _) (image_subset_image (subset_univ X))
  apply Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    ((abPair i j).image e) ((abPair j i).image e)
    (G ∪ ({h} : Finset (Fin 3 × Fin 3)).image e) ((mediumTriple p).image e)
    (hAB i j hij) (hAB j i (Ne.symm hij)) (by simpa using hhub h hh)
  · exact hd _ _ hPQ
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ hPh⟩
  · exact disjoint_union_right.mpr ⟨(hdG _).symm, hd _ _ hQh⟩
  · exact hd _ _ hPS
  · exact hd _ _ hQS
  · exact disjoint_union_left.mpr ⟨hdG _, hd _ _ hhS⟩

/-- Injective grid transport counts twelve distinct missing width-two triples
in the literal local powerset difference. No missing-count premise is assumed. -/
theorem twelve_le_missing_width_two {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i)) (F : Finset (Finset α))
    (hmissing : ∀ S ∈ mediumFamily, S.image e ∉ F) :
    12 ≤ (((region G B (univ.image j)).powersetCard 3 \ F).filter
      (fun S => (support B S).card = 2)).card := by
  classical
  have hsub : mediumFamily.image (fun S => S.image e) ⊆
      (((region G B (univ.image j)).powersetCard 3 \ F).filter
        (fun S => (support B S).card = 2)) := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
    obtain ⟨hTc, hTw⟩ := mediumFamily_geometry T hT
    have hs := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.support_grid_image
      B hB j e heB T
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩,
      hmissing T hT⟩, ?_⟩
    · intro x hx
      obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    · rw [card_image_of_injective _ he, hTc]
    · rw [hs, card_image_of_injective _ hj, hTw]
  have h := card_le_card hsub
  rwa [card_image_of_injective _ (image_injective he), mediumFamily_card] at h

/-- Actual-family final Case II.2(v) bound. The six low hubs are supplied
upstream by minimum-gap completion; they remain literal trace memberships.
The indexed no-four premise is discharged from the original matching-free H. -/
theorem actual_twelve_missing_width_two {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hAB : ∀ i j : Fin 3, i ≠ j →
      ({e (i, 0), e (j, 1)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A))
    (hhub : ∀ h : Fin 3 × Fin 3, h.2 < 2 →
      G ∪ {e h} ∈ H.image (fun S => S ∩ A)) :
    12 ≤ (((region G B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
      (fun S => (support B S).card = 2)).card := by
  classical
  let U := region G B (univ.image j)
  let F := (H.image (fun S => S ∩ A)).filter (fun S => S ⊆ U)
  have hsub (X : Finset (Fin 3 × Fin 3)) : X.image e ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hdG : Disjoint G (univ.image e) := by
    apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (j i)) hxG (heB i a)
  have hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro f hf
    apply Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree G B hBH hBA hBd hGB (univ.image j)
      (by rw [Fintype.card_prod, Fintype.card_bool, card_image_of_injective _ hj,
        card_univ, Fintype.card_fin]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  apply twelve_le_missing_width_two G B hBd j hj e he heB (H.image (fun S => S ∩ A))
  intro S hS hST
  apply mediumFamily_missing e he G hdG F hno
    (fun i j hij => mem_filter.mpr ⟨by simpa [abPair] using hAB i j hij, hsub _⟩)
    (fun h hh => mem_filter.mpr ⟨hhub h hh,
      union_subset subset_union_left (by simpa using hsub {h})⟩) S hS
  exact mem_filter.mpr ⟨hST, hsub S⟩

end Submissions.Erdos1020MatchingRankThreeTwelveMedium.Main

namespace Submissions.Erdos1020MatchingRankThreeNoAC.Main

open Finset
open Submissions.Erdos1020MatchingRankThreeLowGraph.Main
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeGridPairs.Main

/-- The finite low graph supplies the Case II scalar alternatives. The final
full-graph medium count is explicit here for the actual-family adapter. -/
theorem count_alternatives (P : Finset (Finset (Fin 3 × Fin 3)))
    (hP : P ⊆ lowPairs) {d2 d3 : ℕ} (hwide : 4 + (active P).card ≤ d3)
    (hmedium : P = lowPairs → 12 ≤ d2) :
    (P.card ≤ 6 ∧ 4 ≤ d3) ∨ (P.card ≤ 7 ∧ 5 ≤ d3) ∨
      (P.card ≤ 10 ∧ 6 ≤ d3) ∨ (P.card ≤ 11 ∧ 7 ≤ d3) ∨
      (P.card ≤ 12 ∧ 7 ≤ d3 ∧ 12 ≤ d2) := by
  have hPc : P.card ≤ 12 := by
    simpa only [lowPairs_card] using card_le_card hP
  by_cases h6 : P.card ≤ 6
  · exact Or.inl ⟨h6, by omega⟩
  by_cases h7 : P.card ≤ 7
  · have ha := one_le_active_card P hP (by omega)
    exact Or.inr (Or.inl ⟨h7, by omega⟩)
  by_cases h8 : P.card ≤ 8
  · have ha := two_le_active_card P hP (by omega)
    exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have ha := three_le_active_card P hP (by omega)
  by_cases h11 : P.card ≤ 11
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h11, by omega⟩)))
  have heq : P = lowPairs := eq_of_subset_of_card_le hP (by rw [lowPairs_card]; omega)
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hPc, by omega, hmedium heq⟩)))

/-- In the actual no-top-pair branch the graph alternatives, including the
last twelve-medium count, follow from the original matching-free family. -/
theorem actual_counts {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ H.image (fun S => S ∩ A))
    (hcover : ∀ S ∈ H.image (fun S => S ∩ A), ∀ T ∈ H.image (fun S => S ∩ A),
      S ∪ T ≠ univ.image (e ∘ Submissions.Erdos1020MatchingRankThreeActiveWide.Main.upperBoard))
    (hnotop : ∀ i j : Fin 3, i ≠ j → ∀ a b : Fin 3, a = 2 ∨ b = 2 →
      ({e (i, a), e (j, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A)) :
    let T := H.image (fun S => S ∩ A)
    let U := region G B (univ.image j)
    let p2 := (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 2)).card
    let d2 := ((U.powersetCard 3 \ T).filter (fun S => (support B S).card = 2)).card
    let d3 := ((U.powersetCard 3 \ T).filter (fun S => (support B S).card = 3)).card
    (p2 ≤ 6 ∧ 4 ≤ d3) ∨ (p2 ≤ 7 ∧ 5 ≤ d3) ∨ (p2 ≤ 10 ∧ 6 ≤ d3) ∨
      (p2 ≤ 11 ∧ 7 ≤ d3) ∨ (p2 ≤ 12 ∧ 7 ≤ d3 ∧ 12 ≤ d2) := by
  classical
  dsimp only
  let T := H.image (fun S => S ∩ A)
  let P := presentPairs e T
  have hBe (i : Fin 3) : B (j i) = univ.image (fun a => e (i, a)) := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      exact heB i a
    · have hi : Function.Injective (fun a => e (i, a)) :=
        fun a b h => congrArg Prod.snd (he h)
      rw [hH _ (hBH _), card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  have hcard := local_pairs_card G B hBd hGB j hj e he heB hBe T
  have hP : P ⊆ lowPairs := presentPairs_subset_lowPairs e T hnotop
  have hPT : ∀ Q ∈ P, Q.image e ∈ T := fun Q hQ => (mem_filter.mp hQ).2
  have hwide := Submissions.Erdos1020MatchingRankThreeActiveTrace.Main.actual_four_plus_active
    H A hH hA hcut hstable hfree G B hBH hBA hBd hGB j hj e he heB hhub hcover P hP hPT
  have hmedium : P = lowPairs → 12 ≤
      (((region G B (univ.image j)).powersetCard 3 \ T).filter
        (fun S => (support B S).card = 2)).card := by
    intro heq
    apply Submissions.Erdos1020MatchingRankThreeTwelveMedium.Main.actual_twelve_missing_width_two
      H A hH hA hcut hstable hfree G B hBH hBA hBd hGB j hj e he heB
    · intro i l hil
      have hfinite : ∀ i l : Fin 3, i ≠ l →
          ({(i, 0), (l, 1)} : Finset (Fin 3 × Fin 3)) ∈ lowPairs := by decide
      have hpair := hPT {(i, 0), (l, 1)} (heq.symm ▸ hfinite i l hil)
      simpa only [image_insert, image_singleton] using hpair
    · intro x hx
      exact hhub x (mem_filter.mpr ⟨mem_univ _, hx⟩)
  have h := count_alternatives P hP hwide hmedium
  have hcard' : P.card = (T.filter (fun S => S ⊆ region G B (univ.image j) ∧
      S.card = 2 ∧ (support B S).card = 2)).card := hcard.symm
  rw [hcard'] at h
  simpa only [T] using h

end Submissions.Erdos1020MatchingRankThreeNoAC.Main

namespace Submissions.Erdos1020MatchingRankThreeRelabel.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- Permute columns while retaining every height within its column. -/
def relabel {α β : Type*} (σ : Equiv.Perm (Fin 3)) (e : Fin 3 × β → α) :
    Fin 3 × β → α := fun p => e (σ p.1, p.2)

theorem relabel_injective {α β : Type*} (σ : Equiv.Perm (Fin 3))
    (e : Fin 3 × β → α) (he : Function.Injective e) :
    Function.Injective (relabel σ e) := by
  intro p q h
  have hpq := he h
  have hfst : σ p.1 = σ q.1 := congrArg Prod.fst hpq
  have hsnd := congrArg (fun z : Fin 3 × β => z.2) hpq
  exact Prod.ext (σ.injective hfst) hsnd

theorem selected_image {α : Type*} [DecidableEq α]
    (σ : Equiv.Perm (Fin 3)) (J : Fin 3 → α) :
    univ.image (J ∘ σ) = univ.image J := by
  ext x
  constructor
  · rintro hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨σ i, mem_univ _, rfl⟩
  · rintro hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨σ.symm i, mem_univ _, by simp⟩

/-- A column permutation preserves the actual board vertex set. -/
theorem grid_image {α β : Type*} [DecidableEq α] [Fintype β]
    (σ : Equiv.Perm (Fin 3)) (e : Fin 3 × β → α) :
    univ.image (relabel σ e) = univ.image e := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨(σ i, a), mem_univ _, rfl⟩
  · intro hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨(σ.symm i, a), mem_univ _, by simp [relabel]⟩

theorem region_relabel {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (σ : Equiv.Perm (Fin 3)) (J : Fin 3 → Fin s) :
    region G B (univ.image (J ∘ σ)) = region G B (univ.image J) := by
  rw [selected_image]

end Submissions.Erdos1020MatchingRankThreeRelabel.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseClassify.Main

open Finset

-- A closed computable enumeration keeps kernel decision proofs free of local instances.
local instance : Fintype (Equiv.Perm (Fin 3)) := fintypePerm

/-- The six possible directed AC indices, with the source column different
from the target column. Membership is not an actual-trace assumption here. -/
def offDiagonal : Finset (Fin 3 × Fin 3) :=
  univ.filter (fun p => p.1 ≠ p.2)

theorem offDiagonal_card : offDiagonal.card = 6 := by decide

/-- Any two different columns can be the first two columns of a permutation. -/
theorem exists_perm_zero_one (i j : Fin 3) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
  have h : ∀ i j : Fin 3, i ≠ j →
      ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by decide +kernel
  exact h i j hij

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- The certificate examines only the 64 subsets of the six directed indices,
using the explicit six-permutation enumeration. -/
private theorem classification_certificate : ∀ P ∈ offDiagonal.powerset,
    ∃ σ : Equiv.Perm (Fin 3),
      (∃ p q : Fin 3, p ≠ q ∧ (σ 0, σ p) ∈ P ∧ (σ 1, σ q) ∈ P) ∨
      P = {(σ 0, σ 1), (σ 2, σ 1)} ∨
      P = {(σ 1, σ 0), (σ 1, σ 2)} ∨
      P = {(σ 0, σ 1)} ∨ P = ∅ := by
  decide +kernel

/-- Up to one column permutation, an arbitrary AC-index family contains two
disjoint AC edges, is one of the two two-edge stars, is a singleton, or is empty.
The first branch retains the two distinct target indices explicitly. -/
theorem classify (P : Finset (Fin 3 × Fin 3)) (hP : P ⊆ offDiagonal) :
    ∃ σ : Equiv.Perm (Fin 3),
      (∃ p q : Fin 3, p ≠ q ∧ (σ 0, σ p) ∈ P ∧ (σ 1, σ q) ∈ P) ∨
      P = {(σ 0, σ 1), (σ 2, σ 1)} ∨
      P = {(σ 1, σ 0), (σ 1, σ 2)} ∨
      P = {(σ 0, σ 1)} ∨ P = ∅ :=
  classification_certificate P (mem_powerset.mpr hP)

end Submissions.Erdos1020MatchingRankThreeCaseClassify.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseTwo.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeLowGraph.Main
open Submissions.Erdos1020MatchingRankThreeActiveWide.Main
open Submissions.Erdos1020MatchingRankThreeRelabel.Main
open Submissions.Erdos1020MatchingRankThreeCaseClassify.Main

def Alternatives (p2 d2 d3 : ℕ) : Prop :=
  (p2 ≤ 18 ∧ 12 ≤ d3) ∨ (p2 ≤ 10 ∧ 6 ≤ d3) ∨
  (p2 ≤ 5 ∧ 4 ≤ d3) ∨ (p2 ≤ 6 ∧ 4 ≤ d3) ∨
  (p2 ≤ 7 ∧ 5 ≤ d3) ∨ (p2 ≤ 11 ∧ 7 ≤ d3) ∨
  (p2 ≤ 12 ∧ 7 ≤ d3 ∧ 12 ≤ d2)

/-- Exhaust the actual AC configurations after excluding barred BC. All
seven count alternatives are derived; hubs remain explicit actual traces. -/
theorem actual_counts {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (J : Fin 3 → Fin s) (hJ : Function.Injective J)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (J i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hhub : ∀ x ∈ lowVertices, G ∪ {e x} ∈ H.image (fun S => S ∩ A))
    (htophub : ∀ i l : Fin 3, i ≠ l →
      ({e (i, 0), e (l, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) →
      G ∪ {e (l, 2)} ∈ H.image (fun S => S ∩ A))
    (hcover : ∀ S ∈ H.image (fun S => S ∩ A), ∀ T ∈ H.image (fun S => S ∩ A),
      S ∪ T ≠ univ.image (e ∘ upperBoard))
    (hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A)) :
    let T := H.image (fun S => S ∩ A)
    let U := region G B (univ.image J)
    Alternatives (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 2)).card
      ((U.powersetCard 3 \ T).filter (fun S => (support B S).card = 2)).card
      ((U.powersetCard 3 \ T).filter (fun S => (support B S).card = 3)).card := by
  classical
  let T := H.image (fun S => S ∩ A)
  let P := offDiagonal.filter (fun p => ({e (p.1, 0), e (p.2, 2)} : Finset (Fin n)) ∈ T)
  obtain ⟨σ, hcase⟩ := classify P (filter_subset _ _)
  let J' := J ∘ σ
  let e' := relabel σ e
  have hJ' : Function.Injective J' := hJ.comp σ.injective
  have he' : Function.Injective e' := relabel_injective σ e he
  have heB' : ∀ i a, e' (i, a) ∈ B (J' i) := fun i a => heB (σ i) a
  have hrow' : ∀ i, StrictMono (fun a : Fin 3 => e' (i, a)) := fun i => hrow (σ i)
  have hreg : region G B (univ.image J') = region G B (univ.image J) := region_relabel G B σ J
  have hupp : univ.image (e' ∘ upperBoard) = univ.image (e ∘ upperBoard) := by
    exact grid_image σ (e ∘ upperBoard)
  have hcover' : ∀ S ∈ T, ∀ Q ∈ T, S ∪ Q ≠ univ.image (e' ∘ upperBoard) := by
    simpa only [hupp] using hcover
  have hhub' : ∀ x ∈ lowVertices, G ∪ {e' x} ∈ T := by
    intro x hx
    exact hhub (σ x.1, x.2) (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩)
  have hbar' : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e' (i, a), e' (l, b)} : Finset (Fin n)) ∉ T :=
    fun i l hil a b ha hb hab => hbar (σ i) (σ l) (fun h => hil (σ.injective h)) a b ha hb hab
  have hmem (i l : Fin 3) (hil : i ≠ l)
      (h : ({e' (i, 0), e' (l, 2)} : Finset (Fin n)) ∈ T) : (σ i, σ l) ∈ P :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, fun h => hil (σ.injective h)⟩, h⟩
  have htrace (i l : Fin 3) (h : (σ i, σ l) ∈ P) :
      ({e' (i, 0), e' (l, 2)} : Finset (Fin n)) ∈ T := (mem_filter.mp h).2
  have hmid (i : Fin 3) : G ∪ {e' (i, 1)} ∈ T :=
    hhub' (i, 1) (mem_filter.mpr ⟨mem_univ _, by change (1 : Fin 3) < 2; decide⟩)
  change Alternatives _ _ _
  rcases hcase with htwo | hcommon | hbottom | hsole | hnone
  · obtain ⟨p, q, hpq, hP, hQ⟩ := htwo
    have h := Submissions.Erdos1020MatchingRankThreeACTwo.Main.actual_counts
      H A hH hA hcut hstable hfree G B hBH hBA hBd hGB J' hJ' e' he' heB' hrow'
      hbar' p q hpq (htrace 0 p hP) (htrace 1 q hQ) (hmid 2)
    exact Or.inl (by simpa only [hreg] using h)
  · have hAC : ∀ i l : Fin 3, i ≠ l →
        ({e' (i, 0), e' (l, 2)} : Finset (Fin n)) ∈ T → (i = 0 ∨ i = 2) ∧ l = 1 := by
      intro i l hil h
      have hm := hmem i l hil h
      rw [hcommon] at hm
      simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hm
      rcases hm with ⟨hi, hl⟩ | ⟨hi, hl⟩
      · exact ⟨Or.inl (σ.injective hi), σ.injective hl⟩
      · exact ⟨Or.inr (σ.injective hi), σ.injective hl⟩
    have hP := htrace 0 1 (by rw [hcommon]; exact mem_insert_self _ _)
    have hQ := htrace 2 1 (by rw [hcommon]; exact mem_insert_of_mem (mem_singleton_self _))
    have h := Submissions.Erdos1020MatchingRankThreeACCommon.Main.actual_counts
      H A hH hA hcut hstable hfree G B hBH hBA hBd hGB J' hJ' e' he' heB' hrow'
      hbar' hAC hP hQ hmid
    exact Or.inr (Or.inl (by simpa only [hreg] using h))
  · have hAC : ∀ i l : Fin 3, i ≠ l →
        ({e' (i, 0), e' (l, 2)} : Finset (Fin n)) ∈ T → i = 1 ∧ (l = 0 ∨ l = 2) := by
      intro i l hil h
      have hm := hmem i l hil h
      rw [hbottom] at hm
      simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hm
      rcases hm with ⟨hi, hl⟩ | ⟨hi, hl⟩
      · exact ⟨σ.injective hi, Or.inl (σ.injective hl)⟩
      · exact ⟨σ.injective hi, Or.inr (σ.injective hl)⟩
    have hP := htrace 1 0 (by rw [hbottom]; exact mem_insert_self _ _)
    have hQ := htrace 1 2 (by rw [hbottom]; exact mem_insert_of_mem (mem_singleton_self _))
    have hh : ∀ x ∈ Submissions.Erdos1020MatchingRankThreeACFew.Main.commonHubs,
        G ∪ {e' x} ∈ T := by
      intro x hx
      rcases mem_union.mp hx with hl | ht
      · exact hhub' x hl
      · simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact htophub (σ 1) (σ 0) (σ.injective.ne (by decide)) hP
        · exact htophub (σ 1) (σ 2) (σ.injective.ne (by decide)) hQ
    have h := Submissions.Erdos1020MatchingRankThreeACFew.Main.common_bottom_actual_counts
      H A hH hA hcut hstable hfree G B hBH hBA hBd hGB J' hJ' e' he' heB' hrow'
      hbar' hAC hP hQ hh hcover'
    rcases h with h | h
    · exact Or.inr (Or.inl (by simpa only [hreg] using h))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [hreg] using h)))
  · have hAC : ∀ i l : Fin 3, i ≠ l →
        ({e' (i, 0), e' (l, 2)} : Finset (Fin n)) ∈ T → i = 0 ∧ l = 1 := by
      intro i l hil h
      have hm := hmem i l hil h
      rw [hsole] at hm
      have hp := Prod.mk.inj (mem_singleton.mp hm)
      exact ⟨σ.injective hp.1, σ.injective hp.2⟩
    have hP := htrace 0 1 (by rw [hsole]; exact mem_singleton_self _)
    have h := Submissions.Erdos1020MatchingRankThreeACFew.Main.sole_ac_actual_counts
      H A hH hA hcut hstable hfree G B hBH hBA hBd hGB J' hJ' e' he' heB' hrow'
      hbar' hAC hP hhub' hcover'
    rcases h with h | h
    · have h' : _ ≤ 10 ∧ _ := ⟨h.1.trans (by decide : 9 ≤ 10), h.2⟩
      exact Or.inr (Or.inl (by simpa only [hreg] using h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hreg] using h))))
  · have hAC : ∀ i l : Fin 3, i ≠ l →
        ({e' (i, 0), e' (l, 2)} : Finset (Fin n)) ∉ T := by
      intro i l hil h
      have hm := hmem i l hil h
      rw [hnone] at hm
      exact notMem_empty _ hm
    have hnotop : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, a = 2 ∨ b = 2 →
        ({e' (i, a), e' (l, b)} : Finset (Fin n)) ∉ T := by
      intro i l hil a b hab h
      rcases hab with rfl | rfl
      · by_cases hb : b = 0
        · exact hAC l i hil.symm (by simpa only [hb, pair_comm] using h)
        · exact hbar' i l hil 2 b (by decide) (by omega) (Or.inl rfl) h
      · by_cases ha : a = 0
        · exact hAC i l hil (by simpa only [ha] using h)
        · exact hbar' i l hil a 2 (by omega) (by decide) (Or.inr rfl) h
    have h := Submissions.Erdos1020MatchingRankThreeNoAC.Main.actual_counts
      H A hH hA hcut hstable hfree G B hBH hBA hBd hGB J' hJ' e' he' heB' hhub' hcover' hnotop
    rcases h with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hreg] using h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hreg] using h)))))
    · exact Or.inr (Or.inl (by simpa only [hreg] using h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hreg] using h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [hreg] using h))))))

end Submissions.Erdos1020MatchingRankThreeCaseTwo.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseTwoNumeric.Main

/-- A scalar budget converts explicit local counts to inequality (A). -/
theorem weighted_of_budget {s N p1 p2 d1 d2 d3 x y e : ℕ}
    (hN : 2 * N ≤ s + 2) (hp1 : p1 ≤ 9) (hnarrow : p1 ≤ d1)
    (hp2 : p2 ≤ x) (hd3 : y ≤ d3) (hd2 : e ≤ d2)
    (hbudget : (s + 2) * (s - 1) * x + 18 * s ≤
      2 * (s - 1) * (s - 2) * y + 2 * (s - 1) * e) :
    N * ((s - 1) * p2 + 2 * p1) ≤
      (s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1 := by
  have hcount : (s - 1) * p2 + 2 * p1 ≤ (s - 1) * x + 2 * p1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left (s - 1) hp2) _
  have hsmall : (s + 2) * ((s - 1) * x + 2 * p1) ≤
      (s + 2) * (s - 1) * x + 18 * s + 4 * d1 := by
    nlinarith only [Nat.mul_le_mul_left s hp1, hnarrow]
  have hlarge : (s + 2) * (s - 1) * x + 18 * s + 4 * d1 ≤
      2 * ((s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1) := by
    nlinarith only [hbudget, Nat.mul_le_mul_left ((s - 1) * (s - 2)) hd3,
      Nat.mul_le_mul_left (s - 1) hd2]
  have htwice : 2 * (N * ((s - 1) * p2 + 2 * p1)) ≤
      2 * ((s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1) := by
    calc
      _ ≤ 2 * (N * ((s - 1) * x + 2 * p1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left N hcount)
      _ = (2 * N) * ((s - 1) * x + 2 * p1) := by ring
      _ ≤ (s + 2) * ((s - 1) * x + 2 * p1) := Nat.mul_le_mul_right _ hN
      _ ≤ (s + 2) * (s - 1) * x + 18 * s + 4 * d1 := hsmall
      _ ≤ _ := hlarge
  omega

/-- The seven remaining Case II count alternatives share the explicit cutoff32.
The alternatives are premises here; actual-family lemmas must supply them. -/
theorem case_two_weighted_comparison {s N p1 p2 d1 d2 d3 : ℕ}
    (hs : 32 ≤ s) (hN : 2 * N ≤ s + 2)
    (hp1 : p1 ≤ 9) (hnarrow : p1 ≤ d1)
    (hcounts : (p2 ≤ 18 ∧ 12 ≤ d3) ∨ (p2 ≤ 10 ∧ 6 ≤ d3) ∨
      (p2 ≤ 5 ∧ 4 ≤ d3) ∨ (p2 ≤ 6 ∧ 4 ≤ d3) ∨
      (p2 ≤ 7 ∧ 5 ≤ d3) ∨ (p2 ≤ 11 ∧ 7 ≤ d3) ∨
      (p2 ≤ 12 ∧ 7 ≤ d3 ∧ 12 ≤ d2)) :
    N * ((s - 1) * p2 + 2 * p1) ≤
      (s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1 := by
  have hs1 : s - 1 + 1 = s := by omega
  have hs2 : s - 2 + 2 = s := by omega
  have hss : 32 * s ≤ s * s := Nat.mul_le_mul_right s hs
  rcases hcounts with h | h | h | h | h | h | h
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2 (Nat.zero_le d2)
    nlinarith only [hs1, hs2, hss, hs]
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2 (Nat.zero_le d2)
    nlinarith only [hs1, hs2, hss, hs]
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2 (Nat.zero_le d2)
    nlinarith only [hs1, hs2, hss, hs]
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2 (Nat.zero_le d2)
    nlinarith only [hs1, hs2, hss, hs]
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2 (Nat.zero_le d2)
    nlinarith only [hs1, hs2, hss, hs]
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2 (Nat.zero_le d2)
    nlinarith only [hs1, hs2, hss, hs]
  · apply weighted_of_budget hN hp1 hnarrow h.1 h.2.1 h.2.2
    nlinarith only [hs1, hs2, hss, hs]

end Submissions.Erdos1020MatchingRankThreeCaseTwoNumeric.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseTwoWeighted.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeLowGraph.Main
open Submissions.Erdos1020MatchingRankThreeActiveWide.Main

/-- The literal local comparison (A) in Case II. The actual-family classifier
supplies all seven count alternatives; the actual narrow bound supplies both
width-one inequalities. Only structural trace hypotheses remain explicit. -/
theorem actual_weighted_comparison {n s N : ℕ}
    (hs : 32 ≤ s) (hN : 2 * N ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hhub : ∀ x ∈ lowVertices, {v, d} ∪ {e x} ∈ H.image (fun S => S ∩ A))
    (htophub : ∀ i l : Fin 3, i ≠ l →
      ({e (i, 0), e (l, 2)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) →
      {v, d} ∪ {e (l, 2)} ∈ H.image (fun S => S ∩ A))
    (hcover : ∀ S ∈ H.image (fun S => S ∩ A), ∀ T ∈ H.image (fun S => S ∩ A),
      S ∪ T ≠ univ.image (e ∘ upperBoard))
    (hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
      ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A)) :
    N * ((s - 1) *
        ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
          S.card = 2 ∧ (support B S).card = 2)).card +
      2 * ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
        S.card = 2 ∧ (support B S).card = 1)).card) ≤
      (s - 1) * (s - 2) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 3)).card +
      (s - 1) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 2)).card +
      2 * (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 1)).card := by
  have hMc : (univ.image j).card = 3 := by
    rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have hnarrow := Submissions.Erdos1020MatchingRankThreeWidthOne.Main.actual_width_one_bounds
    H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB
    (univ.image j) hMc
  have hcounts := Submissions.Erdos1020MatchingRankThreeCaseTwo.Main.actual_counts
    H A hH hA hcut hstable hfree {v, d} B hBH hBA hBd hGB j hj e he heB hrow
    hhub htophub hcover hbar
  exact Submissions.Erdos1020MatchingRankThreeCaseTwoNumeric.Main.case_two_weighted_comparison
    hs hN hnarrow.2 hnarrow.1 hcounts

end Submissions.Erdos1020MatchingRankThreeCaseTwoWeighted.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseOne.Main

open Finset

/-- The Case I union condition already forces the two trace sets to be
disjoint, since every rank-three trace has at most three vertices. -/
theorem disjoint_of_union_card_six {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hP : P.card ≤ 3) (hQ : Q.card ≤ 3)
    (hunion : (P ∪ Q).card = 6) : Disjoint P Q := by
  have h := card_union_add_card_inter P Q
  have hc : (P ∩ Q).card = 0 := by omega
  exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hc)

/-- Two disjoint upper members, together with every gap-plus-bottom triple,
exclude every pair of bottom vertices. The upper members are only required
to avoid the gap and the three bottoms. -/
theorem bottom_pair_missing {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (G : Finset α) (a : Fin 3 → α) (ha : Function.Injective a)
    (hGa : Disjoint G (univ.image a))
    (P Q : Finset α) (hP : P ∈ F) (hQ : Q ∈ F) (hPQ : Disjoint P Q)
    (hPU : Disjoint P (G ∪ univ.image a))
    (hQU : Disjoint Q (G ∪ univ.image a))
    (hbottom : ∀ i, insert (a i) G ∈ F)
    (i j : Fin 3) (hij : i ≠ j) : ({a i, a j} : Finset α) ∉ F := by
  classical
  obtain ⟨k, _, hk⟩ := exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin 3))) (t := univ)
    (by simp only [card_pair hij, card_univ, Fintype.card_fin]; decide)
  have hki : k ≠ i := fun h => hk (by simp [h])
  have hkj : k ≠ j := fun h => hk (by simp [h])
  have hai (l : Fin 3) : a l ∈ univ.image a := mem_image.mpr ⟨l, mem_univ _, rfl⟩
  have haG (l : Fin 3) : a l ∉ G := fun h => disjoint_left.mp hGa h (hai l)
  have hRsub : insert (a k) G ⊆ G ∪ univ.image a := by
    apply insert_subset
    · exact mem_union_right _ (hai k)
    · exact subset_union_left
  have hTsub : ({a i, a j} : Finset α) ⊆ G ∪ univ.image a := by
    apply insert_subset
    · exact mem_union_right _ (hai i)
    · exact singleton_subset_iff.mpr (mem_union_right _ (hai j))
  have hRT : Disjoint (insert (a k) G) ({a i, a j} : Finset α) := by
    apply disjoint_right.mpr
    intro x hxT hxR
    simp only [mem_insert, mem_singleton] at hxT
    rcases hxT with rfl | rfl
    · rcases mem_insert.mp hxR with h | h
      · exact hki ((ha h).symm)
      · exact haG i h
    · rcases mem_insert.mp hxR with h | h
      · exact hkj ((ha h).symm)
      · exact haG j h
  exact Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    P Q (insert (a k) G) {a i, a j} hP hQ (hbottom k) hPQ
    (hPU.mono (Subset.refl _) hRsub) (hQU.mono (Subset.refl _) hRsub)
    (hPU.mono (Subset.refl _) hTsub) (hQU.mono (Subset.refl _) hTsub) hRT

/-- Any trace pair meeting two different labeled rows can be lowered to the
two row minima. Only within-row order is used. -/
theorem lower_pair_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (i j : Fin 3) (hij : i ≠ j) (a b : Fin 3)
    (hP : ({e (i, a), e (j, b)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A)) :
    ({e (i, 0), e (j, 0)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) := by
  have hcross (c d : Fin 3) : e (i, c) ≠ e (j, d) :=
    fun h => hij (congrArg Prod.fst (he h))
  have h1 : ({e (i, 0), e (j, b)} : Finset (Fin n)) ∈ H.image (fun S => S ∩ A) := by
    by_cases ha : a = 0
    · simpa only [ha] using hP
    · have hlt : (0 : Fin 3) < a := by omega
      have hne : e (i, 0) ≠ e (i, a) := (hrow i hlt).ne
      have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable {e (i, a), e (j, b)} hP (e (i, 0)) (e (i, a))
        (heA _) (hrow i hlt) (by simp) (by simp [hne, hcross])
      simpa [hcross] using h
  by_cases hb : b = 0
  · simpa only [hb] using h1
  · have hlt : (0 : Fin 3) < b := by omega
    have hne : e (j, 0) ≠ e (j, b) := (hrow j hlt).ne
    have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable {e (i, 0), e (j, b)} h1 (e (j, 0)) (e (j, b))
      (heA _) (hrow j hlt) (by simp) (by simp [hne, (hcross 0 0).symm])
    have hlast : insert (e (j, 0)) ({e (i, 0)} : Finset (Fin n)) ∈
        H.image (fun S => S ∩ A) := by
      simpa only [erase_insert_of_ne (hcross 0 b), erase_singleton, Finset.insert_empty] using h
    exact (pair_comm (e (j, 0)) (e (i, 0))) ▸ hlast

/-- The abstract no-wide-pair argument applied to the actual trace family.
The local no-four-matching and the bottom triples remain explicit premises;
their checked actual-hypergraph adapters are separate dependencies. -/
theorem row_pair_missing {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heA : ∀ p, e p ∈ A) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (F : Finset (Finset (Fin n)))
    (hFtrace : F ⊆ H.image (fun S => S ∩ A))
    (htraceF : ∀ i j : Fin 3, ({e (i, 0), e (j, 0)} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) → ({e (i, 0), e (j, 0)} : Finset (Fin n)) ∈ F)
    (hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (G : Finset (Fin n)) (hGe : Disjoint G (univ.image e))
    (P Q : Finset (Fin n)) (hP : P ∈ F) (hQ : Q ∈ F) (hPQ : Disjoint P Q)
    (hPU : Disjoint P (G ∪ univ.image (fun i : Fin 3 => e (i, 0))))
    (hQU : Disjoint Q (G ∪ univ.image (fun i : Fin 3 => e (i, 0))))
    (hbottom : ∀ i : Fin 3, insert (e (i, 0)) G ∈ F)
    (i j : Fin 3) (hij : i ≠ j) (a b : Fin 3) :
    ({e (i, a), e (j, b)} : Finset (Fin n)) ∉ F := by
  have ha : Function.Injective (fun i : Fin 3 => e (i, 0)) :=
    fun i j h => congrArg Prod.fst (he h)
  have hGbottom : Disjoint G (univ.image (fun i : Fin 3 => e (i, 0))) := by
    apply hGe.mono (Subset.refl _)
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨(i, 0), mem_univ _, rfl⟩
  have hmissing := bottom_pair_missing F hno G (fun i => e (i, 0)) ha hGbottom
    P Q hP hQ hPQ hPU hQU hbottom i j hij
  intro hpair
  exact hmissing (htraceF i j (lower_pair_trace H A hstable e he heA hrow i j hij a b
    (hFtrace hpair)))

/-- Absence of all two-row pairs is exactly sufficient to empty the width-two
pair filter. This lemma works for arbitrary pairwise disjoint blocks. -/
theorem width_two_pairs_eq_empty {α : Type*} [DecidableEq α] {s : ℕ}
    (F : Finset (Finset α)) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hmissing : ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, ({x, y} : Finset α) ∉ F) :
    F.filter (fun S => S.card = 2 ∧
      (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 2) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSF, hSc, hwidth⟩ := mem_filter.mp hS
  obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (show 1 <
    (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card by omega)
  obtain ⟨x, hx⟩ := (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B S i).mp hi
  obtain ⟨y, hy⟩ := (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B S j).mp hj
  have hxS := (mem_inter.mp hx).1
  have hxB := (mem_inter.mp hx).2
  have hyS := (mem_inter.mp hy).1
  have hyB := (mem_inter.mp hy).2
  have hxy : x ≠ y := fun h => disjoint_left.mp (hB hij) hxB (h.symm ▸ hyB)
  have hpair : ({x, y} : Finset α) = S := by
    apply eq_of_subset_of_card_le
    · exact insert_subset hxS (singleton_subset_iff.mpr hyS)
    · rw [hSc, card_pair hxy]
  exact hmissing i j hij x hxB y hyB (hpair.symm ▸ hSF)

/-- The same empty-filter conclusion with the actual selected-region
predicate. Only two-row pairs whose rows are selected need to be excluded. -/
theorem local_width_two_pairs_eq_empty {α : Type*} [DecidableEq α] {s : ℕ}
    (F : Finset (Finset α)) (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (M : Finset (Fin s))
    (hmissing : ∀ i ∈ M, ∀ j ∈ M, i ≠ j →
      ∀ x ∈ B i, ∀ y ∈ B j, ({x, y} : Finset α) ∉ F) :
    F.filter (fun S => S ⊆ Submissions.Erdos1020MatchingBlockSupport.Main.region G B M ∧
      S.card = 2 ∧ (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 2) = ∅ := by
  classical
  let U := Submissions.Erdos1020MatchingBlockSupport.Main.region G B M
  have hU : U ⊆ G ∪ univ.biUnion B := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact mem_union_left _ hx
    · obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, hxi⟩)
  have hlocal : ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j,
      ({x, y} : Finset α) ∉ F.filter (fun S => S ⊆ U) := by
    intro i j hij x hxi y hyj hpair
    obtain ⟨hpairF, hpairU⟩ := mem_filter.mp hpair
    have hs := (Submissions.Erdos1020MatchingBlockSupport.Main.subset_region_iff
      G B hB hG {x, y} (hpairU.trans hU) M).mp hpairU
    have hi : i ∈ Submissions.Erdos1020MatchingBlockSupport.Main.support B {x, y} :=
      (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ i).mpr
        ⟨x, mem_inter.mpr ⟨by simp, hxi⟩⟩
    have hj : j ∈ Submissions.Erdos1020MatchingBlockSupport.Main.support B {x, y} :=
      (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ j).mpr
        ⟨y, mem_inter.mpr ⟨by simp, hyj⟩⟩
    exact hmissing i (hs hi) j (hs hj) hij x hxi y hyj hpairF
  have h := width_two_pairs_eq_empty (F.filter (fun S => S ⊆ U)) B hB hlocal
  simpa only [filter_filter, and_assoc, U] using h

/-- One active row excludes the medium seed supported on the other two rows.
Upward propagation and counting its nine majorants are separate next steps. -/
theorem medium_seed_missing {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hno : ∀ f : Bool × Bool → Finset α, (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)))
    (v d : α) (hvd : v ≠ d) (a : Fin 3 → α) (ha : Function.Injective a)
    (hGa : Disjoint ({v, d} : Finset α) (univ.image a))
    (P Q : Finset α) (hP : P ∈ F) (hQ : Q ∈ F) (hPQ : Disjoint P Q)
    (hPU : Disjoint P ({v, d} ∪ univ.image a))
    (hQU : Disjoint Q ({v, d} ∪ univ.image a))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hpair : ({v, a i} : Finset α) ∈ F) : ({d, a j, a k} : Finset α) ∉ F := by
  have hai (l : Fin 3) : a l ∈ univ.image a := mem_image.mpr ⟨l, mem_univ _, rfl⟩
  have hav (l : Fin 3) : a l ≠ v := fun h =>
    disjoint_left.mp hGa (by simp) (h ▸ hai l)
  have had (l : Fin 3) : a l ≠ d := fun h =>
    disjoint_left.mp hGa (by simp) (h ▸ hai l)
  have haij : a i ≠ a j := fun h => hij (ha h)
  have haik : a i ≠ a k := fun h => hik (ha h)
  have hRsub : ({v, a i} : Finset α) ⊆ {v, d} ∪ univ.image a := by
    exact insert_subset (mem_union_left _ (by simp))
      (singleton_subset_iff.mpr (mem_union_right _ (hai i)))
  have hTsub : ({d, a j, a k} : Finset α) ⊆ {v, d} ∪ univ.image a := by
    exact insert_subset (mem_union_left _ (by simp))
      (insert_subset (mem_union_right _ (hai j))
        (singleton_subset_iff.mpr (mem_union_right _ (hai k))))
  have hRT : Disjoint ({v, a i} : Finset α) {d, a j, a k} := by
    simp [Ne.symm hvd, Ne.symm (had i), hav j, hav k, Ne.symm haij, Ne.symm haik]
  exact Submissions.Erdos1020MatchingRankThreeBC.Main.missing_of_three F hno
    P Q {v, a i} {d, a j, a k} hP hQ hpair hPQ
    (hPU.mono (Subset.refl _) hRsub) (hQU.mono (Subset.refl _) hRsub)
    (hPU.mono (Subset.refl _) hTsub) (hQU.mono (Subset.refl _) hTsub) hRT

end Submissions.Erdos1020MatchingRankThreeCaseOne.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseOneMajorants.Main

open Finset

/-- A medium certificate has the gap vertex and one vertex in each of two rows. -/
def mediumTriple {α : Type*} [DecidableEq α]
    (d : α) (e : Fin 3 × Fin 3 → α) (j k : Fin 3) (p : Fin 3 × Fin 3) : Finset α :=
  {d, e (j, p.1), e (k, p.2)}

theorem mediumTriple_injective {α : Type*} [DecidableEq α]
    (d : α) (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (hd : d ∉ univ.image e) (j k : Fin 3) (hjk : j ≠ k) :
    Function.Injective (mediumTriple d e j k) := by
  have hde (p : Fin 3 × Fin 3) : e p ≠ d := fun h =>
    hd (mem_image.mpr ⟨p, mem_univ _, h⟩)
  intro p q hpq
  have hfirst : p.1 = q.1 := by
    have hm : e (j, p.1) ∈ mediumTriple d e j k q := hpq ▸ (by simp [mediumTriple])
    rcases mem_insert.mp hm with h | h
    · exact (hde _ h).elim
    · simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact congrArg Prod.snd (he h)
      · exact (hjk (congrArg Prod.fst (he h))).elim
  have hsecond : p.2 = q.2 := by
    have hm : e (k, p.2) ∈ mediumTriple d e j k q := hpq ▸ (by simp [mediumTriple])
    rcases mem_insert.mp hm with h | h
    · exact (hde _ h).elim
    · simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact (hjk (congrArg Prod.fst (he h)).symm).elim
      · simpa only using congrArg Prod.snd (@he (k, p.2) (k, q.2) h)
  exact Prod.ext hfirst hsecond

theorem mediumTriple_card {α : Type*} [DecidableEq α]
    (d : α) (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (hd : d ∉ univ.image e) (j k : Fin 3) (hjk : j ≠ k) (p : Fin 3 × Fin 3) :
    (mediumTriple d e j k p).card = 3 := by
  have hde (q : Fin 3 × Fin 3) : d ≠ e q := fun h =>
    hd (mem_image.mpr ⟨q, mem_univ _, h.symm⟩)
  have hcross : e (j, p.1) ≠ e (k, p.2) := fun h => hjk (congrArg Prod.fst (he h))
  simp [mediumTriple, hde, hcross]

theorem nine_card {α : Type*} [DecidableEq α]
    (d : α) (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (hd : d ∉ univ.image e) (j k : Fin 3) (hjk : j ≠ k) :
    (univ.image (mediumTriple d e j k)).card = 9 := by
  rw [card_image_of_injective _ (mediumTriple_injective d e he hd j k hjk),
    card_univ, Fintype.card_prod, Fintype.card_fin]

/-- Any present medium majorant lowers to the seed. The gap vertex stays fixed;
no comparison between that vertex and the rows is needed. -/
theorem majorant_missing_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (d : Fin n) (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (hd : d ∉ univ.image e) (heA : ∀ p, e p ∈ A)
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (j k : Fin 3) (hjk : j ≠ k)
    (hseed : mediumTriple d e j k (0, 0) ∉ H.image (fun S => S ∩ A))
    (p : Fin 3 × Fin 3) : mediumTriple d e j k p ∉ H.image (fun S => S ∩ A) := by
  intro hP
  have hde (q : Fin 3 × Fin 3) : d ≠ e q := fun h =>
    hd (mem_image.mpr ⟨q, mem_univ _, h.symm⟩)
  have hcross (a b : Fin 3) : e (j, a) ≠ e (k, b) :=
    fun h => hjk (congrArg Prod.fst (he h))
  have hfirst : ({d, e (j, 0), e (k, p.2)} : Finset (Fin n)) ∈
      H.image (fun S => S ∩ A) := by
    by_cases hp : p.1 = 0
    · simpa [mediumTriple, hp] using hP
    · have hlt : (0 : Fin 3) < p.1 := by omega
      have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable (mediumTriple d e j k p) hP (e (j, 0)) (e (j, p.1)) (heA _)
        (hrow j hlt) (by simp [mediumTriple])
        (by simp [mediumTriple, (hde (j, 0)).symm, (hrow j hlt).ne, hcross])
      have hlast : insert (e (j, 0)) ({d, e (k, p.2)} : Finset (Fin n)) ∈
          H.image (fun S => S ∩ A) := by
        simpa only [mediumTriple, erase_insert_of_ne (hde (j, p.1)),
          erase_insert (s := {e (k, p.2)}) (a := e (j, p.1)) (by simp [hcross])] using h
      exact (insert_comm (e (j, 0)) d {e (k, p.2)}) ▸ hlast
  by_cases hp : p.2 = 0
  · exact hseed (by simpa [mediumTriple, hp] using hfirst)
  · have hlt : (0 : Fin 3) < p.2 := by omega
    have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
      H A hstable {d, e (j, 0), e (k, p.2)} hfirst (e (k, 0)) (e (k, p.2)) (heA _)
      (hrow k hlt) (by simp)
      (by simp [(hde (k, 0)).symm, (hcross 0 0).symm, (hrow k hlt).ne])
    have hlast : insert (e (k, 0)) ({d, e (j, 0)} : Finset (Fin n)) ∈
        H.image (fun S => S ∩ A) := by
      simpa only [erase_insert_of_ne (hde (k, p.2)),
        erase_insert_of_ne (hcross 0 p.2), erase_singleton, Finset.insert_empty] using h
    have heq : insert (e (k, 0)) ({d, e (j, 0)} : Finset (Fin n)) =
        mediumTriple d e j k (0, 0) := by
      rw [insert_comm (e (k, 0)) d, pair_comm (e (k, 0)) (e (j, 0))]
      rfl
    exact hseed (heq ▸ hlast)

/-- The support of a medium certificate is exactly the two chosen row indices. -/
theorem mediumTriple_support {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (d : α) (hdG : d ∈ G)
    (J : Fin 3 → Fin s) (e : Fin 3 × Fin 3 → α)
    (heB : ∀ i a, e (i, a) ∈ B (J i)) (j k : Fin 3) (p : Fin 3 × Fin 3) :
    Submissions.Erdos1020MatchingBlockSupport.Main.support B (mediumTriple d e j k p) =
      {J j, J k} := by
  ext i
  constructor
  · intro hi
    obtain ⟨x, hx⟩ := (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ i).mp hi
    obtain ⟨hxT, hxB⟩ := mem_inter.mp hx
    rcases mem_insert.mp hxT with hxd | hxT
    · subst x
      exact (disjoint_left.mp (hG i) hdG hxB).elim
    · simp only [mem_insert, mem_singleton] at hxT
      rcases hxT with hxj | hxk
      · have hJi : J j = i := by
          by_contra hne
          exact disjoint_left.mp (hB hne) (heB j p.1) (hxj ▸ hxB)
        simp [hJi]
      · have hKi : J k = i := by
          by_contra hne
          exact disjoint_left.mp (hB hne) (heB k p.2) (hxk ▸ hxB)
        simp [hKi]
  · intro hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ _).mpr
        ⟨e (j, p.1), mem_inter.mpr ⟨by simp [mediumTriple], heB j p.1⟩⟩
    · exact (Submissions.Erdos1020MatchingBlockSupport.Main.mem_support B _ _).mpr
        ⟨e (k, p.2), mem_inter.mpr ⟨by simp [mediumTriple], heB k p.2⟩⟩

/-- Every missing medium majorant belongs to the literal missing width-two
triple filter in the selected three-block region. -/
theorem medium_candidates_subset {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (d : α) (hdG : d ∈ G)
    (J : Fin 3 → Fin s) (hJ : Function.Injective J)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (J i)) (j k : Fin 3) (hjk : j ≠ k)
    (F : Finset (Finset α)) (hmissing : ∀ p, mediumTriple d e j k p ∉ F) :
    univ.image (mediumTriple d e j k) ⊆
      (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image J)).powersetCard 3
        \ F).filter (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 2)) := by
  classical
  have hd : d ∉ univ.image e := by
    intro hd
    obtain ⟨⟨i, a⟩, _, hia⟩ := mem_image.mp hd
    exact disjoint_left.mp (hG (J i)) hdG (hia ▸ heB i a)
  intro S hS
  obtain ⟨p, _, rfl⟩ := mem_image.mp hS
  refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨?_,
    mediumTriple_card d e he hd j k hjk p⟩, hmissing p⟩, ?_⟩
  · have heU (i a : Fin 3) : e (i, a) ∈
        Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image J) :=
      mem_union_right _ (mem_biUnion.mpr
        ⟨J i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
    exact insert_subset (mem_union_left _ hdG)
      (insert_subset (heU j p.1) (singleton_subset_iff.mpr (heU k p.2)))
  · rw [mediumTriple_support G B hB hG d hdG J e heB j k p,
      card_pair (fun h => hjk (hJ h))]

/-- A single active row provides nine distinct missing medium triples. -/
theorem nine_missing_width_two {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hG : ∀ i, Disjoint G (B i)) (d : α) (hdG : d ∈ G)
    (J : Fin 3 → Fin s) (hJ : Function.Injective J)
    (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (J i)) (j k : Fin 3) (hjk : j ≠ k)
    (F : Finset (Finset α)) (hmissing : ∀ p, mediumTriple d e j k p ∉ F) :
    9 ≤ (((Submissions.Erdos1020MatchingBlockSupport.Main.region G B (univ.image J)).powersetCard 3
      \ F).filter (fun S => (Submissions.Erdos1020MatchingBlockSupport.Main.support B S).card = 2)).card := by
  have hd : d ∉ univ.image e := by
    intro hd
    obtain ⟨⟨i, a⟩, _, hia⟩ := mem_image.mp hd
    exact disjoint_left.mp (hG (J i)) hdG (hia ▸ heB i a)
  have h := card_le_card (medium_candidates_subset G B hB hG d hdG J hJ e he heB j k hjk F hmissing)
  rwa [nine_card d e he hd j k hjk] at h

/-- Certificates for different active rows cannot coincide because their
supports omit different selected rows. Thus the per-row nine counts add. -/
theorem nine_certificate_union_le {α : Type*} [DecidableEq α] {s : ℕ}
    (B : Fin s → Finset α) (M I : Finset (Fin s)) (hIM : I ⊆ M)
    (C : Fin s → Finset (Finset α)) (D : Finset (Finset α))
    (hCcard : ∀ i ∈ I, (C i).card = 9) (hCD : ∀ i ∈ I, C i ⊆ D)
    (hsupport : ∀ i ∈ I, ∀ S ∈ C i,
      Submissions.Erdos1020MatchingBlockSupport.Main.support B S = M.erase i) :
    9 * I.card ≤ D.card := by
  classical
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro S hSi hSj
    have heq : M.erase i = M.erase j := (hsupport i hi S hSi).symm.trans (hsupport j hj S hSj)
    have hiErase : i ∈ M.erase j := mem_erase.mpr ⟨hij, hIM hi⟩
    exact notMem_erase i M (heq.symm ▸ hiErase)
  have hsub : I.biUnion C ⊆ D := by
    intro S hS
    obtain ⟨i, hi, hSi⟩ := mem_biUnion.mp hS
    exact hCD i hi hSi
  calc
    9 * I.card = ∑ i ∈ I, (C i).card := by
      simpa only [Nat.mul_comm] using (sum_const_nat hCcard).symm
    _ = (I.biUnion C).card := (card_biUnion hdisj).symm
    _ ≤ D.card := card_le_card hsub

end Submissions.Erdos1020MatchingRankThreeCaseOneMajorants.Main

namespace Submissions.Erdos1020MatchingRankThreeCaseOneActual.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeCaseOne.Main
open Submissions.Erdos1020MatchingRankThreeCaseOneMajorants.Main
open Submissions.Erdos1020ShiftNormalize.Main (Uniform MatchingFree)

private theorem row_eq_triple {n s : ℕ}
    (H : Finset (Finset (Fin n))) (hH : Uniform H 3)
    (B : Fin s → Finset (Fin n)) (hBH : ∀ i, B i ∈ H)
    (J : Fin 3 → Fin s) (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (J i)) (i : Fin 3) :
    B (J i) = {e (i, 0), e (i, 1), e (i, 2)} := by
  have hne (a b : Fin 3) (hab : a ≠ b) : e (i, a) ≠ e (i, b) :=
    fun h => hab (congrArg Prod.snd (he h))
  have hc : ({e (i, 0), e (i, 1), e (i, 2)} : Finset (Fin n)).card = 3 := by
    simp [hne 0 1 (by decide), hne 0 2 (by decide), hne 1 2 (by decide)]
  apply Eq.symm
  apply eq_of_subset_of_card_le
  · exact insert_subset (heB i 0) (insert_subset (heB i 1) (singleton_subset_iff.mpr (heB i 2)))
  · rw [hH _ (hBH _), hc]

/-- A narrow actual trace pair lowers to the least vertex and its row minimum.
Only the least-head and within-row minimum properties are needed. -/
theorem lower_narrow_pair_trace {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (B : Finset (Fin n)) (hBA : B ⊆ A) (hGB : Disjoint ({v, d} : Finset (Fin n)) B)
    (a : Fin n) (haB : a ∈ B) (hmin : ∀ x ∈ B, a ≤ x)
    (S : Finset (Fin n)) (hST : S ∈ H.image (fun E => E ∩ A))
    (hSU : S ⊆ {v, d} ∪ B) (hSc : S.card = 2) :
    ({v, a} : Finset (Fin n)) ∈ H.image (fun E => E ∩ A) := by
  have hdS := Submissions.Erdos1020MatchingRankThreeLocal.Main.pair_avoids_second
    H A hstable v d hvA hleast hvd hgap S hST hSc
  have hvB : v ∉ B := disjoint_left.mp hGB (by simp)
  have hrowmem (x : Fin n) (hxS : x ∈ S) (hxv : x ≠ v) : x ∈ B := by
    rcases mem_union.mp (hSU hxS) with hx | hx
    · simp only [mem_insert, mem_singleton] at hx
      rcases hx with h | h
      · exact (hxv h).elim
      · exact (hdS (h ▸ hxS)).elim
    · exact hx
  have hlower (y : Fin n) (hyB : y ∈ B)
      (hpair : ({v, y} : Finset (Fin n)) ∈ H.image (fun E => E ∩ A)) :
      ({v, a} : Finset (Fin n)) ∈ H.image (fun E => E ∩ A) := by
    by_cases hay : a = y
    · simpa only [hay] using hpair
    · have haylt : a < y := lt_of_le_of_ne (hmin y hyB) hay
      have hav : a ≠ v := fun h => hvB (h ▸ haB)
      have hvy : v ≠ y := fun h => hvB (h.symm ▸ hyB)
      have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable {v, y} hpair a y (hBA haB) haylt (by simp) (by simp [hav, hay])
      have hlast : insert a ({v} : Finset (Fin n)) ∈ H.image (fun E => E ∩ A) := by
        simpa only [erase_insert_of_ne hvy, erase_singleton, Finset.insert_empty] using h
      exact (pair_comm a v) ▸ hlast
  obtain ⟨x, y, hxy, hS⟩ := card_eq_two.mp hSc
  have hxS : x ∈ S := by rw [hS]; simp
  have hyS : y ∈ S := by rw [hS]; simp
  by_cases hxv : x = v
  · subst x
    exact hlower y (hrowmem y hyS hxy.symm) (hS ▸ hST)
  · by_cases hyv : y = v
    · subst y
      apply hlower x (hrowmem x hxS hxv)
      simpa only [hS, pair_comm x v] using hST
    · have hxB := hrowmem x hxS hxv
      have hyB := hrowmem y hyS hyv
      have hvx : v < x := lt_of_le_of_ne (hleast x (hBA hxB)) (Ne.symm hxv)
      have h := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
        H A hstable S hST v x hvA hvx hxS (by simp [hS, (Ne.symm hxv), (Ne.symm hyv)])
      apply hlower y hyB
      simpa only [hS, erase_insert (s := {y}) (a := x) (by simp [hxy])] using h

private theorem upper_avoids_gap_bottom {α : Type*} [DecidableEq α]
    (G : Finset α) (e : Fin 3 × Fin 3 → α) (he : Function.Injective e)
    (hGe : Disjoint G (univ.image e)) :
    Disjoint (((univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.2 ≠ 0)).image e)
      (G ∪ univ.image (fun i : Fin 3 => e (i, 0))) := by
  apply disjoint_left.mpr
  intro x hx hxU
  obtain ⟨p, hp, hpx⟩ := mem_image.mp hx
  rcases mem_union.mp hxU with hxG | hxA
  · exact disjoint_left.mp hGe hxG (mem_image.mpr ⟨p, mem_univ _, hpx⟩)
  · obtain ⟨i, _, hix⟩ := mem_image.mp hxA
    exact (mem_filter.mp hp).2 (congrArg Prod.snd (he (hpx.trans hix.symm)))

/-- Literal Case I counts in the actual three-block trace region. Actual
gap-plus-bottom edges are supplied here; the final wrapper proves them from
the minimum-gap and maximality hypotheses. -/
theorem actual_case_one_bounds {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : MatchingFree H (s + 1))
    (v d : Fin n) (hvA : v ∈ A) (hdA : d ∈ A)
    (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun E => E ∩ A))
    (B : Fin s → Finset (Fin n)) (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (J : Fin 3 → Fin s) (hJ : Function.Injective J)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (J i)) (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hbottom : ∀ i : Fin 3, insert (e (i, 0)) ({v, d} : Finset (Fin n)) ∈ H)
    (P Q : Finset (Fin n)) (hP : P ∈ H.image (fun E => E ∩ A))
    (hQ : Q ∈ H.image (fun E => E ∩ A))
    (hcover : P ∪ Q = (((univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.2 ≠ 0)).image e)) :
    let T := H.image (fun E => E ∩ A)
    let M := univ.image J
    let U := region {v, d} B M
    (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 2)).card = 0 ∧
      3 * (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 1)).card ≤
        ((U.powersetCard 3 \ T).filter (fun S => (support B S).card = 2)).card := by
  classical
  let T := H.image (fun E => E ∩ A)
  let M := univ.image J
  let U := region {v, d} B M
  let F := T.filter (fun S => S ⊆ U)
  let D := (U.powersetCard 3 \ T).filter (fun S => (support B S).card = 2)
  let p := fun i : Fin s => (T.filter (fun S => S ⊆ {v, d} ∪ B i ∧ S.card = 2)).card
  let C := fun i : Fin s => D.filter (fun S => support B S = M.erase i)
  change (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 2)).card = 0 ∧
    3 * (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 1)).card ≤ D.card
  have hMc : M.card = 3 := by
    change (univ.image J).card = 3
    rw [card_image_of_injective _ hJ, card_univ, Fintype.card_fin]
  have heA (p : Fin 3 × Fin 3) : e p ∈ A := hBA _ (heB p.1 p.2)
  have heU (i a : Fin 3) : e (i, a) ∈ U := mem_union_right _
    (mem_biUnion.mpr ⟨J i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, heB i a⟩)
  have hGsub : ({v, d} : Finset (Fin n)) ⊆ U := subset_union_left
  have hGe : Disjoint ({v, d} : Finset (Fin n)) (univ.image e) := by
    apply disjoint_left.mpr
    intro x hxG hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact disjoint_left.mp (hGB (J i)) hxG (heB i a)
  have hdboard : d ∉ univ.image e := disjoint_left.mp hGe (by simp)
  have hainj : Function.Injective (fun i : Fin 3 => e (i, 0)) :=
    fun i j h => congrArg Prod.fst (he h)
  have hGbottom : Disjoint ({v, d} : Finset (Fin n)) (univ.image (fun i : Fin 3 => e (i, 0))) := by
    apply hGe.mono (Subset.refl _)
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact mem_image.mpr ⟨(i, 0), mem_univ _, rfl⟩
  have hroweq := row_eq_triple H hH B hBH J e he heB
  have hrowonto (i : Fin 3) (x : Fin n) (hx : x ∈ B (J i)) :
      ∃ a : Fin 3, e (i, a) = x := by
    rw [hroweq i] at hx
    rcases mem_insert.mp hx with h | h
    · exact ⟨0, h.symm⟩
    · simp only [mem_insert, mem_singleton] at h
      rcases h with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  have hminrow (i : Fin 3) (x : Fin n) (hx : x ∈ B (J i)) : e (i, 0) ≤ x := by
    obtain ⟨a, rfl⟩ := hrowonto i x hx
    exact (hrow i).monotone (by omega)
  have hno : ∀ f : Bool × Bool → Finset (Fin n), (∀ i, f i ∈ F) →
      ¬ Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro f hf
    exact Submissions.Erdos1020MatchingRankThreeLocal.Main.no_indexed_local_trace_matching
      (by decide) H A hH hA hcut hstable hfree {v, d} B hBH hBA hBd hGB M
      (by simp only [Fintype.card_prod, Fintype.card_bool, hMc]) f
      (fun i => (mem_filter.mp (hf i)).1) (fun i => (mem_filter.mp (hf i)).2)
  have hupperU : (((univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.2 ≠ 0)).image e) ⊆ U := by
    intro x hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := mem_image.mp hx
    exact heU i a
  have hPU : P ⊆ U := by
    intro x hx
    apply hupperU
    rw [← hcover]
    exact mem_union_left _ hx
  have hQU : Q ⊆ U := by
    intro x hx
    apply hupperU
    rw [← hcover]
    exact mem_union_right _ hx
  have hPF : P ∈ F := mem_filter.mpr ⟨hP, hPU⟩
  have hQF : Q ∈ F := mem_filter.mpr ⟨hQ, hQU⟩
  have hsmall (R : Finset (Fin n)) (hR : R ∈ T) : R.card ≤ 3 := by
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hR
    exact (card_le_card inter_subset_left).trans_eq (hH E hE)
  have hPQ : Disjoint P Q := disjoint_of_union_card_six P Q (hsmall P hP) (hsmall Q hQ)
    (by rw [hcover, card_image_of_injective _ he]; decide)
  have hupperD := upper_avoids_gap_bottom {v, d} e he hGe
  have hPD : Disjoint P ({v, d} ∪ univ.image (fun i : Fin 3 => e (i, 0))) :=
    hupperD.mono (by rw [← hcover]; exact subset_union_left) (Subset.refl _)
  have hQD : Disjoint Q ({v, d} ∪ univ.image (fun i : Fin 3 => e (i, 0))) :=
    hupperD.mono (by rw [← hcover]; exact subset_union_right) (Subset.refl _)
  have hbottomF (i : Fin 3) : insert (e (i, 0)) ({v, d} : Finset (Fin n)) ∈ F := by
    have hSA : insert (e (i, 0)) ({v, d} : Finset (Fin n)) ⊆ A :=
      insert_subset (heA _) (insert_subset hvA (singleton_subset_iff.mpr hdA))
    refine mem_filter.mpr ⟨?_, insert_subset (heU i 0) hGsub⟩
    exact mem_image.mpr ⟨_, hbottom i, inter_eq_left.mpr hSA⟩
  have htraceF (i j : Fin 3) (hT : ({e (i, 0), e (j, 0)} : Finset (Fin n)) ∈ T) :
      ({e (i, 0), e (j, 0)} : Finset (Fin n)) ∈ F :=
    mem_filter.mpr ⟨hT, insert_subset (heU i 0) (singleton_subset_iff.mpr (heU j 0))⟩
  have hp2zero : (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 2)).card = 0 := by
    have hempty := local_width_two_pairs_eq_empty T {v, d} B hBd hGB M (by
      intro i hi j hj hij x hx y hy
      obtain ⟨i0, _, rfl⟩ := mem_image.mp hi
      obtain ⟨j0, _, rfl⟩ := mem_image.mp hj
      obtain ⟨a, rfl⟩ := hrowonto i0 x hx
      obtain ⟨b, rfl⟩ := hrowonto j0 y hy
      have hnot := row_pair_missing H A hstable e he heA hrow F (filter_subset _ _) htraceF
        hno {v, d} hGe P Q hPF hQF hPQ hPD hQD hbottomF i0 j0
        (fun h => hij (congrArg J h)) a b
      intro hpair
      exact hnot (mem_filter.mpr ⟨hpair,
        insert_subset (heU i0 a) (singleton_subset_iff.mpr (heU j0 b))⟩))
    rw [hempty, card_empty]
  have hPcount : (T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ (support B S).card = 1)).card =
      ∑ i ∈ M, p i := by
    let TP := T.filter (fun S => S.card = 2)
    have hnotG : ∀ S ∈ TP, ¬ S ⊆ ({v, d} : Finset (Fin n)) := by
      intro S hS hSG
      have hc := (mem_filter.mp hS).2
      have heq : S = {v, d} := eq_of_subset_of_card_le hSG (by rw [card_pair hvd.ne, hc])
      exact hgap (heq ▸ (mem_filter.mp hS).1)
    have h := Submissions.Erdos1020MatchingRankThreeWidthOne.Main.width_one_card_eq_sum
      {v, d} B hBd hGB TP hnotG M
    simpa only [TP, p, filter_filter, and_assoc, and_left_comm, and_comm] using h
  have hpoint : ∀ i ∈ M, 3 * p i ≤ (C i).card := by
    intro i hi
    by_cases hpi : p i = 0
    · simp only [hpi, Nat.mul_zero, Nat.zero_le]
    · obtain ⟨i0, _, rfl⟩ := mem_image.mp hi
      have hpc : 0 < (T.filter (fun S => S ⊆ {v, d} ∪ B (J i0) ∧ S.card = 2)).card :=
        Nat.pos_of_ne_zero hpi
      obtain ⟨S, hS⟩ := card_pos.mp hpc
      obtain ⟨hST, hSU, hSc⟩ := mem_filter.mp hS
      have hpair := lower_narrow_pair_trace H A hstable v d hvA hleast hvd hgap
        (B (J i0)) (hBA _) (hGB _) (e (i0, 0)) (heB i0 0) (hminrow i0) S hST hSU hSc
      have hremaining : ((univ : Finset (Fin 3)).erase i0).card = 2 := by simp
      obtain ⟨j, k, hjk, hrest⟩ := card_eq_two.mp hremaining
      have hj : j ∈ (univ : Finset (Fin 3)).erase i0 := by rw [hrest]; simp
      have hk : k ∈ (univ : Finset (Fin 3)).erase i0 := by rw [hrest]; simp
      have hcomp : ({J j, J k} : Finset (Fin s)) = M.erase (J i0) := by
        ext l
        constructor
        · intro hl
          simp only [mem_insert, mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact mem_erase.mpr ⟨fun h => (mem_erase.mp hj).1 (hJ h), mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩
          · exact mem_erase.mpr ⟨fun h => (mem_erase.mp hk).1 (hJ h), mem_image.mpr ⟨k, mem_univ _, rfl⟩⟩
        · intro hl
          obtain ⟨hlne, hlM⟩ := mem_erase.mp hl
          obtain ⟨a, _, rfl⟩ := mem_image.mp hlM
          have ha : a ∈ (univ : Finset (Fin 3)).erase i0 :=
            mem_erase.mpr ⟨fun h => hlne (congrArg J h), mem_univ _⟩
          rw [hrest] at ha
          simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl <;> simp
      have hseedF := medium_seed_missing F hno v d hvd.ne (fun i => e (i, 0)) hainj hGbottom
        P Q hPF hQF hPQ hPD hQD i0 j k (mem_erase.mp hj).1.symm (mem_erase.mp hk).1.symm
        (mem_filter.mpr ⟨hpair, insert_subset (hGsub (by simp)) (singleton_subset_iff.mpr (heU i0 0))⟩)
      have hseed : mediumTriple d e j k (0, 0) ∉ T := by
        intro hseedT
        apply hseedF
        exact mem_filter.mpr ⟨hseedT, insert_subset (hGsub (by simp))
          (insert_subset (heU j 0) (singleton_subset_iff.mpr (heU k 0)))⟩
      have hmissing := majorant_missing_trace H A hstable d e he hdboard heA hrow j k hjk hseed
      have hCD := medium_candidates_subset {v, d} B hBd hGB d (by simp) J hJ e he heB j k hjk T hmissing
      have hCsub : univ.image (mediumTriple d e j k) ⊆ C (J i0) := by
        intro S hS
        refine mem_filter.mpr ⟨hCD hS, ?_⟩
        obtain ⟨q, _, rfl⟩ := mem_image.mp hS
        rw [mediumTriple_support {v, d} B hBd hGB d (by simp) J e heB j k q, hcomp]
      have h9 : 9 ≤ (C (J i0)).card := by
        have h := card_le_card hCsub
        rwa [nine_card d e he hdboard j k hjk] at h
      have hp3 := (Submissions.Erdos1020MatchingRankThreeNarrow.Main.actual_narrow_bounds
        H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB (J i0)).2
      exact (Nat.mul_le_mul_left 3 hp3).trans h9
  have hCdisj : ∀ i ∈ M, ∀ j ∈ M, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro S hSi hSj
    have heq : M.erase i = M.erase j := ((mem_filter.mp hSi).2).symm.trans ((mem_filter.mp hSj).2)
    exact notMem_erase i M (heq.symm ▸ mem_erase.mpr ⟨hij, hi⟩)
  have hCsub : M.biUnion C ⊆ D := by
    intro S hS
    obtain ⟨i, _, hiS⟩ := mem_biUnion.mp hS
    exact (mem_filter.mp hiS).1
  refine ⟨hp2zero, ?_⟩
  calc
    _ = ∑ i ∈ M, 3 * p i := by rw [hPcount, mul_sum]
    _ ≤ ∑ i ∈ M, (C i).card := sum_le_sum hpoint
    _ = (M.biUnion C).card := (card_biUnion hCdisj).symm
    _ ≤ D.card := card_le_card hCsub

end Submissions.Erdos1020MatchingRankThreeCaseOneActual.Main

namespace Submissions.Erdos1020MatchingRankThreeBCCompletion.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeBC.Main
open Submissions.Erdos1020MatchingRankThreeBCPairs.Main

/-- Trace completion alone excludes every subtrace of a missing head seed. -/
private theorem seed_subpair_missing_of_completion {n : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hcomplete : ∀ S : Finset (Fin n), S.card = 3 →
      (∃ E ∈ H, E ∩ A ⊆ S) → S ∈ H)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e) (heA : ∀ p, e p ∈ A)
    (hseed : seed.image e ∉ H.image (fun S => S ∩ A))
    (P : Finset (Fin 3 × Fin 3)) (hP : P ⊆ seed) :
    P.image e ∉ H.image (fun S => S ∩ A) := by
  intro htrace
  obtain ⟨f, hf, hfA⟩ := mem_image.mp htrace
  have hSc : (seed.image e).card = 3 := by
    rw [card_image_of_injective _ he]
    decide
  have hSA : seed.image e ⊆ A := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := mem_image.mp hx
    exact heA p
  have hSH := hcomplete (seed.image e) hSc
    ⟨f, hf, by rw [hfA]; exact image_subset_image hP⟩
  exact hseed (mem_image.mpr ⟨seed.image e, hSH, inter_eq_left.mpr hSA⟩)

/-- The checked 27-minus-15 pair count needs only completion at its three seed pairs. -/
private theorem width_two_bound_of_completion {n s : ℕ}
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hcomplete : ∀ S : Finset (Fin n), S.card = 3 →
      (∃ E ∈ H, E ∩ A ⊆ S) → S ∈ H)
    (G : Finset (Fin n)) (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j))) (hGB : ∀ i, Disjoint G (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A))
    (hR : G ∪ hub.image e ∈ H.image (fun S => S ∩ A)) :
    ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region G B (univ.image j) ∧
      S.card = 2 ∧ (support B S).card = 2)).card ≤ 12 := by
  have heA (p : Fin 3 × Fin 3) : e p ∈ A := hBA _ (heB p.1 p.2)
  have hseed := actual_seed_missing H A hH hA hcut hstable hfree G B hBH hBA hBd hGB
    (univ.image j) (by rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin])
    j (fun i => mem_image.mpr ⟨i, mem_univ _, rfl⟩) e he heB hrow hP hR
  have h02 := seed_subpair_missing_of_completion H A hcomplete e he heA hseed
    {(0, 0), (2, 0)} (by decide)
  have h01 := seed_subpair_missing_of_completion H A hcomplete e he heA hseed
    {(0, 0), (1, 2)} (by decide)
  have h12 := seed_subpair_missing_of_completion H A hcomplete e he heA hseed
    {(1, 2), (2, 0)} (by decide)
  have hmissing := forbidden_missing H A hstable e he heA hrow
    (by simpa using h02) (by simpa using h01) (by simpa using h12)
  have hBe (i : Fin 3) : B (j i) = univ.image (fun a => e (i, a)) := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, _, rfl⟩ := mem_image.mp hx
      exact heB i a
    · have hi : Function.Injective (fun a => e (i, a)) :=
        fun a b h => congrArg Prod.snd (he h)
      rw [hH _ (hBH _), card_image_of_injective _ hi, card_univ, Fintype.card_fin]
  exact width_two_le_twelve G B hBd hGB j hj e he heB hBe (H.image (fun S => S ∩ A)) hmissing


/-- The literal local comparison (A) in the actual BC subcase. Every count is
obtained from the original family; no local comparison or numerical count is a premise.
The parameter N is explicit for the later substitution N=n-(3*s+2). -/
theorem actual_weighted_comparison {n s N : ℕ}
    (hs : 14 ≤ s) (hN : 2 * N ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hcomplete : ∀ S : Finset (Fin n), S.card = 3 →
      (∃ E ∈ H, E ∩ A ⊆ S) → S ∈ H)
    (v d : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hP : upperPair.image e ∈ H.image (fun S => S ∩ A))
    (hR : {v, d} ∪ hub.image e ∈ H.image (fun S => S ∩ A)) :
    N * ((s - 1) *
        ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
          S.card = 2 ∧ (support B S).card = 2)).card +
      2 * ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
        S.card = 2 ∧ (support B S).card = 1)).card) ≤
      (s - 1) * (s - 2) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 3)).card +
      (s - 1) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 2)).card +
      2 * (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 1)).card := by
  have hMc : (univ.image j).card = 3 := by
    rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  have hp1 := (Submissions.Erdos1020MatchingRankThreeWidthOne.Main.actual_width_one_bounds
    H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB
    (univ.image j) hMc).2
  have hp2 := width_two_bound_of_completion
    H A hH hA hcut hstable hfree hcomplete {v, d} B hBH hBA hBd hGB j hj e he heB hrow hP hR
  have hd3 := Submissions.Erdos1020MatchingRankThreeBCMajorants.Main.actual_nine_missing
    H A hH hA hcut hstable hfree {v, d} B hBH hBA hBd hGB j hj e he heB hrow hP hR
  exact Submissions.Erdos1020MatchingRankThreeCaseNumeric.Main.bc_weighted_comparison
    hs hN hp1 hp2 hd3


end Submissions.Erdos1020MatchingRankThreeBCCompletion.Main

namespace Submissions.Erdos1020MatchingRankThreeLocalCases.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingRankThreeLowGraph.Main
open Submissions.Erdos1020MatchingRankThreeActiveWide.Main
open Submissions.Erdos1020MatchingRankThreeRelabel.Main

/-- All actual three-block cases imply the local comparison. Trace completion
and the six actual low hubs are the structural inputs; no case-specific absence,
cover, count or weighted inequality is assumed. -/
theorem actual_weighted_comparison {n s N : ℕ}
    (hs : 32 ≤ s) (hN : 2 * N ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hcomplete : ∀ S : Finset (Fin n), S.card = 3 →
      (∃ E ∈ H, E ∩ A ⊆ S) → S ∈ H)
    (v d : Fin n) (hvA : v ∈ A) (hdA : d ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a)))
    (hlow : ∀ i a : Fin 3, a ≤ 1 → ({v, d} ∪ {e (i, a)} : Finset (Fin n)) ∈ H) :
    N * ((s - 1) *
        ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
          S.card = 2 ∧ (support B S).card = 2)).card +
      2 * ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
        S.card = 2 ∧ (support B S).card = 1)).card) ≤
      (s - 1) * (s - 2) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 3)).card +
      (s - 1) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 2)).card +
      2 * (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 1)).card := by
  classical
  let T := H.image (fun S => S ∩ A)
  have heA (x : Fin 3 × Fin 3) : e x ∈ A := hBA _ (heB x.1 x.2)
  have heG (x : Fin 3 × Fin 3) : e x ∉ ({v, d} : Finset (Fin n)) :=
    fun h => disjoint_left.mp (hGB (j x.1)) h (heB x.1 x.2)
  have hhub (x : Fin 3 × Fin 3) (hx : x.2 ≤ 1) : {v, d} ∪ {e x} ∈ T := by
    have hsub : ({v, d} ∪ {e x} : Finset (Fin n)) ⊆ A :=
      union_subset (insert_subset hvA (singleton_subset_iff.mpr hdA)) (singleton_subset_iff.mpr (heA x))
    exact mem_image.mpr ⟨_, hlow x.1 x.2 hx, inter_eq_left.mpr hsub⟩
  have hMc : (univ.image j).card = 3 := by
    rw [card_image_of_injective _ hj, card_univ, Fintype.card_fin]
  by_cases hcover : ∃ P ∈ T, ∃ Q ∈ T, P ∪ Q = univ.image (e ∘ upperBoard)
  · obtain ⟨P, hP, Q, hQ, hPQ⟩ := hcover
    have hupper : univ.image (e ∘ upperBoard) =
        (((univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.2 ≠ 0)).image e) := by
      rw [← image_image]
      exact congrArg (fun U : Finset (Fin 3 × Fin 3) => U.image e) (by decide)
    have hbottom (i : Fin 3) : insert (e (i, 0)) ({v, d} : Finset (Fin n)) ∈ H := by
      simpa only [union_singleton] using hlow i 0 (by decide)
    have hcounts := Submissions.Erdos1020MatchingRankThreeCaseOneActual.Main.actual_case_one_bounds
      H A hH hA hcut hstable hfree v d hvA hdA hleast hvd hgap B hBH hBA hBd hGB
      j hj e he heB hrow hbottom P Q hP hQ (hPQ.trans hupper)
    have hwidth := Submissions.Erdos1020MatchingRankThreeWidthOne.Main.actual_width_one_bounds
      H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB (univ.image j) hMc
    exact Submissions.Erdos1020MatchingRankThreeCaseNumeric.Main.case_one_weighted_comparison
      (by omega) hN hcounts.1 hcounts.2 hwidth.1
  · have hnocover : ∀ P ∈ T, ∀ Q ∈ T, P ∪ Q ≠ univ.image (e ∘ upperBoard) :=
      fun P hP Q hQ hPQ => hcover ⟨P, hP, Q, hQ, hPQ⟩
    by_cases hBC : ∃ i l : Fin 3, i ≠ l ∧ ({e (i, 2), e (l, 1)} : Finset (Fin n)) ∈ T
    · obtain ⟨i, l, hil, hpair⟩ := hBC
      obtain ⟨σ, hσ0, hσ1⟩ :=
        Submissions.Erdos1020MatchingRankThreeCaseClassify.Main.exists_perm_zero_one i l hil
      let j' := j ∘ σ
      let e' := relabel σ e
      have hj' : Function.Injective j' := hj.comp σ.injective
      have he' : Function.Injective e' := relabel_injective σ e he
      have heB' : ∀ i a, e' (i, a) ∈ B (j' i) := fun i a => heB (σ i) a
      have hrow' : ∀ i, StrictMono (fun a : Fin 3 => e' (i, a)) := fun i => hrow (σ i)
      have hP : Submissions.Erdos1020MatchingRankThreeBC.Main.upperPair.image e' ∈ T := by
        simpa only [Submissions.Erdos1020MatchingRankThreeBC.Main.upperPair,
          image_insert, image_singleton, e', relabel, hσ0, hσ1] using hpair
      have hR : {v, d} ∪ Submissions.Erdos1020MatchingRankThreeBC.Main.hub.image e' ∈ T := by
        simpa only [Submissions.Erdos1020MatchingRankThreeBC.Main.hub,
          image_singleton, e', relabel] using hhub (σ 2, 1) (show (1 : Fin 3) ≤ 1 from le_rfl)
      have h := Submissions.Erdos1020MatchingRankThreeBCCompletion.Main.actual_weighted_comparison
        (by omega : 14 ≤ s) hN H A hH hA hcut hstable hfree hcomplete
        v d hvA hleast hvd hgap B hBH hBA hBd hGB j' hj' e' he' heB' hrow' hP hR
      have hreg : region {v, d} B (univ.image j') = region {v, d} B (univ.image j) :=
        region_relabel {v, d} B σ j
      simpa only [hreg] using h
    · have hbar : ∀ i l : Fin 3, i ≠ l → ∀ a b : Fin 3, 1 ≤ a → 1 ≤ b → a = 2 ∨ b = 2 →
          ({e (i, a), e (l, b)} : Finset (Fin n)) ∉ T := by
        intro i l hil a b ha hb hab hpair
        rcases hab with rfl | rfl
        · have hp := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
            H A hstable e he heA hrow i l hil 2 2 1 b le_rfl hb hpair
          exact hBC ⟨i, l, hil, hp⟩
        · have hp := Submissions.Erdos1020MatchingRankThreeBCPairs.Main.lower_grid_pair_trace
            H A hstable e he heA hrow l i hil.symm 2 2 1 a le_rfl ha
            (by simpa only [pair_comm] using hpair)
          exact hBC ⟨l, i, hil.symm, hp⟩
      have htophub : ∀ i l : Fin 3, i ≠ l →
          ({e (i, 0), e (l, 2)} : Finset (Fin n)) ∈ T → {v, d} ∪ {e (l, 2)} ∈ T := by
        intro i l hil hpair
        have hvx : v ≠ e (i, 0) := fun h => heG (i, 0) (by simp [← h])
        have hvy : v ≠ e (l, 2) := fun h => heG (l, 2) (by simp [← h])
        have hxy : e (i, 0) ≠ e (l, 2) := fun h => hil (congrArg Prod.fst (he h))
        have hlowpair := Submissions.Erdos1020MatchingRankThreeLocal.Main.replace_mem_trace
          H A hstable {e (i, 0), e (l, 2)} hpair v (e (i, 0)) hvA
          (lt_of_le_of_ne (hleast _ (heA (i, 0))) hvx) (by simp) (by simp [hvx, hvy])
        have hvpair : ({v, e (l, 2)} : Finset (Fin n)) ∈ T := by
          simpa only [erase_insert (show e (i, 0) ∉ ({e (l, 2)} : Finset (Fin n)) from by simp [hxy])]
            using hlowpair
        obtain ⟨E, hE, hEA⟩ := mem_image.mp hvpair
        have hfull : insert (e (l, 2)) ({v, d} : Finset (Fin n)) ∈ H := by
          apply hcomplete _ (by rw [card_insert_of_notMem (heG (l, 2)), card_pair hvd.ne])
          refine ⟨E, hE, ?_⟩
          rw [hEA]
          exact insert_subset (by simp) (by simp)
        have hfull' : ({v, d} ∪ {e (l, 2)} : Finset (Fin n)) ∈ H := by
          simpa only [union_singleton] using hfull
        have hsub : ({v, d} ∪ {e (l, 2)} : Finset (Fin n)) ⊆ A :=
          union_subset (insert_subset hvA (singleton_subset_iff.mpr hdA))
            (singleton_subset_iff.mpr (heA (l, 2)))
        exact mem_image.mpr ⟨_, hfull', inter_eq_left.mpr hsub⟩
      exact Submissions.Erdos1020MatchingRankThreeCaseTwoWeighted.Main.actual_weighted_comparison
        hs hN H A hH hA hcut hstable hfree v d hvA hleast hvd hgap B hBH hBA hBd hGB
        j hj e he heB hrow
        (fun x hx => hhub x (by have h := (mem_filter.mp hx).2; omega)) htophub hnocover hbar

end Submissions.Erdos1020MatchingRankThreeLocalCases.Main

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

namespace Submissions.Erdos1020MatchingRankThreeRows.Main

open Finset

/-- Any three selected disjoint triples have an injective grid labeling,
strictly increasing within each row. Only selected blocks need cardinality three. -/
theorem exists_rows {α : Type*} [LinearOrder α] {s : ℕ}
    (B : Fin s → Finset α) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (M : Finset (Fin s)) (hMc : M.card = 3)
    (hcard : ∀ i ∈ M, (B i).card = 3) :
    ∃ (J : Fin 3 → Fin s) (e : Fin 3 × Fin 3 → α),
      Function.Injective J ∧ univ.image J = M ∧ Function.Injective e ∧
      (∀ i a, e (i, a) ∈ B (J i)) ∧
      (∀ i, StrictMono (fun a : Fin 3 => e (i, a))) ∧
      (∀ i, univ.image (fun a : Fin 3 => e (i, a)) = B (J i)) := by
  let J : Fin 3 ↪o Fin s := M.orderEmbOfFin hMc
  have hJM (i : Fin 3) : J i ∈ M := M.orderEmbOfFin_mem hMc i
  let row (i : Fin 3) : Fin 3 ↪o α := (B (J i)).orderEmbOfFin (hcard _ (hJM i))
  let e : Fin 3 × Fin 3 → α := fun p => row p.1 p.2
  have heB (i a : Fin 3) : e (i, a) ∈ B (J i) :=
    (B (J i)).orderEmbOfFin_mem (hcard _ (hJM i)) a
  have he : Function.Injective e := by
    intro p q heq
    have hJ : J p.1 = J q.1 := by
      by_contra hne
      exact disjoint_left.mp (hB hne) (heB p.1 p.2) (heq.symm ▸ heB q.1 q.2)
    have hpq : p.1 = q.1 := J.injective hJ
    apply Prod.ext hpq
    change row p.1 p.2 = row q.1 q.2 at heq
    rw [hpq] at heq
    exact (row q.1).injective heq
  refine ⟨J, e, J.injective, M.image_orderEmbOfFin_univ hMc, he, heB, ?_, ?_⟩
  · intro i
    exact (row i).strictMono
  · intro i
    exact (B (J i)).image_orderEmbOfFin_univ (hcard _ (hJM i))

end Submissions.Erdos1020MatchingRankThreeRows.Main

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

namespace Submissions.Erdos1020MatchingRankThreeWeights.Main

open Finset

private theorem sum_by_width {β : Type*} [DecidableEq β]
    (D : Finset β) (c : β → ℕ) (hc : ∀ x ∈ D, 1 ≤ c x ∧ c x ≤ 3)
    (w : ℕ → ℚ) :
    (∑ x ∈ D, w (c x)) =
      ((D.filter (c · = 1)).card : ℚ) * w 1 +
      ((D.filter (c · = 2)).card : ℚ) * w 2 +
      ((D.filter (c · = 3)).card : ℚ) * w 3 := by
  have hm : ∀ x ∈ D, c x ∈ ({1, 2, 3} : Finset ℕ) := by
    intro x hx
    have h := hc x hx
    have he : c x = 1 ∨ c x = 2 ∨ c x = 3 := by omega
    simpa only [mem_insert, mem_singleton] using he
  rw [← sum_fiberwise_of_maps_to' hm w]
  simp [sum_const, nsmul_eq_mul, add_assoc]

/-- Clear the two positive rank-three binomial denominators. This arithmetic
helper keeps the literal integer comparison as its premise. -/
theorem rational_comparison {s N p1 p2 d1 d2 d3 : ℕ} (hs : 3 ≤ s)
    (h : N * ((s - 1) * p2 + 2 * p1) ≤
      (s - 1) * (s - 2) * d3 + (s - 1) * d2 + 2 * d1) :
    (p1 : ℚ) * ((N : ℚ) / ((s - 1).choose 2 : ℚ)) +
      (p2 : ℚ) * ((N : ℚ) / (s - 2 : ℕ)) ≤
    (d1 : ℚ) * (1 / ((s - 1).choose 2 : ℚ)) +
      (d2 : ℚ) * (1 / (s - 2 : ℕ)) + (d3 : ℚ) := by
  have ht : 0 < s - 2 := by omega
  have hC : 0 < (s - 1).choose 2 := Nat.choose_pos (by omega)
  have hCq : (0 : ℚ) < ((s - 1).choose 2 : ℚ) := Nat.cast_pos.mpr hC
  have htq : (0 : ℚ) < (s - 2 : ℕ) := Nat.cast_pos.mpr ht
  have hchoose := Nat.choose_succ_right_eq (s - 1) 1
  have hsub : s - 1 - 1 = s - 2 := by omega
  norm_num only [Nat.choose_one_right, hsub] at hchoose
  have hchooseQ : ((s - 1).choose 2 : ℚ) * 2 =
      (s - 1 : ℕ) * (s - 2 : ℕ) := by exact_mod_cast hchoose
  have hq : (N : ℚ) * ((s - 1 : ℕ) * (p2 : ℚ) + 2 * (p1 : ℚ)) ≤
      (s - 1 : ℕ) * (s - 2 : ℕ) * (d3 : ℚ) +
        (s - 1 : ℕ) * (d2 : ℚ) + 2 * (d1 : ℚ) := by exact_mod_cast h
  have ha : ((s - 1 : ℕ) : ℚ) =
      2 * ((s - 1).choose 2 : ℚ) / (s - 2 : ℕ) := by
    apply (eq_div_iff htq.ne').mpr
    nlinarith only [hchooseQ]
  rw [ha] at hq
  field_simp at hq
  apply (mul_le_mul_iff_left₀ (mul_pos hCq htq)).mp
  field_simp
  nlinarith only [hq]

set_option maxHeartbeats 1000000 in
/-- Cancel the present triples and use their exact missing-width counts.
The hypotheses explicitly require trace sizes two or three and positive width;
the actual-family adapter must discharge them. -/
theorem local_weight_le_of_counts {α : Type*} [DecidableEq α] {s N : ℕ}
    (hs : 3 ≤ s) (U : Finset α) (F : Finset (Finset α))
    (c : Finset α → ℕ) (hFU : ∀ S ∈ F, S ⊆ U)
    (hFr : ∀ S ∈ F, 2 ≤ S.card ∧ S.card ≤ 3)
    (hFc : ∀ S ∈ F, 1 ≤ c S ∧ c S ≤ S.card)
    (hPc : ∀ S ∈ U.powersetCard 3, 1 ≤ c S ∧ c S ≤ 3)
    (hcounts :
      N * ((s - 1) * (F.filter (fun S => S.card = 2 ∧ c S = 2)).card +
        2 * (F.filter (fun S => S.card = 2 ∧ c S = 1)).card) ≤
      (s - 1) * (s - 2) * ((U.powersetCard 3 \ F).filter (c · = 3)).card +
        (s - 1) * ((U.powersetCard 3 \ F).filter (c · = 2)).card +
        2 * ((U.powersetCard 3 \ F).filter (c · = 1)).card) :
    (∑ S ∈ F, (N.choose (3 - S.card) : ℚ) /
      ((s - c S).choose (3 - c S) : ℚ)) ≤
    ∑ S ∈ U.powersetCard 3, (N.choose (3 - S.card) : ℚ) /
      ((s - c S).choose (3 - c S) : ℚ) := by
  classical
  let P := U.powersetCard 3
  let L := F.filter (fun S => S.card = 3)
  let K := F.filter (fun S => S.card = 2)
  let D := P \ F
  let w : Finset α → ℚ := fun S => (N.choose (3 - S.card) : ℚ) /
    ((s - c S).choose (3 - c S) : ℚ)
  have hLP : L ⊆ P := by
    intro S hS
    exact mem_powersetCard.mpr ⟨hFU S (mem_filter.mp hS).1, (mem_filter.mp hS).2⟩
  have hdiff : P \ L = D := by
    ext S
    constructor
    · rintro hS
      obtain ⟨hSP, hSL⟩ := mem_sdiff.mp hS
      refine mem_sdiff.mpr ⟨hSP, ?_⟩
      intro hSF
      exact hSL (mem_filter.mpr ⟨hSF, (mem_powersetCard.mp hSP).2⟩)
    · intro hS
      obtain ⟨hSP, hSF⟩ := mem_sdiff.mp hS
      exact mem_sdiff.mpr ⟨hSP, fun hSL => hSF (mem_filter.mp hSL).1⟩
  have hsplitF : (∑ S ∈ K, w S) + (∑ S ∈ L, w S) = ∑ S ∈ F, w S := by
    have heq : F.filter (fun S => ¬ S.card = 2) = L := by
      ext S
      simp only [L, mem_filter]
      constructor
      · rintro ⟨hSF, hS⟩
        exact ⟨hSF, by have h := hFr S hSF; omega⟩
      · rintro ⟨hSF, hS⟩
        exact ⟨hSF, by omega⟩
    have hh := sum_filter_add_sum_filter_not F (fun S => S.card = 2) w
    rwa [heq] at hh
  have hsplitP : (∑ S ∈ D, w S) + (∑ S ∈ L, w S) = ∑ S ∈ P, w S := by
    simpa only [hdiff] using sum_sdiff hLP (f := w)
  have hKsum : (∑ S ∈ K, w S) =
      ((F.filter (fun S => S.card = 2 ∧ c S = 1)).card : ℚ) *
        ((N : ℚ) / ((s - 1).choose 2 : ℚ)) +
      ((F.filter (fun S => S.card = 2 ∧ c S = 2)).card : ℚ) *
        ((N : ℚ) / (s - 2 : ℕ)) := by
    have hzero : K.filter (c · = 3) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hSK, hc⟩ := mem_filter.mp hS
      have hSc := (mem_filter.mp hSK).2
      have hb := (hFc S (mem_filter.mp hSK).1).2
      omega
    calc
      _ = ∑ S ∈ K, (N : ℚ) / ((s - c S).choose (3 - c S) : ℚ) := by
        apply sum_congr rfl
        intro S hS
        simp only [w, (mem_filter.mp hS).2, Nat.reduceSub, Nat.choose_one_right]
      _ = _ := by
        rw [sum_by_width K c (fun S hS =>
          ⟨(hFc S (mem_filter.mp hS).1).1,
            (hFc S (mem_filter.mp hS).1).2.trans (hFr S (mem_filter.mp hS).1).2⟩)
          (fun j => (N : ℚ) / ((s - j).choose (3 - j) : ℚ))]
        simp only [hzero, card_empty, Nat.cast_zero, zero_mul, add_zero,
          K, filter_filter, Nat.reduceSub, Nat.choose_one_right]
  have hDsum : (∑ S ∈ D, w S) =
      ((D.filter (c · = 1)).card : ℚ) * (1 / ((s - 1).choose 2 : ℚ)) +
      ((D.filter (c · = 2)).card : ℚ) * (1 / (s - 2 : ℕ)) +
      ((D.filter (c · = 3)).card : ℚ) := by
    calc
      _ = ∑ S ∈ D, (1 : ℚ) / ((s - c S).choose (3 - c S) : ℚ) := by
        apply sum_congr rfl
        intro S hS
        have hSc := (mem_powersetCard.mp (mem_sdiff.mp hS).1).2
        simp only [w, hSc, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      _ = _ := by
        rw [sum_by_width D c (fun S hS => hPc S (mem_sdiff.mp hS).1)
          (fun j => (1 : ℚ) / ((s - j).choose (3 - j) : ℚ))]
        simp only [Nat.reduceSub, Nat.choose_one_right, Nat.choose_zero_right,
          Nat.cast_one, div_one, mul_one]
  have hshort : (∑ S ∈ K, w S) ≤ ∑ S ∈ D, w S := by
    rw [hKsum, hDsum]
    exact rational_comparison hs hcounts
  change (∑ S ∈ F, w S) ≤ ∑ S ∈ P, w S
  rw [← hsplitF, ← hsplitP]
  exact add_le_add hshort (le_refl _)

end Submissions.Erdos1020MatchingRankThreeWeights.Main

namespace Submissions.Erdos1020MatchingRankThreeWeightsActual.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- A local member of size at least two cannot have zero support when the
cardinality-two gap itself is absent. -/
theorem support_pos_of_mem {α : Type*} [DecidableEq α] {s : ℕ}
    (G : Finset α) (hGc : G.card = 2) (B : Fin s → Finset α)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (M : Finset (Fin s))
    (T : Finset (Finset α)) (hgap : G ∉ T)
    (S : Finset α) (hST : S ∈ T) (hSU : S ⊆ region G B M) (hmin : 2 ≤ S.card) :
    1 ≤ (support B S).card := by
  have hfull : S ⊆ G ∪ univ.biUnion B := hSU.trans
    (union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ M)))
  by_contra h
  have hzero : support B S = ∅ := card_eq_zero.mp (by omega)
  have hsmall := (subset_region_iff G B hB hGB S hfull ∅).mpr (by simp [hzero])
  have hSG : S ⊆ G := by simpa [region] using hsmall
  have heq : S = G := eq_of_subset_of_card_le hSG (by simpa only [hGc] using hmin)
  exact hgap (heq ▸ hST)

/-- Restricting the ambient family does not change missing subsets of U. -/
theorem missing_local_eq {α : Type*} [DecidableEq α]
    (U : Finset α) (T : Finset (Finset α)) (r : ℕ) :
    U.powersetCard r \ T.filter (fun S => S ⊆ U) = U.powersetCard r \ T := by
  ext S
  constructor
  · intro hS
    obtain ⟨hSP, hSF⟩ := mem_sdiff.mp hS
    exact mem_sdiff.mpr ⟨hSP, fun hST =>
      hSF (mem_filter.mpr ⟨hST, (mem_powersetCard.mp hSP).1⟩)⟩
  · intro hS
    obtain ⟨hSP, hST⟩ := mem_sdiff.mp hS
    exact mem_sdiff.mpr ⟨hSP, fun hSF => hST (mem_filter.mp hSF).1⟩

/-- The nested local pair filter is the literal pair count used in (A). -/
theorem local_pair_filter {α : Type*} [DecidableEq α]
    (U : Finset α) (T : Finset (Finset α)) (c : Finset α → ℕ) (i : ℕ) :
    (T.filter (fun S => S ⊆ U)).filter (fun S => S.card = 2 ∧ c S = i) =
      T.filter (fun S => S ⊆ U ∧ S.card = 2 ∧ c S = i) := by
  rw [filter_filter]

/-- Actual-trace adapter for the rational local weight theorem. Minimum trace
size two remains explicit for the upstream ONE argument. The integer (A) stays
a hypothesis; no rational comparison is assumed. -/
theorem actual_local_weight_le {α : Type*} [DecidableEq α] {s N : ℕ}
    (hs : 3 ≤ s) (H : Finset (Finset α)) (A : Finset α)
    (hTr : ∀ S ∈ H.image (fun e => e ∩ A), 2 ≤ S.card ∧ S.card ≤ 3)
    (G : Finset α) (hGc : G.card = 2)
    (hgap : G ∉ H.image (fun e => e ∩ A))
    (B : Fin s → Finset α) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint G (B i)) (M : Finset (Fin s))
    (hcounts :
      N * ((s - 1) *
          ((H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M ∧
            S.card = 2 ∧ (support B S).card = 2)).card +
        2 * ((H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M ∧
          S.card = 2 ∧ (support B S).card = 1)).card) ≤
        (s - 1) * (s - 2) *
          (((region G B M).powersetCard 3 \ H.image (fun e => e ∩ A)).filter
            (fun S => (support B S).card = 3)).card +
        (s - 1) *
          (((region G B M).powersetCard 3 \ H.image (fun e => e ∩ A)).filter
            (fun S => (support B S).card = 2)).card +
        2 * (((region G B M).powersetCard 3 \ H.image (fun e => e ∩ A)).filter
          (fun S => (support B S).card = 1)).card) :
    (∑ S ∈ (H.image (fun e => e ∩ A)).filter (fun S => S ⊆ region G B M),
      (N.choose (3 - S.card) : ℚ) /
        ((s - (support B S).card).choose (3 - (support B S).card) : ℚ)) ≤
    ∑ S ∈ (region G B M).powersetCard 3,
      (N.choose (3 - S.card) : ℚ) /
        ((s - (support B S).card).choose (3 - (support B S).card) : ℚ) := by
  let T := H.image (fun e => e ∩ A)
  let U := region G B M
  let F := T.filter (fun S => S ⊆ U)
  refine Submissions.Erdos1020MatchingRankThreeWeights.Main.local_weight_le_of_counts
    hs U F (fun S => (support B S).card) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    exact (mem_filter.mp hS).2
  · intro S hS
    exact hTr S (mem_filter.mp hS).1
  · intro S hS
    have hST := (mem_filter.mp hS).1
    exact ⟨support_pos_of_mem G hGc B hB hGB M T hgap S hST
      (mem_filter.mp hS).2 (hTr S hST).1, support_card_le_card B hB S⟩
  · intro S hS
    obtain ⟨hSU, hSc⟩ := mem_powersetCard.mp hS
    have hfull : S ⊆ G ∪ univ.biUnion B := hSU.trans
      (union_subset_union (Subset.refl _) (biUnion_subset_biUnion_of_subset_left B (subset_univ M)))
    exact ⟨support_pos_of_large_card G B hB hGB S hfull (by omega),
      by simpa only [hSc] using support_card_le_card B hB S⟩
  · simpa only [F, local_pair_filter, missing_local_eq] using hcounts

end Submissions.Erdos1020MatchingRankThreeWeightsActual.Main

namespace Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main
open Submissions.Erdos1020MatchingWeightedIncidence.Main

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

/-- Local comparisons imply the global clique bound by upper-counting trace
completions and using their exact block multiplicities. -/
theorem card_le_of_local {n r s : ℕ} (hrs : r ≤ s)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = r)
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
  have hF : ∀ S ∈ H.image (fun E => E ∩ A), S ⊆ G ∪ univ.biUnion B := by
    intro S hS
    obtain ⟨E, _, rfl⟩ := mem_image.mp hS
    rw [hpart]
    exact inter_subset_right
  have hFr : ∀ S ∈ H.image (fun E => E ∩ A), S.card ≤ r := by
    intro S hS
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hS
    exact (card_le_card inter_subset_left).trans_eq (hH E hE)
  apply (Nat.cast_le (α := ℚ)).mp
  calc
    (H.card : ℚ) ≤ ∑ S ∈ H.image (fun E => E ∩ A),
        ((n - A.card).choose (r - S.card) : ℚ) := by
      exact_mod_cast card_le_trace_sum H A hH
    _ = _ := (normalized_incidence hrs G B hB hG _ hF hFr
      (fun S => ((n - A.card).choose (r - S.card) : ℚ))).symm
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
    _ = (A.card.choose r : ℚ) := Submissions.Erdos1020MatchingTraceIncidence.Main.clique_weight_sum hrs A G B hB hG hpart

end Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main

namespace Submissions.Erdos1020MatchingRankThreeSaturatedLocal.Main

open Finset
open Submissions.Erdos1020MatchingBlockSupport.Main

/-- Rank-specific saturation and a minimum missing pair supply completion and
the six low full edges, so every actual three-block case satisfies the local comparison. -/
theorem actual_weighted_comparison {n s N : ℕ}
    (hs : 32 ≤ s) (hN : 2 * N ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : ∀ S ∈ H, S.card = 3) (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
      ∀ S ∈ K, ∀ T ∈ K, S ≠ T → Disjoint S T)
    (hsat : ∀ S : Finset (Fin n), S.card = 3 → S ∉ H →
      ¬ Submissions.Erdos1020ShiftNormalize.Main.MatchingFree (insert S H) (s + 1))
    (v d : Fin n) (hvA : v ∈ A) (hdA : d ∈ A) (hleast : ∀ x ∈ A, v ≤ x) (hvd : v < d)
    (hgap : ({v, d} : Finset (Fin n)) ∉ H.image (fun S => S ∩ A))
    (hmin : ∀ x ∈ A, v < x →
      {v, x} ∉ H.image (fun S => S ∩ A) → d ≤ x)
    (B : Fin s → Finset (Fin n))
    (hBH : ∀ i, B i ∈ H) (hBA : ∀ i, B i ⊆ A)
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hGB : ∀ i, Disjoint ({v, d} : Finset (Fin n)) (B i))
    (j : Fin 3 → Fin s) (hj : Function.Injective j)
    (e : Fin 3 × Fin 3 → Fin n) (he : Function.Injective e)
    (heB : ∀ i a, e (i, a) ∈ B (j i))
    (hrow : ∀ i, StrictMono (fun a : Fin 3 => e (i, a))) :
    N * ((s - 1) *
        ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
          S.card = 2 ∧ (support B S).card = 2)).card +
      2 * ((H.image (fun S => S ∩ A)).filter (fun S => S ⊆ region {v, d} B (univ.image j) ∧
        S.card = 2 ∧ (support B S).card = 1)).card) ≤
      (s - 1) * (s - 2) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 3)).card +
      (s - 1) *
        (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
          (fun S => (support B S).card = 2)).card +
      2 * (((region {v, d} B (univ.image j)).powersetCard 3 \ H.image (fun S => S ∩ A)).filter
        (fun S => (support B S).card = 1)).card := by
  have hcomplete : ∀ S : Finset (Fin n), S.card = 3 →
      (∃ E ∈ H, E ∩ A ⊆ S) → S ∈ H := by
    intro S hSc htrace
    exact Submissions.Erdos1020MatchingRankThreeSaturated.Main.mem_of_trace_subset
      (by decide) H A hH hfree hsat hA hcut hstable S hSc htrace
  have hlow : ∀ i a : Fin 3, a ≤ 1 → ({v, d} ∪ {e (i, a)} : Finset (Fin n)) ∈ H := by
    intro i a ha
    have hne (b c : Fin 3) (hbc : b ≠ c) : e (i, b) ≠ e (i, c) :=
      fun h => hbc ((hrow i).injective h)
    have hcard : ({e (i, 0), e (i, 1), e (i, 2)} : Finset (Fin n)).card = 3 := by
      simp [hne 0 1 (by decide), hne 0 2 (by decide), hne 1 2 (by decide)]
    have hroweq : B (j i) = {e (i, 0), e (i, 1), e (i, 2)} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · exact insert_subset (heB i 0) (insert_subset (heB i 1) (singleton_subset_iff.mpr (heB i 2)))
      · rw [hH _ (hBH _), hcard]
    have hnotG (b : Fin 3) : e (i, b) ∉ ({v, d} : Finset (Fin n)) :=
      fun h => disjoint_left.mp (hGB (j i)) h (heB i b)
    have hmid := Submissions.Erdos1020MatchingRankThreeSaturated.Main.insert_middle_mem
      H A hH hfree hsat hA hcut hstable v d hvA hdA hvd hleast hmin
      (e (i, 0)) (e (i, 1)) (e (i, 2)) (hrow i (by decide)) (hrow i (by decide))
      (by rw [← hroweq]; exact hBH _)
      (by rw [← hroweq]; exact hBA _)
      (by rw [← hroweq]; exact hGB _)
    have hfull : insert (e (i, a)) ({v, d} : Finset (Fin n)) ∈ H := by
      have ha' : a = 0 ∨ a = 1 := by omega
      rcases ha' with rfl | rfl
      · exact Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
          (hstable (e (i, 0)) (e (i, 1)) (hrow i (by decide))) (hnotG 1) (hnotG 0) hmid
      · exact hmid
    simpa only [union_singleton] using hfull
  exact Submissions.Erdos1020MatchingRankThreeLocalCases.Main.actual_weighted_comparison
    hs hN H A hH hA hcut hstable hfree hcomplete v d hvA hdA hleast hvd hgap
    B hBH hBA hBd hGB j hj e he heB hrow hlow

end Submissions.Erdos1020MatchingRankThreeSaturatedLocal.Main

namespace Submissions.Erdos1020MatchingRankThreeCriticalOne.Main

open Finset
open Submissions.Erdos1020ShiftNormalize.Main (Uniform MatchingFree)

/-- In the critical ambient range, the actual ONE matching, saturation and
all local comparisons give the clique bound. No local count is a premise. -/
theorem saturated_bound {n s : ℕ} (hs : 32 ≤ s) (hn : 3 * (s + 1) ≤ n)
    (hN : 2 * (n - (3 * s + 2)) ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H (s + 1))
    (hsat : ∀ E : Finset (Fin n), E.card = 3 → E ∉ H →
      ¬ MatchingFree (insert E H) (s + 1))
    (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hMv : ∀ E ∈ M, v ∉ E) : H.card ≤ (3 * s + 2).choose 3 := by
  classical
  obtain ⟨d, hdA, hvd, hgap, hmin, B, hBH, hBd, hGB, hBA, hpart, _⟩ :=
    Submissions.Erdos1020MatchingRankThreeSaturated.Main.exists_minimum_pair_partition
      hn H A hH hfree hsat hA hcut hstable v hvA hleast M hMH hMc hMd hMv
  have hAc : A.card = 3 * s + 2 := by omega
  have hN' : 2 * (n - A.card) ≤ s + 2 := by simpa only [hAc] using hN
  have hmintrace := Submissions.Erdos1020MatchingRankThreeOne.Main.trace_card_two_le_of_avoiding_matching
    (by decide) H A hH hA hcut hstable hfree v hvA hleast M hMH hMc hMd hMv
  have hTr : ∀ S ∈ H.image (fun E => E ∩ A), 2 ≤ S.card ∧ S.card ≤ 3 := by
    intro S hS
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hS
    exact ⟨hmintrace E hE, (card_le_card inter_subset_left).trans_eq (hH E hE)⟩
  rw [← hAc]
  apply Submissions.Erdos1020MatchingRankThreeGlobalUpper.Main.card_le_of_local
    (by omega) H A hH {v, d} B hBd hGB hpart
  intro L hL
  obtain ⟨J, e, hJ, hJL, he, heB, hrow, _⟩ :=
    Submissions.Erdos1020MatchingRankThreeRows.Main.exists_rows B hBd L
      (mem_powersetCard.mp hL).2 (fun i _ => hH _ (hBH i))
  have hcounts := Submissions.Erdos1020MatchingRankThreeSaturatedLocal.Main.actual_weighted_comparison
    hs hN' H A hH hA hcut hstable hfree hsat v d hvA hdA hleast hvd hgap hmin
    B hBH hBA hBd hGB J hJ e he heB hrow
  rw [hJL] at hcounts
  exact Submissions.Erdos1020MatchingRankThreeWeightsActual.Main.actual_local_weight_le
    (by omega) H A hTr {v, d} (card_pair hvd.ne) hgap B hBd hGB L hcounts

/-- A containing shifted saturated extension preserves the actual ONE
matching, so the critical clique bound applies to every shifted family. -/
theorem bound {n s : ℕ} (hs : 32 ≤ s) (hn : 3 * (s + 1) ≤ n)
    (hN : 2 * (n - (3 * s + 2)) ≤ s + 2)
    (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (hH : Uniform H 3) (hfree : MatchingFree H (s + 1))
    (hA : A.card + 1 = 3 * (s + 1))
    (hcut : ∀ a ∈ A, ∀ x, x ∉ A → a < x)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (v : Fin n) (hvA : v ∈ A) (hleast : ∀ x ∈ A, v ≤ x)
    (M : Finset (Finset (Fin n))) (hMH : M ⊆ H) (hMc : M.card = s)
    (hMd : ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hMv : ∀ E ∈ M, v ∉ E) : H.card ≤ (3 * s + 2).choose 3 := by
  obtain ⟨K, hHK, hK, hKm, hKs, hsat⟩ :=
    Submissions.Erdos1020MatchingRankThreeMaxExtension.Main.exists_saturated_shifted_extension
      (by decide) H hH hfree hstable
  exact (card_le_card hHK).trans
    (saturated_bound hs hn hN K A hK hKm hsat hA hcut hKs v hvA hleast M
      (hMH.trans hHK) hMc hMd hMv)

end Submissions.Erdos1020MatchingRankThreeCriticalOne.Main



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

end Submissions.Erdos1020MatchingMaximalShift.Main

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

namespace Submissions.Erdos1020MatchingRankThreeOneAmbient.Main

open Finset

/-- The last-vertex link has the rank-two star bound. Supplying only the
actual deletion's bound suffices for the ambient step; no theorem about all
families on the smaller ambient is assumed here. -/
theorem last_vertex_star_step_of_deletion_bound {n s : ℕ} (hs : 1 ≤ s)
    (hn : 3 * (s + 1) ≤ n + 1)
    (H : Finset (Finset (Fin (n + 1)))) (hH : ∀ e ∈ H, e.card = 3)
    (hstable : ∀ i j : Fin (n + 1), i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin (n + 1))), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (hD : (H.nonMemberSubfamily (Fin.last n)).card ≤ n.choose 3 - (n - s).choose 3) :
    H.card ≤ (n + 1).choose 3 - (n + 1 - s).choose 3 := by
  classical
  let z : Fin (n + 1) := Fin.last n
  change (H.nonMemberSubfamily z).card ≤ n.choose 3 - (n - s).choose 3 at hD
  have hzstable : ∀ x, UV.IsCompressed {x} {z} H := by
    intro x
    by_cases hx : x = z
    · subst x
      exact UV.isCompressed_self _ _
    · exact hstable x z (lt_of_le_of_ne (Fin.le_last x) hx)
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

end Submissions.Erdos1020MatchingRankThreeOneAmbient.Main

namespace Submissions.Erdos1020MatchingRankThreeOneDeletion.Main

open Finset

/-- Ordered deletion at the last vertex preserves a supplied rank-three
matching avoiding the designated vertex, after packing it into the deletion. -/
theorem reindex {n s : ℕ} (p : Fin n) (hn : 3 * s + 1 ≤ n)
    (H : Finset (Finset (Fin (n + 1)))) (hH : ∀ E ∈ H, E.card = 3)
    (hstable : ∀ x z, x < z → UV.IsCompressed {x} {z} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin (n + 1))),
      M ⊆ H ∧ M.card = s + 1 ∧
        ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (hone : ∃ M : Finset (Finset (Fin (n + 1))),
      M ⊆ H ∧ M.card = s ∧
        (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ E ∈ M, p.castSucc ∉ E) :
    ∃ H' : Finset (Finset (Fin n)),
      H'.card = (H.nonMemberSubfamily (Fin.last n)).card ∧
      (∀ E ∈ H', E.card = 3) ∧
      (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H' ∧ M.card = s + 1 ∧
        ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
      (∀ x z, x < z → UV.IsCompressed {x} {z} H') ∧
      ∃ M : Finset (Finset (Fin n)), M ⊆ H' ∧ M.card = s ∧
        (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧
        ∀ E ∈ M, p ∉ E := by
  classical
  let b : Fin n ↪ Fin (n + 1) := Fin.castSuccEmb
  let B := (Finset.mapEmbedding b).toEmbedding
  let H' := H.preimage B B.injective.injOn
  have hmem (E : Finset (Fin n)) : E ∈ H' ↔ E.map b ∈ H := mem_preimage
  have havoid (E : Finset (Fin n)) : Fin.last n ∉ E.map b := by
    intro h
    obtain ⟨x, _, hx⟩ := mem_map.mp h
    exact (Fin.castSucc_lt_last x).ne hx
  have hpull (E : Finset (Fin (n + 1))) (hE : Fin.last n ∉ E) :
      (E.preimage b b.injective.injOn).map b = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact mem_preimage.mp hy
    · intro hx
      have hxlast : x ≠ Fin.last n := fun h => hE (h ▸ hx)
      obtain ⟨y, hy⟩ := Fin.exists_castSucc_eq.mpr hxlast
      refine mem_map.mpr ⟨y, mem_preimage.mpr ?_, hy⟩
      change y.castSucc ∈ E
      rwa [hy]
  have hmap : H'.map B = H.nonMemberSubfamily (Fin.last n) := by
    ext E
    constructor
    · intro hE
      obtain ⟨E', hE', rfl⟩ := mem_map.mp hE
      exact mem_nonMemberSubfamily.mpr ⟨(hmem E').mp hE', havoid E'⟩
    · intro hE
      obtain ⟨hEH, hElast⟩ := mem_nonMemberSubfamily.mp hE
      have hEq := hpull E hElast
      refine mem_map.mpr ⟨E.preimage b b.injective.injOn, ?_, hEq⟩
      apply (hmem _).mpr
      rwa [hEq]
  have hH' : ∀ E ∈ H', E.card = 3 := by
    intro E hE
    simpa only [card_map] using hH _ ((hmem E).mp hE)
  refine ⟨H', ?_, hH', ?_, ?_, ?_⟩
  · simpa only [card_map] using congrArg card hmap
  · rintro ⟨M, hMH, hMc, hMd⟩
    apply hfree
    refine ⟨M.map B, ?_, by simpa only [card_map] using hMc, ?_⟩
    · intro E hE
      obtain ⟨E', hE', rfl⟩ := mem_map.mp hE
      exact (hmem E').mp (hMH hE')
    · intro E hE F hF hEF
      obtain ⟨E', hE', rfl⟩ := mem_map.mp hE
      obtain ⟨F', hF', rfl⟩ := mem_map.mp hF
      exact (disjoint_map b).mpr
        (hMd E' hE' F' hF' (fun h => hEF (congrArg B h)))
  · intro x z hxz
    have hclose (E : Finset (Fin n)) (hE : E ∈ H') :
        UV.compress {x} {z} E ∈ H' := by
      by_cases hx : x ∈ E
      · simpa [UV.compress, disjoint_singleton_left, hx] using hE
      by_cases hz : z ∈ E
      · have hcompressed : UV.compress {x} {z} E = insert x (E.erase z) := by
          rw [UV.compress_of_disjoint_of_le (disjoint_singleton_left.mpr hx)
            (singleton_subset_iff.mpr hz), sup_eq_union, union_singleton,
            sdiff_singleton_eq_erase, erase_insert_of_ne hxz.ne]
        rw [hcompressed, hmem, map_insert]
        apply Submissions.Erdos1020RainbowLift.Main.insert_mem_of_singleton_stable
          (hstable (b x) (b z) (Fin.castSucc_lt_castSucc_iff.mpr hxz))
        · intro h
          exact notMem_erase z E ((mem_map' b).mp h)
        · intro h
          exact hx (mem_of_mem_erase ((mem_map' b).mp h))
        · change insert (b z) ((E.erase z).map b) ∈ H
          rw [← map_insert, insert_erase hz]
          exact (hmem E).mp hE
      · simpa [UV.compress, singleton_subset_iff, hz] using hE
    change UV.compression {x} {z} H' = H'
    ext E
    rw [UV.mem_compression]
    constructor
    · rintro (⟨hE, _⟩ | ⟨_, F, hF, rfl⟩)
      · exact hE
      · exact hclose F hF
    · intro hE
      exact Or.inl ⟨hE, hclose E hE⟩
  · obtain ⟨M, hMH, hMc, hMd, hMp⟩ := hone
    let A : Finset (Fin (n + 1)) := univ.erase (Fin.last n)
    have hpA : p.castSucc ∈ A :=
      mem_erase.mpr ⟨(Fin.castSucc_lt_last p).ne, mem_univ _⟩
    have hAc : A.card = n := by simp [A]
    have hroom : (A \ {p.castSucc}).card = n - 1 := by
      rw [sdiff_singleton_eq_erase, card_erase_of_mem hpA, hAc]
    have hcap : 3 * Fintype.card M ≤ (A \ {p.castSucc}).card := by
      rw [hroom, Fintype.card_coe, hMc]
      omega
    have hcut : ∀ v ∈ A, ∀ x, x ∉ A → v < x := by
      intro v hv x hx
      have hxlast : x = Fin.last n := by
        by_contra h
        exact hx (mem_erase.mpr ⟨h, mem_univ _⟩)
      subst x
      obtain ⟨y, rfl⟩ := Fin.exists_castSucc_eq.mpr (mem_erase.mp hv).1
      exact Fin.castSucc_lt_last y
    obtain ⟨g, hg, hgd, hgp, hgA⟩ :=
      Submissions.Erdos1020MatchingPack.Main.exists_packed_matching
        H A {p.castSucc} hH hcap hcut hstable (fun c : M => c.val)
        (fun c => hMH c.property)
        (fun c d hcd => hMd c.val c.property d.val d.property
          (fun h => hcd (Subtype.ext h)))
        (fun c => disjoint_singleton_left.mpr (hMp c.val c.property))
    let g' : M → Finset (Fin n) := fun c => (g c).preimage b b.injective.injOn
    have hgmap (c : M) : (g' c).map b = g c := by
      apply hpull
      intro h
      exact (notMem_erase _ _) (hgA c h)
    have hgmem (c : M) : g' c ∈ H' := by
      apply (hmem _).mpr
      rw [hgmap]
      exact hg c
    have hgc (c : M) : (g' c).card = 3 := hH' _ (hgmem c)
    have hgd' : Pairwise (fun c d => Disjoint (g' c) (g' d)) := by
      intro c d hcd
      apply (disjoint_map b).mp
      rw [hgmap, hgmap]
      exact hgd hcd
    have hginj : Function.Injective g' := by
      intro c d h
      by_contra hcd
      obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (g' c).card by rw [hgc]; decide)
      exact (disjoint_left.mp (hgd' hcd)) hx (h ▸ hx)
    refine ⟨univ.image g', ?_, ?_, ?_, ?_⟩
    · intro E hE
      obtain ⟨c, _, rfl⟩ := mem_image.mp hE
      exact hgmem c
    · rw [card_image_of_injective _ hginj, card_univ, Fintype.card_coe, hMc]
    · intro E hE F hF hEF
      obtain ⟨c, _, rfl⟩ := mem_image.mp hE
      obtain ⟨d, _, rfl⟩ := mem_image.mp hF
      exact hgd' (fun h => hEF (congrArg g' h))
    · intro E hE hp
      obtain ⟨c, _, rfl⟩ := mem_image.mp hE
      exact (disjoint_singleton_left.mp (hgp c)) (mem_preimage.mp hp)

end Submissions.Erdos1020MatchingRankThreeOneDeletion.Main

namespace Submissions.Erdos1020MatchingRankThreeOneTail.Main

open Finset

/- The ONE input is retained literally. Its cardinal maximality premise is
available by maximizing before the avoiding-matching case split. -/
variable (hONE : ∀ (n s : ℕ), 32 ≤ s → 3 * (s + 1) ≤ n →
    ∀ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) →
      (∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H) →
      (¬ ∃ K : Finset (Finset (Fin n)), K ⊆ H ∧ K.card = s + 1 ∧
        ∀ e ∈ K, ∀ f ∈ K, e ≠ f → Disjoint e f) →
      (∀ K : Finset (Finset (Fin n)), (∀ e ∈ K, e.card = 3) →
        (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ K ∧ M.card = s + 1 ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) → K.card ≤ H.card) →
      ∀ v : Fin n, (∀ x : Fin n, v ≤ x) →
      (∃ M : Finset (Finset (Fin n)), M ⊆ H.filter (v ∉ ·) ∧ M.card = s ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) →
      H.card ≤ max ((3 * s + 2).choose 3) (n.choose 3 - (n - s).choose 3))

include hONE in
/-- Refined supplies the s=31 base. Deleting the least vertex preserves the
ambient-minus-matching-parameter guard, so no smaller-s EMC premise is needed. -/
theorem bound_of_gap {n s : ℕ} (hs : 31 ≤ s) (hn : 3 * (s + 1) ≤ n)
    (hgap : 107 ≤ n - s) (H : Finset (Finset (Fin n)))
    (hH : ∀ e ∈ H, e.card = 3)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ max ((3 * s + 2).choose 3) (n.choose 3 - (n - s).choose 3) := by
  classical
  induction s using Nat.strong_induction_on generalizing n with
  | h s ih =>
    by_cases hsbase : s = 31
    · subst s
      exact (Submissions.Erdos1020MatchingRefined.Main.star_bound
        (r := 3) (s := 31) (t := 53) (by decide) (by decide) (by omega)
        H hH hfree).trans (le_max_right _ _)
    have hs32 : 32 ≤ s := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨G, hHG, hGu, hGm, hGmax, hGs⟩ :=
      Submissions.Erdos1020MatchingMaximalShift.Main.exists_maximal_shifted H hH hfree
    let v : Fin (m + 1) := ⟨0, by omega⟩
    by_cases havoid : ∃ M : Finset (Finset (Fin (m + 1))),
        M ⊆ G.filter (v ∉ ·) ∧ M.card = s ∧
          ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f
    · exact hHG.trans (hONE (m + 1) s hs32 hn G hGu hGs hGm hGmax
        v (fun x => show 0 ≤ x.val from Nat.zero_le _) havoid)
    let D := G.filter (v ∉ ·)
    have hD : ∀ e ∈ D, e.card = 3 :=
      fun e he => hGu e (mem_filter.mp he).1
    obtain ⟨K, hKc, hKu, hKm⟩ :=
      Submissions.Erdos1020MatchingDeleteVertex.Main.reindex D v
        (fun e he => (mem_filter.mp he).2) hD havoid
    have hprev := ih (s - 1) (by omega) (n := m) (by omega) (by omega)
      (by omega) K hKu (by simpa only [Nat.sub_add_cancel (show 1 ≤ s by omega)] using hKm)
    rw [hKc] at hprev
    have hdegree : (G.filter (v ∈ ·)).card ≤ m.choose 2 := by
      simpa using
        (Submissions.Erdos1020MatchingDegree.Main.card_containing_le hGu
          (s := {v}) (by simp))
    have hpart := card_filter_add_card_filter_not (s := G) (fun e => v ∈ e)
    change (G.filter (v ∈ ·)).card + D.card = G.card at hpart
    have hstep := Submissions.Erdos1020MatchingRankThreeRecurrence.Main.max_step
      (show 1 ≤ s by omega) hn
    simp only [Nat.add_sub_cancel] at hstep
    omega

private theorem choose_three_cast {d : ℕ} (hd : 2 ≤ d) :
    (d.choose 3 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 6 := by
  have hd1 : 1 ≤ d := by omega
  have h := congrArg (fun a : ℕ => (a : ℚ))
    (Nat.descFactorial_eq_factorial_mul_choose d 3)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.factorial_succ, Nat.cast_sub hd, Nat.cast_sub hd1] at h
  nlinarith only [h]

/-- The fixed-gap padded ambient is clique-dominant for every s at least 43. -/
theorem star_le_clique_at_gap107 {s : ℕ} (hs : 43 ≤ s) :
    (s + 107).choose 3 - (107 : ℕ).choose 3 ≤ (3 * s + 2).choose 3 := by
  have hsQ : (43 : ℚ) ≤ s := Nat.cast_le.mpr hs
  have hpoly : 0 ≤ 26 * (s : ℚ) ^ 2 - 291 * (s : ℚ) - 33701 := by
    nlinarith only [hsQ, sq_nonneg ((s : ℚ) - 43)]
  have hscaled := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hpoly
  have hq : ((s + 107).choose 3 : ℚ) ≤
      ((3 * s + 2).choose 3 : ℚ) + ((107 : ℕ).choose 3 : ℚ) := by
    rw [choose_three_cast (d := s + 107) (by omega),
      choose_three_cast (d := 3 * s + 2) (by omega),
      choose_three_cast (d := 107) (by decide)]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hscaled]
  have hnat : (s + 107).choose 3 ≤ (3 * s + 2).choose 3 + (107 : ℕ).choose 3 := by
    exact_mod_cast hq
  omega

private theorem matchingFree_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {k : ℕ} (f : α ↪ β) (H : Finset (Finset α))
    (hfree : ¬ ∃ M : Finset (Finset α), M ⊆ H ∧ M.card = k ∧
      ∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g) :
    ¬ ∃ M : Finset (Finset β),
      M ⊆ H.map (Finset.mapEmbedding f).toEmbedding ∧ M.card = k ∧
        ∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g := by
  classical
  let E := (Finset.mapEmbedding f).toEmbedding
  rintro ⟨M, hMH, hMc, hMd⟩
  obtain ⟨K, hKH, rfl⟩ := Finset.subset_map_iff.mp hMH
  apply hfree
  refine ⟨K, hKH, by simpa only [Finset.card_map] using hMc, ?_⟩
  intro e he g hg heg
  exact (Finset.disjoint_map f).mp
    (hMd (E e) (mem_map.mpr ⟨e, he, rfl⟩)
      (E g) (mem_map.mpr ⟨g, hg, rfl⟩)
      (fun h => heg (E.injective h)))

include hONE in
/-- Removing the fixed-gap guard by an injective padding map gives all ambients
for s at least 43, conditional only on the displayed global ONE hypothesis. -/
theorem bound {n s : ℕ} (hs : 43 ≤ s) (H : Finset (Finset (Fin n)))
    (hH : ∀ e ∈ H, e.card = 3)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) :
    H.card ≤ max ((3 * s + 2).choose 3) (n.choose 3 - (n - s).choose 3) := by
  classical
  by_cases hn : 3 * (s + 1) ≤ n
  · by_cases hgap : 107 ≤ n - s
    · exact bound_of_gap hONE (by omega) hn hgap H hH hfree
    have hnm : n ≤ s + 107 := by omega
    let f : Fin n ↪ Fin (s + 107) := Fin.castLEEmb hnm
    let E := (Finset.mapEmbedding f).toEmbedding
    let J := H.map E
    have hJc : J.card = H.card := card_map _
    have hJu : ∀ e ∈ J, e.card = 3 := by
      intro e he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      simpa [E] using hH e' he'
    have hJm : ¬ ∃ M : Finset (Finset (Fin (s + 107))),
        M ⊆ J ∧ M.card = s + 1 ∧
          ∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g :=
      matchingFree_map f H hfree
    have hbound := bound_of_gap hONE (by omega) (show 3 * (s + 1) ≤ s + 107 by omega)
      (show 107 ≤ s + 107 - s by omega) J hJu hJm
    rw [hJc, show s + 107 - s = 107 by omega,
      max_eq_left (star_le_clique_at_gap107 hs)] at hbound
    exact hbound.trans (le_max_left _ _)
  · have hsub : H ⊆ (univ : Finset (Fin n)).powersetCard 3 := by
      intro e he
      exact mem_powersetCard.mpr ⟨subset_univ e, hH e he⟩
    have hc : H.card ≤ n.choose 3 := by simpa using card_le_card hsub
    exact (hc.trans (Nat.choose_le_choose 3 (by omega))).trans (le_max_left _ _)

end Submissions.Erdos1020MatchingRankThreeOneTail.Main

namespace Submissions.Erdos1020MatchingRankThreeGlobalOne.Main

open Finset

/-- The critical ONE bound extends through ordered last-vertex deletion.
Only the same-s ONE statement is used in the ambient induction. -/
theorem bound {n s : ℕ} (hs : 32 ≤ s) (hn : 3 * (s + 1) ≤ n)
    (H : Finset (Finset (Fin n))) (hH : ∀ E ∈ H, E.card = 3)
    (hstable : ∀ i j : Fin n, i < j → UV.IsCompressed {i} {j} H)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F)
    (v : Fin n) (hleast : ∀ x : Fin n, v ≤ x)
    (hone : ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s ∧
      (∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) ∧ ∀ E ∈ M, v ∉ E) :
    H.card ≤ max ((3 * s + 2).choose 3) (n.choose 3 - (n - s).choose 3) := by
  classical
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hN : 2 * (m + 1 - (3 * s + 2)) ≤ s + 2
    · have hmle : 3 * s + 2 ≤ m + 1 := by omega
      let emb : Fin (3 * s + 2) ↪ Fin (m + 1) :=
        ⟨fun x => ⟨x.val, lt_of_lt_of_le x.isLt hmle⟩,
          fun _ _ h => Fin.ext (congrArg (fun x : Fin (m + 1) => x.val) h)⟩
      let A : Finset (Fin (m + 1)) := univ.map emb
      have hAc : A.card = 3 * s + 2 := by simp [A]
      have hAmem (x : Fin (m + 1)) : x ∈ A ↔ x.val < 3 * s + 2 := by
        constructor
        · intro hx
          obtain ⟨y, _, rfl⟩ := mem_map.mp hx
          exact y.isLt
        · intro hx
          exact mem_map.mpr ⟨⟨x.val, hx⟩, mem_univ _, Fin.ext rfl⟩
      have hA : A.card + 1 = 3 * (s + 1) := by rw [hAc]; omega
      have hcut : ∀ x ∈ A, ∀ y, y ∉ A → x < y := by
        intro x hx y hy
        have hx' := (hAmem x).mp hx
        have hy' : ¬ y.val < 3 * s + 2 := fun h => hy ((hAmem y).mpr h)
        change x.val < y.val
        omega
      have hv0 : v.val = 0 := by
        have h := hleast ⟨0, by omega⟩
        change v.val ≤ 0 at h
        omega
      obtain ⟨M, hMH, hMc, hMd, hMv⟩ := hone
      exact (Submissions.Erdos1020MatchingRankThreeCriticalOne.Main.bound
        hs hn hN H A hH hfree hA hcut hstable v
        ((hAmem v).mpr (by rw [hv0]; omega)) (fun x _ => hleast x)
        M hMH hMc hMd hMv).trans (le_max_left _ _)
    · have hprevn : 3 * (s + 1) ≤ m := by omega
      let p : Fin m := ⟨0, by omega⟩
      have hp : p.castSucc = v := by
        apply Fin.ext
        have h := hleast p.castSucc
        change v.val ≤ 0 at h
        change 0 = v.val
        omega
      obtain ⟨D, hDc, hDu, hDm, hDs, hDone⟩ :=
        Submissions.Erdos1020MatchingRankThreeOneDeletion.Main.reindex
          p (by omega) H hH hstable hfree (by simpa only [hp] using hone)
      have hbound := ih hprevn D hDu hDs hDm p
        (fun x => show 0 ≤ x.val from Nat.zero_le _) hDone
      have hdom := Submissions.Erdos1020MatchingRankThreeThreshold.Main.clique_le_star_of_ambient
        (show 1 ≤ s by omega) (show 7 * s + 5 ≤ 2 * m by omega)
      rw [max_eq_right hdom, hDc] at hbound
      exact (Submissions.Erdos1020MatchingRankThreeOneAmbient.Main.last_vertex_star_step_of_deletion_bound
        (by omega) hn H hH hstable hfree hbound).trans (le_max_right _ _)

end Submissions.Erdos1020MatchingRankThreeGlobalOne.Main

namespace Submissions.Erdos1020MatchingRankThree.Main

open Finset

/-- The global ONE theorem discharges the only remaining premise in the
checked tail reduction, giving all ambients for s at least 43. -/
theorem bound {n s : ℕ} (hs : 43 ≤ s)
    (H : Finset (Finset (Fin n))) (hH : ∀ E ∈ H, E.card = 3)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = s + 1 ∧
      ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) :
    H.card ≤ max ((3 * s + 2).choose 3) (n.choose 3 - (n - s).choose 3) := by
  classical
  apply Submissions.Erdos1020MatchingRankThreeOneTail.Main.bound (hONE := ?_) hs H hH hfree
  intro n s hs hn H hH hstable hfree _ v hleast hone
  obtain ⟨M, hMH, hMc, hMd⟩ := hone
  exact Submissions.Erdos1020MatchingRankThreeGlobalOne.Main.bound hs hn H hH hstable hfree
    v hleast ⟨M, fun E hE => (mem_filter.mp (hMH hE)).1, hMc, hMd,
      fun E hE => (mem_filter.mp (hMH hE)).2⟩

/-- Original natural-valued extremal expression in the rank-three range. -/
theorem proof : ∀ (n r k : ℕ), 3 ≤ r → 1 ≤ k → r = 3 → 44 ≤ k →
    ∀ H : Finset (Finset (Fin n)), (∀ E ∈ H, E.card = r) →
      (¬ ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
        ∀ E ∈ M, ∀ F ∈ M, E ≠ F → Disjoint E F) →
      H.card ≤ max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) := by
  intro n r k _ hk hr hk44 H hH hfree
  subst r
  by_cases hkn : k ≤ n
  · have hpred : k - 1 + 1 = k := by omega
    have hbound := bound (s := k - 1) (by omega) H hH (by simpa only [hpred] using hfree)
    have hclique : 3 * (k - 1) + 2 = 3 * k - 1 := by omega
    have hstar : n - (k - 1) = n - k + 1 := by omega
    simpa only [hclique, hstar] using hbound
  · have hsub : H ⊆ (univ : Finset (Fin n)).powersetCard 3 := by
      intro E hE
      exact mem_powersetCard.mpr ⟨subset_univ E, hH E hE⟩
    have hc : H.card ≤ n.choose 3 := by simpa using card_le_card hsub
    exact (hc.trans (Nat.choose_le_choose 3 (by omega))).trans (le_max_left _ _)

end Submissions.Erdos1020MatchingRankThree.Main
