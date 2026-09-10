import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp

namespace Submissions.BrownErdosSosThresholdReduction.Main

namespace P163

open Finset

abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

def IsUniform (r : ℕ) {n : ℕ} (G : Hypergraph n) : Prop :=
  ∀ edge ∈ G, edge.card = r

def HasCopy {d n : ℕ} (F : Hypergraph d) (G : Hypergraph n) : Prop :=
  ∃ f : Fin d ↪ Fin n, ∀ edge ∈ F, edge.image f ∈ G

def AvoidsFamily (r d e n : ℕ) (G : Hypergraph n) : Prop :=
  IsUniform r G ∧
    ∀ F : Hypergraph d, IsUniform r F → F.card = e → ¬HasCopy F G

/-- A labeled copy yields the same number of distinct edges with support of size at most `d`. -/
theorem support_le_of_hasCopy {d e n : ℕ} {F : Hypergraph d} {G : Hypergraph n}
    (he : F.card = e) (hcopy : HasCopy F G) :
    ∃ H : Hypergraph n, H ⊆ G ∧ H.card = e ∧ (H.biUnion id).card ≤ d := by
  classical
  obtain ⟨f, hf⟩ := hcopy
  refine ⟨F.image (fun A => A.image f), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    exact hf B hB
  · exact (card_image_of_injective F (image_injective f.injective)).trans he
  · have hsub : (F.image (fun A => A.image f)).biUnion id ⊆
        (univ : Finset (Fin d)).image f := by
      intro x hx
      obtain ⟨A, hA, hx⟩ := mem_biUnion.mp hx
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨y, mem_univ y, rfl⟩
    calc
      _ ≤ ((univ : Finset (Fin d)).image f).card := card_le_card hsub
      _ ≤ d := card_image_le.trans (by simp)

/-- Padding the support to `d` vertices accounts for the isolated labeled vertices. -/
theorem hasCopy_of_support {r d e n : ℕ} {G H : Hypergraph n}
    (hG : IsUniform r G) (hdn : d ≤ n) (hHG : H ⊆ G)
    (hHe : H.card = e) (hHd : (H.biUnion id).card ≤ d) :
    ∃ F : Hypergraph d, IsUniform r F ∧ F.card = e ∧ HasCopy F G := by
  classical
  obtain ⟨S, hUS, _, hSd⟩ := exists_subsuperset_card_eq
    (subset_univ (H.biUnion id)) hHd (by simpa using hdn)
  let equiv : S ≃ Fin d := Finset.equivFinOfCardEq hSd
  let f : Fin d ↪ Fin n :=
    equiv.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hfS : ∀ v ∈ S, ∃ x : Fin d, f x = v := by
    intro v hv
    refine ⟨equiv ⟨v, hv⟩, ?_⟩
    change (equiv.symm (equiv ⟨v, hv⟩)).val = v
    simp
  let pull : Finset (Fin n) → Finset (Fin d) :=
    fun A => univ.filter fun x => f x ∈ A
  have hround : ∀ A ∈ H, (pull A).image f = A := by
    intro A hA
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hx).2
    · intro hv
      have hvS : v ∈ S := hUS (mem_biUnion.mpr ⟨A, hA, hv⟩)
      obtain ⟨x, rfl⟩ := hfS v hvS
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ x, hv⟩, rfl⟩
  have hpull : Set.InjOn pull (↑H : Set (Finset (Fin n))) := by
    intro A hA B hB hAB
    calc
      A = (pull A).image f := (hround A hA).symm
      _ = (pull B).image f := congrArg (fun s : Finset (Fin d) => s.image f) hAB
      _ = B := hround B hB
  refine ⟨H.image pull, ?_, ?_, f, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    calc
      (pull B).card = ((pull B).image f).card :=
        (card_image_of_injective _ f.injective).symm
      _ = B.card := congrArg Finset.card (hround B hB)
      _ = r := hG B (hHG hB)
  · exact (card_image_of_injOn hpull).trans hHe
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    rw [hround B hB]
    exact hHG hB

/-- For `n ≥ d`, the canonical labeled-copy definition is exactly support avoidance. -/
theorem avoidsFamily_iff_support {r d e n : ℕ} {G : Hypergraph n}
    (hG : IsUniform r G) (hdn : d ≤ n) :
    AvoidsFamily r d e n G ↔
      ∀ H : Hypergraph n, H ⊆ G → H.card = e → d < (H.biUnion id).card := by
  constructor
  · intro hav H hHG hHe
    by_contra hbad
    obtain ⟨F, hFu, hFe, hcopy⟩ :=
      hasCopy_of_support hG hdn hHG hHe (Nat.le_of_not_gt hbad)
    exact hav.2 F hFu hFe hcopy
  · intro h
    refine ⟨hG, ?_⟩
    intro F hFu hFe hcopy
    obtain ⟨H, hHG, hHe, hHd⟩ := support_le_of_hasCopy hFe hcopy
    exact (Nat.not_lt_of_ge hHd) (h H hHG hHe)

end P163

namespace P163

open Finset

variable {n r d e : ℕ}

/-- Edges containing a common core use at most the core plus the remaining vertices. -/
theorem common_core_bound (G : Hypergraph n) (S : Finset (Fin n))
    (hG : IsUniform r G) (hS : ∀ A ∈ G, S ⊆ A) :
    (G.biUnion id).card ≤ S.card + G.card * (r - S.card) := by
  classical
  have hcover : G.biUnion id ⊆ S ∪ G.biUnion (fun A => A \ S) := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
    by_cases hxS : x ∈ S
    · exact mem_union_left _ hxS
    · exact mem_union_right _ (mem_biUnion.mpr ⟨A, hA, mem_sdiff.mpr ⟨hxA, hxS⟩⟩)
  calc
    (G.biUnion id).card ≤ (S ∪ G.biUnion (fun A => A \ S)).card := card_le_card hcover
    _ ≤ S.card + (G.biUnion (fun A => A \ S)).card := card_union_le _ _
    _ ≤ S.card + ∑ A ∈ G, (A \ S).card := Nat.add_le_add_left card_biUnion_le _
    _ = S.card + G.card * (r - S.card) := by
      congr 1
      calc
        ∑ A ∈ G, (A \ S).card = ∑ A ∈ G, (r - S.card) := by
          apply sum_congr rfl
          intro A hA
          rw [card_sdiff_of_subset (hS A hA), hG A hA]
        _ = G.card * (r - S.card) := by simp

/-- Support avoidance forces bounded pair codegrees, already one vertex below the BES threshold. -/
theorem pair_codegree_bound (G : Hypergraph n) (hG : IsUniform r G)
    (havoid : ∀ H ⊆ G, H.card = e → d < (H.biUnion id).card)
    (hd : 2 + e * (r - 2) ≤ d) (S : Finset (Fin n)) (hS : S.card = 2) :
    (G.filter (fun A => S ⊆ A)).card < e := by
  classical
  by_contra h
  obtain ⟨H, hH, hHe⟩ := exists_subset_card_eq (Nat.le_of_not_gt h)
  have hHG : H ⊆ G := fun A hA => (mem_filter.mp (hH hA)).1
  have hHU : IsUniform r H := fun A hA => hG A (hHG hA)
  have hHS : ∀ A ∈ H, S ⊆ A := fun A hA => (mem_filter.mp (hH hA)).2
  have hbound := common_core_bound H S hHU hHS
  rw [hS, hHe] at hbound
  exact (Nat.not_lt_of_ge (hbound.trans hd)) (havoid H hHG hHe)

def IsLinear (G : Hypergraph n) : Prop :=
  ∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).card ≤ 1

/-- A maximal linear family meets every original edge in at least one pair. -/
theorem maximal_linear_cover (G : Hypergraph n) (hG : IsUniform r G) (hr : 2 ≤ r) :
    ∃ L ⊆ G, IsLinear L ∧ ∀ A ∈ G, ∃ B ∈ L, 2 ≤ (A ∩ B).card := by
  classical
  let C := G.powerset.filter IsLinear
  have hC : C.Nonempty := ⟨∅, by simp [C, IsLinear]⟩
  obtain ⟨L, hL, hmax⟩ := C.exists_maximal hC
  have hLG : L ⊆ G := mem_powerset.mp (mem_filter.mp hL).1
  have hlin : IsLinear L := (mem_filter.mp hL).2
  refine ⟨L, hLG, hlin, ?_⟩
  intro A hA
  by_contra h
  have hsmall : ∀ B ∈ L, (A ∩ B).card ≤ 1 := by
    intro B hB
    have : ¬2 ≤ (A ∩ B).card := fun hcard => h ⟨B, hB, hcard⟩
    omega
  have hins : IsLinear (insert A L) := by
    intro B hB D hD hne
    rcases mem_insert.mp hB with rfl | hBL
    · rcases mem_insert.mp hD with rfl | hDL
      · exact (hne rfl).elim
      · exact hsmall D hDL
    · rcases mem_insert.mp hD with rfl | hDL
      · simpa [inter_comm] using hsmall B hBL
      · exact hlin B hBL D hDL hne
  have hinC : insert A L ∈ C :=
    mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hA hLG), hins⟩
  have hAL : A ∈ L := hmax hinC (subset_insert A L) (mem_insert_self A L)
  have hs := hsmall A hAL
  rw [inter_self, hG A hA] at hs
  omega

/-- Finite linearization with a uniform constant, for arbitrary simple hypergraphs. -/
theorem linear_subgraph (G : Hypergraph n) (hG : IsUniform r G) (hr : 2 ≤ r)
    (hcode : ∀ S : Finset (Fin n), S.card = 2 →
      (G.filter (fun A => S ⊆ A)).card < e) :
    ∃ L ⊆ G, IsLinear L ∧ G.card ≤ L.card * (r.choose 2 * (e - 1)) := by
  classical
  obtain ⟨L, hLG, hlin, hcover⟩ := maximal_linear_cover G hG hr
  refine ⟨L, hLG, hlin, ?_⟩
  let stars := fun S : Finset (Fin n) => G.filter (fun A => S ⊆ A)
  have hcovered : G ⊆ L.biUnion (fun B => (B.powersetCard 2).biUnion stars) := by
    intro A hA
    obtain ⟨B, hB, hAB⟩ := hcover A hA
    obtain ⟨S, hS, hS2⟩ := exists_subset_card_eq hAB
    have hSB : S ⊆ B := fun x hx => (mem_inter.mp (hS hx)).2
    have hSA : S ⊆ A := fun x hx => (mem_inter.mp (hS hx)).1
    exact mem_biUnion.mpr ⟨B, hB, mem_biUnion.mpr
      ⟨S, mem_powersetCard.mpr ⟨hSB, hS2⟩, mem_filter.mpr ⟨hA, hSA⟩⟩⟩
  calc
    G.card ≤ (L.biUnion (fun B => (B.powersetCard 2).biUnion stars)).card :=
      card_le_card hcovered
    _ ≤ ∑ B ∈ L, ((B.powersetCard 2).biUnion stars).card := card_biUnion_le
    _ ≤ ∑ B ∈ L, r.choose 2 * (e - 1) := by
      apply sum_le_sum
      intro B hB
      calc
        ((B.powersetCard 2).biUnion stars).card ≤ ∑ S ∈ B.powersetCard 2, (stars S).card :=
          card_biUnion_le
        _ ≤ ∑ S ∈ B.powersetCard 2, (e - 1) := by
          apply sum_le_sum
          intro S hS
          have hlt := hcode S (mem_powersetCard.mp hS).2
          dsimp [stars]
          omega
        _ = r.choose 2 * (e - 1) := by simp [hG B (hLG hB)]
    _ = L.card * (r.choose 2 * (e - 1)) := by simp

/-- The finite reduction in the original labeled-copy vocabulary. -/
theorem avoids_linear_subgraph (G : Hypergraph n) (hG : AvoidsFamily r d e n G)
    (hr : 2 ≤ r) (hd : 2 + e * (r - 2) ≤ d) (hdn : d ≤ n) :
    ∃ L ⊆ G, AvoidsFamily r d e n L ∧ IsLinear L ∧
      G.card ≤ L.card * (r.choose 2 * (e - 1)) := by
  have hsupport := (avoidsFamily_iff_support hG.1 hdn).mp hG
  obtain ⟨L, hLG, hlin, hcard⟩ :=
    linear_subgraph G hG.1 hr (pair_codegree_bound G hG.1 hsupport hd)
  refine ⟨L, hLG, ?_, hlin, hcard⟩
  apply (avoidsFamily_iff_support (fun A hA => hG.1 A (hLG hA)) hdn).mpr
  intro H hHL hHe
  exact hsupport H (hHL.trans hLG) hHe

end P163

namespace P163

open Finset

variable {n r k e : ℕ}

/-- Restoring the discarded vertices costs at most `r-k` per edge. -/
theorem support_bound_of_projection (G : Hypergraph n) (hG : IsUniform r G)
    (p : Finset (Fin n) → Finset (Fin n))
    (hsub : ∀ A ∈ G, p A ⊆ A) (hcard : ∀ A ∈ G, (p A).card = k) :
    (G.biUnion id).card ≤ ((G.image p).biUnion id).card + G.card * (r - k) := by
  classical
  have hcover : G.biUnion id ⊆
      (G.image p).biUnion id ∪ G.biUnion (fun A => A \ p A) := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx
    by_cases hxp : x ∈ p A
    · exact mem_union_left _
        (mem_biUnion.mpr ⟨p A, mem_image.mpr ⟨A, hA, rfl⟩, hxp⟩)
    · exact mem_union_right _
        (mem_biUnion.mpr ⟨A, hA, mem_sdiff.mpr ⟨hxA, hxp⟩⟩)
  calc
    (G.biUnion id).card ≤
        ((G.image p).biUnion id ∪ G.biUnion (fun A => A \ p A)).card :=
      card_le_card hcover
    _ ≤ ((G.image p).biUnion id).card + (G.biUnion (fun A => A \ p A)).card :=
      card_union_le _ _
    _ ≤ ((G.image p).biUnion id).card + ∑ A ∈ G, (A \ p A).card :=
      Nat.add_le_add_left card_biUnion_le _
    _ = ((G.image p).biUnion id).card + G.card * (r - k) := by
      congr 1
      calc
        ∑ A ∈ G, (A \ p A).card = ∑ A ∈ G, (r - k) := by
          apply sum_congr rfl
          intro A hA
          rw [card_sdiff_of_subset (hsub A hA), hG A hA, hcard A hA]
        _ = G.card * (r - k) := by simp

/-- In a linear hypergraph, choosing at least two vertices per edge cannot identify edges. -/
theorem projection_injOn (G : Hypergraph n) (hlin : IsLinear G)
    (p : Finset (Fin n) → Finset (Fin n)) (hk : 2 ≤ k)
    (hsub : ∀ A ∈ G, p A ⊆ A) (hcard : ∀ A ∈ G, (p A).card = k) :
    Set.InjOn p (↑G : Set (Finset (Fin n))) := by
  intro A hA B hB hAB
  by_contra hne
  have hpAB : p A ⊆ A ∩ B := by
    intro x hx
    exact mem_inter.mpr ⟨hsub A hA hx, hsub B hB (hAB ▸ hx)⟩
  have hle := (card_le_card hpAB).trans (hlin A hA B hB hne)
  rw [hcard A hA] at hle
  omega

/-- Shrinking each edge preserves linearity. -/
theorem projection_linear (G : Hypergraph n) (hlin : IsLinear G)
    (p : Finset (Fin n) → Finset (Fin n)) (hsub : ∀ A ∈ G, p A ⊆ A) :
    IsLinear (G.image p) := by
  classical
  intro C hC D hD hne
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
  have hpAB : p A ∩ p B ⊆ A ∩ B := by
    intro x hx
    exact mem_inter.mpr ⟨hsub A hA (mem_inter.mp hx).1,
      hsub B hB (mem_inter.mp hx).2⟩
  exact (card_le_card hpAB).trans
    (hlin A hA B hB (fun h => hne (congrArg p h)))

/-- Every projected subfamily has a unique lift with the same number of edges. -/
theorem lift_projection_subfamily (G : Hypergraph n) (hG : IsUniform r G)
    (p : Finset (Fin n) → Finset (Fin n))
    (hinj : Set.InjOn p (↑G : Set (Finset (Fin n))))
    (hsub : ∀ A ∈ G, p A ⊆ A) (hcard : ∀ A ∈ G, (p A).card = k)
    (J : Hypergraph n) (hJG : J ⊆ G.image p) :
    ∃ H : Hypergraph n, H ⊆ G ∧ H.card = J.card ∧
      (H.biUnion id).card ≤ (J.biUnion id).card + J.card * (r - k) := by
  classical
  let H := G.filter fun A => p A ∈ J
  have hHG : H ⊆ G := filter_subset _ _
  have himage : H.image p = J := by
    apply Subset.antisymm
    · intro C hC
      obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
      exact (mem_filter.mp hA).2
    · intro C hC
      obtain ⟨A, hA, rfl⟩ := mem_image.mp (hJG hC)
      exact mem_image.mpr ⟨A, mem_filter.mpr ⟨hA, hC⟩, rfl⟩
  have hinjH : Set.InjOn p (↑H : Set (Finset (Fin n))) := by
    intro A hA B hB hAB
    exact hinj (hHG hA) (hHG hB) hAB
  have hHcard : H.card = J.card := by
    calc
      H.card = (H.image p).card := (card_image_of_injOn hinjH).symm
      _ = J.card := congrArg Finset.card himage
  refine ⟨H, hHG, hHcard, ?_⟩
  have hbound := support_bound_of_projection H (fun A hA => hG A (hHG hA)) p
    (fun A hA => hsub A (hHG hA)) (fun A hA => hcard A (hHG hA))
  simpa only [himage, hHcard] using hbound

/-- A linear uniform hypergraph projects to a linear triple system without losing edges. -/
theorem linear_three_projection (G : Hypergraph n) (hG : IsUniform r G)
    (hr : 3 ≤ r) (hlin : IsLinear G) :
    ∃ T : Hypergraph n, IsUniform 3 T ∧ IsLinear T ∧ T.card = G.card ∧
      ∀ J : Hypergraph n, J ⊆ T →
        ∃ H : Hypergraph n, H ⊆ G ∧ H.card = J.card ∧
          (H.biUnion id).card ≤ (J.biUnion id).card + J.card * (r - 3) := by
  classical
  have hex : ∀ A : Finset (Fin n), ∃ B : Finset (Fin n),
      A ∈ G → B ⊆ A ∧ B.card = 3 := by
    intro A
    by_cases hA : A ∈ G
    · obtain ⟨B, hBA, hB3⟩ := exists_subset_card_eq
        (show 3 ≤ A.card by simpa only [hG A hA] using hr)
      exact ⟨B, fun _ => ⟨hBA, hB3⟩⟩
    · exact ⟨∅, fun h => (hA h).elim⟩
  let p : Finset (Fin n) → Finset (Fin n) := fun A => Classical.choose (hex A)
  have hsub : ∀ A ∈ G, p A ⊆ A :=
    fun A hA => (Classical.choose_spec (hex A) hA).1
  have hcard : ∀ A ∈ G, (p A).card = 3 :=
    fun A hA => (Classical.choose_spec (hex A) hA).2
  have hinj := projection_injOn G hlin p (by decide : 2 ≤ 3) hsub hcard
  refine ⟨G.image p, ?_, projection_linear G hlin p hsub,
    card_image_of_injOn hinj, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    exact hcard B hB
  · intro J hJ
    exact lift_projection_subfamily G hG p hinj hsub hcard J hJ

/-- The finite BES support-avoidance property descends from linear `r`-graphs to triples. -/
theorem linear_three_projection_avoids (G : Hypergraph n) (hG : IsUniform r G)
    (hr : 3 ≤ r) (hlin : IsLinear G)
    (havoid : ∀ H : Hypergraph n, H ⊆ G → H.card = e →
      (r - 2) * e + 3 < (H.biUnion id).card) :
    ∃ T : Hypergraph n, IsUniform 3 T ∧ IsLinear T ∧ T.card = G.card ∧
      ∀ J : Hypergraph n, J ⊆ T → J.card = e → e + 3 < (J.biUnion id).card := by
  obtain ⟨T, hTu, hTl, hTc, hlift⟩ := linear_three_projection G hG hr hlin
  refine ⟨T, hTu, hTl, hTc, ?_⟩
  intro J hJT hJe
  obtain ⟨H, hHG, hHJ, hbound⟩ := hlift J hJT
  have hHe : H.card = e := hHJ.trans hJe
  rw [hJe] at hbound
  by_contra hbad
  have hupper := hbound.trans
    (Nat.add_le_add_right (Nat.le_of_not_gt hbad) (e * (r - 3)))
  have heq : (e + 3) + e * (r - 3) = (r - 2) * e + 3 := by
    have hrsub : r - 2 = (r - 3) + 1 := by omega
    rw [hrsub, Nat.add_mul, Nat.one_mul, Nat.mul_comm (r - 3) e]
    omega
  rw [heq] at hupper
  exact (Nat.not_lt_of_ge hupper) (havoid H hHG hHe)

end P163

namespace P163

open Filter Finset
open scoped Topology

noncomputable def extremal (r d e n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : Hypergraph n =>
      if AvoidsFamily r d e n G then G.card else 0

def HasQuadraticVanishing (r d e : ℕ) : Prop :=
  (fun n => (extremal r d e n : ℝ)) =o[atTop]
    (fun n => (n : ℝ) ^ 2)

theorem card_le_extremal {r d e n : ℕ} {G : Hypergraph n}
    (hG : AvoidsFamily r d e n G) : G.card ≤ extremal r d e n := by
  classical
  simpa [extremal, hG] using
    (le_sup (f := fun H : Hypergraph n => if AvoidsFamily r d e n H then H.card else 0)
      (mem_univ G))

theorem real_extremal_le {r d e n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ G : Hypergraph n, AvoidsFamily r d e n G → (G.card : ℝ) ≤ b) :
    (extremal r d e n : ℝ) ≤ b := by
  classical
  obtain ⟨G, _, hG⟩ := exists_mem_eq_sup (univ : Finset (Hypergraph n)) univ_nonempty
    (fun H : Hypergraph n => if AvoidsFamily r d e n H then H.card else 0)
  unfold extremal
  rw [hG]
  split_ifs with hav
  · exact h G hav
  · simpa using hb

theorem vanishing_iff_support_bound (r d e : ℕ) : HasQuadraticVanishing r d e ↔
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ G : Hypergraph n,
      IsUniform r G →
      (∀ H ⊆ G, H.card = e → d < (H.biUnion id).card) →
      (G.card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  constructor
  · intro h δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (Asymptotics.isLittleO_iff.mp h hδ)
    refine ⟨max N d, ?_⟩
    intro n hn G hu hs
    have hav := (avoidsFamily_iff_support hu (le_trans (le_max_right _ _) hn)).mpr hs
    have hle : (G.card : ℝ) ≤ (extremal r d e n : ℝ) := by
      exact_mod_cast card_le_extremal hav
    exact hle.trans (by
      simpa only [norm_pow, Real.norm_natCast] using hN n (le_trans (le_max_left _ _) hn))
  · intro h
    apply Asymptotics.isLittleO_iff.mpr
    intro δ hδ
    obtain ⟨N, hN⟩ := h δ hδ
    refine eventually_atTop.mpr ⟨max N d, ?_⟩
    intro n hn
    have hb : (extremal r d e n : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
      apply real_extremal_le (by positivity)
      intro G hav
      exact hN n (le_trans (le_max_left _ _) hn) G hav.1
        ((avoidsFamily_iff_support hav.1 (le_trans (le_max_right _ _) hn)).mp hav)
    simpa only [norm_pow, Real.norm_natCast] using hb

/-- Exact support threshold transfer from linear triple systems to arbitrary uniformity. -/
theorem upper_of_linear_triples (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e)
    (hthree : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ T : Hypergraph n,
      IsUniform 3 T → IsLinear T →
      (∀ J ⊆ T, J.card = e → e + 3 < (J.biUnion id).card) →
      (T.card : ℝ) ≤ δ * (n : ℝ) ^ 2) :
    HasQuadraticVanishing r ((r - 2) * e + 3) e := by
  apply (vanishing_iff_support_bound _ _ _).mpr
  intro δ hδ
  let C : ℕ := r.choose 2 * (e - 1)
  have hCnat : 0 < C := Nat.mul_pos (Nat.choose_pos (by omega)) (by omega)
  have hC : 0 < (C : ℝ) := by exact_mod_cast hCnat
  obtain ⟨N, hN⟩ := hthree (δ / C) (div_pos hδ hC)
  refine ⟨N, ?_⟩
  intro n hn G hu hs
  have hcode := pair_codegree_bound G hu hs
    (by rw [Nat.mul_comm e (r - 2)]; omega : 2 + e * (r - 2) ≤ (r - 2) * e + 3)
  obtain ⟨L, hLG, hlin, hcard⟩ := linear_subgraph G hu (by omega) hcode
  have hLu : IsUniform r L := fun A hA => hu A (hLG hA)
  have hLs : ∀ H ⊆ L, H.card = e → (r - 2) * e + 3 < (H.biUnion id).card :=
    fun H hHL hHe => hs H (hHL.trans hLG) hHe
  obtain ⟨T, hTu, hTl, hTc, hTs⟩ := linear_three_projection_avoids L hLu hr hlin hLs
  have hT := hN n hn T hTu hTl hTs
  have hGL : (G.card : ℝ) ≤ (L.card : ℝ) * C := by exact_mod_cast hcard
  rw [hTc] at hT
  calc
    (G.card : ℝ) ≤ (L.card : ℝ) * C := hGL
    _ ≤ (δ / C * (n : ℝ) ^ 2) * C := mul_le_mul_of_nonneg_right hT hC.le
    _ = δ * (n : ℝ) ^ 2 := by
      rw [mul_right_comm, div_mul_cancel₀ _ hC.ne']

/-- The arbitrary-uniformity upper question reduces to its triple-system case. -/
theorem upper_of_triples (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e)
    (hthree : HasQuadraticVanishing 3 (e + 3) e) :
    HasQuadraticVanishing r ((r - 2) * e + 3) e := by
  apply upper_of_linear_triples r e hr he
  intro δ hδ
  obtain ⟨N, hN⟩ := (vanishing_iff_support_bound _ _ _).mp hthree δ hδ
  exact ⟨N, fun n hn T hu _ hs => hN n hn T hu hs⟩

end P163

/-!
The linear (6,3) theorem of Ruzsa and Szemerédi, via Mathlib's triangle-removal
and tripartite-graph development by Yaël Dillies and Bhavik Mehta. The sorted
triple encoding also appears in Aristotle/JoshuaB's formalization of Erdős 716;
see literature.md for source provenance. This module treats linear hypergraphs
directly; Core.linear_subgraph handles the passage from arbitrary hypergraphs.
-/

namespace P163

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles

variable {n : ℕ}

def triangleIndices (G : Hypergraph n) : Finset (Fin n × Fin n × Fin n) :=
  univ.filter fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ {p.1, p.2.1, p.2.2} ∈ G

@[simp] theorem mem_triangleIndices {G : Hypergraph n} {p : Fin n × Fin n × Fin n} :
    p ∈ triangleIndices G ↔
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ {p.1, p.2.1, p.2.2} ∈ G := by
  classical
  simp [triangleIndices]

private theorem sorted_triple_injective {a b c x y z : Fin n}
    (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (h : ({a, b, c} : Finset (Fin n)) = {x, y, z}) :
    (a, b, c) = (x, y, z) := by
  simp only [Finset.ext_iff, mem_insert, mem_singleton] at h
  have ha := (h a).mp (Or.inl rfl)
  have hb := (h b).mp (Or.inr (Or.inl rfl))
  have hc := (h c).mp (Or.inr (Or.inr rfl))
  have hx := (h x).mpr (Or.inl rfl)
  have hy := (h y).mpr (Or.inr (Or.inl rfl))
  have hz := (h z).mpr (Or.inr (Or.inr rfl))
  have heq : a = x ∧ b = y ∧ c = z := by omega
  rcases heq with ⟨rfl, rfl, rfl⟩
  rfl

theorem card_triangleIndices {G : Hypergraph n} (hG : IsUniform 3 G) :
    (triangleIndices G).card = G.card := by
  classical
  apply card_bij (fun p _ => ({p.1, p.2.1, p.2.2} : Finset (Fin n)))
  · intro p hp
    exact (mem_triangleIndices.mp hp).2.2
  · intro p hp q hq heq
    have hp' := mem_triangleIndices.mp hp
    have hq' := mem_triangleIndices.mp hq
    exact sorted_triple_injective hp'.1 hp'.2.1 hq'.1 hq'.2.1 heq
  · intro A hA
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (hG A hA)
    have hsort : ∃ x y z : Fin n, x < y ∧ y < z ∧
        ({x, y, z} : Finset (Fin n)) = {a, b, c} := by
      rcases lt_or_gt_of_ne hab with hab | hba <;>
        rcases lt_or_gt_of_ne hac with hac | hca <;>
        rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨a, b, c, hab, hbc, rfl⟩
      · exact ⟨a, c, b, hac, hcb, by ext; simp; tauto⟩
      · omega
      · exact ⟨c, a, b, hca, hab, by ext; simp; tauto⟩
      · exact ⟨b, a, c, hba, hac, by ext; simp; tauto⟩
      · omega
      · exact ⟨b, c, a, hbc, hca, by ext; simp; tauto⟩
      · exact ⟨c, b, a, hcb, hba, by ext; simp; tauto⟩
    obtain ⟨x, y, z, hxy, hyz, hset⟩ := hsort
    exact ⟨(x, y, z), mem_triangleIndices.mpr ⟨hxy, hyz, by rw [hset]; exact hA⟩, hset⟩

private theorem linear_pair_eq {G : Hypergraph n} (hlin : IsLinear G)
    {A B : Finset (Fin n)} (hA : A ∈ G) (hB : B ∈ G)
    {u v : Fin n} (huv : u ≠ v) (huA : u ∈ A) (hvA : v ∈ A)
    (huB : u ∈ B) (hvB : v ∈ B) : A = B := by
  classical
  by_contra hne
  have hsub : ({u, v} : Finset (Fin n)) ⊆ A ∩ B := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_inter]
    exact ⟨⟨huA, huB⟩, hvA, hvB⟩
  have hcard := card_le_card hsub
  have hsmall := hlin A hA B hB hne
  simp [huv] at hcard
  omega

theorem triangleIndices_explicit {G : Hypergraph n} (hlin : IsLinear G) :
    ExplicitDisjoint (triangleIndices G) := by
  classical
  constructor
  · intro a b c a' hp hq
    obtain ⟨hab, hbc, hp⟩ := mem_triangleIndices.mp hp
    obtain ⟨ha'b, _, hq⟩ := mem_triangleIndices.mp hq
    have heq := linear_pair_eq hlin hp hq hbc.ne
      (by simp : b ∈ ({a, b, c} : Finset (Fin n))) (by simp : c ∈ ({a, b, c} : Finset (Fin n)))
      (by simp : b ∈ ({a', b, c} : Finset (Fin n))) (by simp : c ∈ ({a', b, c} : Finset (Fin n)))
    exact congrArg Prod.fst (sorted_triple_injective hab hbc ha'b hbc heq)
  · intro a b c b' hp hq
    obtain ⟨hab, hbc, hp⟩ := mem_triangleIndices.mp hp
    obtain ⟨hab', hb'c, hq⟩ := mem_triangleIndices.mp hq
    have heq := linear_pair_eq hlin hp hq (hab.trans hbc).ne
      (by simp : a ∈ ({a, b, c} : Finset (Fin n))) (by simp : c ∈ ({a, b, c} : Finset (Fin n)))
      (by simp : a ∈ ({a, b', c} : Finset (Fin n))) (by simp : c ∈ ({a, b', c} : Finset (Fin n)))
    exact congrArg (fun p => p.2.1) (sorted_triple_injective hab hbc hab' hb'c heq)
  · intro a b c c' hp hq
    obtain ⟨hab, hbc, hp⟩ := mem_triangleIndices.mp hp
    obtain ⟨_, hbc', hq⟩ := mem_triangleIndices.mp hq
    have heq := linear_pair_eq hlin hp hq hab.ne
      (by simp : a ∈ ({a, b, c} : Finset (Fin n))) (by simp : b ∈ ({a, b, c} : Finset (Fin n)))
      (by simp : a ∈ ({a, b, c'} : Finset (Fin n))) (by simp : b ∈ ({a, b, c'} : Finset (Fin n)))
    exact congrArg (fun p => p.2.2) (sorted_triple_injective hab hbc hab hbc' heq)

theorem triangleIndices_noAccidental {G : Hypergraph n}
    (havoid : ∀ H ⊆ G, H.card = 3 → 6 < (H.biUnion id).card) :
    NoAccidental (triangleIndices G) := by
  classical
  constructor
  intro a a' b b' c c' hp hq hs
  obtain ⟨ha'b, hbc, hp⟩ := mem_triangleIndices.mp hp
  obtain ⟨hab', hb'c, hq⟩ := mem_triangleIndices.mp hq
  obtain ⟨hab, hbc', hs⟩ := mem_triangleIndices.mp hs
  by_contra h
  push Not at h
  let A : Finset (Fin n) := {a', b, c}
  let B : Finset (Fin n) := {a, b', c}
  let C : Finset (Fin n) := {a, b, c'}
  have hAB : A ≠ B := fun heq => h.1 (congrArg Prod.fst
    (sorted_triple_injective ha'b hbc hab' hb'c heq)).symm
  have hAC : A ≠ C := fun heq => h.1 (congrArg Prod.fst
    (sorted_triple_injective ha'b hbc hab hbc' heq)).symm
  have hBC : B ≠ C := fun heq => h.2.1 (congrArg (fun p => p.2.1)
    (sorted_triple_injective hab' hb'c hab hbc' heq)).symm
  have hH := havoid {A, B, C} (by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hp, hq, hs⟩)
    (by simp [hAB, hAC, hBC])
  have hsub : (({A, B, C} : Hypergraph n).biUnion id) ⊆
      ({a, a', b, b', c, c'} : Finset (Fin n)) := by
    simp [A, B, C, subset_iff] <;> tauto
  have hcard := card_le_card hsub
  have h₁ := card_insert_le a ({a', b, b', c, c'} : Finset (Fin n))
  have h₂ := card_insert_le a' ({b, b', c, c'} : Finset (Fin n))
  have h₃ := card_insert_le b ({b', c, c'} : Finset (Fin n))
  have h₄ := card_insert_le b' ({c, c'} : Finset (Fin n))
  have h₅ := card_insert_le c ({c'} : Finset (Fin n))
  simp only [card_singleton] at h₅
  omega

theorem linear_card_le_sq {G : Hypergraph n} (hG : IsUniform 3 G) (hlin : IsLinear G) :
    G.card ≤ n ^ 2 := by
  classical
  haveI := triangleIndices_explicit hlin
  have hinj : Function.Injective (fun p : {p // p ∈ triangleIndices G} => (p.val.1, p.val.2.1)) := by
    intro p q heq
    apply Subtype.ext
    obtain ⟨p, hp⟩ := p
    obtain ⟨q, hq⟩ := q
    rcases p with ⟨a, b, c⟩
    rcases q with ⟨a', b', c'⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have : c = c' := ExplicitDisjoint.inj₂ hp hq
    simp [this]
  have hc := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
    card_triangleIndices hG, pow_two] using hc

/-- The known linear (6,3) upper bound, with all density and size quantifiers explicit. -/
theorem linear_six_three_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : Hypergraph n,
      IsUniform 3 G → IsLinear G →
      (∀ H ⊆ G, H.card = 3 → 6 < (H.biUnion id).card) →
      (G.card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  classical
  let c := triangleRemovalBound (δ / 9)
  have hc : 0 < c := triangleRemovalBound_pos (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  refine ⟨N, ?_⟩
  intro n hn G hG hlin havoid
  have hnc : 1 / c < (n : ℝ) := hN.trans_le (Nat.cast_le.mpr hn)
  have hnpos : 0 < (n : ℝ) := (div_pos zero_lt_one hc).trans hnc
  have hcn : 1 < c * (n : ℝ) := by
    have := (div_lt_iff₀ hc).mp hnc
    nlinarith
  let t := triangleIndices G
  haveI : ExplicitDisjoint t := triangleIndices_explicit hlin
  haveI : NoAccidental t := triangleIndices_noAccidental havoid
  by_contra hsmall
  have hlarge : δ * (n : ℝ) ^ 2 < (G.card : ℝ) := lt_of_not_ge hsmall
  have hfar : (graph t).FarFromTriangleFree (δ / 9) := by
    apply farFromTriangleFree
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_add]
    change δ / 9 * ((n : ℝ) + n + n) ^ 2 ≤ ((triangleIndices G).card : ℝ)
    rw [card_triangleIndices hG]
    nlinarith
  have hmany := hfar.le_card_cliqueFinset
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, card_triangles] at hmany
  simp only [← add_assoc] at hmany
  change c * ((n : ℝ) + n + n) ^ 3 ≤ ((triangleIndices G).card : ℝ) at hmany
  rw [card_triangleIndices hG] at hmany
  have hcap : (G.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    simpa only [Nat.cast_pow] using
      (Nat.cast_le.mpr (linear_card_le_sq hG hlin) : (G.card : ℝ) ≤ (n ^ 2 : ℕ))
  have hprod := mul_lt_mul_of_pos_right hcn (sq_pos_of_pos hnpos)
  have hnonneg : 0 ≤ c * (n : ℝ) ^ 3 := mul_nonneg hc.le (pow_nonneg hnpos.le 3)
  nlinarith

/-- The classical e=3 upper bound, in the exact canonical extremal vocabulary. -/
theorem upper_three (r : ℕ) (hr : 3 ≤ r) :
    HasQuadraticVanishing r ((r - 2) * 3 + 3) 3 := by
  apply upper_of_linear_triples r 3 hr (by decide)
  intro δ hδ
  simpa using linear_six_three_bound δ hδ

end P163

namespace P163

open Finset

variable {α : Type*} [DecidableEq α]

/-- Hitting each initially present forbidden set removes at most one element per set. -/
theorem delete_bad_sets (R : Finset α) (B : Finset (Finset α))
    (hB : ∀ F ∈ B, F.Nonempty) :
    ∃ G ⊆ R, (∀ F ∈ B, ¬F ⊆ G) ∧
      R.card ≤ G.card + (B.filter (fun F => F ⊆ R)).card := by
  classical
  let C := B.filter fun F => F ⊆ R
  have hex (F : C) : ∃ a, a ∈ (F : Finset α) :=
    hB F.val (mem_filter.mp F.property).1
  let pick : C → α := fun F => Classical.choose (hex F)
  let T := C.attach.image pick
  have hTcard : T.card ≤ C.card := by
    calc
      T.card ≤ C.attach.card := card_image_le
      _ = C.card := card_attach
  refine ⟨R \ T, sdiff_subset, ?_, ?_⟩
  · intro F hF hFG
    have hFR : F ⊆ R := hFG.trans sdiff_subset
    let f : C := ⟨F, mem_filter.mpr ⟨hF, hFR⟩⟩
    have hpick : pick f ∈ F := Classical.choose_spec (hex f)
    have hmemT : pick f ∈ T := mem_image.mpr ⟨f, mem_attach C f, rfl⟩
    exact (mem_sdiff.mp (hFG hpick)).2 hmemT
  · exact card_le_card_sdiff_add_card.trans (Nat.add_le_add_left hTcard _)

section FiniteSampling

variable [Fintype α]

/-- The ordinary finite Bernoulli product weight, expressed entirely in the rationals. -/
def bernoulliWeight (p : ℚ) (ω : α → Bool) : ℚ :=
  ∏ a, if ω a = true then p else 1 - p

def bernoulliSample (E : Finset α) (ω : α → Bool) : Finset α :=
  E.filter fun a => ω a = true

theorem bernoulliWeight_nonneg (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : α → Bool) : 0 ≤ bernoulliWeight p ω := by
  apply prod_nonneg
  intro a ha
  split_ifs
  · exact hp
  · exact sub_nonneg.mpr hp1

theorem bernoulliWeight_sum (p : ℚ) :
    (∑ ω : α → Bool, bernoulliWeight p ω) = 1 := by
  classical
  simpa [bernoulliWeight, Fintype.sum_bool] using
    (Fintype.prod_sum (fun (_ : α) (b : Bool) =>
      if b = true then p else 1 - p)).symm

/-- Requiring every member of `F` to be sampled has total weight `p^|F|`. -/
theorem bernoulli_contains_sum (p : ℚ) (F : Finset α) :
    (∑ ω : α → Bool,
      if ∀ a ∈ F, ω a = true then bernoulliWeight p ω else 0) = p ^ F.card := by
  classical
  let q : α → Bool → ℚ := fun a b =>
    (if b = true then p else 1 - p) *
      (if a ∈ F → b = true then 1 else 0)
  have hprod (ω : α → Bool) :
      (∏ a, q a (ω a)) =
        if ∀ a ∈ F, ω a = true then bernoulliWeight p ω else 0 := by
    dsimp only [q]
    rw [prod_mul_distrib, Fintype.prod_boole]
    simp only [
      mul_ite, mul_one, mul_zero, bernoulliWeight]
  have hsum (a : α) : (∑ b : Bool, q a b) = if a ∈ F then p else 1 := by
    by_cases ha : a ∈ F <;> simp [q, Fintype.sum_bool, ha]
  calc
    _ = ∑ ω : α → Bool, ∏ a, q a (ω a) :=
      sum_congr rfl (fun ω _ => (hprod ω).symm)
    _ = ∏ a, ∑ b : Bool, q a b := (Fintype.prod_sum q).symm
    _ = ∏ a : α, if a ∈ F then p else 1 :=
      prod_congr rfl (fun a _ => hsum a)
    _ = p ^ F.card := by simp

theorem bernoulli_sample_contains_sum (E F : Finset α) (hFE : F ⊆ E) (p : ℚ) :
    (∑ ω : α → Bool,
      if F ⊆ bernoulliSample E ω then bernoulliWeight p ω else 0) = p ^ F.card := by
  classical
  have hevent (ω : α → Bool) :
      F ⊆ bernoulliSample E ω ↔ ∀ a ∈ F, ω a = true := by
    constructor
    · intro h a ha
      exact (mem_filter.mp (h ha)).2
    · intro h a ha
      exact mem_filter.mpr ⟨hFE ha, h a ha⟩
  calc
    _ = ∑ ω : α → Bool,
        if ∀ a ∈ F, ω a = true then bernoulliWeight p ω else 0 := by
      apply sum_congr rfl
      intro ω hω
      simp only [hevent ω]
    _ = p ^ F.card := bernoulli_contains_sum p F

theorem bernoulli_sample_card_sum (E : Finset α) (p : ℚ) :
    (∑ ω : α → Bool, bernoulliWeight p ω * ((bernoulliSample E ω).card : ℚ)) =
      (E.card : ℚ) * p := by
  classical
  calc
    _ = ∑ ω : α → Bool, ∑ a ∈ E,
        if ω a = true then bernoulliWeight p ω else 0 := by
      apply sum_congr rfl
      intro ω hω
      rw [bernoulliSample, natCast_card_filter, mul_sum]
      apply sum_congr rfl
      intro a ha
      split_ifs <;> simp
    _ = ∑ a ∈ E, ∑ ω : α → Bool,
        if ω a = true then bernoulliWeight p ω else 0 := sum_comm
    _ = ∑ a ∈ E, p := by
      apply sum_congr rfl
      intro a ha
      simpa using bernoulli_contains_sum p ({a} : Finset α)
    _ = (E.card : ℚ) * p := by simp

theorem bernoulli_bad_card_sum (E : Finset α) (B : Finset (Finset α)) (e : ℕ)
    (hsub : ∀ F ∈ B, F ⊆ E) (hcard : ∀ F ∈ B, F.card = e) (p : ℚ) :
    (∑ ω : α → Bool, bernoulliWeight p ω *
      ((B.filter (fun F => F ⊆ bernoulliSample E ω)).card : ℚ)) =
        (B.card : ℚ) * p ^ e := by
  classical
  calc
    _ = ∑ ω : α → Bool, ∑ F ∈ B,
        if F ⊆ bernoulliSample E ω then bernoulliWeight p ω else 0 := by
      apply sum_congr rfl
      intro ω hω
      rw [natCast_card_filter, mul_sum]
      apply sum_congr rfl
      intro F hF
      split_ifs <;> simp
    _ = ∑ F ∈ B, ∑ ω : α → Bool,
        if F ⊆ bernoulliSample E ω then bernoulliWeight p ω else 0 := sum_comm
    _ = ∑ F ∈ B, p ^ e := by
      apply sum_congr rfl
      intro F hF
      rw [bernoulli_sample_contains_sum E F (hsub F hF) p, hcard F hF]
    _ = (B.card : ℚ) * p ^ e := by simp

/-- One outcome attains at least the mean of the number of elements minus bad sets. -/
theorem bernoulli_sampling_bound (E : Finset α) (B : Finset (Finset α)) (e : ℕ)
    (hsub : ∀ F ∈ B, F ⊆ E) (hcard : ∀ F ∈ B, F.card = e)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ ω : α → Bool,
      (E.card : ℚ) * p - (B.card : ℚ) * p ^ e ≤
        ((bernoulliSample E ω).card : ℚ) -
          ((B.filter (fun F => F ⊆ bernoulliSample E ω)).card : ℚ) := by
  classical
  let Z : (α → Bool) → ℚ := fun ω =>
    ((bernoulliSample E ω).card : ℚ) -
      ((B.filter (fun F => F ⊆ bernoulliSample E ω)).card : ℚ)
  have hmean : (∑ ω : α → Bool, bernoulliWeight p ω * Z ω) =
      (E.card : ℚ) * p - (B.card : ℚ) * p ^ e := by
    simp_rw [Z, mul_sub]
    rw [sum_sub_distrib, bernoulli_sample_card_sum,
      bernoulli_bad_card_sum E B e hsub hcard]
  obtain ⟨ω, hω, hmax⟩ :=
    (univ : Finset (α → Bool)).exists_max_image Z univ_nonempty
  refine ⟨ω, ?_⟩
  calc
    (E.card : ℚ) * p - (B.card : ℚ) * p ^ e =
        ∑ v : α → Bool, bernoulliWeight p v * Z v := hmean.symm
    _ ≤ ∑ v : α → Bool, bernoulliWeight p v * Z ω := by
      apply sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (hmax v hv) (bernoulliWeight_nonneg p hp hp1 v)
    _ = (∑ v : α → Bool, bernoulliWeight p v) * Z ω := (sum_mul _ _ _).symm
    _ = Z ω := by rw [bernoulliWeight_sum, one_mul]

/-- Finite alteration for a family of forbidden `e`-element sets. -/
theorem finite_alteration (E : Finset α) (B : Finset (Finset α)) (e : ℕ)
    (he : 0 < e) (hB : ∀ F ∈ B, F ⊆ E ∧ F.card = e)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ G ⊆ E, (∀ F ∈ B, ¬F ⊆ G) ∧
      (E.card : ℚ) * p - (B.card : ℚ) * p ^ e ≤ (G.card : ℚ) := by
  classical
  obtain ⟨ω, hω⟩ := bernoulli_sampling_bound E B e
    (fun F hF => (hB F hF).1) (fun F hF => (hB F hF).2) p hp hp1
  have hnonempty : ∀ F ∈ B, F.Nonempty := by
    intro F hF
    apply card_pos.mp
    rw [(hB F hF).2]
    exact he
  obtain ⟨G, hGR, havoid, hdel⟩ := delete_bad_sets (bernoulliSample E ω) B hnonempty
  refine ⟨G, hGR.trans (filter_subset _ _), havoid, hω.trans ?_⟩
  apply sub_le_iff_le_add.mpr
  have hcast := (Nat.cast_le (α := ℚ)).mpr hdel
  simpa only [Nat.cast_add] using hcast

end FiniteSampling

end P163

namespace P163

open Finset

/-- Alteration for the exact canonical support condition, before choosing a sampling density. -/
theorem hypergraph_alteration (r d e n : ℕ) (he : 0 < e) (hdn : d ≤ n)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ G : Hypergraph n, AvoidsFamily r d e n G ∧
      (n.choose r : ℚ) * p -
        ((n.choose d : ℚ) * (((d.choose r).choose e : ℕ) : ℚ)) * p ^ e ≤
          (G.card : ℚ) := by
  classical
  let V : Finset (Fin n) := univ
  let E := V.powersetCard r
  let B : Finset (Hypergraph n) := (V.powersetCard d).biUnion
    (fun D => (D.powersetCard r).powersetCard e)
  have hBE : ∀ F ∈ B, F ⊆ E ∧ F.card = e := by
    intro F hF
    obtain ⟨D, hD, hFD⟩ := mem_biUnion.mp hF
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hFD
    exact ⟨hsub.trans (powersetCard_mono (mem_powersetCard.mp hD).1), hcard⟩
  have hBcard : B.card ≤ n.choose d * (d.choose r).choose e := by
    calc
      B.card ≤ ∑ D ∈ V.powersetCard d, ((D.powersetCard r).powersetCard e).card :=
        card_biUnion_le
      _ = ∑ D ∈ V.powersetCard d, (d.choose r).choose e := by
        apply sum_congr rfl
        intro D hD
        simp only [card_powersetCard, (mem_powersetCard.mp hD).2]
      _ = n.choose d * (d.choose r).choose e := by simp [V]
  have hEcard : E.card = n.choose r := by simp [E, V]
  obtain ⟨G, hGE, havoid, hsize⟩ := finite_alteration E B e he hBE p hp hp1
  have hGu : IsUniform r G := fun A hA => (mem_powersetCard.mp (hGE hA)).2
  have hGs : ∀ H : Hypergraph n, H ⊆ G → H.card = e → d < (H.biUnion id).card := by
    intro H hHG hHe
    by_contra hbad
    obtain ⟨D, hUD, hDV, hDd⟩ := exists_subsuperset_card_eq
      (subset_univ (H.biUnion id)) (Nat.le_of_not_gt hbad) (by simpa using hdn)
    have hHD : H ⊆ D.powersetCard r := by
      intro A hA
      refine mem_powersetCard.mpr ⟨?_, hGu A (hHG hA)⟩
      intro x hx
      exact hUD (mem_biUnion.mpr ⟨A, hA, hx⟩)
    have hHB : H ∈ B := mem_biUnion.mpr
      ⟨D, mem_powersetCard.mpr ⟨hDV, hDd⟩, mem_powersetCard.mpr ⟨hHD, hHe⟩⟩
    exact havoid H hHB hHG
  refine ⟨G, (avoidsFamily_iff_support hGu hdn).mpr hGs, ?_⟩
  have hBq : (B.card : ℚ) ≤
      (n.choose d : ℚ) * (((d.choose r).choose e : ℕ) : ℚ) := by
    exact_mod_cast hBcard
  have hbadq := mul_le_mul_of_nonneg_right hBq (pow_nonneg hp e)
  have hbound := (sub_le_sub_left hbadq ((E.card : ℚ) * p)).trans hsize
  simpa only [hEcard] using hbound

/-- A convenient explicit lower estimate for the number of possible edges. -/
theorem choose_lower_half (r n : ℕ) (hn : 2 * r ≤ n) :
    (n : ℚ) ^ r / (2 ^ r * (r.factorial : ℚ)) ≤ (n.choose r : ℚ) := by
  have hrn : r ≤ n + 1 := by omega
  have hhalf : (n : ℚ) / 2 ≤ ((n + 1 - r : ℕ) : ℚ) := by
    rw [Nat.cast_sub hrn, Nat.cast_add, Nat.cast_one]
    have hnq : 2 * (r : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  calc
    (n : ℚ) ^ r / (2 ^ r * (r.factorial : ℚ)) =
        ((n : ℚ) / 2) ^ r / (r.factorial : ℚ) := by rw [div_pow, div_div]
    _ ≤ (((n + 1 - r : ℕ) : ℚ) ^ r) / (r.factorial : ℚ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf r) (by positivity)
    _ ≤ (n.choose r : ℚ) := by simpa only [Nat.cast_pow] using (Nat.pow_le_choose r n :
      (((n + 1 - r : ℕ) ^ r : ℚ) / (r.factorial : ℚ)) ≤ (n.choose r : ℚ))

/-- Explicit quadratic examples at one vertex below the conjectured threshold. -/
theorem finite_sharpness (r e n : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e)
    (hn : max ((r - 2) * e + 2) (2 * r) ≤ n) :
    let d := (r - 2) * e + 2
    let A := 2 ^ r * r.factorial
    let M := (d.choose r).choose e
    ∃ G : Hypergraph n, AvoidsFamily r d e n G ∧
      n ^ 2 ≤ 4 * A ^ 2 * (M + 1) * G.card := by
  let d := (r - 2) * e + 2
  let A := 2 ^ r * r.factorial
  let M := (d.choose r).choose e
  change ∃ G : Hypergraph n, AvoidsFamily r d e n G ∧
    n ^ 2 ≤ 4 * A ^ 2 * (M + 1) * G.card
  have hdn : d ≤ n := (le_max_left _ _).trans hn
  have hnr : 2 * r ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hn1 : 1 ≤ (n : ℚ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hAnat : 0 < A := by dsimp [A]; positivity
  have hA : 0 < (A : ℚ) := by exact_mod_cast hAnat
  have hA1 : 1 ≤ (A : ℚ) := by exact_mod_cast (Nat.succ_le_iff.mpr hAnat)
  have hM0 : 0 ≤ (M : ℚ) := by positivity
  have hM1 : 0 < (M : ℚ) + 1 := by positivity
  let a : ℚ := 1 / (2 * (A : ℚ) * ((M : ℚ) + 1))
  let q : ℚ := (n : ℚ) ^ (r - 2)
  let p : ℚ := a / q
  have hden : 0 < 2 * (A : ℚ) * ((M : ℚ) + 1) := by positivity
  have ha : 0 < a := div_pos (by norm_num) hden
  have hden1 : (1 : ℚ) ≤ 2 * (A : ℚ) * ((M : ℚ) + 1) := by
    calc
      (1 : ℚ) ≤ (A : ℚ) := hA1
      _ ≤ 2 * (A : ℚ) := by linarith
      _ ≤ 2 * (A : ℚ) * ((M : ℚ) + 1) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
  have ha1 : a ≤ 1 := (div_le_one₀ hden).mpr hden1
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := one_le_pow₀ hn1
  have hp : 0 ≤ p := (div_pos ha hq).le
  have hp1 : p ≤ 1 := (div_le_one₀ hq).mpr (ha1.trans hq1)
  have hMa : (M : ℚ) * a ≤ 1 / (2 * (A : ℚ)) := by
    calc
      (M : ℚ) * a = ((M : ℚ) / ((M : ℚ) + 1)) / (2 * (A : ℚ)) := by
        dsimp [a]
        field_simp [hA.ne', hM1.ne'] <;> ring
      _ ≤ 1 / (2 * (A : ℚ)) := div_le_div_of_nonneg_right
        ((div_le_one₀ hM1).mpr (by linarith)) (by positivity)
  have hbadcoef : (M : ℚ) * a ^ e ≤ a / (2 * (A : ℚ)) := by
    calc
      (M : ℚ) * a ^ e ≤ (M : ℚ) * a ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ha.le ha1 (by omega)) hM0
      _ = a * ((M : ℚ) * a) := by ring
      _ ≤ a * (1 / (2 * (A : ℚ))) := mul_le_mul_of_nonneg_left hMa ha.le
      _ = a / (2 * (A : ℚ)) := by ring
  have hpowr : (n : ℚ) ^ r = q * (n : ℚ) ^ 2 := by
    dsimp [q]
    rw [← pow_add]
    congr 1
    omega
  have hpowd : (n : ℚ) ^ d = q ^ e * (n : ℚ) ^ 2 := by
    simp only [d, q, pow_add, pow_mul]
  have hchoose : (n : ℚ) ^ r / (A : ℚ) ≤ (n.choose r : ℚ) := by
    simpa [A] using choose_lower_half r n hnr
  have hedge : a / (A : ℚ) * (n : ℚ) ^ 2 ≤ (n.choose r : ℚ) * p := by
    calc
      a / (A : ℚ) * (n : ℚ) ^ 2 = ((n : ℚ) ^ r / (A : ℚ)) * p := by
        rw [hpowr]
        dsimp [p]
        field_simp [hA.ne', hq.ne'] <;> ring
      _ ≤ (n.choose r : ℚ) * p := mul_le_mul_of_nonneg_right hchoose hp
  have hchooseD : (n.choose d : ℚ) ≤ (n : ℚ) ^ d := by
    exact_mod_cast Nat.choose_le_pow n d
  have hbad : ((n.choose d : ℚ) * (M : ℚ)) * p ^ e ≤
      (a / (2 * (A : ℚ))) * (n : ℚ) ^ 2 := by
    calc
      ((n.choose d : ℚ) * (M : ℚ)) * p ^ e ≤
          ((n : ℚ) ^ d * (M : ℚ)) * p ^ e :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchooseD hM0)
          (pow_nonneg hp e)
      _ = ((M : ℚ) * a ^ e) * (n : ℚ) ^ 2 := by
        rw [hpowd]
        dsimp [p]
        rw [div_pow]
        field_simp [hq.ne'] <;> ring
      _ ≤ (a / (2 * (A : ℚ))) * (n : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_right hbadcoef (sq_nonneg _)
  obtain ⟨G, hG, hcard⟩ := hypergraph_alteration r d e n (by omega) hdn p hp hp1
  have hhalf : a / (A : ℚ) * (n : ℚ) ^ 2 -
      (a / (2 * (A : ℚ))) * (n : ℚ) ^ 2 =
        (a / (2 * (A : ℚ))) * (n : ℚ) ^ 2 := by
    field_simp [hA.ne'] <;> ring
  have hdensity : (a / (2 * (A : ℚ))) * (n : ℚ) ^ 2 ≤ (G.card : ℚ) := by
    calc
      _ = a / (A : ℚ) * (n : ℚ) ^ 2 -
          (a / (2 * (A : ℚ))) * (n : ℚ) ^ 2 := hhalf.symm
      _ ≤ (n.choose r : ℚ) * p - ((n.choose d : ℚ) * (M : ℚ)) * p ^ e :=
        sub_le_sub hedge hbad
      _ ≤ (G.card : ℚ) := hcard
  have hcoef : a / (2 * (A : ℚ)) = 1 / (4 * (A : ℚ) ^ 2 * ((M : ℚ) + 1)) := by
    dsimp [a]
    field_simp [hA.ne', hM1.ne'] <;> ring
  rw [hcoef] at hdensity
  have hC : 0 < (4 : ℚ) * (A : ℚ) ^ 2 * ((M : ℚ) + 1) := by positivity
  have hdiv : (n : ℚ) ^ 2 / (4 * (A : ℚ) ^ 2 * ((M : ℚ) + 1)) ≤ (G.card : ℚ) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hdensity
  have hcross : (n : ℚ) ^ 2 ≤
      (4 * (A : ℚ) ^ 2 * ((M : ℚ) + 1)) * (G.card : ℚ) := by
    simpa only [mul_comm] using (div_le_iff₀ hC).mp hdiv
  refine ⟨G, hG, ?_⟩
  exact_mod_cast hcross

/-- The entire strict-lower-threshold half of the Brown–Erdős–Sós statement. -/
theorem lower_sharpness (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    ∀ d < (r - 2) * e + 3, ¬HasQuadraticVanishing r d e := by
  intro d hd hvan
  let d0 := (r - 2) * e + 2
  let A := 2 ^ r * r.factorial
  let M := (d0.choose r).choose e
  let C := 4 * A ^ 2 * (M + 1)
  have hCnat : 0 < C := by dsimp [C, A]; positivity
  have hC : 0 < (C : ℝ) := by exact_mod_cast hCnat
  let δ : ℝ := 1 / (2 * (C : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := (vanishing_iff_support_bound r d e).mp hvan δ hδ
  let n := max N (max d0 (2 * r))
  have hnN : N ≤ n := le_max_left _ _
  have hnbound : max d0 (2 * r) ≤ n := le_max_right _ _
  have hnd : d0 ≤ n := (le_max_left _ _).trans hnbound
  have hnr : 2 * r ≤ n := (le_max_right _ _).trans hnbound
  have hdsmall : d ≤ d0 := by dsimp [d0]; omega
  obtain ⟨G, hG, hcard⟩ := finite_sharpness r e n hr he hnbound
  have hsupport := (avoidsFamily_iff_support hG.1 hnd).mp hG
  have hsmall : ∀ H : Hypergraph n, H ⊆ G → H.card = e → d < (H.biUnion id).card :=
    fun H hHG hHe => hdsmall.trans_lt (hsupport H hHG hHe)
  have hupper := hN n hnN G hG.1 hsmall
  have hcardR : (n : ℝ) ^ 2 ≤ (C : ℝ) * (G.card : ℝ) := by
    change n ^ 2 ≤ C * G.card at hcard
    exact_mod_cast hcard
  have hupperC := mul_le_mul_of_nonneg_left hupper hC.le
  have hhalf : (C : ℝ) * (δ * (n : ℝ) ^ 2) = (n : ℝ) ^ 2 / 2 := by
    dsimp [δ]
    field_simp [hC.ne'] <;> ring
  rw [hhalf] at hupperC
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn2pos : 0 < (n : ℝ) ^ 2 := pow_pos hnpos 2
  linarith

end P163

namespace P163

/-- The complete original question, including sharpness at every smaller vertex count. -/
def FullThreshold : Prop :=
  ∀ r e : ℕ, 3 ≤ r → 3 ≤ e →
    let threshold := (r - 2) * e + 3
    HasQuadraticVanishing r threshold e ∧
      ∀ d < threshold, ¬HasQuadraticVanishing r d e

/-- Exactly the upper question for triple systems with at least four edges remains. -/
theorem full_threshold_iff_triples :
    FullThreshold ↔ ∀ e : ℕ, 4 ≤ e → HasQuadraticVanishing 3 (e + 3) e := by
  constructor
  · intro h e he
    simpa using (h 3 e (by decide) (by omega)).1
  · intro h r e hr he
    refine ⟨?_, lower_sharpness r e hr he⟩
    by_cases he3 : e = 3
    · subst e
      exact upper_three r hr
    · exact upper_of_triples r e hr he (h e (by omega))

end P163
theorem proof :
    (∀ r e : ℕ, 3 ≤ r → 3 ≤ e →
      ∀ d < (r - 2) * e + 3, ¬P163.HasQuadraticVanishing r d e) ∧
    (∀ r : ℕ, 3 ≤ r → P163.HasQuadraticVanishing r ((r - 2) * 3 + 3) 3) ∧
    (P163.FullThreshold ↔ ∀ e : ℕ, 4 ≤ e → P163.HasQuadraticVanishing 3 (e + 3) e) :=
  ⟨P163.lower_sharpness, P163.upper_three, P163.full_threshold_iff_triples⟩

end Submissions.BrownErdosSosThresholdReduction.Main
