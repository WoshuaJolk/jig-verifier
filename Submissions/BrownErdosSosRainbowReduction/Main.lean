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
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod

/-! Known tripartite/rainbow reformulations of Brown–Erdős–Sós.
Credit: Gyárfás–Sárközy (2023), Proposition 1.6; Mathlib authors and prior
Ruzsa–Szemerédi formalization as documented below. No density theorem is claimed. -/

namespace Submissions.BrownErdosSosRainbowReduction.Main

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

/-!
Finite tripartite reformulation of the upper question. Sorting a triple and
then putting its three coordinates in separate tagged copies preserves every
edge. Forgetting the tags can only decrease support. In the other direction,
three tagged copies have exactly three times the original ambient size.

This uses the sorted-triple construction and its provenance documented in
RuzsaSzemeredi.lean, and Mathlib's existing `toTriangle` embedding.
-/

namespace P163

open Finset SimpleGraph.TripartiteFromTriangles

variable {n : ℕ}

/-- The number of vertices used in the three separate coordinate parts. -/
def coordinateSupport {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (T : Finset (α × β × γ)) : ℕ :=
  (T.image Prod.fst).card + (T.image fun p => p.2.1).card +
    (T.image fun p => p.2.2).card

/-- Forget the three coordinate tags of a triple. -/
def untaggedEdge (p : Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {p.1, p.2.1, p.2.2}

private theorem sorted_untagged_injective {G : Hypergraph n} :
    Set.InjOn untaggedEdge (↑(triangleIndices G) : Set (Fin n × Fin n × Fin n)) := by
  intro p hp q hq heq
  rcases p with ⟨a, b, c⟩
  rcases q with ⟨x, y, z⟩
  obtain ⟨hab, hbc, _⟩ := mem_triangleIndices.mp hp
  obtain ⟨hxy, hyz, _⟩ := mem_triangleIndices.mp hq
  dsimp only at hab hbc hxy hyz
  change ({a, b, c} : Finset (Fin n)) = {x, y, z} at heq
  simp only [Finset.ext_iff, mem_insert, mem_singleton] at heq
  have ha := (heq a).mp (Or.inl rfl)
  have hb := (heq b).mp (Or.inr (Or.inl rfl))
  have hc := (heq c).mp (Or.inr (Or.inr rfl))
  have hx := (heq x).mpr (Or.inl rfl)
  have hy := (heq y).mpr (Or.inr (Or.inl rfl))
  have hz := (heq z).mpr (Or.inr (Or.inr rfl))
  have hxyz : a = x ∧ b = y ∧ c = z := by omega
  rcases hxyz with ⟨rfl, rfl, rfl⟩
  rfl

theorem untagged_subfamily {G : Hypergraph n} {S : Finset (Fin n × Fin n × Fin n)}
    (hS : S ⊆ triangleIndices G) : S.image untaggedEdge ⊆ G := by
  intro A hA
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hA
  exact (mem_triangleIndices.mp (hS hp)).2.2

theorem card_untagged_subfamily {G : Hypergraph n}
    {S : Finset (Fin n × Fin n × Fin n)} (hS : S ⊆ triangleIndices G) :
    (S.image untaggedEdge).card = S.card := by
  apply card_image_of_injOn
  intro p hp q hq heq
  exact sorted_untagged_injective (hS hp) (hS hq) heq

theorem untagged_support_le (S : Finset (Fin n × Fin n × Fin n)) :
    ((S.image untaggedEdge).biUnion id).card ≤ coordinateSupport S := by
  have hsub : (S.image untaggedEdge).biUnion id ⊆
      (S.image Prod.fst ∪ S.image (fun p => p.2.1)) ∪ S.image (fun p => p.2.2) := by
    intro x hx
    obtain ⟨A, hA, hx⟩ := mem_biUnion.mp hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hA
    have hx' : x = p.1 ∨ x = p.2.1 ∨ x = p.2.2 := by
      simpa only [id_eq, untaggedEdge, mem_insert, mem_singleton] using hx
    simp only [mem_union, mem_image]
    rcases hx' with rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
    · exact Or.inr ⟨p, hp, rfl⟩
  have h₁ := card_le_card hsub
  have h₂ := card_union_le (S.image Prod.fst ∪ S.image (fun p => p.2.1))
    (S.image (fun p => p.2.2))
  have h₃ := card_union_le (S.image Prod.fst) (S.image (fun p => p.2.1))
  unfold coordinateSupport
  omega

/-- A support-avoiding triple system gives an equally large relation with the
same support-avoidance threshold, without discarding any edges. -/
theorem triangleIndices_support {G : Hypergraph n} {d e : ℕ}
    (hG : ∀ H ⊆ G, H.card = e → d < (H.biUnion id).card) :
    ∀ S ⊆ triangleIndices G, S.card = e → d < coordinateSupport S := by
  intro S hS he
  exact (hG (S.image untaggedEdge) (untagged_subfamily hS)
    ((card_untagged_subfamily hS).trans he)).trans_le (untagged_support_le S)

theorem tagged_support_eq {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (T : Finset (α × β × γ)) :
    (T.map toTriangle).biUnion id =
      (T.image Prod.fst).disjSum
        ((T.image fun p => p.2.1).disjSum (T.image fun p => p.2.2)) := by
  rw [map_eq_image, image_biUnion]
  ext x
  rcases x with a | (b | c) <;>
    simp [toTriangle_apply, Sum3.in₀, Sum3.in₁, Sum3.in₂, eq_comm]

theorem card_tagged_support {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (T : Finset (α × β × γ)) :
    ((T.map toTriangle).biUnion id).card = coordinateSupport T := by
  rw [tagged_support_eq]
  simp only [card_disjSum, coordinateSupport, Nat.add_assoc]

/-- Relabel the three disjoint copies by exactly `3 * n` vertex labels. -/
noncomputable def tripleTagEquiv (n : ℕ) :
    (Fin n ⊕ Fin n ⊕ Fin n) ≃ Fin (3 * n) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

noncomputable def taggedEdge (n : ℕ) (p : Fin n × Fin n × Fin n) :
    Finset (Fin (3 * n)) :=
  (toTriangle p).image (tripleTagEquiv n)

theorem taggedEdge_injective (n : ℕ) : Function.Injective (taggedEdge n) := by
  intro p q heq
  exact toTriangle.injective ((image_injective (tripleTagEquiv n).injective) heq)

noncomputable def taggedRelation (T : Finset (Fin n × Fin n × Fin n)) :
    Hypergraph (3 * n) := T.image (taggedEdge n)

@[simp] theorem card_taggedRelation (T : Finset (Fin n × Fin n × Fin n)) :
    (taggedRelation T).card = T.card :=
  card_image_of_injective T (taggedEdge_injective n)

theorem taggedRelation_uniform (T : Finset (Fin n × Fin n × Fin n)) :
    IsUniform 3 (taggedRelation T) := by
  intro A hA
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hA
  unfold taggedEdge
  rw [card_image_of_injective _ (tripleTagEquiv n).injective]
  simp [toTriangle_apply, Sum3.in₀, Sum3.in₁, Sum3.in₂]

theorem taggedRelation_support (T : Finset (Fin n × Fin n × Fin n)) :
    ((taggedRelation T).biUnion id).card = coordinateSupport T := by
  have heq : (taggedRelation T).biUnion id =
      ((T.map toTriangle).biUnion id).image (tripleTagEquiv n) := by
    simp only [taggedRelation, taggedEdge, map_eq_image, image_biUnion,
      biUnion_image, id_eq]
  rw [heq, card_image_of_injective _ (tripleTagEquiv n).injective,
    card_tagged_support]

theorem taggedRelation_avoids {T : Finset (Fin n × Fin n × Fin n)} {d e : ℕ}
    (hT : ∀ S ⊆ T, S.card = e → d < coordinateSupport S) :
    ∀ H ⊆ taggedRelation T, H.card = e → d < (H.biUnion id).card := by
  intro H hH he
  let S := T.filter fun p => taggedEdge n p ∈ H
  have hST : S ⊆ T := filter_subset _ _
  have hSH : taggedRelation S = H := by
    ext A
    constructor
    · intro hA
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hA
      exact (mem_filter.mp hp).2
    · intro hA
      obtain ⟨p, hp, rfl⟩ := mem_image.mp (hH hA)
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hA⟩, rfl⟩
  have hSe : S.card = e := by
    rw [← card_taggedRelation S, hSH]
    exact he
  rw [← hSH, taggedRelation_support]
  exact hT S hST hSe

/-- The upper question for linear relations on three separate `n`-element parts. -/
def TripartiteRelationBound (e : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
    ∀ T : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint T →
      (∀ S ⊆ T, S.card = e → e + 3 < coordinateSupport S) →
      (T.card : ℝ) ≤ δ * (n : ℝ) ^ 2

theorem relation_bound_of_vanishing {e : ℕ}
    (h : HasQuadraticVanishing 3 (e + 3) e) : TripartiteRelationBound e := by
  intro δ hδ
  obtain ⟨N, hN⟩ := (vanishing_iff_support_bound _ _ _).mp h (δ / 9) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn T _ hT
  have hbound := hN (3 * n) (by omega) (taggedRelation T)
    (taggedRelation_uniform T) (taggedRelation_avoids hT)
  rw [card_taggedRelation] at hbound
  calc
    (T.card : ℝ) ≤ δ / 9 * (↑(3 * n) : ℝ) ^ 2 := hbound
    _ = δ * (n : ℝ) ^ 2 := by push_cast; ring

/-- The relation formulation implies the upper bound at every uniformity. -/
theorem upper_of_relation_bound (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e)
    (h : TripartiteRelationBound e) :
    HasQuadraticVanishing r ((r - 2) * e + 3) e := by
  apply upper_of_linear_triples r e hr he
  intro δ hδ
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, ?_⟩
  intro n hn G hG hlin havoid
  have hbound := hN n hn (triangleIndices G) (triangleIndices_explicit hlin)
    (triangleIndices_support havoid)
  simpa only [card_triangleIndices hG] using hbound

/-- No density is lost in passing to sorted relations; the converse uses only
the fixed ambient-size change from `n` to `3 * n`. -/
theorem vanishing_iff_relation_bound (e : ℕ) (he : 3 ≤ e) :
    HasQuadraticVanishing 3 (e + 3) e ↔ TripartiteRelationBound e := by
  constructor
  · exact relation_bound_of_vanishing
  · intro h
    simpa using upper_of_relation_bound 3 e (by decide) he h

end P163

namespace P163

open Finset SimpleGraph.TripartiteFromTriangles

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

private theorem card_le_coordinate_product (s : Finset δ) (f : δ → α) (g : δ → β)
    (h : Set.InjOn (fun x => (f x, g x)) (↑s : Set δ)) :
    s.card ≤ (s.image f).card * (s.image g).card := by
  classical
  calc
    s.card = (s.image (fun x => (f x, g x))).card := (card_image_of_injOn h).symm
    _ ≤ ((s.image f) ×ˢ (s.image g)).card := by
      apply card_le_card
      intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
      exact mem_product.mpr ⟨mem_image_of_mem f hx, mem_image_of_mem g hx⟩
    _ = (s.image f).card * (s.image g).card := card_product _ _

theorem pair_projection_bounds (T : Finset (α × β × γ)) [ExplicitDisjoint T] :
    T.card ≤ (T.image Prod.fst).card * (T.image (fun p => p.2.1)).card ∧
    T.card ≤ (T.image Prod.fst).card * (T.image (fun p => p.2.2)).card ∧
    T.card ≤ (T.image (fun p => p.2.1)).card * (T.image (fun p => p.2.2)).card := by
  refine ⟨card_le_coordinate_product T _ _ ?_,
    card_le_coordinate_product T _ _ ?_, card_le_coordinate_product T _ _ ?_⟩
  · intro p hp q hq heq
    rcases p with ⟨a, b, c⟩
    rcases q with ⟨a', b', c'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hc : c = c' := ExplicitDisjoint.inj₂ hp hq
    simp [hc]
  · intro p hp q hq heq
    rcases p with ⟨a, b, c⟩
    rcases q with ⟨a', b', c'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hb : b = b' := ExplicitDisjoint.inj₁ hp hq
    simp [hb]
  · intro p hp q hq heq
    rcases p with ⟨a, b, c⟩
    rcases q with ⟨a', b', c'⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have ha : a = a' := ExplicitDisjoint.inj₀ hp hq
    simp [ha]

/-- Four linear tripartite edges on at most seven vertices have two parts of size two. -/
theorem two_parts_of_four_on_seven (T : Finset (α × β × γ)) [ExplicitDisjoint T]
    (hfour : T.card = 4)
    (hseven : (T.image Prod.fst).card + (T.image (fun p => p.2.1)).card +
      (T.image (fun p => p.2.2)).card ≤ 7) :
    ((T.image Prod.fst).card = 2 ∧ (T.image (fun p => p.2.1)).card = 2) ∨
    ((T.image Prod.fst).card = 2 ∧ (T.image (fun p => p.2.2)).card = 2) ∨
    ((T.image (fun p => p.2.1)).card = 2 ∧ (T.image (fun p => p.2.2)).card = 2) := by
  obtain ⟨hxy, hxz, hyz⟩ := pair_projection_bounds T
  rw [hfour] at hxy hxz hyz
  have hx : 2 ≤ (T.image Prod.fst).card := by
    by_contra h
    have hle : (T.image Prod.fst).card ≤ 1 := by omega
    have hy := hxy.trans (Nat.mul_le_mul_right _ hle)
    have hz := hxz.trans (Nat.mul_le_mul_right _ hle)
    simp only [one_mul] at hy hz
    omega
  have hy : 2 ≤ (T.image (fun p => p.2.1)).card := by
    by_contra h
    have hle : (T.image (fun p => p.2.1)).card ≤ 1 := by omega
    have hx' := hxy.trans (Nat.mul_le_mul_left _ hle)
    have hz := hyz.trans (Nat.mul_le_mul_right _ hle)
    simp only [one_mul, mul_one] at hx' hz
    omega
  have hz : 2 ≤ (T.image (fun p => p.2.2)).card := by
    by_contra h
    have hle : (T.image (fun p => p.2.2)).card ≤ 1 := by omega
    have hx' := hxz.trans (Nat.mul_le_mul_left _ hle)
    have hy' := hyz.trans (Nat.mul_le_mul_left _ hle)
    simp only [mul_one] at hx' hy'
    omega
  omega

private theorem pair_image_injective (T : Finset (α × β × γ)) [ExplicitDisjoint T] :
    Set.InjOn (fun p => (p.1, p.2.1)) (↑T : Set (α × β × γ)) := by
  rintro ⟨a, b, c⟩ hp ⟨a', b', c'⟩ hq heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hc : c = c' := ExplicitDisjoint.inj₂ hp hq
  simp [hc]

/-- A full two-by-two projection, with at most three colors, has a repeated diagonal color. -/
theorem rectangle_of_two_by_two (T : Finset (α × β × γ)) [ExplicitDisjoint T]
    (hfour : T.card = 4) (hx : (T.image Prod.fst).card = 2)
    (hy : (T.image (fun p => p.2.1)).card = 2)
    (hz : (T.image (fun p => p.2.2)).card ≤ 3) :
    ∃ a a' b b' c₀₀ c₀₁ c₁₀ c₁₁,
      a ≠ a' ∧ b ≠ b' ∧
      (a, b, c₀₀) ∈ T ∧ (a, b', c₀₁) ∈ T ∧
      (a', b, c₁₀) ∈ T ∧ (a', b', c₁₁) ∈ T ∧
      (c₀₀ = c₁₁ ∨ c₀₁ = c₁₀) := by
  obtain ⟨a, a', haa, hA⟩ := card_eq_two.mp hx
  obtain ⟨b, b', hbb, hB⟩ := card_eq_two.mp hy
  have hsub : T.image (fun p => (p.1, p.2.1)) ⊆
      (T.image Prod.fst) ×ˢ (T.image (fun p => p.2.1)) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact mem_product.mpr ⟨mem_image_of_mem _ hq, mem_image_of_mem _ hq⟩
  have hprod : T.image (fun p => (p.1, p.2.1)) =
      (T.image Prod.fst) ×ˢ (T.image (fun p => p.2.1)) := by
    apply eq_of_subset_of_card_le hsub
    rw [card_product, hx, hy, card_image_of_injOn (pair_image_injective T), hfour]
  have hget : ∀ x ∈ ({a, a'} : Finset α), ∀ y ∈ ({b, b'} : Finset β),
      ∃ c, (x, y, c) ∈ T := by
    intro x hxx y hyy
    have hmem : (x, y) ∈ T.image (fun p => (p.1, p.2.1)) := by
      rw [hprod, hA, hB]
      exact mem_product.mpr ⟨hxx, hyy⟩
    obtain ⟨⟨u, v, c⟩, hc, heq⟩ := mem_image.mp hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨c, hc⟩
  obtain ⟨c₀₀, h₀₀⟩ := hget a (by simp) b (by simp)
  obtain ⟨c₀₁, h₀₁⟩ := hget a (by simp) b' (by simp)
  obtain ⟨c₁₀, h₁₀⟩ := hget a' (by simp) b (by simp)
  obtain ⟨c₁₁, h₁₁⟩ := hget a' (by simp) b' (by simp)
  refine ⟨a, a', b, b', c₀₀, c₀₁, c₁₀, c₁₁, haa, hbb,
    h₀₀, h₀₁, h₁₀, h₁₁, ?_⟩
  have h₀₀₀₁ : c₀₀ ≠ c₀₁ := by
    intro h; subst c₀₁
    exact hbb (ExplicitDisjoint.inj₁ h₀₀ h₀₁)
  have h₀₀₁₀ : c₀₀ ≠ c₁₀ := by
    intro h; subst c₁₀
    exact haa (ExplicitDisjoint.inj₀ h₀₀ h₁₀)
  have h₀₁₁₁ : c₀₁ ≠ c₁₁ := by
    intro h; subst c₁₁
    exact haa (ExplicitDisjoint.inj₀ h₀₁ h₁₁)
  have h₁₀₁₁ : c₁₀ ≠ c₁₁ := by
    intro h; subst c₁₁
    exact hbb (ExplicitDisjoint.inj₁ h₁₀ h₁₁)
  by_contra h
  push Not at h
  have hcsub : ({c₀₀, c₀₁, c₁₀, c₁₁} : Finset γ) ⊆ T.image (fun p => p.2.2) := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_image_of_mem _ h₀₀, mem_image_of_mem _ h₀₁,
      mem_image_of_mem _ h₁₀, mem_image_of_mem _ h₁₁⟩
  have hcard := card_le_card hcsub
  simp [h₀₀₀₁, h₀₀₁₀, h₀₁₁₁, h₁₀₁₁, h.1, h.2] at hcard
  omega

/-- A projected four-cycle with a repeated diagonal color. Properness follows from linearity. -/
def RepeatedRectangle (T : Finset (α × β × γ)) : Prop :=
  ∃ a a' b b' c₀₀ c₀₁ c₁₀ c₁₁,
    a ≠ a' ∧ b ≠ b' ∧
    (a, b, c₀₀) ∈ T ∧ (a, b', c₀₁) ∈ T ∧
    (a', b, c₁₀) ∈ T ∧ (a', b', c₁₁) ∈ T ∧
    (c₀₀ = c₁₁ ∨ c₀₁ = c₁₀)

def rotateTriples (T : Finset (α × β × γ)) : Finset (β × γ × α) :=
  T.image fun p => (p.2.1, p.2.2, p.1)

@[simp] theorem mem_rotateTriples {T : Finset (α × β × γ)} {a : α} {b : β} {c : γ} :
    (b, c, a) ∈ rotateTriples T ↔ (a, b, c) ∈ T := by
  simp [rotateTriples, Prod.ext_iff, and_comm, and_left_comm]

theorem rotateTriples_explicit (T : Finset (α × β × γ)) [ExplicitDisjoint T] :
    ExplicitDisjoint (rotateTriples T) := by
  constructor
  · intro b c a b' hp hq
    exact ExplicitDisjoint.inj₁ (mem_rotateTriples.mp hp) (mem_rotateTriples.mp hq)
  · intro b c a c' hp hq
    exact ExplicitDisjoint.inj₂ (mem_rotateTriples.mp hp) (mem_rotateTriples.mp hq)
  · intro b c a a' hp hq
    exact ExplicitDisjoint.inj₀ (mem_rotateTriples.mp hp) (mem_rotateTriples.mp hq)

@[simp] theorem card_rotateTriples (T : Finset (α × β × γ)) :
    (rotateTriples T).card = T.card := by
  apply card_image_of_injective
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  tauto

@[simp] theorem rotateTriples_first (T : Finset (α × β × γ)) :
    (rotateTriples T).image Prod.fst = T.image (fun p => p.2.1) := by
  simp [rotateTriples, image_image, Function.comp_def]

@[simp] theorem rotateTriples_second (T : Finset (α × β × γ)) :
    (rotateTriples T).image (fun p => p.2.1) = T.image (fun p => p.2.2) := by
  simp [rotateTriples, image_image, Function.comp_def]

@[simp] theorem rotateTriples_third (T : Finset (α × β × γ)) :
    (rotateTriples T).image (fun p => p.2.2) = T.image Prod.fst := by
  simp [rotateTriples, image_image, Function.comp_def]

/-- Every forbidden four-edge configuration is detected in at least one of the three projections. -/
theorem four_on_seven_has_rectangle (T : Finset (α × β × γ)) [ExplicitDisjoint T]
    (hfour : T.card = 4)
    (hseven : (T.image Prod.fst).card + (T.image (fun p => p.2.1)).card +
      (T.image (fun p => p.2.2)).card ≤ 7) :
    RepeatedRectangle T ∨ RepeatedRectangle (rotateTriples T) ∨
      RepeatedRectangle (rotateTriples (rotateTriples T)) := by
  haveI := rotateTriples_explicit T
  haveI := rotateTriples_explicit (rotateTriples T)
  rcases two_parts_of_four_on_seven T hfour hseven with hxy | hxz | hyz
  · exact Or.inl (rectangle_of_two_by_two T hfour hxy.1 hxy.2 (by omega))
  · apply Or.inr ∘ Or.inr
    apply rectangle_of_two_by_two (rotateTriples (rotateTriples T))
    · simpa using hfour
    · simpa using hxz.2
    · simpa using hxz.1
    · simp only [rotateTriples_third, rotateTriples_first]
      omega
  · apply Or.inr ∘ Or.inl
    apply rectangle_of_two_by_two (rotateTriples T)
    · simpa using hfour
    · simpa using hyz.1
    · simpa using hyz.2
    · simp only [rotateTriples_third]
      omega

theorem repeatedRectangle_has_small_subfamily {T : Finset (α × β × γ)}
    (h : RepeatedRectangle T) :
    ∃ S ⊆ T, S.card = 4 ∧
      (S.image Prod.fst).card + (S.image (fun p => p.2.1)).card +
      (S.image (fun p => p.2.2)).card ≤ 7 := by
  obtain ⟨a, a', b, b', c₀₀, c₀₁, c₁₀, c₁₁, haa, hbb, h₀₀, h₀₁, h₁₀, h₁₁, hdiag⟩ := h
  let S : Finset (α × β × γ) :=
    {(a, b, c₀₀), (a, b', c₀₁), (a', b, c₁₀), (a', b', c₁₁)}
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa only [S, insert_subset_iff, singleton_subset_iff] using ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩
  · simp [S, haa, hbb]
  · have hx : (S.image Prod.fst).card = 2 := by simp [S, haa]
    have hy : (S.image (fun p => p.2.1)).card = 2 := by simp [S, hbb]
    have hz : (S.image (fun p => p.2.2)).card ≤ 3 := by
      rcases hdiag with h | h
      · simpa [S, ← h, insert_comm] using
          (card_le_three : ({c₀₁, c₁₀, c₀₀} : Finset γ).card ≤ 3)
      · simpa [S, ← h, insert_comm] using
          (card_le_three : ({c₀₀, c₀₁, c₁₁} : Finset γ).card ≤ 3)
    omega

theorem RepeatedRectangle.mono {S T : Finset (α × β × γ)} (hST : S ⊆ T)
    (h : RepeatedRectangle S) : RepeatedRectangle T := by
  obtain ⟨a, a', b, b', c₀₀, c₀₁, c₁₀, c₁₁, haa, hbb, h₀₀, h₀₁, h₁₀, h₁₁, hd⟩ := h
  exact ⟨a, a', b, b', c₀₀, c₀₁, c₁₀, c₁₁, haa, hbb,
    hST h₀₀, hST h₀₁, hST h₁₀, hST h₁₁, hd⟩

theorem rotateTriples_mono {S T : Finset (α × β × γ)} (hST : S ⊆ T) :
    rotateTriples S ⊆ rotateTriples T := image_mono _ hST

@[simp] theorem rotateTriples_three (T : Finset (α × β × γ)) :
    rotateTriples (rotateTriples (rotateTriples T)) = T := by
  ext ⟨a, b, c⟩
  simp

def FourOnSeven (T : Finset (α × β × γ)) : Prop :=
  ∃ S ⊆ T, S.card = 4 ∧
    (S.image Prod.fst).card + (S.image (fun p => p.2.1)).card +
      (S.image (fun p => p.2.2)).card ≤ 7

theorem FourOnSeven.rotate {T : Finset (α × β × γ)} (h : FourOnSeven T) :
    FourOnSeven (rotateTriples T) := by
  obtain ⟨S, hST, hfour, hseven⟩ := h
  refine ⟨rotateTriples S, rotateTriples_mono hST, by simpa using hfour, ?_⟩
  simp only [rotateTriples_first, rotateTriples_second, rotateTriples_third]
  omega

/-- The finite exact equivalence requires all three projected graphs. -/
theorem fourOnSeven_iff_rectangles (T : Finset (α × β × γ)) [ExplicitDisjoint T] :
    FourOnSeven T ↔ RepeatedRectangle T ∨ RepeatedRectangle (rotateTriples T) ∨
      RepeatedRectangle (rotateTriples (rotateTriples T)) := by
  constructor
  · rintro ⟨S, hST, hfour, hseven⟩
    have : ExplicitDisjoint S := {
      inj₀ := fun {_ _ _ _} hp hq => ExplicitDisjoint.inj₀ (hST hp) (hST hq)
      inj₁ := fun {_ _ _ _} hp hq => ExplicitDisjoint.inj₁ (hST hp) (hST hq)
      inj₂ := fun {_ _ _ _} hp hq => ExplicitDisjoint.inj₂ (hST hp) (hST hq) }
    rcases four_on_seven_has_rectangle S hfour hseven with h | h | h
    · exact Or.inl (h.mono hST)
    · exact Or.inr (Or.inl (h.mono (rotateTriples_mono hST)))
    · exact Or.inr (Or.inr (h.mono (rotateTriples_mono (rotateTriples_mono hST))))
  · rintro (h | h | h)
    · exact repeatedRectangle_has_small_subfamily h
    · have hs : FourOnSeven (rotateTriples T) := repeatedRectangle_has_small_subfamily h
      simpa using hs.rotate.rotate
    · have hs : FourOnSeven (rotateTriples (rotateTriples T)) :=
        repeatedRectangle_has_small_subfamily h
      simpa using hs.rotate

end P163

namespace P163

open Finset SimpleGraph.TripartiteFromTriangles

/-- Under `ExplicitDisjoint`, every four-cycle in each projection has four different colors. -/
def AllRectanglesRainbow {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (T : Finset (α × β × γ)) : Prop :=
  ¬ RepeatedRectangle T ∧ ¬ RepeatedRectangle (rotateTriples T) ∧
    ¬ RepeatedRectangle (rotateTriples (rotateTriples T))

theorem support_avoids_iff_rainbow {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (T : Finset (α × β × γ)) [ExplicitDisjoint T] :
    (∀ S ⊆ T, S.card = 4 → 7 < coordinateSupport S) ↔ AllRectanglesRainbow T := by
  have hs : (∀ S ⊆ T, S.card = 4 → 7 < coordinateSupport S) ↔ ¬ FourOnSeven T := by
    constructor
    · intro h ⟨S, hST, hfour, hseven⟩
      exact (Nat.not_lt_of_ge hseven) (h S hST hfour)
    · intro h S hST hfour
      by_contra hle
      exact h ⟨S, hST, hfour, Nat.le_of_not_gt hle⟩
  rw [hs, fourOnSeven_iff_rectangles]
  simp only [AllRectanglesRainbow, not_or]

/-- The still-open density statement for the exact three-projection graph class. -/
def RainbowDensityBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
    ∀ T : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint T →
      AllRectanglesRainbow T → (T.card : ℝ) ≤ δ * (n : ℝ) ^ 2

theorem seven_four_iff_rainbow_density :
    HasQuadraticVanishing 3 7 4 ↔ RainbowDensityBound := by
  rw [vanishing_iff_relation_bound 4 (by decide)]
  constructor
  · intro h δ hδ
    obtain ⟨N, hN⟩ := h δ hδ
    refine ⟨N, ?_⟩
    intro n hn T hlin hT
    have := hlin
    exact hN n hn T hlin ((support_avoids_iff_rainbow T).mpr hT)
  · intro h δ hδ
    obtain ⟨N, hN⟩ := h δ hδ
    refine ⟨N, ?_⟩
    intro n hn T hlin hT
    have := hlin
    exact hN n hn T hlin ((support_avoids_iff_rainbow T).mp hT)

theorem upper_four_of_rainbow (r : ℕ) (hr : 3 ≤ r) (h : RainbowDensityBound) :
    HasQuadraticVanishing r ((r - 2) * 4 + 3) 4 :=
  upper_of_triples r 4 hr (by decide) (seven_four_iff_rainbow_density.mpr h)

/-- Seven vertices are enough to hide the obstruction from two fixed projections. -/
def twoProjectionTrap : Finset (Fin 3 × Fin 3 × Fin 3) :=
  {(0, 0, 0), (0, 1, 1), (1, 0, 2), (1, 1, 0)}

theorem twoProjectionTrap_linear : ExplicitDisjoint twoProjectionTrap := by
  constructor <;> decide

theorem twoProjectionTrap_small : twoProjectionTrap.card = 4 ∧
    coordinateSupport twoProjectionTrap = 7 := by decide

theorem twoProjectionTrap_missed :
    RepeatedRectangle twoProjectionTrap ∧
    ¬ RepeatedRectangle (rotateTriples twoProjectionTrap) ∧
    ¬ RepeatedRectangle (rotateTriples (rotateTriples twoProjectionTrap)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, 1, 0, 1, 0, 1, 2, 0, by decide⟩
  all_goals
    unfold RepeatedRectangle
    simp only [not_exists]
    intro a a' b b' c₀₀ c₀₁ c₁₀ c₁₁
    simp only [mem_rotateTriples, twoProjectionTrap, mem_insert, mem_singleton,
      Prod.mk.injEq]
    omega


end P163

theorem proof :
    (∀ e : ℕ, 3 ≤ e →
      (P163.HasQuadraticVanishing 3 (e + 3) e ↔ P163.TripartiteRelationBound e)) ∧
    (P163.HasQuadraticVanishing 3 7 4 ↔ P163.RainbowDensityBound) ∧
    SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint P163.twoProjectionTrap ∧
    (P163.twoProjectionTrap.card = 4 ∧ P163.coordinateSupport P163.twoProjectionTrap = 7) ∧
    (P163.RepeatedRectangle P163.twoProjectionTrap ∧
      ¬P163.RepeatedRectangle (P163.rotateTriples P163.twoProjectionTrap) ∧
      ¬P163.RepeatedRectangle (P163.rotateTriples (P163.rotateTriples P163.twoProjectionTrap))) :=
  ⟨P163.vanishing_iff_relation_bound, P163.seven_four_iff_rainbow_density,
    P163.twoProjectionTrap_linear, P163.twoProjectionTrap_small, P163.twoProjectionTrap_missed⟩

end Submissions.BrownErdosSosRainbowReduction.Main
