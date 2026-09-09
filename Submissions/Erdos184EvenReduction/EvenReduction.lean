import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Order.Preorder.Finite

/-
This is the standard conditional reduction to even-degree graphs. The uniform
even-degree bound remains an assumption; the open conjecture is not proved. The singleton construction below is reused from Jig
artifact bb4fb627-8bcf-4169-bedf-6b62bdc06d04 (woshuajolk / Worker04), original
source SHA-256 fd1d049d3067da86983173eeb8df6876fbc1a4f9d461326531510fb55afeaaa4.
Only its namespace and final theorem name are changed. The locally verified
ForestParity proof is inlined below. No Statements or Submissions imports.
-/

open SimpleGraph

namespace Submissions.Erdos184EvenReduction.EvenReduction
universe u

namespace ForestParity


open scoped Classical

theorem degree_sdiff {V : Type*} [Fintype V] (G H : SimpleGraph V)
    (h : H ≤ G) (v : V) : (G \ H).degree v = G.degree v - H.degree v := by
  classical
  simp only [← card_neighborFinset_eq_degree, neighborFinset_sdiff]
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact (G.mem_neighborFinset v w).mpr (h ((H.mem_neighborFinset v w).mp hw))

theorem cycle_even {V : Type*} [Fintype V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (v : V) :
    Even (p.toSubgraph.spanningCoe.degree v) := by
  classical
  rw [Subgraph.degree_spanningCoe]
  by_cases hv : v ∈ p.toSubgraph.verts
  · have h := hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)
    have hd : p.toSubgraph.degree v = 2 := by
      simpa [Subgraph.degree, Set.fintypeCard_eq_ncard] using h
    rw [hd]
    decide
  · rw [Subgraph.degree_of_notMem_verts hv]
    exact ⟨0, rfl⟩

/-- Removing a forest is enough to make every degree even. This is the standard
structural reduction; it supplies no bound on the number of remaining cycles. -/
theorem proof {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeFinset.card ≤ Fintype.card V - 1 ∧
      ∀ v, Even ((G \ F).degree v) := by
  classical
  let S : Set (SimpleGraph V) := {F | F ≤ G ∧ ∀ v, Even (F.degree v) ↔ Even (G.degree v)}
  obtain ⟨F, hF⟩ := (Set.toFinite S).exists_minimal (show S.Nonempty from ⟨G, le_rfl, fun _ => Iff.rfl⟩)
  have hFG : F ≤ G := hF.1.1
  have hpar : ∀ v, Even (F.degree v) ↔ Even (G.degree v) := hF.1.2
  have hacyc : F.IsAcyclic := by
    intro u p hp
    let C := p.toSubgraph.spanningCoe
    have hCF : C ≤ F := p.toSubgraph.spanningCoe_le
    have hsub : F \ C ≤ F := sdiff_le
    have hm : F \ C ∈ S := by
      refine ⟨hsub.trans hFG, fun v => ?_⟩
      have hcycle : Even (C.degree v) := by
        simpa only [C, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using cycle_even p hp v
      have hlocal : Even ((F \ C).degree v) ↔ Even (G.degree v) := by
        rw [degree_sdiff F C hCF v, Nat.even_sub (degree_le_of_le (v := v) hCF)]
        simpa only [hcycle, iff_true] using hpar v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hlocal
    have hback : F ≤ F \ C := hF.2 hm hsub
    have he : p.toSubgraph.Adj u p.snd := p.toSubgraph_adj_snd hp.not_nil
    have hf : F.Adj u p.snd := p.toSubgraph.adj_sub he
    exact (sdiff_adj F C u p.snd).mp (hback hf) |>.2 he
  refine ⟨F, hFG, hacyc, ?_, fun v => ?_⟩
  · cases isEmpty_or_nonempty V with
    | inl h =>
      let := h
      have hbot : F = ⊥ := by
        ext v w
        exact isEmptyElim v
      simp [hbot]
    | inr h =>
      let := h
      obtain ⟨T, hFT, _, hT⟩ := connected_top.exists_isTree_le_of_le_of_isAcyclic
        (show F ≤ (⊤ : SimpleGraph V) from le_top) hacyc
      have hc := Finset.card_le_card (edgeFinset_mono hFT)
      have ht := hT.card_edgeFinset
      omega
  · rw [degree_sdiff G F hFG v, Nat.even_sub (degree_le_of_le (v := v) hFG)]
    exact (hpar v).symm


end ForestParity

def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

noncomputable def edgeSubgraph {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    G.Subgraph where
  verts := Set.univ
  Adj v w := s(v, w) = e.1
  adj_sub h := by
    rw [← G.mem_edgeSet, h]
    exact e.2
  edge_vert := by simp

theorem edgeSet_edgeSubgraph {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) :
    (edgeSubgraph G e).edgeSet = {e.1} := by
  ext x
  induction x using Sym2.inductionOn with
  | _ v w =>
      simp [Subgraph.mem_edgeSet, edgeSubgraph]

open scoped Classical in
noncomputable def singletonEdgeDecomposition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Finset G.Subgraph :=
  G.edgeFinset.attach.image fun e =>
    edgeSubgraph G ⟨e.1, SimpleGraph.mem_edgeFinset.mp e.2⟩

open scoped Classical in
theorem singletonProof :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        D.card ≤ G.edgeFinset.card := by
  intro V _ G
  refine ⟨singletonEdgeDecomposition G, ?_, ?_, ?_⟩
  · intro H hH
    simp only [singletonEdgeDecomposition, Finset.mem_image] at hH
    obtain ⟨e, -, rfl⟩ := hH
    right
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [← Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    rw [Subgraph.image_coe_edgeSet_coe, edgeSet_edgeSubgraph]
    simp
  · constructor
    · rintro H hH K hK hne
      simp only [singletonEdgeDecomposition, Finset.mem_coe, Finset.mem_image] at hH hK
      obtain ⟨e, -, rfl⟩ := hH
      obtain ⟨e', -, rfl⟩ := hK
      change Disjoint (edgeSubgraph G ⟨e.1, _⟩).edgeSet (edgeSubgraph G ⟨e'.1, _⟩).edgeSet
      rw [edgeSet_edgeSubgraph, edgeSet_edgeSubgraph]
      simp only [Set.disjoint_singleton]
      intro he
      apply hne
      congr
    · ext e
      simp [singletonEdgeDecomposition, edgeSet_edgeSubgraph]
  · unfold singletonEdgeDecomposition
    exact (Finset.card_image_le).trans_eq Finset.card_attach

/- `Subgraph.map` maps the vertex set through an image. Retaining the original
vertex set makes the canonical piece property definitionally unchanged. -/
def promote {V : Type*} {G H : SimpleGraph V} (h : H ≤ G) (K : H.Subgraph) :
    G.Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub ha := h (K.adj_sub ha)
  edge_vert := K.edge_vert
  symm := K.symm

@[simp] theorem promote_edgeSet {V : Type*} {G H : SimpleGraph V}
    (h : H ≤ G) (K : H.Subgraph) : (promote h K).edgeSet = K.edgeSet := rfl

@[simp] theorem promote_coe {V : Type*} {G H : SimpleGraph V}
    (h : H ≤ G) (K : H.Subgraph) : (promote h K).coe = K.coe := rfl

open scoped Classical in
theorem promote_pairwise {V : Type*} {G H : SimpleGraph V} (h : H ≤ G)
    (D : Finset H.Subgraph)
    (hd : Set.PairwiseDisjoint (D : Set H.Subgraph) (fun K => K.edgeSet)) :
    Set.PairwiseDisjoint (D.image (promote h) : Set G.Subgraph) (fun K => K.edgeSet) := by
  rintro A hA B hB hne
  obtain ⟨A0, hA0, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B0, hB0, rfl⟩ := Finset.mem_image.mp hB
  exact hd hA0 hB0 (fun heq => hne (congrArg (promote h) heq))

open scoped Classical in
theorem promote_cover {V : Type*} {G H : SimpleGraph V} (h : H ≤ G)
    (D : Finset H.Subgraph) :
    (⋃ K ∈ D.image (promote h), K.edgeSet) = ⋃ K ∈ D, K.edgeSet := by
  change (⋃ K ∈ (↑(D.image (promote h)) : Set G.Subgraph), K.edgeSet) = _
  rw [Finset.coe_image, Set.biUnion_image]
  rfl

open scoped Classical in
theorem combine {V : Type*} [Fintype V] {G H K : SimpleGraph V}
    (hHG : H ≤ G) (hKG : K ≤ G)
    (hdisj : Disjoint H.edgeSet K.edgeSet) (hcover : H.edgeSet ∪ K.edgeSet = G.edgeSet)
    (D : Finset H.Subgraph) (E : Finset K.Subgraph)
    (hDgood : ∀ L ∈ D, IsCycleOrEdge L.coe) (hD : IsDecomposition H D)
    (hEgood : ∀ L ∈ E, IsCycleOrEdge L.coe) (hE : IsDecomposition K E) :
    ∃ P : Finset G.Subgraph, (∀ L ∈ P, IsCycleOrEdge L.coe) ∧
      IsDecomposition G P ∧ P.card ≤ D.card + E.card := by
  let D' := D.image (promote hHG)
  let E' := E.image (promote hKG)
  refine ⟨D' ∪ E', ?_, ⟨?_, ?_⟩, ?_⟩
  · intro L hL
    rcases Finset.mem_union.mp hL with hL | hL
    · obtain ⟨L0, hL0, rfl⟩ := Finset.mem_image.mp hL
      exact hDgood L0 hL0
    · obtain ⟨L0, hL0, rfl⟩ := Finset.mem_image.mp hL
      exact hEgood L0 hL0
  · rw [Finset.coe_union]
    apply (promote_pairwise hHG D hD.1).union (promote_pairwise hKG E hE.1)
    intro A hA B hB _
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB
    exact hdisj.mono A.edgeSet_subset B.edgeSet_subset
  · change (⋃ L ∈ (↑(D' ∪ E') : Set G.Subgraph), L.edgeSet) = G.edgeSet
    rw [Finset.coe_union, Set.biUnion_union]
    change (⋃ L ∈ D.image (promote hHG), L.edgeSet) ∪
      (⋃ L ∈ E.image (promote hKG), L.edgeSet) = G.edgeSet
    rw [promote_cover, promote_cover, hD.2, hE.2]
    exact hcover
  · exact (Finset.card_union_le D' E').trans (add_le_add Finset.card_image_le Finset.card_image_le)

open Filter
open scoped Classical

/-- Canonical connected-cycle-or-single-edge bound, restricted only by even degree. -/
def EvenBound (C : ℝ) : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (∀ v, Even (G.degree v)) →
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ (D.card : ℝ) ≤ C * (Fintype.card V : ℝ)

/-- Exact copy of the root type, with local copies of its two definitions. -/
abbrev Root : Prop :=
  ∃ f : ℕ → ℝ,
    (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)

/-- The full root follows conditionally from the even-degree case, with C+1 overhead. -/
theorem proof (C : ℝ) (hC : EvenBound.{u} C) : Root.{u} := by
  refine ⟨fun n => (C + 1) * (n : ℝ),
    Asymptotics.isBigO_const_mul_self (C + 1) (fun n : ℕ => (n : ℝ)) atTop, ?_⟩
  intro V _ _ G
  obtain ⟨F, hFG, _, hFcard, hFeven⟩ :=
    ForestParity.proof G
  obtain ⟨D, hDgood, hD, hDcard⟩ := hC (G \ F) (by
    intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hFeven v)
  obtain ⟨E, hEgood, hE, hEcard⟩ := singletonProof F
  have hdisj : Disjoint (G \ F).edgeSet F.edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.disjoint_left.mpr (fun _ he hf => he.2 hf)
  have hcover : (G \ F).edgeSet ∪ F.edgeSet = G.edgeSet := by
    rw [edgeSet_sdiff, Set.sdiff_union_of_subset (edgeSet_mono hFG)]
  obtain ⟨P, hPgood, hP, hPcard⟩ :=
    combine (G := G) sdiff_le hFG hdisj hcover D E hDgood hD hEgood hE
  refine ⟨P, hPgood, hP, ?_⟩
  have hEn : (E.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hEcard.trans (hFcard.trans (Nat.sub_le _ _))
  calc
    (P.card : ℝ) ≤ (D.card : ℝ) + (E.card : ℝ) := by exact_mod_cast hPcard
    _ ≤ C * (Fintype.card V : ℝ) + (Fintype.card V : ℝ) := add_le_add hDcard hEn
    _ = (C + 1) * (Fintype.card V : ℝ) := by rw [add_mul, one_mul]

end Submissions.Erdos184EvenReduction.EvenReduction
