import Mathlib

namespace CompactnessConjecture

noncomputable section Foundations

open Filter Finset SimpleGraph
open scoped Topology

structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

def CompactnessConjectureStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → IsCyclicFamily family → IsCompactFamily family

theorem FamilyFree.member {family : Finset FiniteGraph}
    {forbidden : FiniteGraph} (hmem : forbidden ∈ family)
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree family host) : forbidden.graph.Free host :=
  hfree forbidden hmem

end Foundations

noncomputable section DensityReduction

open Finset SimpleGraph
open scoped Classical

lemma edgeFinset_card_eq_natCard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.edgeFinset_card (G := G))

lemma degree_eq_natCard_neighborSet {V : Type*}
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.card_neighborSet_eq_degree G v).symm

def booleanCut {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : SimpleGraph V :=
  G ⊓ (⊤ : SimpleGraph Bool).comap color

@[simp]
lemma booleanCut_adj {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) (u v : V) :
    (booleanCut G color).Adj u v ↔ G.Adj u v ∧ color u ≠ color v :=
  Iff.rfl

instance booleanCutDecidableRel {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) :
    DecidableRel (booleanCut G color).Adj :=
  inferInstanceAs
    (DecidableRel fun u v => G.Adj u v ∧ color u ≠ color v)

lemma booleanCut_le {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : booleanCut G color ≤ G := by
  intro u v huv
  exact huv.1

lemma booleanCut_isBipartite {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : (booleanCut G color).IsBipartite := by
  simpa using (SimpleGraph.Coloring.mk
    (G := booleanCut G color) color (fun h => h.2)).colorable

def flipBooleanColor {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) : V → Bool :=
  Function.update color v (! color v)

@[simp]
lemma flipBooleanColor_self {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) :
    flipBooleanColor color v v = ! color v := by
  simp [flipBooleanColor]

lemma booleanCut_deleteIncidence_flip
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).deleteIncidenceSet v =
      (booleanCut G color).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, booleanCut_adj]
  by_cases hx : x = v
  · subst x
    simp
  by_cases hy : y = v
  · subst y
    simp
  simp [flipBooleanColor, hx, hy]

lemma booleanCut_flip_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).neighborFinset v =
      G.neighborFinset v \ (booleanCut G color).neighborFinset v := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
    booleanCut_adj]
  by_cases hwv : w = v
  · subst w
    simp
  · cases hcv : color v <;> cases hcw : color w <;>
      simp [flipBooleanColor, hwv, hcv, hcw]

lemma booleanCut_flip_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).degree v +
        (booleanCut G color).degree v = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      booleanCut_flip_neighborFinset]
  apply Finset.card_sdiff_add_card_eq_card
  intro w hw
  have hadj : (booleanCut G color).Adj v w := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw
  simpa only [SimpleGraph.mem_neighborFinset] using hadj.1

theorem exists_maximum_booleanCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ color : V → Bool, ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card := by
  classical
  obtain ⟨color, _, hcolor⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V → Bool))
    (fun candidate => (booleanCut G candidate).edgeFinset.card)
    (Finset.univ_nonempty)
  exact ⟨color, fun other => hcolor other (Finset.mem_univ other)⟩

lemma maximum_booleanCut_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool)
    (hmax : ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card)
    (v : V) :
    G.degree v ≤ 2 * (booleanCut G color).degree v := by
  classical
  let flipped := flipBooleanColor color v
  have hflipped := hmax flipped
  have hdeleted := congrArg (fun H : SimpleGraph V => Nat.card H.edgeSet)
    (booleanCut_deleteIncidence_flip G color v)
  have hedge :
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v := by
    calc
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        ((booleanCut G flipped).deleteIncidenceSet v).edgeFinset.card :=
        (SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G flipped) v).symm
      _ = Nat.card ((booleanCut G flipped).deleteIncidenceSet v).edgeSet :=
        edgeFinset_card_eq_natCard _
      _ = Nat.card ((booleanCut G color).deleteIncidenceSet v).edgeSet :=
        hdeleted
      _ = ((booleanCut G color).deleteIncidenceSet v).edgeFinset.card :=
        (edgeFinset_card_eq_natCard _).symm
      _ = (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v :=
        SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G color) v
  have hflipDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G flipped) v
  have hcutDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G color) v
  have hpartition := booleanCut_flip_degree_add G color v
  change (booleanCut G flipped).degree v +
    (booleanCut G color).degree v = G.degree v at hpartition
  omega

theorem exists_bipartite_half_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ B : SimpleGraph V,
      B.IsBipartite ∧ B ≤ G ∧
      G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
  classical
  obtain ⟨color, hmax⟩ := exists_maximum_booleanCut G
  refine ⟨booleanCut G color, booleanCut_isBipartite G color,
    booleanCut_le G color, ?_⟩
  have hsum :
      2 * G.edgeFinset.card ≤
        2 * (2 * (booleanCut G color).edgeFinset.card) := by
    calc
      2 * G.edgeFinset.card = ∑ v : V, G.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
      _ ≤ ∑ v : V, 2 * (booleanCut G color).degree v :=
        Finset.sum_le_sum fun v _ =>
          maximum_booleanCut_degree G color hmax v
      _ = 2 * (2 * (booleanCut G color).edgeFinset.card) := by
        rw [← Finset.mul_sum,
          SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hhalf := Nat.le_of_mul_le_mul_left hsum (by omega)
  simpa only [edgeFinset_card_eq_natCard] using hhalf

lemma natCard_support_le_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card G.support ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    (Finite.card_subtype_le (fun v : V => v ∈ G.support))

lemma natCard_support_deleteIncidence_add_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (hv : v ∈ G.support) :
    Nat.card (G.deleteIncidenceSet v).support + 1 ≤
      Nat.card G.support := by
  have hdrop := SimpleGraph.card_support_deleteIncidenceSet G hv
  have hpositive : 0 < Nat.card G.support :=
    Finite.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  simp only [Nat.card_eq_fintype_card] at hpositive ⊢
  omega

noncomputable def sharpPruningPotential {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * Fintype.card V * Nat.card H.edgeSet +
    originalEdges * (Fintype.card V - Nat.card H.support)

noncomputable def sharpPruningScore {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * sharpPruningPotential originalEdges H +
    (if 0 < Nat.card H.edgeSet then 1 else 0)

theorem exists_maximum_sharp_pruning_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (base : SimpleGraph V) (originalEdges : ℕ) :
    ∃ H : SimpleGraph V, H ≤ base ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningPotential originalEdges D ≤
          sharpPruningPotential originalEdges H) ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningScore originalEdges D ≤
          sharpPruningScore originalEdges H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => H ≤ base)
  have hnonempty : candidates.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [candidates]
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    candidates (sharpPruningScore originalEdges) hnonempty
  refine ⟨H, (Finset.mem_filter.mp hH).2, ?_, ?_⟩
  · intro D hD
    have hscore := hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)
    unfold sharpPruningScore at hscore
    split_ifs at hscore <;> omega
  · intro D hD
    exact hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)

lemma maximum_sharp_pruning_subgraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (base H : SimpleGraph V) [DecidableRel H.Adj]
    (originalEdges : ℕ) (hHB : H ≤ base)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningPotential originalEdges D ≤
        sharpPruningPotential originalEdges H)
    {v : V} (hv : v ∈ H.support) :
    originalEdges ≤ 2 * Fintype.card V * H.degree v := by
  classical
  let D := H.deleteIncidenceSet v
  have hDB : D ≤ base :=
    le_trans (SimpleGraph.deleteIncidenceSet_le H v) hHB
  have hscore := hmax D hDB
  have hdrop : Nat.card D.support + 1 ≤ Nat.card H.support :=
    natCard_support_deleteIncidence_add_one_le H hv
  have hsupport : Nat.card H.support ≤ Fintype.card V :=
    natCard_support_le_card H
  have hcomplement :
      Fintype.card V - Nat.card H.support + 1 ≤
        Fintype.card V - Nat.card D.support := by
    omega
  have hweightedComplement :
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges ≤
        originalEdges * (Fintype.card V - Nat.card D.support) := by
    calc
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges =
        originalEdges * (Fintype.card V - Nat.card H.support + 1) := by
          simp [Nat.mul_add]
      _ ≤ originalEdges * (Fintype.card V - Nat.card D.support) :=
        Nat.mul_le_mul_left originalEdges hcomplement
  have hdeleted :
      Nat.card D.edgeSet =
        Nat.card H.edgeSet - Nat.card (H.neighborSet v) := by
    simpa only [D, edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.card_edgeFinset_deleteIncidenceSet H v)
  have hdegreeEdges :
      Nat.card (H.neighborSet v) ≤ Nat.card H.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.degree_le_card_edgeFinset H v)
  have hedgeAdd :
      Nat.card D.edgeSet + Nat.card (H.neighborSet v) =
        Nat.card H.edgeSet := by
    omega
  have hweightedEdges :
      2 * Fintype.card V * Nat.card H.edgeSet =
        2 * Fintype.card V * Nat.card D.edgeSet +
          2 * Fintype.card V * Nat.card (H.neighborSet v) := by
    rw [← hedgeAdd, mul_add]
  change
    2 * Fintype.card V * Nat.card D.edgeSet +
        originalEdges * (Fintype.card V - Nat.card D.support) ≤
      2 * Fintype.card V * Nat.card H.edgeSet +
        originalEdges * (Fintype.card V - Nat.card H.support)
    at hscore
  simp only [degree_eq_natCard_neighborSet]
  omega

lemma maximum_sharp_pruning_subgraph_edge_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (original base H : SimpleGraph V) [DecidableRel original.Adj]
    (hpositive : 0 < original.edgeFinset.card)
    (hhalf : original.edgeFinset.card ≤ 2 * base.edgeFinset.card)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningScore (Nat.card original.edgeSet) D ≤
        sharpPruningScore (Nat.card original.edgeSet) H) :
    0 < Nat.card H.edgeSet := by
  classical
  have hpositiveNat : 0 < Nat.card original.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hpositive
  have hhalfNat :
      Nat.card original.edgeSet ≤ 2 * Nat.card base.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hhalf
  have hbasePositive : 0 < Nat.card base.edgeSet := by
    omega
  have hbaseScore := hmax base (le_refl base)
  by_contra hnot
  have hHzero : Nat.card H.edgeSet = 0 := by
    omega
  have hHedge : H.edgeFinset.card = 0 := by
    simpa only [edgeFinset_card_eq_natCard] using hHzero
  have hHbot : H = ⊥ := by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    exact Finset.card_eq_zero.mp hHedge
  have hsharpBase :
      Nat.card original.edgeSet * Fintype.card V ≤
        sharpPruningPotential (Nat.card original.edgeSet) base := by
    have hcross :
        Nat.card original.edgeSet * Fintype.card V ≤
          2 * Fintype.card V * Nat.card base.edgeSet := by
      calc
        Nat.card original.edgeSet * Fintype.card V =
            Fintype.card V * Nat.card original.edgeSet := by
          ac_rfl
        _ ≤ Fintype.card V * (2 * Nat.card base.edgeSet) :=
          Nat.mul_le_mul_left (Fintype.card V) hhalfNat
        _ = 2 * Fintype.card V * Nat.card base.edgeSet := by
          ac_rfl
    unfold sharpPruningPotential
    omega
  have hHscore :
      sharpPruningScore (Nat.card original.edgeSet) H =
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    rw [hHbot]
    simp [sharpPruningScore, sharpPruningPotential]
  have hscoreContradiction :
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 ≤
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    calc
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 =
          sharpPruningScore (Nat.card original.edgeSet) base := by
        unfold sharpPruningScore
        rw [if_pos hbasePositive]
      _ ≤ sharpPruningScore (Nat.card original.edgeSet) H :=
        hbaseScore
      _ = 2 * (Nat.card original.edgeSet * Fintype.card V) :=
        hHscore
  omega

theorem exists_bipartite_min_degree_supported_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ H : SimpleGraph V,
      H.IsBipartite ∧ H ≤ G ∧ 0 < Nat.card H.edgeSet ∧
      ∀ v : V, v ∈ H.support →
        G.edgeFinset.card ≤ 2 * Fintype.card V * H.degree v := by
  classical
  obtain ⟨cut, hcutBipartite, hcutSubgraph, hcutEdges⟩ :=
    exists_bipartite_half_edges G
  obtain ⟨H, hH, hpotential, hscore⟩ :=
    exists_maximum_sharp_pruning_subgraph cut (Nat.card G.edgeSet)
  refine ⟨H, SimpleGraph.Colorable.mono_left hH hcutBipartite,
    le_trans hH hcutSubgraph,
    maximum_sharp_pruning_subgraph_edge_positive
      G cut H hpositive hcutEdges hscore, ?_⟩
  intro v hv
  simpa only [edgeFinset_card_eq_natCard,
    degree_eq_natCard_neighborSet] using
    (maximum_sharp_pruning_subgraph_degree
      cut H (Nat.card G.edgeSet) hH hpotential hv)

theorem exists_bipartite_min_degree_subgraph
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ (N : ℕ) (B : SimpleGraph (Fin N)) (f : Fin N ↪ Fin n),
      0 < N ∧ N ≤ n ∧ B.IsBipartite ∧ B.map f ≤ G ∧
      G.edgeFinset.card ≤ 2 * n * B.minDegree ∧
      ∀ v : Fin N, G.edgeFinset.card ≤ 2 * n * B.degree v := by
  classical
  obtain ⟨H, hHbip, hHG, hHpositive, hminimum⟩ :=
    exists_bipartite_min_degree_supported_subgraph G hpositive
  have hsupportPositive : 0 < Nat.card H.support := by
    apply Finite.card_pos_iff.mpr
    obtain ⟨⟨edge, hedge⟩⟩ := Finite.card_pos_iff.mp hHpositive
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have huv : H.Adj u v := by
        simpa only [SimpleGraph.mem_edgeSet] using hedge
      exact ⟨⟨u, huv.mem_support_left⟩⟩
  let N := Nat.card H.support
  let supportEquiv : Fin N ≃ H.support :=
    (Finite.equivFin H.support).symm
  let f : Fin N ↪ Fin n :=
    supportEquiv.toEmbedding.trans
      (Function.Embedding.subtype (fun v : Fin n => v ∈ H.support))
  let B : SimpleGraph (Fin N) :=
    (H.induce H.support).comap supportEquiv.toEmbedding
  have hBcomap : B = H.comap f := by
    ext u v
    rfl
  have hBbip : B.IsBipartite := by
    rw [hBcomap]
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.comap f H) hHbip
  have hmap : B.map f ≤ G := by
    calc
      B.map f ≤ H := by
        rw [hBcomap]
        exact SimpleGraph.map_comap_le f H
      _ ≤ G := hHG
  let supportIso : B ≃g H.induce H.support :=
    SimpleGraph.Iso.comap supportEquiv (H.induce H.support)
  have hdegrees : ∀ v : Fin N,
      G.edgeFinset.card ≤ 2 * n * B.degree v := by
    intro v
    have hdegree := hminimum (f v) (supportEquiv v).property
    have hBdegree :
        Nat.card (B.neighborSet v) =
          Nat.card (H.neighborSet (f v)) := by
      calc
        Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet
              (supportEquiv v)) := by
          change Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet (supportIso v))
          exact Nat.card_congr (supportIso.mapNeighborSet v)
        _ = Nat.card (H.neighborSet (f v)) := by
          change Nat.card ((H.induce H.support).neighborSet
            (supportEquiv v)) =
              Nat.card (H.neighborSet (supportEquiv v : Fin n))
          simpa only [degree_eq_natCard_neighborSet] using
            (SimpleGraph.degree_induce_support (G := H)
              (supportEquiv v))
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet, Fintype.card_fin, hBdegree]
      using hdegree
  have hNn : N ≤ n := by
    simpa using Fintype.card_le_of_injective f f.injective
  letI : Nonempty (Fin N) := ⟨⟨0, hsupportPositive⟩⟩
  obtain ⟨v, hv⟩ := B.exists_minimal_degree_vertex
  have hmin : G.edgeFinset.card ≤ 2 * n * B.minDegree := by
    rw [hv]
    exact hdegrees v
  exact ⟨N, B, f, hsupportPositive, hNn,
    hBbip, hmap, hmin, hdegrees⟩

end DensityReduction

noncomputable section Patterns

open SimpleGraph

abbrev SubdivisionVertex (k : ℕ) :=
  (Fin 3 ⊕ Fin k) ⊕ (Fin 3 × Fin k)

def subdivisionRelation (k : ℕ) :
    SubdivisionVertex k → SubdivisionVertex k → Prop
  | .inl (.inl base), .inr (otherBase, _) => base = otherBase
  | .inl (.inr center), .inr (_, otherCenter) => center = otherCenter
  | _, _ => False

def SubdivisionGraph (k : ℕ) : SimpleGraph (SubdivisionVertex k) :=
  SimpleGraph.fromRel (subdivisionRelation k)

def subdivisionColor (k : ℕ) : SubdivisionVertex k → Bool
  | .inl _ => false
  | .inr _ => true

abbrev thetaGraph : SimpleGraph (SubdivisionVertex 2) :=
  SubdivisionGraph 2

abbrev gammaGraph : SimpleGraph (SubdivisionVertex 3) :=
  SubdivisionGraph 3

end Patterns

noncomputable section Quotients

open Finset SimpleGraph

abbrev JVertex :=
  (Fin 4 ⊕ (Fin 2 × Fin 2)) ⊕
    ((Fin 2 × (Fin 3 × Fin 2)) ⊕ Unit)

def jBase (copy : Fin 2) (base : Fin 3) : Fin 4 :=
  if base = 0 then
    if copy = 0 then 0 else 1
  else if base = 1 then 2 else 3

def jTemplateRelation : JVertex → JVertex → Prop
  | .inl (.inl base), .inr (.inl (copy, (i, _))) =>
      base = jBase copy i
  | .inl (.inr (copy, center)), .inr (.inl (copy', (_, center'))) =>
      copy = copy' ∧ center = center'
  | .inl (.inl base), .inr (.inr _) =>
      base = 0 ∨ base = 1
  | _, _ => False

def jTemplate : SimpleGraph JVertex :=
  SimpleGraph.fromRel jTemplateRelation

def jColor : JVertex → Bool
  | .inl _ => false
  | .inr _ => true

def InJCopy (copy : Fin 2) : JVertex → Prop
  | .inl (.inl base) => ∃ i : Fin 3, base = jBase copy i
  | .inl (.inr (copy', _)) => copy = copy'
  | .inr (.inl (copy', _)) => copy = copy'
  | .inr (.inr _) => False

abbrev KVertex := Fin 2 × SubdivisionVertex 3

def kSpecifiedCenter : SubdivisionVertex 3 :=
  .inl (.inr 0)

def kTemplateRelation (u v : KVertex) : Prop :=
  (u.1 = v.1 ∧ subdivisionRelation 3 u.2 v.2) ∨
    (u.1 = 0 ∧ v.1 = 1 ∧
      u.2 = kSpecifiedCenter ∧ v.2 = kSpecifiedCenter)

def kTemplate : SimpleGraph KVertex :=
  SimpleGraph.fromRel kTemplateRelation

def kColor (v : KVertex) : Bool :=
  if v.1 = 0 then subdivisionColor 3 v.2
  else !(subdivisionColor 3 v.2)

def ColorRespecting {α : Type*}
    (color : α → Bool) (f : α → α) : Prop :=
  ∀ u v, f u = f v → color u = color v

def JAdmissible (f : JVertex → JVertex) : Prop :=
  ColorRespecting jColor f ∧
    Function.Injective
      (fun base : Fin 4 => f (.inl (.inl base))) ∧
    ∀ copy : Fin 2, Set.InjOn f {v | InJCopy copy v}

def KAdmissible (f : KVertex → KVertex) : Prop :=
  ColorRespecting kColor f ∧
    ∀ copy : Fin 2,
      Set.InjOn f {v : KVertex | v.1 = copy}

def quotientRelation {α : Type*}
    (graph : SimpleGraph α) (f : α → α)
    (u v : Set.range f) : Prop :=
  ∃ x y : α, f x = (u : α) ∧ f y = (v : α) ∧ graph.Adj x y

def quotientGraph {α : Type*}
    (graph : SimpleGraph α) (f : α → α) :
    SimpleGraph (Set.range f) :=
  SimpleGraph.fromRel (quotientRelation graph f)

noncomputable def encodeFiniteGraph {α : Type*} [Fintype α]
    (graph : SimpleGraph α) : FiniteGraph :=
  ⟨Fintype.card α,
    graph.map (Fintype.equivFin α).toEmbedding⟩

noncomputable def jQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : JVertex → JVertex // JAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph jTemplate (f : JVertex → JVertex)))).toFinset

theorem jQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ jQuotients ↔
      ∃ f : JVertex → JVertex, JAdmissible f ∧
        encodeFiniteGraph (quotientGraph jTemplate f) = graph := by
  rw [jQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

noncomputable def kQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : KVertex → KVertex // KAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph kTemplate (f : KVertex → KVertex)))).toFinset

theorem kQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ kQuotients ↔
      ∃ f : KVertex → KVertex, KAdmissible f ∧
        encodeFiniteGraph (quotientGraph kTemplate f) = graph := by
  rw [kQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

def finiteCycle (n : ℕ) : FiniteGraph :=
  ⟨n, SimpleGraph.cycleGraph n⟩

noncomputable def proposedFamily : Finset FiniteGraph := by
  classical
  exact {finiteCycle 4, finiteCycle 6} ∪ jQuotients ∪ kQuotients

theorem proposedFamily_mem_iff {graph : FiniteGraph} :
    graph ∈ proposedFamily ↔
      (((graph = finiteCycle 4 ∨ graph = finiteCycle 6) ∨
        (∃ f : JVertex → JVertex, JAdmissible f ∧
          encodeFiniteGraph (quotientGraph jTemplate f) = graph)) ∨
        (∃ f : KVertex → KVertex, KAdmissible f ∧
          encodeFiniteGraph (quotientGraph kTemplate f) = graph)) := by
  classical
  simp only [proposedFamily, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, jQuotients_mem_iff, kQuotients_mem_iff]

theorem proposedFamily_induction {P : FiniteGraph → Prop}
    (hfour : P (finiteCycle 4)) (hsix : P (finiteCycle 6))
    (hj : ∀ f : JVertex → JVertex, JAdmissible f →
      P (encodeFiniteGraph (quotientGraph jTemplate f)))
    (hk : ∀ f : KVertex → KVertex, KAdmissible f →
      P (encodeFiniteGraph (quotientGraph kTemplate f))) :
    ∀ graph ∈ proposedFamily, P graph := by
  intro graph hgraph
  rcases proposedFamily_mem_iff.mp hgraph with
    ((rfl | rfl) | ⟨f, hf, rfl⟩) | ⟨f, hf, rfl⟩
  · exact hfour
  · exact hsix
  · exact hj f hf
  · exact hk f hf

theorem four_cycle_mem_proposedFamily :
    finiteCycle 4 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inl rfl)))

theorem proposedFamily_nonempty : proposedFamily.Nonempty :=
  ⟨finiteCycle 4, four_cycle_mem_proposedFamily⟩

theorem six_cycle_mem_proposedFamily : finiteCycle 6 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inr rfl)))

theorem proposedFamilyFree_four_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 4).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member four_cycle_mem_proposedFamily hfree

theorem proposedFamilyFree_six_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 6).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member six_cycle_mem_proposedFamily hfree

lemma jQuotient_mem_proposedFamily
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    encodeFiniteGraph (quotientGraph jTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inr ⟨f, hf, rfl⟩))

lemma kQuotient_mem_proposedFamily
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    encodeFiniteGraph (quotientGraph kTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inr ⟨f, hf, rfl⟩)

end Quotients

noncomputable section Geometry

open SimpleGraph

section SymplecticGeometry

variable (K : Type*) [Field K]

abbrev SymplecticVector := Fin 4 → K

def standardSymplecticForm
    (u v : SymplecticVector K) : K :=
  u 0 * v 1 - u 1 * v 0 +
    (u 2 * v 3 - u 3 * v 2)

theorem standardSymplecticForm_self
    (u : SymplecticVector K) :
    standardSymplecticForm K u u = 0 := by
  unfold standardSymplecticForm
  ring

lemma standardSymplecticForm_swap
    (u v : SymplecticVector K) :
    standardSymplecticForm K u v =
      -standardSymplecticForm K v u := by
  unfold standardSymplecticForm
  ring

lemma standardSymplecticForm_add_left
    (u v w : SymplecticVector K) :
    standardSymplecticForm K (u + v) w =
      standardSymplecticForm K u w + standardSymplecticForm K v w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring

lemma standardSymplecticForm_add_right
    (u v w : SymplecticVector K) :
    standardSymplecticForm K u (v + w) =
      standardSymplecticForm K u v + standardSymplecticForm K u w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring

lemma standardSymplecticForm_smul_left
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K (a • u) v =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring

lemma standardSymplecticForm_smul_right
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K u (a • v) =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring

theorem standardSymplecticForm_nondegenerate_left
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K u v = 0) : u = 0 := by
  funext i
  fin_cases i
  · simpa [standardSymplecticForm] using h ![0, 1, 0, 0]
  · simpa [standardSymplecticForm] using h ![1, 0, 0, 0]
  · simpa [standardSymplecticForm] using h ![0, 0, 0, 1]
  · simpa [standardSymplecticForm] using h ![0, 0, 1, 0]

theorem standardSymplecticForm_nondegenerate_right
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K v u = 0) : u = 0 := by
  apply standardSymplecticForm_nondegenerate_left K u
  intro v
  rw [standardSymplecticForm_swap, h v, neg_zero]

def standardSymplecticBilin :
    LinearMap.BilinForm K (SymplecticVector K) :=
  LinearMap.mk₂ K (standardSymplecticForm K)
    (standardSymplecticForm_add_left K)
    (fun a u v => by
      simpa [smul_eq_mul] using standardSymplecticForm_smul_left K a u v)
    (standardSymplecticForm_add_right K)
    (fun a u v => by
      simpa [smul_eq_mul] using standardSymplecticForm_smul_right K a u v)

theorem standardSymplecticBilin_nondegenerate :
    (standardSymplecticBilin K).Nondegenerate := by
  constructor
  · intro u hu
    exact standardSymplecticForm_nondegenerate_left K u hu
  · intro u hu
    exact standardSymplecticForm_nondegenerate_right K u hu

theorem standardSymplecticBilin_isAlt :
    (standardSymplecticBilin K).IsAlt := by
  intro u
  exact standardSymplecticForm_self K u

abbrev SymplecticPoint :=
  {P : Submodule K (SymplecticVector K) //
    Module.finrank K P = 1}

abbrev SymplecticLine :=
  {L : Submodule K (SymplecticVector K) //
    Module.finrank K L = 2 ∧
      ∀ u ∈ L, ∀ v ∈ L, standardSymplecticForm K u v = 0}

abbrev SymplecticPointOrthogonal (p : SymplecticPoint K) :=
  (standardSymplecticBilin K).orthogonal p.1

lemma symplecticPoint_le_orthogonal (p : SymplecticPoint K) :
    p.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  by_cases hx0 : x = 0
  · simp [hx0, standardSymplecticForm]
  · have hxsub : (⟨x, hx⟩ : p.1) ≠ 0 := by
      intro h
      apply hx0
      simpa using congrArg Subtype.val h
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hxsub (⟨y, hy⟩ : p.1)
    have hav : a • x = y := congrArg Subtype.val ha
    rw [← hav, standardSymplecticForm_smul_left,
      standardSymplecticForm_self, mul_zero]

lemma symplecticPointOrthogonal_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointOrthogonal K p) = 3 := by
  change Module.finrank K
    ((standardSymplecticBilin K).orthogonal p.1) = 3
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K), p.2]
  simp [SymplecticVector]

abbrev SymplecticPointRadical (p : SymplecticPoint K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype p.1

lemma symplecticPointRadical_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointRadical K p) = 1 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticPoint_le_orthogonal K p)).finrank_eq.trans p.2

abbrev SymplecticPointQuotient (p : SymplecticPoint K) :=
  (SymplecticPointOrthogonal K p) ⧸ (SymplecticPointRadical K p)

lemma symplecticPointQuotient_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointQuotient K p) = 2 := by
  change Module.finrank K
    (↥(SymplecticPointOrthogonal K p) ⧸
      SymplecticPointRadical K p) = 2
  have h := Submodule.finrank_quotient_add_finrank
    (SymplecticPointRadical K p)
  rw [symplecticPointRadical_finrank K p,
    symplecticPointOrthogonal_finrank K p] at h
  omega

lemma quotient_map_finrank
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (R S : Submodule K W) (hRS : R ≤ S) :
    Module.finrank K (Submodule.map R.mkQ S) +
      Module.finrank K R = Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (R.mkQ.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hRS).finrank_eq] at h
  exact h

lemma symplecticLine_le_pointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) : L.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  exact L.2.2 y (hpL hy) x hx

lemma symplectic_two_plane_isotropic
    {p : SymplecticPoint K}
    {S : Submodule K (SymplecticVector K)}
    (hdim : Module.finrank K S = 2)
    (hpS : p.1 ≤ S)
    (hSorth : S ≤ SymplecticPointOrthogonal K p) :
    ∀ u ∈ S, ∀ v ∈ S, standardSymplecticForm K u v = 0 := by
  intro u hu v hv
  by_cases huP : u ∈ p.1
  · exact hSorth hv u huP
  · have hle : p.1 ⊔ K ∙ u ≤ S := by
      apply sup_le hpS
      exact (Submodule.span_le).mpr (by simpa using hu)
    have hspan : p.1 ⊔ K ∙ u = S :=
      Submodule.eq_of_le_of_finrank_eq hle (by
        rw [Submodule.finrank_sup_span_singleton huP, p.2, hdim])
    have hvspan : v ∈ p.1 ⊔ K ∙ u := hspan.symm ▸ hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvspan
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have horth : standardSymplecticForm K a u = 0 :=
      hSorth hu a ha
    have hreverse : standardSymplecticForm K u a = 0 := by
      rw [standardSymplecticForm_swap, horth, neg_zero]
    rw [standardSymplecticForm_add_right,
      standardSymplecticForm_smul_right,
      standardSymplecticForm_self,
      hreverse, mul_zero, add_zero]

abbrev SymplecticLinesOnPoint (p : SymplecticPoint K) :=
  {L : SymplecticLine K // p.1 ≤ L.1}

abbrev SymplecticLineInPointOrthogonal
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype L.1

lemma symplecticLineInPointOrthogonal_finrank
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    Module.finrank K (SymplecticLineInPointOrthogonal K p L) = 2 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticLine_le_pointOrthogonal K hpL)).finrank_eq.trans L.2.1

lemma symplecticPointRadical_le_lineInPointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    SymplecticPointRadical K p ≤
      SymplecticLineInPointOrthogonal K p L :=
  Submodule.comap_mono hpL

noncomputable def symplecticLinesOnPointEquivSubmodule
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      {S : Submodule K (SymplecticPointQuotient K p) //
        Module.finrank K S = 1} where
  toFun L :=
    ⟨Submodule.map (SymplecticPointRadical K p).mkQ
       (SymplecticLineInPointOrthogonal K p L.1), by
       change Module.finrank K
         (Submodule.map (SymplecticPointRadical K p).mkQ
           (SymplecticLineInPointOrthogonal K p L.1)) = 1
       have h := quotient_map_finrank K
         (SymplecticPointRadical K p)
         (SymplecticLineInPointOrthogonal K p L.1)
         (symplecticPointRadical_le_lineInPointOrthogonal K L.2)
       rw [symplecticPointRadical_finrank K p,
         symplecticLineInPointOrthogonal_finrank K L.2] at h
       omega⟩
  invFun Q := by
    let T : Submodule K (SymplecticPointOrthogonal K p) :=
      Submodule.comap (SymplecticPointRadical K p).mkQ Q.1
    have hrad : SymplecticPointRadical K p ≤ T :=
      Submodule.le_comap_mkQ (SymplecticPointRadical K p) Q.1
    have hmap :
        Submodule.map (SymplecticPointRadical K p).mkQ T = Q.1 := by
      apply Submodule.map_comap_eq_self
      rw [Submodule.range_mkQ]
      exact le_top
    have hdimT : Module.finrank K T = 2 := by
      have h := quotient_map_finrank K
        (SymplecticPointRadical K p) T hrad
      rw [hmap, Q.2, symplecticPointRadical_finrank K p] at h
      omega
    let S : Submodule K (SymplecticVector K) :=
      Submodule.map (SymplecticPointOrthogonal K p).subtype T
    have hdimS : Module.finrank K S = 2 := by
      exact (Submodule.finrank_map_subtype_eq
        (SymplecticPointOrthogonal K p) T).trans hdimT
    have hSorth : S ≤ SymplecticPointOrthogonal K p := by
      intro x hx
      rcases hx with ⟨y, _, rfl⟩
      exact y.2
    have hpS : p.1 ≤ S := by
      intro x hx
      have hxorth : x ∈ SymplecticPointOrthogonal K p :=
        symplecticPoint_le_orthogonal K p hx
      have hxrad :
          (⟨x, hxorth⟩ : SymplecticPointOrthogonal K p) ∈
            SymplecticPointRadical K p := hx
      exact ⟨⟨x, hxorth⟩, hrad hxrad, rfl⟩
    exact ⟨⟨S, hdimS,
      symplectic_two_plane_isotropic K hdimS hpS hSorth⟩, hpS⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointRadical K p).mkQ
        (Submodule.map (SymplecticPointRadical K p).mkQ
          (SymplecticLineInPointOrthogonal K p L.1))) = L.1.1
    rw [Submodule.comap_map_mkQ,
      sup_eq_right.mpr
        (symplecticPointRadical_le_lineInPointOrthogonal K L.2)]
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        L.1.1) = L.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr
      (symplecticLine_le_pointOrthogonal K L.2)
  right_inv Q := by
    apply Subtype.ext
    change Submodule.map (SymplecticPointRadical K p).mkQ
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        (Submodule.map (SymplecticPointOrthogonal K p).subtype
          (Submodule.comap (SymplecticPointRadical K p).mkQ
            Q.1))) = Q.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr
        (SymplecticPointOrthogonal K p).subtype_injective,
      sup_bot_eq]
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_mkQ]
    exact le_top

noncomputable def symplecticLinesOnPointEquiv
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      Projectivization K (SymplecticPointQuotient K p) :=
  (symplecticLinesOnPointEquivSubmodule K p).trans
    (Projectivization.equivSubmodule K
      (SymplecticPointQuotient K p)).symm

lemma symplecticLinesOnPoint_card [Finite K]
    (p : SymplecticPoint K) :
    Nat.card (SymplecticLinesOnPoint K p) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticLinesOnPointEquiv K p)]
  exact Projectivization.card_of_finrank_two K
    (SymplecticPointQuotient K p)
    (symplecticPointQuotient_finrank K p)

abbrev SymplecticPointsOnLine (L : SymplecticLine K) :=
  {p : SymplecticPoint K // p.1 ≤ L.1}

noncomputable def symplecticPointsOnLineEquivSubmodule
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃
      {S : Submodule K L.1 // Module.finrank K S = 1} where
  toFun p :=
    ⟨Submodule.comap L.1.subtype p.1.1,
      (Submodule.comapSubtypeEquivOfLe p.2).finrank_eq.trans p.1.2⟩
  invFun S :=
    ⟨⟨Submodule.map L.1.subtype S.1,
       (Submodule.finrank_map_subtype_eq L.1 S.1).trans S.2⟩,
      by
        intro x hx
        rcases hx with ⟨y, _, rfl⟩
        exact y.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map L.1.subtype
      (Submodule.comap L.1.subtype p.1.1) = p.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr p.2
  right_inv S := by
    apply Subtype.ext
    change Submodule.comap L.1.subtype
      (Submodule.map L.1.subtype S.1) = S.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr L.1.subtype_injective, sup_bot_eq]

noncomputable def symplecticPointsOnLineEquiv
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃ Projectivization K L.1 :=
  (symplecticPointsOnLineEquivSubmodule K L).trans
    (Projectivization.equivSubmodule K L.1).symm

lemma symplecticPointsOnLine_card [Finite K]
    (L : SymplecticLine K) :
    Nat.card (SymplecticPointsOnLine K L) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticPointsOnLineEquiv K L)]
  exact Projectivization.card_of_finrank_two K L.1 L.2.1

lemma symplecticPoint_sup_finrank
    {p q : SymplecticPoint K} (hpq : p ≠ q) :
    Module.finrank K
      (p.1 ⊔ q.1 : Submodule K (SymplecticVector K)) = 2 := by
  have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
  have hd : Disjoint p.1 q.1 :=
    (Submodule.isAtom_iff_finrank_eq_one.mpr p.2).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.mpr q.2) hne
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
  rw [hd.eq_bot, finrank_bot, p.2, q.2] at hrank
  omega

lemma symplecticLine_eq_of_points
    {p q : SymplecticPoint K} (hpq : p ≠ q)
    {L M : SymplecticLine K}
    (hpL : p.1 ≤ L.1) (hqL : q.1 ≤ L.1)
    (hpM : p.1 ≤ M.1) (hqM : q.1 ≤ M.1) : L = M := by
  have hsupL : p.1 ⊔ q.1 ≤ L.1 := sup_le hpL hqL
  have hsupM : p.1 ⊔ q.1 ≤ M.1 := sup_le hpM hqM
  have hL : p.1 ⊔ q.1 = L.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupL
      ((symplecticPoint_sup_finrank K hpq).trans L.2.1.symm)
  have hM : p.1 ⊔ q.1 = M.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupM
      ((symplecticPoint_sup_finrank K hpq).trans M.2.1.symm)
  exact Subtype.ext (hL.symm.trans hM)

lemma symplectic_isotropic_finrank_le_two
    (S : Submodule K (SymplecticVector K))
    (hS : ∀ u ∈ S, ∀ v ∈ S,
      standardSymplecticForm K u v = 0) :
    Module.finrank K S ≤ 2 := by
  have hle : S ≤ (standardSymplecticBilin K).orthogonal S := by
    intro x hx
    change ∀ y ∈ S, standardSymplecticForm K y x = 0
    intro y hy
    exact hS y hy x hx
  have hrank := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K)] at hrank
  have hambient : Module.finrank K (SymplecticVector K) = 4 := by
    simp [SymplecticVector]
  rw [hambient] at hrank
  omega

lemma symplectic_triangle_points_collinear
    {p q r : SymplecticPoint K} (hpq : p ≠ q)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    r.1 ≤ Lpq.1 := by
  let T : Submodule K (SymplecticVector K) :=
    (p.1 ⊔ q.1) ⊔ r.1
  have hiso : ∀ u ∈ T, ∀ v ∈ T,
      standardSymplecticForm K u v = 0 := by
    intro u hu v hv
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    obtain ⟨de, hde, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hde
    have had := Lpq.2.2 a (hpLpq ha) d (hpLpq hd)
    have hae := Lpq.2.2 a (hpLpq ha) e (hqLpq he)
    have haf := Lpr.2.2 a (hpLpr ha) f (hrLpr hf)
    have hbd := Lpq.2.2 b (hqLpq hb) d (hpLpq hd)
    have hbe := Lpq.2.2 b (hqLpq hb) e (hqLpq he)
    have hbf := Lqr.2.2 b (hqLqr hb) f (hrLqr hf)
    have hcd := Lpr.2.2 c (hrLpr hc) d (hpLpr hd)
    have hce := Lqr.2.2 c (hrLqr hc) e (hqLqr he)
    have hcf := Lpr.2.2 c (hrLpr hc) f (hrLpr hf)
    simp [standardSymplecticForm_add_left,
      standardSymplecticForm_add_right,
      had, hae, haf, hbd, hbe, hbf, hcd, hce, hcf]
  have hbound : Module.finrank K T ≤ 2 :=
    symplectic_isotropic_finrank_le_two K T hiso
  have hspan : p.1 ⊔ q.1 = T :=
    Submodule.eq_of_le_of_finrank_le le_sup_left
      (by simpa [symplecticPoint_sup_finrank K hpq] using hbound)
  exact (show r.1 ≤ T from le_sup_right).trans
    (hspan.symm ▸ sup_le hpLpq hqLpq)

lemma symplectic_triangle_lines_eq
    {p q r : SymplecticPoint K}
    (hpq : p ≠ q) (hqr : q ≠ r)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    Lpq = Lqr := by
  have hrLpq : r.1 ≤ Lpq.1 := symplectic_triangle_points_collinear K hpq
    hpLpq hqLpq hpLpr hrLpr hqLqr hrLqr
  exact symplecticLine_eq_of_points K hqr hqLpq hrLpq hqLqr hrLqr

abbrev QuadrangleVertex :=
  SymplecticPoint K ⊕ SymplecticLine K

def quadrangleIncidence :
    QuadrangleVertex K → QuadrangleVertex K → Prop
  | .inl point, .inr line => (point.1 : Submodule K _) ≤ line.1
  | _, _ => False

def symplecticQuadrangle : SimpleGraph (QuadrangleVertex K) :=
  SimpleGraph.fromRel (quadrangleIncidence K)

theorem symplecticQuadrangle_incidence_adj
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticQuadrangle K).Adj (.inl p) (.inr L) ↔ p.1 ≤ L.1 := by
  simp [symplecticQuadrangle, SimpleGraph.fromRel_adj, quadrangleIncidence]

theorem symplecticQuadrangle_adjacent_to_point
    {p : SymplecticPoint K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inl p) v) :
    ∃ L : SymplecticLine K, v = .inr L ∧ p.1 ≤ L.1 := by
  rcases v with q | L
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h
  · exact ⟨L, rfl, (symplecticQuadrangle_incidence_adj K p L).mp h⟩

theorem symplecticQuadrangle_adjacent_to_line
    {L : SymplecticLine K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inr L) v) :
    ∃ p : SymplecticPoint K, v = .inl p ∧ p.1 ≤ L.1 := by
  rcases v with p | M
  · exact ⟨p, rfl,
      (symplecticQuadrangle_incidence_adj K p L).mp h.symm⟩
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h

theorem symplecticQuadrangle_common_neighbor_unique
    {u v : QuadrangleVertex K} (huv : u ≠ v)
    {w z : QuadrangleVertex K}
    (huw : (symplecticQuadrangle K).Adj u w)
    (hvw : (symplecticQuadrangle K).Adj v w)
    (huz : (symplecticQuadrangle K).Adj u z)
    (hvz : (symplecticQuadrangle K).Adj v z) : w = z := by
  rcases u with p | L <;>
    rcases v with q | M <;>
    rcases w with r | R <;>
    rcases z with s | S <;>
    simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at huw hvw huz hvz
  · apply congrArg Sum.inr
    apply symplecticLine_eq_of_points K
      (fun hpq => huv (congrArg Sum.inl hpq))
    · exact huw
    · exact hvw
    · exact huz
    · exact hvz
  · apply congrArg Sum.inl
    by_contra hrs
    have hlines : L = M := symplecticLine_eq_of_points K hrs
      huw huz hvw hvz
    exact huv (congrArg Sum.inr hlines)

theorem symplecticQuadrangle_four_cycle_free :
    (SimpleGraph.cycleGraph 4).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h21 : (symplecticQuadrangle K).Adj (copy 2) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h03 : (symplecticQuadrangle K).Adj (copy 0) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h02 : copy 0 ≠ copy 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (copy.injective h)
  have h13 : copy 1 = copy 3 :=
    symplecticQuadrangle_common_neighbor_unique K h02 h01 h21 h03 h23
  exact (by decide : (1 : Fin 4) ≠ 3) (copy.injective h13)

theorem symplecticQuadrangle_six_cycle_free :
    (SimpleGraph.cycleGraph 6).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 0 1 by decide)
  have h12 : (symplecticQuadrangle K).Adj (copy 1) (copy 2) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 1 2 by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 2 3 by decide)
  have h34 : (symplecticQuadrangle K).Adj (copy 3) (copy 4) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 3 4 by decide)
  have h45 : (symplecticQuadrangle K).Adj (copy 4) (copy 5) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 4 5 by decide)
  have h50 : (symplecticQuadrangle K).Adj (copy 5) (copy 0) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 5 0 by decide)
  cases h0 : copy 0 with
  | inl p =>
      rw [h0] at h01 h50
      obtain ⟨L, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_point K h01
      rw [h1] at h12
      obtain ⟨q, h2, hqL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h12
      rw [h2] at h23
      obtain ⟨M, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h23
      rw [h3] at h34
      obtain ⟨r, h4, hrM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h34
      rw [h4] at h45
      obtain ⟨N, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h45
      rw [h5] at h50
      have hpN : p.1 ≤ N.1 :=
        (symplecticQuadrangle_incidence_adj K p N).mp h50.symm
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (0 : Fin 6) ≠ 2)
        apply copy.injective
        change copy 0 = copy 2
        rw [h0, h2, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (2 : Fin 6) ≠ 4)
        apply copy.injective
        change copy 2 = copy 4
        rw [h2, h4, heq]
      have hLM : L = M := symplectic_triangle_lines_eq K hpq hqr
        hpL hqL hpN hrN hqM hrM
      apply (by decide : (1 : Fin 6) ≠ 3)
      apply copy.injective
      change copy 1 = copy 3
      rw [h1, h3, hLM]
  | inr L =>
      rw [h0] at h01 h50
      obtain ⟨p, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h01
      rw [h1] at h12
      obtain ⟨M, h2, hpM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h12
      rw [h2] at h23
      obtain ⟨q, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h23
      rw [h3] at h34
      obtain ⟨N, h4, hqN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h34
      rw [h4] at h45
      obtain ⟨r, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_line K h45
      rw [h5] at h50
      have hrL : r.1 ≤ L.1 :=
        (symplecticQuadrangle_incidence_adj K r L).mp h50
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (1 : Fin 6) ≠ 3)
        apply copy.injective
        change copy 1 = copy 3
        rw [h1, h3, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (3 : Fin 6) ≠ 5)
        apply copy.injective
        change copy 3 = copy 5
        rw [h3, h5, heq]
      have hMN : M = N := symplectic_triangle_lines_eq K hpq hqr
        hpM hqM hpL hrL hqN hrN
      apply (by decide : (2 : Fin 6) ≠ 4)
      apply copy.injective
      change copy 2 = copy 4
      rw [h2, h4, hMN]

lemma symplecticPoint_card [Finite K] :
    Nat.card (SymplecticPoint K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  calc
    Nat.card (SymplecticPoint K) =
        Nat.card (Projectivization K (SymplecticVector K)) :=
      Nat.card_congr
        (Projectivization.equivSubmodule K (SymplecticVector K)).symm
    _ = ∑ i ∈ Finset.range 4, (Nat.card K) ^ i :=
      Projectivization.card_of_finrank K (SymplecticVector K) (by simp)
    _ = (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
      simp [Finset.sum_range_succ]
      ring

abbrev SymplecticIncidence :=
  {x : SymplecticPoint K × SymplecticLine K // x.1.1 ≤ x.2.1}

def symplecticIncidenceEquivSigmaPoints :
    SymplecticIncidence K ≃
      (Σ p : SymplecticPoint K, SymplecticLinesOnPoint K p) where
  toFun i := ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨p, ⟨L, h⟩⟩
    rfl

def symplecticIncidenceEquivSigmaLines :
    SymplecticIncidence K ≃
      (Σ L : SymplecticLine K, SymplecticPointsOnLine K L) where
  toFun i := ⟨i.1.2, ⟨i.1.1, i.2⟩⟩
  invFun s := ⟨(s.2.1, s.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨L, ⟨p, h⟩⟩
    rfl

lemma symplecticIncidence_card_by_points [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ p : SymplecticPoint K,
          SymplecticLinesOnPoint K p) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaPoints K)
    _ = ∑ p : SymplecticPoint K,
          Nat.card (SymplecticLinesOnPoint K p) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
      simp_rw [symplecticLinesOnPoint_card]
      simp [Nat.card_eq_fintype_card]

lemma symplecticIncidence_card_by_lines [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ L : SymplecticLine K,
          SymplecticPointsOnLine K L) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaLines K)
    _ = ∑ L : SymplecticLine K,
          Nat.card (SymplecticPointsOnLine K L) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
      simp_rw [symplecticPointsOnLine_card]
      simp [Nat.card_eq_fintype_card]

lemma symplecticLine_card [Finite K] :
    Nat.card (SymplecticLine K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  have hcounts :
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) =
        Nat.card (SymplecticLine K) * (Nat.card K + 1) :=
    (symplecticIncidence_card_by_points K).symm.trans
      (symplecticIncidence_card_by_lines K)
  have hline : Nat.card (SymplecticPoint K) =
      Nat.card (SymplecticLine K) :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hcounts
  rw [← hline, symplecticPoint_card]

lemma symplecticIncidence_card [Finite K] :
    Nat.card (SymplecticIncidence K) =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [symplecticIncidence_card_by_points, symplecticPoint_card]
  ring

theorem symplecticQuadrangle_vertex_card [Finite K] :
    Nat.card (QuadrangleVertex K) =
      2 * (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  rw [Nat.card_sum, symplecticPoint_card, symplecticLine_card]
  ring

def symplecticIncidenceToEdge :
    SymplecticIncidence K → (symplecticQuadrangle K).edgeSet :=
  fun i =>
    ⟨s(Sum.inl i.1.1, Sum.inr i.1.2),
      (symplecticQuadrangle_incidence_adj K i.1.1 i.1.2).mpr i.2⟩

lemma symplecticIncidenceToEdge_injective :
    Function.Injective (symplecticIncidenceToEdge K) := by
  intro i j h
  have hedges := congrArg Subtype.val h
  change s(Sum.inl i.1.1, Sum.inr i.1.2) =
    s(Sum.inl j.1.1, Sum.inr j.1.2) at hedges
  rcases Sym2.eq_iff.mp hedges with ⟨hp, hL⟩ | ⟨hbad, _⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact Sum.inl_injective hp
    · exact Sum.inr_injective hL
  · cases hbad

lemma symplecticIncidenceToEdge_surjective :
    Function.Surjective (symplecticIncidenceToEdge K) := by
  intro e
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.1
  change s(u, v) = e.1 at huv
  have hadj : (symplecticQuadrangle K).Adj u v := by
    apply (symplecticQuadrangle K).mem_edgeSet.mp
    rw [huv]
    exact e.2
  rcases u with p | L <;> rcases v with q | M
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at hadj
  · refine ⟨⟨(p, M),
        (symplecticQuadrangle_incidence_adj K p M).mp hadj⟩, ?_⟩
    apply Subtype.ext
    exact huv
  · refine ⟨⟨(q, L),
        (symplecticQuadrangle_incidence_adj K q L).mp hadj.symm⟩, ?_⟩
    apply Subtype.ext
    exact Sym2.eq_swap.trans huv
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at hadj

noncomputable def symplecticIncidenceEquivEdge :
    SymplecticIncidence K ≃ (symplecticQuadrangle K).edgeSet :=
  Equiv.ofBijective (symplecticIncidenceToEdge K)
    ⟨symplecticIncidenceToEdge_injective K,
      symplecticIncidenceToEdge_surjective K⟩

theorem symplecticQuadrangle_edge_card [Finite K] :
    Nat.card (symplecticQuadrangle K).edgeSet =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [← Nat.card_congr (symplecticIncidenceEquivEdge K),
    symplecticIncidence_card]

end SymplecticGeometry

section NumericalParameters

def quadrangleVertexCount (q : ℕ) : ℕ :=
  2 * (q + 1) * (q ^ 2 + 1)

def quadrangleEdgeCount (q : ℕ) : ℕ :=
  (q + 1) ^ 2 * (q ^ 2 + 1)

theorem quadrangle_density_certificate (q : ℕ) :
    (quadrangleVertexCount q : ℝ) ^ 4 ≤
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 := by
  have hnonneg :
      0 ≤ 32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
        ((q : ℝ) ^ 2 + 1) ^ 3 := by
    positivity
  have hidentity :
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 -
          (quadrangleVertexCount q : ℝ) ^ 4 =
        32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
          ((q : ℝ) ^ 2 + 1) ^ 3 := by
    simp only [quadrangleVertexCount, quadrangleEdgeCount,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  linarith

theorem quadrangle_rpow_density (q : ℕ) :
    (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  apply ((by decide : Odd 3).strictMono_pow.le_iff_le).mp
  have hcubed :
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (quadrangleVertexCount q : ℝ) ^ 4 / 16 := by
    rw [mul_pow,
      ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))
        (-((4 : ℝ) / 3)) 3,
      ← Real.rpow_mul_natCast
        (by exact_mod_cast (Nat.zero_le (quadrangleVertexCount q)))
        ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    ring
  rw [hcubed]
  nlinarith [quadrangle_density_certificate q]

theorem quadrangleVertexCount_mul_le
    (q t : ℕ) (ht : 1 ≤ t) :
    quadrangleVertexCount (t * q) ≤
      t ^ 3 * quadrangleVertexCount q := by
  have hfirst : t * q + 1 ≤ t * (q + 1) := by
    nlinarith
  have hsecond : (t * q) ^ 2 + 1 ≤ t ^ 2 * (q ^ 2 + 1) := by
    nlinarith [sq_nonneg (t - 1)]
  unfold quadrangleVertexCount
  calc
    2 * (t * q + 1) * ((t * q) ^ 2 + 1) ≤
        2 * (t * (q + 1)) * (t ^ 2 * (q ^ 2 + 1)) := by
      gcongr
    _ = t ^ 3 * (2 * (q + 1) * (q ^ 2 + 1)) := by
      ring

end NumericalParameters

end Geometry

noncomputable section Cyclicity

open Finset SimpleGraph

def thetaCycleVertex : Fin 8 → SubdivisionVertex 2 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]

def thetaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) thetaGraph := by
  refine ⟨⟨thetaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [thetaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide

def jThetaVertex (copy : Fin 2) : SubdivisionVertex 2 → JVertex
  | .inl (.inl base) => .inl (.inl (jBase copy base))
  | .inl (.inr center) => .inl (.inr (copy, center))
  | .inr (base, center) => .inr (.inl (copy, (base, center)))

def jThetaCopy (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph jTemplate := by
  refine ⟨⟨jThetaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 2) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · left
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · right
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
  · fin_cases copy <;> decide

lemma jThetaVertex_mem (copy : Fin 2)
    (v : SubdivisionVertex 2) :
    InJCopy copy (jThetaVertex copy v) := by
  rcases v with (base | center) | pair
  · exact ⟨base, rfl⟩
  · simp [InJCopy, jThetaVertex]
  · simp [InJCopy, jThetaVertex]

def gammaCycleVertex : Fin 8 → SubdivisionVertex 3 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]

def gammaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) gammaGraph := by
  refine ⟨⟨gammaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [gammaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide

def kGammaVertex (copy : Fin 2)
    (v : SubdivisionVertex 3) : KVertex := (copy, v)

def kGammaCopy (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph kTemplate := by
  refine ⟨⟨kGammaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 3) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · left
        exact Or.inl ⟨rfl, hforward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · right
        exact Or.inl ⟨rfl, hbackward⟩
  · intro u v h
    exact congrArg Prod.snd h

def copyToQuotient {α β : Type*}
    (source : SimpleGraph β) (target : SimpleGraph α)
    (f : α → α) (copy : SimpleGraph.Copy source target)
    (hinj : Function.Injective (fun v : β => f (copy v))) :
    SimpleGraph.Copy source (quotientGraph target f) := by
  refine ⟨⟨fun v => ⟨f (copy v), ⟨copy v, rfl⟩⟩, ?_⟩, ?_⟩
  · intro u v hadj
    apply (SimpleGraph.fromRel_adj
      (quotientRelation target f) _ _).mpr
    constructor
    · intro heq
      exact hadj.ne (hinj (congrArg Subtype.val heq))
    · left
      exact ⟨copy u, copy v, rfl, rfl, copy.toHom.map_rel hadj⟩
  · intro u v heq
    exact hinj (congrArg Subtype.val heq)

lemma not_acyclic_of_eight_cycle_copy
    {α : Type*} {graph : SimpleGraph α}
    (copy : SimpleGraph.Copy (SimpleGraph.cycleGraph 8) graph) :
    ¬ graph.IsAcyclic := by
  intro hacyclic
  have hcycle : (SimpleGraph.cycleGraph 8).IsAcyclic :=
    hacyclic.comap copy.toHom copy.injective
  exact hcycle (SimpleGraph.cycleGraph.cycle 5)
    (SimpleGraph.cycleGraph.isCycle_cycle)

lemma encodeFiniteGraph_not_acyclic
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by
  intro hencoded
  apply h
  exact (SimpleGraph.Iso.map (Fintype.equivFin α) graph).isAcyclic_iff.mpr
    hencoded

lemma jTheta_quotient_injective
    {f : JVertex → JVertex} (hf : JAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 2 =>
      f (jThetaVertex copy v)) := by
  intro u v heq
  have htemplate : jThetaVertex copy u = jThetaVertex copy v :=
    hf.2.2 copy (jThetaVertex_mem copy u)
      (jThetaVertex_mem copy v) heq
  exact (jThetaCopy copy).injective htemplate

theorem jQuotient_not_acyclic
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient thetaGraph jTemplate f (jThetaCopy 0)
    (jTheta_quotient_injective hf 0)).comp thetaCycleCopy

lemma kGamma_quotient_injective
    {f : KVertex → KVertex} (hf : KAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 3 =>
      f (kGammaVertex copy v)) := by
  intro u v heq
  have htemplate : kGammaVertex copy u = kGammaVertex copy v :=
    hf.2 copy (show (kGammaVertex copy u).1 = copy from rfl)
      (show (kGammaVertex copy v).1 = copy from rfl) heq
  exact (kGammaCopy copy).injective htemplate

theorem kQuotient_not_acyclic
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient gammaGraph kTemplate f (kGammaCopy 0)
    (kGamma_quotient_injective hf 0)).comp gammaCycleCopy

theorem four_cycle_not_acyclic :
    ¬ (finiteCycle 4).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 1)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem six_cycle_not_acyclic :
    ¬ (finiteCycle 6).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 3)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem proposedFamily_isCyclic : IsCyclicFamily proposedFamily :=
  proposedFamily_induction (P := fun graph => ¬ graph.graph.IsAcyclic)
    four_cycle_not_acyclic six_cycle_not_acyclic
    (fun _ hf => jQuotient_not_acyclic hf)
    (fun _ hf => kQuotient_not_acyclic hf)

end Cyclicity

noncomputable section CharacteristicAvoidance

open SimpleGraph

section PointClass

variable (K : Type*) [Field K]

def SymplecticPointRelated (p q : SymplecticPoint K) : Prop :=
  p ≠ q ∧ ∃ L : SymplecticLine K, p.1 ≤ L.1 ∧ q.1 ≤ L.1

lemma symplecticPointRelated_symm
    {p q : SymplecticPoint K}
    (h : SymplecticPointRelated K p q) :
    SymplecticPointRelated K q p := by
  obtain ⟨hpq, L, hpL, hqL⟩ := h
  exact ⟨Ne.symm hpq, L, hqL, hpL⟩

lemma symplecticPointRelated_iff_orthogonal
    (p q : SymplecticPoint K) :
    SymplecticPointRelated K p q ↔
      p ≠ q ∧ p.1 ≤ SymplecticPointOrthogonal K q := by
  constructor
  · rintro ⟨hpq, L, hpL, hqL⟩
    refine ⟨hpq, ?_⟩
    intro x hx
    change ∀ y ∈ q.1, standardSymplecticForm K y x = 0
    intro y hy
    exact L.2.2 y (hqL hy) x (hpL hx)
  · rintro ⟨hpq, hporth⟩
    let U : Submodule K (SymplecticVector K) := p.1 ⊔ q.1
    have hdim : Module.finrank K U = 2 :=
      symplecticPoint_sup_finrank K hpq
    have hqU : q.1 ≤ U := le_sup_right
    have hUorth : U ≤ SymplecticPointOrthogonal K q :=
      sup_le hporth (symplecticPoint_le_orthogonal K q)
    exact ⟨hpq,
      ⟨U, hdim, symplectic_two_plane_isotropic K hdim hqU hUorth⟩,
      le_sup_left, le_sup_right⟩

lemma symplecticPointRelated_of_quadrangle_common_neighbor
    {p q : SymplecticPoint K}
    (hpq : p ≠ q) {v : QuadrangleVertex K}
    (hpv : (symplecticQuadrangle K).Adj (.inl p) v)
    (hqv : (symplecticQuadrangle K).Adj (.inl q) v) :
    SymplecticPointRelated K p q := by
  obtain ⟨L, hv, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hpv
  rw [hv] at hqv
  exact ⟨hpq, L, hpL,
    (symplecticQuadrangle_incidence_adj K q L).mp hqv⟩

lemma subdivisionGraph_base_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma subdivisionGraph_center_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma subdivisionPoint_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    ∃ L : SymplecticLine K,
      copy (.inr (base, center)) = .inr L ∧
        p.1 ≤ L.1 ∧ c.1 ≤ L.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨L, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K c L).mp hcenteradj⟩

lemma subdivisionPoint_center_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ c : SymplecticPoint K,
      copy (.inl (.inr center)) = .inl c := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨c, hc, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj.symm
  exact ⟨c, hc⟩

lemma subdivisionPoint_base_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ q : SymplecticPoint K,
      copy (.inl (.inl otherBase)) = .inl q := by
  obtain ⟨c, hc⟩ := subdivisionPoint_center_of_point_base K
    copy (center := center) hbase
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (otherBase, center))) at hcenteradj
  rw [hc] at hcenteradj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj
  have hotheradj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl otherBase)))
    (copy (.inr (otherBase, center))) at hotheradj
  rw [hpair] at hotheradj
  obtain ⟨q, hq, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hotheradj.symm
  exact ⟨q, hq⟩

lemma subdivisionPoint_base_center_related
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    SymplecticPointRelated K p c := by
  obtain ⟨L, _, hpL, hcL⟩ :=
    subdivisionPoint_pair_incidence K copy hbase hcenter
  refine ⟨?_, L, hpL, hcL⟩
  intro hpc
  have hvertex :
      (Sum.inl (Sum.inl base) : SubdivisionVertex k) =
        .inl (.inr center) := by
    apply copy.injective
    change copy (.inl (.inl base)) =
      copy (.inl (.inr center))
    rw [hbase, hcenter, hpc]
  cases hvertex

lemma subdivisionPoint_bases_unrelated
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (p : Fin 3 → SymplecticPoint K)
    (c : Fin k → SymplecticPoint K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inl (c center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    ¬ SymplecticPointRelated K (p i) (p j) := by
  obtain ⟨Li, hi_pair, hpiLi, hcLi⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase i)
      (hcenter center)
  obtain ⟨Lj, hj_pair, hpjLj, hcLj⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase j)
      (hcenter center)
  have hic : SymplecticPointRelated K (p i) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase i)
      (hcenter center)
  have hjc : SymplecticPointRelated K (p j) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase j)
      (hcenter center)
  rintro ⟨_, Lij, hpiLij, hpjLij⟩
  have hlines : Li = Lj :=
    symplectic_triangle_lines_eq K hic.1
      (symplecticPointRelated_symm K hjc).1
      hpiLi hcLi hpiLij hpjLij hcLj hpjLj
  have hpair :
      copy (.inr (i, center)) = copy (.inr (j, center)) := by
    rw [hi_pair, hj_pair, hlines]
  have hsource :
      (Sum.inr (i, center) : SubdivisionVertex k) =
        .inr (j, center) := copy.injective hpair
  exact hij (congrArg Prod.fst (Sum.inr.inj hsource))

lemma symplecticPointSpan_orthogonal_finrank
    {y z : SymplecticPoint K} (hyz : y ≠ z) :
    Module.finrank K
      ((standardSymplecticBilin K).orthogonal
        (y.1 ⊔ z.1)) = 2 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K),
    symplecticPoint_sup_finrank K hyz]
  simp [SymplecticVector]

lemma symplecticPoint_centers_span_orthogonal
    {y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    c.1 ⊔ d.1 =
      (standardSymplecticBilin K).orthogonal (y.1 ⊔ z.1) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hcy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hcz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hdy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hdz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
  · rw [symplecticPoint_sup_finrank K hcd,
      symplecticPointSpan_orthogonal_finrank K hyz]

lemma symplecticPoint_mem_span_of_two_centers
    {x y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcx : c.1 ≤ SymplecticPointOrthogonal K x)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdx : d.1 ≤ SymplecticPointOrthogonal K x)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    x.1 ≤ y.1 ⊔ z.1 := by
  have hcenters := symplecticPoint_centers_span_orthogonal K
    hyz hcd hcy hcz hdy hdz
  have hxorth :
      x.1 ≤ (standardSymplecticBilin K).orthogonal (c.1 ⊔ d.1) := by
    intro w hw
    change ∀ u ∈ c.1 ⊔ d.1,
      standardSymplecticForm K u w = 0
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [standardSymplecticForm_add_left]
    have haorth : standardSymplecticForm K a w = 0 := by
      have h := hcx ha w hw
      change standardSymplecticForm K w a = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    have hborth : standardSymplecticForm K b w = 0 := by
      have h := hdx hb w hw
      change standardSymplecticForm K w b = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    rw [haorth, hborth, add_zero]
  rw [hcenters,
    LinearMap.BilinForm.orthogonal_orthogonal
      (standardSymplecticBilin_nondegenerate K)
      (standardSymplecticBilin_isAlt K).isRefl] at hxorth
  exact hxorth

theorem symplecticPoint_point_class_avoidance
    {x x' y z c d c' d' : SymplecticPoint K}
    (hyz : y ≠ z)
    (hyz_unrelated : ¬ SymplecticPointRelated K y z)
    (hxx' : x ≠ x')
    (hcd : c ≠ d) (hc'd' : c' ≠ d')
    (hcx : SymplecticPointRelated K c x)
    (hcy : SymplecticPointRelated K c y)
    (hcz : SymplecticPointRelated K c z)
    (hdx : SymplecticPointRelated K d x)
    (hdy : SymplecticPointRelated K d y)
    (hdz : SymplecticPointRelated K d z)
    (hc'x' : SymplecticPointRelated K c' x')
    (hc'y : SymplecticPointRelated K c' y)
    (hc'z : SymplecticPointRelated K c' z)
    (hd'x' : SymplecticPointRelated K d' x')
    (hd'y : SymplecticPointRelated K d' y)
    (hd'z : SymplecticPointRelated K d' z) :
    ¬ SymplecticPointRelated K x x' := by
  have hxspan : x.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hcd
      ((symplecticPointRelated_iff_orthogonal K c x).mp hcx).2
      ((symplecticPointRelated_iff_orthogonal K c y).mp hcy).2
      ((symplecticPointRelated_iff_orthogonal K c z).mp hcz).2
      ((symplecticPointRelated_iff_orthogonal K d x).mp hdx).2
      ((symplecticPointRelated_iff_orthogonal K d y).mp hdy).2
      ((symplecticPointRelated_iff_orthogonal K d z).mp hdz).2
  have hx'span : x'.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hc'd'
      ((symplecticPointRelated_iff_orthogonal K c' x').mp hc'x').2
      ((symplecticPointRelated_iff_orthogonal K c' y).mp hc'y).2
      ((symplecticPointRelated_iff_orthogonal K c' z).mp hc'z).2
      ((symplecticPointRelated_iff_orthogonal K d' x').mp hd'x').2
      ((symplecticPointRelated_iff_orthogonal K d' y).mp hd'y).2
      ((symplecticPointRelated_iff_orthogonal K d' z).mp hd'z).2
  intro hrelated
  obtain ⟨_, L, hxL, hx'L⟩ := hrelated
  have hspan : x.1 ⊔ x'.1 = y.1 ⊔ z.1 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hxspan hx'span)
    rw [symplecticPoint_sup_finrank K hxx',
      symplecticPoint_sup_finrank K hyz]
  have hyzL : y.1 ⊔ z.1 ≤ L.1 := by
    rw [← hspan]
    exact sup_le hxL hx'L
  exact hyz_unrelated
    ⟨hyz, L, le_sup_left.trans hyzL, le_sup_right.trans hyzL⟩

def colorRespectingQuotientProjectionHom
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    graph →g quotientGraph graph f := by
  refine ⟨fun v => ⟨f v, v, rfl⟩, ?_⟩
  intro u v hadj
  apply (SimpleGraph.fromRel_adj
    (quotientRelation graph f)
    (⟨f u, u, rfl⟩ : Set.range f)
    (⟨f v, v, rfl⟩ : Set.range f)).mpr
  constructor
  · intro heq
    exact hproper hadj
      (hf u v (congrArg Subtype.val heq))
  · left
    exact ⟨u, v, rfl, rfl, hadj⟩

lemma jTemplate_adj_color_ne
    {u v : JVertex} (h : jTemplate.Adj u v) :
    jColor u ≠ jColor v := by
  rcases u with (u | u) | (u | u) <;>
    rcases v with (v | v) | (v | v) <;>
    simp_all [jTemplate, SimpleGraph.fromRel_adj,
      jTemplateRelation, jColor]

lemma kTemplate_adj_color_ne
    {u v : KVertex} (h : kTemplate.Adj u v) :
    kColor u ≠ kColor v := by
  rcases u with ⟨u, (u | u) | u⟩ <;>
    rcases v with ⟨v, (v | v) | v⟩ <;>
    fin_cases u <;> fin_cases v <;>
    simp_all [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kColor, subdivisionColor,
      subdivisionRelation, kSpecifiedCenter]
  all_goals aesop

def jQuotientProjectionHom
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    jTemplate →g quotientGraph jTemplate f :=
  colorRespectingQuotientProjectionHom jTemplate jColor
    (fun _ _ h => jTemplate_adj_color_ne h) f hf.1

def kQuotientProjectionHom
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    kTemplate →g quotientGraph kTemplate f :=
  colorRespectingQuotientProjectionHom kTemplate kColor
    (fun _ _ h => kTemplate_adj_color_ne h) f hf.1

def jThetaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : jTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph host := by
  refine ⟨hom.comp (jThetaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (jThetaVertex copy u) =
    hom (jThetaVertex copy v) at huv
  apply (jThetaCopy copy).injective
  exact hcopies copy (jThetaVertex_mem copy u)
    (jThetaVertex_mem copy v) huv

theorem symplecticQuadrangle_no_point_jTemplate
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (p : Fin 4 → SymplecticPoint K)
    (c : Fin 2 → Fin 2 → SymplecticPoint K)
    (hbase : ∀ base : Fin 4,
      hom (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ (copy center : Fin 2),
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center)) : False := by
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) (base : Fin 3) :
      θ copy (.inl (.inl base)) =
        .inl (p (jBase copy base)) := by
    change hom (jThetaVertex copy (.inl (.inl base))) = _
    simpa [jThetaVertex] using hbase (jBase copy base)
  have hθcenter (copy center : Fin 2) :
      θ copy (.inl (.inr center)) =
        .inl (c copy center) := by
    change hom (jThetaVertex copy (.inl (.inr center))) = _
    simpa [jThetaVertex] using hcenter copy center
  have hcenters_inj (copy : Fin 2) :
      Function.Injective (c copy) := by
    intro i j hij
    have himage :
        θ copy (.inl (.inr i)) =
          θ copy (.inl (.inr j)) := by
      rw [hθcenter copy i, hθcenter copy j, hij]
    have hsource :
        (Sum.inl (Sum.inr i) : SubdivisionVertex 2) =
          .inl (.inr j) := (θ copy).injective himage
    exact Sum.inr.inj (Sum.inl.inj hsource)
  have hpoints_inj : Function.Injective p := by
    intro i j hij
    apply hbase_inj
    change hom (.inl (.inl i)) = hom (.inl (.inl j))
    rw [hbase i, hbase j, hij]
  have hyz : p 2 ≠ p 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (hpoints_inj h)
  have hxx' : p 0 ≠ p 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hpoints_inj h)
  have hyz_unrelated :
      ¬ SymplecticPointRelated K (p 2) (p 3) := by
    have h := subdivisionPoint_bases_unrelated K (θ 0)
      (fun base => p (jBase 0 base)) (c 0)
      (hθbase 0) (hθcenter 0)
      (by decide : (1 : Fin 3) ≠ 2) 0
    simpa [jBase] using h
  have hrelated (copy : Fin 2) (base : Fin 3)
      (center : Fin 2) :
      SymplecticPointRelated K
        (c copy center) (p (jBase copy base)) :=
    symplecticPointRelated_symm K
      (subdivisionPoint_base_center_related K
        (θ copy) (hθbase copy base) (hθcenter copy center))
  have hcd : c 0 0 ≠ c 0 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 0 h)
  have hc'd' : c 1 0 ≠ c 1 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 1 h)
  have havoid := symplecticPoint_point_class_avoidance K
    (x := p 0) (x' := p 1) (y := p 2) (z := p 3)
    (c := c 0 0) (d := c 0 1)
    (c' := c 1 0) (d' := c 1 1)
    hyz hyz_unrelated hxx' hcd hc'd'
    (by simpa [jBase] using hrelated 0 0 0)
    (by simpa [jBase] using hrelated 0 1 0)
    (by simpa [jBase] using hrelated 0 2 0)
    (by simpa [jBase] using hrelated 0 0 1)
    (by simpa [jBase] using hrelated 0 1 1)
    (by simpa [jBase] using hrelated 0 2 1)
    (by simpa [jBase] using hrelated 1 0 0)
    (by simpa [jBase] using hrelated 1 1 0)
    (by simpa [jBase] using hrelated 1 2 0)
    (by simpa [jBase] using hrelated 1 0 1)
    (by simpa [jBase] using hrelated 1 1 1)
    (by simpa [jBase] using hrelated 1 2 1)
  have hjoin0 : jTemplate.Adj
      (.inl (.inl (0 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoin1 : jTemplate.Adj
      (.inl (.inl (1 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hleft := hom.map_rel hjoin0
  have hright := hom.map_rel hjoin1
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hleft
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hright
  rw [hbase 0] at hleft
  rw [hbase 1] at hright
  exact havoid
    (symplecticPointRelated_of_quadrangle_common_neighbor K
      hxx' hleft hright)

theorem symplecticQuadrangle_no_point_jTemplate_of_bases
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hpoint : ∀ base : Fin 4,
      ∃ p : SymplecticPoint K,
        hom (.inl (.inl base)) = .inl p) : False := by
  classical
  let p : Fin 4 → SymplecticPoint K :=
    fun base => Classical.choose (hpoint base)
  have hp (base : Fin 4) :
      hom (.inl (.inl base)) = .inl (p base) :=
    Classical.choose_spec (hpoint base)
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) :
      θ copy (.inl (.inl (0 : Fin 3))) =
        .inl (p (jBase copy 0)) := by
    change hom (jThetaVertex copy (.inl (.inl 0))) = _
    simpa [jThetaVertex] using hp (jBase copy 0)
  have hcenter_exists (copy center : Fin 2) :
      ∃ q : SymplecticPoint K,
        hom (.inl (.inr (copy, center))) = .inl q := by
    have h := subdivisionPoint_center_of_point_base K
      (θ copy) (center := center) (hθbase copy)
    change ∃ q : SymplecticPoint K,
      hom (jThetaVertex copy (.inl (.inr center))) = .inl q at h
    simpa [jThetaVertex] using h
  let c : Fin 2 → Fin 2 → SymplecticPoint K :=
    fun copy center => Classical.choose (hcenter_exists copy center)
  have hc (copy center : Fin 2) :
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center) :=
    Classical.choose_spec (hcenter_exists copy center)
  exact symplecticQuadrangle_no_point_jTemplate K hom
    hbase_inj hcopies p c hp hc

theorem symplecticQuadrangle_no_point_jTemplate_of_first_base
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hfirst : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (0 : Fin 4))) = .inl p) : False := by
  obtain ⟨p₀, hp₀⟩ := hfirst
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hx : θ 0 (.inl (.inl (0 : Fin 3))) = .inl p₀ := by
    change hom (jThetaVertex 0 (.inl (.inl 0))) = _
    simpa [jThetaVertex, jBase] using hp₀
  have hy : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (2 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (1 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  have hz : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (3 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (2 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  obtain ⟨py, hpy⟩ := hy
  have hy' : θ 1 (.inl (.inl (1 : Fin 3))) = .inl py := by
    change hom (jThetaVertex 1 (.inl (.inl 1))) = _
    simpa [jThetaVertex, jBase] using hpy
  have hx' : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (1 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 1)
      (otherBase := (0 : Fin 3)) 0 hy'
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  apply symplecticQuadrangle_no_point_jTemplate_of_bases K
    hom hbase_inj hcopies
  intro base
  fin_cases base
  · exact ⟨p₀, hp₀⟩
  · exact hx'
  · exact ⟨py, hpy⟩
  · exact hz

theorem symplecticQuadrangle_jTemplate_first_base_is_line
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) :
    ∃ L : SymplecticLine K,
      hom (.inl (.inl (0 : Fin 4))) = .inr L := by
  cases h : hom (.inl (.inl (0 : Fin 4))) with
  | inl p =>
      exact False.elim
        (symplecticQuadrangle_no_point_jTemplate_of_first_base K
          hom hbase_inj hcopies ⟨p, h⟩)
  | inr L => exact ⟨L, rfl⟩

def kGammaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : kTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy})
    (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph host := by
  refine ⟨hom.comp (kGammaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (kGammaVertex copy u) =
    hom (kGammaVertex copy v) at huv
  apply (kGammaCopy copy).injective
  exact hcopies copy (show (kGammaVertex copy u).1 = copy from rfl)
    (show (kGammaVertex copy v).1 = copy from rfl) huv

theorem symplecticQuadrangle_kTemplate_has_line_gamma
    (hom : kTemplate →g symplecticQuadrangle K)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) :
    ∃ (i : Fin 2) (L : SymplecticLine K),
      (kGammaHomCopy hom hcopies i) kSpecifiedCenter = .inr L := by
  have hjoin : kTemplate.Adj
      ((0 : Fin 2), kSpecifiedCenter)
      ((1 : Fin 2), kSpecifiedCenter) := by
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kSpecifiedCenter]
  have hadj := hom.map_rel hjoin
  change (symplecticQuadrangle K).Adj
    (hom ((0 : Fin 2), kSpecifiedCenter))
    (hom ((1 : Fin 2), kSpecifiedCenter)) at hadj
  cases hzero : hom ((0 : Fin 2), kSpecifiedCenter) with
  | inl p =>
      rw [hzero] at hadj
      obtain ⟨L, hL, _⟩ :=
        symplecticQuadrangle_adjacent_to_point K hadj
      refine ⟨1, L, ?_⟩
      change hom (kGammaVertex 1 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hL
  | inr L =>
      refine ⟨0, L, ?_⟩
      change hom (kGammaVertex 0 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hzero

end PointClass

end CharacteristicAvoidance

noncomputable section SubdivisionLineExtraction

open SimpleGraph

variable (K : Type*) [Field K]

lemma subdivisionLine_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L C : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L)
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ p : SymplecticPoint K,
      copy (.inr (base, center)) = .inl p ∧
        p.1 ≤ L.1 ∧ p.1 ≤ C.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨p, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K p C).mp hcenteradj.symm⟩

lemma subdivisionLine_center_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ C : SymplecticLine K,
      copy (.inl (.inr center)) = .inr C := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨C, hC, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj.symm
  exact ⟨C, hC⟩

lemma subdivisionLine_base_of_line_center
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {C : SymplecticLine K}
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ L : SymplecticLine K,
      copy (.inl (.inl base)) = .inr L := by
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter] at hcenteradj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hpair] at hbaseadj
  obtain ⟨L, hL, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj.symm
  exact ⟨L, hL⟩

lemma subdivisionLine_base_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ M : SymplecticLine K,
      copy (.inl (.inl otherBase)) = .inr M := by
  obtain ⟨C, hC⟩ := subdivisionLine_center_of_line_base K
    copy (center := center) hbase
  exact subdivisionLine_base_of_line_center K
    copy (base := otherBase) hC

lemma subdivisionLine_centers_injective
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply copy.injective
  change copy (.inl (.inr i)) = copy (.inl (.inr j))
  rw [hcenter i, hcenter j, hij]

lemma subdivisionLine_bases_disjoint
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (L : Fin 3 → SymplecticLine K)
    (C : Fin k → SymplecticLine K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inr (L base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    Disjoint (L i).1 (L j).1 := by
  apply Submodule.disjoint_def.mpr
  intro x hxi hxj
  by_contra hx
  let p : SymplecticPoint K :=
    ⟨K ∙ x, finrank_span_singleton hx⟩
  have hpLi : p.1 ≤ (L i).1 :=
    (Submodule.span_le).mpr (by simpa using hxi)
  have hpLj : p.1 ≤ (L j).1 :=
    (Submodule.span_le).mpr (by simpa using hxj)
  obtain ⟨pi, hpairi, hpiLi, hpiC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase i) (hcenter center)
  obtain ⟨pj, hpairj, hpjLj, hpjC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase j) (hcenter center)
  have hpipj : pi ≠ pj := by
    intro heq
    apply hij
    have hsource :
        (Sum.inr (i, center) : SubdivisionVertex k) =
          .inr (j, center) := by
      apply copy.injective
      change copy (.inr (i, center)) =
        copy (.inr (j, center))
      rw [hpairi, hpairj, heq]
    exact congrArg Prod.fst (Sum.inr.inj hsource)
  have hcenterNeBase (base : Fin 3) : C center ≠ L base := by
    intro heq
    have hsource :
        (Sum.inl (Sum.inr center) : SubdivisionVertex k) =
          .inl (.inl base) := by
      apply copy.injective
      change copy (.inl (.inr center)) =
        copy (.inl (.inl base))
      rw [hcenter center, hbase base, heq]
    cases Sum.inl.inj hsource
  have hpjp : pj ≠ p := by
    intro heq
    have hpjLi : pj.1 ≤ (L i).1 := by
      simpa only [heq] using hpLi
    have hline : C center = L i :=
      symplecticLine_eq_of_points K hpipj
        hpiC hpjC hpiLi hpjLi
    exact hcenterNeBase i hline
  have hline : C center = L j :=
    symplectic_triangle_lines_eq K hpipj hpjp
      hpiC hpjC hpiLi hpLi hpjLj hpLj
  exact hcenterNeBase j hline

end SubdivisionLineExtraction

noncomputable section Padding

open SimpleGraph

def GraphHasNoIsolated {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ u : V, ∃ v : V, graph.Adj u v

lemma free_map_of_no_isolated
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by
  classical
  rintro ⟨copy⟩
  have hpreimage (u : U) :
      ∃ v : V, embedding v = copy u := by
    obtain ⟨w, huw⟩ := hneighbors u
    have hadj := copy.toHom.map_rel huw
    change (host.map embedding).Adj (copy u) (copy w) at hadj
    obtain ⟨v, _, _, hv, _⟩ :=
      (SimpleGraph.map_adj embedding host _ _).mp hadj
    exact ⟨v, hv⟩
  let lift : U → V := fun u => Classical.choose (hpreimage u)
  have hlift (u : U) : embedding (lift u) = copy u :=
    Classical.choose_spec (hpreimage u)
  apply hfree
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hadj := copy.toHom.map_rel huv
    change (host.map embedding).Adj (copy u) (copy v) at hadj
    rw [← hlift u, ← hlift v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    change lift u = lift v at huv
    apply copy.injective
    change copy u = copy v
    rw [← hlift u, ← hlift v]
    exact congrArg embedding huv

lemma extremalNumber_monotone_of_no_isolated
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.extremalNumber m forbidden ≤
      SimpleGraph.extremalNumber n forbidden := by
  classical
  have hbound :
      SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
        SimpleGraph.extremalNumber n forbidden := by
    apply (SimpleGraph.extremalNumber_le_iff
      (V := Fin m) forbidden
      (SimpleGraph.extremalNumber n forbidden)).mpr
    intro host _ hfree
    let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
    have hpadded : forbidden.Free (host.map embedding) :=
      free_map_of_no_isolated forbidden hneighbors embedding hfree
    calc
      host.edgeFinset.card =
          (host.map embedding).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using
          (SimpleGraph.card_edgeFinset_map embedding host).symm
      _ ≤ SimpleGraph.extremalNumber n forbidden := by
        simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
  simpa using hbound

lemma cycleGraph_no_isolated (k : ℕ) :
    ∀ u : Fin (k + 2),
      ∃ v : Fin (k + 2),
        (SimpleGraph.cycleGraph (k + 2)).Adj u v := by
  intro u
  refine ⟨u + 1, ?_⟩
  change u + 1 ∈
    (SimpleGraph.cycleGraph (k + 2)).neighborSet u
  rw [SimpleGraph.cycleGraph_neighborSet]
  simp

lemma quotientGraph_no_isolated
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v)
    (f : V → V) (hf : ColorRespecting color f) :
    ∀ u : Set.range f,
      ∃ v : Set.range f, (quotientGraph graph f).Adj u v := by
  rintro ⟨_, ⟨u, rfl⟩⟩
  obtain ⟨v, huv⟩ := hneighbors u
  refine ⟨⟨f v, v, rfl⟩, ?_⟩
  exact (colorRespectingQuotientProjectionHom
    graph color hproper f hf).map_rel huv

lemma map_equiv_no_isolated
    {V W : Type*} (graph : SimpleGraph V) (e : V ≃ W)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    ∀ u : W, ∃ v : W, (graph.map e.toEmbedding).Adj u v := by
  intro u
  obtain ⟨v, huv⟩ := hneighbors (e.symm u)
  refine ⟨e v, ?_⟩
  have h :=
    (SimpleGraph.map_adj_apply
      (G := graph) (f := e.toEmbedding)
      (a := e.symm u) (b := v)).mpr huv
  simpa using h

lemma encodeFiniteGraph_no_isolated
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    GraphHasNoIsolated (encodeFiniteGraph graph).graph := by
  classical
  exact map_equiv_no_isolated graph (Fintype.equivFin V) hneighbors

lemma jTemplate_no_isolated :
    GraphHasNoIsolated jTemplate := by
  intro u
  rcases u with (base | ⟨copy, center⟩) |
    (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inl (0, (1, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
    · refine ⟨.inr (.inl (0, (2, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
  · refine ⟨.inr (.inl (copy, (0, center))), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl (jBase copy base)), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl 0), ?_⟩
    cases lastVertex
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]

lemma kTemplate_no_isolated :
    GraphHasNoIsolated kTemplate := by
  intro u
  rcases u with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · refine ⟨(copy, .inr (base, 0)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inr (0, center)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inl (.inl base)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]

lemma encodedJQuotient_no_isolated
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph jTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph jTemplate f)
    (quotientGraph_no_isolated jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h)
      jTemplate_no_isolated f hf.1)

lemma encodedKQuotient_no_isolated
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph kTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph kTemplate f)
    (quotientGraph_no_isolated kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h)
      kTemplate_no_isolated f hf.1)

theorem proposedFamily_member_no_isolated
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    GraphHasNoIsolated forbidden.graph :=
  proposedFamily_induction (P := fun graph => GraphHasNoIsolated graph.graph)
    (cycleGraph_no_isolated 2) (cycleGraph_no_isolated 4)
    (fun _ hf => encodedJQuotient_no_isolated hf)
    (fun _ hf => encodedKQuotient_no_isolated hf)
    forbidden hforbidden

lemma nat_le_pow_of_two_le
    {t : ℕ} (ht : 2 ≤ t) (j : ℕ) : j ≤ t ^ j := by
  exact (Nat.lt_pow_self (show 1 < t by omega)).le

theorem quadrangleVertexCount_parameter_lt (q : ℕ) :
    q < quadrangleVertexCount q := by
  unfold quadrangleVertexCount
  nlinarith [sq_nonneg q]

theorem quadrangle_prime_power_bracketing
    {t n : ℕ} (ht : 2 ≤ t)
    (hn : quadrangleVertexCount t ≤ n) :
    ∃ j : ℕ, 0 < j ∧
      quadrangleVertexCount (t ^ j) ≤ n ∧
      n < t ^ 3 * quadrangleVertexCount (t ^ j) := by
  let P : ℕ → Prop := fun j =>
    quadrangleVertexCount (t ^ j) ≤ n
  let j := Nat.findGreatest P (n + 1)
  have hone : P 1 := by
    simpa [P] using hn
  have hjfit : P j :=
    Nat.findGreatest_spec (P := P)
      (show 1 ≤ n + 1 by omega) hone
  have hjpositive : 0 < j := by
    have hle : 1 ≤ j := Nat.le_findGreatest
      (show 1 ≤ n + 1 by omega) hone
    omega
  have hjn : j ≤ n := by
    have hpow := nat_le_pow_of_two_le ht j
    have hvertex := quadrangleVertexCount_parameter_lt (t ^ j)
    change quadrangleVertexCount (t ^ j) ≤ n at hjfit
    omega
  have hnext : ¬ P (j + 1) :=
    Nat.findGreatest_is_greatest (P := P)
      (show j < j + 1 by omega)
      (show j + 1 ≤ n + 1 by omega)
  have hnnext :
      n < quadrangleVertexCount (t * t ^ j) := by
    have h := Nat.lt_of_not_ge hnext
    change n < quadrangleVertexCount (t ^ (j + 1)) at h
    simpa [pow_succ, Nat.mul_comm] using h
  have hgap := quadrangleVertexCount_mul_le (t ^ j) t
    (show 1 ≤ t by omega)
  exact ⟨j, hjpositive, hjfit, lt_of_lt_of_le hnnext hgap⟩

theorem quadrangle_extremal_lower_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hfree : forbidden.Free (symplecticQuadrangle K)) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber
        (quadrangleVertexCount (Nat.card K)) forbidden := by
  classical
  letI : Fintype (QuadrangleVertex K) := Fintype.ofFinite _
  have hvertex : Fintype.card (QuadrangleVertex K) =
      quadrangleVertexCount (Nat.card K) := by
    rw [← Nat.card_eq_fintype_card, symplecticQuadrangle_vertex_card]
    rfl
  calc
    quadrangleEdgeCount (Nat.card K) =
        (symplecticQuadrangle K).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        symplecticQuadrangle_edge_card]
      rfl
    _ ≤ SimpleGraph.extremalNumber
          (Fintype.card (QuadrangleVertex K)) forbidden :=
      SimpleGraph.card_edgeFinset_le_extremalNumber hfree
    _ = SimpleGraph.extremalNumber
          (quadrangleVertexCount (Nat.card K)) forbidden := by
      rw [hvertex]

theorem quadrangle_extremal_lower_padded_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (hfree : forbidden.Free (symplecticQuadrangle K))
    {n : ℕ} (hn : quadrangleVertexCount (Nat.card K) ≤ n) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber n forbidden := by
  exact (quadrangle_extremal_lower_of_free K forbidden hfree).trans
    (extremalNumber_monotone_of_no_isolated forbidden hneighbors hn)

theorem quadrangle_manuscript_scaled_density_of_gap
    (q n : ℕ)
    (hgap : n ≤ 27 * quadrangleVertexCount q) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  have hreal :
      (n : ℝ) ≤ (27 : ℝ) * (quadrangleVertexCount q : ℝ) := by
    exact_mod_cast hgap
  calc
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        (n : ℝ) ^ ((4 : ℝ) / 3) ≤
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        ((27 : ℝ) * (quadrangleVertexCount q : ℝ)) ^
          ((4 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hreal (by positivity))
        (by positivity)
    _ = (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hcancel :
          (27 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ ((4 : ℝ) / 3) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 27)]
        norm_num
      calc
        ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
            ((27 : ℝ) ^ ((4 : ℝ) / 3) *
              (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) =
          (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            ((27 : ℝ) ^ (-((4 : ℝ) / 3)) *
              (27 : ℝ) ^ ((4 : ℝ) / 3)) *
                (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
          ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ (quadrangleEdgeCount q : ℝ) := quadrangle_rpow_density q

theorem quadrangle_uniform_lower_of_prime_power_avoidance
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.Free (symplecticQuadrangle (GaloisField t j)))
    {n : ℕ} (hn : quadrangleVertexCount t ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
  obtain ⟨j, hj, hfit, hgap⟩ :=
    quadrangle_prime_power_bracketing ht hn
  let K := GaloisField t j
  have hcard : Nat.card K = t ^ j :=
    GaloisField.card t j (Nat.ne_of_gt hj)
  have hfitK : quadrangleVertexCount (Nat.card K) ≤ n := by
    simpa [hcard] using hfit
  have havoid : forbidden.Free (symplecticQuadrangle K) :=
    hfree j hj
  have hedge := quadrangle_extremal_lower_padded_of_free K
    forbidden hneighbors havoid hfitK
  have hedge' :
      (quadrangleEdgeCount (t ^ j) : ℝ) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
    exact_mod_cast (show quadrangleEdgeCount (t ^ j) ≤
      SimpleGraph.extremalNumber n forbidden by
        simpa [hcard] using hedge)
  have hfactor :
      t ^ 3 * quadrangleVertexCount (t ^ j) ≤
        27 * quadrangleVertexCount (t ^ j) :=
    Nat.mul_le_mul_right (quadrangleVertexCount (t ^ j)) htgap
  have hgap27 : n ≤ 27 * quadrangleVertexCount (t ^ j) :=
    (Nat.le_of_lt hgap).trans hfactor
  exact (quadrangle_manuscript_scaled_density_of_gap
    (t ^ j) n hgap27).trans hedge'

theorem four_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 4)
    (by simpa using cycleGraph_no_isolated 2)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_four_cycle_free _) hn

theorem six_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 6)
    (by simpa using cycleGraph_no_isolated 4)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_six_cycle_free _) hn

end Padding

noncomputable section LocalGeometry

open SimpleGraph

theorem common_neighbor_unique_of_four_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  by_contra hxy
  apply hfree
  let f : Fin 4 → V := ![u, x, v, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph]
    all_goals
      first
      | exact hux.symm
      | exact hvx.symm
      | exact huy.symm
      | exact hvy.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hux.ne, hux.symm.ne, hvx.ne, hvx.symm.ne,
        huy.ne, huy.symm.ne, hvy.ne, hvy.symm.ne]

def CommonNeighborRelated {V : Type*} (G : SimpleGraph V)
    (u v : V) : Prop :=
  u ≠ v ∧ ∃ w : V, G.Adj u w ∧ G.Adj v w

lemma commonNeighborRelated_symm
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : CommonNeighborRelated G u v) :
    CommonNeighborRelated G v u := by
  obtain ⟨hne, w, huw, hvw⟩ := h
  exact ⟨hne.symm, w, hvw, huw⟩

lemma bipartite_coloring_eq_of_common_neighbor
    {V : Type*} {G : SimpleGraph V}
    (color : G.Coloring (Fin 2)) {u v w : V}
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    color u = color v := by
  have hu := color.valid huw
  have hv := color.valid hvw
  apply Fin.ext
  omega

theorem common_neighbors_triangle_eq_of_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v w a b c : V}
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hwb : G.Adj w b)
    (hwc : G.Adj w c) (huc : G.Adj u c) :
    a = b ∧ b = c := by
  by_cases hab : a = b
  · subst b
    refine ⟨rfl, ?_⟩
    exact common_neighbor_unique_of_four_cycle_free hfour huw
      hua hwb huc hwc
  by_cases hbc : b = c
  · subst c
    have hac : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour huv
        hua hva huc hvb
    exact (hab hac).elim
  by_cases hac : a = c
  · subst c
    have hab' : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour hvw
        hva hwc hvb hwb
    exact (hab hab').elim
  obtain ⟨color⟩ := hbip
  have hcolor_uv : color u = color v :=
    bipartite_coloring_eq_of_common_neighbor color hua hva
  have hcolor_vw : color v = color w :=
    bipartite_coloring_eq_of_common_neighbor color hvb hwb
  have hub : u ≠ b := by
    intro h
    subst b
    exact color.valid hvb hcolor_uv.symm
  have hvc : v ≠ c := by
    intro h
    subst c
    exact color.valid huc hcolor_uv
  have hwa : w ≠ a := by
    intro h
    subst a
    exact color.valid hva hcolor_vw
  exfalso
  apply hsix
  let f : Fin 6 → V := ![u, a, v, b, w, c]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, SimpleGraph.cycleGraph]
    all_goals
      first
      | exact hua
      | exact hua.symm
      | exact hva
      | exact hva.symm
      | exact hvb
      | exact hvb.symm
      | exact hwb
      | exact hwb.symm
      | exact hwc
      | exact hwc.symm
      | exact huc
      | exact huc.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, huv, huv.symm, hvw, hvw.symm, huw, huw.symm,
        hab, Ne.symm hab, hbc, Ne.symm hbc, hac, Ne.symm hac,
        hua.ne, hua.symm.ne, hva.ne, hva.symm.ne,
        hvb.ne, hvb.symm.ne, hwb.ne, hwb.symm.ne,
        hwc.ne, hwc.symm.ne, huc.ne, huc.symm.ne,
        hub, hub.symm, hvc, hvc.symm, hwa, hwa.symm] at hij ⊢

theorem common_second_neighbors_pairwise_unrelated
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (hxu : CommonNeighborRelated G x u)
    (hxv : CommonNeighborRelated G x v)
    (hyu : CommonNeighborRelated G y u)
    (hyv : CommonNeighborRelated G y v) :
    ¬ CommonNeighborRelated G x y := by
  rintro ⟨hxy, b, hxb, hyb⟩
  obtain ⟨hxu_ne, a, hxa, hua⟩ := hxu
  obtain ⟨hxv_ne, d, hxd, hvd⟩ := hxv
  obtain ⟨hyu_ne, c, hyc, huc⟩ := hyu
  obtain ⟨hyv_ne, e, hye, hve⟩ := hyv
  have habc : a = c ∧ c = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxu_ne (Ne.symm hyu_ne) hxy
      hxa hua huc hyc hyb hxb
  have hdeb : d = e ∧ e = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxv_ne (Ne.symm hyv_ne) hxy
      hxd hvd hve hye hyb hxb
  apply hunrelated
  refine ⟨huv, b, ?_, ?_⟩
  · rwa [habc.1.trans habc.2] at hua
  · rwa [hdeb.1.trans hdeb.2] at hvd

section FourPathCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NonbacktrackingNeighbor (G : SimpleGraph V)
    (previous current : V) :=
  {next : V // G.Adj current next ∧ next ≠ previous}

lemma card_nonbacktrackingNeighbor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {previous current : V} (hedge : G.Adj current previous) :
    Fintype.card (NonbacktrackingNeighbor G previous current) =
      G.degree current - 1 := by
  classical
  calc
    Fintype.card (NonbacktrackingNeighbor G previous current) =
        ((G.neighborFinset current).erase previous).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext next
      simp [and_comm]
    _ = G.degree current - 1 := by
      rw [Finset.card_erase_of_mem]
      · rfl
      · simpa using hedge

abbrev NonbacktrackingFourPath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
        NonbacktrackingNeighbor G (w : V) (b : V)

lemma fintype_card_sigma_lower
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    {baseLower fiberLower : ℕ}
    (hbase : baseLower ≤ Fintype.card α)
    (hfiber : ∀ a : α, fiberLower ≤ Fintype.card (β a)) :
    baseLower * fiberLower ≤ Fintype.card (Sigma β) := by
  classical
  rw [Fintype.card_sigma]
  calc
    baseLower * fiberLower ≤ Fintype.card α * fiberLower :=
      Nat.mul_le_mul_right fiberLower hbase
    _ = ∑ _a : α, fiberLower := by simp
    _ ≤ ∑ a : α, Fintype.card (β a) :=
      Finset.sum_le_sum fun a _ => hfiber a

lemma card_nonbacktrackingFourPath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (NonbacktrackingFourPath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hthird (a : G.neighborSet u)
      (w : NonbacktrackingNeighbor G u (a : V)) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
            NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep w.property.1.symm
    · intro b
      exact hstep b.property.1.symm
  have hsecond (a : G.neighborSet u) :
      (d - 1) * ((d - 1) * (d - 1)) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
              NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · exact hthird a
  have hfirst : d ≤ Fintype.card (G.neighborSet u) := by
    simpa [G.card_neighborSet_eq_degree] using hdegree u
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
          NonbacktrackingNeighbor G (w : V) (b : V))
    hfirst hsecond
  simpa [pow_succ, mul_assoc] using hcount

def nonbacktrackingFourPathPair
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingFourPath G u) : V × V :=
  (path.2.2.2.1, path.2.1.1)

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_ne
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    u ≠ (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change u ≠ (v : V)
  intro huv
  have hub : G.Adj u (b : V) := by
    simpa only [huv] using v.property.1.symm
  have hab : (a : V) = (b : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm a.property w.property.1.symm
      hub b.property.1
  exact b.property.2 hab.symm

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    ¬ CommonNeighborRelated G u
      (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change ¬ CommonNeighborRelated G u (v : V)
  rintro ⟨_, c, huc, hvc⟩
  have huv : u ≠ (v : V) :=
    nonbacktrackingFourPath_endpoint_ne G hfour
      ⟨a, w, b, v⟩
  have hab := common_neighbors_triangle_eq_of_cycle_free
    hbip hfour hsix w.property.2.symm
    v.property.2.symm huv
    a.property w.property.1.symm
    b.property.1 v.property.1.symm hvc huc
  exact b.property.2 hab.1.symm

abbrev FourPathEndpointWitness (G : SimpleGraph V) (u : V) :=
  {pair : V × V //
    u ≠ pair.1 ∧
      ¬ CommonNeighborRelated G u pair.1 ∧
      CommonNeighborRelated G u pair.2 ∧
      CommonNeighborRelated G pair.1 pair.2}

noncomputable instance fourPathEndpointWitnessFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (FourPathEndpointWitness G u) :=
  Fintype.ofFinite _

def nonbacktrackingFourPathWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    FourPathEndpointWitness G u := by
  refine ⟨nonbacktrackingFourPathPair G path,
    nonbacktrackingFourPath_endpoint_ne G hfour path,
    nonbacktrackingFourPath_endpoint_unrelated G hbip hfour hsix path,
    ?_, ?_⟩
  · refine ⟨path.2.1.property.2.symm, path.1,
      path.1.property, path.2.1.property.1.symm⟩
  · refine ⟨path.2.2.2.property.2, path.2.2.1,
      path.2.2.2.property.1.symm,
      path.2.2.1.property.1⟩

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathPair_injective
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathPair G
        (u := u)) := by
  rintro ⟨a, w, b, v⟩ ⟨a', w', b', v'⟩ hpair
  change ((v : V), (w : V)) =
    ((v' : V), (w' : V)) at hpair
  have hv : (v : V) = (v' : V) :=
    congrArg Prod.fst hpair
  have hw : (w : V) = (w' : V) :=
    congrArg Prod.snd hpair
  have hwa' : G.Adj (w : V) (a' : V) := by
    rw [hw]
    exact w'.property.1.symm
  have haa' : (a : V) = (a' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm
      a.property w.property.1.symm
      a'.property hwa'
  have ha : a = a' := Subtype.ext haa'
  subst a'
  have hw' : w = w' := Subtype.ext hw
  subst w'
  have hvb' : G.Adj (v : V) (b' : V) := by
    rw [hv]
    exact v'.property.1.symm
  have hbb' : (b : V) = (b' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      v.property.2.symm
      b.property.1 v.property.1.symm
      b'.property.1 hvb'
  have hb : b = b' := Subtype.ext hbb'
  subst b'
  have hv' : v = v' := Subtype.ext hv
  subst v'
  rfl

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathWitness G hbip hfour hsix
        (u := u)) := by
  intro p q hpq
  apply nonbacktrackingFourPathPair_injective G hfour
  exact congrArg Subtype.val hpq

lemma four_path_endpoint_witness_count_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (FourPathEndpointWitness G u) := by
  calc
    d * (d - 1) ^ 3 ≤
        Fintype.card (NonbacktrackingFourPath G u) :=
      card_nonbacktrackingFourPath_lower G d hdegree u
    _ ≤ Fintype.card (FourPathEndpointWitness G u) :=
      Fintype.card_le_of_injective
        (nonbacktrackingFourPathWitness G hbip hfour hsix)
        (nonbacktrackingFourPathWitness_injective G hbip hfour hsix)

abbrev UnrelatedFourPathEndpoint (G : SimpleGraph V) (u : V) :=
  {v : V // u ≠ v ∧ ¬ CommonNeighborRelated G u v}

abbrev CommonSecondNeighbor (G : SimpleGraph V) (u v : V) :=
  {w : V //
    CommonNeighborRelated G u w ∧ CommonNeighborRelated G v w}

noncomputable instance unrelatedFourPathEndpointFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (UnrelatedFourPathEndpoint G u) :=
  Fintype.ofFinite _

noncomputable instance commonSecondNeighborFintype
    (G : SimpleGraph V) (u v : V) :
    Fintype (CommonSecondNeighbor G u v) :=
  Fintype.ofFinite _

def fourPathEndpointWitnessEquiv
    (G : SimpleGraph V) (u : V) :
    FourPathEndpointWitness G u ≃
      Σ v : UnrelatedFourPathEndpoint G u,
        CommonSecondNeighbor G u (v : V) where
  toFun pair :=
    ⟨⟨pair.1.1, pair.2.1, pair.2.2.1⟩,
      ⟨pair.1.2, pair.2.2.2.1, pair.2.2.2.2⟩⟩
  invFun pair :=
    ⟨((pair.1 : V), (pair.2 : V)),
      pair.1.2.1, pair.1.2.2,
      pair.2.2.1, pair.2.2.2⟩
  left_inv pair := Subtype.ext rfl
  right_inv pair := by
    rcases pair with ⟨v, w⟩
    rfl

omit [DecidableEq V] in
lemma fourPathEndpointWitness_card_eq_sum
    (G : SimpleGraph V) (u : V) :
    Fintype.card (FourPathEndpointWitness G u) =
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [Fintype.card_congr (fourPathEndpointWitnessEquiv G u),
    Fintype.card_sigma]

theorem four_path_common_second_neighbor_sum_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [← fourPathEndpointWitness_card_eq_sum G u]
  exact four_path_endpoint_witness_count_lower
    G hbip hfour hsix d hdegree u

def CommonNeighborIndependent (G : SimpleGraph V)
    (vertices : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ vertices → y ∈ vertices → x ≠ y →
    ¬ CommonNeighborRelated G x y

omit [Fintype V] in
lemma commonNeighborIndependent_neighborhood_injective
    (G : SimpleGraph V) (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    Function.Injective
      (fun pair :
        (Σ x : {x : V // x ∈ vertices},
          G.neighborSet (x : V)) =>
          (pair.2 : V)) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ hab
  have hxy : (x : V) = (y : V) := by
    by_contra hne
    apply hindependent x.property y.property hne
    refine ⟨hne, (a : V), a.property, ?_⟩
    have hyb : G.Adj (y : V) (b : V) := b.property
    exact Eq.mp
      (congrArg (G.Adj (y : V)) hab.symm) hyb
  have hsub : x = y := Subtype.ext hxy
  subst y
  have hneighbor : a = b := Subtype.ext hab
  subst b
  rfl

lemma commonNeighborIndependent_sum_degree_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    (∑ x : {x : V // x ∈ vertices}, G.degree (x : V)) ≤
      Fintype.card V := by
  have hcard := Fintype.card_le_of_injective
    (fun pair :
      (Σ x : {x : V // x ∈ vertices},
        G.neighborSet (x : V)) =>
        (pair.2 : V))
    (commonNeighborIndependent_neighborhood_injective
      G vertices hindependent)
  simpa only [Fintype.card_sigma,
    SimpleGraph.card_neighborSet_eq_degree] using hcard

lemma commonNeighborIndependent_card_mul_degree_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) :
    vertices.card * d ≤ Fintype.card V := by
  calc
    vertices.card * d = ∑ _x : {x : V // x ∈ vertices}, d := by simp
    _ ≤ ∑ x : {x : V // x ∈ vertices}, G.degree (x : V) :=
      Finset.sum_le_sum fun x _ => hdegree x
    _ ≤ Fintype.card V :=
      commonNeighborIndependent_sum_degree_le_card G vertices hindependent

end FourPathCounting

end LocalGeometry

noncomputable section BreadthFirstCounting

open SimpleGraph

section BreadthFirstPaths

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NonbacktrackingThreePath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      NonbacktrackingNeighbor G (a : V) (w : V)

def nonbacktrackingThreePathEndpoint
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingThreePath G u) : V :=
  path.2.2.1

lemma card_nonbacktrackingThreePath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    G.degree u * (d - 1) ^ 2 ≤
      Fintype.card (NonbacktrackingThreePath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hsecond (a : G.neighborSet u) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            NonbacktrackingNeighbor G (a : V) (w : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · intro w
      exact hstep w.property.1.symm
  have hroot : G.degree u ≤ Fintype.card (G.neighborSet u) := by
    exact (G.card_neighborSet_eq_degree u).symm.le
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        NonbacktrackingNeighbor G (a : V) (w : V))
    hroot hsecond
  simpa [pow_two] using hcount

omit [Fintype V] in
lemma nonbacktrackingThreePathEndpoint_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingThreePathEndpoint G (u := u)) := by
  rintro ⟨a, w, b⟩ ⟨a', w', b'⟩ hb
  change (b : V) = (b' : V) at hb
  have haa : (a : V) = (a' : V) := by
    by_contra hne
    have hww : (w : V) ≠ (w' : V) := by
      intro heq
      have hwa' : G.Adj (w : V) (a' : V) :=
        Eq.mp
          (congrArg (fun x : V => G.Adj x (a' : V)) heq.symm)
          w'.property.1.symm
      have heqa : (a : V) = (a' : V) :=
        common_neighbor_unique_of_four_cycle_free hfour
          w.property.2.symm
          a.property w.property.1.symm
          a'.property hwa'
      exact hne heqa
    have hwb : G.Adj (w' : V) (b : V) :=
      Eq.mp (congrArg (G.Adj (w' : V)) hb.symm)
        b'.property.1
    have htriangle := common_neighbors_triangle_eq_of_cycle_free
      hbip hfour hsix
      w.property.2.symm hww w'.property.2.symm
      a.property w.property.1.symm
      b.property.1 hwb
      w'.property.1.symm a'.property
    exact b.property.2 htriangle.1.symm
  have ha : a = a' := Subtype.ext haa
  subst a'
  have hwb' : G.Adj (b : V) (w' : V) :=
    Eq.mp (congrArg (fun x : V => G.Adj x (w' : V)) hb.symm)
      b'.property.1.symm
  have hww : (w : V) = (w' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      b.property.2.symm
      w.property.1 b.property.1.symm
      w'.property.1 hwb'
  have hw : w = w' := Subtype.ext hww
  subst w'
  have hb' : b = b' := Subtype.ext hb
  subst b'
  rfl

theorem girthEight_degree_mul_pred_sq_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v)
    (u : V) :
    G.degree u * (d - 1) ^ 2 ≤ Fintype.card V := by
  calc
    G.degree u * (d - 1) ^ 2 ≤
        Fintype.card (NonbacktrackingThreePath G u) :=
      card_nonbacktrackingThreePath_lower G d hdegree u
    _ ≤ Fintype.card V :=
      Fintype.card_le_of_injective
        (nonbacktrackingThreePathEndpoint G)
        (nonbacktrackingThreePathEndpoint_injective
          G hbip hfour hsix)

end BreadthFirstPaths

end BreadthFirstCounting

noncomputable section SubdivisionCounting

open SimpleGraph

section SubdivisionCopies

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def subdivisionVertexImage
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V) : SubdivisionVertex k → V
  | .inl (.inl i) => base i
  | .inl (.inr j) => center j
  | .inr (i, j) => pair i j

lemma subdivisionPairVertex_injective
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective
      (fun ij : Fin 3 × Fin k => pair ij.1 ij.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hpair
  have hi : i = i' := by
    by_contra hne
    apply hbase_unrelated hne
    refine ⟨fun h => hne (hbase h), pair i j,
      hpair_base i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (base i')) hpair.symm)
      (hpair_base i' j')
  subst i'
  have hj : j = j' := by
    by_contra hne
    apply hcenter_unrelated hne
    refine ⟨fun h => hne (hcenter h), pair i j,
      hpair_center i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (center j')) hpair.symm)
      (hpair_center i j')
  exact Prod.ext rfl hj

lemma subdivisionPairVertex_ne_base
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j : Fin k) (other : Fin 3) :
    pair i j ≠ base other := by
  obtain ⟨color⟩ := hbip
  have hfirst : color (base i) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i j) (hpair_center i j)
  have hother : color (base other) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base other j) (hpair_center other j)
  intro heq
  apply color.valid (hpair_base i j)
  exact hfirst.trans
    (hother.symm.trans (congrArg color heq).symm)

lemma subdivisionPairVertex_ne_center
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j other : Fin k) :
    pair i j ≠ center other := by
  obtain ⟨color⟩ := hbip
  have hother : color (base i) = color (center other) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i other) (hpair_center i other)
  intro heq
  apply color.valid (hpair_base i j)
  exact hother.trans (congrArg color heq).symm

lemma subdivisionVertexImage_injective
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective (subdivisionVertexImage base center pair) := by
  intro u v huv
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩
  · change base i = base i' at huv
    exact congrArg (fun a : Fin 3 =>
      (Sum.inl (Sum.inl a) : SubdivisionVertex k)) (hbase huv)
  · change base i = center j' at huv
    exact False.elim (hbase_center i j' huv)
  · change base i = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i' j' i huv.symm)
  · change center j = base i' at huv
    exact False.elim (hbase_center i' j huv.symm)
  · change center j = center j' at huv
    exact congrArg (fun a : Fin k =>
      (Sum.inl (Sum.inr a) : SubdivisionVertex k)) (hcenter huv)
  · change center j = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i' j' j huv.symm)
  · change pair i j = base i' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i j i' huv)
  · change pair i j = center j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i j j' huv)
  · change pair i j = pair i' j' at huv
    have heq : (i, j) = (i', j') :=
      subdivisionPairVertex_injective base center pair
        hbase hcenter hbase_unrelated hcenter_unrelated
        hpair_base hpair_center huv
    exact congrArg
      (fun ij : Fin 3 × Fin k =>
        (Sum.inr ij : SubdivisionVertex k)) heq

lemma subdivisionVertexImage_map_relation
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    {u v : SubdivisionVertex k}
    (hadj : (SubdivisionGraph k).Adj u v) :
    G.Adj (subdivisionVertexImage base center pair u)
      (subdivisionVertexImage base center pair v) := by
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩ <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation, subdivisionVertexImage]
  all_goals
    first
    | exact (hpair_base _ _).symm
    | exact (hpair_center _ _).symm

def subdivisionCopyOfCommonNeighbors
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  refine ⟨⟨subdivisionVertexImage base center pair, ?_⟩, ?_⟩
  · intro u v huv
    exact subdivisionVertexImage_map_relation base center pair
      hpair_base hpair_center huv
  · exact subdivisionVertexImage_injective hbip base center pair
      hbase hcenter hbase_center hbase_unrelated
      hcenter_unrelated hpair_base hpair_center

noncomputable def subdivisionCopyOfRelatedCenters
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  classical
  let pair : Fin 3 → Fin k → V :=
    fun i j => Classical.choose (hrelated i j).2
  have hpair_base (i : Fin 3) (j : Fin k) :
      G.Adj (base i) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).1
  have hpair_center (i : Fin 3) (j : Fin k) :
      G.Adj (center j) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).2
  exact subdivisionCopyOfCommonNeighbors hbip base center pair
    hbase hcenter (fun i j => (hrelated i j).1)
    hbase_unrelated hcenter_unrelated hpair_base hpair_center

noncomputable def subdivisionCopyOfGirthEightCenters
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  have hbase01 : base 0 ≠ base 1 := by
    intro heq
    exact (by decide : (0 : Fin 3) ≠ 1) (hbase heq)
  have hcenter_unrelated :
      ∀ ⦃i j : Fin k⦄, i ≠ j →
        ¬ CommonNeighborRelated G (center i) (center j) := by
    intro i j hij
    exact common_second_neighbors_pairwise_unrelated
      hbip hfour hsix hbase01
      (hbase_unrelated (by decide : (0 : Fin 3) ≠ 1))
      (commonNeighborRelated_symm (hrelated 0 i))
      (commonNeighborRelated_symm (hrelated 1 i))
      (commonNeighborRelated_symm (hrelated 0 j))
      (commonNeighborRelated_symm (hrelated 1 j))
  exact subdivisionCopyOfRelatedCenters hbip base center
    hbase hcenter hbase_unrelated hcenter_unrelated hrelated

end SubdivisionCopies

end SubdivisionCounting

noncomputable section QuotientWitnesses

open SimpleGraph

noncomputable def fiberRepresentative
    {α β : Type*} (g : α → β) (b : Set.range g) : α :=
  Classical.choose b.property

lemma fiberRepresentative_spec
    {α β : Type*} (g : α → β) (b : Set.range g) :
    g (fiberRepresentative g b) = b.1 :=
  Classical.choose_spec b.property

noncomputable def kernelNormalForm
    {α β : Type*} (g : α → β) (x : α) : α :=
  fiberRepresentative g ⟨g x, ⟨x, rfl⟩⟩

lemma kernelNormalForm_spec
    {α β : Type*} (g : α → β) (x : α) :
    g (kernelNormalForm g x) = g x :=
  fiberRepresentative_spec g ⟨g x, ⟨x, rfl⟩⟩

lemma kernelNormalForm_eq_iff
    {α β : Type*} (g : α → β) (x y : α) :
    kernelNormalForm g x = kernelNormalForm g y ↔ g x = g y := by
  constructor
  · intro h
    calc
      g x = g (kernelNormalForm g x) :=
        (kernelNormalForm_spec g x).symm
      _ = g (kernelNormalForm g y) := congrArg g h
      _ = g y := kernelNormalForm_spec g y
  · intro h
    unfold kernelNormalForm
    congr 1
    exact Subtype.ext h

lemma kernelNormalForm_idempotent
    {α β : Type*} (g : α → β) (x : α) :
    kernelNormalForm g (kernelNormalForm g x) =
      kernelNormalForm g x := by
  apply (kernelNormalForm_eq_iff g _ _).mpr
  exact kernelNormalForm_spec g x

lemma kernelNormalForm_fixed
    {α β : Type*} (g : α → β)
    (u : Set.range (kernelNormalForm g)) :
    kernelNormalForm g u.1 = u.1 := by
  obtain ⟨x, hx⟩ := u.property
  rw [← hx]
  exact kernelNormalForm_idempotent g x

noncomputable def kernelQuotientCopy
    {α β : Type*} (source : SimpleGraph α)
    (target : SimpleGraph β) (hom : source →g target) :
    SimpleGraph.Copy
      (quotientGraph source (kernelNormalForm hom)) target := by
  refine ⟨⟨fun u => hom u.1, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (quotientRelation source (kernelNormalForm hom))
        u v).mp hadj with ⟨_, hforward | hbackward⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hforward
      have hu : hom u.1 = hom x := by
        calc
          hom u.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hv : hom v.1 = hom y := by
        calc
          hom v.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact hom.map_rel hxy
    · obtain ⟨x, y, hx, hy, hxy⟩ := hbackward
      have hv : hom v.1 = hom x := by
        calc
          hom v.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hu : hom u.1 = hom y := by
        calc
          hom u.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact (hom.map_rel hxy).symm
  · intro u v huv
    apply Subtype.ext
    have h := (kernelNormalForm_eq_iff hom u.1 v.1).mpr huv
    rwa [kernelNormalForm_fixed hom u,
      kernelNormalForm_fixed hom v] at h

noncomputable def encodeFiniteGraphCopy
    {α β : Type*} [Fintype α]
    (source : SimpleGraph α) (target : SimpleGraph β)
    (copy : SimpleGraph.Copy source target) :
    SimpleGraph.Copy (encodeFiniteGraph source).graph target := by
  exact copy.comp
    (SimpleGraph.Iso.map (Fintype.equivFin α) source).symm.toCopy

lemma kernelNormalForm_jAdmissible
    {V : Type*} (g : JVertex → V)
    (hcolor : ∀ u v, g u = g v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => g (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v | InJCopy copy v}) :
    JAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro u v huv
    apply hbase
    exact (kernelNormalForm_eq_iff g _ _).mp huv
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

lemma kernelNormalForm_kAdmissible
    {V : Type*} (g : KVertex → V)
    (hcolor : ∀ u v, g u = g v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v : KVertex | v.1 = copy}) :
    KAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

theorem proposedFamilyFree_no_jTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : jTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) : False := by
  let f := kernelNormalForm hom
  have hf : JAdmissible f :=
    kernelNormalForm_jAdmissible hom hcolor hbase hcopies
  have hmember := jQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph jTemplate f) host
    (kernelQuotientCopy jTemplate host hom)⟩

theorem proposedFamilyFree_no_kTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : kTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) : False := by
  let f := kernelNormalForm hom
  have hf : KAdmissible f :=
    kernelNormalForm_kAdmissible hom hcolor hcopies
  have hmember := kQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph kTemplate f) host
    (kernelQuotientCopy kTemplate host hom)⟩

end QuotientWitnesses

section CommutativeRing

variable {K : Type*} [CommRing K]

def symmetricQuadratic (a b c x y : K) : K :=
  a * x ^ 2 + (2 : K) * b * x * y + c * y ^ 2

def symmetricDet (a b c : K) : K := a * c - b ^ 2

lemma symmetricQuadratic_eq_bilinear
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by
  unfold symmetricQuadratic
  ring

lemma symmetricDet_zero_diagonal_sub (b b' : K) :
    symmetricDet (0 : K) (b - b') 0 = -((b - b') ^ 2) := by
  simp [symmetricDet]

end CommutativeRing

section CharacteristicTwo

variable {K : Type*} [Field K] [CharP K 2]

lemma symmetricQuadratic_char_two
    (a b c x y : K) :
    symmetricQuadratic a b c x y = a * x ^ 2 + c * y ^ 2 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [symmetricQuadratic, htwo]

lemma symmetricQuadratic_char_two_eq_square
    (r s b x y : K) :
    symmetricQuadratic (r ^ 2) b (s ^ 2) x y =
      (r * x + s * y) ^ 2 := by
  rw [symmetricQuadratic_char_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 =
        (r * x) ^ 2 + (s * y) ^ 2 := by ring
    _ = (r * x + s * y) ^ 2 := by
      rw [add_sq]
      simp [htwo]

lemma square_surjective_char_two [Finite K] :
    Function.Surjective (fun x : K => x ^ 2) := by
  intro a
  obtain ⟨r, hr⟩ := (isSquare_of_charTwo' a).exists_sq
  exact ⟨r, hr.symm⟩

lemma symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    [Finite K] {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : symmetricQuadratic a b c x y = 0)
    (hsecond : symmetricQuadratic a b c x' y' = 0) :
    a = 0 ∧ c = 0 := by
  obtain ⟨r, hr⟩ := square_surjective_char_two a
  obtain ⟨s, hs⟩ := square_surjective_char_two c
  change r ^ 2 = a at hr
  change s ^ 2 = c at hs
  have hlinfirst : r * x + s * y = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hfirst
  have hlinsecond : r * x' + s * y' = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hsecond
  have hrdet : (x * y' - x' * y) * r = 0 := by
    linear_combination y' * hlinfirst - y * hlinsecond
  have hsdet : (x * y' - x' * y) * s = 0 := by
    linear_combination x * hlinsecond - x' * hlinfirst
  have hrzero : r = 0 := (mul_eq_zero.mp hrdet).resolve_left hind
  have hszero : s = 0 := (mul_eq_zero.mp hsdet).resolve_left hind
  constructor
  · simpa [hrzero] using hr.symm
  · simpa [hszero] using hs.symm

end CharacteristicTwo

section Field

variable {K : Type*} [Field K]

def symmetricQuadraticEvaluationMatrix
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x₀ ^ 2, (2 : K) * x₀ * y₀, y₀ ^ 2;
     x₁ ^ 2, (2 : K) * x₁ * y₁, y₁ ^ 2;
     x₂ ^ 2, (2 : K) * x₂ * y₂, y₂ ^ 2]

lemma symmetricQuadraticEvaluationMatrix_det
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) :
    (symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂).det =
      (2 : K) * (x₀ * y₁ - x₁ * y₀) *
        (x₀ * y₂ - x₂ * y₀) * (x₁ * y₂ - x₂ * y₁) := by
  rw [Matrix.det_fin_three]
  simp [symmetricQuadraticEvaluationMatrix]
  ring

lemma symmetricQuadratic_no_three_independent_roots
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  let A := symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂
  have hdet : A.det ≠ 0 := by
    rw [symmetricQuadraticEvaluationMatrix_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo h01) h02) h12
  have hmul : A.mulVec ![a, b, c] = 0 := by
    funext i
    fin_cases i
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₀
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₁
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₂
  have hzero : ![a, b, c] = (0 : Fin 3 → K) :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have ha : a = 0 := congrFun hzero 0
  have hb : b = 0 := congrFun hzero 1
  have hc : c = 0 := congrFun hzero 2
  exact hcoeff.elim (fun h => h ha)
    (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))

lemma symmetricQuadratic_no_three_roots_of_det_ne_zero
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  apply symmetricQuadratic_no_three_independent_roots
    htwo (a := a) (b := b) (c := c) (x₀ := x₀) (y₀ := y₀)
    (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂)
    (h01 := h01) (h02 := h02) (h12 := h12)
    (hroot₀ := hroot₀) (hroot₁ := hroot₁) (hroot₂ := hroot₂)
  by_contra h
  push Not at h
  obtain ⟨ha, hb, hc⟩ := h
  apply hdet
  simp [symmetricDet, ha, hb, hc]

lemma symmetricDet_zero_diagonal_sub_ne_zero
    {b b' : K} (h : b ≠ b') :
    symmetricDet (0 : K) (b - b') 0 ≠ 0 := by
  rw [symmetricDet_zero_diagonal_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr h))

end Field

noncomputable section Separation

open Filter Finset SimpleGraph
open scoped Topology

def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)

lemma extremalScale_pos {n : ℕ} (hn : 0 < n) :
    0 < extremalScale n := by
  unfold extremalScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma extremalScale_nonneg (n : ℕ) :
    0 ≤ extremalScale n := by
  unfold extremalScale
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

def FamilyLittleO (family : Finset FiniteGraph) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (familyExtremal family n : ℝ) ≤ ε * extremalScale n

def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)

structure SeparationCertificate (family : Finset FiniteGraph) where
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  family_littleO : FamilyLittleO family
  member_lower : UniformMemberLower family lowerConstant

noncomputable def manuscriptLowerConstant : ℝ :=
  (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
    (27 : ℝ) ^ (-((4 : ℝ) / 3))

theorem manuscriptLowerConstant_pos : 0 < manuscriptLowerConstant := by
  unfold manuscriptLowerConstant
  positivity

lemma not_compact_of_separation
    {family : Finset FiniteGraph}
    (certificate : SeparationCertificate family) :
    ¬ IsCompactFamily family := by
  rintro ⟨forbidden, hmem, C, hC, hcomparison⟩
  have hepsilon : 0 < certificate.lowerConstant / (2 * C) := by
    exact div_pos certificate.lowerConstant_pos
      (mul_pos (by norm_num) hC)
  have hupper := certificate.family_littleO
    (certificate.lowerConstant / (2 * C)) hepsilon
  have hlower := certificate.member_lower forbidden hmem
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  have himpossible : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hupper, hlower, hcomparison, hpositive]
      with n hnupper hnlower hncomparison hnpositive
    have hs := extremalScale_pos hnpositive
    have hscaled :
        C * (familyExtremal family n : ℝ) ≤
          C * ((certificate.lowerConstant / (2 * C)) *
            extremalScale n) :=
      mul_le_mul_of_nonneg_left hnupper hC.le
    have hidentity :
        C * ((certificate.lowerConstant / (2 * C)) *
          extremalScale n) =
            (certificate.lowerConstant / 2) * extremalScale n := by
      field_simp
    rw [hidentity] at hscaled
    nlinarith [mul_pos certificate.lowerConstant_pos hs]
  exact himpossible.exists.elim (fun _ h => h)

theorem proposedFamily_not_compact_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ IsCompactFamily proposedFamily := by
  apply not_compact_of_separation
  exact
    { lowerConstant := manuscriptLowerConstant
      lowerConstant_pos := manuscriptLowerConstant_pos
      family_littleO := hupper
      member_lower := hlower }

lemma not_compactnessConjecture_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ CompactnessConjectureStatement := by
  intro hconjecture
  exact proposedFamily_not_compact_of_bounds hupper hlower
    (hconjecture proposedFamily proposedFamily_nonempty
      proposedFamily_isCyclic)

end Separation

noncomputable section Supersaturation

open Finset SimpleGraph

section FiniteHeavyFibers

def fourPathHeavyThreshold (N p : ℕ) : ℝ :=
  (p : ℝ) / (2 * (N : ℝ))

def finiteHeavyFiberMass {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ) : ℝ :=
  ∑ x : α,
    if fourPathHeavyThreshold N p ≤ (weight x : ℝ)
    then (weight x : ℝ) else 0

theorem finite_heavy_fiber_mass_half
    {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ)
    (hN : 0 < N)
    (hcapacity : Fintype.card α ≤ N)
    (htotal : p ≤ ∑ x : α, weight x) :
    (p : ℝ) / 2 ≤ finiteHeavyFiberMass weight N p := by
  classical
  let R : ℝ := fourPathHeavyThreshold N p
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hsum :
      (∑ x : α, (weight x : ℝ)) ≤
        (∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) +
          (Fintype.card α : ℝ) * R := by
    calc
      (∑ x : α, (weight x : ℝ)) ≤
          ∑ x : α,
            ((if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) + R) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with hx
        · linarith
        · have : (weight x : ℝ) < R := lt_of_not_ge hx
          linarith
      _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hcapacityReal : (Fintype.card α : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcapacity
  have hthreshold : (N : ℝ) * R = (p : ℝ) / 2 := by
    dsimp [R, fourPathHeavyThreshold]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  have htotalReal :
      (p : ℝ) ≤ ∑ x : α, (weight x : ℝ) := by
    exact_mod_cast htotal
  change (p : ℝ) / 2 ≤
    ∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0
  nlinarith [mul_le_mul_of_nonneg_right hcapacityReal hR]

end FiniteHeavyFibers

section ActualFourPathFibers

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma unrelated_four_path_endpoint_card_le
    (G : SimpleGraph V) (u : V) :
    Fintype.card (UnrelatedFourPathEndpoint G u) ≤ Fintype.card V := by
  exact Fintype.card_le_of_injective
    (fun v : UnrelatedFourPathEndpoint G u => (v : V))
    Subtype.val_injective

omit [Fintype V] [DecidableEq V] in
lemma common_second_neighbor_pairwise_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v : V}
    (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (x y : CommonSecondNeighbor G u v) :
    ¬ CommonNeighborRelated G (x : V) (y : V) := by
  exact common_second_neighbors_pairwise_unrelated
    hbip hfour hsix huv hunrelated
    (commonNeighborRelated_symm x.property.1)
    (commonNeighborRelated_symm x.property.2)
    (commonNeighborRelated_symm y.property.1)
    (commonNeighborRelated_symm y.property.2)

lemma four_path_heavy_common_second_neighbor_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 2 ≤
      finiteHeavyFiberMass
        (fun v : UnrelatedFourPathEndpoint G u =>
          Fintype.card (CommonSecondNeighbor G u (v : V)))
        (Fintype.card V) (d * (d - 1) ^ 3) := by
  apply finite_heavy_fiber_mass_half
  · exact Fintype.card_pos_iff.mpr ⟨u⟩
  · exact unrelated_four_path_endpoint_card_le G u
  · exact four_path_common_second_neighbor_sum_lower
      G hbip hfour hsix d hdegree u

end ActualFourPathFibers

section ActualThetaExtensions

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thetaBaseExtensions
    (G : SimpleGraph V) (y z : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ witness : SimpleGraph.Copy thetaGraph G,
      witness (.inl (.inl (0 : Fin 3))) = x ∧
      witness (.inl (.inl (1 : Fin 3))) = y ∧
      witness (.inl (.inl (2 : Fin 3))) = z

lemma mem_thetaBaseExtensions
    (G : SimpleGraph V) (x y z : V) :
    x ∈ thetaBaseExtensions G y z ↔
      ∃ witness : SimpleGraph.Copy thetaGraph G,
        witness (.inl (.inl (0 : Fin 3))) = x ∧
        witness (.inl (.inl (1 : Fin 3))) = y ∧
        witness (.inl (.inl (2 : Fin 3))) = z := by
  classical
  simp [thetaBaseExtensions]

def gluedJBase {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G) : Fin 4 → V :=
  ![copies 0 (.inl (.inl (0 : Fin 3))),
    copies 1 (.inl (.inl (0 : Fin 3))),
    copies 0 (.inl (.inl (1 : Fin 3))),
    copies 0 (.inl (.inl (2 : Fin 3)))]

def gluedJVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V) : JVertex → V
  | .inl (.inl base) => gluedJBase copies base
  | .inl (.inr (copy, center)) =>
      copies copy (.inl (.inr center))
  | .inr (.inl (copy, (base, center))) =>
      copies copy (.inr (base, center))
  | .inr (.inr _) => joining

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_jBase
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (base : Fin 3) :
    gluedJBase copies (jBase copy base) =
      copies copy (.inl (.inl base)) := by
  fin_cases copy <;> fin_cases base <;>
    simp [gluedJBase, jBase, hfirst, hsecond]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_jThetaVertex
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (vertex : SubdivisionVertex 2) :
    gluedJVertex copies joining (jThetaVertex copy vertex) =
      copies copy vertex := by
  rcases vertex with (base | center) | pair
  · exact gluedJBase_jBase copies hfirst hsecond copy base
  · simp [jThetaVertex, gluedJVertex]
  · simp [jThetaVertex, gluedJVertex]

lemma inJCopy_iff_exists_jThetaVertex
    (copy : Fin 2) (vertex : JVertex) :
    InJCopy copy vertex ↔
      ∃ source : SubdivisionVertex 2,
        jThetaVertex copy source = vertex := by
  constructor
  · intro h
    rcases vertex with (base | center) | (pair | joining)
    · obtain ⟨source, hsource⟩ := h
      refine ⟨.inl (.inl source), ?_⟩
      simpa [jThetaVertex] using congrArg
        (fun value : Fin 4 => (Sum.inl (Sum.inl value) : JVertex))
        hsource.symm
    · rcases center with ⟨index, center⟩
      change copy = index at h
      subst index
      exact ⟨.inl (.inr center), rfl⟩
    · rcases pair with ⟨index, base, center⟩
      change copy = index at h
      subst index
      exact ⟨.inr (base, center), rfl⟩
    · exact False.elim h
  · rintro ⟨source, rfl⟩
    exact jThetaVertex_mem copy source

lemma theta_base_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma theta_center_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    {source target : JVertex}
    (hedge : jTemplateRelation source target) :
    G.Adj
      (gluedJVertex copies joining source)
      (gluedJVertex copies joining target) := by
  rcases source with (base | center) | (pair | star)
  · rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy, base', center'⟩
      change base = jBase copy base' at hedge
      subst base
      change G.Adj
        (gluedJBase copies (jBase copy base'))
        (copies copy (.inr (base', center')))
      rw [gluedJBase_jBase copies hfirst hsecond copy base']
      exact (copies copy).toHom.map_rel
        (theta_base_pair_adj base' center')
    · change base = 0 ∨ base = 1 at hedge
      rcases hedge with hbase | hbase
      · subst base
        simpa [gluedJVertex, gluedJBase] using hjoinFirst
      · subst base
        simpa [gluedJVertex, gluedJBase] using hjoinSecond
  · rcases center with ⟨copy, center⟩
    rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy', base, center'⟩
      change copy = copy' ∧ center = center' at hedge
      obtain ⟨hcopy, hcenter⟩ := hedge
      subst copy'
      subst center'
      exact (copies copy).toHom.map_rel
        (theta_center_pair_adj base center)
    · exact False.elim hedge
  · exact False.elim hedge
  · exact False.elim hedge

def gluedJHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    jTemplate →g G where
  toFun := gluedJVertex copies joining
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      jTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedJVertex_map_relation copies joining hfirst hsecond
        hjoinFirst hjoinSecond hforward
    · exact (gluedJVertex_map_relation copies joining
        hfirst hsecond hjoinFirst hjoinSecond hbackward).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    (copy : Fin 2) :
    Set.InjOn
      (gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond)
      {vertex | InJCopy copy vertex} := by
  intro left hleft right hright heq
  change InJCopy copy left at hleft
  change InJCopy copy right at hright
  obtain ⟨source, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy left).mp hleft
  obtain ⟨target, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy right).mp hright
  change
    gluedJVertex copies joining (jThetaVertex copy source) =
      gluedJVertex copies joining (jThetaVertex copy target) at heq
  rw [gluedJVertex_jThetaVertex copies joining hfirst hsecond copy,
    gluedJVertex_jThetaVertex copies joining hfirst hsecond copy] at heq
  have hequal := (copies copy).injective heq
  subst target
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_injective
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hdistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3)))) :
    Function.Injective (gluedJBase copies) := by
  have hcopy (index : Fin 2) {i j : Fin 3}
      (hij : i ≠ j) :
      copies index (.inl (.inl i)) ≠
        copies index (.inl (.inl j)) := by
    intro h
    apply hij
    simpa using (copies index).injective h
  have h02 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) :=
    hcopy 0 (by decide)
  have h03 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h23 :
      copies 0 (.inl (.inl (1 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h12 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 1))
      (h.trans hfirst.symm)
  have h13 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 2))
      (h.trans hsecond.symm)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [gluedJBase]

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_center_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by
  exact bipartite_coloring_eq_of_common_neighbor color
    (copy.toHom.map_rel (theta_base_pair_adj base center))
    (copy.toHom.map_rel (theta_center_pair_adj base center))

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (first second : Fin 3) :
    color (copy (.inl (.inl first))) =
      color (copy (.inl (.inl second))) := by
  calc
    color (copy (.inl (.inl first))) =
        color (copy (.inl (.inr (0 : Fin 2)))) :=
      thetaCopy_base_center_color_eq color copy first 0
    _ = color (copy (.inl (.inl second))) :=
      (thetaCopy_base_center_color_eq color copy second 0).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedThetaBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (copy : Fin 2) (base : Fin 3) :
    color (copies copy (.inl (.inl base))) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases copy
  · exact thetaCopy_base_color_eq color (copies 0) base 0
  · calc
      color (copies 1 (.inl (.inl base))) =
          color (copies 1 (.inl (.inl (1 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 1) base 1
      _ = color (copies 0 (.inl (.inl (1 : Fin 3)))) :=
        congrArg color hfirst
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 0) 1 0

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (base : Fin 4) :
    color (gluedJBase copies base) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases base
  · rfl
  · exact gluedThetaBase_color_eq copies hfirst color 1 0
  · exact gluedThetaBase_color_eq copies hfirst color 0 1
  · exact gluedThetaBase_color_eq copies hfirst color 0 2

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (color : G.Coloring (Fin 2))
    (vertex : JVertex) :
    jColor vertex = false ↔
      color (gluedJVertex copies joining vertex) =
        color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  rcases vertex with (base | center) | (pair | star)
  · simpa [jColor, gluedJVertex] using
      gluedJBase_color_eq copies hfirst color base
  · rcases center with ⟨copy, center⟩
    simp only [jColor, gluedJVertex, true_iff]
    calc
      color (copies copy (.inl (.inr center))) =
          color (copies copy (.inl (.inl (0 : Fin 3)))) :=
        (thetaCopy_base_center_color_eq
          color (copies copy) 0 center).symm
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        gluedThetaBase_color_eq copies hfirst color copy 0
  · rcases pair with ⟨copy, base, center⟩
    simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    have hedge := (copies copy).toHom.map_rel
      (theta_base_pair_adj base center)
    have hvalid := color.valid hedge
    apply hvalid
    exact (gluedThetaBase_color_eq
      copies hfirst color copy base).trans heq.symm
  · simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    exact (color.valid hjoinFirst) heq.symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    ∀ left right,
      gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond left =
          gluedJHom copies joining hfirst hsecond
            hjoinFirst hjoinSecond right →
        jColor left = jColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hcolor :
      color (gluedJVertex copies joining left) =
        color (gluedJVertex copies joining right) :=
    congrArg color heq
  cases hleft : jColor left <;> cases hright : jColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mp hleft
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mpr
        (hcolor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mp hright
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mpr
        (hcolor.trans hbase)
    simp [hleft] at hfalse
  · rfl

lemma thetaBaseExtensions_commonNeighborIndependent
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (y z : Fin n) :
    CommonNeighborIndependent host (thetaBaseExtensions host y z) := by
  intro x x' hx hx' hdistinct
  rintro ⟨_, joining, hxjoin, hx'join⟩
  obtain ⟨first, hfirstX, hfirstY, hfirstZ⟩ :=
    (mem_thetaBaseExtensions host x y z).mp hx
  obtain ⟨second, hsecondX, hsecondY, hsecondZ⟩ :=
    (mem_thetaBaseExtensions host x' y z).mp hx'
  let copies : Fin 2 → SimpleGraph.Copy thetaGraph host :=
    ![first, second]
  have hsharedFirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    change second (.inl (.inl (1 : Fin 3))) =
      first (.inl (.inl (1 : Fin 3)))
    exact hsecondY.trans hfirstY.symm
  have hsharedSecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    change second (.inl (.inl (2 : Fin 3))) =
      first (.inl (.inl (2 : Fin 3)))
    exact hsecondZ.trans hfirstZ.symm
  have hjoinFirst :
      host.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (first (.inl (.inl (0 : Fin 3)))) joining
    rw [hfirstX]
    exact hxjoin
  have hjoinSecond :
      host.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (second (.inl (.inl (0 : Fin 3)))) joining
    rw [hsecondX]
    exact hx'join
  have hbaseDistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3))) := by
    change first (.inl (.inl (0 : Fin 3))) ≠
      second (.inl (.inl (0 : Fin 3)))
    rw [hfirstX, hsecondX]
    exact hdistinct
  apply proposedFamilyFree_no_jTemplate hfree
    (gluedJHom copies joining hsharedFirst hsharedSecond
      hjoinFirst hjoinSecond)
  · exact gluedJHom_color_respecting hbip copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond
  · change Function.Injective (gluedJBase copies)
    exact gluedJBase_injective copies hsharedFirst
      hsharedSecond hbaseDistinct
  · intro copy
    exact gluedJHom_injOn_marked_copy copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond copy

lemma thetaBaseExtensions_card_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (y z : Fin n) :
    (thetaBaseExtensions host y z).card * d ≤ n := by
  simpa using
    (commonNeighborIndependent_card_mul_degree_le
      host (thetaBaseExtensions host y z)
      (thetaBaseExtensions_commonNeighborIndependent
        host hfree hbip y z)
      d hdegree)

end ActualThetaExtensions

section ActualCommonCenterTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ i : Fin 3, CommonNeighborRelated G (base i) center

omit [DecidableEq V] in
lemma mem_tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) (center : V) :
    center ∈ tripleCommonCenters G base ↔
      ∀ i : Fin 3, CommonNeighborRelated G (base i) center := by
  classical
  simp [tripleCommonCenters]

lemma mem_thetaBaseExtensions_of_girthEightCenters
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin 2 → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  refine (mem_thetaBaseExtensions G _ _ _).mpr ?_
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_, ?_, ?_⟩
  all_goals rfl

lemma mem_thetaBaseExtensions_of_two_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenters : 2 ≤ (tripleCommonCenters G base).card) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  classical
  have hcard : 1 < (tripleCommonCenters G base).card := by omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp hcard
  let center : Fin 2 → V := ![first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base first).mp hfirst i
    · exact (mem_tripleCommonCenters G base second).mp hsecond i
  exact mem_thetaBaseExtensions_of_girthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated

end ActualCommonCenterTriples

section CubicBinomialSupersaturation

lemma choose_three_factorial_identity (t : ℕ) :
    6 * t.choose 3 = t * (t - 1) * (t - 2) := by
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose t 3).symm

lemma choose_three_cubic_lower {t : ℕ} (ht : 3 ≤ t) :
    (t : ℝ) ^ 3 / 27 ≤ (t.choose 3 : ℝ) := by
  have hone : 1 ≤ t := by omega
  have htwo : 2 ≤ t := by omega
  have hidentity := congrArg (fun value : ℕ => (value : ℝ))
    (choose_three_factorial_identity t)
  norm_num [Nat.cast_sub hone, Nat.cast_sub htwo] at hidentity
  have htReal : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hfactor :
      0 ≤ (t : ℝ) * ((t : ℝ) - 3) *
        (7 * (t : ℝ) - 6) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (by linarith)
  nlinarith

end CubicBinomialSupersaturation

section ActualTripleSupersaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonSecondNeighborTripleMass
    (G : SimpleGraph V) (u : V) : ℕ :=
  ∑ v : UnrelatedFourPathEndpoint G u,
    (Fintype.card (CommonSecondNeighbor G u (v : V))).choose 3

lemma four_path_common_second_neighbor_triple_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass G u : ℝ) := by
  classical
  let p : ℕ := d * (d - 1) ^ 3
  let R : ℝ := fourPathHeavyThreshold (Fintype.card V) p
  let weight : UnrelatedFourPathEndpoint G u → ℕ :=
    fun v => Fintype.card (CommonSecondNeighbor G u (v : V))
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hRthree : (3 : ℝ) ≤ R := by
    simpa [R, p] using hthreshold
  have hheavy :
      (p : ℝ) / 2 ≤
        finiteHeavyFiberMass weight (Fintype.card V) p := by
    simpa [weight, p] using
      (four_path_heavy_common_second_neighbor_mass_lower
        G hbip hfour hsix d hdegree u)
  have hpoint (v : UnrelatedFourPathEndpoint G u) :
      R ^ 2 *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) / 27 ≤
        ((weight v).choose 3 : ℝ) := by
    split_ifs with hv
    · have htReal : (3 : ℝ) ≤ (weight v : ℝ) := hRthree.trans hv
      have ht : 3 ≤ weight v := by exact_mod_cast htReal
      have hsquare : R ^ 2 ≤ (weight v : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hR
          (sub_nonneg.mpr hv),
          mul_nonneg (Nat.cast_nonneg (weight v))
            (sub_nonneg.mpr hv)]
      have hcubic :
          R ^ 2 * (weight v : ℝ) ≤ (weight v : ℝ) ^ 3 := by
        calc
          R ^ 2 * (weight v : ℝ) ≤
              (weight v : ℝ) ^ 2 * (weight v : ℝ) :=
            mul_le_mul_of_nonneg_right hsquare
              (Nat.cast_nonneg (weight v))
          _ = (weight v : ℝ) ^ 3 := by ring
      calc
        R ^ 2 * (weight v : ℝ) / 27 ≤
            (weight v : ℝ) ^ 3 / 27 := by linarith
        _ ≤ ((weight v).choose 3 : ℝ) :=
          choose_three_cubic_lower ht
    · simp
  change R ^ 2 * (p : ℝ) / 54 ≤
    (commonSecondNeighborTripleMass G u : ℝ)
  calc
    R ^ 2 * (p : ℝ) / 54 =
        (R ^ 2 / 27) * ((p : ℝ) / 2) := by ring
    _ ≤ (R ^ 2 / 27) *
        finiteHeavyFiberMass weight (Fintype.card V) p :=
      mul_le_mul_of_nonneg_left hheavy (by positivity)
    _ = ∑ v : UnrelatedFourPathEndpoint G u,
          R ^ 2 *
            (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) /
              27 := by
      simp only [finiteHeavyFiberMass, Finset.mul_sum]
      apply Finset.sum_congr
      · rfl
      · intro v hv
        change (R ^ 2 / 27) *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) = _
        ring
    _ ≤ ∑ v : UnrelatedFourPathEndpoint G u,
          ((weight v).choose 3 : ℝ) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (commonSecondNeighborTripleMass G u : ℝ) := by
      simp [commonSecondNeighborTripleMass, weight]

theorem proposedFamilyFree_four_path_triple_mass_lower
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (u : Fin n)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass host u : ℝ) := by
  have hthreshold' : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card (Fin n))
        (d * (d - 1) ^ 3) := by
    simpa using hthreshold
  simpa using four_path_common_second_neighbor_triple_mass_lower
    host hbip (proposedFamilyFree_four_cycle hfree)
    (proposedFamilyFree_six_cycle hfree) d hdegree u hthreshold'

end ActualTripleSupersaturation

section OrderedThetaTripleCounting

noncomputable def orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n)) : ℕ :=
  ∑ y : Fin n, ∑ z : Fin n, (thetaBaseExtensions host y z).card

lemma orderedThetaTripleCount_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    orderedThetaTripleCount host * d ≤ n ^ 3 := by
  classical
  calc
    orderedThetaTripleCount host * d =
        ∑ y : Fin n, ∑ z : Fin n,
          (thetaBaseExtensions host y z).card * d := by
      simp [orderedThetaTripleCount, Finset.sum_mul]
    _ ≤ ∑ _y : Fin n, ∑ _z : Fin n, n := by
      gcongr with y _ z _
      exact thetaBaseExtensions_card_mul_degree_le
        host hfree hbip d hdegree y z
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]

end OrderedThetaTripleCounting

section ActualGammaAndKForcing

variable {V : Type*} [Fintype V] [DecidableEq V]

def GammaGood (G : SimpleGraph V) (u : V) : Prop :=
  ∃ witness : SimpleGraph.Copy gammaGraph G,
    witness kSpecifiedCenter = u

lemma gammaGood_of_three_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    {u : V}
    (hu : u ∈ tripleCommonCenters G base)
    (hcenters : 3 ≤ (tripleCommonCenters G base).card) :
    GammaGood G u := by
  classical
  have herase :
      1 < ((tripleCommonCenters G base).erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp herase
  have hfirstne : first ≠ u := (Finset.mem_erase.mp hfirst).1
  have hsecondne : second ≠ u := (Finset.mem_erase.mp hsecond).1
  have hfirstmem : first ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hfirst).2
  have hsecondmem : second ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hsecond).2
  let center : Fin 3 → V := ![u, first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base u).mp hu i
    · exact (mem_tripleCommonCenters G base first).mp hfirstmem i
    · exact (mem_tripleCommonCenters G base second).mp hsecondmem i
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_⟩
  rfl

lemma gamma_base_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma gamma_center_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gammaCopy_vertex_color_false_iff
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (witness : SimpleGraph.Copy gammaGraph G)
    (vertex : SubdivisionVertex 3) :
    subdivisionColor 3 vertex = false ↔
      color (witness vertex) = color (witness kSpecifiedCenter) := by
  rcases vertex with (base | center) | pair
  · simp only [subdivisionColor, true_iff]
    exact bipartite_coloring_eq_of_common_neighbor color
      (witness.toHom.map_rel (gamma_base_pair_adj base 0))
      (witness.toHom.map_rel (gamma_center_pair_adj base 0))
  · simp only [subdivisionColor, true_iff]
    calc
      color (witness (.inl (.inr center))) =
          color (witness (.inl (.inl (0 : Fin 3)))) :=
        (bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 center))
          (witness.toHom.map_rel
            (gamma_center_pair_adj 0 center))).symm
      _ = color (witness kSpecifiedCenter) :=
        bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 0))
          (witness.toHom.map_rel (gamma_center_pair_adj 0 0))
  · rcases pair with ⟨base, center⟩
    simp only [subdivisionColor, Bool.true_eq_false, false_iff]
    intro heq
    have hbase :
        color (witness (.inl (.inl base))) =
          color (witness kSpecifiedCenter) :=
      bipartite_coloring_eq_of_common_neighbor color
        (witness.toHom.map_rel (gamma_base_pair_adj base 0))
        (witness.toHom.map_rel (gamma_center_pair_adj base 0))
    exact (color.valid
      (witness.toHom.map_rel (gamma_base_pair_adj base center)))
        (hbase.trans heq.symm)

def gluedKVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (vertex : KVertex) : V :=
  copies vertex.1 vertex.2

lemma subdivisionRelation_adj
    {k : ℕ} {source target : SubdivisionVertex k}
    (hedge : subdivisionRelation k source target) :
    (SubdivisionGraph k).Adj source target := by
  rcases source with (base | center) | pair <;>
    rcases target with (targetBase | targetCenter) | targetPair <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    {source target : KVertex}
    (hedge : kTemplateRelation source target) :
    G.Adj (gluedKVertex copies source)
      (gluedKVertex copies target) := by
  rcases hedge with hcopy | hjoin
  · obtain ⟨hindex, hsubdivision⟩ := hcopy
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = index' at hindex
    subst index'
    exact (copies index).toHom.map_rel
      (subdivisionRelation_adj hsubdivision)
  · obtain ⟨hsource, htarget, hvertex, hvertex'⟩ := hjoin
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = 0 at hsource
    change index' = 1 at htarget
    subst index
    subst index'
    change vertex = kSpecifiedCenter at hvertex
    change vertex' = kSpecifiedCenter at hvertex'
    subst vertex
    subst vertex'
    exact hjoining

def gluedKHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    kTemplate →g G where
  toFun := gluedKVertex copies
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      kTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedKVertex_map_relation copies hjoining hforward
    · exact (gluedKVertex_map_relation
        copies hjoining hbackward).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (index : Fin 2) :
    Set.InjOn (gluedKHom copies hjoining)
      {vertex : KVertex | vertex.1 = index} := by
  rintro ⟨leftIndex, leftVertex⟩ hleft
    ⟨rightIndex, rightVertex⟩ hright heq
  change leftIndex = index at hleft
  change rightIndex = index at hright
  subst leftIndex
  subst rightIndex
  change copies index leftVertex = copies index rightVertex at heq
  have hvertices := (copies index).injective heq
  subst rightVertex
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (color : G.Coloring (Fin 2))
    (vertex : KVertex) :
    kColor vertex = false ↔
      color (gluedKVertex copies vertex) =
        color (copies 0 kSpecifiedCenter) := by
  rcases vertex with ⟨index, vertex⟩
  fin_cases index
  · simpa [kColor, gluedKVertex] using
      (gammaCopy_vertex_color_false_iff color (copies 0) vertex)
  · have hvalid :
        color (copies 0 kSpecifiedCenter) ≠
          color (copies 1 kSpecifiedCenter) :=
        color.valid hjoining
    change
      (if (1 : Fin 2) = 0 then subdivisionColor 3 vertex
        else !(subdivisionColor 3 vertex)) = false ↔
        color (copies 1 vertex) = color (copies 0 kSpecifiedCenter)
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    cases hcolor : subdivisionColor 3 vertex
    · simp only [Bool.not_false, Bool.true_eq_false, false_iff]
      intro heq
      have hsame :
          color (copies 1 vertex) =
            color (copies 1 kSpecifiedCenter) :=
        (gammaCopy_vertex_color_false_iff
          color (copies 1) vertex).mp hcolor
      exact hvalid (heq.symm.trans hsame)
    · simp only [Bool.not_true, true_iff]
      have hdistinct :
          color (copies 1 vertex) ≠
            color (copies 1 kSpecifiedCenter) := by
        intro heq
        have hfalse :=
          (gammaCopy_vertex_color_false_iff
            color (copies 1) vertex).mpr heq
        simp [hcolor] at hfalse
      apply Fin.ext
      omega

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    ∀ left right,
      gluedKHom copies hjoining left =
        gluedKHom copies hjoining right →
      kColor left = kColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hhostColor :
      color (gluedKVertex copies left) =
        color (gluedKVertex copies right) :=
    congrArg color heq
  cases hleft : kColor left <;> cases hright : kColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mp hleft
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mpr
        (hhostColor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mp hright
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mpr
        (hhostColor.trans hbase)
    simp [hleft] at hfalse
  · rfl

theorem proposedFamilyFree_not_adj_gammaGood
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hu : GammaGood host u) (hv : GammaGood host v) :
    ¬ host.Adj u v := by
  obtain ⟨first, hfirst⟩ := hu
  obtain ⟨second, hsecond⟩ := hv
  intro hedge
  let copies : Fin 2 → SimpleGraph.Copy gammaGraph host :=
    ![first, second]
  have hjoining :
      host.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter) := by
    change host.Adj (first kSpecifiedCenter)
      (second kSpecifiedCenter)
    rwa [hfirst, hsecond]
  exact proposedFamilyFree_no_kTemplate hfree
    (gluedKHom copies hjoining)
    (gluedKHom_color_respecting hbip copies hjoining)
    (gluedKHom_injOn_marked_copy copies hjoining)

end ActualGammaAndKForcing

section ActualBadVertexEdgeCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def gammaBadVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ GammaGood G v

omit [DecidableEq V] in
lemma mem_gammaBadVertices (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by
  classical
  simp [gammaBadVertices]

theorem proposedFamilyFree_edge_has_gammaBad
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hedge : host.Adj u v) :
    u ∈ gammaBadVertices host ∨ v ∈ gammaBadVertices host := by
  classical
  by_cases hu : GammaGood host u
  · right
    apply (mem_gammaBadVertices host v).mpr
    intro hv
    exact proposedFamilyFree_not_adj_gammaGood
      host hfree hbip hu hv hedge
  · left
    exact (mem_gammaBadVertices host u).mpr hu

lemma edgeFinset_card_le_sum_degree_of_vertex_cover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover : Finset V)
    (hcover : ∀ ⦃u v : V⦄, G.Adj u v →
      u ∈ cover ∨ v ∈ cover) :
    G.edgeFinset.card ≤ ∑ v ∈ cover, G.degree v := by
  classical
  have hsubset :
      G.edgeFinset ⊆ cover.biUnion (fun v => G.incidenceFinset v) := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hedge
      rcases hcover hadj with hu | hv
      · exact Finset.mem_biUnion.mpr
          ⟨u, hu, (G.mem_incidenceFinset u _).mpr
            (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨v, hv, (G.mem_incidenceFinset v _).mpr
            (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩
  calc
    G.edgeFinset.card ≤
        (cover.biUnion fun v => G.incidenceFinset v).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ cover, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ cover, G.degree v := by
      simp

theorem proposedFamilyFree_edge_card_le_gammaBad_degree_sum
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite) :
    host.edgeFinset.card ≤
      ∑ v ∈ gammaBadVertices host, host.degree v :=
  edgeFinset_card_le_sum_degree_of_vertex_cover
    host (gammaBadVertices host)
    (fun _ _ hedge => proposedFamilyFree_edge_has_gammaBad
      host hfree hbip hedge)

end ActualBadVertexEdgeCounting

end Supersaturation

noncomputable section BadVertexCounting

open Finset SimpleGraph

noncomputable def finiteBadFiberMass
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop) : ℕ := by
  classical
  exact ∑ index : α,
    ((fibers index).filter fun vertex => ¬ good vertex).card

lemma finite_bad_fiber_card_le_two
    {α β : Type*} [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    [DecidablePred good]
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex)
    (index : α) :
    ((fibers index).filter fun vertex => ¬ good vertex).card ≤ 2 := by
  classical
  by_cases hlarge : 3 ≤ (fibers index).card
  · have hempty :
        (fibers index).filter (fun vertex => ¬ good vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro vertex hvertex hbad
      exact hbad (hgood index vertex hvertex hlarge)
    simp [hempty]
  · have hcard :=
      Finset.card_filter_le (fibers index)
        (fun vertex => ¬ good vertex)
    omega

lemma finite_bad_fiber_mass_le_two
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex) :
    finiteBadFiberMass fibers good ≤ 2 * Fintype.card α := by
  classical
  simpa [finiteBadFiberMass, Nat.mul_comm] using
    Finset.sum_le_card_nsmul Finset.univ
      (fun index => ((fibers index).filter fun vertex => ¬ good vertex).card)
      2 (fun index _ => finite_bad_fiber_card_le_two fibers good hgood index)

section ActualIndependentTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ vertex ∈ base, CommonNeighborRelated G vertex center

lemma mem_commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) (center : V) :
    center ∈ commonCenterFinset G base ↔
      ∀ vertex ∈ base, CommonNeighborRelated G vertex center := by
  classical
  simp [commonCenterFinset]

def IsIndependentThetaTriple
    (G : SimpleGraph V) (base : Finset V) : Prop :=
  base.card = 3 ∧
    (base : Set V).Pairwise
      (fun first second => ¬ CommonNeighborRelated G first second) ∧
    2 ≤ (commonCenterFinset G base).card

abbrev IndependentThetaTriple (G : SimpleGraph V) :=
  {base : Finset V // IsIndependentThetaTriple G base}

noncomputable instance independentThetaTripleFintype
    (G : SimpleGraph V) : Fintype (IndependentThetaTriple G) :=
  Fintype.ofFinite _

abbrev OrderedThetaWitness (G : SimpleGraph V) :=
  Σ first : V, Σ second : V,
    {third : V // third ∈ thetaBaseExtensions G first second}

noncomputable def independentThetaTripleBase
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Fin 3 → V :=
  fun index =>
    ((Finset.equivFinOfCardEq triple.property.1).symm index : triple.val)

lemma independentThetaTripleBase_injective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Function.Injective (independentThetaTripleBase G triple) := by
  intro first second heq
  apply (Finset.equivFinOfCardEq triple.property.1).symm.injective
  exact Subtype.ext heq

lemma independentThetaTripleBase_mem
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    (index : Fin 3) :
    independentThetaTripleBase G triple index ∈ triple.val :=
  ((Finset.equivFinOfCardEq triple.property.1).symm index).property

lemma independentThetaTripleBase_surjective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    {vertex : V} (hvertex : vertex ∈ triple.val) :
    ∃ index : Fin 3,
      independentThetaTripleBase G triple index = vertex := by
  let member : triple.val := ⟨vertex, hvertex⟩
  refine ⟨Finset.equivFinOfCardEq triple.property.1 member, ?_⟩
  change (((Finset.equivFinOfCardEq triple.property.1).symm
    (Finset.equivFinOfCardEq triple.property.1 member) : triple.val) : V) =
      vertex
  simp [member]

lemma commonCenterFinset_eq_tripleCommonCenters
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    commonCenterFinset G triple.val =
      tripleCommonCenters G (independentThetaTripleBase G triple) := by
  classical
  ext center
  rw [mem_commonCenterFinset, mem_tripleCommonCenters]
  constructor
  · intro hcenter index
    exact hcenter _ (independentThetaTripleBase_mem G triple index)
  · intro hcenter vertex hvertex
    obtain ⟨index, rfl⟩ :=
      independentThetaTripleBase_surjective G triple hvertex
    exact hcenter index

lemma independentThetaTripleBase_unrelated
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    ⦃first second : Fin 3⦄ (hne : first ≠ second) :
    ¬ CommonNeighborRelated G
      (independentThetaTripleBase G triple first)
      (independentThetaTripleBase G triple second) := by
  apply triple.property.2.1
    (independentThetaTripleBase_mem G triple first)
    (independentThetaTripleBase_mem G triple second)
  exact fun heq =>
    hne (independentThetaTripleBase_injective G triple heq)

lemma gammaGood_of_independentThetaTriple_fiber
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) (vertex : V)
    (hvertex : vertex ∈ commonCenterFinset G triple.val)
    (hcard : 3 ≤ (commonCenterFinset G triple.val).card) :
    GammaGood G vertex := by
  apply gammaGood_of_three_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hvertex
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hcard

noncomputable def independentThetaTripleOrderedWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) : OrderedThetaWitness G := by
  refine ⟨independentThetaTripleBase G triple 1,
    independentThetaTripleBase G triple 2,
    ⟨independentThetaTripleBase G triple 0, ?_⟩⟩
  apply mem_thetaBaseExtensions_of_two_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  rw [← commonCenterFinset_eq_tripleCommonCenters]
  exact triple.property.2.2

lemma independentThetaTripleOrderedWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (independentThetaTripleOrderedWitness G hbip hfour hsix) := by
  intro left right heq
  have hbase : independentThetaTripleBase G left =
      independentThetaTripleBase G right := by
    funext index
    fin_cases index
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.2.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.1) heq
  apply Subtype.ext
  ext vertex
  constructor
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G left hvertex
    rw [hbase]
    exact independentThetaTripleBase_mem G right index
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G right hvertex
    rw [← hbase]
    exact independentThetaTripleBase_mem G left index

lemma orderedThetaWitness_card
    {n : ℕ} (host : SimpleGraph (Fin n)) :
    Fintype.card (OrderedThetaWitness host) =
      orderedThetaTripleCount host := by
  classical
  simp [OrderedThetaWitness, orderedThetaTripleCount,
    Fintype.card_sigma, Fintype.card_coe]

lemma independentThetaTriple_card_le_orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    Fintype.card (IndependentThetaTriple host) ≤
      orderedThetaTripleCount host := by
  calc
    Fintype.card (IndependentThetaTriple host) ≤
        Fintype.card (OrderedThetaWitness host) :=
      Fintype.card_le_of_injective
        (independentThetaTripleOrderedWitness host hbip hfour hsix)
        (independentThetaTripleOrderedWitness_injective
          host hbip hfour hsix)
    _ = orderedThetaTripleCount host := orderedThetaWitness_card host

theorem gamma_bad_triple_fiber_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    finiteBadFiberMass
        (fun triple : IndependentThetaTriple host =>
          commonCenterFinset host triple.val)
        (GammaGood host) ≤
      2 * orderedThetaTripleCount host := by
  exact (finite_bad_fiber_mass_le_two _ _ (fun triple vertex hvertex hcard =>
    gammaGood_of_independentThetaTriple_fiber
      host hbip hfour hsix triple vertex hvertex hcard)).trans
    (Nat.mul_le_mul_left 2
      (independentThetaTriple_card_le_orderedThetaTripleCount
        host hbip hfour hsix))

end ActualIndependentTriples

end BadVertexCounting

noncomputable section TripleMassIncidence

open Finset SimpleGraph

section TripleIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonSecondNeighborFinset
    (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x

omit [DecidableEq V] in
lemma mem_commonSecondNeighborFinset
    (G : SimpleGraph V) (u v x : V) :
    x ∈ commonSecondNeighborFinset G u v ↔
      CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x := by
  classical
  simp [commonSecondNeighborFinset]

omit [DecidableEq V] in
lemma commonSecondNeighborFinset_card
    (G : SimpleGraph V) (u v : V) :
    (commonSecondNeighborFinset G u v).card =
      Fintype.card (CommonSecondNeighbor G u v) := by
  classical
  rw [Fintype.card_subtype]
  rfl

abbrev BadFourPathTripleWitness (G : SimpleGraph V) :=
  Σ center : {u : V // ¬ GammaGood G u},
    Σ endpoint : UnrelatedFourPathEndpoint G (center : V),
      {base : Finset V //
        base ∈ (commonSecondNeighborFinset G
          (center : V) (endpoint : V)).powersetCard 3}

abbrev BadIndependentTripleWitness (G : SimpleGraph V) :=
  Σ triple : IndependentThetaTriple G,
    {center : V // center ∈ commonCenterFinset G triple.val ∧
      ¬ GammaGood G center}

noncomputable instance badFourPathTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadFourPathTripleWitness G) := by
  classical
  infer_instance

noncomputable instance badIndependentTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadIndependentTripleWitness G) := by
  classical
  infer_instance

noncomputable def fourPathTripleToIndependentThetaTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    IndependentThetaTriple G := by
  have hsubset :
      base.val ⊆ commonSecondNeighborFinset G u (endpoint : V) :=
    (Finset.mem_powersetCard.mp base.property).1
  refine ⟨base.val, ?_, ?_, ?_⟩
  · exact (Finset.mem_powersetCard.mp base.property).2
  · intro x hx y hy hne
    have hx' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)
    have hy' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) y).mp (hsubset hy)
    exact common_second_neighbor_pairwise_unrelated
      G hbip hfour hsix endpoint.property.1 endpoint.property.2
      (⟨x, hx'⟩ : CommonSecondNeighbor G u (endpoint : V))
      (⟨y, hy'⟩ : CommonSecondNeighbor G u (endpoint : V))
  · have hu : u ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val u).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).1
    have hv : (endpoint : V) ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).2
    have hcard : 1 < (commonCenterFinset G base.val).card :=
      Finset.one_lt_card.mpr
        ⟨u, hu, (endpoint : V), hv, endpoint.property.1⟩
    omega

lemma fourPathTripleToIndependentThetaTriple_center_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    u ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change u ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val u).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).1

lemma fourPathTripleToIndependentThetaTriple_endpoint_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    (endpoint : V) ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change (endpoint : V) ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).2

lemma badIndependentThetaTriple_other_center_unique
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G)
    (u : V)
    (hu : u ∈ commonCenterFinset G triple.val)
    (hbad : ¬ GammaGood G u)
    {v w : V}
    (hv : v ∈ commonCenterFinset G triple.val)
    (hw : w ∈ commonCenterFinset G triple.val)
    (huv : u ≠ v) (huw : u ≠ w) :
    v = w := by
  classical
  by_contra hvw
  have hsubset :
      ({u, v, w} : Finset V) ⊆ commonCenterFinset G triple.val := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hcard : 3 ≤ (commonCenterFinset G triple.val).card := by
    calc
      3 = ({u, v, w} : Finset V).card := by
        simp [huv, huw, hvw]
      _ ≤ (commonCenterFinset G triple.val).card :=
        Finset.card_le_card hsubset
  exact hbad (gammaGood_of_independentThetaTriple_fiber
    G hbip hfour hsix triple u hu hcard)

noncomputable def badFourPathTripleToBadIndependentTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    BadFourPathTripleWitness G → BadIndependentTripleWitness G := by
  rintro ⟨center, endpoint, base⟩
  refine ⟨fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix center endpoint base, ?_⟩
  refine ⟨center, ?_, center.property⟩
  exact fourPathTripleToIndependentThetaTriple_center_mem
    G hbip hfour hsix center endpoint base

lemma badFourPathTripleToBadIndependentTriple_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (badFourPathTripleToBadIndependentTriple
        G hbip hfour hsix) := by
  rintro ⟨u, v, base⟩ ⟨u', v', base'⟩ heq
  have hcenter := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      (witness.2 : V)) heq
  change (u : V) = (u' : V) at hcenter
  have husub : u = u' := Subtype.ext hcenter
  subst u'
  have hbase := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      witness.1.val) heq
  change base.val = base'.val at hbase
  let triple := fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix (u : V) v base
  have hu : (u : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_center_mem
      G hbip hfour hsix (u : V) v base
  have hv : (v : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v base
  have hv' : (v' : V) ∈ commonCenterFinset G triple.val := by
    change (v' : V) ∈ commonCenterFinset G base.val
    rw [hbase]
    exact fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v' base'
  have hendpoint : (v : V) = (v' : V) :=
    badIndependentThetaTriple_other_center_unique
      G hbip hfour hsix triple (u : V) hu u.property hv hv'
      v.property.1 v'.property.1
  have hvsub : v = v' := Subtype.ext hendpoint
  subst v'
  have hbasesub : base = base' := Subtype.ext hbase
  subst base'
  rfl

omit [DecidableEq V] in
lemma badFourPathTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadFourPathTripleWitness G) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_coe,
    Finset.card_powersetCard, commonSecondNeighborFinset_card]
  change
    (∑ u : {u : V // ¬ GammaGood G u},
      commonSecondNeighborTripleMass G u) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u
  symm
  apply Finset.sum_subtype
    (gammaBadVertices G)
    (fun u => (mem_gammaBadVertices G u))

lemma badIndependentTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadIndependentTripleWitness G) =
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  classical
  rw [Fintype.card_sigma]
  unfold finiteBadFiberMass
  apply Finset.sum_congr
  · rfl
  · intro triple htriple
    rw [Fintype.card_subtype]
    congr 1
    ext center
    simp

lemma gammaBad_four_path_triple_mass_le_bad_fiber_mass
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    (∑ u ∈ gammaBadVertices G,
      commonSecondNeighborTripleMass G u) ≤
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  rw [← badFourPathTripleWitness_card,
    ← badIndependentTripleWitness_card]
  exact Fintype.card_le_of_injective
    (badFourPathTripleToBadIndependentTriple
      G hbip hfour hsix)
    (badFourPathTripleToBadIndependentTriple_injective
      G hbip hfour hsix)

theorem gammaBad_four_path_triple_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    (∑ u ∈ gammaBadVertices host,
      commonSecondNeighborTripleMass host u) ≤
      2 * orderedThetaTripleCount host := by
  exact (gammaBad_four_path_triple_mass_le_bad_fiber_mass
    host hbip hfour hsix).trans
      (gamma_bad_triple_fiber_mass_le_two_orderedTheta
        host hbip hfour hsix)

lemma gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        (fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54) ≤
      2 * (orderedThetaTripleCount host : ℝ) := by
  classical
  let lower : ℝ :=
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54
  have hpoint (u : Fin n) :
      lower ≤ (commonSecondNeighborTripleMass host u : ℝ) := by
    exact proposedFamilyFree_four_path_triple_mass_lower
      host hfree hbip d hdegree u hthreshold
  change ((gammaBadVertices host).card : ℝ) * lower ≤
    2 * (orderedThetaTripleCount host : ℝ)
  calc
    ((gammaBadVertices host).card : ℝ) * lower =
        ∑ u ∈ gammaBadVertices host, lower := by simp
    _ ≤ ∑ u ∈ gammaBadVertices host,
        (commonSecondNeighborTripleMass host u : ℝ) := by
      gcongr with u hu
      exact hpoint u
    _ = ((∑ u ∈ gammaBadVertices host,
          commonSecondNeighborTripleMass host u) : ℝ) := by
      simp
    _ ≤ ((2 * orderedThetaTripleCount host : ℕ) : ℝ) := by
      exact_mod_cast
        (gammaBad_four_path_triple_mass_le_two_orderedTheta
          host hbip (proposedFamilyFree_four_cycle hfree)
          (proposedFamilyFree_six_cycle hfree))
    _ = 2 * (orderedThetaTripleCount host : ℝ) := by
      norm_num

theorem gammaBad_card_mul_fourpath_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (gammaBadVertices host).card *
      (d * (d - 1) ^ 3) ^ 3 * d ≤ 432 * n ^ 5 := by
  have hn : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst n
    norm_num [fourPathHeavyThreshold] at hthreshold
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let p : ℕ := d * (d - 1) ^ 3
  let bad : ℕ := (gammaBadVertices host).card
  let theta : ℕ := orderedThetaTripleCount host
  have hmass :
      (bad : ℝ) *
        (fourPathHeavyThreshold n p ^ 2 *
          (p : ℝ) / 54) ≤ 2 * (theta : ℝ) := by
    exact gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
      host hfree hbip d hdegree hthreshold
  have hnormalized :
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) ≤ 2 * (theta : ℝ) := by
    calc
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) =
        (bad : ℝ) *
          (fourPathHeavyThreshold n p ^ 2 * (p : ℝ) / 54) := by
            unfold fourPathHeavyThreshold
            field_simp [ne_of_gt hnReal]
            ring
      _ ≤ 2 * (theta : ℝ) := hmass
  have hden : 0 < (216 : ℝ) * (n : ℝ) ^ 2 := by
    positivity
  have hclear := (div_le_iff₀ hden).mp hnormalized
  have hbadpoly :
      (bad : ℝ) * (p : ℝ) ^ 3 ≤
        432 * (theta : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith
  have htheta :
      (theta : ℝ) * (d : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast
      (orderedThetaTripleCount_mul_degree_le
        host hfree hbip d hdegree)
  have hfinal :
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 5 := by
    calc
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
          (432 * (theta : ℝ) * (n : ℝ) ^ 2) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hbadpoly (Nat.cast_nonneg d)
      _ = 432 * ((theta : ℝ) * (d : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ 432 * (n : ℝ) ^ 3 * (n : ℝ) ^ 2 := by
        gcongr
      _ = 432 * (n : ℝ) ^ 5 := by ring
  exact_mod_cast hfinal

theorem proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n := by
  classical
  calc
    host.edgeFinset.card * (d - 1) ^ 2 ≤
        (∑ u ∈ gammaBadVertices host, host.degree u) *
          (d - 1) ^ 2 :=
      Nat.mul_le_mul_right ((d - 1) ^ 2)
        (proposedFamilyFree_edge_card_le_gammaBad_degree_sum
          host hfree hbip)
    _ = ∑ u ∈ gammaBadVertices host,
        host.degree u * (d - 1) ^ 2 := by
      simp [Finset.sum_mul]
    _ ≤ ∑ _u ∈ gammaBadVertices host, n := by
      gcongr with u hu
      simpa using girthEight_degree_mul_pred_sq_le_card
        host hbip (proposedFamilyFree_four_cycle hfree)
        (proposedFamilyFree_six_cycle hfree) d hdegree u
    _ = (gammaBadVertices host).card * n := by simp

lemma fourPathHeavyThreshold_low_degree_fourth_le
    (N d : ℕ)
    (hN : 0 < N)
    (hd : 2 ≤ d)
    (hlow : ¬ (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 4 ≤ 48 * (N : ℝ) := by
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hthreshold :
      fourPathHeavyThreshold N (d * (d - 1) ^ 3) < 3 :=
    lt_of_not_ge hlow
  have hp :
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) < 6 * (N : ℝ) := by
    unfold fourPathHeavyThreshold at hthreshold
    have hden : 0 < 2 * (N : ℝ) := by positivity
    have hclear := (div_lt_iff₀ hden).mp hthreshold
    nlinarith
  have hpredNat : d ≤ 2 * (d - 1) := by omega
  have hpredReal : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredNat
  have hpowers :
      (d : ℝ) ^ 3 ≤ (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 := by
    gcongr
  have hfourth :
      (d : ℝ) ^ 4 ≤
        8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
    calc
      (d : ℝ) ^ 4 = (d : ℝ) * (d : ℝ) ^ 3 := by ring
      _ ≤ (d : ℝ) *
          (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left hpowers (Nat.cast_nonneg d)
      _ = 8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
        push_cast
        ring
  nlinarith

end TripleIncidence

end TripleMassIncidence

noncomputable section QuantitativeBadVertexBound

open Finset SimpleGraph

lemma quantitative_minimum_degree_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    n * d ≤ 2 * host.edgeFinset.card := by
  simpa [SimpleGraph.sum_degrees_eq_twice_card_edges] using
    Finset.card_nsmul_le_sum Finset.univ
      (fun vertex : Fin n => host.degree vertex) d
      (fun vertex _ => hdegree vertex)

lemma quantitative_bad_vertex_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n :=
  proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    host hfree hbip d hdegree

lemma quantitative_bad_vertex_heavy_triple_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
      432 * (n : ℝ) ^ 5 := by
  apply (mul_le_mul_iff_right₀
    (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  exact_mod_cast Nat.mul_le_mul_left n
    (gammaBad_card_mul_fourpath_power_le
      host hfree hbip d hdegree hthreshold)

theorem proposedFamilyFree_minDegree_polynomial_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 ≤
      864 * (n : ℝ) ^ 5 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdegreeReal :
      (n : ℝ) * (d : ℝ) ≤ 2 * (host.edgeFinset.card : ℝ) := by
    exact_mod_cast quantitative_minimum_degree_edge_bound
      host d hdegree
  have hedgeReal :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 ≤
        ((gammaBadVertices host).card : ℝ) * (n : ℝ) := by
    exact_mod_cast quantitative_bad_vertex_edge_bound
      host hfree hbip d hdegree
  have hbadReal := quantitative_bad_vertex_heavy_triple_bound
    host hn hfree hbip d hdegree hthreshold
  have hedgePolynomial :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 6 := by
    calc
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
          (((gammaBadVertices host).card : ℝ) * (n : ℝ)) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) := by
        gcongr
      _ = (((gammaBadVertices host).card : ℝ) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) *
            (n : ℝ) := by ring
      _ ≤ (432 * (n : ℝ) ^ 5) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hbadReal (Nat.cast_nonneg n)
      _ = 432 * (n : ℝ) ^ 6 := by ring
  apply (mul_le_mul_iff_right₀ hnreal).mp
  calc
    (n : ℝ) *
        ((d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3) =
        ((n : ℝ) * (d : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ (2 * (host.edgeFinset.card : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      gcongr
    _ = 2 *
          ((host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ 2 * (432 * (n : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left hedgePolynomial (by norm_num)
    _ = (n : ℝ) * (864 * (n : ℝ) ^ 5) := by ring

theorem proposedFamilyFree_minDegree_sixteenth_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hd : 2 ≤ d)
    (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 16 ≤ 1769472 * (n : ℝ) ^ 5 := by
  have hraw := proposedFamilyFree_minDegree_polynomial_le
    host hn hfree hbip d hdegree hthreshold
  have hshape :
      (d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11 ≤
        864 * (n : ℝ) ^ 5 := by
    convert hraw using 1
    push_cast
    ring
  have hdone : 1 ≤ d := by omega
  have hhalf : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdone, Nat.cast_one]
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  calc
    (d : ℝ) ^ 16 = (d : ℝ) ^ 5 * (d : ℝ) ^ 11 := by ring
    _ ≤ (d : ℝ) ^ 5 *
        (2 * ((d - 1 : ℕ) : ℝ)) ^ 11 := by
      gcongr
    _ = 2 ^ (11 : ℕ) *
        ((d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11) := by ring
    _ ≤ 2 ^ (11 : ℕ) * (864 * (n : ℝ) ^ 5) := by
      gcongr
    _ = 1769472 * (n : ℝ) ^ 5 := by ring

end QuantitativeBadVertexBound

noncomputable section LineCoordinates

variable (K : Type*) [Field K]

def symplecticHorizontalVector (x y : K) : SymplecticVector K :=
  ![x, 0, y, 0]

def symplecticAnnihilatorVector (x y : K) : SymplecticVector K :=
  ![0, -y, 0, x]

def symmetricGraphVector (a b c x y : K) : SymplecticVector K :=
  ![x, a * x + b * y, y, b * x + c * y]

lemma symmetricGraphVector_orthogonal
    (a b c x y x' y' : K) :
    standardSymplecticForm K
      (symmetricGraphVector K a b c x y)
      (symmetricGraphVector K a b c x' y') = 0 := by
  simp [standardSymplecticForm, symmetricGraphVector]
  ring

def coordinateCenterLinearMap (x y : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h :=
    h 0 • symplecticHorizontalVector K x y +
      h 1 • symplecticAnnihilatorVector K x y
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, smul_eq_mul] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

lemma coordinateCenterLinearMap_injective
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    Function.Injective (coordinateCenterLinearMap K x y) := by
  intro u v huv
  have hzero := congrFun huv 0
  have hone := congrFun huv 1
  have htwo := congrFun huv 2
  have hthree := congrFun huv 3
  simp [coordinateCenterLinearMap, symplecticHorizontalVector,
    symplecticAnnihilatorVector, smul_eq_mul]
    at hzero hone htwo hthree
  funext i
  fin_cases i
  · rcases hxy with hx | hy
    · exact hzero.resolve_right hx
    · exact htwo.resolve_right hy
  · rcases hxy with hx | hy
    · exact hthree.resolve_right hx
    · exact hone.resolve_right hy

def coordinateCenterLine (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0) :
    SymplecticLine K :=
  ⟨LinearMap.range (coordinateCenterLinearMap K x y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (coordinateCenterLinearMap_injective K hxy)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [coordinateCenterLinearMap, standardSymplecticForm,
        symplecticHorizontalVector, symplecticAnnihilatorVector,
        smul_eq_mul]
      ring⟩

def symmetricGraphLinearMap (a b c : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h := symmetricGraphVector K a b c (h 0) (h 1)
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.add_apply] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.smul_apply, smul_eq_mul] <;> ring

lemma symmetricGraphLinearMap_injective
    (a b c : K) :
    Function.Injective (symmetricGraphLinearMap K a b c) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      congrFun huv 0
  · simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      congrFun huv 2

def symmetricGraphLine (a b c : K) : SymplecticLine K :=
  ⟨LinearMap.range (symmetricGraphLinearMap K a b c), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symmetricGraphLinearMap_injective K a b c)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact symmetricGraphVector_orthogonal K a b c
        (u' 0) (u' 1) (v' 0) (v' 1)⟩

lemma symmetricGraphVector_mem_center_span_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ s t : K,
      symmetricGraphVector K a b c x y =
        s • symplecticHorizontalVector K x y +
          t • symplecticAnnihilatorVector K x y) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨s, t, hvector⟩
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp [symmetricGraphVector, symplecticHorizontalVector,
      symplecticAnnihilatorVector, Pi.add_apply,
      smul_eq_mul] at hzero hone htwo hthree
    have hs : s = 1 := by
      rcases hxy with hx | hy
      · have hproduct : (s - 1) * x = 0 := by
          linear_combination -hzero
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hx)
      · have hproduct : (s - 1) * y = 0 := by
          linear_combination -htwo
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hy)
    subst s
    rw [symmetricQuadratic_eq_bilinear]
    linear_combination x * hone + y * hthree
  · intro hquadratic
    have hbilinear :
        x * (a * x + b * y) + y * (b * x + c * y) = 0 := by
      simpa [symmetricQuadratic_eq_bilinear] using hquadratic
    rcases hxy with hx | hy
    · refine ⟨1, (b * x + c * y) / x, ?_⟩
      funext i
      fin_cases i
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul]
        field_simp [hx]
        linear_combination hbilinear
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul, hx]
    · refine ⟨1, -(a * x + b * y) / y, ?_⟩
      funext i
      fin_cases i
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul, hy]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector]
      · simp [symmetricGraphVector, symplecticHorizontalVector,
          symplecticAnnihilatorVector, Pi.add_apply,
          smul_eq_mul]
        field_simp [hy]
        linear_combination hbilinear

lemma symmetricGraphLine_coordinateCenter_intersection_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ w : SymplecticVector K,
      w ≠ 0 ∧ w ∈ (symmetricGraphLine K a b c).1 ∧
        w ∈ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨w, hw, hgraph, hcenter⟩
    obtain ⟨u, hu⟩ := hgraph
    obtain ⟨d, hd⟩ := hcenter
    have hvector :
        symmetricGraphVector K a b c (u 0) (u 1) =
          d 0 • symplecticHorizontalVector K x y +
            d 1 • symplecticAnnihilatorVector K x y := by
      exact hu.trans hd.symm
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp [symmetricGraphVector, symplecticHorizontalVector,
      symplecticAnnihilatorVector, Pi.add_apply,
      smul_eq_mul] at hzero hone htwo hthree
    have hdnonzero : d 0 ≠ 0 := by
      intro hd0
      have hu0 : u 0 = 0 := by
        simpa [hd0] using hzero
      have hu1 : u 1 = 0 := by
        simpa [hd0] using htwo
      apply hw
      rw [← hu]
      change symmetricGraphVector K a b c (u 0) (u 1) = 0
      funext i
      fin_cases i <;> simp [symmetricGraphVector, hu0, hu1]
    have hproduct : d 0 * symmetricQuadratic a b c x y = 0 := by
      rw [symmetricQuadratic_eq_bilinear]
      linear_combination x * hone + y * hthree -
        (a * x + b * y) * hzero -
        (b * x + c * y) * htwo
    exact (mul_eq_zero.mp hproduct).resolve_left hdnonzero
  · intro hquadratic
    obtain ⟨s, t, hvector⟩ :=
      (symmetricGraphVector_mem_center_span_iff K hxy).mpr hquadratic
    refine ⟨symmetricGraphVector K a b c x y, ?_, ?_, ?_⟩
    · intro hzero
      rcases hxy with hx | hy
      · apply hx
        simpa [symmetricGraphVector] using congrFun hzero 0
      · apply hy
        simpa [symmetricGraphVector] using congrFun hzero 2
    · refine ⟨![x, y], ?_⟩
      simp [symmetricGraphLinearMap, symmetricGraphVector]
    · refine ⟨![s, t], ?_⟩
      simpa [coordinateCenterLinearMap] using hvector.symm

lemma symmetricGraphLine_coordinateCenter_common_point_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  rw [← symmetricGraphLine_coordinateCenter_intersection_iff K hxy]
  constructor
  · rintro ⟨p, hpgraph, hpcenter⟩
    have hpbot : p.1 ≠ ⊥ := by
      intro hbot
      have hrank := p.2
      rw [hbot, finrank_bot] at hrank
      omega
    obtain ⟨w, hw, hwne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hpbot
    exact ⟨w, hwne, hpgraph hw, hpcenter hw⟩
  · rintro ⟨w, hwne, hwgraph, hwcenter⟩
    let p : SymplecticPoint K :=
      ⟨K ∙ w, finrank_span_singleton hwne⟩
    refine ⟨p, ?_, ?_⟩
    · exact (Submodule.span_le).mpr (by simpa using hwgraph)
    · exact (Submodule.span_le).mpr (by simpa using hwcenter)

lemma projectiveDirection_nonzero_left
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]

lemma projectiveDirection_nonzero_right
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x' ≠ 0 ∨ y' ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]

lemma symmetricGraphLine_odd_no_three_actual_centers
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hcenter₀ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₀ y₀
            (projectiveDirection_nonzero_left K h01)).1)
    (hcenter₁ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₁ y₁
            (projectiveDirection_nonzero_right K h01)).1)
    (hcenter₂ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₂ y₂
            (projectiveDirection_nonzero_right K h02)).1) :
    False := by
  apply symmetricQuadratic_no_three_roots_of_det_ne_zero
    htwo hdet h01 h02 h12
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K h01)).mp hcenter₀
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h01)).mp hcenter₁
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h02)).mp hcenter₂

lemma symmetricGraphLines_disjoint_of_difference_det
    {a b c a' b' c' : K}
    (hdet : symmetricDet (a - a') (b - b') (c - c') ≠ 0) :
    Disjoint (symmetricGraphLine K a b c).1
      (symmetricGraphLine K a' b' c').1 := by
  apply Submodule.disjoint_def.mpr
  intro w hw hw'
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hw'
  have hvector :
      symmetricGraphVector K a b c (u 0) (u 1) =
        symmetricGraphVector K a' b' c' (v 0) (v 1) := by
    exact hu.trans hv.symm
  have hzero := congrFun hvector 0
  have htwo := congrFun hvector 2
  simp [symmetricGraphVector] at hzero htwo
  have huv : u = v := by
    funext i
    fin_cases i
    · exact hzero
    · exact htwo
  subst v
  have hone := congrFun hvector 1
  have hthree := congrFun hvector 3
  simp [symmetricGraphVector] at hone hthree
  have hdetx :
      symmetricDet (a - a') (b - b') (c - c') * u 0 = 0 := by
    unfold symmetricDet
    linear_combination (c - c') * hone - (b - b') * hthree
  have hdety :
      symmetricDet (a - a') (b - b') (c - c') * u 1 = 0 := by
    unfold symmetricDet
    linear_combination -(b - b') * hone + (a - a') * hthree
  have hx : u 0 = 0 :=
    (mul_eq_zero.mp hdetx).resolve_left hdet
  have hy : u 1 = 0 :=
    (mul_eq_zero.mp hdety).resolve_left hdet
  rw [← hu]
  change symmetricGraphVector K a b c (u 0) (u 1) = 0
  funext i
  fin_cases i <;> simp [symmetricGraphVector, hx, hy]

theorem symmetricGraphLine_zero_diagonal_disjoint
    {b b' : K} (h : b ≠ b') :
    Disjoint (symmetricGraphLine K 0 b 0).1
      (symmetricGraphLine K 0 b' 0).1 := by
  apply symmetricGraphLines_disjoint_of_difference_det K
  simpa using symmetricDet_zero_diagonal_sub_ne_zero h

section CharacteristicTwo

variable [CharP K 2] [Finite K]

lemma symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
    {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x y
            (projectiveDirection_nonzero_left K hind)).1)
    (hsecond : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x' y'
            (projectiveDirection_nonzero_right K hind)).1) :
    a = 0 ∧ c = 0 := by
  apply symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    hind
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K hind)).mp hfirst
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K hind)).mp hsecond

end CharacteristicTwo

end LineCoordinates

noncomputable section ArbitraryLineNormalization

open SimpleGraph

variable (K : Type*) [Field K]

abbrev SymplecticAutomorphism :=
  (standardSymplecticBilin K).IsometryEquiv
    (standardSymplecticBilin K)

lemma symplecticAutomorphism_form
    (e : SymplecticAutomorphism K)
    (u v : SymplecticVector K) :
    standardSymplecticForm K (e u) (e v) =
      standardSymplecticForm K u v := by
  change
    standardSymplecticBilin K (e u) (e v) =
      standardSymplecticBilin K u v
  exact e.map_app' u v

def symplecticAutomorphismPoint
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) : SymplecticPoint K :=
  ⟨p.1.map e.toLinearEquiv.toLinearMap,
    (e.toLinearEquiv.finrank_map_eq p.1).trans p.2⟩

def symplecticAutomorphismLine
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) : SymplecticLine K := by
  refine ⟨L.1.map e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · exact (e.toLinearEquiv.finrank_map_eq L.1).trans L.2.1
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_map.mp hu)
    obtain ⟨v', hv', rfl⟩ := (Submodule.mem_map.mp hv)
    change standardSymplecticForm K (e u') (e v') = 0
    exact (symplecticAutomorphism_form K e u' v').trans
      (L.2.2 u' hu' v' hv')

lemma symplecticAutomorphism_incidence_iff
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticAutomorphismPoint K e p).1 ≤
        (symplecticAutomorphismLine K e L).1 ↔
      p.1 ≤ L.1 := by
  change
    p.1.map e.toLinearEquiv.toLinearMap ≤
      L.1.map e.toLinearEquiv.toLinearMap ↔ p.1 ≤ L.1
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective)

lemma symplecticAutomorphism_isotropic_iff
    (e : SymplecticAutomorphism K)
    (S : Submodule K (SymplecticVector K)) :
    (∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
      ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
        standardSymplecticForm K u v = 0) ↔
      (∀ u ∈ S, ∀ v ∈ S,
        standardSymplecticForm K u v = 0) := by
  constructor
  · intro h u hu v hv
    have hmap := h (e u) (Submodule.mem_map_of_mem hu)
      (e v) (Submodule.mem_map_of_mem hv)
    exact (symplecticAutomorphism_form K e u v).symm.trans hmap
  · intro h u hu v hv
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    exact (symplecticAutomorphism_form K e u' v').trans
      (h u' hu' v' hv')

def symplecticAutomorphismLineEquiv
    (e : SymplecticAutomorphism K) :
    SymplecticLine K ≃ SymplecticLine K :=
  (Submodule.orderIsoMapComap e.toLinearEquiv).toEquiv.subtypeEquiv
    (fun S => by
      change
        (Module.finrank K S = 2 ∧
          ∀ u ∈ S, ∀ v ∈ S,
            standardSymplecticForm K u v = 0) ↔
        (Module.finrank K
            (S.map e.toLinearEquiv.toLinearMap) = 2 ∧
          ∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
            ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
              standardSymplecticForm K u v = 0)
      rw [e.toLinearEquiv.finrank_map_eq,
        symplecticAutomorphism_isotropic_iff K e S])

@[simp]
lemma symplecticAutomorphismLineEquiv_apply
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) :
    symplecticAutomorphismLineEquiv K e L =
      symplecticAutomorphismLine K e L := by
  apply Subtype.ext
  rfl

lemma symplecticLine_orthogonal_eq
    (L : SymplecticLine K) :
    (standardSymplecticBilin K).orthogonal L.1 = L.1 := by
  have hle :
      L.1 ≤ (standardSymplecticBilin K).orthogonal L.1 := by
    intro u hu
    change ∀ v ∈ L.1, standardSymplecticForm K v u = 0
    intro v hv
    exact L.2.2 v hv u hu
  have hdim :
      Module.finrank K
        ((standardSymplecticBilin K).orthogonal L.1) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal
      (standardSymplecticBilin_nondegenerate K), L.2.1]
    simp [SymplecticVector]
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (L.2.1.trans hdim.symm)).symm

lemma symplecticLine_isCompl_of_disjoint
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) : IsCompl L.1 M.1 := by
  apply (Submodule.isCompl_iff_disjoint L.1 M.1 ?_).mpr hLM
  simp [SymplecticVector, L.2.1, M.2.1]

def symplecticLinePairing
    (L M : SymplecticLine K) :
    M.1 →ₗ[K] Module.Dual K L.1 where
  toFun y :=
    { toFun := fun x =>
        standardSymplecticForm K
          (x : SymplecticVector K) (y : SymplecticVector K)
      map_add' := by
        intro x x'
        simpa using standardSymplecticForm_add_left K
          (x : SymplecticVector K)
          (x' : SymplecticVector K)
          (y : SymplecticVector K)
      map_smul' := by
        intro c x
        simpa [smul_eq_mul] using
          standardSymplecticForm_smul_left K c
            (x : SymplecticVector K)
            (y : SymplecticVector K) }
  map_add' := by
    intro y y'
    apply LinearMap.ext
    intro x
    simpa using standardSymplecticForm_add_right K
      (x : SymplecticVector K)
      (y : SymplecticVector K)
      (y' : SymplecticVector K)
  map_smul' := by
    intro c y
    apply LinearMap.ext
    intro x
    simpa [smul_eq_mul] using
      standardSymplecticForm_smul_right K c
        (x : SymplecticVector K)
        (y : SymplecticVector K)

lemma symplecticLinePairing_injective
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) :
    Function.Injective (symplecticLinePairing K L M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro y hy
    have hpair : symplecticLinePairing K L M y = 0 := by
      exact LinearMap.mem_ker.mp hy
    have hyorth :
        (y : SymplecticVector K) ∈
          (standardSymplecticBilin K).orthogonal L.1 := by
      change
        ∀ x ∈ L.1,
          standardSymplecticForm K x
            (y : SymplecticVector K) = 0
      intro x hx
      have hz := DFunLike.congr_fun hpair (⟨x, hx⟩ : L.1)
      simpa [symplecticLinePairing] using hz
    have hyL : (y : SymplecticVector K) ∈ L.1 := by
      rw [symplecticLine_orthogonal_eq K L] at hyorth
      exact hyorth
    have hyzero : (y : SymplecticVector K) = 0 := by
      have hbot :
          (y : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hLM.le_bot ⟨hyL, y.2⟩
      simpa using hbot
    have hyzero' : y = 0 := by
      apply Subtype.ext
      simpa using hyzero
    exact (Submodule.mem_bot K).2 hyzero'
  · exact bot_le

lemma symplecticLinePairing_finrank
    (L M : SymplecticLine K) :
    Module.finrank K M.1 =
      Module.finrank K (Module.Dual K L.1) := by
  rw [Subspace.dual_finrank_eq, L.2.1, M.2.1]

def symplecticLinePairingEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] Module.Dual K L.1 :=
  (symplecticLinePairing K L M).linearEquivOfInjective
    (symplecticLinePairing_injective K hLM)
    (symplecticLinePairing_finrank K L M)

def symplecticLineBasis
    (L : SymplecticLine K) : Module.Basis (Fin 2) K L.1 :=
  Module.finBasisOfFinrankEq K L.1 L.2.1

def symplecticLineDualCoordinates
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] (Fin 2 → K) :=
  (symplecticLinePairingEquiv K L M hLM).trans
    (symplecticLineBasis K L).dualBasis.equivFun

@[simp]
lemma symplecticLineDualCoordinates_apply
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) (i : Fin 2) :
    symplecticLineDualCoordinates K L M hLM y i =
      standardSymplecticForm K
        ((symplecticLineBasis K L i : L.1) : SymplecticVector K)
        (y : SymplecticVector K) := by
  change
    (symplecticLineBasis K L).dualBasis.equivFun
        (symplecticLinePairingEquiv K L M hLM y) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  rfl

def symplecticCoordinateInterleave :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] SymplecticVector K where
  toFun x := ![x.1 0, x.2 0, x.1 1, x.2 1]
  invFun x := (![x 0, x 2], ![x 1, x 3])
  left_inv := by
    intro x
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticLineCoordinateEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticVector K ≃ₗ[K] SymplecticVector K :=
  ((L.1.prodEquivOfIsCompl M.1
      (symplecticLine_isCompl_of_disjoint K hLM)).symm.trans
      ((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))).trans
      (symplecticCoordinateInterleave K)

lemma symplecticLinePairing_coordinate_expansion
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
  let b := symplecticLineBasis K L
  have hsum :
      (∑ i : Fin 2, b.equivFun x i • b i) = x :=
    b.sum_equivFun x
  calc
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
        symplecticLinePairing K L M y x := rfl
    _ = symplecticLinePairing K L M y
          (∑ i : Fin 2, b.equivFun x i • b i) :=
      congrArg (symplecticLinePairing K L M y) hsum.symm
    _ = ∑ i : Fin 2,
          b.equivFun x i *
            standardSymplecticForm K
              ((b i : L.1) : SymplecticVector K)
              (y : SymplecticVector K) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp [smul_eq_mul, symplecticLinePairing]
    _ = (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
      simp [Fin.sum_univ_two, b,
        symplecticLineDualCoordinates_apply]

lemma symplecticLineCoordinateEquiv_apply_add
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    symplecticLineCoordinateEquiv K L M hLM
        ((x : SymplecticVector K) + (y : SymplecticVector K)) =
      ![(symplecticLineBasis K L).equivFun x 0,
        symplecticLineDualCoordinates K L M hLM y 0,
        (symplecticLineBasis K L).equivFun x 1,
        symplecticLineDualCoordinates K L M hLM y 1] := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  have hsplit :
      (L.1.prodEquivOfIsCompl M.1 hcompl).symm
        ((x : SymplecticVector K) +
          (y : SymplecticVector K)) = (x, y) := by
    apply (L.1.prodEquivOfIsCompl M.1 hcompl).symm_apply_eq.mpr
    rfl
  change
    symplecticCoordinateInterleave K
      (((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))
        ((L.1.prodEquivOfIsCompl M.1 hcompl).symm
          ((x : SymplecticVector K) +
            (y : SymplecticVector K)))) = _
  rw [hsplit]
  rfl

lemma symplecticLineCoordinateEquiv_form
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (u v : SymplecticVector K) :
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM u)
        (symplecticLineCoordinateEquiv K L M hLM v) =
      standardSymplecticForm K u v := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  obtain ⟨⟨x, y⟩, hu⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective u
  obtain ⟨⟨x', y'⟩, hv⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective v
  rw [← hu, ← hv]
  change
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K))
  calc
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y' 0 -
        symplecticLineDualCoordinates K L M hLM y 0 *
          (symplecticLineBasis K L).equivFun x' 0 +
        ((symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y' 1 -
        symplecticLineDualCoordinates K L M hLM y 1 *
          (symplecticLineBasis K L).equivFun x' 1) := by
        simp [symplecticLineCoordinateEquiv_apply_add,
          standardSymplecticForm]
    _ = standardSymplecticForm K
          (x : SymplecticVector K) (y' : SymplecticVector K) -
        standardSymplecticForm K
          (x' : SymplecticVector K) (y : SymplecticVector K) := by
        rw [symplecticLinePairing_coordinate_expansion K L M hLM x y',
          symplecticLinePairing_coordinate_expansion K L M hLM x' y]
        ring
    _ = standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K)) := by
        have hxx :
            standardSymplecticForm K
              (x : SymplecticVector K)
              (x' : SymplecticVector K) = 0 :=
          L.2.2 x x.2 x' x'.2
        have hyy :
            standardSymplecticForm K
              (y : SymplecticVector K)
              (y' : SymplecticVector K) = 0 :=
          M.2.2 y y.2 y' y'.2
        rw [standardSymplecticForm_add_left,
          standardSymplecticForm_add_right,
          standardSymplecticForm_add_right,
          hxx, hyy,
          standardSymplecticForm_swap K
            (y : SymplecticVector K)
            (x' : SymplecticVector K)]
        ring

def symplecticLineNormalizer
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticAutomorphism K :=
  { symplecticLineCoordinateEquiv K L M hLM with
    map_app' := by
      intro u v
      change
        standardSymplecticForm K
            (symplecticLineCoordinateEquiv K L M hLM u)
            (symplecticLineCoordinateEquiv K L M hLM v) =
          standardSymplecticForm K u v
      exact symplecticLineCoordinateEquiv_form K L M hLM u v }

lemma symplecticLineNormalizer_apply_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) :
    symplecticLineNormalizer K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    x (0 : M.1)
  simpa [standardSymplecticForm] using h

lemma symplecticLineNormalizer_apply_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) :
    symplecticLineNormalizer K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    (0 : L.1) y
  simpa using h

def symplecticVerticalLinearMap :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun y := ![0, y 0, 0, y 1]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c y := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticVerticalLinearMap_injective :
    Function.Injective (symplecticVerticalLinearMap K) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa [symplecticVerticalLinearMap] using congrFun huv 1
  · simpa [symplecticVerticalLinearMap] using congrFun huv 3

def symplecticVerticalLine : SymplecticLine K :=
  ⟨LinearMap.range (symplecticVerticalLinearMap K), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symplecticVerticalLinearMap_injective K)]
      simp
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp [symplecticVerticalLinearMap,
        standardSymplecticForm]⟩

lemma symplecticLineNormalizer_map_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) L =
      symmetricGraphLine K 0 0 0 := by
  apply Subtype.ext
  change
    L.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨(symplecticLineBasis K L).equivFun ⟨x, hx⟩, ?_⟩
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (symplecticLineNormalizer_apply_left K L M hLM
        (⟨x, hx⟩ : L.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let x : L.1 := (symplecticLineBasis K L).equivFun.symm z
    refine Submodule.mem_map.mpr
      ⟨(x : SymplecticVector K), x.2, ?_⟩
    simpa [x, symmetricGraphLinearMap, symmetricGraphVector] using
      symplecticLineNormalizer_apply_left K L M hLM x

lemma symplecticLineNormalizer_map_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) M =
      symplecticVerticalLine K := by
  apply Subtype.ext
  change
    M.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symplecticVerticalLinearMap K)
  apply le_antisymm
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨symplecticLineDualCoordinates K L M hLM ⟨y, hy⟩, ?_⟩
    simpa [symplecticVerticalLinearMap] using
      (symplecticLineNormalizer_apply_right K L M hLM
        (⟨y, hy⟩ : M.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let y : M.1 :=
      (symplecticLineDualCoordinates K L M hLM).symm z
    refine Submodule.mem_map.mpr
      ⟨(y : SymplecticVector K), y.2, ?_⟩
    change
      symplecticLineNormalizer K L M hLM
          (y : SymplecticVector K) =
        symplecticVerticalLinearMap K z
    rw [symplecticLineNormalizer_apply_right]
    change
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] =
        ![0, z 0, 0, z 1]
    have hy : symplecticLineDualCoordinates K L M hLM y = z :=
      (symplecticLineDualCoordinates K L M hLM).apply_symm_apply z
    rw [hy]

def symplecticHorizontalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 0, v 2]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticVerticalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, v 3]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticHorizontalProjection_ker :
    LinearMap.ker (symplecticHorizontalProjection K) =
      (symplecticVerticalLine K).1 := by
  apply le_antisymm
  · intro v hv
    have hzero := LinearMap.mem_ker.mp hv
    have hfirst := congrFun hzero 0
    have hthird := congrFun hzero 1
    simp [symplecticHorizontalProjection] at hfirst hthird
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K)
    refine ⟨![v 1, v 3], ?_⟩
    funext i
    fin_cases i <;>
      simp [symplecticVerticalLinearMap, hfirst, hthird]
  · intro v hv
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
    obtain ⟨y, rfl⟩ := hv
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalProjection,
        symplecticVerticalLinearMap]

lemma symplecticLineHorizontalProjection_injective
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    Function.Injective
      ((symplecticHorizontalProjection K).comp L.1.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hproj := LinearMap.mem_ker.mp hx
    change
      symplecticHorizontalProjection K
          (x : SymplecticVector K) = 0 at hproj
    have hxvertical :
        (x : SymplecticVector K) ∈
          (symplecticVerticalLine K).1 := by
      rw [← symplecticHorizontalProjection_ker K]
      exact LinearMap.mem_ker.mpr hproj
    have hxzero : (x : SymplecticVector K) = 0 := by
      have hbot :
          (x : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hvertical.le_bot ⟨x.2, hxvertical⟩
      simpa using hbot
    have hxsub : x = 0 := by
      apply Subtype.ext
      simpa using hxzero
    exact (Submodule.mem_bot K).2 hxsub
  · exact bot_le

def symplecticLineHorizontalProjectionEquiv
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    L.1 ≃ₗ[K] (Fin 2 → K) :=
  ((symplecticHorizontalProjection K).comp L.1.subtype).linearEquivOfInjective
      (symplecticLineHorizontalProjection_injective K L hvertical)
      (by simp [L.2.1])

def symplecticLineGraphMap
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (symplecticVerticalProjection K).comp
    (L.1.subtype.comp
      (symplecticLineHorizontalProjectionEquiv K L hvertical).symm.toLinearMap)

lemma symplecticLineGraphMap_horizontal
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by
  change
    symplecticVerticalProjection K
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm
        (symplecticLineHorizontalProjectionEquiv K L hvertical x) :
          SymplecticVector K) = _
  rw [LinearEquiv.symm_apply_apply]

lemma symplecticLineGraphMap_symmetric
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    symplecticLineGraphMap K L hvertical ![1, 0] 1 =
      symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![1, 0]
  let v : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![0, 1]
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = ![1, 0] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u =
        ![1, 0]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![1, 0]
  have hv :
      symplecticHorizontalProjection K
        (v : SymplecticVector K) = ![0, 1] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical v =
        ![0, 1]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![0, 1]
  have hu0 : (u : SymplecticVector K) 0 = 1 := by
    simpa [symplecticHorizontalProjection] using congrFun hu 0
  have hu2 : (u : SymplecticVector K) 2 = 0 := by
    simpa [symplecticHorizontalProjection] using congrFun hu 1
  have hv0 : (v : SymplecticVector K) 0 = 0 := by
    simpa [symplecticHorizontalProjection] using congrFun hv 0
  have hv2 : (v : SymplecticVector K) 2 = 1 := by
    simpa [symplecticHorizontalProjection] using congrFun hv 1
  have hu3 :
      (u : SymplecticVector K) 3 =
        symplecticLineGraphMap K L hvertical ![1, 0] 1 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical u) 1
    rw [hu] at h
    simpa [symplecticVerticalProjection] using h.symm
  have hv1 :
      (v : SymplecticVector K) 1 =
        symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical v) 0
    rw [hv] at h
    simpa [symplecticVerticalProjection] using h.symm
  have hpair := L.2.2
    (u : SymplecticVector K) u.2
    (v : SymplecticVector K) v.2
  have hzero :
      symplecticLineGraphMap K L hvertical ![0, 1] 0 -
        symplecticLineGraphMap K L hvertical ![1, 0] 1 = 0 := by
    rw [sub_eq_add_neg]
    simpa [standardSymplecticForm, hu0, hu2, hv0, hv2,
      hu3, hv1] using hpair
  exact (sub_eq_zero.mp hzero).symm

lemma symplecticLineGraphMap_coordinate_expansion
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) (i : Fin 2) :
    symplecticLineGraphMap K L hvertical z i =
      symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    funext j
    fin_cases j <;> simp [smul_eq_mul]
  calc
    symplecticLineGraphMap K L hvertical z i =
        symplecticLineGraphMap K L hvertical
          (z 0 • ![1, 0] + z 1 • ![0, 1]) i := by
      rw [← hz]
    _ = symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
      rw [map_add, map_smul, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

lemma symplecticLineGraphMap_graphVector
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) :
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm z :
        SymplecticVector K) := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = z := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u = z
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply z
  have hg :
      symplecticLineGraphMap K L hvertical z =
        symplecticVerticalProjection K
          (u : SymplecticVector K) := by
    rw [← hu]
    exact symplecticLineGraphMap_horizontal K L hvertical u
  change
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      (u : SymplecticVector K)
  funext i
  fin_cases i
  · simpa [symmetricGraphVector, symplecticHorizontalProjection]
      using (congrFun hu 0).symm
  · have hg0 := congrFun hg 0
    change
      symplecticLineGraphMap K L hvertical z 0 =
        (u : SymplecticVector K) 1 at hg0
    change
      symplecticLineGraphMap K L hvertical ![1, 0] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 1 =
        (u : SymplecticVector K) 1
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 0).symm.trans hg0
  · simpa [symmetricGraphVector, symplecticHorizontalProjection]
      using (congrFun hu 1).symm
  · have hg1 := congrFun hg 1
    change
      symplecticLineGraphMap K L hvertical z 1 =
        (u : SymplecticVector K) 3 at hg1
    change
      symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 1 * z 1 =
        (u : SymplecticVector K) 3
    rw [← symplecticLineGraphMap_symmetric K L hvertical]
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 1).symm.trans hg1

lemma symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    ∃ a b c : K, L = symmetricGraphLine K a b c := by
  let a := symplecticLineGraphMap K L hvertical ![1, 0] 0
  let b := symplecticLineGraphMap K L hvertical ![0, 1] 0
  let c := symplecticLineGraphMap K L hvertical ![0, 1] 1
  refine ⟨a, b, c, ?_⟩
  apply Subtype.ext
  change L.1 = LinearMap.range (symmetricGraphLinearMap K a b c)
  apply le_antisymm
  · intro w hw
    let x : L.1 := ⟨w, hw⟩
    let z := symplecticHorizontalProjection K
      (w : SymplecticVector K)
    refine ⟨z, ?_⟩
    change symmetricGraphVector K a b c (z 0) (z 1) = w
    have hgraph := symplecticLineGraphMap_graphVector
      K L hvertical z
    have hpreimage :
        (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z =
          x := by
      apply
        (symplecticLineHorizontalProjectionEquiv K L hvertical).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) = w
    rw [hgraph, hpreimage]
  · intro w hw
    obtain ⟨z, rfl⟩ := hw
    change
      symmetricGraphVector K a b c (z 0) (z 1) ∈ L.1
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) ∈ L.1
    rw [symplecticLineGraphMap_graphVector K L hvertical z]
    exact ((symplecticLineHorizontalProjectionEquiv
      K L hvertical).symm z).2

lemma symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
    (a b c : K)
    (hhorizontal :
      Disjoint (symmetricGraphLine K a b c).1
        (symmetricGraphLine K 0 0 0).1) :
    symmetricDet a b c ≠ 0 := by
  intro hdet
  have hkernel :
      ∃ x y : K,
        (x ≠ 0 ∨ y ≠ 0) ∧
          a * x + b * y = 0 ∧
          b * x + c * y = 0 := by
    by_cases ha : a = 0
    · have hb : b = 0 := by
        have hsq : b ^ 2 = 0 := by
          simpa [symmetricDet, ha] using hdet
        exact eq_zero_of_pow_eq_zero hsq
      exact ⟨1, 0, Or.inl one_ne_zero, by simp [ha, hb],
        by simp [hb]⟩
    · refine ⟨b, -a, Or.inr (neg_ne_zero.mpr ha), ?_, ?_⟩
      · ring
      · unfold symmetricDet at hdet
        linear_combination -hdet
  obtain ⟨x, y, hnonzero, hfirst, hsecond⟩ := hkernel
  let w := symmetricGraphVector K a b c x y
  have hwgraph : w ∈ (symmetricGraphLine K a b c).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K a b c)
    exact ⟨![x, y], rfl⟩
  have hwhorizontal : w ∈ (symmetricGraphLine K 0 0 0).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    refine ⟨![x, y], ?_⟩
    funext i
    fin_cases i <;>
      simp [symmetricGraphLinearMap, symmetricGraphVector,
        w, hfirst, hsecond]
  have hwzero : w = (0 : SymplecticVector K) := by
    have hbot : w ∈ (⊥ : Submodule K (SymplecticVector K)) :=
      hhorizontal.le_bot ⟨hwgraph, hwhorizontal⟩
    simpa using hbot
  have hxzero : x = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 0
  have hyzero : y = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 2
  exact hnonzero.elim (fun h => h hxzero) (fun h => h hyzero)

lemma symplecticLine_eq_invertible_symmetricGraphLine
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (hhorizontal :
      Disjoint L.1 (symmetricGraphLine K 0 0 0).1) :
    ∃ a b c : K,
      L = symmetricGraphLine K a b c ∧
        symmetricDet a b c ≠ 0 := by
  obtain ⟨a, b, c, hL⟩ :=
    symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
      K L hvertical
  refine ⟨a, b, c, hL, ?_⟩
  apply symmetricGraphLine_det_ne_zero_of_disjoint_horizontal K a b c
  rw [← hL]
  exact hhorizontal

lemma symplecticCanonicalLines_disjoint :
    Disjoint (symmetricGraphLine K 0 0 0).1
      (symplecticVerticalLine K).1 := by
  apply Submodule.disjoint_def.mpr
  intro w hwH hwV
  change w ∈ LinearMap.range
    (symmetricGraphLinearMap K 0 0 0) at hwH
  change w ∈ LinearMap.range
    (symplecticVerticalLinearMap K) at hwV
  obtain ⟨z, hz⟩ := hwH
  obtain ⟨t, ht⟩ := hwV
  have heq := hz.trans ht.symm
  have hz0 : z 0 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector,
      symplecticVerticalLinearMap] using congrFun heq 0
  have hz1 : z 1 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector,
      symplecticVerticalLinearMap] using congrFun heq 2
  rw [← hz]
  funext i
  fin_cases i <;>
    simp [symmetricGraphLinearMap, symmetricGraphVector,
      hz0, hz1]

lemma symplecticVertical_mem_coordinateCenter_of_orthogonal
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0)
    {v : SymplecticVector K}
    (hv : v ∈ (symplecticVerticalLine K).1)
    (horth : standardSymplecticForm K
      (symplecticHorizontalVector K x y) v = 0) :
    v ∈ (coordinateCenterLine K x y hxy).1 := by
  change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
  obtain ⟨z, hz⟩ := hv
  have hv0 : v 0 = 0 := by
    simpa [symplecticVerticalLinearMap] using
      (congrFun hz 0).symm
  have hv2 : v 2 = 0 := by
    simpa [symplecticVerticalLinearMap] using
      (congrFun hz 2).symm
  have heq : x * v 1 + y * v 3 = 0 := by
    simpa [standardSymplecticForm,
      symplecticHorizontalVector] using horth
  change v ∈ LinearMap.range (coordinateCenterLinearMap K x y)
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases hxy with h | h
      · exact False.elim (h hx)
      · exact h
    refine ⟨![0, -(v 1 / y)], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hy]
    linear_combination -heq
  · refine ⟨![0, v 3 / x], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hx]
    linear_combination -heq

lemma symplecticLine_eq_coordinateCenterLine_of_common_points
    (C : SymplecticLine K)
    (p q : SymplecticPoint K)
    (hpH : p.1 ≤ (symmetricGraphLine K 0 0 0).1)
    (hpC : p.1 ≤ C.1)
    (hqV : q.1 ≤ (symplecticVerticalLine K).1)
    (hqC : q.1 ≤ C.1) :
    ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
      C = coordinateCenterLine K x y hxy := by
  have hpos : 0 < Module.finrank K p.1 := by
    rw [p.2]
    norm_num
  obtain ⟨u, hu⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have huhorizontal := hpH u.2
  change
    (u : SymplecticVector K) ∈
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    at huhorizontal
  obtain ⟨z, hz⟩ := huhorizontal
  have hu1 : (u : SymplecticVector K) 1 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (congrFun hz 1).symm
  have hu3 : (u : SymplecticVector K) 3 = 0 := by
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (congrFun hz 3).symm
  let x : K := (u : SymplecticVector K) 0
  let y : K := (u : SymplecticVector K) 2
  have huvector :
      (u : SymplecticVector K) =
        symplecticHorizontalVector K x y := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, x, y, hu1, hu3]
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    have hx : x = 0 :=
      Classical.byContradiction (fun hx => h (Or.inl hx))
    have hy : y = 0 :=
      Classical.byContradiction (fun hy => h (Or.inr hy))
    have huzero : (u : SymplecticVector K) = 0 := by
      rw [huvector, hx, hy]
      simp [symplecticHorizontalVector]
    apply hu
    apply Subtype.ext
    simpa using huzero
  have hpq : p ≠ q := by
    intro heq
    subst q
    have hbot :
        (u : SymplecticVector K) ∈
          (⊥ : Submodule K (SymplecticVector K)) :=
      (symplecticCanonicalLines_disjoint K).le_bot
        ⟨hpH u.2, hqV u.2⟩
    apply hu
    apply Subtype.ext
    simpa using hbot
  have hucenter :
      (u : SymplecticVector K) ∈
        (coordinateCenterLine K x y hxy).1 := by
    change
      (u : SymplecticVector K) ∈
        LinearMap.range (coordinateCenterLinearMap K x y)
    refine ⟨![1, 0], ?_⟩
    rw [huvector]
    simp [coordinateCenterLinearMap,
      symplecticHorizontalVector,
      symplecticAnnihilatorVector, smul_eq_mul]
  have hpcenter :
      p.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hu (⟨v, hv⟩ : p.1)
    have hav : a • (u : SymplecticVector K) = v :=
      congrArg Subtype.val ha
    rw [← hav]
    exact (coordinateCenterLine K x y hxy).1.smul_mem a hucenter
  have hqcenter :
      q.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    apply symplecticVertical_mem_coordinateCenter_of_orthogonal
      K hxy (hqV hv)
    rw [← huvector]
    exact C.2.2 (u : SymplecticVector K)
      (hpC u.2) v (hqC hv)
  refine ⟨x, y, hxy, ?_⟩
  apply Subtype.ext
  have hspanC : p.1 ⊔ q.1 = C.1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpC hqC)
      ((symplecticPoint_sup_finrank K hpq).trans C.2.1.symm)
  have hspanCenter :
      p.1 ⊔ q.1 = (coordinateCenterLine K x y hxy).1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpcenter hqcenter)
      ((symplecticPoint_sup_finrank K hpq).trans
        (coordinateCenterLine K x y hxy).2.1.symm)
  exact hspanC.symm.trans hspanCenter

lemma coordinateCenterLine_direction_det_ne_zero_of_ne
    {x y x' y' : K}
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hxy' : x' ≠ 0 ∨ y' ≠ 0)
    (hne : coordinateCenterLine K x y hxy ≠
      coordinateCenterLine K x' y' hxy') :
    x * y' - x' * y ≠ 0 := by
  intro hdet
  have hscale :
      ∃ t : K, t ≠ 0 ∧ x' = t * x ∧ y' = t * y := by
    rcases hxy with hx | hy
    · let t : K := x' / x
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hx]
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hx]
        linear_combination hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
    · let t : K := y' / y
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hy]
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hy]
        linear_combination -hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
  obtain ⟨t, ht, hfirst, hsecond⟩ := hscale
  apply hne
  apply Subtype.ext
  change
    LinearMap.range (coordinateCenterLinearMap K x y) =
      LinearMap.range (coordinateCenterLinearMap K x' y')
  have hmap (u : Fin 2 → K) :
      coordinateCenterLinearMap K x' y' u =
        t • coordinateCenterLinearMap K x y u := by
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hfirst, hsecond] <;>
      ring
  apply le_antisymm
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t⁻¹ • u, ?_⟩
    rw [hmap, map_smul]
    simp [ht]
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t • u, ?_⟩
    rw [map_smul, ← hmap]

lemma symplecticAutomorphism_disjoint_iff
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K) :
    Disjoint (symplecticAutomorphismLine K e L).1
        (symplecticAutomorphismLine K e M).1 ↔
      Disjoint L.1 M.1 := by
  change
    Disjoint (L.1.map e.toLinearEquiv.toLinearMap)
        (M.1.map e.toLinearEquiv.toLinearMap) ↔
      Disjoint L.1 M.1
  rw [disjoint_iff,
    ← Submodule.map_inf e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.injective,
    Submodule.map_eq_bot_iff,
    ← disjoint_iff]

lemma symplecticCanonical_line_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (X : SymplecticLine K)
    (hXH :
      Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV :
      Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  classical
  obtain ⟨a, b, c, hXgraph, hdet⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine
      K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 3) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hdir {i j : Fin 3} (hij : i ≠ j) :
      x i * y j - x j * y i ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy i) (hxy j)
    intro heq
    apply hij
    apply hcenters
    exact (hrepr i).trans (heq.trans (hrepr j).symm)
  have h01 : x 0 * y 1 - x 1 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 1)
  have h02 : x 0 * y 2 - x 2 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 2)
  have h12 : x 1 * y 2 - x 2 * y 1 ≠ 0 :=
    hdir (by decide : (1 : Fin 3) ≠ 2)
  apply symmetricGraphLine_odd_no_three_actual_centers K
    htwo hdet h01 h02 h12
  · obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 2
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 2]
      exact hpC

theorem symplecticLine_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (Y Z X : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hY : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (centers i).1)
    (hZ : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  have hleft :
      symplecticAutomorphismLine K e Y =
        symmetricGraphLine K 0 0 0 := by
    exact symplecticLineNormalizer_map_left K Y Z hYZ
  have hright :
      symplecticAutomorphismLine K e Z =
        symplecticVerticalLine K := by
    exact symplecticLineNormalizer_map_right K Y Z hYZ
  apply symplecticCanonical_line_no_three_common_centers K htwo
    (symplecticAutomorphismLine K e X)
    (centers := fun i =>
      symplecticAutomorphismLine K e (centers i))
  · rw [← hleft]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  · rw [← hright]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  · intro i j hij
    apply hcenters
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  · intro i
    obtain ⟨p, hpY, hpC⟩ := hY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hleft]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpZ, hpC⟩ := hZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hright]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpX, hpC⟩ := hX i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · exact (symplecticAutomorphism_incidence_iff K e p X).mpr hpX
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC

theorem symplecticQuadrangle_no_line_gamma_of_odd
    (htwo : (2 : K) ≠ 0)
    (copy : SimpleGraph.Copy gammaGraph
      (symplecticQuadrangle K))
    (C : SymplecticLine K)
    (hC : copy kSpecifiedCenter = .inr C) :
    False := by
  classical
  have hspecified :
      copy (.inl (.inr (0 : Fin 3))) = .inr C := by
    simpa [kSpecifiedCenter] using hC
  have hbase_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inl i)) = .inr L :=
    subdivisionLine_base_of_line_center K copy
      (base := i) (center := (0 : Fin 3)) hspecified
  choose bases hbase using hbase_exists
  have hcenter_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K copy
      (base := (0 : Fin 3)) (center := i) (hbase 0)
  choose centers hcenter using hcenter_exists
  apply symplecticLine_no_three_common_centers K htwo
    (bases 1) (bases 2) (bases 0)
    (centers := centers)
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (1 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 1) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_centers_injective K copy centers hcenter
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 1) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 2) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 0) (hcenter i)
    exact ⟨p, hpB, hpC⟩

theorem symplecticQuadrangle_no_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (quotientGraph kTemplate f).Free
      (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  let hom : kTemplate →g symplecticQuadrangle K :=
    copy.toHom.comp (kQuotientProjectionHom hf)
  have hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = i} := by
    intro i u hu v hv huv
    change
      copy (⟨f u, u, rfl⟩ : Set.range f) =
        copy (⟨f v, v, rfl⟩ : Set.range f)
      at huv
    apply hf.2 i hu hv
    exact congrArg Subtype.val (copy.injective huv)
  obtain ⟨i, L, hL⟩ :=
    symplecticQuadrangle_kTemplate_has_line_gamma
      K hom hcopies
  exact symplecticQuadrangle_no_line_gamma_of_odd K htwo
    (kGammaHomCopy hom hcopies i) L hL

theorem symplecticQuadrangle_encodeFiniteGraph_free_iff
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (encodeFiniteGraph G).graph.Free
        (symplecticQuadrangle K) ↔
      G.Free (symplecticQuadrangle K) :=
  (SimpleGraph.free_congr_left
    (SimpleGraph.Iso.map (Fintype.equivFin V) G)).symm

theorem symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  (symplecticQuadrangle_encodeFiniteGraph_free_iff K
    (quotientGraph kTemplate f)).mpr
    (symplecticQuadrangle_no_kQuotient_of_odd K htwo hf)

end ArbitraryLineNormalization

noncomputable section JQuotientAvoidanceReduction

open SimpleGraph

lemma jQuotient_free_of_template_avoidance
    {V : Type*} (host : SimpleGraph V)
    (havoid : ∀ hom : jTemplate →g host,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (quotientGraph jTemplate f).Free host := by
  rintro ⟨copy⟩
  let hom : jTemplate →g host :=
    copy.toHom.comp (jQuotientProjectionHom hf)
  apply havoid hom
  · intro first second heq
    change
      copy (⟨f (.inl (.inl first)),
        .inl (.inl first), rfl⟩ : Set.range f) =
        copy (⟨f (.inl (.inl second)),
          .inl (.inl second), rfl⟩ : Set.range f)
      at heq
    apply hf.2.1
    exact congrArg Subtype.val (copy.injective heq)
  · intro index first hfirst second hsecond heq
    change
      copy (⟨f first, first, rfl⟩ : Set.range f) =
        copy (⟨f second, second, rfl⟩ : Set.range f)
      at heq
    apply hf.2.2 index hfirst hsecond
    exact congrArg Subtype.val (copy.injective heq)

theorem symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance
    (K : Type*) [Field K]
    (havoid : ∀ hom : jTemplate →g symplecticQuadrangle K,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) := by
  exact
    (symplecticQuadrangle_encodeFiniteGraph_free_iff K
      (quotientGraph jTemplate f)).mpr
      (jQuotient_free_of_template_avoidance
        (symplecticQuadrangle K) havoid hf)

end JQuotientAvoidanceReduction

noncomputable section JTemplateLineAvoidanceReduction

open SimpleGraph

variable (K : Type*) [Field K]

def CharTwoLinePairAvoidance : Prop :=
  ∀ (Y Z X X' : SymplecticLine K),
    Disjoint Y.1 Z.1 →
    Disjoint X.1 Y.1 →
    Disjoint X.1 Z.1 →
    Disjoint X'.1 Y.1 →
    Disjoint X'.1 Z.1 →
    X ≠ X' →
    ∀ (C C' : Fin 2 → SymplecticLine K),
      Function.Injective C →
      Function.Injective C' →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) →
      Disjoint X.1 X'.1

theorem symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    (havoid : CharTwoLinePairAvoidance K)
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun i : Fin 4 => hom (.inl (.inl i))))
    (hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v | InJCopy i v}) :
    False := by
  classical
  let θ (i : Fin 2) := jThetaHomCopy hom hcopies i
  obtain ⟨X, hX⟩ :=
    symplecticQuadrangle_jTemplate_first_base_is_line
      K hom hbase_inj hcopies
  have hθ0X :
      θ 0 (.inl (.inl (0 : Fin 3))) = .inr X := by
    change
      hom (jThetaVertex 0 (.inl (.inl (0 : Fin 3)))) =
        .inr X
    simpa [jThetaVertex, jBase] using hX
  obtain ⟨Y, hθ0Y⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (1 : Fin 3)) (0 : Fin 2) hθ0X
  have hY :
      hom (.inl (.inl (2 : Fin 4))) = .inr Y := by
    change
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) =
        .inr Y at hθ0Y
    simpa [jThetaVertex, jBase] using hθ0Y
  obtain ⟨Z, hθ0Z⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (2 : Fin 3)) (0 : Fin 2) hθ0X
  have hZ :
      hom (.inl (.inl (3 : Fin 4))) = .inr Z := by
    change
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) =
        .inr Z at hθ0Z
    simpa [jThetaVertex, jBase] using hθ0Z
  have hθ1Y :
      θ 1 (.inl (.inl (1 : Fin 3))) = .inr Y := by
    change
      hom (jThetaVertex 1 (.inl (.inl (1 : Fin 3)))) =
        .inr Y
    simpa [jThetaVertex, jBase] using hY
  obtain ⟨X', hθ1X'⟩ :=
    subdivisionLine_base_of_line_base K (θ 1)
      (otherBase := (0 : Fin 3)) (0 : Fin 2) hθ1Y
  have hX' :
      hom (.inl (.inl (1 : Fin 4))) = .inr X' := by
    change
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) =
        .inr X' at hθ1X'
    simpa [jThetaVertex, jBase] using hθ1X'
  let B : Fin 3 → SymplecticLine K := ![X, Y, Z]
  let B' : Fin 3 → SymplecticLine K := ![X', Y, Z]
  have hθ1Z :
      θ 1 (.inl (.inl (2 : Fin 3))) = .inr Z := by
    change
      hom (jThetaVertex 1 (.inl (.inl (2 : Fin 3)))) =
        .inr Z
    simpa [jThetaVertex, jBase] using hZ
  have hB : ∀ i : Fin 3,
      θ 0 (.inl (.inl i)) = .inr (B i) := by
    intro i
    fin_cases i
    · simpa [B] using hθ0X
    · simpa [B] using hθ0Y
    · simpa [B] using hθ0Z
  have hB' : ∀ i : Fin 3,
      θ 1 (.inl (.inl i)) = .inr (B' i) := by
    intro i
    fin_cases i
    · simpa [B'] using hθ1X'
    · simpa [B'] using hθ1Y
    · simpa [B'] using hθ1Z
  have hC_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 0 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 0)
      (base := (0 : Fin 3)) (center := i) (hB 0)
  choose C hC using hC_exists
  have hC'_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 1 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 1)
      (base := (0 : Fin 3)) (center := i) (hB' 0)
  choose C' hC' using hC'_exists
  have hXX' : X ≠ X' := by
    intro heq
    have hbaseeq : (0 : Fin 4) = 1 := by
      apply hbase_inj
      change
        hom (.inl (.inl (0 : Fin 4))) =
          hom (.inl (.inl (1 : Fin 4)))
      rw [hX, hX', heq]
    exact (by decide : (0 : Fin 4) ≠ 1) hbaseeq
  have hYZ : Disjoint Y.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (1 : Fin 3) ≠ 2) (0 : Fin 2)
  have hXY : Disjoint X.1 Y.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hXZ : Disjoint X.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hX'Y : Disjoint X'.1 Y.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hX'Z : Disjoint X'.1 Z.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hdisjoint : Disjoint X.1 X'.1 := by
    apply havoid Y Z X X'
      hYZ hXY hXZ hX'Y hX'Z hXX' C C'
      (subdivisionLine_centers_injective K (θ 0) C hC)
      (subdivisionLine_centers_injective K (θ 1) C' hC')
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 1) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 2) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 0) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 1) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 2) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 0) (hC' i)
      exact ⟨p, hpB, hpC⟩
  have hjoinX : jTemplate.Adj
      (.inl (.inl (0 : Fin 4))) (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoinX' : jTemplate.Adj
      (.inl (.inl (1 : Fin 4))) (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hadjX := hom.map_rel hjoinX
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX
  rw [hX] at hadjX
  obtain ⟨p, hpjoin, hpX⟩ :=
    symplecticQuadrangle_adjacent_to_line K hadjX
  have hadjX' := hom.map_rel hjoinX'
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX'
  rw [hX', hpjoin] at hadjX'
  have hpX' : p.1 ≤ X'.1 :=
    (symplecticQuadrangle_incidence_adj K p X').mp
      hadjX'.symm
  have hpzero :
      p.1 = (⊥ : Submodule K (SymplecticVector K)) :=
    eq_bot_iff.mpr
      ((le_inf hpX hpX').trans hdisjoint.le_bot)
  have hdim := p.2
  rw [hpzero] at hdim
  simp at hdim

end JTemplateLineAvoidanceReduction

noncomputable section CharacteristicTwoLineAvoidance

open SimpleGraph

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

lemma symplecticLine_char_two_canonical_zero_diagonal
    (X : SymplecticLine K)
    (hXH : Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV : Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 2 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    ∃ b : K, X = symmetricGraphLine K 0 b 0 := by
  classical
  obtain ⟨a, b, c, hXgraph, _⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 2) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hind : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy 0) (hxy 1)
    intro heq
    have hindex : (0 : Fin 2) = 1 := by
      apply hcenters
      exact (hrepr 0).trans (heq.trans (hrepr 1).symm)
    exact (by decide : (0 : Fin 2) ≠ 1) hindex
  have hfirst :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 0) (y 0)
              (projectiveDirection_nonzero_left K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  have hsecond :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 1) (y 1)
              (projectiveDirection_nonzero_right K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  obtain ⟨ha, hc⟩ :=
    symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
      K hind hfirst hsecond
  refine ⟨b, ?_⟩
  simpa [ha, hc] using hXgraph

omit [CharP K 2] [Finite K] in
lemma symplecticAutomorphism_commonPoint
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K)
    (hpoint : ∃ p : SymplecticPoint K,
      p.1 ≤ L.1 ∧ p.1 ≤ M.1) :
    ∃ p : SymplecticPoint K,
      p.1 ≤ (symplecticAutomorphismLine K e L).1 ∧
        p.1 ≤ (symplecticAutomorphismLine K e M).1 := by
  obtain ⟨p, hpL, hpM⟩ := hpoint
  exact ⟨symplecticAutomorphismPoint K e p,
    (symplecticAutomorphism_incidence_iff K e p L).mpr hpL,
    (symplecticAutomorphism_incidence_iff K e p M).mpr hpM⟩

lemma symplecticLine_char_two_disjoint_of_two_common_center_pairs
    (Y Z X X' : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (hX'Y : Disjoint X'.1 Y.1)
    (hX'Z : Disjoint X'.1 Z.1)
    (hXX' : X ≠ X')
    (C C' : Fin 2 → SymplecticLine K)
    (hCinj : Function.Injective C)
    (hC'inj : Function.Injective C')
    (hCY : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1)
    (hCZ : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1)
    (hCX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (C i).1)
    (hC'Y : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1)
    (hC'Z : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1)
    (hC'X : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) :
    Disjoint X.1 X'.1 := by
  classical
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  let Xn : SymplecticLine K := symplecticAutomorphismLine K e X
  let X'n : SymplecticLine K := symplecticAutomorphismLine K e X'
  let Cn : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C i)
  let C'n : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C' i)
  have hXH : Disjoint Xn.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  have hXV : Disjoint Xn.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  have hX'H : Disjoint X'n.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Y).mpr hX'Y
  have hX'V : Disjoint X'n.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Z).mpr hX'Z
  have hCn : Function.Injective Cn := by
    intro i j hij
    apply hCinj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hC'n : Function.Injective C'n := by
    intro i j hij
    apply hC'inj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hCnH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hCY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hCZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ Xn.1 ∧ p.1 ≤ (Cn i).1 := by
    exact symplecticAutomorphism_commonPoint K e X (C i) (hCX i)
  have hC'nH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hC'Y i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hC'Z i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'n.1 ∧ p.1 ≤ (C'n i).1 := by
    exact symplecticAutomorphism_commonPoint K e X' (C' i) (hC'X i)
  obtain ⟨b, hb⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K Xn hXH hXV Cn hCn hCnH hCnV hCnX
  obtain ⟨b', hb'⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K X'n hX'H hX'V C'n hC'n hC'nH hC'nV hC'nX
  have hbb : b ≠ b' := by
    intro heq
    apply hXX'
    apply (symplecticAutomorphismLineEquiv K e).injective
    simp only [symplecticAutomorphismLineEquiv_apply]
    change Xn = X'n
    rw [hb, hb', heq]
  apply (symplecticAutomorphism_disjoint_iff K e X X').mp
  change Disjoint Xn.1 X'n.1
  rw [hb, hb']
  exact symmetricGraphLine_zero_diagonal_disjoint K hbb

lemma symplecticLine_char_two_pair_avoidance :
    CharTwoLinePairAvoidance K :=
  symplecticLine_char_two_disjoint_of_two_common_center_pairs K

theorem symplecticQuadrangle_no_jTemplate_of_char_two
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {vertex | InJCopy copy vertex}) :
    False :=
  symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    K (symplecticLine_char_two_pair_avoidance K) hom hbase hcopies

theorem symplecticQuadrangle_no_encoded_jQuotient_of_char_two
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance K
    (symplecticQuadrangle_no_jTemplate_of_char_two K) hf

end CharacteristicTwoLineAvoidance

noncomputable section UpperBoundReduction

open Filter Finset SimpleGraph
open scoped Classical Topology

theorem familyExtremal_real_le_of_forall_free
    (family : Finset FiniteGraph) (n : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hfree : ∀ host : SimpleGraph (Fin n),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ≤ bound) :
    (familyExtremal family n : ℝ) ≤ bound := by
  classical
  have hnat : familyExtremal family n ≤ ⌊bound⌋₊ := by
    unfold familyExtremal
    apply Finset.sup_le
    intro host hhost
    apply Nat.le_floor
    simpa only [edgeFinset_card_eq_natCard] using
      hfree host (Finset.mem_filter.mp hhost).2
  have hcast : (familyExtremal family n : ℝ) ≤ (⌊bound⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le hbound)

lemma familyLittleO_of_eventual_host_bounds
    (family : Finset FiniteGraph)
    (hhost : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ host : SimpleGraph (Fin n),
          FamilyFree family host →
            (host.edgeFinset.card : ℝ) ≤ ε * extremalScale n) :
    FamilyLittleO family := by
  intro ε hε
  filter_upwards [hhost ε hε] with n hn
  exact familyExtremal_real_le_of_forall_free family n
    (mul_nonneg hε.le (extremalScale_nonneg n)) hn

end UpperBoundReduction

noncomputable section AsymptoticExtraction

open Filter Finset SimpleGraph
open scoped Classical Topology

lemma familyFree_of_embedded_subgraph
    {family : Finset FiniteGraph}
    {n N : ℕ} (host : SimpleGraph (Fin n))
    (subgraph : SimpleGraph (Fin N))
    (embedding : Fin N ↪ Fin n)
    (hsub : subgraph.map embedding ≤ host)
    (hfree : FamilyFree family host) :
    FamilyFree family subgraph := by
  intro forbidden hforbidden hcontained
  exact hfree forbidden hforbidden
    ((hcontained.trans
      ⟨(SimpleGraph.Embedding.map embedding subgraph).toCopy⟩).mono_right hsub)

lemma eventually_constant_le_positive_nat_rpow
    (constant coefficient exponent : ℝ)
    (hcoefficient : 0 < coefficient)
    (hexponent : 0 < exponent) :
    ∀ᶠ n : ℕ in Filter.atTop,
      constant ≤ coefficient * (n : ℝ) ^ exponent := by
  have hpower :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ exponent)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexponent).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpower.eventually
    (Filter.eventually_ge_atTop (constant / coefficient))]
    with n hn
  calc
    constant = coefficient * (constant / coefficient) := by
      field_simp
    _ ≤ coefficient * (n : ℝ) ^ exponent :=
      mul_le_mul_of_nonneg_left hn hcoefficient.le

lemma extremalScale_sixteenth_power
    {n : ℕ} (hn : 0 < n) :
    (extremalScale n) ^ 16 =
      (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extremalScale
  calc
    ((n : ℝ) ^ ((4 : ℝ) / 3)) ^ 16 =
        (n : ℝ) ^ (((4 : ℝ) / 3) * (16 : ℝ)) := by
      exact (Real.rpow_mul_natCast hnreal.le
        ((4 : ℝ) / 3) 16).symm
    _ = (n : ℝ) ^ ((21 : ℝ) + (1 : ℝ) / 3) := by
      congr 1
      norm_num
    _ = (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      simp [Real.rpow_add hnreal]

lemma familyLittleO_of_sixteenth_power_host_bound
    (family : Finset FiniteGraph) (constant : ℝ)
    (hbound : ∀ (n : ℕ) (host : SimpleGraph (Fin n)),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21) :
    FamilyLittleO family := by
  apply familyLittleO_of_eventual_host_bounds
  intro ε hε
  have hεpow : 0 < ε ^ (16 : ℕ) := pow_pos hε _
  have hconstant := eventually_constant_le_positive_nat_rpow
    constant (ε ^ (16 : ℕ)) ((1 : ℝ) / 3)
    hεpow (by norm_num)
  filter_upwards [hconstant, Filter.eventually_gt_atTop 0]
    with n hn hnpositive
  intro host hfree
  have hhost := hbound n host hfree
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have htarget :
      (host.edgeFinset.card : ℝ) ^ 16 ≤
        (ε * extremalScale n) ^ 16 := by
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21 := hhost
      _ ≤ (ε ^ (16 : ℕ) * (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (n : ℝ) ^ 21 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (ε * extremalScale n) ^ 16 := by
        rw [mul_pow, extremalScale_sixteenth_power hnpositive]
        ring
  have hresult :
      (Nat.card host.edgeSet : ℝ) ≤ ε * extremalScale n := by
    apply le_of_pow_le_pow_left₀
      (by norm_num : (16 : ℕ) ≠ 0)
      (mul_nonneg hε.le (extremalScale_nonneg n))
    simpa only [edgeFinset_card_eq_natCard] using htarget
  simpa only [edgeFinset_card_eq_natCard] using hresult

noncomputable def compactnessDegreePowerConstant : ℝ :=
  (48 : ℝ) ^ (4 : ℕ) + 1769472 + 1

theorem proposedFamilyFree_minDegree_ambient_sixteenth_power_le
    {N n : ℕ} (host : SimpleGraph (Fin N))
    (hN : 0 < N) (hn : 0 < n) (hNn : N ≤ n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin N, d ≤ host.degree v) :
    (d : ℝ) ^ 16 ≤
      compactnessDegreePowerConstant * (n : ℝ) ^ 5 := by
  classical
  have hNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoefLow :
      (48 : ℝ) ^ (4 : ℕ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefHigh :
      (1769472 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefOne : (1 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  by_cases hd : 2 ≤ d
  · by_cases hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)
    · have hhigh := proposedFamilyFree_minDegree_sixteenth_power_le
        host hN hfree hbip d hd hdegree hthreshold
      calc
        (d : ℝ) ^ 16 ≤ 1769472 * (N : ℝ) ^ 5 := hhigh
        _ ≤ 1769472 * (n : ℝ) ^ 5 := by
          gcongr
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefHigh (by positivity)
    · have hlow := fourPathHeavyThreshold_low_degree_fourth_le
        N d hN hd hthreshold
      have hfour :
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        calc
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by gcongr
          _ = (n : ℝ) ^ 4 * 1 := by ring
          _ ≤ (n : ℝ) ^ 4 * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnreal (by positivity)
          _ = (n : ℝ) ^ 5 := by ring
      calc
        (d : ℝ) ^ 16 = ((d : ℝ) ^ 4) ^ 4 := by ring
        _ ≤ (48 * (N : ℝ)) ^ 4 := by gcongr
        _ = (48 : ℝ) ^ 4 * (N : ℝ) ^ 4 := by ring
        _ ≤ (48 : ℝ) ^ 4 * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_left hfour (by positivity)
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefLow (by positivity)
  · have hdNat : d ≤ 1 := by omega
    have hdReal : (d : ℝ) ≤ 1 := by exact_mod_cast hdNat
    calc
      (d : ℝ) ^ 16 ≤ (1 : ℝ) ^ 16 := by gcongr
      _ = 1 ^ (5 : ℕ) := by norm_num
      _ ≤ (n : ℝ) ^ 5 := by gcongr
      _ = 1 * (n : ℝ) ^ 5 := by ring
      _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hcoefOne (by positivity)

noncomputable def compactnessHostPowerConstant : ℝ :=
  (2 : ℝ) ^ (16 : ℕ) * compactnessDegreePowerConstant

theorem proposedFamilyFree_sixteenth_power_host_bound
    (n : ℕ) (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host) :
    (host.edgeFinset.card : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  by_cases hzero : host.edgeFinset.card = 0
  · simp only [hzero, Nat.cast_zero, zero_pow (by norm_num : 16 ≠ 0)]
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  · have hpositive : 0 < host.edgeFinset.card :=
      Nat.pos_of_ne_zero hzero
    obtain ⟨N, B, f, hN, hNn, hBbip, hmap, hminimum,
      _hminimum_pointwise⟩ :=
      exists_bipartite_min_degree_subgraph host hpositive
    have hn : 0 < n := by
      omega
    have hBfree : FamilyFree proposedFamily B :=
      familyFree_of_embedded_subgraph host B f hmap hfree
    let d : ℕ := B.minDegree
    have hdegree : ∀ v : Fin N, d ≤ B.degree v := by
      intro v
      exact B.minDegree_le_degree v
    have hminimumNat :
        host.edgeFinset.card ≤ 2 * n * d := by
      simpa only [d] using hminimum
    have hminimumReal :
        (host.edgeFinset.card : ℝ) ≤
          2 * (n : ℝ) * (d : ℝ) := by
      exact_mod_cast hminimumNat
    have hdPower := proposedFamilyFree_minDegree_ambient_sixteenth_power_le
      B hN hn hNn hBfree hBbip d hdegree
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          (2 * (n : ℝ) * (d : ℝ)) ^ 16 := by
        gcongr
      _ = (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 * (d : ℝ) ^ 16 := by
        ring
      _ ≤ (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 *
          (compactnessDegreePowerConstant * (n : ℝ) ^ 5) := by
        gcongr
      _ = compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
        unfold compactnessHostPowerConstant
        ring

theorem proposedFamily_familyLittleO :
    FamilyLittleO proposedFamily :=
  familyLittleO_of_sixteenth_power_host_bound
    proposedFamily compactnessHostPowerConstant
    proposedFamilyFree_sixteenth_power_host_bound

end AsymptoticExtraction

noncomputable section CycleBounds

open Filter Finset SimpleGraph
open scoped Topology

theorem four_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    four_cycle_uniform_manuscript_lower hn

theorem six_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    six_cycle_uniform_manuscript_lower hn

theorem member_eventual_lower_of_prime_power_avoidance
    {forbidden : FiniteGraph}
    (hmember : forbidden ∈ proposedFamily)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.graph.Free
        (symplecticQuadrangle (GaloisField t j))) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount t)]
    with n hn
  simpa [manuscriptLowerConstant, extremalScale] using
    quadrangle_uniform_lower_of_prime_power_avoidance
      forbidden.graph
      (proposedFamily_member_no_isolated hmember)
      t ht htgap hfree hn

theorem uniformMemberLower_of_characteristic_avoidance
    (hj : ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)))
    (hk : ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j))) :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  proposedFamily_induction
    (P := fun graph => ∀ᶠ n : ℕ in Filter.atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n graph.graph : ℝ))
    (by simpa [finiteCycle] using four_cycle_eventual_manuscript_lower)
    (by simpa [finiteCycle] using six_cycle_eventual_manuscript_lower)
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (jQuotient_mem_proposedFamily hf)
      2 (by norm_num) (by norm_num) (hj f hf))
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (kQuotient_mem_proposedFamily hf)
      3 (by norm_num) (by norm_num) (hk f hf))

end CycleBounds

noncomputable section Counterexample

open SimpleGraph

theorem proposedFamily_odd_characteristic_avoidance :
    ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j)) := by
  intro f hf j _
  exact symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (GaloisField 3 j)
    ((CharP.cast_eq_zero_iff (GaloisField 3 j) 3 2).not.mpr (by norm_num)) hf

theorem proposedFamily_even_characteristic_avoidance :
    ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)) :=
  fun _ hf j _ =>
    symplecticQuadrangle_no_encoded_jQuotient_of_char_two
      (GaloisField 2 j) hf

theorem proposedFamily_uniformMemberLower :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  uniformMemberLower_of_characteristic_avoidance
    proposedFamily_even_characteristic_avoidance
    proposedFamily_odd_characteristic_avoidance

theorem proposedFamily_not_compact :
    ¬ IsCompactFamily proposedFamily :=
  proposedFamily_not_compact_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower

theorem not_erdos_180 :
    ¬ CompactnessConjectureStatement :=
  not_compactnessConjecture_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower

end Counterexample

noncomputable section Connectedness

open Finset SimpleGraph

lemma jTemplate_connected : jTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable jTemplate).2
  let root : JVertex := .inl (.inl (2 : Fin 4))
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inl (jBase copy base)))
        (.inr (.inl (copy, (base, center)))) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inr (copy, center)))
        (.inr (.inl (copy, (base, center)))) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hrootCenter (copy : Fin 2) (center : Fin 2) :
      jTemplate.Reachable root (.inl (.inr (copy, center))) := by
    have hfirst :
        jTemplate.Adj root
          (.inr (.inl (copy, ((1 : Fin 3), center)))) := by
      simpa [root, jBase] using hbasePair copy 1 center
    exact hfirst.reachable.trans
      (hcenterPair copy 1 center).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Reachable root
        (.inr (.inl (copy, (base, center)))) :=
    (hrootCenter copy center).trans (hcenterPair copy base center).reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      jTemplate.Reachable root (.inl (.inl (jBase copy base))) :=
    (hrootPair copy base 0).trans (hbasePair copy base 0).symm.reachable
  intro vertex
  rcases vertex with (base | ⟨copy, center⟩) |
      (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · simpa [jBase] using hrootBase 0 0
    · simpa [jBase] using hrootBase 1 0
    · simpa [jBase] using hrootBase 0 1
    · simpa [jBase] using hrootBase 0 2
  · exact hrootCenter copy center
  · exact hrootPair copy base center
  · cases lastVertex
    have hjoin :
        jTemplate.Adj (.inl (.inl (0 : Fin 4)))
          (.inr (.inr ())) := by
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    have hzero :
        jTemplate.Reachable root (.inl (.inl (0 : Fin 4))) := by
      simpa [jBase] using hrootBase 0 0
    exact hzero.trans hjoin.reachable

lemma kTemplate_connected : kTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable kTemplate).2
  let root : KVertex := ((0 : Fin 2), kSpecifiedCenter)
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inl base))
        (copy, .inr (base, center)) := by
    simp [kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      subdivisionRelation]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inr center))
        (copy, .inr (base, center)) := by
    simp [kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      subdivisionRelation]
  have hbridge :
      kTemplate.Adj root ((1 : Fin 2), kSpecifiedCenter) := by
    simp [root, kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      kSpecifiedCenter, subdivisionRelation]
  have hhub (copy : Fin 2) :
      kTemplate.Reachable root (copy, kSpecifiedCenter) := by
    fin_cases copy
    · exact SimpleGraph.Reachable.refl root
    · exact hbridge.reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inl base)) := by
    have hfirst :
        kTemplate.Reachable root (copy, .inr (base, (0 : Fin 3))) := by
      exact (hhub copy).trans
        (by
          simpa [kSpecifiedCenter] using
            (hcenterPair copy base 0).reachable)
    exact hfirst.trans (hbasePair copy base 0).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inr (base, center)) :=
    (hrootBase copy base).trans (hbasePair copy base center).reachable
  have hrootCenter (copy : Fin 2) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inr center)) :=
    (hrootPair copy 0 center).trans
      (hcenterPair copy 0 center).symm.reachable
  intro vertex
  rcases vertex with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · exact hrootBase copy base
  · exact hrootCenter copy center
  · exact hrootPair copy base center

lemma quotientGraph_connected_of_colorRespecting
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f)
    (hconnected : graph.Connected) :
    (quotientGraph graph f).Connected := by
  refine SimpleGraph.Connected.map
    (colorRespectingQuotientProjectionHom graph color hproper f hf)
    ?_ hconnected
  rintro ⟨_, ⟨v, rfl⟩⟩
  exact ⟨v, rfl⟩

lemma encodeFiniteGraph_connected
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hconnected : graph.Connected) :
    (encodeFiniteGraph graph).graph.Connected := by
  change (graph.map (Fintype.equivFin V).toEmbedding).Connected
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.Iso.map (Fintype.equivFin V) graph)).mp hconnected

lemma encodedJQuotient_connected {f : JVertex → JVertex}
    (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1 jTemplate_connected)

lemma encodedKQuotient_connected {f : KVertex → KVertex}
    (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1 kTemplate_connected)

theorem finiteCycle_connected {n : ℕ} (hn : 0 < n) :
    (finiteCycle n).graph.Connected := by
  change (SimpleGraph.cycleGraph n).Connected
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨SimpleGraph.cycleGraph_preconnected⟩

theorem proposedFamily_member_connected
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.Connected :=
  proposedFamily_induction (P := fun graph => graph.graph.Connected)
    (finiteCycle_connected (by norm_num : 0 < (4 : ℕ)))
    (finiteCycle_connected (by norm_num : 0 < (6 : ℕ)))
    (fun _ hf => encodedJQuotient_connected hf)
    (fun _ hf => encodedKQuotient_connected hf)
    forbidden hforbidden

end Connectedness

noncomputable section Bipartiteness

open Finset SimpleGraph

lemma colorRespectingQuotient_isBipartite
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    (quotientGraph graph f).IsBipartite := by
  classical
  let representative : Set.range f → V :=
    fun vertex => Classical.choose vertex.property
  have hrepresentative (vertex : Set.range f) :
      f (representative vertex) = (vertex : V) :=
    Classical.choose_spec vertex.property
  let quotientColor : Set.range f → Bool :=
    fun vertex => color (representative vertex)
  have hdirected {u v : Set.range f}
      (h : quotientRelation graph f u v) :
      quotientColor u ≠ quotientColor v := by
    rcases h with ⟨x, y, hx, hy, hxy⟩
    change color (representative u) ≠ color (representative v)
    intro heq
    apply hproper hxy
    calc
      color x = color (representative u) :=
        (hf (representative u) x
          ((hrepresentative u).trans hx.symm)).symm
      _ = color (representative v) := heq
      _ = color y :=
        hf (representative v) y
          ((hrepresentative v).trans hy.symm)
  have hcoloring : (quotientGraph graph f).Coloring Bool :=
    SimpleGraph.Coloring.mk quotientColor (by
      intro u v hadj
      change (SimpleGraph.fromRel (quotientRelation graph f)).Adj u v at hadj
      rcases
          (SimpleGraph.fromRel_adj (quotientRelation graph f) u v).mp hadj with
        ⟨_, hforward | hbackward⟩
      · exact hdirected hforward
      · exact Ne.symm (hdirected hbackward))
  simpa using hcoloring.colorable

lemma encodeFiniteGraph_isBipartite
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hbipartite : graph.IsBipartite) :
    (encodeFiniteGraph graph).graph.IsBipartite := by
  classical
  exact SimpleGraph.Colorable.map
    (Fintype.equivFin V).toEmbedding hbipartite

lemma encodedJQuotient_isBipartite
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1)

lemma encodedKQuotient_isBipartite
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1)

theorem proposedFamily_member_isBipartite
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.IsBipartite :=
  proposedFamily_induction (P := fun graph => graph.graph.IsBipartite)
    (SimpleGraph.cycleGraph.bicoloring_of_even 4 (by decide)).colorable
    (SimpleGraph.cycleGraph.bicoloring_of_even 6 (by decide)).colorable
    (fun _ hf => encodedJQuotient_isBipartite hf)
    (fun _ hf => encodedKQuotient_isBipartite hf)
    forbidden hforbidden

end Bipartiteness

noncomputable section FamilyExtremal

open Finset SimpleGraph

theorem finiteNatSup_sixteenth_power_le
    {α : Type*} (s : Finset α) (weight : α → ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hweight : ∀ a ∈ s, (weight a : ℝ) ^ 16 ≤ bound) :
    ((s.sup weight : ℕ) : ℝ) ^ 16 ≤ bound := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst s
    simpa using hbound
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup s hs weight
    simpa [hmax] using hweight a ha

theorem proposedFamily_familyExtremal_sixteenth_power_le (n : ℕ) :
    (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  have hbound :
      0 ≤ compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  unfold familyExtremal
  apply finiteNatSup_sixteenth_power_le
    (Finset.univ.filter (FamilyFree proposedFamily))
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)
    (compactnessHostPowerConstant * (n : ℝ) ^ 21) hbound
  intro host hhost
  exact proposedFamilyFree_sixteenth_power_host_bound n host
    (Finset.mem_filter.mp hhost).2

theorem proposedFamily_familyExtremal_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (familyExtremal proposedFamily n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((21 : ℝ) / 16)) := by
  let C : ℝ := max compactnessHostPowerConstant 1
  have hCone : 1 ≤ C := le_max_right _ _
  have hCnonneg : 0 ≤ C := zero_le_one.trans hCone
  have hconstant : compactnessHostPowerConstant ≤ C ^ (16 : ℕ) :=
    (le_max_left _ _).trans (le_self_pow₀ hCone (by norm_num))
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Filter.Eventually.of_forall fun n => ?_⟩
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hscale :
      ((n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) =
        (n : ℝ) ^ (21 : ℕ) := by
    rw [← Real.rpow_mul_natCast hnnonneg ((21 : ℝ) / 16) 16]
    norm_num
  have hpower :
      (familyExtremal proposedFamily n : ℝ) ^ (16 : ℕ) ≤
        (C * (n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) := by
    calc
      (familyExtremal proposedFamily n : ℝ) ^ (16 : ℕ) ≤
          compactnessHostPowerConstant * (n : ℝ) ^ (21 : ℕ) :=
        proposedFamily_familyExtremal_sixteenth_power_le n
      _ ≤ C ^ (16 : ℕ) * (n : ℝ) ^ (21 : ℕ) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = (C * (n : ℝ) ^ ((21 : ℝ) / 16)) ^ (16 : ℕ) := by
        rw [mul_pow, hscale]
  have hbound := le_of_pow_le_pow_left₀
    (by norm_num : (16 : ℕ) ≠ 0)
    (mul_nonneg hCnonneg (Real.rpow_nonneg hnnonneg _)) hpower
  have hextremal_nonneg :
      (0 : ℝ) ≤ (familyExtremal proposedFamily n : ℝ) :=
    Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
    abs_of_nonneg (Real.rpow_nonneg hnnonneg _)] using hbound

end FamilyExtremal

noncomputable section MainTheorem

open Finset SimpleGraph
open scoped Classical

noncomputable def compactnessSharpHostPowerConstant : ℝ :=
  compactnessHostPowerConstant

theorem compactnessSharpHostPowerConstant_pos :
    0 < compactnessSharpHostPowerConstant := by
  unfold compactnessSharpHostPowerConstant compactnessHostPowerConstant
    compactnessDegreePowerConstant
  positivity

theorem checkedManuscriptCounterexample :
    proposedFamily.Nonempty ∧
      (∀ forbidden ∈ proposedFamily,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      (0 : ℝ) < manuscriptLowerConstant ∧
      UniformMemberLower proposedFamily manuscriptLowerConstant ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree proposedFamily host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤
            compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
          compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily proposedFamily ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily_nonempty, ?_,
    manuscriptLowerConstant_pos, proposedFamily_uniformMemberLower,
    proposedFamilyFree_sixteenth_power_host_bound,
    proposedFamily_familyExtremal_sixteenth_power_le,
    by norm_num, by norm_num,
    proposedFamily_not_compact, not_erdos_180⟩
  intro forbidden hforbidden
  exact ⟨proposedFamily_member_connected hforbidden,
    proposedFamily_member_isBipartite hforbidden,
    proposedFamily_isCyclic forbidden hforbidden⟩

theorem quantitativeCompactnessCounterexample :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  obtain ⟨hnonempty, hgeometry, hlower_pos, hlower, hhost, hfamily,
    hgap_pos, hexponents, hnot_compact, hconjecture⟩ :=
    checkedManuscriptCounterexample
  refine ⟨proposedFamily, manuscriptLowerConstant,
    compactnessHostPowerConstant, hnonempty, hgeometry, hlower_pos, ?_,
    hlower, hhost, hfamily, hgap_pos, hexponents, hnot_compact,
    hconjecture⟩
  simpa [compactnessSharpHostPowerConstant] using
    compactnessSharpHostPowerConstant_pos

theorem compactnessCounterexample_bigO :
    ∃ (family : Finset FiniteGraph) (c : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      UniformMemberLower family c ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (familyExtremal family n : ℝ))
        (fun n : ℕ =>
          (n : ℝ) ^ ((4 : ℝ) / 3 - (1 : ℝ) / 48)) ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily, manuscriptLowerConstant,
    proposedFamily_nonempty, ?_, manuscriptLowerConstant_pos,
    proposedFamily_uniformMemberLower, ?_, proposedFamily_not_compact,
    not_erdos_180⟩
  · intro forbidden hforbidden
    exact ⟨proposedFamily_member_connected hforbidden,
      proposedFamily_member_isBipartite hforbidden,
      proposedFamily_isCyclic forbidden hforbidden⟩
  · convert proposedFamily_familyExtremal_isBigO using 1
    norm_num

end MainTheorem

end CompactnessConjecture

namespace TwoDegenerateGraphs

open Filter Finset SimpleGraph
open scoped Topology

section BinaryEntropy

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

noncomputable def tau : ℝ := (Real.sqrt 3 - 1) / 2

noncomputable def kappa : ℝ := 3 / 2 - (3 / 4) * logTwo 3

noncomputable def certifiedWindowWidth : ℝ :=
  logTwo ((97 + 56 * Real.sqrt 3) / 192) / 4

theorem twelve_sevenths_lt_sqrt_three : (12 : ℝ) / 7 < Real.sqrt 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  nlinarith

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem binaryEntropy_nonneg {x : ℝ} (hzero : 0 ≤ x)
    (hone : x ≤ 1) : 0 ≤ binaryEntropy x := by
  exact div_nonneg (Real.binEntropy_nonneg hzero hone) log_two_pos.le

theorem binaryEntropy_le_one (x : ℝ) : binaryEntropy x ≤ 1 := by
  unfold binaryEntropy
  apply (div_le_iff₀ log_two_pos).2
  simpa using (Real.binEntropy_le_log_two (p := x))

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  simp [binaryEntropy]

@[fun_prop] theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _

theorem binaryEntropy_scale_le (probability scale : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hscale_zero : 0 ≤ scale)
    (hscale_one : scale ≤ 1) :
    scale * binaryEntropy probability ≤
      binaryEntropy (scale * probability) := by
  have hconcavity := Real.strictConcave_binEntropy.concaveOn.2
    (show probability ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hprobability_zero, hprobability_one⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    hscale_zero (sub_nonneg.mpr hscale_one)
    (show scale + (1 - scale) = 1 by ring)
  have hnatural :
      scale * Real.binEntropy probability ≤
        Real.binEntropy (scale * probability) := by
    simpa [smul_eq_mul] using hconcavity
  unfold binaryEntropy
  calc
    scale * (Real.binEntropy probability / Real.log 2) =
      (scale * Real.binEntropy probability) / Real.log 2 := by ring
    _ ≤ Real.binEntropy (scale * probability) / Real.log 2 :=
      (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

theorem binaryEntropy_subadditive (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y ≤ 1) :
    binaryEntropy (x + y) ≤ binaryEntropy x + binaryEntropy y := by
  by_cases hzero : x + y = 0
  · have hxzero : x = 0 := by linarith
    have hyzero : y = 0 := by linarith
    simp [hxzero, hyzero]
  have hpositive : 0 < x + y :=
    lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hzero)
  have hxscale : 0 ≤ x / (x + y) :=
    div_nonneg hx hpositive.le
  have hyscale : 0 ≤ y / (x + y) :=
    div_nonneg hy hpositive.le
  have hxscale_one : x / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hyscale_one : y / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hxentropy := binaryEntropy_scale_le (x + y) (x / (x + y))
    (add_nonneg hx hy) hsum hxscale hxscale_one
  have hyentropy := binaryEntropy_scale_le (x + y) (y / (x + y))
    (add_nonneg hx hy) hsum hyscale hyscale_one
  have hxidentity : x / (x + y) * (x + y) = x := by
    field_simp [hpositive.ne']
  have hyidentity : y / (x + y) * (x + y) = y := by
    field_simp [hpositive.ne']
  rw [hxidentity] at hxentropy
  rw [hyidentity] at hyentropy
  have hcombined := add_le_add hxentropy hyentropy
  have hleft :
      x / (x + y) * binaryEntropy (x + y) +
          y / (x + y) * binaryEntropy (x + y) =
        binaryEntropy (x + y) := by
    field_simp [hpositive.ne']
  rw [hleft] at hcombined
  exact hcombined

theorem abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (x y : ℝ)
    (hxzero : 0 ≤ x) (hxone : x ≤ 1)
    (hyzero : 0 ≤ y) (hyone : y ≤ 1) :
    |binaryEntropy x - binaryEntropy y| ≤
      binaryEntropy |x - y| := by
  have hordered :
      ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x ≤ y →
        |binaryEntropy x - binaryEntropy y| ≤ binaryEntropy |x - y| := by
    intro a b hazero haone hbzero hbone hab
    have hdifference : 0 ≤ b - a := sub_nonneg.mpr hab
    have hforward :
        binaryEntropy b ≤ binaryEntropy a + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive a (b - a)
        hazero hdifference (by linarith)
      have hargument : a + (b - a) = b := by ring
      rwa [hargument] at h
    have hbackward :
        binaryEntropy a ≤ binaryEntropy b + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive (1 - b) (b - a)
        (sub_nonneg.mpr hbone) hdifference (by linarith)
      have hargument : 1 - b + (b - a) = 1 - a := by ring
      rw [hargument, binaryEntropy_one_sub, binaryEntropy_one_sub] at h
      exact h
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_le]
    have hneg : -(a - b) = b - a := by ring
    rw [hneg]
    constructor <;> linarith
  by_cases hxy : x ≤ y
  · exact hordered x y hxzero hxone hyzero hyone hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := hordered y x hyzero hyone hxzero hxone hyx
    simpa [abs_sub_comm] using h

theorem binaryEntropy_mono_on_half
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyhalf : y ≤ (2 : ℝ)⁻¹) :
    binaryEntropy x ≤ binaryEntropy y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hxhalf : x ≤ (2 : ℝ)⁻¹ := hxy.trans hyhalf
  have hnatural := Real.binEntropy_strictMonoOn.monotoneOn
    (show x ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hx, hxhalf⟩)
    (show y ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hy, hyhalf⟩)
    hxy
  unfold binaryEntropy
  exact (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

noncomputable def binaryPinskerGap (q : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy q - (2 * q - 1) ^ 2 / 2

noncomputable def binaryPinskerGapDeriv (q : ℝ) : ℝ :=
  Real.log q - Real.log (1 - q) - 2 * (2 * q - 1)

noncomputable def binaryPinskerGapDerivTwo (q : ℝ) : ℝ :=
  q⁻¹ + (1 - q)⁻¹ - 4

theorem binaryPinskerGap_continuous : Continuous binaryPinskerGap := by
  unfold binaryPinskerGap
  fun_prop

theorem binaryPinskerGap_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGap (binaryPinskerGapDeriv q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hderiv :=
    ((Real.hasDerivAt_binEntropy hqzero hqone).const_sub (Real.log 2)).sub
      ((hlinear.pow 2).div_const 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGap, binaryPinskerGapDeriv]; ring)

theorem binaryPinskerGapDeriv_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGapDeriv (binaryPinskerGapDerivTwo q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hcomplement : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have hcomplement_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hqone.symm
  have hderiv :=
    ((Real.hasDerivAt_log hqzero).sub
      (hcomplement.log hcomplement_ne)).sub (hlinear.const_mul 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGapDeriv, binaryPinskerGapDerivTwo]; ring)

theorem binaryPinskerGapDerivTwo_nonneg {q : ℝ}
    (hqzero : 0 < q) (hqone : q < 1) :
    0 ≤ binaryPinskerGapDerivTwo q := by
  have hcomplement : 0 < 1 - q := sub_pos.mpr hqone
  have hidentity :
      binaryPinskerGapDerivTwo q =
        (2 * q - 1) ^ 2 / (q * (1 - q)) := by
    unfold binaryPinskerGapDerivTwo
    field_simp [hqzero.ne', hcomplement.ne']
    ring
  rw [hidentity]
  exact div_nonneg (sq_nonneg _) (mul_pos hqzero hcomplement).le

theorem binaryPinskerGap_convex :
    ConvexOn ℝ (Set.Icc 0 1) binaryPinskerGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := binaryPinskerGapDeriv)
    (f'' := binaryPinskerGapDerivTwo)
    (convex_Icc (0 : ℝ) 1)
    binaryPinskerGap_continuous.continuousOn ?_ ?_ ?_
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact (binaryPinskerGap_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact
      (binaryPinskerGapDeriv_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact binaryPinskerGapDerivTwo_nonneg hq'.1 hq'.2

@[simp] theorem binaryPinskerGap_half :
    binaryPinskerGap ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGap
  rw [Real.binEntropy_two_inv]
  norm_num

@[simp] theorem binaryPinskerGapDeriv_half :
    binaryPinskerGapDeriv ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGapDeriv
  norm_num

theorem binary_pinsker (q : ℝ) (hqzero : 0 ≤ q) (hqone : q ≤ 1) :
    Real.binEntropy q ≤
      Real.log 2 - (2 * q - 1) ^ 2 / 2 := by
  have habove :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ)⁻¹ ≤ x →
        0 ≤ binaryPinskerGap x := by
    intro x hxzero hxone hxhalf
    by_cases hxeq : x = (2 : ℝ)⁻¹
    · simp [hxeq]
    · have hxstrict : (2 : ℝ)⁻¹ < x :=
        lt_of_le_of_ne hxhalf (Ne.symm hxeq)
      have hmid :
          HasDerivAt binaryPinskerGap 0 ((2 : ℝ)⁻¹) := by
        convert binaryPinskerGap_hasDerivAt
          (q := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1
        exact binaryPinskerGapDeriv_half.symm
      have hslope := binaryPinskerGap_convex.le_slope_of_hasDerivAt
        (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show x ∈ Set.Icc 0 1 from ⟨hxzero, hxone⟩)
        hxstrict hmid
      rw [slope_def_field, binaryPinskerGap_half, sub_zero] at hslope
      rcases (div_nonneg_iff.mp hslope) with hpositive | hnegative
      · exact hpositive.1
      · exfalso
        have hden : 0 < x - (2 : ℝ)⁻¹ := sub_pos.mpr hxstrict
        linarith [hnegative.2]
  by_cases hhalf : (2 : ℝ)⁻¹ ≤ q
  · have hgap := habove q hqzero hqone hhalf
    unfold binaryPinskerGap at hgap
    linarith
  · have hcomplement : (2 : ℝ)⁻¹ ≤ 1 - q := by
      norm_num at hhalf ⊢
      linarith
    have hgap := habove (1 - q) (sub_nonneg.mpr hqone)
      (by linarith) hcomplement
    unfold binaryPinskerGap at hgap
    rw [Real.binEntropy_one_sub] at hgap
    nlinarith

theorem log_le_tangent {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at hlog
  linarith

theorem log_four_thirds_lt_one_third :
    Real.log ((4 : ℝ) / 3) < (1 : ℝ) / 3 := by
  have hlog := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 : ℝ) / 3 ≠ 1 by norm_num)
  norm_num at hlog ⊢
  linarith

theorem sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  have hroot := Real.sqrt_nonneg (1 + x)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x by linarith)
  nlinarith [sq_nonneg x]

theorem normalized_binary_cauchy (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    a * x + b * y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hrad : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hroot := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hsquare := Real.sq_sqrt hrad
  have hidentity :
      (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
        (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  rw [hab, one_mul] at hidentity
  nlinarith [sq_nonneg (a * y - b * x)]

theorem binary_log_sum_bound (probability zeroWeight oneWeight : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hzeroWeight : 0 < zeroWeight)
    (honeWeight : 0 < oneWeight) :
    Real.binEntropy probability +
        (1 - probability) * Real.log zeroWeight +
        probability * Real.log oneWeight ≤
      Real.log (zeroWeight + oneWeight) := by
  by_cases hzero : probability = 0
  · subst probability
    simpa using Real.log_le_log hzeroWeight
      (le_add_of_nonneg_right honeWeight.le)
  by_cases hone : probability = 1
  · subst probability
    simpa using Real.log_le_log honeWeight
      (le_add_of_nonneg_left hzeroWeight.le)
  have hprobability_pos : 0 < probability :=
    lt_of_le_of_ne hprobability_zero (Ne.symm hzero)
  have hcomplement_pos : 0 < 1 - probability :=
    sub_pos.mpr (lt_of_le_of_ne hprobability_one hone)
  have hnormalize :
      (1 - probability) * (zeroWeight / (1 - probability)) +
          probability * (oneWeight / probability) =
        zeroWeight + oneWeight := by
    field_simp [hprobability_pos.ne', hcomplement_pos.ne']
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.2
    (show zeroWeight / (1 - probability) ∈ Set.Ioi (0 : ℝ) from
      div_pos hzeroWeight hcomplement_pos)
    (show oneWeight / probability ∈ Set.Ioi (0 : ℝ) from
      div_pos honeWeight hprobability_pos)
    hcomplement_pos.le hprobability_pos.le
    (show (1 - probability) + probability = 1 by ring)
  simp only [smul_eq_mul] at hjensen
  rw [hnormalize] at hjensen
  rw [Real.log_div hzeroWeight.ne' hcomplement_pos.ne',
    Real.log_div honeWeight.ne' hprobability_pos.ne'] at hjensen
  have hentropy :
      Real.binEntropy probability =
        -(1 - probability) * Real.log (1 - probability) -
          probability * Real.log probability := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  rw [hentropy]
  linarith

noncomputable def entropyTangentSigma : ℝ :=
  4 / (3 * Real.sqrt 2)

noncomputable def entropyTangentRho : ℝ :=
  Real.sqrt 2 / Real.sqrt 3

theorem entropyTangentSigma_pos : 0 < entropyTangentSigma := by
  unfold entropyTangentSigma
  positivity

theorem entropyTangentRho_pos : 0 < entropyTangentRho := by
  unfold entropyTangentRho
  positivity

theorem log_entropyTangentSigma :
    Real.log entropyTangentSigma =
      (3 / 2 : ℝ) * Real.log 2 - Real.log 3 := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold entropyTangentSigma
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), hlogfour]
  ring

theorem log_entropyTangentRho :
    Real.log entropyTangentRho =
      (Real.log 2 - Real.log 3) / 2 := by
  unfold entropyTangentRho
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)]
  ring

theorem sqrt_three_mul_entropyTangentRho :
    Real.sqrt 3 * entropyTangentRho = Real.sqrt 2 := by
  unfold entropyTangentRho
  have hthree : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp [hthree]

noncomputable def entropyTangentZeroCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (3 - 2 * q) / 4

noncomputable def entropyTangentOneCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + 2 * q) / 4

theorem entropyTangentZeroCoefficient_eq (q : ℝ) :
    (1 - q) ^ 2 / entropyTangentSigma +
        q ^ 2 / (3 * entropyTangentSigma) +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentZeroCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentZeroCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem entropyTangentOneCoefficient_eq (q : ℝ) :
    (1 - q) ^ 2 / (3 * entropyTangentSigma) +
        q ^ 2 / entropyTangentSigma +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentOneCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentOneCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem entropyTangentCoefficient_norm (q : ℝ) :
    entropyTangentZeroCoefficient q ^ 2 +
        entropyTangentOneCoefficient q ^ 2 =
      1 + (2 * q - 1) ^ 2 / 4 := by
  unfold entropyTangentZeroCoefficient entropyTangentOneCoefficient
  calc
    (Real.sqrt 2 * (3 - 2 * q) / 4) ^ 2 +
        (Real.sqrt 2 * (1 + 2 * q) / 4) ^ 2 =
      (Real.sqrt 2) ^ 2 *
        (((3 - 2 * q) ^ 2 + (1 + 2 * q) ^ 2) / 16) := by ring
    _ = 1 + (2 * q - 1) ^ 2 / 4 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring

theorem entropyTangentLog_constant (q : ℝ) :
    ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
        2 * q * (1 - q) * Real.log entropyTangentRho =
      Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [log_entropyTangentSigma, log_entropyTangentRho,
    Real.log_div (by positivity) (by positivity), hlogfour]
  ring

noncomputable def binaryConditionalLogPotential (q zeroAmplitude oneAmplitude : ℝ) : ℝ :=
  Real.binEntropy q / 2 +
    (1 - q) ^ 2 * Real.log (zeroAmplitude + oneAmplitude / 3) +
    q ^ 2 * Real.log (zeroAmplitude / 3 + oneAmplitude) +
    2 * q * (1 - q) *
      Real.log ((zeroAmplitude + oneAmplitude) / Real.sqrt 3)

theorem binaryConditionalLogPotential_tangent_bound
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      Real.binEntropy q / 2 +
        Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) +
        Real.sqrt (1 + (2 * q - 1) ^ 2 / 4) - 1 := by
  have hsum : 0 < zeroAmplitude + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargzero : 0 < zeroAmplitude + oneAmplitude / 3 := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargone : 0 < zeroAmplitude / 3 + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hargmixed :
      0 < (zeroAmplitude + oneAmplitude) / Real.sqrt 3 :=
    div_pos hsum hthree
  have htangentzero := mul_le_mul_of_nonneg_left
    (log_le_tangent hargzero entropyTangentSigma_pos)
    (sq_nonneg (1 - q))
  have htangentone := mul_le_mul_of_nonneg_left
    (log_le_tangent hargone entropyTangentSigma_pos)
    (sq_nonneg q)
  have hmixedweight : 0 ≤ 2 * q * (1 - q) := by
    have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
    positivity
  have htangentmixed := mul_le_mul_of_nonneg_left
    (log_le_tangent hargmixed entropyTangentRho_pos)
    hmixedweight
  have hcombined :=
    add_le_add (add_le_add htangentzero htangentone) htangentmixed
  have hright :
      ((1 - q) ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude + oneAmplitude / 3) /
              entropyTangentSigma - 1) +
        q ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude / 3 + oneAmplitude) /
              entropyTangentSigma - 1)) +
        (2 * q * (1 - q)) *
          (Real.log entropyTangentRho +
            ((zeroAmplitude + oneAmplitude) / Real.sqrt 3) /
              entropyTangentRho - 1) =
        ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
          2 * q * (1 - q) * Real.log entropyTangentRho +
          zeroAmplitude * entropyTangentZeroCoefficient q +
          oneAmplitude * entropyTangentOneCoefficient q - 1 := by
    rw [← entropyTangentZeroCoefficient_eq,
      ← entropyTangentOneCoefficient_eq]
    field_simp [entropyTangentSigma_pos.ne',
      entropyTangentRho_pos.ne', hthree.ne']
    ring
  rw [hright, entropyTangentLog_constant] at hcombined
  have hcauchy := normalized_binary_cauchy
    zeroAmplitude oneAmplitude
    (entropyTangentZeroCoefficient q)
    (entropyTangentOneCoefficient q) hamplitudes
  rw [entropyTangentCoefficient_norm] at hcauchy
  unfold binaryConditionalLogPotential
  linarith

theorem binaryConditionalLogPotential_le_kappa
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      kappa * Real.log 2 := by
  have htangent := binaryConditionalLogPotential_tangent_bound
    q zeroAmplitude oneAmplitude hqzero hqone
    hzeroAmplitude honeAmplitude hamplitudes
  have hpinsker := binary_pinsker q hqzero hqone
  have hsqrt := sqrt_one_add_le ((2 * q - 1) ^ 2 / 4)
    (by positivity)
  have hlogscaled := mul_le_mul_of_nonneg_left
    log_four_thirds_lt_one_third.le
    (show 0 ≤ (2 * q - 1) ^ 2 / 4 by positivity)
  have hkappa :
      kappa * Real.log 2 =
        (3 / 2 : ℝ) * Real.log 2 -
          (3 / 4 : ℝ) * Real.log 3 := by
    unfold kappa logTwo
    field_simp [log_two_pos.ne']
  rw [hkappa]
  nlinarith [sq_nonneg (2 * q - 1)]

def binaryCoinMass (q : ℝ) (outcome : Bool) : ℝ :=
  if outcome then q else 1 - q

theorem binaryCoinMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (outcome : Bool) :
    0 ≤ binaryCoinMass q outcome := by
  cases outcome <;> simp [binaryCoinMass] <;> linarith

def independentBinaryPairMass (q : ℝ) (left right : Bool) : ℝ :=
  binaryCoinMass q left * binaryCoinMass q right

theorem independentBinaryPairMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (left right : Bool) :
    0 ≤ independentBinaryPairMass q left right := by
  exact mul_nonneg
    (binaryCoinMass_nonneg hqzero hqone left)
    (binaryCoinMass_nonneg hqzero hqone right)

theorem independentBinaryPairMass_sum (q : ℝ) :
    (∑ left : Bool, ∑ right : Bool,
      independentBinaryPairMass q left right) = 1 := by
  simp [Fintype.univ_bool, independentBinaryPairMass, binaryCoinMass]
  ring

structure BinaryPairKernel where
  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1
  childProbability : Bool → Bool → ℝ
  childProbability_nonneg : ∀ left right, 0 ≤ childProbability left right
  childProbability_le_one : ∀ left right, childProbability left right ≤ 1

namespace BinaryPairKernel

noncomputable def childMarginal (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      kernel.childProbability left right

noncomputable def conditionalEntropy (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy (kernel.childProbability left right)

def bitDisagreementProbability (parent : Bool) (childProbability : ℝ) : ℝ :=
  if parent then 1 - childProbability else childProbability

noncomputable def averageDisagreement (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      ((bitDisagreementProbability left
          (kernel.childProbability left right) +
        bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

theorem childMarginal_nonneg (kernel : BinaryPairKernel) :
    0 ≤ kernel.childMarginal := by
  unfold childMarginal
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (independentBinaryPairMass_nonneg
      kernel.parentProbability_nonneg kernel.parentProbability_le_one
      left right)
    (kernel.childProbability_nonneg left right)

theorem childMarginal_le_one (kernel : BinaryPairKernel) :
    kernel.childMarginal ≤ 1 := by
  unfold childMarginal
  calc
    (∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right *
          kernel.childProbability left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left
            (kernel.childProbability_le_one left right)
            (independentBinaryPairMass_nonneg
              kernel.parentProbability_nonneg kernel.parentProbability_le_one
              left right)
    _ = 1 := by
      simpa using independentBinaryPairMass_sum kernel.parentProbability

theorem childMarginal_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.childMarginal =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          kernel.childProbability false true +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          kernel.childProbability true false +
        kernel.parentProbability ^ 2 *
          kernel.childProbability true true := by
  simp [childMarginal, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass]
  ring

theorem conditionalEntropy_mul_log_two (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy * Real.log 2 =
      (1 - kernel.parentProbability) ^ 2 *
          Real.binEntropy (kernel.childProbability false false) +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          Real.binEntropy (kernel.childProbability false true) +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          Real.binEntropy (kernel.childProbability true false) +
        kernel.parentProbability ^ 2 *
          Real.binEntropy (kernel.childProbability true true) := by
  simp [conditionalEntropy, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass, binaryEntropy]
  field_simp [log_two_pos.ne']
  ring

theorem bitDisagreementProbability_mem_Icc (parent : Bool)
    (childProbability : ℝ)
    (hzero : 0 ≤ childProbability) (hone : childProbability ≤ 1) :
    0 ≤ bitDisagreementProbability parent childProbability ∧
      bitDisagreementProbability parent childProbability ≤ 1 := by
  cases parent <;> simp [bitDisagreementProbability] <;> constructor <;>
    linarith

theorem averageDisagreement_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        kernel.parentProbability * (1 - kernel.parentProbability) +
        kernel.parentProbability ^ 2 *
          (1 - kernel.childProbability true true) := by
  simp [averageDisagreement, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass,
    bitDisagreementProbability]
  ring

noncomputable def smoothed (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) : BinaryPairKernel where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability left right :=
    (1 - mixing) * kernel.childProbability left right + mixing / 2
  childProbability_nonneg := by
    intro left right
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one)
        (kernel.childProbability_nonneg left right))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro left right
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one left right)
      (sub_nonneg.mpr hmixing_one)
    nlinarith

theorem smoothed_childMarginal (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  rw [childMarginal_eq_four_outcomes,
    childMarginal_eq_four_outcomes kernel]
  simp [smoothed]
  ring

theorem smoothed_averageDisagreement (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  rw [averageDisagreement_eq_four_outcomes,
    averageDisagreement_eq_four_outcomes kernel]
  simp [smoothed]
  ring

noncomputable def smoothedConditionalEntropy
    (kernel : BinaryPairKernel) (mixing : ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy
        ((1 - mixing) * kernel.childProbability left right + mixing / 2)

theorem smoothedConditionalEntropy_continuous (kernel : BinaryPairKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop

theorem smoothed_conditionalEntropy (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := by
  rfl

theorem conditionalEntropy_logsum_reduction (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy * Real.log 2 -
        Real.binEntropy kernel.childMarginal / 2 -
        Real.log 3 * kernel.averageDisagreement ≤
      binaryConditionalLogPotential kernel.parentProbability
          (Real.sqrt (1 - kernel.childMarginal))
          (Real.sqrt kernel.childMarginal) -
        Real.binEntropy kernel.parentProbability / 2 := by
  let q : ℝ := kernel.parentProbability
  let v : ℝ := kernel.childMarginal
  let a : ℝ := Real.sqrt (1 - v)
  let b : ℝ := Real.sqrt v
  let z₀₀ : ℝ := kernel.childProbability false false
  let z₀₁ : ℝ := kernel.childProbability false true
  let z₁₀ : ℝ := kernel.childProbability true false
  let z₁₁ : ℝ := kernel.childProbability true true
  have hqzero : 0 ≤ q := kernel.parentProbability_nonneg
  have hqone : q ≤ 1 := kernel.parentProbability_le_one
  have hvzero : 0 < v := hmarginal_zero
  have hvone : v < 1 := hmarginal_one
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hvone)
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.mpr hvzero
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have h₀₀ := binary_log_sum_bound z₀₀ a (b / 3)
    (kernel.childProbability_nonneg false false)
    (kernel.childProbability_le_one false false)
    ha (by positivity)
  have h₀₁ := binary_log_sum_bound z₀₁
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg false true)
    (kernel.childProbability_le_one false true)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₀ := binary_log_sum_bound z₁₀
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg true false)
    (kernel.childProbability_le_one true false)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₁ := binary_log_sum_bound z₁₁ (a / 3) b
    (kernel.childProbability_nonneg true true)
    (kernel.childProbability_le_one true true)
    (by positivity) hb
  have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
  have hscaled₀₀ := mul_le_mul_of_nonneg_left h₀₀
    (sq_nonneg (1 - q))
  have hscaled₀₁ := mul_le_mul_of_nonneg_left h₀₁
    (mul_nonneg hcomplement hqzero)
  have hscaled₁₀ := mul_le_mul_of_nonneg_left h₁₀
    (mul_nonneg hqzero hcomplement)
  have hscaled₁₁ := mul_le_mul_of_nonneg_left h₁₁ (sq_nonneg q)
  have hcombined := add_le_add
    (add_le_add (add_le_add hscaled₀₀ hscaled₀₁) hscaled₁₀)
    hscaled₁₁
  have hmarginal :
      v =
        (1 - q) ^ 2 * z₀₀ +
          (1 - q) * q * z₀₁ +
          q * (1 - q) * z₁₀ +
          q ^ 2 * z₁₁ := by
    simpa [q, v, z₀₀, z₀₁, z₁₀, z₁₁] using
      childMarginal_eq_four_outcomes kernel
  have hentropy :
      kernel.conditionalEntropy * Real.log 2 =
        (1 - q) ^ 2 * Real.binEntropy z₀₀ +
          (1 - q) * q * Real.binEntropy z₀₁ +
          q * (1 - q) * Real.binEntropy z₁₀ +
          q ^ 2 * Real.binEntropy z₁₁ := by
    simpa [q, z₀₀, z₀₁, z₁₀, z₁₁] using
      conditionalEntropy_mul_log_two kernel
  have hdisagreement :
      kernel.averageDisagreement =
        (1 - q) ^ 2 * z₀₀ +
          q * (1 - q) + q ^ 2 * (1 - z₁₁) := by
    simpa [q, z₀₀, z₁₁] using
      averageDisagreement_eq_four_outcomes kernel
  have hloga : Real.log a = Real.log (1 - v) / 2 := by
    dsimp [a]
    exact Real.log_sqrt (sub_pos.mpr hvone).le
  have hlogb : Real.log b = Real.log v / 2 := by
    dsimp [b]
    exact Real.log_sqrt hvzero.le
  have hlogthree :
      Real.log (Real.sqrt (3 : ℝ)) = Real.log 3 / 2 :=
    Real.log_sqrt (by positivity)
  have hchildentropy :
      Real.binEntropy v =
        -v * Real.log v - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hleft :
      (((1 - q) ^ 2 *
          (Real.binEntropy z₀₀ +
            (1 - z₀₀) * Real.log a + z₀₀ * Real.log (b / 3)) +
        ((1 - q) * q) *
          (Real.binEntropy z₀₁ +
            (1 - z₀₁) * Real.log (a / Real.sqrt 3) +
              z₀₁ * Real.log (b / Real.sqrt 3))) +
        (q * (1 - q)) *
          (Real.binEntropy z₁₀ +
            (1 - z₁₀) * Real.log (a / Real.sqrt 3) +
              z₁₀ * Real.log (b / Real.sqrt 3))) +
        q ^ 2 *
          (Real.binEntropy z₁₁ +
            (1 - z₁₁) * Real.log (a / 3) + z₁₁ * Real.log b) =
        kernel.conditionalEntropy * Real.log 2 -
          Real.binEntropy v / 2 -
          Real.log 3 * kernel.averageDisagreement := by
    rw [hentropy, hdisagreement, hchildentropy,
      Real.log_div hb.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div ha.ne' hthree.ne',
      Real.log_div hb.ne' hthree.ne',
      Real.log_div ha.ne' (by norm_num : (3 : ℝ) ≠ 0),
      hloga, hlogb, hlogthree]
    linear_combination
      ((Real.log (1 - v) - Real.log v) / 2) * hmarginal
  have hright :
      (((1 - q) ^ 2 * Real.log (a + b / 3) +
        ((1 - q) * q) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        (q * (1 - q)) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        q ^ 2 * Real.log (a / 3 + b) =
        binaryConditionalLogPotential q a b - Real.binEntropy q / 2 := by
    have hmixed :
        a / Real.sqrt 3 + b / Real.sqrt 3 =
          (a + b) / Real.sqrt 3 := by ring
    rw [hmixed]
    unfold binaryConditionalLogPotential
    ring
  rw [hleft, hright] at hcombined
  simpa [q, v, a, b] using hcombined

theorem conditionalEntropy_bound_of_marginal_interior
    (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hzeroAmplitude :
      0 ≤ Real.sqrt (1 - kernel.childMarginal) :=
    Real.sqrt_nonneg _
  have honeAmplitude : 0 ≤ Real.sqrt kernel.childMarginal :=
    Real.sqrt_nonneg _
  have hamplitudes :
      Real.sqrt (1 - kernel.childMarginal) ^ 2 +
          Real.sqrt kernel.childMarginal ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_pos.mpr hmarginal_one).le,
      Real.sq_sqrt hmarginal_zero.le]
    ring
  have hpotential := binaryConditionalLogPotential_le_kappa
    kernel.parentProbability
    (Real.sqrt (1 - kernel.childMarginal))
    (Real.sqrt kernel.childMarginal)
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hzeroAmplitude honeAmplitude hamplitudes
  have hreduction := conditionalEntropy_logsum_reduction kernel
    hmarginal_zero hmarginal_one
  have hright :
      (kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        kappa * Real.log 2 +
          Real.log 3 * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy logTwo
    field_simp [log_two_pos.ne']
  have hscaled :
      kernel.conditionalEntropy * Real.log 2 ≤
        (kappa + logTwo 3 * kernel.averageDisagreement +
          (binaryEntropy kernel.childMarginal -
            binaryEntropy kernel.parentProbability) / 2) * Real.log 2 := by
    rw [hright]
    linarith
  exact (mul_le_mul_iff_of_pos_right log_two_pos).mp hscaled

theorem conditionalEntropy_bound (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by
    dsimp [mixing]
    positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryPairKernel := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto :
      Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have hnonnegative := mul_nonneg
      (sub_nonneg.mpr (hmixing_le_one n))
      (childMarginal_nonneg kernel)
    have hpositive := div_pos (hmixing_pos n) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmarginal_one (n : ℕ) : (approximation n).childMarginal < 1 := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal < 1
    rw [hformula]
    have hproduct := mul_le_mul_of_nonneg_left
      (childMarginal_le_one kernel)
      (sub_nonneg.mpr (hmixing_le_one n))
    have hpositive := hmixing_pos n
    nlinarith
  have hconditional_tendsto :
      Filter.Tendsto (fun n => (approximation n).conditionalEntropy)
        Filter.atTop (nhds kernel.conditionalEntropy) := by
    have hcontinuous :=
      (smoothedConditionalEntropy_continuous kernel).continuousAt.tendsto.comp
        hmixing_tendsto
    have hzero :
        smoothedConditionalEntropy kernel 0 = kernel.conditionalEntropy := by
      simp [smoothedConditionalEntropy, conditionalEntropy]
    rw [hzero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with n
    exact (smoothed_conditionalEntropy kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)).symm
  have hmarginal_tendsto :
      Filter.Tendsto (fun n => (approximation n).childMarginal)
        Filter.atTop (nhds kernel.childMarginal) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.childMarginal))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.childMarginal + mixing n / 2)
          Filter.atTop (nhds kernel.childMarginal) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hdisagreement_tendsto :
      Filter.Tendsto (fun n => (approximation n).averageDisagreement)
        Filter.atTop (nhds kernel.averageDisagreement) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.averageDisagreement))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.averageDisagreement + mixing n / 2)
          Filter.atTop (nhds kernel.averageDisagreement) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_averageDisagreement kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := by
    rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          kappa + logTwo 3 * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          (kappa + logTwo 3 * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hdisagreement_term :=
      (tendsto_const_nhds (x := logTwo 3)).mul hdisagreement_tendsto
    have hentropy_term :=
      (hchildentropy_tendsto.sub
        (tendsto_const_nhds (x :=
          binaryEntropy kernel.parentProbability))).div_const 2
    have hsum :=
      (tendsto_const_nhds (x := kappa)).add
        (hdisagreement_term.add hentropy_term)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto'
    hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior
    (approximation n) (hmarginal_zero n) (hmarginal_one n)

end BinaryPairKernel

def empiricalBinaryOutcomeCount
    (parentCount oneCount : ℕ) (outcome : Bool) : ℝ :=
  if outcome then (oneCount : ℝ)
  else (parentCount : ℝ) - (oneCount : ℝ)

noncomputable def withoutReplacementBinaryPairMass
    (parentCount oneCount : ℕ) (left right : Bool) : ℝ :=
  empiricalBinaryOutcomeCount parentCount oneCount left *
      (empiricalBinaryOutcomeCount parentCount oneCount right -
        if left = right then 1 else 0) /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1))

theorem withoutReplacementBinaryPairMass_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (left right : Bool) :
    0 ≤ withoutReplacementBinaryPairMass parentCount oneCount left right := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hdenominator :
      0 ≤ (parentCount : ℝ) * ((parentCount : ℝ) - 1) :=
    (mul_pos hparent_real hparent_minus).le
  have hone_nonneg : (0 : ℝ) ≤ (oneCount : ℝ) := by positivity
  have hcount : (oneCount : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hones
  have hzero_nonneg : 0 ≤ (parentCount : ℝ) - (oneCount : ℝ) := by
    linarith
  have hone_diagonal :
      0 ≤ (oneCount : ℝ) * ((oneCount : ℝ) - 1) := by
    by_cases hzero : oneCount = 0
    · simp [hzero]
    · have hone : 1 ≤ oneCount := Nat.one_le_iff_ne_zero.mpr hzero
      have hone_real : (1 : ℝ) ≤ (oneCount : ℝ) := by
        exact_mod_cast hone
      positivity
  have hzero_diagonal :
      0 ≤ ((parentCount : ℝ) - (oneCount : ℝ)) *
        ((parentCount : ℝ) - (oneCount : ℝ) - 1) := by
    by_cases hfull : oneCount = parentCount
    · simp [hfull]
    · have hstrict : oneCount < parentCount :=
        lt_of_le_of_ne hones hfull
      have hsucc : oneCount + 1 ≤ parentCount := by omega
      have hsucc_real :
          (oneCount : ℝ) + 1 ≤ (parentCount : ℝ) := by
        exact_mod_cast hsucc
      have hfactor :
          0 ≤ (parentCount : ℝ) - (oneCount : ℝ) - 1 := by
        linarith
      exact mul_nonneg hzero_nonneg hfactor
  cases left <;> cases right
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hzero_diagonal hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hzero_nonneg hone_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hone_nonneg hzero_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hone_diagonal hdenominator

theorem withoutReplacementBinaryPairMass_sum
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount) :
    (∑ left : Bool, ∑ right : Bool,
      withoutReplacementBinaryPairMass parentCount oneCount left right) = 1 := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

noncomputable def withoutReplacementBinaryPairExpectation
    (parentCount oneCount : ℕ) (f : Bool → Bool → ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    withoutReplacementBinaryPairMass parentCount oneCount left right *
      f left right

theorem withoutReplacementBinaryPairExpectation_sub
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount)
    (f : Bool → Bool → ℝ) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right) =
      (((oneCount : ℝ) / (parentCount : ℝ)) *
        (1 - (oneCount : ℝ) / (parentCount : ℝ)) /
          ((parentCount : ℝ) - 1)) *
        (f false true + f true false - f false false - f true true) := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [withoutReplacementBinaryPairExpectation, Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount,
    independentBinaryPairMass, binaryCoinMass]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

theorem withoutReplacementBinaryPairExpectation_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right ∧ f left right ≤ 1) :
    |withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right)| ≤ 1 / (parentCount : ℝ) := by
  let q : ℝ := (oneCount : ℝ) / (parentCount : ℝ)
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hqzero : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one hparent_real).mpr
    exact_mod_cast hones
  have hvariance : q * (1 - q) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hscaledvariance :=
    mul_le_mul_of_nonneg_right hvariance hparent_real.le
  have hdelta_nonneg : 0 ≤ q * (1 - q) / ((parentCount : ℝ) - 1) := by
    exact div_nonneg
      (mul_nonneg hqzero (sub_nonneg.mpr hqone))
      hparent_minus.le
  have hdelta_bound :
      2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) ≤
        1 / (parentCount : ℝ) := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    rw [show 2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) =
      (2 * (q * (1 - q))) / ((parentCount : ℝ) - 1) by ring]
    apply (div_le_div_iff₀ hparent_minus hparent_real).mpr
    nlinarith
  have hbracket :
      |f false true + f true false - f false false - f true true| ≤
        (2 : ℝ) := by
    rw [abs_le]
    have h₀₀ := hf false false
    have h₀₁ := hf false true
    have h₁₀ := hf true false
    have h₁₁ := hf true true
    constructor <;> linarith
  rw [withoutReplacementBinaryPairExpectation_sub
    parentCount oneCount hparents f, abs_mul]
  change
    |q * (1 - q) / ((parentCount : ℝ) - 1)| *
        |f false true + f true false - f false false - f true true| ≤
      1 / (parentCount : ℝ)
  rw [abs_of_nonneg hdelta_nonneg]
  calc
    (q * (1 - q) / ((parentCount : ℝ) - 1)) *
        |f false true + f true false - f false false - f true true| ≤
      (q * (1 - q) / ((parentCount : ℝ) - 1)) * 2 :=
        mul_le_mul_of_nonneg_left hbracket hdelta_nonneg
    _ ≤ 1 / (parentCount : ℝ) := by
      nlinarith

theorem withoutReplacementBinaryPairExpectation_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right) :
    0 ≤ withoutReplacementBinaryPairExpectation parentCount oneCount f := by
  unfold withoutReplacementBinaryPairExpectation
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (withoutReplacementBinaryPairMass_nonneg
      parentCount oneCount hparents hones left right)
    (hf left right)

theorem withoutReplacementBinaryPairExpectation_le_one
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, f left right ≤ 1) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f ≤ 1 := by
  unfold withoutReplacementBinaryPairExpectation
  calc
    (∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right *
          f left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left (hf left right)
            (withoutReplacementBinaryPairMass_nonneg
              parentCount oneCount hparents hones left right)
    _ = 1 := by
      simpa using
        withoutReplacementBinaryPairMass_sum parentCount oneCount hparents

noncomputable def empiricalChildMarginal
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    kernel.childProbability

noncomputable def empiricalConditionalEntropy
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right => binaryEntropy (kernel.childProbability left right))

noncomputable def empiricalAverageDisagreement
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right =>
      (BinaryPairKernel.bitDisagreementProbability left
          (kernel.childProbability left right) +
        BinaryPairKernel.bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

theorem empiricalChildMarginal_mem_Icc
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel) :
    0 ≤ empiricalChildMarginal parentCount oneCount kernel ∧
      empiricalChildMarginal parentCount oneCount kernel ≤ 1 := by
  constructor
  · exact withoutReplacementBinaryPairExpectation_nonneg
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_nonneg
  · exact withoutReplacementBinaryPairExpectation_le_one
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_le_one

theorem empiricalChildMarginal_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    kernel.childProbability
    (fun left right =>
      ⟨kernel.childProbability_nonneg left right,
        kernel.childProbability_le_one left right⟩)
  rw [← hparameter] at herror
  simpa [empiricalChildMarginal, BinaryPairKernel.childMarginal] using herror

theorem empiricalConditionalEntropy_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalConditionalEntropy parentCount oneCount kernel -
      kernel.conditionalEntropy| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    (fun left right => binaryEntropy (kernel.childProbability left right))
    (fun left right =>
      ⟨binaryEntropy_nonneg
        (kernel.childProbability_nonneg left right)
        (kernel.childProbability_le_one left right),
        binaryEntropy_le_one (kernel.childProbability left right)⟩)
  rw [← hparameter] at herror
  simpa [empiricalConditionalEntropy,
    BinaryPairKernel.conditionalEntropy] using herror

theorem empiricalAverageDisagreement_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalAverageDisagreement parentCount oneCount kernel -
      kernel.averageDisagreement| ≤ 1 / (parentCount : ℝ) := by
  let observable : Bool → Bool → ℝ := fun left right =>
    (BinaryPairKernel.bitDisagreementProbability left
        (kernel.childProbability left right) +
      BinaryPairKernel.bitDisagreementProbability right
        (kernel.childProbability left right)) / 2
  have hobservable (left right : Bool) :
      0 ≤ observable left right ∧ observable left right ≤ 1 := by
    have hleft := BinaryPairKernel.bitDisagreementProbability_mem_Icc left
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    have hright := BinaryPairKernel.bitDisagreementProbability_mem_Icc right
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    dsimp [observable]
    constructor <;> linarith
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones observable hobservable
  rw [← hparameter] at herror
  simpa [empiricalAverageDisagreement,
    BinaryPairKernel.averageDisagreement, observable] using herror

noncomputable def binomialProbabilityMass
    (trialCount successCount : ℕ) (probability : ℝ) : ℝ :=
  (trialCount.choose successCount : ℝ) *
    probability ^ successCount *
    (1 - probability) ^ (trialCount - successCount)

theorem binomialProbabilityMass_nonneg
    (trialCount successCount : ℕ) (probability : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity

theorem binomialProbabilityMass_succ_mul
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1) probability *
        ((successCount + 1 : ℕ) : ℝ) * (1 - probability) =
      binomialProbabilityMass trialCount successCount probability *
        ((trialCount - successCount : ℕ) : ℝ) * probability := by
  have hc :
      ((trialCount.choose (successCount + 1) : ℕ) : ℝ) *
          ((successCount + 1 : ℕ) : ℝ) =
        ((trialCount.choose successCount : ℕ) : ℝ) *
          ((trialCount - successCount : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq trialCount successCount
  have hs : trialCount - successCount =
      (trialCount - (successCount + 1)) + 1 := by omega
  unfold binomialProbabilityMass
  rw [hs] at hc ⊢
  simp only [pow_succ]
  linear_combination
    (probability ^ successCount *
      (1 - probability) ^ (trialCount - (successCount + 1)) *
      probability * (1 - probability)) * hc

theorem binomialModeRatio_le_of_lt
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hcount : successCount < mode) :
    ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) ≤
      ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub hmode,
    Nat.cast_sub (show successCount ≤ trialCount by omega),
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (mode : ℝ) - (successCount : ℝ) - 1 := by
    have hcast : (successCount : ℝ) + 1 ≤ (mode : ℝ) := by
      exact_mod_cast (show successCount + 1 ≤ mode by omega)
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_nonneg : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  nlinarith

theorem binomialModeRatio_le_of_ge
    (trialCount mode successCount : ℕ)
    (htrials : 0 < trialCount)
    (hmode : mode ≤ trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub (Nat.le_of_lt hsuccess),
    Nat.cast_sub hmode,
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (successCount : ℝ) - (mode : ℝ) := by
    have hcast : (mode : ℝ) ≤ (successCount : ℝ) := by
      exact_mod_cast hcount
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_le : (mode : ℝ) ≤ (trialCount : ℝ) := by
    exact_mod_cast hmode
  nlinarith

theorem binomialProbabilityMass_le_succ_of_lt_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : successCount < mode) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_lt
    trialCount mode successCount hmode.le hcount
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    (show successCount < trialCount by omega)
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hmass
    _ = binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]

theorem binomialProbabilityMass_succ_le_of_ge_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_ge
    trialCount mode successCount htrials hmode.le hcount hsuccess
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ)) hsuccess
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) =
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]
    _ ≤ binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hmass

theorem binomialProbabilityMass_le_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hsuccess : successCount ≤ trialCount) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  by_cases htrials : trialCount = 0
  · subst trialCount
    have hmode_zero : mode = 0 := by omega
    have hsuccess_zero : successCount = 0 := by omega
    subst mode
    subst successCount
    exact le_rfl
  by_cases hmode_zero : mode = 0
  · subst mode
    by_cases hsuccess_zero : successCount = 0
    · subst successCount
      exact le_rfl
    · simp [binomialProbabilityMass, hsuccess_zero]
  by_cases hmode_full : mode = trialCount
  · subst mode
    have htrials_real : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast htrials
    rw [div_self htrials_real]
    by_cases hsuccess_full : successCount = trialCount
    · subst successCount
      exact le_rfl
    · have hpositive : 0 < trialCount - successCount := by omega
      simp [binomialProbabilityMass, hpositive.ne']
  have hmode_lt : mode < trialCount := by omega
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hstep_up (index : ℕ) (hindex : index < mode) :
      binomialProbabilityMass trialCount index probability ≤
        binomialProbabilityMass trialCount (index + 1) probability := by
    exact binomialProbabilityMass_le_succ_of_lt_mode
      trialCount mode index hmode_lt hindex
  have hstep_down (index : ℕ)
      (hindex_mode : mode ≤ index)
      (hindex_trials : index < trialCount) :
      binomialProbabilityMass trialCount (index + 1) probability ≤
        binomialProbabilityMass trialCount index probability := by
    exact binomialProbabilityMass_succ_le_of_ge_mode
      trialCount mode index hmode_lt hindex_mode hindex_trials
  by_cases hbelow : successCount ≤ mode
  · have hwalk (index : ℕ) (hindex : successCount ≤ index) :
        index ≤ mode →
          binomialProbabilityMass trialCount successCount probability ≤
            binomialProbabilityMass trialCount index probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hinduction (by omega)).trans
          (hstep_up index (by omega))
    exact hwalk mode hbelow (le_refl mode)
  · have habove : mode ≤ successCount := by omega
    have hwalk (index : ℕ) (hindex : mode ≤ index) :
        index ≤ trialCount →
          binomialProbabilityMass trialCount index probability ≤
            binomialProbabilityMass trialCount mode probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hstep_down index hindex (by omega)).trans
          (hinduction (by omega))
    exact hwalk successCount habove hsuccess

theorem binomialProbabilityMass_sum_eq_one
    (trialCount : ℕ) (probability : ℝ) :
    (∑ successCount ∈ Finset.range (trialCount + 1),
      binomialProbabilityMass trialCount successCount probability) = 1 := by
  unfold binomialProbabilityMass
  calc
    (∑ successCount ∈ Finset.range (trialCount + 1),
      (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount)) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        probability ^ successCount *
          (1 - probability) ^ (trialCount - successCount) *
          (trialCount.choose successCount : ℝ) := by
            apply Finset.sum_congr rfl
            intro successCount _
            ring
    _ = (probability + (1 - probability)) ^ trialCount :=
      (add_pow probability (1 - probability) trialCount).symm
    _ = 1 := by
      rw [show probability + (1 - probability) = 1 by ring]
      simp

theorem binomialProbabilityMass_mode_ge_inverse
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    1 / ((trialCount + 1 : ℕ) : ℝ) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have hdenominator : 0 < ((trialCount + 1 : ℕ) : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenominator).mpr
  calc
    (1 : ℝ) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount successCount
          ((mode : ℝ) / (trialCount : ℝ)) :=
      (binomialProbabilityMass_sum_eq_one
        trialCount ((mode : ℝ) / (trialCount : ℝ))).symm
    _ ≤ ∑ _successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) := by
      apply Finset.sum_le_sum
      intro successCount hsuccess
      apply binomialProbabilityMass_le_mode
        trialCount mode successCount hmode
      have hbound := Finset.mem_range.mp hsuccess
      omega
    _ = binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) *
        ((trialCount + 1 : ℕ) : ℝ) := by
      simp [nsmul_eq_mul]
      ring

theorem binomialProbabilityMass_mode_mul_exp_entropy
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) *
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((mode : ℝ) / (trialCount : ℝ))) =
      (trialCount.choose mode : ℝ) := by
  by_cases hzero : mode = 0
  · subst mode
    simp [binomialProbabilityMass]
  by_cases hfull : mode = trialCount
  · subst mode
    have htrials : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    simp [binomialProbabilityMass, htrials]
  have hmode_pos : 0 < mode := Nat.pos_of_ne_zero hzero
  have hmode_lt : mode < trialCount :=
    lt_of_le_of_ne hmode hfull
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hprobability : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode_lt
  have hcomplement : 0 < 1 - probability := by
    linarith
  have hproduct :
      0 < probability ^ mode *
        (1 - probability) ^ (trialCount - mode) := by
    positivity
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(mode : ℝ) * Real.log probability -
          ((trialCount - mode : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hmode]
    dsimp [probability]
    field_simp [htrials_real.ne']
    ring
  have hlog :
      Real.log
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode)) +
        (trialCount : ℝ) * Real.binEntropy probability = 0 := by
    rw [Real.log_mul
      (pow_pos hprobability mode).ne'
      (pow_pos hcomplement (trialCount - mode)).ne',
      Real.log_pow, Real.log_pow, hentropy]
    ring
  change
    binomialProbabilityMass trialCount mode probability *
      Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ)
  calc
    binomialProbabilityMass trialCount mode probability *
        Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ) *
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode) *
          Real.exp ((trialCount : ℝ) * Real.binEntropy probability)) := by
        unfold binomialProbabilityMass
        ring
    _ = (trialCount.choose mode : ℝ) *
        Real.exp
          (Real.log
              (probability ^ mode *
                (1 - probability) ^ (trialCount - mode)) +
            (trialCount : ℝ) * Real.binEntropy probability) := by
          rw [Real.exp_add, Real.exp_log hproduct]
    _ = (trialCount.choose mode : ℝ) := by
      rw [hlog]
      simp

theorem exp_binary_entropy_div_le_choose
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) ≤
      (trialCount.choose successCount : ℝ) := by
  have hmode := binomialProbabilityMass_mode_ge_inverse
    trialCount successCount hcount
  have hexponential :
      0 ≤ Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) :=
    (Real.exp_pos _).le
  calc
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) =
      (1 / ((trialCount + 1 : ℕ) : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) := by
        ring
    _ ≤ binomialProbabilityMass trialCount successCount
          ((successCount : ℝ) / (trialCount : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) :=
      mul_le_mul_of_nonneg_right hmode hexponential
    _ = (trialCount.choose successCount : ℝ) :=
      binomialProbabilityMass_mode_mul_exp_entropy
        trialCount successCount hcount

theorem binomial_probability_term_le_one
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount ≤ trialCount)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) ≤ 1 := by
  have hcomplement : 0 ≤ 1 - probability :=
    sub_nonneg.mpr hprobability_one
  have hsum :
      (∑ count ∈ Finset.range (trialCount + 1),
        probability ^ count *
          (1 - probability) ^ (trialCount - count) *
          (trialCount.choose count : ℝ)) = 1 := by
    calc
      (∑ count ∈ Finset.range (trialCount + 1),
          probability ^ count *
            (1 - probability) ^ (trialCount - count) *
            (trialCount.choose count : ℝ)) =
          (probability + (1 - probability)) ^ trialCount :=
        (add_pow probability (1 - probability) trialCount).symm
      _ = 1 := by
        rw [show probability + (1 - probability) = 1 by ring]
        simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (trialCount + 1))
    (f := fun count : ℕ =>
      probability ^ count *
        (1 - probability) ^ (trialCount - count) *
        (trialCount.choose count : ℝ))
    (fun count _ => by positivity)
    (show successCount ∈ Finset.range (trialCount + 1) by
      simp; omega)
  rw [hsum] at hterm
  nlinarith

theorem log_choose_le_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.log (trialCount.choose successCount : ℝ) ≤
      (trialCount : ℝ) *
        Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ)) := by
  by_cases hzero : successCount = 0
  · subst successCount
    simp
  by_cases hfull : successCount = trialCount
  · subst successCount
    by_cases htrials : trialCount = 0
    · simp [htrials]
    · have htrials_real : (trialCount : ℝ) ≠ 0 := by
        exact_mod_cast htrials
      simp [htrials_real]
  have hsuccess : 0 < successCount := Nat.pos_of_ne_zero hzero
  have hstrict : successCount < trialCount :=
    lt_of_le_of_ne hcount hfull
  have htrials : 0 < trialCount :=
    lt_of_lt_of_le hsuccess hcount
  let probability : ℝ :=
    (successCount : ℝ) / (trialCount : ℝ)
  have hprobability_pos : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_lt_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one (by exact_mod_cast htrials)).mpr
    exact_mod_cast hstrict
  have hcomplement : 0 < 1 - probability :=
    sub_pos.mpr hprobability_lt_one
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  have hmass := binomial_probability_term_le_one
    trialCount successCount probability hcount
    hprobability_pos.le hprobability_lt_one.le
  have hproduct :
      0 < (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) := by
    positivity
  have hlogmass := Real.log_le_log hproduct hmass
  simp only [Real.log_one] at hlogmass
  rw [Real.log_mul
      (mul_pos hchoose (pow_pos hprobability_pos _)).ne'
      (pow_pos hcomplement _).ne',
    Real.log_mul hchoose.ne' (pow_pos hprobability_pos _).ne',
    Real.log_pow, Real.log_pow] at hlogmass
  have htrials_real : (trialCount : ℝ) ≠ 0 := by
    exact_mod_cast htrials.ne'
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(successCount : ℝ) * Real.log probability -
          ((trialCount - successCount : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hcount]
    dsimp [probability]
    field_simp [htrials_real]
    ring
  change Real.log (trialCount.choose successCount : ℝ) ≤
    (trialCount : ℝ) * Real.binEntropy probability
  rw [hentropy]
  linarith

theorem choose_le_exp_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    (trialCount.choose successCount : ℝ) ≤
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ))) := by
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  exact (Real.log_le_iff_le_exp hchoose).mp
    (log_choose_le_binary_entropy trialCount successCount hcount)

theorem choose_product_le_exp_binary_entropy
    {ι : Type*} [Fintype ι]
    (population success : ι → ℕ)
    (hcount : ∀ index, success index ≤ population index) :
    (∏ index : ι,
      (population index).choose (success index) : ℝ) ≤
      Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
  calc
    (∏ index : ι,
        (population index).choose (success index) : ℝ) ≤
      ∏ index : ι,
        Real.exp
          ((population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
        apply Finset.prod_le_prod
        · intro index _
          positivity
        · intro index _
          exact choose_le_exp_binary_entropy
            (population index) (success index) (hcount index)
    _ = Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
      rw [Real.exp_sum]

theorem certificate_ratio_one_lt :
    (1 : ℝ) < (97 + 56 * Real.sqrt 3) / 192 := by
  have h := twelve_sevenths_lt_sqrt_three
  nlinarith

theorem certifiedWindowWidth_pos : 0 < certifiedWindowWidth := by
  unfold certifiedWindowWidth logTwo
  exact div_pos
    (div_pos (Real.log_pos certificate_ratio_one_lt)
      log_two_pos)
    (by norm_num)

theorem tau_pos : 0 < tau := by
  unfold tau
  nlinarith [twelve_sevenths_lt_sqrt_three]

theorem tau_lt_one_half : tau < (1 : ℝ) / 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith

theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by
  positivity

theorem tau_complement : 1 - tau = Real.sqrt 3 * tau := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith

theorem tau_reciprocal_identity :
    1 + 1 / Real.sqrt 3 = (1 - tau)⁻¹ := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  rw [tau_complement]
  field_simp [sqrt_three_pos.ne', tau_pos.ne']
  unfold tau
  nlinarith

theorem log_three_eq_twice_log_sqrt_three :
    Real.log (3 : ℝ) = 2 * Real.log (Real.sqrt 3) := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  calc
    Real.log (3 : ℝ) = Real.log ((Real.sqrt 3) ^ 2) := by rw [hsqrt_sq]
    _ = 2 * Real.log (Real.sqrt 3) := by
      rw [Real.log_pow]
      ring

theorem entropy_tau_identity :
    2 * binaryEntropy tau - tau * logTwo 3 =
      2 * logTwo (1 + 1 / Real.sqrt 3) := by
  have hlog_complement :
      Real.log (1 - tau) = Real.log (Real.sqrt 3) + Real.log tau := by
    rw [tau_complement, Real.log_mul sqrt_three_pos.ne' tau_pos.ne']
  unfold binaryEntropy logTwo Real.binEntropy
  rw [Real.log_inv, Real.log_inv, tau_reciprocal_identity, Real.log_inv,
    hlog_complement, log_three_eq_twice_log_sqrt_three]
  ring

theorem certificate_ratio_identity :
    (1 + 1 / Real.sqrt 3) ^ (8 : ℕ) * 27 / 1024 =
      (97 + 56 * Real.sqrt 3) / 192 := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by positivity)
  have hz : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp [hz]
  ring_nf at hs ⊢
  linear_combination
    (-1728 - 13824 * Real.sqrt 3
      - 48960 * Real.sqrt 3 ^ 2
      - 101376 * Real.sqrt 3 ^ 3
      - 137280 * Real.sqrt 3 ^ 4
      - 130560 * Real.sqrt 3 ^ 5
      - 94144 * Real.sqrt 3 ^ 6
      - 57344 * Real.sqrt 3 ^ 7) * hs

theorem log_certificate_ratio_identity :
    Real.log ((97 + 56 * Real.sqrt 3) / 192) =
      8 * Real.log (1 + 1 / Real.sqrt 3) +
        3 * Real.log 3 - 10 * Real.log 2 := by
  have hu : 0 < (1 : ℝ) + 1 / Real.sqrt 3 := by
    positivity
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    calc
      Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    calc
      Real.log (1024 : ℝ) = Real.log ((2 : ℝ) ^ (10 : ℕ)) := by norm_num
      _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [← certificate_ratio_identity,
    Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by norm_num),
    Real.log_pow, hlog27, hlog1024]
  ring

noncomputable def entropyLowerEndpoint : ℝ := kappa + tau * logTwo 3

noncomputable def entropyUpperEndpoint : ℝ := 2 * binaryEntropy tau - 1

noncomputable def midpointBeta : ℝ :=
  (entropyLowerEndpoint + entropyUpperEndpoint) / 2

theorem entropyWindow_eq_certifiedWindowWidth :
    entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth := by
  have hentropy := entropy_tau_identity
  have hlog := log_certificate_ratio_identity
  unfold logTwo at hentropy
  have hlog_argument :
      (Real.sqrt 3 + 1) / Real.sqrt 3 =
        1 + 1 / Real.sqrt 3 := by
    field_simp [sqrt_three_pos.ne']
  unfold entropyUpperEndpoint entropyLowerEndpoint kappa
    certifiedWindowWidth logTwo
  field_simp [log_two_pos.ne'] at hentropy ⊢
  rw [hlog_argument] at hentropy
  ring_nf at hentropy hlog ⊢
  linarith

theorem entropyWindow_pos : entropyLowerEndpoint < entropyUpperEndpoint := by
  have h := certifiedWindowWidth_pos
  rw [← entropyWindow_eq_certifiedWindowWidth] at h
  linarith

theorem midpointBeta_gt_lower
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    entropyLowerEndpoint < midpointBeta := by
  unfold midpointBeta
  linarith

theorem midpointBeta_lt_upper
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    midpointBeta < entropyUpperEndpoint := by
  unfold midpointBeta
  linarith

theorem midpointBeta_gt_lower_unconditional :
    entropyLowerEndpoint < midpointBeta :=
  midpointBeta_gt_lower entropyWindow_pos

theorem midpointBeta_lt_upper_unconditional :
    midpointBeta < entropyUpperEndpoint :=
  midpointBeta_lt_upper entropyWindow_pos

theorem logTwo_three_pos : 0 < logTwo 3 := by
  unfold logTwo
  exact div_pos (Real.log_pos (by norm_num)) log_two_pos

theorem logTwo_three_lt_two : logTwo 3 < 2 := by
  have hlog : Real.log (3 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold logTwo
  apply (div_lt_iff₀ log_two_pos).mpr
  nlinarith [hlog]

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  nlinarith [logTwo_three_lt_two]

theorem entropyLowerEndpoint_pos : 0 < entropyLowerEndpoint := by
  unfold entropyLowerEndpoint
  positivity [kappa_pos, tau_pos, logTwo_three_pos]

theorem binaryEntropy_tau_lt_one : binaryEntropy tau < 1 := by
  have htau_ne : tau ≠ (2 : ℝ)⁻¹ := by
    intro heq
    have hlt := tau_lt_one_half
    rw [heq] at hlt
    norm_num at hlt
  unfold binaryEntropy
  apply (div_lt_iff₀ log_two_pos).mpr
  simpa using (Real.binEntropy_lt_log_two.mpr htau_ne)

theorem entropyUpperEndpoint_lt_one : entropyUpperEndpoint < 1 := by
  unfold entropyUpperEndpoint
  nlinarith [binaryEntropy_tau_lt_one]

theorem midpointBeta_pos : 0 < midpointBeta :=
  entropyLowerEndpoint_pos.trans midpointBeta_gt_lower_unconditional

theorem midpointBeta_lt_one : midpointBeta < 1 :=
  midpointBeta_lt_upper_unconditional.trans entropyUpperEndpoint_lt_one

noncomputable def entropySlack : ℝ := certifiedWindowWidth / 8

noncomputable def exponentGain : ℝ :=
  certifiedWindowWidth / (8 * (1 - midpointBeta))

theorem entropySlack_pos : 0 < entropySlack := by
  unfold entropySlack
  exact div_pos certifiedWindowWidth_pos (by norm_num)

theorem exponentGain_pos : 0 < exponentGain := by
  unfold exponentGain
  exact div_pos certifiedWindowWidth_pos
    (mul_pos (by norm_num) (sub_pos.mpr midpointBeta_lt_one))

noncomputable def empiricalEntropyError (layerSize : ℕ) : ℝ :=
  (1 + logTwo 3) / (layerSize : ℝ) +
    binaryEntropy (1 / (layerSize : ℝ)) / 2

theorem empiricalChildMarginal_entropy_error
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |binaryEntropy (empiricalChildMarginal parentCount oneCount kernel) -
      binaryEntropy kernel.childMarginal| ≤
        binaryEntropy (1 / (parentCount : ℝ)) := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hempirical := empiricalChildMarginal_mem_Icc
    parentCount oneCount hparents_two hones kernel
  have hchild :
      0 ≤ kernel.childMarginal ∧ kernel.childMarginal ≤ 1 :=
    ⟨BinaryPairKernel.childMarginal_nonneg kernel,
      BinaryPairKernel.childMarginal_le_one kernel⟩
  have hcoupling := empiricalChildMarginal_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmodulus := abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (empiricalChildMarginal parentCount oneCount kernel)
    kernel.childMarginal hempirical.1 hempirical.2 hchild.1 hchild.2
  have hparents_real : (4 : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hparents
  have hparents_pos : (0 : ℝ) < (parentCount : ℝ) := by
    linarith
  have hhalf : 1 / (parentCount : ℝ) ≤ (2 : ℝ)⁻¹ := by
    apply (div_le_iff₀ hparents_pos).mpr
    norm_num
    linarith
  have hmonotone := binaryEntropy_mono_on_half
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal|
    (1 / (parentCount : ℝ))
    (abs_nonneg _) hcoupling hhalf
  exact hmodulus.trans hmonotone

theorem empiricalConditionalEntropy_bound
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hconditional := empiricalConditionalEntropy_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hdisagreement := empiricalAverageDisagreement_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmarginal := empiricalChildMarginal_entropy_error
    parentCount oneCount hparents hones kernel hparameter
  have hindependent := BinaryPairKernel.conditionalEntropy_bound kernel
  have hconditional_upper :
      empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hconditional).2
    linarith
  have hdisagreement_upper :
      kernel.averageDisagreement ≤
        empiricalAverageDisagreement parentCount oneCount kernel +
          1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hdisagreement).1
    linarith
  have hdisagreement_scaled := mul_le_mul_of_nonneg_left
    hdisagreement_upper logTwo_three_pos.le
  have hmarginal_upper :
      binaryEntropy kernel.childMarginal ≤
        binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) +
          binaryEntropy (1 / (parentCount : ℝ)) := by
    have h := (abs_le.mp hmarginal).1
    linarith
  have herror :
      1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2 =
        empiricalEntropyError parentCount := by
    unfold empiricalEntropyError
    ring
  calc
    empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) :=
      hconditional_upper
    _ ≤ kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        (1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2) := by
      nlinarith
    _ = kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
      rw [herror]

theorem empiricalEntropyError_tendsto_zero :
    Filter.Tendsto empiricalEntropyError Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun L : ℕ => 1 / (L : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfirst :
      Filter.Tendsto
        (fun L : ℕ => (1 + logTwo 3) / (L : ℝ))
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℕ => 1 + logTwo 3)
          Filter.atTop (nhds (1 + logTwo 3)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hentropy :
      Filter.Tendsto
        (fun L : ℕ => binaryEntropy (1 / (L : ℝ)))
        Filter.atTop (nhds 0) := by
    have hcontinuous := binaryEntropy_continuous.continuousAt.tendsto.comp hinv
    rw [binaryEntropy_zero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with L
    rfl
  change Filter.Tendsto
    (fun L : ℕ => (1 + logTwo 3) / (L : ℝ) +
      binaryEntropy (1 / (L : ℝ)) / 2)
    Filter.atTop (nhds 0)
  simpa using hfirst.add (hentropy.div_const 2)

theorem logTwo_pairLayer_card_add_one_le (L : ℕ) (hL : 2 ≤ L) :
    logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
      2 * (L : ℝ) / Real.log 2 := by
  let x : ℝ := ((L.choose 2 + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 := by
    exact Nat.cast_choose_two ℝ L
  have hxle : x ≤ (L : ℝ) ^ 2 := by
    dsimp [x]
    push_cast
    rw [hchoose]
    nlinarith [sq_nonneg ((L : ℝ) - 1)]
  have hsqrt : Real.sqrt x ≤ (L : ℝ) := by
    have hsq := Real.sq_sqrt hxpos.le
    have hsqrt_nonneg := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have hbound := Real.log_le_rpow_div hxpos.le
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hbound
    norm_num at hbound
    linarith
  change Real.log x / Real.log 2 ≤ 2 * (L : ℝ) / Real.log 2
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  linarith

theorem exists_empiricalEntropyError_base :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → empiricalEntropyError L < entropySlack := by
  have heventually :
      ∀ᶠ L : ℕ in Filter.atTop,
        empiricalEntropyError L < entropySlack :=
    (tendsto_order.1 empiricalEntropyError_tendsto_zero).2
      entropySlack entropySlack_pos
  obtain ⟨L₀, hL₀⟩ := (Filter.eventually_atTop.1 heventually)
  refine ⟨max 4 L₀, le_max_left _ _, ?_⟩
  intro L hL
  exact hL₀ L ((le_max_right 4 L₀).trans hL)

theorem exists_entropy_exclusion_base :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        empiricalEntropyError L < entropySlack ∧
        (L : ℝ) +
            3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (L.choose 2 : ℝ) < -1 := by
  obtain ⟨Lerror, _, herror⟩ := exists_empiricalEntropyError_base
  let C : ℝ := 1 + 6 / Real.log 2
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (4 * (C + entropySlack + 1) / entropySlack)
  refine ⟨max 4 (max Lerror N), le_max_left _ _, ?_⟩
  intro L hL
  have hrest : max Lerror N ≤ L :=
    (le_max_right 4 (max Lerror N)).trans hL
  have herrorL : Lerror ≤ L := (le_max_left Lerror N).trans hrest
  have hNL : N ≤ L := (le_max_right Lerror N).trans hrest
  refine ⟨herror L herrorL, ?_⟩
  have hLfour : 4 ≤ L :=
    (le_max_left 4 (max Lerror N)).trans hL
  have hLreal : (4 : ℝ) ≤ L := by exact_mod_cast hLfour
  have hLpos : 0 < (L : ℝ) := by linarith
  have hNreal : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hthreshold :
      4 * (C + entropySlack + 1) / entropySlack < (L : ℝ) :=
    hN.trans_le hNreal
  have hbig :
      4 * (C + entropySlack + 1) < entropySlack * (L : ℝ) := by
    have h := (div_lt_iff₀ entropySlack_pos).mp hthreshold
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hbig hLpos
  have hlog := logTwo_pairLayer_card_add_one_le L (by omega)
  have hlinear :
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
        C * (L : ℝ) := by
    calc
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
          (L : ℝ) + 3 * (2 * (L : ℝ) / Real.log 2) := by
            gcongr
      _ = C * (L : ℝ) := by
        dsimp [C]
        ring
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ L
  rw [hchoose]
  nlinarith [mul_pos entropySlack_pos hLpos]

theorem exists_entropy_exclusion_depth :
    ∃ depth : ℕ, 0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) := by
  obtain ⟨depth, hdepth⟩ :=
    exists_nat_gt ((2 : ℝ) / certifiedWindowWidth)
  have hwidth := certifiedWindowWidth_pos
  have hdepth_real : 0 < (depth : ℝ) :=
    (div_pos (by norm_num) hwidth).trans hdepth
  have hdepth_nat : 0 < depth := by exact_mod_cast hdepth_real
  refine ⟨depth, hdepth_nat, ?_⟩
  have hproduct := (div_lt_iff₀ hwidth).mp hdepth
  nlinarith

theorem entropy_potential_increment
    (potentialBefore potentialAfter conditionalEntropy error : ℝ)
    (herror : error < entropySlack)
    (hlower : midpointBeta - entropySlack < conditionalEntropy)
    (hupper : conditionalEntropy ≤
      entropyLowerEndpoint +
        (potentialAfter - potentialBefore) / 2 + error) :
    certifiedWindowWidth / 2 < potentialAfter - potentialBefore := by
  have hwindow := entropyWindow_eq_certifiedWindowWidth
  unfold midpointBeta entropySlack at hlower
  unfold entropySlack at herror
  linarith

theorem entropy_potential_layers_impossible
    (depth : ℕ) (potential : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hincrement : ∀ i < depth,
      certifiedWindowWidth / 2 < potential (i + 1) - potential i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  have htotal :
      ∀ i ≤ depth,
        (i : ℝ) * (certifiedWindowWidth / 2) ≤
          potential i - potential 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiprev : i ≤ depth := by omega
        have histep : i < depth := by omega
        have hprevious := ih hiprev
        have hnext := (hincrement i histep).le
        push_cast
        linarith
  have hstart := (hrange 0 (by omega)).1
  have hfinish := (hrange depth le_rfl).2
  have hsum := htotal depth le_rfl
  linarith

theorem entropy_layer_exclusion
    (depth : ℕ) (potential conditionalEntropy error : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (herror : ∀ i < depth, error i < entropySlack)
    (hlower : ∀ i < depth,
      midpointBeta - entropySlack < conditionalEntropy i)
    (hupper : ∀ i < depth,
      conditionalEntropy i ≤
        entropyLowerEndpoint +
          (potential (i + 1) - potential i) / 2 + error i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  apply entropy_potential_layers_impossible depth potential hrange
    (hdepth := hdepth)
  intro i hi
  exact entropy_potential_increment (potential i) (potential (i + 1))
    (conditionalEntropy i) (error i)
    (herror i hi) (hlower i hi) (hupper i hi)

end BinaryEntropy

section ForbiddenGraph

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

abbrev IsTwoDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 2 G

def DegeneracyConjectureStatement : Prop :=
  ∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
    0 < r → H.IsBipartite → IsDegenerate r H →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ) ^ (((2 : ℕ) : ℝ) - 1 / (r : ℝ)))

theorem isTwoDegenerate_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsTwoDegenerate G) :
    IsTwoDegenerate H := by
  classical
  intro s hs
  let t : Finset V := s.map e.symm.toEquiv.toEmbedding
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨e.symm w, ?_⟩
    exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hcard⟩ := hG t ht
  refine ⟨e v, ?_, ?_⟩
  · change v ∈ s.map e.symm.toEquiv.toEmbedding at hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwv : w = e v := by
      apply e.symm.toEquiv.injective
      simpa using heq
    simpa [← hwv] using hw
  · have hneighbors :
        neighborsWithin H s (e v) =
          (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [neighborsWithin, Finset.mem_filter, Finset.mem_map_equiv]
      have hmembership : e.symm w ∈ t ↔ w ∈ s := by
        change e.symm w ∈ s.map e.symm.toEquiv.toEmbedding ↔ w ∈ s
        constructor
        · intro hmember
          obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hmember
          have huw : u = w := e.symm.toEquiv.injective heq
          simpa [huw] using hu
        · intro hmember
          exact Finset.mem_map.mpr ⟨w, hmember, rfl⟩
      have hadjacency :
          G.Adj v (e.symm w) ↔ H.Adj (e v) w := by
        simpa using (e.map_rel_iff (a := v) (b := e.symm w)).symm
      exact (and_congr hmembership hadjacency).symm
    rw [hneighbors, Finset.card_map]
    exact hcard

theorem isBipartite_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨coloring⟩ := hG
  exact ⟨coloring.comp e.symm.toHom⟩

structure ParentSystem (V : Type*) where
  level : V → ℕ
  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ 2

namespace ParentSystem

def graph {V : Type*} (P : ParentSystem V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)

theorem graph_adj_iff {V : Type*} (P : ParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔
      v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := by
  rfl

theorem graph_isBipartite {V : Type*} (P : ParentSystem V) :
    P.graph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨P.level v % 2, by omega⟩ : Fin 2)) ?_⟩
  intro v u hadj
  apply Fin.ne_of_val_ne
  change P.level v % 2 ≠ P.level u % 2
  rcases (P.graph_adj_iff v u).mp hadj with ⟨_, huv | huv⟩
  · have hlevel := P.parent_level huv
    omega
  · have hlevel := P.parent_level huv
    omega

theorem graph_isTwoDegenerate {V : Type*} (P : ParentSystem V) :
    IsTwoDegenerate P.graph := by
  classical
  intro s hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s P.level hs
  refine ⟨v, hv, ?_⟩
  have hsubset : neighborsWithin P.graph s v ⊆ P.parents v := by
    intro u hu
    have hus : u ∈ s ∧ P.graph.Adj v u := by
      simpa [neighborsWithin] using hu
    rcases (P.graph_adj_iff v u).mp hus.2 with ⟨_, hparent | hchild⟩
    · exact hparent
    · have hlevel := P.parent_level hchild
      have hle := hmax u hus.1
      omega
  exact (Finset.card_le_card hsubset).trans (P.parent_card v)

end ParentSystem

def PairLayer (baseSize : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (PairLayer baseSize i) // parents.card = 2}

noncomputable instance pairLayerFintype (baseSize i : ℕ) :
    Fintype (PairLayer baseSize i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (PairLayer baseSize i) // parents.card = 2}
      infer_instance

theorem pairLayer_card_zero (baseSize : ℕ) :
    Fintype.card (PairLayer baseSize 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp

theorem pairLayer_card_succ (baseSize i : ℕ) :
    Fintype.card (PairLayer baseSize (i + 1)) =
      (Fintype.card (PairLayer baseSize i)).choose 2 := by
  classical
  let layerPairs : Finset (Finset (PairLayer baseSize i)) :=
    (Finset.univ : Finset (PairLayer baseSize i)).powersetCard 2
  let equivalence : PairLayer baseSize (i + 1) ≃ layerPairs :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (PairLayer baseSize (i + 1)) = Fintype.card layerPairs :=
      Fintype.card_congr equivalence
    _ = layerPairs.card := Fintype.card_coe layerPairs
    _ = (Fintype.card (PairLayer baseSize i)).choose 2 := by
      simp [layerPairs]

theorem le_choose_two_of_four {size : ℕ} (hsize : 4 ≤ size) :
    size ≤ size.choose 2 := by
  have hreal : (4 : ℝ) ≤ (size : ℝ) := by
    exact_mod_cast hsize
  have hchoose :
      (size.choose 2 : ℝ) =
        (size : ℝ) * ((size : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ size
  have hbound : (size : ℝ) ≤ (size.choose 2 : ℝ) := by
    rw [hchoose]
    nlinarith [sq_nonneg ((size : ℝ) - 2)]
  exact_mod_cast hbound

theorem pairLayer_card_ge_base
    (baseSize i : ℕ) (hbase : 4 ≤ baseSize) :
    baseSize ≤ Fintype.card (PairLayer baseSize i) := by
  induction i with
  | zero =>
      rw [pairLayer_card_zero]
  | succ i ih =>
      rw [pairLayer_card_succ]
      exact ih.trans
        (le_choose_two_of_four (hbase.trans ih))

noncomputable def pairLayerFinEquiv (baseSize layer : ℕ) :
    PairLayer baseSize layer ≃
      Fin (Fintype.card (PairLayer baseSize layer)) :=
  Fintype.equivFin (PairLayer baseSize layer)

noncomputable def pairLayerPairEquiv (baseSize layer : ℕ) :
    PairLayer (Fintype.card (PairLayer baseSize layer)) 1 ≃
      PairLayer baseSize (layer + 1) := by
  classical
  change
    {parents : Finset
      (Fin (Fintype.card (PairLayer baseSize layer))) //
        parents.card = 2} ≃
      {parents : Finset (PairLayer baseSize layer) //
        parents.card = 2}
  exact
    (pairLayerFinEquiv baseSize layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by
        simp [Equiv.finsetCongr_apply])

theorem pairLayerPair_nonempty
    {parentCount : ℕ}
    (hparents : 2 ≤ parentCount) :
    Nonempty (PairLayer parentCount 1) := by
  apply Fintype.card_pos_iff.mp
  rw [pairLayer_card_succ parentCount 0,
    pairLayer_card_zero]
  exact Nat.choose_pos hparents

abbrev PairVertex (baseSize depth : ℕ) :=
  Σ i : Fin (depth + 1), PairLayer baseSize i.val

def pairLayerEmbedding (baseSize depth i : ℕ) (hi : i < depth + 1) :
    PairLayer baseSize i ↪ PairVertex baseSize depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by
    intro v w heq
    cases heq
    rfl

noncomputable def pairParents (baseSize depth : ℕ) :
    PairVertex baseSize depth → Finset (PairVertex baseSize depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (pairLayerEmbedding baseSize depth i (by omega))

noncomputable def pairParentSystem (baseSize depth : ℕ) :
    ParentSystem (PairVertex baseSize depth) where
  level v := v.1.val
  parents := pairParents baseSize depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero =>
        simp [pairParents] at hparent
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp only [pairParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero =>
        simp [pairParents]
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp [pairParents, v.property]

theorem pairGraph_parent_child_adj
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : PairLayer baseSize (layer + 1))
    (parent : PairLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (pairParentSystem baseSize depth).graph.Adj
      (pairLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (pairLayerEmbedding baseSize depth layer (by omega) parent) := by
  apply (ParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val)
      hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        pairParents baseSize depth
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer child)
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        child.val.map
          (pairLayerEmbedding baseSize depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩

theorem pairGraph_isBipartite (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph.IsBipartite :=
  ParentSystem.graph_isBipartite (pairParentSystem baseSize depth)

theorem pairGraph_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairParentSystem baseSize depth).graph :=
  ParentSystem.graph_isTwoDegenerate (pairParentSystem baseSize depth)

def pairBaseVertex (baseSize depth : ℕ) (a : Fin baseSize) :
    PairVertex baseSize depth :=
  pairLayerEmbedding baseSize depth 0 (by omega) a

theorem pairLayer_reaches_base (baseSize depth : ℕ) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : PairLayer baseSize i),
      ∃ a : Fin baseSize,
        (pairParentSystem baseSize depth).graph.Reachable
          (pairLayerEmbedding baseSize depth i hi v)
          (pairBaseVertex baseSize depth a) := by
  intro i
  induction i with
  | zero =>
      intro hi v
      exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := pairLayerEmbedding baseSize depth i (by omega) parent
      let upper := pairLayerEmbedding baseSize depth (i + 1) hi v
      have hedge :
          (pairParentSystem baseSize depth).graph.Adj upper lower := by
        apply (ParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : PairVertex baseSize depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ pairParents baseSize depth upper
          change lower ∈
            v.val.map (pairLayerEmbedding baseSize depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      refine ⟨a, hedge.reachable.trans ?_⟩
      exact ha

theorem pairBaseVertices_reachable (baseSize depth : ℕ)
    (hdepth : 0 < depth) (a b : Fin baseSize) :
    (pairParentSystem baseSize depth).graph.Reachable
      (pairBaseVertex baseSize depth a)
      (pairBaseVertex baseSize depth b) := by
  classical
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · let pair : PairLayer baseSize 1 :=
      ⟨{a, b}, Finset.card_pair hab⟩
    let bridge := pairLayerEmbedding baseSize depth 1 (by omega) pair
    have hadj (x : Fin baseSize) (hx : x = a ∨ x = b) :
        (pairParentSystem baseSize depth).graph.Adj
          bridge (pairBaseVertex baseSize depth x) := by
      apply (ParentSystem.graph_adj_iff _ bridge _).mpr
      constructor
      · intro heq
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) heq
        change 1 = 0 at hlevels
        omega
      · left
        change pairBaseVertex baseSize depth x ∈
          pairParents baseSize depth bridge
        have hxmem : x ∈ ({a, b} : Finset (PairLayer baseSize 0)) := by
          rcases hx with hxa | hxb
          · rw [hxa]
            exact @Finset.mem_insert_self (PairLayer baseSize 0)
              pairDecidableEq a ({b} : Finset (PairLayer baseSize 0))
          · rw [hxb]
            exact @Finset.mem_insert_of_mem (PairLayer baseSize 0)
              pairDecidableEq ({b} : Finset (PairLayer baseSize 0)) b a
              (Finset.mem_singleton_self b)
        change
          pairLayerEmbedding baseSize depth 0 (by omega) x ∈
            ({a, b} : Finset (PairLayer baseSize 0)).map
              (pairLayerEmbedding baseSize depth 0 (by omega))
        exact Finset.mem_map.mpr ⟨x, hxmem, rfl⟩
    exact (hadj a (Or.inl rfl)).symm.reachable.trans
      (hadj b (Or.inr rfl)).reachable

theorem pairGraph_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairParentSystem baseSize depth).graph.Connected := by
  let root : Fin baseSize := ⟨0, hbase⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨pairBaseVertex baseSize depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := pairLayer_reaches_base baseSize depth i hi v
  exact (pairBaseVertices_reachable baseSize depth hdepth root a).trans ha.symm

noncomputable def pairGraphOverFin (baseSize depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
  (pairParentSystem baseSize depth).graph.overFin rfl

noncomputable def pairGraphOverFinIso (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph ≃g
      pairGraphOverFin baseSize depth :=
  (pairParentSystem baseSize depth).graph.overFinIso rfl

theorem pairGraphOverFin_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairGraphOverFin baseSize depth).Connected :=
  (pairGraphOverFinIso baseSize depth).connected_iff.mp
    (pairGraph_connected baseSize depth hbase hdepth)

theorem pairGraphOverFin_isBipartite (baseSize depth : ℕ) :
    (pairGraphOverFin baseSize depth).IsBipartite :=
  isBipartite_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isBipartite baseSize depth)

theorem pairGraphOverFin_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairGraphOverFin baseSize depth) :=
  isTwoDegenerate_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isTwoDegenerate baseSize depth)

open Classical in
theorem degree_gt_two_of_three_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v x y z : V)
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 < G.degree v := by
  classical
  change 2 < (G.neighborFinset v).card
  apply Finset.two_lt_card_iff.mpr
  exact ⟨x, y, z,
    (G.mem_neighborFinset v x).mpr hx,
    (G.mem_neighborFinset v y).mpr hy,
    (G.mem_neighborFinset v z).mpr hz,
    hxy, hxz, hyz⟩

open Classical in
theorem pairGraph_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : PairVertex baseSize depth,
      (pairParentSystem baseSize depth).graph.Adj u v ∧
      2 < (pairParentSystem baseSize depth).graph.degree u ∧
      2 < (pairParentSystem baseSize depth).graph.degree v := by
  classical
  let a : PairLayer baseSize 0 := ⟨0, by omega⟩
  let b : PairLayer baseSize 0 := ⟨1, by omega⟩
  let c : PairLayer baseSize 0 := ⟨2, by omega⟩
  let d : PairLayer baseSize 0 := ⟨3, by omega⟩
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 1 at hval
    omega
  have hac : a ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 2 at hval
    omega
  have had : a ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 3 at hval
    omega
  have hbc : b ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 2 at hval
    omega
  have hbd : b ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 3 at hval
    omega
  have hcd : c ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 2 = 3 at hval
    omega
  let ab : PairLayer baseSize 1 :=
    ⟨{a, b}, Finset.card_pair hab⟩
  let ac : PairLayer baseSize 1 :=
    ⟨{a, c}, Finset.card_pair hac⟩
  let ad : PairLayer baseSize 1 :=
    ⟨{a, d}, Finset.card_pair had⟩
  have habac : ab ≠ ac := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, c} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbc'
    · exact hab hba.symm
    · exact hbc (Finset.mem_singleton.mp hbc')
  have habad : ab ≠ ad := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbd'
    · exact hab hba.symm
    · exact hbd (Finset.mem_singleton.mp hbd')
  have hacad : ac ≠ ad := by
    intro heq
    have hmem : c ∈ ac.val := by
      change c ∈ ({a, c} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
    rw [heq] at hmem
    change c ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hca | hcd'
    · exact hac hca.symm
    · exact hcd (Finset.mem_singleton.mp hcd')
  let abc : PairLayer baseSize 2 :=
    ⟨{ab, ac}, Finset.card_pair habac⟩
  let va : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) a
  let vb : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) b
  let vab : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ab
  let vac : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ac
  let vad : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ad
  let vabc : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 2 (by omega) abc
  let G : SimpleGraph (PairVertex baseSize depth) :=
    (pairParentSystem baseSize depth).graph
  have ha_mem_ab : a ∈ ab.val := by
    change a ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {b}
  have hb_mem_ab : b ∈ ab.val := by
    change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha_mem_ac : a ∈ ac.val := by
    change a ∈ ({a, c} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {c}
  have ha_mem_ad : a ∈ ad.val := by
    change a ∈ ({a, d} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {d}
  have hab_a : G.Adj vab va := by
    simpa only [G, vab, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab a ha_mem_ab
  have hab_b : G.Adj vab vb := by
    simpa only [G, vab, vb] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab b hb_mem_ab
  have hac_a : G.Adj vac va := by
    simpa only [G, vac, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ac a ha_mem_ac
  have had_a : G.Adj vad va := by
    simpa only [G, vad, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ad a ha_mem_ad
  have habc_ab : G.Adj vabc vab := by
    simpa only [G, vabc, vab] using
      pairGraph_parent_child_adj baseSize depth 1
        (by omega) abc ab (by
          change ab ∈ ({ab, ac} : Finset (PairLayer baseSize 1))
          exact Finset.mem_insert_self ab {ac})
  have hab_vac : vab ≠ vac := by
    intro heq
    apply habac
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hab_vad : vab ≠ vad := by
    intro heq
    apply habad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hac_vad : vac ≠ vad := by
    intro heq
    apply hacad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have ha_b : va ≠ vb := by
    intro heq
    have hfin := (pairLayerEmbedding baseSize depth 0 (by omega)).inj' heq
    have hval := congrArg Fin.val hfin
    simp [a, b] at hval
  have ha_abc : va ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have hb_abc : vb ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have ha_degree : 2 < G.degree va :=
    degree_gt_two_of_three_neighbors G va vab vac vad
      hab_a.symm hac_a.symm had_a.symm
      hab_vac hab_vad hac_vad
  have hab_degree : 2 < G.degree vab :=
    degree_gt_two_of_three_neighbors G vab va vb vabc
      hab_a hab_b habc_ab.symm ha_b ha_abc hb_abc
  exact ⟨va, vab, hab_a.symm, ha_degree, hab_degree⟩

open Classical in
theorem pairGraphOverFin_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : Fin (Fintype.card (PairVertex baseSize depth)),
      (pairGraphOverFin baseSize depth).Adj u v ∧
      2 < (pairGraphOverFin baseSize depth).degree u ∧
      2 < (pairGraphOverFin baseSize depth).degree v := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraph_exists_adj_degree_gt_two baseSize depth hbase hdepth
  let e := pairGraphOverFinIso baseSize depth
  refine ⟨e u, e v, (e.map_rel_iff).mpr hadj, ?_, ?_⟩
  · simpa only [e.degree_eq] using hu
  · simpa only [e.degree_eq] using hv

open Classical in
theorem bipartition_maximum_degree_gt_two_of_adj
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {u v : V}
    (hadj : G.Adj u v)
    (hu : 2 < G.degree u) (hv : 2 < G.degree v) :
    ∀ coloring : G.Coloring (Fin 2), ∀ side : Fin 2,
      2 < (Finset.univ.filter
        (fun vertex : V => coloring vertex = side)).sup
        (fun vertex => G.degree vertex) := by
  classical
  intro coloring side
  have hwitness :
      ∃ vertex : V,
        coloring vertex = side ∧ 2 < G.degree vertex := by
    by_cases hcolor : coloring u = side
    · exact ⟨u, hcolor, hu⟩
    · refine ⟨v, ?_, hv⟩
      have hproper : coloring u ≠ coloring v := coloring.valid hadj
      apply Fin.ext
      have hu_lt := (coloring u).isLt
      have hv_lt := (coloring v).isLt
      have hside_lt := side.isLt
      omega
  obtain ⟨vertex, hcolor, hdegree⟩ := hwitness
  have hmember :
      vertex ∈ Finset.univ.filter
        (fun candidate : V => coloring candidate = side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ vertex, hcolor⟩
  exact lt_of_lt_of_le hdegree
    (Finset.le_sup (f := fun candidate => G.degree candidate) hmember)

open Classical in
theorem pairGraphOverFin_bipartition_maximum_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∀ coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2),
      ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin (Fintype.card (PairVertex baseSize depth)) =>
            coloring vertex = side)).sup
          (fun vertex => (pairGraphOverFin baseSize depth).degree vertex) := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraphOverFin_exists_adj_degree_gt_two baseSize depth hbase hdepth
  exact bipartition_maximum_degree_gt_two_of_adj
    (pairGraphOverFin baseSize depth) hadj hu hv

end ForbiddenGraph

section HammingProfiles

abbrev HammingWord (dimension : ℕ) := Fin dimension → Bool

noncomputable def booleanWordOnes {ι : Type*} [Fintype ι]
    (word : ι → Bool) : Finset ι := by
  classical
  exact Finset.univ.filter (fun index => word index = true)

theorem booleanWordOnes_card_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equivalence : ι ≃ κ)
    (word : κ → Bool) :
    (booleanWordOnes (fun index : ι => word (equivalence index))).card =
      (booleanWordOnes word).card := by
  classical
  apply Finset.card_bij
    (fun index _ => equivalence index)
  · intro index hindex
    have hone := (Finset.mem_filter.mp hindex).2
    unfold booleanWordOnes
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hone⟩
  · intro first _ second _ hequal
    exact equivalence.injective hequal
  · intro index hindex
    refine ⟨equivalence.symm index, ?_, equivalence.apply_symm_apply index⟩
    unfold booleanWordOnes
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hone := (Finset.mem_filter.mp hindex).2
    simpa using hone

noncomputable def booleanWordsOfWeight (ι : Type*) [Fintype ι]
    (weight : ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => (booleanWordOnes word).card = weight)

noncomputable def booleanWordsOfWeightEquiv
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    ↥(booleanWordsOfWeight ι weight) ≃
      ↥((Finset.univ : Finset ι).powersetCard weight) := by
  classical
  refine
    { toFun := fun word => ⟨booleanWordOnes word.val, ?_⟩
      invFun := fun support =>
        ⟨fun index => decide (index ∈ support.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hword :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              (booleanWordOnes candidate).card = weight)) := by
      simpa only [booleanWordsOfWeight] using word.property
    exact (Finset.mem_filter.mp hword).2
  · have hsupport :=
      (Finset.mem_powersetCard.mp support.property).2
    have hones :
        booleanWordOnes
          (fun index : ι => decide (index ∈ support.val)) = support.val := by
      ext index
      simp [booleanWordOnes]
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hones]
    exact hsupport
  · intro word
    apply Subtype.ext
    funext index
    cases hbit : word.val index <;>
      simp [booleanWordOnes, hbit]
  · intro support
    apply Subtype.ext
    ext index
    simp [booleanWordOnes]

theorem booleanWordsOfWeight_card
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    (booleanWordsOfWeight ι weight).card =
      (Fintype.card ι).choose weight := by
  calc
    (booleanWordsOfWeight ι weight).card =
        Fintype.card ↥(booleanWordsOfWeight ι weight) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥((Finset.univ : Finset ι).powersetCard weight) :=
      Fintype.card_congr (booleanWordsOfWeightEquiv ι weight)
    _ = ((Finset.univ : Finset ι).powersetCard weight).card :=
      Fintype.card_coe _
    _ = (Fintype.card ι).choose weight := by
      simp

abbrev ClassificationFiber
    {ι γ : Type*} (classify : ι → γ) (group : γ) :=
  {index : ι // classify index = group}

noncomputable def classificationGroup
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) : Finset ι :=
  Finset.univ.filter (fun index => classify index = group)

noncomputable def classifiedWordOnes
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) : Finset ι :=
  (classificationGroup classify group).filter
    (fun index => word index = true)

noncomputable def classifiedWordSupportEquiv
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    ↥(booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)) ≃
      ↥(classifiedWordOnes classify group word) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.val, ?_⟩
      invFun := fun index => ⟨⟨index.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbit : word index.val.val = true := by
      have hmembership :
          index.val ∈
            (Finset.univ.filter
              (fun candidate : ClassificationFiber classify group =>
                word candidate.val = true)) := by
        simpa only [booleanWordOnes] using index.property
      exact (Finset.mem_filter.mp hmembership).2
    simp [classifiedWordOnes, classificationGroup,
      index.val.property, hbit]
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hgroup := (Finset.mem_filter.mp hmembership).1
    exact (Finset.mem_filter.mp hgroup).2
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hbit := (Finset.mem_filter.mp hmembership).2
    simp [booleanWordOnes, hbit]
  · intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro index
    apply Subtype.ext
    rfl

theorem classifiedWordOnes_card
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    (classifiedWordOnes classify group word).card =
      (booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)).card := by
  calc
    (classifiedWordOnes classify group word).card =
        Fintype.card ↥(classifiedWordOnes classify group word) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥(booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)) :=
      Fintype.card_congr
        (classifiedWordSupportEquiv classify group word).symm
    _ = (booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)).card :=
      Fintype.card_coe _

noncomputable def classifiedBooleanWords
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => ∀ group,
      (classifiedWordOnes classify group word).card = counts group)

noncomputable def classifiedBooleanWordsEquiv
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    ↥(classifiedBooleanWords classify counts) ≃
      (∀ group : γ,
        ↥(booleanWordsOfWeight
          (ClassificationFiber classify group) (counts group))) := by
  classical
  refine
    { toFun := fun word group =>
        ⟨fun index => word.val index.val, ?_⟩
      invFun := fun pieces =>
        ⟨fun index => (pieces (classify index)).val ⟨index, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              ∀ group,
                (classifiedWordOnes classify group candidate).card =
                  counts group)) := by
      simpa only [classifiedBooleanWords] using word.property
    have hprofile := (Finset.mem_filter.mp hmembership).2 group
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (classifiedWordOnes_card classify group word.val).symm.trans
      hprofile
  · simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro group
    rw [classifiedWordOnes_card]
    have hrestriction :
        (fun index : ClassificationFiber classify group =>
          (pieces (classify index.val)).val
            ⟨index.val, rfl⟩) =
          (pieces group).val := by
      funext index
      rcases index with ⟨index, hindex⟩
      cases hindex
      rfl
    rw [hrestriction]
    have hmembership := (pieces group).property
    unfold booleanWordsOfWeight at hmembership
    exact (Finset.mem_filter.mp hmembership).2
  · intro word
    apply Subtype.ext
    funext index
    rfl
  · intro pieces
    funext group
    apply Subtype.ext
    funext index
    rcases index with ⟨index, hindex⟩
    cases hindex
    rfl

theorem classifiedBooleanWords_card
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    (classifiedBooleanWords classify counts).card =
      ∏ group : γ,
        (Fintype.card (ClassificationFiber classify group)).choose
          (counts group) := by
  calc
    (classifiedBooleanWords classify counts).card =
        Fintype.card ↥(classifiedBooleanWords classify counts) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        (∀ group : γ,
          ↥(booleanWordsOfWeight
            (ClassificationFiber classify group) (counts group))) :=
      Fintype.card_congr (classifiedBooleanWordsEquiv classify counts)
    _ = ∏ group : γ,
          Fintype.card
            ↥(booleanWordsOfWeight
              (ClassificationFiber classify group) (counts group)) := by
      rw [Fintype.card_pi]
    _ = ∏ group : γ,
          (Fintype.card (ClassificationFiber classify group)).choose
            (counts group) := by
      apply Finset.prod_congr rfl
      intro group _
      rw [Fintype.card_coe,
        booleanWordsOfWeight_card]

abbrev PairBitType := Fin 3

abbrev PairTypeCountProfile (parentCount dimension : ℕ) :=
  PairBitType → Fin dimension → Fin (parentCount.choose 2 + 1)

theorem pairTypeCountProfile_card (parentCount dimension : ℕ) :
    Fintype.card (PairTypeCountProfile parentCount dimension) =
      (parentCount.choose 2 + 1) ^ (3 * dimension) := by
  simp [PairTypeCountProfile, pow_mul, Nat.mul_comm]

noncomputable def pairCoordinateBitType
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : PairBitType := by
  classical
  exact
    if ∀ parent ∈ pair.val, parents parent coordinate = false then 0
    else if ∀ parent ∈ pair.val, parents parent coordinate = true then 1
    else 2

noncomputable def pairTypeGroup
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact Finset.univ.filter
    (fun pair => pairCoordinateBitType parents coordinate pair = bitType)

noncomputable def pairCoordinateClassification
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → PairBitType × Fin dimension :=
  fun index =>
    (pairCoordinateBitType parents index.2 index.1, index.2)

noncomputable def pairCoordinateClassificationFiberEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(pairTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun pair => ⟨(pair.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [pairCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [pairTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [pairCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        pair.val ∈
          (Finset.univ.filter
            (fun candidate : PairLayer parentCount 1 =>
              pairCoordinateBitType parents coordinate candidate = bitType)) := by
      simpa only [pairTypeGroup] using pair.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (pairCoordinateBitType parents coordinate pair.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [pairCoordinateClassification] using hcoordinate.symm
  · intro pair
    apply Subtype.ext
    rfl

theorem pairCoordinateClassificationFiber_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate)) =
      (pairTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (pairCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(pairTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (pairCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (pairTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _

theorem sum_pairTypeGroup_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroup parents coordinate bitType).card) =
      parentCount.choose 2 := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hpairs :
      (Finset.univ : Finset (PairLayer parentCount 1)).card =
        parentCount.choose 2 := by
    rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  calc
    (∑ bitType : PairBitType,
        (pairTypeGroup parents coordinate bitType).card) =
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        simpa [pairTypeGroup] using hpartition.symm
    _ = parentCount.choose 2 := hpairs

theorem pairTypeGroup_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroup parents coordinate bitType).card ≤
      parentCount.choose 2 := by
  classical
  calc
    (pairTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        unfold pairTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose 2 := by
      rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
        pairLayer_card_zero]

noncomputable def pairTypeGroupChildOnes
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact (pairTypeGroup parents coordinate bitType).filter
    (fun pair => children pair coordinate = true)

theorem pairTypeGroupChildOnes_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroupChildOnes parents children coordinate bitType).card ≤
      (pairTypeGroup parents coordinate bitType).card := by
  classical
  unfold pairTypeGroupChildOnes
  exact Finset.card_filter_le _ _

def flattenPairChildArray
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2

theorem pairChildClassificationOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (pairCoordinateClassification parents) (bitType, coordinate)
      (flattenPairChildArray children)).card =
        (pairTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (pairCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenPairChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [pairCoordinateClassification] using hcoordinate
    simp only [pairTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [pairTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [pairCoordinateClassification, hcoord] using htype
    · simpa [flattenPairChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group :=
        (Finset.mem_filter.mp hfirst).1
      have hsecond_group :=
        (Finset.mem_filter.mp hsecond).1
      have hfirst_class :=
        (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class :=
        (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [pairCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro pair hpair
    refine ⟨(pair, coordinate), ?_, rfl⟩
    have hpair_parts := Finset.mem_filter.mp hpair
    have hpair_type := (Finset.mem_filter.mp hpair_parts.1).2
    change
      (pair, coordinate) ∈
        (classificationGroup (pairCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenPairChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext hpair_type rfl
    · exact hpair_parts.2

noncomputable def pairChildCountProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairTypeCountProfile parentCount dimension := by
  intro bitType coordinate
  refine ⟨(pairTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := pairTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := pairTypeGroup_card_le parents coordinate bitType
  omega

noncomputable def pairChildArraysOfProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildCountProfile parents children = profile)

noncomputable def pairChildArraysOfProfileEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    ↥(pairChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenPairChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun pair coordinate => word.val (pair, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold pairChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [pairChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : PairTypeCountProfile parentCount dimension =>
        (candidate bitType coordinate).val) hprofile
    simpa [pairChildCountProfile] using hcount
  · simp only [pairChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (pairTypeGroupChildOnes parents
        (fun pair coordinate => word.val (pair, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← pairChildClassificationOnes_card]
    have hflatten :
        flattenPairChildArray
          (fun pair coordinate => word.val (pair, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨pair, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext pair
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨pair, coordinate⟩
    rfl

theorem pairChildArraysOfProfile_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    (pairChildArraysOfProfile parents profile).card =
      ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (pairChildArraysOfProfile parents profile).card =
      Fintype.card ↥(pairChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (pairChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : PairBitType × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (pairCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (pairCoordinateClassification parents)
          (fun index : PairBitType × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [pairCoordinateClassificationFiber_card]

noncomputable def pairCoordinateConditionalEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : PairBitType,
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      binaryEntropy
        (((pairTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ))

noncomputable def pairChildArrayEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    pairCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)

noncomputable def pairParentCoordinateOneCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun parent => parents parent coordinate)).card

theorem pairParentCoordinateOneCount_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairParentCoordinateOneCount parents coordinate ≤ parentCount := by
  classical
  unfold pairParentCoordinateOneCount booleanWordOnes
  calc
    (Finset.univ.filter
      (fun parent : Fin parentCount =>
        parents parent coordinate = true)).card ≤
        (Finset.univ : Finset (Fin parentCount)).card :=
      Finset.card_filter_le _ _
    _ = parentCount := by simp

noncomputable def pairParentCoordinateSupport
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) : Finset (Fin parentCount) := by
  classical
  exact Finset.univ.filter
    (fun parent => parents parent coordinate = outcome)

theorem pairParentCoordinateSupport_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate true).card =
      pairParentCoordinateOneCount parents coordinate := by
  rfl

theorem pairParentCoordinateSupport_card_add
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card +
      (pairParentCoordinateSupport parents coordinate true).card =
        parentCount := by
  classical
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin parentCount)))
      (fun parent => parents parent coordinate = false)
  simpa [pairParentCoordinateSupport, Bool.not_eq_false] using hpartition

theorem pairParentCoordinateSupport_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card =
      parentCount - pairParentCoordinateOneCount parents coordinate := by
  have hpartition := pairParentCoordinateSupport_card_add parents coordinate
  rw [pairParentCoordinateSupport_true_card] at hpartition
  omega

theorem pairCoordinateBitType_homogeneous_iff
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool) :
    pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0) ↔
      ∀ parent ∈ pair.val, parents parent coordinate = outcome := by
  classical
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp pair.property
  cases outcome <;> cases ha : parents a coordinate <;>
    cases hb : parents b coordinate <;>
    simp_all [pairCoordinateBitType]

noncomputable def pairTypeGroupHomogeneousEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    ↥(pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)) ≃
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) := by
  classical
  refine
    { toFun := fun pair => ⟨pair.val.val, ?_⟩
      invFun := fun support =>
        ⟨⟨support.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := pair.property
    unfold pairTypeGroup at hmembership
    have htype := (Finset.mem_filter.mp hmembership).2
    have hhomogeneous :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair.val outcome).mp htype
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, pair.val.property⟩
    intro parent hparent
    unfold pairParentCoordinateSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hhomogeneous parent hparent⟩
  · exact (Finset.mem_powersetCard.mp support.property).2
  · unfold pairTypeGroup
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (pairCoordinateBitType_homogeneous_iff
      parents coordinate
      ⟨support.val, (Finset.mem_powersetCard.mp support.property).2⟩
      outcome).mpr
    intro parent hparent
    have hsubset :=
      (Finset.mem_powersetCard.mp support.property).1
    have hsupport := hsubset hparent
    unfold pairParentCoordinateSupport at hsupport
    exact (Finset.mem_filter.mp hsupport).2
  · intro pair
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro support
    apply Subtype.ext
    rfl

theorem pairTypeGroup_homogeneous_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 := by
  calc
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      Fintype.card
        ↥(pairTypeGroup parents coordinate
          (if outcome then (1 : PairBitType) else 0)) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) :=
      Fintype.card_congr
        (pairTypeGroupHomogeneousEquiv parents coordinate outcome)
    _ = ((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2).card :=
      Fintype.card_coe _
    _ = (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 :=
      Finset.card_powersetCard _ _

theorem pairTypeGroup_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 0).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_false_card] using
    pairTypeGroup_homogeneous_card parents coordinate false

theorem pairTypeGroup_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 1).card =
      (pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_true_card] using
    pairTypeGroup_homogeneous_card parents coordinate true

theorem pairTypeGroup_mixed_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 2).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate) *
        pairParentCoordinateOneCount parents coordinate := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have htotal :
      (pairTypeGroup parents coordinate 0).card +
        (pairTypeGroup parents coordinate 1).card +
          (pairTypeGroup parents coordinate 2).card =
            parentCount.choose 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      sum_pairTypeGroup_card parents coordinate
  rw [pairTypeGroup_false_card,
    pairTypeGroup_true_card] at htotal
  have htotal_real :
      (((parentCount -
          pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        (((pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) =
          (parentCount.choose 2 : ℝ) := by
    exact_mod_cast htotal
  rw [Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_sub hones] at htotal_real
  have hresult :
      ((pairTypeGroup parents coordinate 2).card : ℝ) =
        (((parentCount -
          pairParentCoordinateOneCount parents coordinate) *
            pairParentCoordinateOneCount parents coordinate : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hones]
    nlinarith
  exact_mod_cast hresult

def pairBitTypeOfOutcomes (left right : Bool) : PairBitType :=
  if left = false ∧ right = false then 0
  else if left = true ∧ right = true then 1
  else 2

noncomputable def pairCoordinateKernel
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryPairKernel where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) /
      (parentCount : ℝ)
  parentProbability_nonneg := by
    positivity
  parentProbability_le_one := by
    have hpositive : 0 < (parentCount : ℝ) := by
      exact_mod_cast hparents
    apply (div_le_one hpositive).mpr
    exact_mod_cast pairParentCoordinateOneCount_le parents coordinate
  childProbability left right :=
    ((pairTypeGroupChildOnes parents children coordinate
      (pairBitTypeOfOutcomes left right)).card : ℝ) /
        ((pairTypeGroup parents coordinate
          (pairBitTypeOfOutcomes left right)).card : ℝ)
  childProbability_nonneg := by
    intro left right
    positivity
  childProbability_le_one := by
    intro left right
    let bitType := pairBitTypeOfOutcomes left right
    have hle := pairTypeGroupChildOnes_card_le
      parents children coordinate bitType
    by_cases hzero : (pairTypeGroup parents coordinate bitType).card = 0
    · simp [bitType, hzero]
    · have hpositive :
          0 < ((pairTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      apply (div_le_one hpositive).mpr
      exact_mod_cast hle

theorem pairCoordinateKernel_parentProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairCoordinateKernel hparents parents children coordinate).parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := by
  rfl

theorem pairCoordinateKernel_childProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    (pairCoordinateKernel hparents parents children coordinate).childProbability
        left right =
      ((pairTypeGroupChildOnes parents children coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
          ((pairTypeGroup parents coordinate
            (pairBitTypeOfOutcomes left right)).card : ℝ) := by
  rfl

noncomputable def pairChildCoordinateOneCount
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun pair => children pair coordinate)).card

theorem sum_pairTypeGroupChildOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      pairChildCoordinateOneCount children coordinate := by
  classical
  let support : Finset (PairLayer parentCount 1) :=
    booleanWordOnes (fun pair => children pair coordinate)
  have hmaps :
      ((support : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1)).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : PairBitType) :
      support.filter
        (fun pair => pairCoordinateBitType parents coordinate pair = bitType) =
      pairTypeGroupChildOnes parents children coordinate bitType := by
    ext pair
    simp [support, booleanWordOnes,
      pairTypeGroupChildOnes, pairTypeGroup, and_comm]
  calc
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      ∑ bitType : PairBitType,
        (support.filter
          (fun pair =>
            pairCoordinateBitType parents coordinate pair = bitType)).card := by
          apply Finset.sum_congr rfl
          intro bitType _
          rw [hfiber]
    _ = support.card := by
      exact hpartition.symm
    _ = pairChildCoordinateOneCount children coordinate := by
      rfl

theorem pairTypeGroup_probability_mul_childRatio
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
        ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroupChildOnes parents children
        coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  by_cases hgroup : (pairTypeGroup parents coordinate bitType).card = 0
  · have hchild :
        (pairTypeGroupChildOnes parents children
          coordinate bitType).card = 0 := by
      have hle := pairTypeGroupChildOnes_card_le
        parents children coordinate bitType
      omega
    simp [hgroup, hchild]
  · have hgroup_real :
        ((pairTypeGroup parents coordinate bitType).card : ℝ) ≠ 0 := by
      exact_mod_cast hgroup
    field_simp [hpair.ne', hgroup_real]

theorem withoutReplacementBinaryPairMass_eq_pairTypeGroup
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have hparent : 0 < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  cases left <;> cases right <;>
    simp [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount,
      pairBitTypeOfOutcomes,
      pairTypeGroup_false_card,
      pairTypeGroup_true_card,
      pairTypeGroup_mixed_card,
      Nat.cast_choose_two,
      Nat.cast_sub hones] <;>
    field_simp [hparent.ne', hparent_minus.ne']

theorem pairCoordinateKernel_empiricalConditionalEntropy
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      pairCoordinateConditionalEntropy parents children coordinate := by
  unfold empiricalConditionalEntropy
    withoutReplacementBinaryPairExpectation
  simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
    hparents parents coordinate]
  simp [Fintype.univ_bool,
    pairCoordinateKernel_childProbability,
    pairBitTypeOfOutcomes,
    pairCoordinateConditionalEntropy,
    Fin.sum_univ_succ]
  ring

theorem pairCoordinateKernel_empiricalChildMarginal
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ) := by
  have hgroups :
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
    calc
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        ∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
              (parentCount.choose 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro bitType _
          exact pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType
      _ =
        (∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ)) /
            (parentCount.choose 2 : ℝ) := by
          rw [Finset.sum_div]
      _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          congr 1
          exact_mod_cast
            sum_pairTypeGroupChildOnes_card parents children coordinate
  calc
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
      unfold empiricalChildMarginal
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        Fin.sum_univ_succ]
      ring
    _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose 2 : ℝ) := hgroups

theorem pairTypeGroup_probability_mul_childComplement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
  calc
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        (((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) := by
          ring
    _ = ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          rw [pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType]
    _ = (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
          ring

theorem pairCoordinateKernel_empiricalAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
  have hzero := pairTypeGroup_probability_mul_childRatio
    hparents parents children coordinate 0
  have hone := pairTypeGroup_probability_mul_childComplement
    hparents parents children coordinate 1
  calc
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((pairTypeGroup parents coordinate 0).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (((pairTypeGroupChildOnes parents children
          coordinate 0).card : ℝ) /
            ((pairTypeGroup parents coordinate 0).card : ℝ)) +
      ((pairTypeGroup parents coordinate 2).card : ℝ) /
          (parentCount.choose 2 : ℝ) * (1 / 2 : ℝ) +
      ((pairTypeGroup parents coordinate 1).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (1 -
          ((pairTypeGroupChildOnes parents children
            coordinate 1).card : ℝ) /
              ((pairTypeGroup parents coordinate 1).card : ℝ)) := by
      unfold empiricalAverageDisagreement
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        BinaryPairKernel.bitDisagreementProbability]
      ring
    _ =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
      rw [hzero, hone]
      ring

noncomputable def pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : ℕ := by
  classical
  exact (pair.val.filter
    (fun parent =>
      parents parent coordinate ≠ children pair coordinate)).card

theorem pairCoordinatePairMismatchCount_homogeneous
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool)
    (hgroup :
      pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0)) :
    pairCoordinatePairMismatchCount parents children coordinate pair =
      if children pair coordinate = outcome then 0 else 2 := by
  classical
  have hhomogeneous :=
    (pairCoordinateBitType_homogeneous_iff
      parents coordinate pair outcome).mp hgroup
  by_cases hchild : children pair coordinate = outcome
  · have hempty :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro parent hmember hdisagree
      exact hdisagree
        ((hhomogeneous parent hmember).trans hchild.symm)
    unfold pairCoordinatePairMismatchCount
    rw [hempty]
    simp [hchild]
  · have hfull :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) =
          pair.val := by
      ext parent
      constructor
      · intro hmember
        exact (Finset.mem_filter.mp hmember).1
      · intro hmember
        apply Finset.mem_filter.mpr
        refine ⟨hmember, ?_⟩
        intro hequal
        apply hchild
        exact hequal.symm.trans
          (hhomogeneous parent hmember)
    unfold pairCoordinatePairMismatchCount
    rw [hfull, if_neg hchild]
    exact pair.property

theorem pairCoordinatePairMismatchCount_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (hgroup : pairCoordinateBitType parents coordinate pair = 2) :
    pairCoordinatePairMismatchCount parents children coordinate pair = 1 := by
  classical
  have hnotfalse :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = false := by
    intro hfalse
    have hzero :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair false).mpr hfalse
    rw [hgroup] at hzero
    simp at hzero
  have hnottrue :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = true := by
    intro htrue
    have hone :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair true).mpr htrue
    rw [hgroup] at hone
    simp at hone
  have hexfalse :
      ∃ parent ∈ pair.val, parents parent coordinate = false := by
    by_contra hnone
    push Not at hnone
    apply hnottrue
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  have hextrue :
      ∃ parent ∈ pair.val, parents parent coordinate = true := by
    by_contra hnone
    push Not at hnone
    apply hnotfalse
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  obtain ⟨falseParent, hfalseParent, hfalseBit⟩ := hexfalse
  obtain ⟨trueParent, htrueParent, htrueBit⟩ := hextrue
  let mismatches : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
  let agreements : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        ¬ parents parent coordinate ≠ children pair coordinate)
  have hmismatch : mismatches.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨trueParent, ?_⟩
      simp [mismatches, htrueParent, htrueBit, hchild]
    · refine ⟨falseParent, ?_⟩
      simp [mismatches, hfalseParent, hfalseBit, hchild]
  have hagreement : agreements.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨falseParent, ?_⟩
      simp [agreements, hfalseParent, hfalseBit, hchild]
    · refine ⟨trueParent, ?_⟩
      simp [agreements, htrueParent, htrueBit, hchild]
  have hpartition : mismatches.card + agreements.card = 2 := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pair.val)
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
    change mismatches.card + agreements.card = pair.val.card at hfilter
    simpa [pair.property] using hfilter
  have hmismatch_pos := Finset.card_pos.mpr hmismatch
  have hagreement_pos := Finset.card_pos.mpr hagreement
  change mismatches.card = 1
  omega

theorem pairCoordinatePairMismatchCount_sum_false
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 0,
        if children pair coordinate = true then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 0)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair false hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
      rw [← Finset.sum_filter]
      simp [pairTypeGroupChildOnes, Nat.mul_comm]

theorem pairCoordinatePairMismatchCount_sum_true
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  let zeroChildren : Finset (PairLayer parentCount 1) :=
    (pairTypeGroup parents coordinate 1).filter
      (fun pair => children pair coordinate = false)
  have hpartition :
      (pairTypeGroupChildOnes parents children coordinate 1).card +
        zeroChildren.card =
          (pairTypeGroup parents coordinate 1).card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pairTypeGroup parents coordinate 1)
      (fun pair => children pair coordinate = true)
    simpa [pairTypeGroupChildOnes, zeroChildren] using hfilter
  have hzero_card :
      zeroChildren.card =
        (pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card := by
    omega
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 1,
        if children pair coordinate = false then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 1)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair true hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * zeroChildren.card := by
      rw [← Finset.sum_filter]
      simp [zeroChildren, Nat.mul_comm]
    _ = 2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
      rw [hzero_card]

theorem pairCoordinatePairMismatchCount_sum_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      (pairTypeGroup parents coordinate 2).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ _pair ∈ pairTypeGroup parents coordinate 2, 1 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 2)) := by
          simpa only [pairTypeGroup] using hpair
        exact pairCoordinatePairMismatchCount_mixed
          parents children coordinate pair
            (Finset.mem_filter.mp hmembership).2
    _ = (pairTypeGroup parents coordinate 2).card := by
      simp

theorem sum_pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair : PairLayer parentCount 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card +
      (pairTypeGroup parents coordinate 2).card +
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to hmaps
      (fun pair =>
        pairCoordinatePairMismatchCount
          parents children coordinate pair)).symm
  have hpartition :
      (∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
        (∑ pair ∈ pairTypeGroup parents coordinate 0,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 2,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) := by
    simpa [pairTypeGroup, Fin.sum_univ_succ, add_assoc] using hfiber
  rw [pairCoordinatePairMismatchCount_sum_false,
    pairCoordinatePairMismatchCount_sum_true,
    pairCoordinatePairMismatchCount_sum_mixed] at hpartition
  omega

theorem sum_pairCoordinatePairMismatchCount_eq_hammingDist
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
      ∑ pair : PairLayer parentCount 1,
        ∑ parent ∈ pair.val,
          hammingDist (parents parent) (children pair) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pair _
  have hcount (coordinate : Fin dimension) :
      pairCoordinatePairMismatchCount parents children coordinate pair =
        ∑ parent ∈ pair.val,
          if parents parent coordinate ≠ children pair coordinate
            then 1 else 0 := by
    change
      (pair.val.filter
        (fun parent =>
          parents parent coordinate ≠ children pair coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro parent _
  change
    (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children pair coordinate
        then 1 else 0) =
      ((Finset.univ : Finset (Fin dimension)).filter
        (fun coordinate =>
          parents parent coordinate ≠ children pair coordinate)).card
  exact Finset.sum_boole _ _

theorem pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair : ℕ) : ℝ) /
        (2 * (parentCount.choose 2 : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hone := pairTypeGroupChildOnes_card_le
    parents children coordinate 1
  rw [pairCoordinateKernel_empiricalAverageDisagreement
    hparents parents children coordinate,
    sum_pairCoordinatePairMismatchCount]
  push_cast [hone]
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  let kernel : BinaryPairKernel :=
    pairCoordinateKernel (by omega) parents children coordinate
  have hkernel := empiricalConditionalEntropy_bound
    parentCount (pairParentCoordinateOneCount parents coordinate)
      hparents hones kernel
      (pairCoordinateKernel_parentProbability
        (by omega) parents children coordinate)
  change
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate) ≤ _ at hkernel
  rw [pairCoordinateKernel_empiricalConditionalEntropy
    (by omega) parents children coordinate] at hkernel
  rw [pairCoordinateKernel_empiricalChildMarginal
    (by omega) parents children coordinate] at hkernel
  change
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount at hkernel
  exact hkernel

noncomputable def pairParentArrayEntropyPotential
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayEntropyPotential
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    empiricalAverageDisagreement parentCount
      (pairParentCoordinateOneCount parents coordinate)
      (pairCoordinateKernel (by omega) parents children coordinate)) /
    (dimension : ℝ)

theorem pairChildArrayAverageDisagreement_le_radius
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges :
      ∀ (pair : PairLayer parentCount 1)
        (parent : PairLayer parentCount 0),
        parent ∈ pair.val →
          hammingDist (parents parent) (children pair) ≤ radius) :
    pairChildArrayAverageDisagreement hparents parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ parentCount)
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) ≤
        2 * parentCount.choose 2 * radius := by
    calc
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) =
        ∑ pair : PairLayer parentCount 1,
          ∑ parent ∈ pair.val,
            hammingDist (parents parent) (children pair) :=
        sum_pairCoordinatePairMismatchCount_eq_hammingDist
          parents children
      _ ≤ ∑ pair : PairLayer parentCount 1,
          ∑ _parent ∈ pair.val, radius := by
        apply Finset.sum_le_sum
        intro pair _
        apply Finset.sum_le_sum
        intro parent hparent
        exact hedges pair parent hparent
      _ = ∑ _pair : PairLayer parentCount 1, 2 * radius := by
        apply Finset.sum_congr rfl
        intro pair _
        simp [pair.property]
      _ = 2 * parentCount.choose 2 * radius := by
        simp [pairLayer_card_succ, pairLayer_card_zero,
          Nat.mul_assoc, Nat.mul_comm]
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair : ℕ) : ℝ)) ≤
        2 * (parentCount.choose 2 : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  unfold pairChildArrayAverageDisagreement
  simp_rw [pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    (by omega : 2 ≤ parentCount) parents children]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdimension_real).mpr
  apply (div_le_iff₀ (mul_pos (by norm_num) hpair)).mpr
  nlinarith

theorem pairChildArrayEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    pairChildArrayEntropy parents children ≤
      kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hsum :
      (∑ coordinate : Fin dimension,
        pairCoordinateConditionalEntropy parents children coordinate) ≤
      ∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount) := by
    apply Finset.sum_le_sum
    intro coordinate _
    exact pairCoordinateConditionalEntropy_empirical_bound
      hparents parents children coordinate
  have hnormalized :=
    (div_le_div_iff_of_pos_right hdimension_real).mpr hsum
  change pairChildArrayEntropy parents children ≤ _ at hnormalized
  let disagreementSum : ℝ :=
    ∑ coordinate : Fin dimension,
      empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate)
  let childEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ))
  let parentEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ))
  have hentropy_sum :
      (∑ coordinate : Fin dimension,
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2) =
        (childEntropySum - parentEntropySum) / 2 := by
    dsimp [childEntropySum, parentEntropySum]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hsum_formula :
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (dimension : ℝ) * kappa +
          logTwo 3 * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
    calc
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (∑ _coordinate : Fin dimension, kappa) +
          (∑ coordinate : Fin dimension,
            logTwo 3 *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate)) +
          (∑ coordinate : Fin dimension,
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2) +
          (∑ _coordinate : Fin dimension,
            empiricalEntropyError parentCount) := by
            simp only [Finset.sum_add_distrib]
      _ = (dimension : ℝ) * kappa +
          logTwo 3 * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
        rw [hentropy_sum]
        dsimp [disagreementSum]
        rw [← Finset.mul_sum]
        simp [nsmul_eq_mul]
  calc
    pairChildArrayEntropy parents children ≤
      (∑ coordinate : Fin dimension,
        (kappa +
          logTwo 3 *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) /
            (dimension : ℝ) := hnormalized
    _ = kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
      change
        (∑ coordinate : Fin dimension,
          (kappa +
            logTwo 3 *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate) +
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2 +
            empiricalEntropyError parentCount)) /
              (dimension : ℝ) =
          kappa +
            logTwo 3 * (disagreementSum / (dimension : ℝ)) +
            (childEntropySum / (dimension : ℝ) -
              parentEntropySum / (dimension : ℝ)) / 2 +
            empiricalEntropyError parentCount
      rw [hsum_formula]
      field_simp [hdimension_real.ne']

theorem pairCoordinateConditionalEntropy_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (parentCount.choose 2 : ℝ) *
        pairCoordinateConditionalEntropy parents children coordinate =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  unfold pairCoordinateConditionalEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bitType _
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_log_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      ((pairTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [log_two_pos.ne']
    _ = (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
      rw [← pairCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring

theorem pairChildGroup_choose_product_entropy_bound
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∏ index : PairBitType × Fin dimension,
      ((pairTypeGroup parents index.2 index.1).card).choose
        ((pairTypeGroupChildOnes parents children index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := PairBitType × Fin dimension)
    (fun index => (pairTypeGroup parents index.2 index.1).card)
    (fun index =>
      (pairTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => pairTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((pairTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [pairCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct

theorem pairChildArraysOfRealizedProfile_card_le
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hcard :
      ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) =
        ∏ index : PairBitType × Fin dimension,
          (((pairTypeGroup parents index.2 index.1).card).choose
            ((pairTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      pairChildArraysOfProfile_card parents
        (pairChildCountProfile parents children)
  rw [hcard]
  exact pairChildGroup_choose_product_entropy_bound
    hparents parents children

noncomputable def badPairChildArrays
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildArrayEntropy parents children ≤ threshold)

theorem badPairChildArrays_card_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badPairChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose 2 : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badPairChildArrays parents threshold :
        Finset (PairLayer parentCount 1 → HammingWord dimension)) :
        Set (PairLayer parentCount 1 → HammingWord dimension)).MapsTo
        (pairChildCountProfile parents)
        (Finset.univ : Finset (PairTypeCountProfile parentCount dimension)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : PairTypeCountProfile parentCount dimension) :
      (((badPairChildArrays parents threshold).filter
        (fun children => pairChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badPairChildArrays parents threshold).filter
          (fun children =>
            pairChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : pairChildCountProfile parents children = profile :=
        hparts.2
      have hbad : pairChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 →
                    HammingWord dimension =>
                  pairChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badPairChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badPairChildArrays parents threshold).filter
              (fun candidate =>
                pairChildCountProfile parents candidate = profile) ⊆
            pairChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold pairChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badPairChildArrays parents threshold).filter
            (fun candidate =>
              pairChildCountProfile parents candidate = profile)).card : ℝ) ≤
            ((pairChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((pairChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact pairChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) ≤
              (dimension : ℝ) * threshold := by
        unfold pairChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose 2 : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
      have hexponential :
          Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badPairChildArrays parents threshold).card : ℝ) =
        ∑ profile : PairTypeCountProfile parentCount dimension,
          (((badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : PairTypeCountProfile parentCount dimension, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose 2 : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        pairTypeCountProfile_card]

end HammingProfiles

section SamplingAndHammingBalls

noncomputable def hammingRetentionProbability (dimension : ℕ) : ℝ :=
  Real.exp (-(midpointBeta * (dimension : ℝ) * Real.log 2))

theorem hammingRetentionProbability_pos (dimension : ℕ) :
    0 < hammingRetentionProbability dimension := by
  unfold hammingRetentionProbability
  exact Real.exp_pos _

theorem hammingRetentionProbability_le_one (dimension : ℕ) :
    hammingRetentionProbability dimension ≤ 1 := by
  unfold hammingRetentionProbability
  apply Real.exp_le_one_iff.mpr
  have hproduct :
      0 ≤ midpointBeta * (dimension : ℝ) * Real.log 2 :=
    mul_nonneg
      (mul_nonneg midpointBeta_pos.le (Nat.cast_nonneg dimension))
      log_two_pos.le
  linarith

theorem hammingRetentionProbability_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_add]
  congr 1
  ring

theorem hammingRetentionProbability_sq_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - 2 * midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem hammingRetentionProbability_mul_wordCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by
  have hrate : 0 < (1 - midpointBeta) * Real.log 2 :=
    mul_pos (sub_pos.mpr midpointBeta_lt_one) log_two_pos
  have hlinear :
      Tendsto
        (fun dimension : ℕ =>
          ((1 - midpointBeta) * Real.log 2) * (dimension : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexponential := Real.tendsto_exp_atTop.comp hlinear
  apply hexponential.congr'
  filter_upwards [] with dimension
  simp only [Function.comp_apply]
  rw [hammingRetentionProbability_mul_wordCount_eq_exp]
  congr 1
  ring

theorem hammingRetentionProbability_mul_wordCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingRetentionProbability_mul_wordCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem exp_mul_div_nat_succ_tendsto_atTop
    (rate : ℝ) (hrate : 0 < rate) :
    Tendsto
      (fun dimension : ℕ =>
        Real.exp (rate * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hquotient :
      Tendsto
        (fun dimension : ℕ =>
          Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ))
        atTop atTop := by
    have htendsto :=
      (tendsto_exp_mul_div_rpow_atTop 1 rate hrate).comp
        tendsto_natCast_atTop_atTop
    refine htendsto.congr' ?_
    filter_upwards [] with dimension
    simp [Function.comp_apply]
  have hhalf :
      Tendsto
        (fun dimension : ℕ =>
          (1 / 2 : ℝ) *
            (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)))
        atTop atTop :=
    hquotient.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' atTop _ hhalf
  filter_upwards [Filter.eventually_ge_atTop 1] with dimension hdimension
  have hpositive : 0 < (dimension : ℝ) := by
    exact_mod_cast (show 0 < dimension by omega)
  have hdimension_real : (1 : ℝ) ≤ (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (1 / 2 : ℝ) *
        (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)) =
      Real.exp (rate * (dimension : ℝ)) /
        (2 * (dimension : ℝ)) := by
        ring
    _ ≤ Real.exp (rate * (dimension : ℝ)) /
        ((dimension + 1 : ℕ) : ℝ) := by
      gcongr
      push_cast
      nlinarith

noncomputable def hammingRetentionParameter (dimension : ℕ) : unitInterval :=
  ⟨hammingRetentionProbability dimension,
    hammingRetentionProbability_pos dimension |>.le,
    hammingRetentionProbability_le_one dimension⟩

noncomputable def hammingRetentionMeasure (dimension : ℕ) :
    MeasureTheory.Measure (Set (Bool × HammingWord dimension)) :=
  ProbabilityTheory.setBernoulli Set.univ
    (hammingRetentionParameter dimension)

theorem hammingRetentionMeasure_isProbability (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) := by
  unfold hammingRetentionMeasure
  infer_instance

theorem hammingRetentionMeasure_integrable
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.Integrable observable
      (hammingRetentionMeasure dimension) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  exact MeasureTheory.Integrable.of_finite

theorem hammingRetentionMeasure_memLp_two
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.MemLp observable 2
      (hammingRetentionMeasure dimension) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    (hammingRetentionMeasure_integrable dimension observable).aestronglyMeasurable).mpr
  exact hammingRetentionMeasure_integrable dimension
    (fun retained => observable retained ^ 2)

theorem hammingRetentionMeasure_integral_eq_sum
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂hammingRetentionMeasure dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (hammingRetentionMeasure dimension).real {retained} *
          observable retained := by
  classical
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_fintype
      (hammingRetentionMeasure_integrable dimension observable))

open Classical in
theorem hammingRetentionMeasure_real_event_eq_sum
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (hammingRetentionMeasure dimension).real event =
      ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  let support : Finset (Set (Bool × HammingWord dimension)) :=
    Finset.univ.filter (fun retained => retained ∈ event)
  have hsupport :
      (support : Set (Set (Bool × HammingWord dimension))) = event := by
    ext retained
    simp [support]
  calc
    (hammingRetentionMeasure dimension).real event =
        (hammingRetentionMeasure dimension).real support := by
      rw [hsupport]
    _ = ∑ retained ∈ support,
        (hammingRetentionMeasure dimension).real {retained} := by
      exact (MeasureTheory.sum_measureReal_singleton support).symm
    _ = ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
      rw [← Finset.sum_filter]

open Classical in
theorem hammingRetentionMeasure_integral_event_indicator
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (∫ retained,
      (if retained ∈ event then (1 : ℝ) else 0)
        ∂hammingRetentionMeasure dimension) =
      (hammingRetentionMeasure dimension).real event := by
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  split_ifs <;> simp

theorem hammingRetentionMeasure_real_deviation_le
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂hammingRetentionMeasure dimension)|} ≤
      ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hchebyshev :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (hammingRetentionMeasure_memLp_two dimension observable)
      hthreshold
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchebyshev
  have hnonnegative :
      0 ≤ ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg observable
        (hammingRetentionMeasure dimension))
      (sq_nonneg threshold)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_ofReal hnonnegative]
    using hreal

theorem hammingRetentionMeasure_real_contains_finset
    (dimension : ℕ)
    (required : Finset (Bool × HammingWord dimension)) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} =
      hammingRetentionProbability dimension ^ required.card := by
  classical
  have hpreimage :
      (fun membership : (Bool × HammingWord dimension) → Prop =>
        {vertex | membership vertex}) ⁻¹'
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        Set.pi (required : Set (Bool × HammingWord dimension))
          (fun _ => ({True} : Set Prop)) := by
    ext membership
    simp
  have hmeasure :
      hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        (↑(unitInterval.toNNReal
          (hammingRetentionParameter dimension)) : ENNReal) ^
            required.card := by
    unfold hammingRetentionMeasure
    rw [ProbabilityTheory.setBernoulli_apply']
    rw [hpreimage]
    rw [MeasureTheory.Measure.infinitePi_pi]
    · simp
    · intro vertex _
      measurability
  change
    ENNReal.toReal
        (hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained}) = _
  rw [hmeasure, ENNReal.toReal_pow]
  simp [hammingRetentionParameter]

theorem hammingRetentionMeasure_real_contains_pair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by
  classical
  simpa [hdistinct] using
    hammingRetentionMeasure_real_contains_finset dimension {first, second}

theorem hammingRetentionMeasure_real_contains_vertex
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      hammingRetentionProbability dimension := by
  classical
  simpa using
    hammingRetentionMeasure_real_contains_finset dimension {vertex}

theorem hammingRetentionMeasure_real_contains_edgePair
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      hammingRetentionProbability dimension ^
        (2 +
          (if firstLeft = secondLeft then 0 else 1) +
          (if firstRight = secondRight then 0 else 1)) := by
  classical
  let required : Finset (Bool × HammingWord dimension) :=
    {(false, firstLeft), (true, firstRight),
      (false, secondLeft), (true, secondRight)}
  have hevent :
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} := by
    ext retained
    simp [required, and_left_comm]
  rw [hevent, hammingRetentionMeasure_real_contains_finset]
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight
  · subst secondLeft
    subst secondRight
    simp [required]
  · subst secondLeft
    simp [required, hright]
  · subst secondRight
    simp [required, hleft]
  · simp [required, hleft, hright]

theorem hammingRetentionMeasure_real_contains_edgePair_le
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} ≤
      hammingRetentionProbability dimension ^ 4 +
        (if firstLeft = secondLeft then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstRight = secondRight then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstLeft = secondLeft ∧ firstRight = secondRight then
          hammingRetentionProbability dimension ^ 2 else 0) := by
  rw [hammingRetentionMeasure_real_contains_edgePair]
  have hnonnegative := (hammingRetentionProbability_pos dimension).le
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight <;>
    simp only [hleft, hright, ↓reduceIte, add_zero, Nat.reduceAdd,
      and_self, and_false, and_true, le_add_iff_nonneg_left, ge_iff_le,
      Std.le_refl] <;>
    positivity

noncomputable def hammingExpectedRetainedVertexCount
    (dimension : ℕ) : ℝ :=
  ∑ vertex : Bool × HammingWord dimension,
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained}

theorem hammingExpectedRetainedVertexCount_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexCount dimension =
      2 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
  unfold hammingExpectedRetainedVertexCount
  simp_rw [hammingRetentionMeasure_real_contains_vertex]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring

theorem hammingExpectedRetainedVertexCount_pos
    (dimension : ℕ) :
    0 < hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

theorem hammingExpectedRetainedVertexCount_tendsto_atTop :
    Tendsto hammingExpectedRetainedVertexCount atTop atTop := by
  have hgrowth :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  apply hgrowth.congr'
  filter_upwards [] with dimension
  rw [hammingExpectedRetainedVertexCount_eq]
  ring

theorem hammingExpectedRetainedVertexCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedVertexCount dimension)
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingExpectedRetainedVertexCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem hammingRetentionMeasure_real_vertexPair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2 := by
  classical
  by_cases hequal : first = second
  · subst second
    have hevent :
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ first ∈ retained} =
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained} := by
      ext retained
      simp
    rw [hevent, hammingRetentionMeasure_real_contains_vertex]
    simp
  · rw [hammingRetentionMeasure_real_contains_pair
      dimension first second hequal]
    simp [hequal]

noncomputable def hammingExpectedRetainedVertexSquare
    (dimension : ℕ) : ℝ :=
  ∑ first : Bool × HammingWord dimension,
    ∑ second : Bool × HammingWord dimension,
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ second ∈ retained}

theorem hammingExpectedRetainedVertexSquare_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension =
      (((2 * 2 ^ dimension : ℕ) : ℝ) ^ 2) *
        hammingRetentionProbability dimension ^ 2 +
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        (hammingRetentionProbability dimension -
          hammingRetentionProbability dimension ^ 2) := by
  classical
  have hpoint
      (first second : Bool × HammingWord dimension) :
      (if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2) =
        hammingRetentionProbability dimension ^ 2 +
          (if first = second then
            hammingRetentionProbability dimension -
              hammingRetentionProbability dimension ^ 2
           else 0) := by
    by_cases hequal : first = second <;>
      simp [hequal]
  unfold hammingExpectedRetainedVertexSquare
  simp_rw [hammingRetentionMeasure_real_vertexPair,
    hpoint, Finset.sum_add_distrib]
  simp [HammingWord, nsmul_eq_mul]
  ring

theorem hammingExpectedRetainedVertexVariance_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 =
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension *
        (1 - hammingRetentionProbability dimension) := by
  rw [hammingExpectedRetainedVertexSquare_eq,
    hammingExpectedRetainedVertexCount_eq]
  push_cast
  ring

theorem hammingExpectedRetainedVertexVariance_le_mean
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexVariance_eq,
    hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  have hupper := hammingRetentionProbability_le_one dimension
  have hfactor :
      0 ≤ (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension := by
    positivity
  have hle : 1 - hammingRetentionProbability dimension ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hle hfactor
  push_cast at hscaled ⊢
  nlinarith

noncomputable def hammingRetainedVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact ∑ vertex : Bool × HammingWord dimension,
    if vertex ∈ retained then 1 else 0

open Classical in
theorem hammingRetainedVertexCount_eq_card
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained =
      (Fintype.card retained : ℝ) := by
  classical
  simp [hammingRetainedVertexCount, Fintype.card_subtype]

theorem hammingRetainedVertexCount_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexCount dimension := by
  classical
  unfold hammingRetainedVertexCount hammingExpectedRetainedVertexCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun vertex _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if vertex ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro vertex _
  exact hammingRetentionMeasure_integral_event_indicator dimension
    {retained : Set (Bool × HammingWord dimension) | vertex ∈ retained}

open Classical in
theorem hammingRetainedVertexCount_sq
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by
  classical
  unfold hammingRetainedVertexCount
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases hfirst : first ∈ retained <;>
    by_cases hsecond : second ∈ retained <;>
    simp [hfirst, hsecond]

theorem hammingRetainedVertexCount_sq_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension := by
  classical
  simp_rw [hammingRetainedVertexCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun first _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  unfold hammingExpectedRetainedVertexSquare
  apply Finset.sum_congr rfl
  intro first _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun second _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro second _
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  by_cases hretained : first ∈ retained ∧ second ∈ retained <;>
    simp [hretained]

theorem hammingRetainedVertexCount_variance_eq
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedVertexCount dimension))]
  change
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedVertexCount dimension retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2
  rw [hammingRetainedVertexCount_sq_integral_eq,
    hammingRetainedVertexCount_integral_eq]

theorem hammingRetainedVertexCount_variance_le
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingRetainedVertexCount_variance_eq]
  exact hammingExpectedRetainedVertexVariance_le_mean dimension

theorem hammingRetainedVertexCount_deviation_probability_le
    (dimension : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      hammingExpectedRetainedVertexCount dimension / threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedVertexCount dimension)
    threshold hthreshold
  rw [hammingRetainedVertexCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      ProbabilityTheory.variance
          (hammingRetainedVertexCount dimension)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedVertexCount_variance_le dimension

theorem hammingRetainedVertexCount_upper_tail_probability_le
    (dimension : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      4 / hammingExpectedRetainedVertexCount dimension := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedVertexCount_pos dimension
  have hthreshold :
      0 < hammingExpectedRetainedVertexCount dimension / 2 := by
    positivity
  have hchebyshev := hammingRetainedVertexCount_deviation_probability_le
    dimension (hammingExpectedRetainedVertexCount dimension / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedVertexCount dimension / 2 ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} := by
    intro retained hretained
    change
      hammingExpectedRetainedVertexCount dimension / 2 ≤
        |hammingRetainedVertexCount dimension retained -
          hammingExpectedRetainedVertexCount dimension|
    have habsolute := le_abs_self
      (hammingRetainedVertexCount dimension retained -
        hammingExpectedRetainedVertexCount dimension)
    rw [hammingExpectedRetainedVertexCount_eq] at habsolute ⊢
    change
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained at hretained
    nlinarith
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          hammingExpectedRetainedVertexCount dimension / 2 ≤
            |hammingRetainedVertexCount dimension retained -
              hammingExpectedRetainedVertexCount dimension|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        (hammingExpectedRetainedVertexCount dimension / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedVertexCount dimension := by
      field_simp [hmean.ne']
      ring

noncomputable def pairChildVertexFinset
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (PairLayer parentCount 1)).image
    (fun pair => (side, children pair))

theorem pairChildVertexFinset_card
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (pairChildVertexFinset side children).card = parentCount.choose 2 := by
  classical
  unfold pairChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)

def pairChildRetentionEvent
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ pair, (side, children pair) ∈ retained}

theorem hammingRetentionMeasure_real_pairChildren
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (hammingRetentionMeasure dimension).real
        (pairChildRetentionEvent side children) =
      hammingRetentionProbability dimension ^ (parentCount.choose 2) := by
  classical
  have hevent :
      pairChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ pairChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [pairChildRetentionEvent, pairChildVertexFinset]
  rw [hevent, hammingRetentionMeasure_real_contains_finset,
    pairChildVertexFinset_card side children hinjective]

noncomputable def badPairChildRetentionEvent
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badPairChildArrays parents threshold).filter Function.Injective,
      pairChildRetentionEvent side children

theorem badPairChildRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let distinctBad :
      Finset (PairLayer parentCount 1 → HammingWord dimension) :=
    (badPairChildArrays parents threshold).filter Function.Injective
  have hprobability_nonneg :
      0 ≤ hammingRetentionProbability dimension ^
        (parentCount.choose 2) :=
    pow_nonneg (hammingRetentionProbability_pos dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badPairChildArrays parents threshold).card : ℝ) := by
    dsimp [distinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badPairChildArrays parents threshold) Function.Injective
  calc
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ children ∈ distinctBad,
          pairChildRetentionEvent side children) := by
        rfl
    _ ≤ ∑ children ∈ distinctBad,
          (hammingRetentionMeasure dimension).real
            (pairChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (pairChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        apply Finset.sum_congr rfl
        intro children hchildren
        have hinjective : Function.Injective children := by
          have hmembership :
              children ∈
                (badPairChildArrays parents threshold).filter
                  Function.Injective := by
            simpa only [distinctBad] using hchildren
          exact (Finset.mem_filter.mp hmembership).2
        exact hammingRetentionMeasure_real_pairChildren
          side children hinjective
    _ = (distinctBad.card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badPairChildArrays parents threshold).card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right
          (badPairChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg

theorem hammingParentTuple_card (parentCount dimension : ℕ) :
    Fintype.card (Fin parentCount → HammingWord dimension) =
      2 ^ (dimension * parentCount) := by
  simp [HammingWord, ← pow_mul]

noncomputable def badPairLayerRetentionEvent
    (parentCount dimension : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badPairChildRetentionEvent parents side threshold

theorem badPairLayerRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let bound : ℝ :=
    ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badPairChildRetentionEvent parents side threshold) := by
        rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (hammingRetentionMeasure dimension).real
            (badPairChildRetentionEvent parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badPairChildRetentionEvent parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      apply Finset.sum_le_sum
      intro parents _
      exact badPairChildRetentionEvent_real_le
        hparents hdimension parents side threshold
    _ =
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card]
      dsimp [bound]
      ring

theorem badPairLayerRetentionBound_eq_exp
    (parentCount dimension : ℕ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (midpointBeta - entropySlack))) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) := by
  have hparent :
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
        Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
          (2 : ℝ) ^ (dimension * parentCount) := by
            norm_cast
      _ = Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hprofile :
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
        Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
          (((parentCount.choose 2 + 1 : ℕ) : ℝ)) ^
            (3 * dimension) := by
              norm_cast
      _ = Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      hammingRetentionProbability dimension ^
          (parentCount.choose 2) =
        Real.exp
          ((parentCount.choose 2 : ℝ) *
            (-(midpointBeta * (dimension : ℝ) * Real.log 2))) := by
    unfold hammingRetentionProbability
    rw [Real.exp_nat_mul]
  rw [hparent, hprofile, hretention,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  unfold logTwo
  push_cast
  field_simp [log_two_pos.ne']
  ring

theorem badPairLayerRetentionEvent_real_lt_exp_neg
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * (parentCount.choose 2 : ℝ) < -1)
    (side : Bool) :
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (midpointBeta - entropySlack)) ≤
      ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * (midpointBeta - entropySlack))) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2)) :=
        badPairLayerRetentionEvent_real_le
          (by omega) hdimension side (midpointBeta - entropySlack)
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) :=
        badPairLayerRetentionBound_eq_exp parentCount dimension
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith

noncomputable def badPairLayersRetentionEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badPairLayerRetentionEvent (layerSizes layer) dimension side
      (midpointBeta - entropySlack)

theorem badPairLayersRetentionEvent_real_le
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  let bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) =
      (hammingRetentionMeasure dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badPairLayerRetentionEvent (layerSizes layer) dimension side
            (midpointBeta - entropySlack)) := by
        rfl
    _ ≤ ∑ side : Bool,
        (hammingRetentionMeasure dimension).real
          (⋃ layer : Fin depth,
            badPairLayerRetentionEvent (layerSizes layer) dimension side
              (midpointBeta - entropySlack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun side =>
            ⋃ layer : Fin depth,
              badPairLayerRetentionEvent (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (hammingRetentionMeasure dimension).real
            (badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack)) := by
        apply Finset.sum_le_sum
        intro side _
        exact MeasureTheory.measureReal_iUnion_fintype_le
          (fun layer =>
            badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (midpointBeta - entropySlack))
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        apply Finset.sum_le_sum
        intro side _
        apply Finset.sum_le_sum
        intro layer _
        exact (badPairLayerRetentionEvent_real_lt_exp_neg
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [bound, nsmul_eq_mul]
        ring

theorem exp_neg_dimension_log_two (dimension : ℕ) :
    Real.exp (-(dimension : ℝ) * Real.log 2) =
      ((1 / 2 : ℝ) ^ dimension) := by
  calc
    Real.exp (-(dimension : ℝ) * Real.log 2) =
        Real.exp (-((dimension : ℝ) * Real.log 2)) := by
          congr 1
          ring
    _ = (Real.exp ((dimension : ℝ) * Real.log 2))⁻¹ :=
      Real.exp_neg _
    _ = ((2 : ℝ) ^ dimension)⁻¹ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = ((1 / 2 : ℝ) ^ dimension) := by
      rw [← inv_pow]
      norm_num

theorem pairLayerExclusionProbability_tendsto_zero (depth : ℕ) :
    Filter.Tendsto
      (fun dimension : ℕ =>
        (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := by
  have hgeometric :
      Filter.Tendsto
        (fun dimension : ℕ => (1 / 2 : ℝ) ^ dimension)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp_rw [exp_neg_dimension_log_two]
  simpa only [mul_zero] using
    hgeometric.const_mul (((2 * depth : ℕ) : ℝ))

theorem exists_hammingRetention_outside_event
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension)))
    (hsmall : (hammingRetentionMeasure dimension).real event < 1) :
    ∃ retained : Set (Bool × HammingWord dimension), retained ∉ event := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  by_contra hnone
  push Not at hnone
  have hevent : event = Set.univ := Set.eq_univ_of_forall hnone
  rw [hevent] at hsmall
  simp at hsmall

theorem exists_actualPairLayer_exclusion_parameters :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ layer : Fin depth,
        let layerSize :=
          Fintype.card (PairLayer baseSize layer.val)
        4 ≤ layerSize ∧
        empiricalEntropyError layerSize < entropySlack ∧
        (layerSize : ℝ) +
          3 * logTwo ((layerSize.choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * (layerSize.choose 2 : ℝ) < -1 := by
  obtain ⟨baseSize, hbase, hbase_conditions⟩ :=
    exists_entropy_exclusion_base
  obtain ⟨depth, hdepth, hdepth_window⟩ :=
    exists_entropy_exclusion_depth
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  intro layer
  dsimp
  have hsize :
      baseSize ≤ Fintype.card (PairLayer baseSize layer.val) :=
    pairLayer_card_ge_base baseSize layer.val hbase
  obtain ⟨herror, hfirst_moment⟩ :=
    hbase_conditions
      (Fintype.card (PairLayer baseSize layer.val)) hsize
  exact ⟨hbase.trans hsize, herror, hfirst_moment⟩

noncomputable def hammingDifferenceSet {dimension : ℕ}
    (u v : HammingWord dimension) : Finset (Fin dimension) := by
  classical
  exact Finset.univ.filter (fun coordinate => u coordinate ≠ v coordinate)

noncomputable def hammingFlip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    HammingWord dimension := by
  classical
  exact fun coordinate =>
    if coordinate ∈ coordinates then !(u coordinate) else u coordinate

theorem hammingDifferenceSet_flip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    hammingDifferenceSet u (hammingFlip u coordinates) = coordinates := by
  classical
  ext coordinate
  by_cases hcoordinate : coordinate ∈ coordinates
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]

theorem hammingFlip_differenceSet {dimension : ℕ}
    (u v : HammingWord dimension) :
    hammingFlip u (hammingDifferenceSet u v) = v := by
  classical
  funext coordinate
  cases hu : u coordinate <;> cases hv : v coordinate <;>
    simp [hammingFlip, hammingDifferenceSet, hu, hv]

noncomputable def hammingBall (dimension radius : ℕ)
    (u : HammingWord dimension) : Finset (HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun v => hammingDist u v ≤ radius)

noncomputable def boundedDifferenceSets (dimension radius : ℕ) :
    Finset (Finset (Fin dimension)) := by
  classical
  exact ((Finset.univ : Finset (Fin dimension)).powerset).filter
    (fun coordinates => coordinates.card ≤ radius)

noncomputable def hammingBallEquiv (dimension radius : ℕ)
    (u : HammingWord dimension) :
    ↥(hammingBall dimension radius u) ≃
      ↥(boundedDifferenceSets dimension radius) := by
  classical
  refine
    { toFun := fun v => ⟨hammingDifferenceSet u v.val, ?_⟩
      invFun := fun coordinates =>
        ⟨hammingFlip u coordinates.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hball : hammingDist u v.val ≤ radius := by
      have hmembership : v.val ∈
          (Finset.univ.filter
            (fun w : HammingWord dimension => hammingDist u w ≤ radius)) := by
        simpa only [hammingBall] using v.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [boundedDifferenceSets, Finset.mem_filter,
      Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, ?_⟩
    simpa [hammingDist, hammingDifferenceSet] using hball
  · have hcoordinates : coordinates.val.card ≤ radius := by
      have hmembership : coordinates.val ∈
          (((Finset.univ : Finset (Fin dimension)).powerset).filter
            (fun S => S.card ≤ radius)) := by
        simpa only [boundedDifferenceSets] using coordinates.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
    change (hammingDifferenceSet u
      (hammingFlip u coordinates.val)).card ≤ radius
    simpa [hammingDifferenceSet_flip] using hcoordinates
  · intro v
    apply Subtype.ext
    exact hammingFlip_differenceSet u v.val
  · intro coordinates
    apply Subtype.ext
    exact hammingDifferenceSet_flip u coordinates.val

theorem boundedDifferenceSets_card (dimension radius : ℕ) :
    (boundedDifferenceSets dimension radius).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  classical
  have hmaps :
      ((boundedDifferenceSets dimension radius :
        Finset (Finset (Fin dimension))) : Set (Finset (Fin dimension))).MapsTo
        Finset.card (Finset.range (radius + 1)) := by
    intro S hS
    have hmembership : S ∈
        (((Finset.univ : Finset (Fin dimension)).powerset).filter
          (fun coordinates => coordinates.card ≤ radius)) := by
      exact Finset.mem_coe.mp hS
    have hcard := (Finset.mem_filter.mp hmembership).2
    exact Finset.mem_range.mpr (by omega)
  calc
    (boundedDifferenceSets dimension radius).card =
        ∑ d ∈ Finset.range (radius + 1),
          ((boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdle : d ≤ radius := by
        have := Finset.mem_range.mp hd
        omega
      have hfiber :
          (boundedDifferenceSets dimension radius).filter
            (fun coordinates => coordinates.card = d) =
          (Finset.univ : Finset (Fin dimension)).powersetCard d := by
        ext coordinates
        simp only [boundedDifferenceSets, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hsubset, _⟩, hcard⟩
          exact ⟨hsubset, hcard⟩
        · rintro ⟨hsubset, hcard⟩
          exact ⟨⟨hsubset, by omega⟩, hcard⟩
      rw [hfiber, Finset.card_powersetCard]
      simp

theorem hammingBall_card (dimension radius : ℕ)
    (u : HammingWord dimension) :
    (hammingBall dimension radius u).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by
  calc
    (hammingBall dimension radius u).card =
        Fintype.card ↥(hammingBall dimension radius u) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥(boundedDifferenceSets dimension radius) :=
      Fintype.card_congr (hammingBallEquiv dimension radius u)
    _ = (boundedDifferenceSets dimension radius).card :=
      Fintype.card_coe _
    _ = ∑ d ∈ Finset.range (radius + 1), dimension.choose d :=
      boundedDifferenceSets_card dimension radius

end SamplingAndHammingBalls

attribute [local instance] Classical.propDecidable

section HammingHostAndExclusion

def hammingHost (dimension radius : ℕ) :
    SimpleGraph (Bool × HammingWord dimension) :=
  SimpleGraph.fromRel
    (fun x y => x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius)

theorem hammingHost_adj_iff (dimension radius : ℕ)
    (x y : Bool × HammingWord dimension) :
    (hammingHost dimension radius).Adj x y ↔
      x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius := by
  rw [hammingHost, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hforward | hbackward⟩
    · exact hforward
    · exact ⟨Ne.symm hbackward.1, by
        simpa [hammingDist_comm] using hbackward.2⟩
  · intro hxy
    refine ⟨?_, Or.inl hxy⟩
    intro heq
    exact hxy.1 (congrArg Prod.fst heq)

theorem hammingBall_card_ge_boundary_binomial
    (dimension radius : ℕ)
    (word : HammingWord dimension) :
    dimension.choose radius ≤ (hammingBall dimension radius word).card := by
  rw [hammingBall_card]
  apply Finset.single_le_sum
    (s := Finset.range (radius + 1))
    (f := fun distance => dimension.choose distance)
  · intro distance _
    exact Nat.zero_le _
  · simp

theorem hammingWordNeighbor_sum_const
    (dimension radius : ℕ) (left : HammingWord dimension)
    (weight : ℝ) :
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
      ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
        ∑ _right ∈ hammingBall dimension radius left, weight := by
          rw [← Finset.sum_filter]
          rfl
    _ = ((hammingBall dimension radius left).card : ℝ) * weight := by
      simp [nsmul_eq_mul]
    _ = ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by
      rw [hammingBall_card]

theorem hammingWordEdge_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius then weight else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  simp_rw [hammingWordNeighbor_sum_const]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring

theorem hammingWordEdgePair_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              weight
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) ^ 2 *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            weight
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((2 ^ dimension : ℕ) : ℝ) *
            ((∑ distance ∈ Finset.range (radius + 1),
              dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hammingWordEdge_sum_const dimension radius weight
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring

theorem hammingWordEdgePairSharedLeft_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hshared (firstLeft : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
    calc
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        ∑ secondLeft : HammingWord dimension,
          if firstLeft = secondLeft then
            ∑ secondRight : HammingWord dimension,
              if hammingDist secondLeft secondRight ≤ radius then
                weight else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro secondLeft _
            by_cases hleft : firstLeft = secondLeft
            · subst secondLeft
              simp
            · simp [hleft]
      _ = ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) * weight := by
        simp [hammingWordNeighbor_sum_const]
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if firstLeft = secondLeft then weight else 0
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hshared firstLeft
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring

theorem hammingWordEdgePairSharedRight_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  calc
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      (∑ firstRight : HammingWord dimension,
        ∑ firstLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            ∑ secondLeft : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if firstRight = secondRight then weight else 0
              else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro firstRight _
        apply Finset.sum_congr rfl
        intro firstLeft _
        rw [Finset.sum_comm]
    _ = ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
      simpa only [hammingDist_comm] using
        hammingWordEdgePairSharedLeft_sum_const dimension radius weight

theorem hammingWordEdgePairIdentical_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    _ = ∑ firstLeft : HammingWord dimension,
          ∑ firstRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius then weight else 0 := by
      apply Finset.sum_congr rfl
      intro firstLeft _
      apply Finset.sum_congr rfl
      intro firstRight _
      by_cases hedge : hammingDist firstLeft firstRight ≤ radius
      · simp only [hedge, true_and, if_true]
        have hpoint (secondLeft secondRight : HammingWord dimension) :
            (if hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
              if firstLeft = secondLeft then
                if firstRight = secondRight then weight else 0
              else 0 := by
          split_ifs <;> simp_all
        simp_rw [hpoint]
        simp
      · simp [hedge]
    _ = _ := hammingWordEdge_sum_const dimension radius weight

noncomputable def hammingExpectedRetainedEdgeCount
    (dimension radius : ℕ) : ℝ :=
  ∑ left : HammingWord dimension,
    ∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then
        (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained}
      else 0

theorem hammingExpectedRetainedEdgeCount_eq
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeCount dimension radius =
      hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) := by
  classical
  have hpair (left right : HammingWord dimension) :
      (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained} =
        hammingRetentionProbability dimension ^ 2 :=
    hammingRetentionMeasure_real_contains_pair
      dimension (false, left) (true, right) (by simp)
  unfold hammingExpectedRetainedEdgeCount
  simp_rw [hpair]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    hammingWordEdge_sum_const dimension radius
      (hammingRetentionProbability dimension ^ 2)

theorem hammingExpectedRetainedEdgeCount_pos
    (dimension radius : ℕ) :
    0 < hammingExpectedRetainedEdgeCount dimension radius := by
  have hterm :
      1 ≤ ∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance := by
    have hzero := Finset.single_le_sum
      (s := Finset.range (radius + 1))
      (f := fun distance : ℕ => dimension.choose distance)
      (fun distance _ => Nat.zero_le _)
      (show 0 ∈ Finset.range (radius + 1) by simp)
    simpa using hzero
  have hdegree :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  rw [hammingExpectedRetainedEdgeCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

noncomputable def hammingExpectedRetainedEdgeSquare
    (dimension radius : ℕ) : ℝ :=
  ∑ firstLeft : HammingWord dimension,
    ∑ firstRight : HammingWord dimension,
      ∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            (hammingRetentionMeasure dimension).real
              {retained : Set (Bool × HammingWord dimension) |
                (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained}
          else 0

theorem hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧
                      firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 := by
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_le_sum
  intro firstLeft _
  apply Finset.sum_le_sum
  intro firstRight _
  apply Finset.sum_le_sum
  intro secondLeft _
  apply Finset.sum_le_sum
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    exact hammingRetentionMeasure_real_contains_edgePair_le
      dimension firstLeft firstRight secondLeft secondRight
  · simp [hedge]

theorem hammingExpectedRetainedEdgeSquare_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  classical
  have hpoint
      (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
      (if hammingDist firstLeft firstRight ≤ radius ∧
          hammingDist secondLeft secondRight ≤ radius then
        hammingRetentionProbability dimension ^ 4 +
          (if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0)
      else 0) =
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          hammingRetentionProbability dimension ^ 4 else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0
        else 0) := by
    split <;> simp
  calc
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧ firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 :=
        hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
          dimension radius
    _ = hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [hammingWordEdgePair_sum_const,
        hammingWordEdgePairSharedLeft_sum_const,
        hammingWordEdgePairSharedRight_sum_const,
        hammingWordEdgePairIdentical_sum_const,
        hammingExpectedRetainedEdgeCount_eq]
      ring

theorem hammingExpectedRetainedEdgeVariance_le
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  have hsecond := hammingExpectedRetainedEdgeSquare_le dimension radius
  linarith

noncomputable def retainedHammingWordEdges
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    Finset (HammingWord dimension × HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun edge =>
    hammingDist edge.1 edge.2 ≤ radius ∧
      (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained)

noncomputable def hammingRetainedEdgeCount
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact
    ∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then 1 else 0

theorem hammingRetainedEdgeCount_eq_wordEdges_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
  classical
  unfold hammingRetainedEdgeCount
  calc
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0) =
      ∑ edge : HammingWord dimension × HammingWord dimension,
        if hammingDist edge.1 edge.2 ≤ radius ∧
            (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained
        then (1 : ℝ) else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ _edge ∈ retainedHammingWordEdges dimension radius retained,
          (1 : ℝ) := by
      unfold retainedHammingWordEdges
      rw [← Finset.sum_filter]
    _ = ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
      simp

theorem hammingRetainedEdgeCount_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeCount dimension radius := by
  classical
  unfold hammingRetainedEdgeCount hammingExpectedRetainedEdgeCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun left _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ right : HammingWord dimension,
          if hammingDist left right ≤ radius ∧
              (false, left) ∈ retained ∧ (true, right) ∈ retained
          then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro left _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun right _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hedge : hammingDist left right ≤ radius
  · simp only [hedge, true_and, if_true]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, left) ∈ retained ∧ (true, right) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

open Classical in
theorem hammingRetainedEdgeCount_sq
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained ^ 2 =
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0 := by
  classical
  unfold hammingRetainedEdgeCount
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstRight _
  apply Finset.sum_congr rfl
  intro secondLeft _
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hfirst_edge : hammingDist firstLeft firstRight ≤ radius <;>
    by_cases hsecond_edge : hammingDist secondLeft secondRight ≤ radius <;>
    by_cases hfirst_left : (false, firstLeft) ∈ retained <;>
    by_cases hfirst_right : (true, firstRight) ∈ retained <;>
    by_cases hsecond_left : (false, secondLeft) ∈ retained <;>
    by_cases hsecond_right : (true, secondRight) ∈ retained <;>
    simp [hfirst_edge, hsecond_edge, hfirst_left, hfirst_right,
      hsecond_left, hsecond_right]

theorem hammingRetainedEdgeCount_sq_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius := by
  classical
  simp_rw [hammingRetainedEdgeCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0))]
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if (false, firstLeft) ∈ retained ∧
                  (true, firstRight) ∈ retained ∧
                  (false, secondLeft) ∈ retained ∧
                  (true, secondRight) ∈ retained
              then (1 : ℝ) else 0
            else 0))]
  apply Finset.sum_congr rfl
  intro firstRight _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondLeft _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained
            then (1 : ℝ) else 0
          else 0))]
  apply Finset.sum_congr rfl
  intro secondLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondRight _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if (false, firstLeft) ∈ retained ∧
              (true, firstRight) ∈ retained ∧
              (false, secondLeft) ∈ retained ∧
              (true, secondRight) ∈ retained
          then (1 : ℝ) else 0
        else 0))]
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, firstLeft) ∈ retained ∧
          (true, firstRight) ∈ retained ∧
          (false, secondLeft) ∈ retained ∧
          (true, secondRight) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

theorem hammingRetainedEdgeCount_variance_eq
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedEdgeCount dimension radius))]
  change
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedEdgeCount dimension radius retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedEdgeSquare dimension radius -
        hammingExpectedRetainedEdgeCount dimension radius ^ 2
  rw [hammingRetainedEdgeCount_sq_integral_eq,
    hammingRetainedEdgeCount_integral_eq]

theorem hammingRetainedEdgeCount_variance_le
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  rw [hammingRetainedEdgeCount_variance_eq]
  exact hammingExpectedRetainedEdgeVariance_le dimension radius

theorem hammingRetainedEdgeCount_deviation_probability_le
    (dimension radius : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedEdgeCount dimension radius)
    threshold hthreshold
  rw [hammingRetainedEdgeCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} ≤
      ProbabilityTheory.variance
          (hammingRetainedEdgeCount dimension radius)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedEdgeCount_variance_le dimension radius

theorem hammingRetainedEdgeCount_lower_tail_probability_le
    (dimension radius : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedEdgeCount_pos dimension radius
  have hthreshold :
      0 < hammingExpectedRetainedEdgeCount dimension radius / 2 := by
    positivity
  have hchebyshev := hammingRetainedEdgeCount_deviation_probability_le
    dimension radius
    (hammingExpectedRetainedEdgeCount dimension radius / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} := by
    intro retained hretained
    change
      hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
        |hammingRetainedEdgeCount dimension radius retained -
          hammingExpectedRetainedEdgeCount dimension radius|
    have habsolute := neg_le_abs
      (hammingRetainedEdgeCount dimension radius retained -
        hammingExpectedRetainedEdgeCount dimension radius)
    change
      hammingRetainedEdgeCount dimension radius retained <
        hammingExpectedRetainedEdgeCount dimension radius / 2 at hretained
    linarith
  have hdegree_positive :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    have hterm :
        1 ≤ ∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance := by
      have hzero := Finset.single_le_sum
        (s := Finset.range (radius + 1))
        (f := fun distance : ℕ => dimension.choose distance)
        (fun distance _ => Nat.zero_le _)
        (show 0 ∈ Finset.range (radius + 1) by simp)
      simpa using hzero
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  have hprobability := hammingRetentionProbability_pos dimension
  have hwords : 0 < ((2 ^ dimension : ℕ) : ℝ) := by
    positivity
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          hammingExpectedRetainedEdgeCount dimension radius / 2} ≤
      (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedEdgeCount dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            hammingExpectedRetainedEdgeCount dimension radius|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤
      (hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        (hammingExpectedRetainedEdgeCount dimension radius / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedEdgeCount dimension radius +
        8 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
      rw [hammingExpectedRetainedEdgeCount_eq]
      field_simp [hprobability.ne', hwords.ne', hdegree_positive.ne']
      ring

def retainedHammingHost (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : SimpleGraph retained :=
  (hammingHost dimension radius).induce retained

open Classical in
theorem retainedHammingHost_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    (retainedHammingHost dimension radius retained).edgeFinset.card =
      (retainedHammingWordEdges dimension radius retained).card := by
  classical
  let toEdge :
      ∀ edge ∈ retainedHammingWordEdges dimension radius retained,
        Sym2 retained := fun edge hedge =>
    s(⟨(false, edge.1), by
        exact (Finset.mem_filter.mp hedge).2.2.1⟩,
      ⟨(true, edge.2), by
        exact (Finset.mem_filter.mp hedge).2.2.2⟩)
  have hcard :
      (retainedHammingWordEdges dimension radius retained).card =
        (retainedHammingHost dimension radius retained).edgeFinset.card := by
    apply Finset.card_bij toEdge
    · intro edge hedge
      have hdata := (Finset.mem_filter.mp hedge).2
      change
        s(⟨(false, edge.1), hdata.2.1⟩,
          ⟨(true, edge.2), hdata.2.2⟩) ∈
          (retainedHammingHost dimension radius retained).edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change (hammingHost dimension radius).Adj
        (false, edge.1) (true, edge.2)
      apply (hammingHost_adj_iff dimension radius _ _).mpr
      exact ⟨by simp, hdata.1⟩
    · intro first hfirst second hsecond hequal
      dsimp [toEdge] at hequal
      rcases (Sym2.eq_iff.mp hequal) with
        ⟨hleft, hright⟩ | ⟨hswap, _⟩
      · apply Prod.ext
        · exact congrArg (fun vertex : retained => vertex.val.2) hleft
        · exact congrArg (fun vertex : retained => vertex.val.2) hright
      · have hside :=
          congrArg (fun vertex : retained => vertex.val.1) hswap
        simp at hside
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | hf first second =>
        have hadj :
            (retainedHammingHost dimension radius retained).Adj
              first second := by
          exact (SimpleGraph.mem_edgeSet
            (retainedHammingHost dimension radius retained)).mp
              ((SimpleGraph.mem_edgeFinset).mp hedge)
        have hhost :
            (hammingHost dimension radius).Adj
              first.val second.val := hadj
        rcases first with ⟨⟨firstSide, firstWord⟩, hfirst⟩
        rcases second with ⟨⟨secondSide, secondWord⟩, hsecond⟩
        have hdata :=
          (hammingHost_adj_iff dimension radius
            (firstSide, firstWord) (secondSide, secondWord)).mp hhost
        cases firstSide <;> cases secondSide
        · simp at hdata
        · refine ⟨(firstWord, secondWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hdata.2, hfirst, hsecond]
          · simp [toEdge]
        · have hreverse : hammingDist secondWord firstWord ≤ radius := by
            simpa [hammingDist_comm] using hdata.2
          refine ⟨(secondWord, firstWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hreverse, hfirst, hsecond]
          · dsimp [toEdge]
            exact Sym2.eq_swap
        · simp at hdata
  exact hcard.symm

open Classical in
theorem hammingRetainedEdgeCount_eq_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingHost dimension radius retained).edgeFinset.card : ℝ) := by
  rw [hammingRetainedEdgeCount_eq_wordEdges_card,
    retainedHammingHost_edgeFinset_card]

theorem pairGraphCopy_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize layer) :
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) second)).val.1 := by
  classical
  by_cases hequal : first = second
  · subst second
    rfl
  · let bridge : PairLayer baseSize (layer + 1) :=
      ⟨{first, second}, Finset.card_pair hequal⟩
    have hfirst_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) first) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge first
        (by simp [bridge])
    have hsecond_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) second) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge second
        (by simp [bridge])
    have hfirst_edge := copy.toHom.map_rel hfirst_source
    have hsecond_edge := copy.toHom.map_rel hsecond_source
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val at hfirst_edge
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val at hsecond_edge
    have hfirst_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
    have hsecond_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
    cases hbridge :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer bridge)).val.1 <;>
      cases hfirst :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val.1 <;>
      cases hsecond :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val.1 <;>
      simp_all

theorem pairGraphCopy_child_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize (layer + 1)) :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer second)).val.1 := by
  classical
  have hfirst_nonempty : first.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [first.property]
    norm_num
  have hsecond_nonempty : second.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [second.property]
    norm_num
  obtain ⟨firstParent, hfirstParent⟩ := hfirst_nonempty
  obtain ⟨secondParent, hsecondParent⟩ := hsecond_nonempty
  have hparent_side := pairGraphCopy_layer_side_eq
    retained copy layer hlayer firstParent secondParent
  have hfirst_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer first firstParent hfirstParent)
  have hsecond_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer second secondParent hsecondParent)
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer first)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val at hfirst_edge
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val at hsecond_edge
  have hfirst_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
  have hsecond_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
  cases hfirst :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 <;>
    cases hsecond :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val.1 <;>
    cases hfirstParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val.1 <;>
    cases hsecondParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val.1 <;>
    simp_all

noncomputable def pairGraphCopyParentWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Fin (Fintype.card (PairLayer baseSize layer.val)) →
      HammingWord dimension :=
  fun parent =>
    (copy
      (pairLayerEmbedding baseSize depth layer.val (by omega)
        ((pairLayerFinEquiv baseSize layer.val).symm parent))).val.2

noncomputable def pairGraphCopyChildWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1 →
      HammingWord dimension :=
  fun pair =>
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).val.2

noncomputable def pairGraphCopyChildSide
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) : Bool :=
  (copy
    (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((pairLayerPairEquiv baseSize layer.val) reference))).val.1

noncomputable def pairGraphCopyLayerPotential
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : PairLayer baseSize layer.val =>
          (copy
            (pairLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
        (Fintype.card (PairLayer baseSize layer.val) : ℝ))) /
    (dimension : ℝ)

theorem pairGraphCopy_parentPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairParentArrayEntropyPotential
        (pairGraphCopyParentWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val, by omega⟩ := by
  unfold pairParentArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount pairGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (pairLayerFinEquiv baseSize layer.val).symm
    (fun vertex : PairLayer baseSize layer.val =>
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          vertex)).val.2 coordinate)]

theorem pairGraphCopy_childPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayEntropyPotential
        (pairGraphCopyChildWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val + 1, by omega⟩ := by
  unfold pairChildArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairChildCoordinateOneCount pairGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (pairLayerPairEquiv baseSize layer.val)
    (fun vertex : PairLayer baseSize (layer.val + 1) =>
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          vertex)).val.2 coordinate)]
  rw [pairLayer_card_succ]

theorem pairGraphCopyLayerPotential_mem_Icc
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) :
    0 ≤ pairGraphCopyLayerPotential retained copy layer ∧
      pairGraphCopyLayerPotential retained copy layer ≤ 1 := by
  classical
  have hlayer :
      0 < Fintype.card (PairLayer baseSize layer.val) := by
    have hcard := pairLayer_card_ge_base
      baseSize layer.val hbase
    omega
  have hlayer_real :
      0 < (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card ≤
          Fintype.card (PairLayer baseSize layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (PairLayer baseSize layer.val))
          (fun vertex =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate = true))
    have hzero :
        0 ≤
          ((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
      positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone,
      binaryEntropy_le_one _⟩
  unfold pairGraphCopyLayerPotential
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg
        (fun coordinate _ => (hterm coordinate).1)
    · exact hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc
      (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val.2 coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) := by
          exact Finset.sum_le_sum
            (fun coordinate _ => (hterm coordinate).2)
      _ = (dimension : ℝ) := by
        simp

theorem pairGraphCopy_layer_entropy_upper_of_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdisagreement :
      pairChildArrayAverageDisagreement
        (hbase.trans
          (pairLayer_card_ge_base baseSize layer.val hbase))
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    pairChildArrayEntropy
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        entropyLowerEndpoint +
          (pairGraphCopyLayerPotential retained copy
              ⟨layer.val + 1, by omega⟩ -
            pairGraphCopyLayerPotential retained copy
              ⟨layer.val, by omega⟩) / 2 +
          empiricalEntropyError
            (Fintype.card (PairLayer baseSize layer.val)) := by
  have hparents :
      4 ≤ Fintype.card (PairLayer baseSize layer.val) :=
    hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase)
  have hbound := pairChildArrayEntropy_empirical_bound
    hparents hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
  rw [pairGraphCopy_childPotential_eq retained copy layer,
    pairGraphCopy_parentPotential_eq retained copy layer] at hbound
  have hscaled := mul_le_mul_of_nonneg_left
    hdisagreement logTwo_three_pos.le
  unfold entropyLowerEndpoint
  nlinarith

theorem pairGraphCopyChildWords_injective
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Function.Injective (pairGraphCopyChildWords retained copy layer) := by
  intro first second hwords
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) first)
    ((pairLayerPairEquiv baseSize layer.val) second)
  have hvertices :
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first))).val =
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second))).val := by
    apply Prod.ext
    · exact hside
    · exact hwords
  have himages :
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first)) =
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second)) :=
    Subtype.ext hvertices
  have hsources := copy.injective himages
  have hpairs :=
    (pairLayerEmbedding baseSize depth (layer.val + 1)
      (by omega)).injective hsources
  exact (pairLayerPairEquiv baseSize layer.val).injective hpairs

theorem pairGraphCopyChildWords_retained
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) :
    retained ∈
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference)
        (pairGraphCopyChildWords retained copy layer) := by
  intro pair
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) reference)
    ((pairLayerPairEquiv baseSize layer.val) pair)
  have hretained :=
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).property
  change
    (pairGraphCopyChildSide retained copy layer reference,
      pairGraphCopyChildWords retained copy layer pair) ∈ retained
  unfold pairGraphCopyChildSide pairGraphCopyChildWords
  rw [hside]
  exact hretained

theorem pairGraphCopy_parent_child_hammingDist_le
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (pair :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (parent :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 0)
    (hparent : parent ∈ pair.val) :
    hammingDist
      (pairGraphCopyParentWords retained copy layer parent)
      (pairGraphCopyChildWords retained copy layer pair) ≤ radius := by
  have hactualParent :
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        ((pairLayerPairEquiv baseSize layer.val) pair).val := by
    change
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        pair.val.map
          (pairLayerFinEquiv baseSize layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := pairGraph_parent_child_adj
    baseSize depth layer.val (by omega)
      ((pairLayerPairEquiv baseSize layer.val) pair)
      ((pairLayerFinEquiv baseSize layer.val).symm parent)
      hactualParent
  have hedge := copy.toHom.map_rel hsource
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) pair))).val
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          ((pairLayerFinEquiv baseSize layer.val).symm parent))).val at hedge
  have hdist :=
    ((hammingHost_adj_iff dimension radius _ _).mp hedge).2
  simpa [pairGraphCopyParentWords, pairGraphCopyChildWords,
    hammingDist_comm] using hdist

theorem pairGraphCopy_averageDisagreement_le_radius
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) := by
  apply pairChildArrayAverageDisagreement_le_radius
    (hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase))
    hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
    radius
  intro pair parent hparent
  exact pairGraphCopy_parent_child_hammingDist_le
    retained copy layer pair parent hparent

theorem pairGraphCopy_averageDisagreement_le_tau
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤ tau := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) :=
      pairGraphCopy_averageDisagreement_le_radius
        hbase hdimension retained copy layer
    _ ≤ tau :=
      (div_le_iff₀ hdimension_real).mpr hradius

theorem pairGraphCopy_entropy_lower_of_exclusion
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (threshold : ℝ)
    (hexclusion :
      retained ∉
        badPairLayerRetentionEvent
          (Fintype.card (PairLayer baseSize layer.val)) dimension
          (pairGraphCopyChildSide retained copy layer reference)
          threshold) :
    threshold <
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) := by
  classical
  by_contra hnot
  have hbad_entropy :
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ threshold :=
    le_of_not_gt hnot
  have hbad_array :
      pairGraphCopyChildWords retained copy layer ∈
        badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold := by
    unfold badPairChildArrays
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hbad_entropy⟩
  have hinjective :
      pairGraphCopyChildWords retained copy layer ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective :=
    Finset.mem_filter.mpr
      ⟨hbad_array,
        pairGraphCopyChildWords_injective retained copy layer⟩
  apply hexclusion
  change retained ∈
    ⋃ parents :
        Fin (Fintype.card (PairLayer baseSize layer.val)) →
          HammingWord dimension,
      badPairChildRetentionEvent parents
        (pairGraphCopyChildSide retained copy layer reference) threshold
  apply Set.mem_iUnion.mpr
  refine ⟨pairGraphCopyParentWords retained copy layer, ?_⟩
  change retained ∈
    ⋃ children ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective,
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference) children
  exact Set.mem_iUnion.mpr
    ⟨pairGraphCopyChildWords retained copy layer,
      Set.mem_iUnion.mpr
        ⟨hinjective,
          pairGraphCopyChildWords_retained
            retained copy layer reference⟩⟩

theorem pairGraph_free_of_layer_exclusion_and_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairParentSystem baseSize depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  let potential : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth + 1 then
      pairGraphCopyLayerPotential retained copy ⟨layer, hlevel⟩
    else 0
  let conditionalEntropy : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy ⟨layer, hlevel⟩)
        (pairGraphCopyChildWords retained copy ⟨layer, hlevel⟩)
    else 0
  let error : ℕ → ℝ := fun layer =>
    if hlevel : layer < depth then
      empiricalEntropyError
        (Fintype.card (PairLayer baseSize layer))
    else 0
  apply entropy_layer_exclusion depth
    potential conditionalEntropy error
  · intro layer hlayer
    have hinrange : layer < depth + 1 := by omega
    have hle : layer ≤ depth := by omega
    simpa [potential, hinrange, hle] using
      pairGraphCopyLayerPotential_mem_Icc
        hbase hdimension retained copy ⟨layer, hinrange⟩
  · intro layer hlayer
    simpa [error, hlayer] using
      herror ⟨layer, hlayer⟩
  · intro layer hlayer
    have hsize :
        2 ≤ Fintype.card (PairLayer baseSize layer) := by
      have hcard := pairLayer_card_ge_base
        baseSize layer hbase
      omega
    let reference :
        PairLayer (Fintype.card (PairLayer baseSize layer)) 1 :=
      Classical.choice (pairLayerPair_nonempty hsize)
    have hlower := pairGraphCopy_entropy_lower_of_exclusion
      retained copy ⟨layer, hlayer⟩ reference
        (midpointBeta - entropySlack)
        (hexclusion
          (pairGraphCopyChildSide
            retained copy ⟨layer, hlayer⟩ reference)
          ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, hlayer] using hlower
  · intro layer hlayer
    have hnext : layer + 1 < depth + 1 := by omega
    have hcurrent : layer < depth + 1 := by omega
    have hnext_le : layer + 1 ≤ depth := by omega
    have hcurrent_le : layer ≤ depth := by omega
    have hupper := pairGraphCopy_layer_entropy_upper_of_disagreement
      hbase hdimension retained copy ⟨layer, hlayer⟩
      (hdisagreement copy ⟨layer, hlayer⟩)
    simpa [conditionalEntropy, potential, error,
      hlayer, hnext, hcurrent, hnext_le, hcurrent_le] using hupper
  · exact hdepth

theorem pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  exact (SimpleGraph.free_congr_left
    (pairGraphOverFinIso baseSize depth)).mp
      (pairGraph_free_of_layer_exclusion_and_disagreement
        hbase hdimension hdepth retained hexclusion herror hdisagreement)

theorem pairGraphOverFin_free_of_layer_exclusion
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  apply pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    hbase hdimension hdepth retained hexclusion herror
  intro copy layer
  exact pairGraphCopy_averageDisagreement_le_tau
    hbase hdimension hradius retained copy layer

end HammingHostAndExclusion

section MainTheorem

noncomputable def manuscriptHammingRadius (dimension : ℕ) : ℕ :=
  ⌊tau * (dimension : ℝ)⌋₊

theorem manuscriptHammingRadius_le (dimension : ℕ) :
    (manuscriptHammingRadius dimension : ℝ) ≤
      tau * (dimension : ℝ) := by
  unfold manuscriptHammingRadius
  exact Nat.floor_le
    (mul_nonneg tau_pos.le (Nat.cast_nonneg dimension))

theorem manuscriptHammingRadius_le_dimension (dimension : ℕ) :
    manuscriptHammingRadius dimension ≤ dimension := by
  have hradius := manuscriptHammingRadius_le dimension
  have hdimension : 0 ≤ (dimension : ℝ) := Nat.cast_nonneg dimension
  have htau := tau_lt_one_half
  have hreal :
      (manuscriptHammingRadius dimension : ℝ) ≤ (dimension : ℝ) := by
    nlinarith
  exact_mod_cast hreal

theorem manuscriptHammingRadius_ratio_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        (manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 tau) := by
  unfold manuscriptHammingRadius
  exact
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) tau_pos.le).comp
      tendsto_natCast_atTop_atTop

theorem manuscriptHammingRadius_binEntropy_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ)))
      atTop (𝓝 (Real.binEntropy tau)) := by
  exact Real.binEntropy_continuous.continuousAt.tendsto.comp
    manuscriptHammingRadius_ratio_tendsto

theorem manuscriptHammingBall_card_entropy_lower
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
  calc
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      (dimension.choose (manuscriptHammingRadius dimension) : ℝ) :=
        exp_binary_entropy_div_le_choose dimension
          (manuscriptHammingRadius dimension)
          (manuscriptHammingRadius_le_dimension dimension)
    _ ≤ ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
      exact_mod_cast hammingBall_card_ge_boundary_binomial
        dimension (manuscriptHammingRadius dimension) word

theorem eventually_manuscriptHammingRadius_binEntropy_ge
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.binEntropy tau - loss ≤
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) /
            (dimension : ℝ)) := by
  have hneighborhood :
      Set.Ioi (Real.binEntropy tau - loss) ∈
        𝓝 (Real.binEntropy tau) :=
    Ioi_mem_nhds (by linarith)
  filter_upwards
    [manuscriptHammingRadius_binEntropy_tendsto hneighborhood]
    with dimension hdimension
  exact (show Real.binEntropy tau - loss <
    Real.binEntropy
      ((manuscriptHammingRadius dimension : ℝ) /
        (dimension : ℝ)) from hdimension).le

noncomputable def sampledHammingEdgeEntropyRate : ℝ :=
  (1 - 2 * midpointBeta) * Real.log 2 + Real.binEntropy tau

theorem sampledHammingEdgeEntropyRate_pos :
    0 < sampledHammingEdgeEntropyRate := by
  have hwindow := midpointBeta_lt_upper_unconditional
  unfold entropyUpperEndpoint at hwindow
  have hbeta := midpointBeta_lt_one
  have hbits : 0 < 1 - 2 * midpointBeta + binaryEntropy tau := by
    nlinarith
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  unfold sampledHammingEdgeEntropyRate
  rw [hentropy]
  nlinarith [mul_pos hbits log_two_pos]

theorem eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) := by
  filter_upwards
    [eventually_manuscriptHammingRadius_binEntropy_ge loss hloss]
    with dimension hentropy
  have hdegree :
      Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := manuscriptHammingBall_card_entropy_lower dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp
        ((dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - loss)) /
        ((dimension + 1 : ℕ) : ℝ) =
      (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) * (Real.binEntropy tau - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [hammingRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold sampledHammingEdgeEntropyRate
        ring_nf
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        gcongr
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
        gcongr
    _ = hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) := by
      rw [hammingExpectedRetainedEdgeCount_eq]

theorem manuscriptExpectedRetainedEdgeCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop atTop := by
  have hrate := sampledHammingEdgeEntropyRate_pos
  have hloss : 0 < sampledHammingEdgeEntropyRate / 2 := by
    positivity
  have hlower := eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop
    (sampledHammingEdgeEntropyRate / 2) hloss
  have hhalf :
      sampledHammingEdgeEntropyRate -
          sampledHammingEdgeEntropyRate / 2 =
        sampledHammingEdgeEntropyRate / 2 := by
    ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension

theorem manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    manuscriptExpectedRetainedEdgeCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

noncomputable def manuscriptSamplingFailureBound
    (depth dimension : ℕ) : ℝ :=
  (((2 * depth : ℕ) : ℝ)) *
      Real.exp (-(dimension : ℝ) * Real.log 2) +
    4 / hammingExpectedRetainedVertexCount dimension +
    (4 / hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) +
      8 / (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)))

theorem manuscriptSamplingFailureBound_tendsto_zero
    (depth : ℕ) :
    Tendsto
      (manuscriptSamplingFailureBound depth)
      atTop (𝓝 0) := by
  have hexclusion := pairLayerExclusionProbability_tendsto_zero depth
  have hvertices :=
    hammingExpectedRetainedVertexCount_inv_tendsto_zero.const_mul 4
  have hedges :=
    manuscriptExpectedRetainedEdgeCount_inv_tendsto_zero.const_mul 4
  have hwords :=
    hammingRetentionProbability_mul_wordCount_inv_tendsto_zero.const_mul 8
  have htotal := (hexclusion.add hvertices).add (hedges.add hwords)
  have htotal_zero :
      Tendsto
        (fun dimension : ℕ =>
          (((2 * depth : ℕ) : ℝ)) *
              Real.exp (-(dimension : ℝ) * Real.log 2) +
            4 * (1 / hammingExpectedRetainedVertexCount dimension) +
            (4 * (1 / hammingExpectedRetainedEdgeCount dimension
                (manuscriptHammingRadius dimension)) +
              8 * (1 / (hammingRetentionProbability dimension *
                ((2 ^ dimension : ℕ) : ℝ)))))
        atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using htotal
  apply htotal_zero.congr'
  filter_upwards [] with dimension
  unfold manuscriptSamplingFailureBound
  push_cast
  simp only [div_eq_mul_inv]
  ring

noncomputable def manuscriptSamplingFailureEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  (badPairLayersRetentionEvent layerSizes dimension ∪
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}) ∪
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}

theorem manuscriptSamplingFailureEvent_real_le
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
      (manuscriptSamplingFailureEvent layerSizes dimension) ≤
        manuscriptSamplingFailureBound depth dimension := by
  let vertexFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}
  let edgeFailure : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}
  change
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
        manuscriptSamplingFailureBound depth dimension
  calc
    (hammingRetentionMeasure dimension).real
      ((badPairLayersRetentionEvent layerSizes dimension ∪
        vertexFailure) ∪ edgeFailure) ≤
      ((hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) +
       (hammingRetentionMeasure dimension).real vertexFailure) +
        (hammingRetentionMeasure dimension).real edgeFailure := by
      calc
        (hammingRetentionMeasure dimension).real
          ((badPairLayersRetentionEvent layerSizes dimension ∪
            vertexFailure) ∪ edgeFailure) ≤
          (hammingRetentionMeasure dimension).real
            (badPairLayersRetentionEvent layerSizes dimension ∪
              vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure :=
              MeasureTheory.measureReal_union_le _ _
        _ ≤ ((hammingRetentionMeasure dimension).real
              (badPairLayersRetentionEvent layerSizes dimension) +
            (hammingRetentionMeasure dimension).real vertexFailure) +
            (hammingRetentionMeasure dimension).real edgeFailure := by
              gcongr
              exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / hammingExpectedRetainedVertexCount dimension) +
        (4 / hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) +
          8 / (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ))) := by
      gcongr
      · exact badPairLayersRetentionEvent_real_le
          layerSizes hdimension hparents hbase
      · exact hammingRetainedVertexCount_upper_tail_probability_le dimension
      · exact hammingRetainedEdgeCount_lower_tail_probability_le
          dimension (manuscriptHammingRadius dimension)
    _ = manuscriptSamplingFailureBound depth dimension := by
      rfl

theorem pairGraphOverFin_free_of_manuscript_exclusion
    {baseSize depth dimension : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained) := by
  exact pairGraphOverFin_free_of_layer_exclusion
    hbase hdimension hdepth
    (manuscriptHammingRadius_le dimension)
    retained hexclusion herror

theorem eventually_exists_pairGraph_free_dense_retainedHost :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (pairGraphOverFin baseSize depth).Free
              (retainedHammingHost dimension
                (manuscriptHammingRadius dimension) retained) ∧
          hammingRetainedVertexCount dimension retained <
            3 * hammingRetentionProbability dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          hammingExpectedRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) / 2 ≤
            hammingRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) retained := by
  obtain ⟨baseSize, depth, hbase, hdepth, hdepth_window, hlayers⟩ :=
    exists_actualPairLayer_exclusion_parameters
  let layerSizes : Fin depth → ℕ := fun layer =>
    Fintype.card (PairLayer baseSize layer.val)
  have hparents : ∀ layer, 4 ≤ layerSizes layer :=
    fun layer => (hlayers layer).1
  have hfirst_moment :
      ∀ layer,
        (layerSizes layer : ℝ) +
          3 * logTwo
            (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
            entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1 :=
    fun layer => (hlayers layer).2.2
  have hsmall :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        manuscriptSamplingFailureBound depth dimension < 1 :=
    (tendsto_order.1
      (manuscriptSamplingFailureBound_tendsto_zero depth)).2
        1 (by norm_num)
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hsmall, Filter.eventually_gt_atTop 0] with dimension
    hbound hdimension
  obtain ⟨retained, houtside⟩ :=
    exists_hammingRetention_outside_event dimension
      (manuscriptSamplingFailureEvent layerSizes dimension)
      ((manuscriptSamplingFailureEvent_real_le layerSizes
        hdimension hparents hfirst_moment).trans_lt hbound)
  have hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (layerSizes layer) dimension side
              (midpointBeta - entropySlack) := by
    intro side layer hbad
    exact houtside (Or.inl (Or.inl (Set.mem_iUnion.mpr
      ⟨side, Set.mem_iUnion.mpr ⟨layer, hbad⟩⟩)))
  have hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) :=
    lt_of_not_ge fun hlarge => houtside (Or.inl (Or.inr hlarge))
  have hedges :
      hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 ≤
        hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained :=
    le_of_not_gt fun hlow => houtside (Or.inr hlow)
  exact ⟨retained,
    pairGraphOverFin_free_of_manuscript_exclusion
      hbase hdimension hdepth_window retained hexclusion
      (fun layer => (hlayers layer).2.1),
    hvertices, hedges⟩

theorem baseSize_le_pairVertex_card
    (baseSize depth : ℕ) :
    baseSize ≤ Fintype.card (PairVertex baseSize depth) := by
  calc
    baseSize = Fintype.card (PairLayer baseSize 0) :=
      (pairLayer_card_zero baseSize).symm
    _ ≤ Fintype.card (PairVertex baseSize depth) :=
      Fintype.card_le_of_embedding
        (pairLayerEmbedding baseSize depth 0 (by omega))

theorem pairGraphOverFin_forall_exists_adj
    (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize)
    (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
      ∃ neighbor,
        (pairGraphOverFin baseSize depth).Adj vertex neighbor := by
  have hcard : 2 ≤ Fintype.card (PairVertex baseSize depth) := by
    have hcard_base := baseSize_le_pairVertex_card baseSize depth
    omega
  letI : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) :=
    Fin.nontrivial_iff_two_le.mpr hcard
  intro vertex
  exact
    (pairGraphOverFin_connected baseSize depth (by omega) hdepth).preconnected
      |>.exists_adj_of_nontrivial vertex

noncomputable def manuscriptVertexCount (dimension : ℕ) : ℕ :=
  ⌈3 * hammingRetentionProbability dimension *
    ((2 ^ dimension : ℕ) : ℝ)⌉₊

open Classical in
theorem retainedVertex_card_le_manuscriptVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ manuscriptVertexCount dimension := by
  have hreal :
      (Fintype.card retained : ℝ) ≤
        (manuscriptVertexCount dimension : ℝ) := by
    calc
      (Fintype.card retained : ℝ) =
          hammingRetainedVertexCount dimension retained :=
        (hammingRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ = (manuscriptVertexCount dimension : ℝ) := rfl
  exact_mod_cast hreal

open Classical in
theorem eventually_expectedRetainedEdge_le_extremalNumber :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) / 2 ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hhosts⟩ :=
    eventually_exists_pairGraph_free_dense_retainedHost
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard :=
    retainedVertex_card_le_manuscriptVertexCount
      dimension retained hvertices
  have hembedding :
      Nonempty (retained ↪ Fin (manuscriptVertexCount dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (manuscriptVertexCount dimension)) :=
    (retainedHammingHost dimension
      (manuscriptHammingRadius dimension) retained).map embedding
  have hpadded_free :
      (pairGraphOverFin baseSize depth).Free paddedHost := by
    exact CompactnessConjecture.free_map_of_no_isolated
      (pairGraphOverFin baseSize depth)
      (pairGraphOverFin_forall_exists_adj baseSize depth hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber
          (manuscriptVertexCount dimension)
          (pairGraphOverFin baseSize depth) := by
    simpa using
      (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) / 2 ≤
      hammingRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) retained := hedges
    _ = ((retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card
        dimension (manuscriptHammingRadius dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension
          (manuscriptHammingRadius dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber
        (manuscriptVertexCount dimension)
        (pairGraphOverFin baseSize depth) : ℝ) := by
      exact_mod_cast hpadded_edges

noncomputable def manuscriptExtremalPower : ℝ :=
  (3 : ℝ) / 2 + exponentGain

theorem manuscriptExtremalPower_pos :
    0 < manuscriptExtremalPower := by
  unfold manuscriptExtremalPower
  linarith [exponentGain_pos]

noncomputable def manuscriptEntropyGap : ℝ :=
  certifiedWindowWidth * Real.log 2 / 16

theorem manuscriptEntropyGap_pos : 0 < manuscriptEntropyGap := by
  unfold manuscriptEntropyGap
  positivity [certifiedWindowWidth_pos, log_two_pos]

theorem sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower :
    sampledHammingEdgeEntropyRate =
      (1 - midpointBeta) * manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
  have hmidpoint :
      entropyUpperEndpoint - midpointBeta =
        certifiedWindowWidth / 2 := by
    have hwindow := entropyWindow_eq_certifiedWindowWidth
    unfold midpointBeta
    linarith
  have hupper :
      binaryEntropy tau = (entropyUpperEndpoint + 1) / 2 := by
    unfold entropyUpperEndpoint
    ring
  have hgain :
      (1 - midpointBeta) * exponentGain =
        certifiedWindowWidth / 8 := by
    have hnonzero : 1 - midpointBeta ≠ 0 :=
      (sub_pos.mpr midpointBeta_lt_one).ne'
    unfold exponentGain
    field_simp [hnonzero]
  have hbits :
      1 - 2 * midpointBeta + binaryEntropy tau =
        (1 - midpointBeta) *
            ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8 := by
    nlinarith [hmidpoint, hupper, hgain]
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  calc
    sampledHammingEdgeEntropyRate =
        (1 - 2 * midpointBeta + binaryEntropy tau) *
          Real.log 2 := by
      unfold sampledHammingEdgeEntropyRate
      rw [hentropy]
      ring
    _ = ((1 - midpointBeta) *
          ((3 : ℝ) / 2 + exponentGain) +
          certifiedWindowWidth / 8) * Real.log 2 := by
      rw [hbits]
    _ = (1 - midpointBeta) *
          manuscriptExtremalPower * Real.log 2 +
        2 * manuscriptEntropyGap := by
      unfold manuscriptExtremalPower manuscriptEntropyGap
      ring

theorem manuscriptVertexCount_le_four_wordMean
    (dimension : ℕ)
    (hmean :
      1 ≤ hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) :
    (manuscriptVertexCount dimension : ℝ) ≤
      4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hargument :
      0 ≤ 3 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
    positivity [hammingRetentionProbability_pos dimension]
  have hceiling :
      (manuscriptVertexCount dimension : ℝ) <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold manuscriptVertexCount
    exact Nat.ceil_lt_add_one hargument
  nlinarith

theorem eventually_manuscriptVertexCount_le_four_wordMean :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ≤
        4 * (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    hammingRetentionProbability_mul_wordCount_tendsto_atTop (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact manuscriptVertexCount_le_four_wordMean dimension hdimension

theorem eventually_manuscriptEntropyGap_dominates_power_constant :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      2 * (4 : ℝ) ^ manuscriptExtremalPower ≤
        Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ) := by
  exact Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop
      manuscriptEntropyGap manuscriptEntropyGap_pos)
    (2 * (4 : ℝ) ^ manuscriptExtremalPower)

theorem eventually_manuscriptVertexCount_power_le_expectedRetainedEdge :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ^
          manuscriptExtremalPower ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
  have hlower :=
    eventually_manuscriptExpectedRetainedEdge_entropy_lower
      manuscriptEntropyGap manuscriptEntropyGap_pos
  have hvertex :=
    eventually_manuscriptVertexCount_le_four_wordMean
  have hconstant :=
    eventually_manuscriptEntropyGap_dominates_power_constant
  filter_upwards [hlower, hvertex, hconstant] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hconstant_half :
      (4 : ℝ) ^ manuscriptExtremalPower ≤
        (Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
    linarith
  have hexponent :
      ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower +
          manuscriptEntropyGap * (dimension : ℝ) =
        (dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - manuscriptEntropyGap) := by
    rw [sampledHammingEdgeEntropyRate_eq_manuscriptExtremalPower]
    ring
  calc
    (manuscriptVertexCount dimension : ℝ) ^
        manuscriptExtremalPower ≤
      (4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^
          manuscriptExtremalPower := by
        apply Real.rpow_le_rpow
        · positivity
        · exact hvertex_bound
        · exact manuscriptExtremalPower_pos.le
    _ = (4 : ℝ) ^ manuscriptExtremalPower *
        Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) := by
      rw [hammingRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le,
        ← Real.exp_mul]
    _ ≤ Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
            manuscriptExtremalPower) *
        ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      calc
        (4 : ℝ) ^ manuscriptExtremalPower *
            Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) =
          Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            (4 : ℝ) ^ manuscriptExtremalPower := by ring
        _ ≤ Real.exp
              (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
                manuscriptExtremalPower) *
            ((Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
              ((dimension + 1 : ℕ) : ℝ)) / 2) :=
          mul_le_mul_of_nonneg_left hconstant_half
            (Real.exp_pos _).le
    _ = (Real.exp
          (((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) *
              manuscriptExtremalPower +
            manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]
      ring
    _ = (Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - manuscriptEntropyGap)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [hexponent]
    _ ≤ hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2 := by
      gcongr

theorem eventually_manuscriptVertexCount_power_le_extremalNumber :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hextremal⟩ :=
    eventually_expectedRetainedEdge_le_extremalNumber
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards
    [eventually_manuscriptVertexCount_power_le_expectedRetainedEdge,
      hextremal] with dimension hpower hbound
  exact hpower.trans hbound

theorem manuscriptVertexCount_tendsto_atTop :
    Filter.Tendsto manuscriptVertexCount Filter.atTop Filter.atTop := by
  have hscaled :
      Filter.Tendsto
        (fun dimension : ℕ =>
          3 * (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change
    ⌈3 * (hammingRetentionProbability dimension *
      ((2 ^ dimension : ℕ) : ℝ))⌉₊ =
      manuscriptVertexCount dimension
  unfold manuscriptVertexCount
  congr 1
  ring

theorem manuscriptVertexCount_succ_le_two_mul
    (dimension : ℕ) :
    manuscriptVertexCount (dimension + 1) ≤
      2 * manuscriptVertexCount dimension := by
  have hfactor :
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤ (2 : ℝ) := by
    calc
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤
          Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_pos midpointBeta_pos log_two_pos]
      _ = 2 := Real.exp_log (by norm_num)
  have hrecurrence :
      hammingRetentionProbability (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - midpointBeta) * Real.log 2) *
          (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [hammingRetentionProbability_mul_wordCount_eq_exp,
      hammingRetentionProbability_mul_wordCount_eq_exp,
      ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold manuscriptVertexCount
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * hammingRetentionProbability (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - midpointBeta) * Real.log 2) *
        (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show
          3 * hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring,
          hrecurrence]
        ring
    _ ≤ 2 * (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfactor (by
          positivity [hammingRetentionProbability_pos dimension])
    _ ≤ 2 *
          (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _

theorem exists_manuscriptVertexCount_bracket
    (minimum n : ℕ)
    (hminimum : manuscriptVertexCount minimum ≤ n) :
    ∃ dimension : ℕ,
      minimum ≤ dimension ∧
      manuscriptVertexCount dimension ≤ n ∧
      n < manuscriptVertexCount (dimension + 1) := by
  have hlarge :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        n < manuscriptVertexCount dimension := by
    have hevent := Filter.tendsto_atTop.1
      manuscriptVertexCount_tendsto_atTop (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists :
      ∃ offset : ℕ,
        n < manuscriptVertexCount (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext :
      n < manuscriptVertexCount (minimum + offset) :=
    Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · have hbefore :
        ¬ n < manuscriptVertexCount (minimum + (offset - 1)) := by
      exact Nat.find_min hexists (by omega)
    exact Nat.le_of_not_gt hbefore
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext

open Classical in
theorem twoDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsTwoDegenerate H ∧
      (∀ coloring : H.Coloring (Fin 2), ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin q => coloring vertex = side)).sup
          (fun vertex => H.degree vertex)) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hsubsequence⟩ :=
    eventually_manuscriptVertexCount_power_le_extremalNumber
  have hwidth : certifiedWindowWidth < 1 := by
    rw [← entropyWindow_eq_certifiedWindowWidth]
    linarith [entropyLowerEndpoint_pos, entropyUpperEndpoint_lt_one]
  have hproduct :
      0 ≤ (depth : ℝ) * (1 - certifiedWindowWidth) :=
    mul_nonneg (Nat.cast_nonneg depth) (sub_nonneg.mpr hwidth.le)
  have hdepth_real : (2 : ℝ) < (depth : ℝ) := by
    nlinarith
  have hdepth_nat : 2 < depth := by
    exact_mod_cast hdepth_real
  have hdepth_two : 2 ≤ depth := by
    omega
  let forbidden :
      SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
    pairGraphOverFin baseSize depth
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor := by
    exact pairGraphOverFin_forall_exists_adj
      baseSize depth hbase hdepth
  refine ⟨Fintype.card (PairVertex baseSize depth), forbidden,
    pairGraphOverFin_connected baseSize depth (by omega) hdepth,
    pairGraphOverFin_isBipartite baseSize depth,
    pairGraphOverFin_isTwoDegenerate baseSize depth,
    ?_,
    1 / (2 : ℝ) ^ manuscriptExtremalPower,
    exponentGain, ?_, exponentGain_pos, ?_⟩
  · simpa only [forbidden] using
      pairGraphOverFin_bipartition_maximum_degree_gt_two
        baseSize depth hbase hdepth_two
  · exact one_div_pos.mpr
      (Real.rpow_pos_of_pos (by norm_num) manuscriptExtremalPower)
  · obtain ⟨minimum, hminimum⟩ :=
      Filter.eventually_atTop.1 hsubsequence
    apply Filter.eventually_atTop.2
    refine ⟨manuscriptVertexCount minimum, ?_⟩
    intro n hn
    obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
      exists_manuscriptVertexCount_bracket minimum n hn
    have hdouble :=
      manuscriptVertexCount_succ_le_two_mul dimension
    have hn_bound :
        n ≤ 2 * manuscriptVertexCount dimension := by
      omega
    have hn_real :
        (n : ℝ) ≤
          2 * (manuscriptVertexCount dimension : ℝ) := by
      exact_mod_cast hn_bound
    have hsubseq := hminimum dimension hdimension
    have hmonotone :
        SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden ≤
          SimpleGraph.extremalNumber n forbidden :=
      CompactnessConjecture.extremalNumber_monotone_of_no_isolated
        forbidden hnoisolated hbelow
    change
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ)
    calc
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (2 * (manuscriptVertexCount dimension : ℝ)) ^
            manuscriptExtremalPower := by
          apply mul_le_mul_of_nonneg_left
          · exact Real.rpow_le_rpow
              (Nat.cast_nonneg n) hn_real
              manuscriptExtremalPower_pos.le
          · positivity
      _ = (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower := by
          rw [Real.mul_rpow (by norm_num)
            (Nat.cast_nonneg (manuscriptVertexCount dimension))]
          have htwo :
              (2 : ℝ) ^ manuscriptExtremalPower ≠ 0 :=
            (Real.rpow_pos_of_pos (by norm_num)
              manuscriptExtremalPower).ne'
          field_simp [htwo]
      _ ≤ (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden : ℝ) :=
          hsubseq
      _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by
          exact_mod_cast hmonotone

theorem not_erdos_146 :
    ¬ DegeneracyConjectureStatement := by
  intro hconjecture
  obtain ⟨q, H, _hconnected, hbipartite, hdegenerate, _hdegree,
    c, ε, hc, hε, hlower⟩ := twoDegenerateExtremalCounterexample
  have hbigO := hconjecture 2 q H (by norm_num)
    hbipartite hdegenerate
  obtain ⟨C, hupper⟩ := Asymptotics.isBigO_iff.mp hbigO
  have hupper' :
      ∀ᶠ n : ℕ in Filter.atTop,
        (SimpleGraph.extremalNumber n H : ℝ) ≤
          C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
    filter_upwards [hupper] with n hn
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hextremal_nonneg :
        (0 : ℝ) ≤ (SimpleGraph.extremalNumber n H : ℝ) :=
      Nat.cast_nonneg _
    have hnormalized :
        (SimpleGraph.extremalNumber n H : ℝ) ≤
          C * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
        abs_of_nonneg (Real.rpow_nonneg hnnonneg _), Nat.cast_ofNat] using hn
    convert hnormalized using 1
    norm_num
  have hlarge :=
    CompactnessConjecture.eventually_constant_le_positive_nat_rpow
      (C + 1) c ε hc hε
  have himpossible : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hlower, hupper', hlarge,
      Filter.eventually_gt_atTop 0] with n hlow hupp hlarge_n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hscale : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hnreal _
    have hdecompose :
        c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) =
          (c * (n : ℝ) ^ ε) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Real.rpow_add hnreal]
      ring
    rw [hdecompose] at hlow
    have hscaled := mul_le_mul_of_nonneg_right hlarge_n hscale.le
    nlinarith
  exact himpossible.exists.elim (fun _ h => h)

end MainTheorem

end TwoDegenerateGraphs


namespace CompactnessConjecture

open Filter Finset SimpleGraph

/-- The published quantitative counterexample directly implies the
corrected negative answer used by the Erdős 575 canonical verifier. -/
theorem erdos575BipartiteCompactness :
    ∃ family : Finset FiniteGraph,
      family.Nonempty ∧
      (∃ forbidden ∈ family, forbidden.graph.IsBipartite) ∧
      ¬ ∃ forbidden ∈ family, forbidden.graph.IsBipartite ∧
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
          (extremalNumber n forbidden.graph : ℝ) ≤
            C * (familyExtremal family n : ℝ) := by
  obtain ⟨family, c, C, hfamily, hall, hc, hC, hlower, hhost,
    hfamilyUpper, hgap, hexponent, hnotCompact, hnotStatement⟩ :=
    quantitativeCompactnessCounterexample
  refine ⟨family, hfamily, ?_, ?_⟩
  · obtain ⟨forbidden, hforbidden⟩ := hfamily
    exact ⟨forbidden, hforbidden, (hall forbidden hforbidden).2.1⟩
  · rintro ⟨forbidden, hforbidden, hbipartite, C', hC', hbound⟩
    exact hnotCompact ⟨forbidden, hforbidden, C', hC', hbound⟩

end CompactnessConjecture

namespace Submissions.Erdos575BipartiteCompactness.Published

open Filter SimpleGraph
open CompactnessConjecture

theorem proof :
    ∃ family : Finset FiniteGraph,
      family.Nonempty ∧
      (∃ forbidden ∈ family, forbidden.graph.IsBipartite) ∧
      ¬ ∃ forbidden ∈ family, forbidden.graph.IsBipartite ∧
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
          (extremalNumber n forbidden.graph : ℝ) ≤
            C * (familyExtremal family n : ℝ) :=
  erdos575BipartiteCompactness

end Submissions.Erdos575BipartiteCompactness.Published
