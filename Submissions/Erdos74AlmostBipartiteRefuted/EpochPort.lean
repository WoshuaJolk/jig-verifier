import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Attribution and verification scope

The mathematical refutation and the main proof body below were produced by
GPT-6 Astra in Epoch AI's FrontierMath Erdős experiments and publicly released
by Epoch AI. This file ports that existing proof to Jig's pinned Mathlib and
adds exact equivalence lemmas for Jig problem 31's canonical definitions.
It does not claim a new solution to Erdős problem 74.

Original published proof:
https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/erdos-ultima-alpha-1000usd-t4aijzkukl7718bm-reruns/Erdos74.erdos_74/Submission/Spec.lean

Announcement and mathematical summary:
https://epoch.ai/latest/announcing-frontiermath-erdos
https://epoch.ai/files/frontiermath-erdos.pdf (Appendix B.2)

The original result was checked under Lean 4.27.0 by SafeVerify. The separate
scores.json returned proof_scorer.value = C. Local port verification is reported
separately, after compiling with Lean 4.33.0 and Jig's pinned Mathlib.
-/

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

lemma delete_all_bipartite {G : SimpleGraph V} (A : G.Subgraph) :
    (A.deleteEdges A.edgeSet).coe.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) ?_⟩
  intro v w h
  exact False.elim (h.2 h.1)

lemma edgeDistances_nonempty {G : SimpleGraph V} (A : G.Subgraph) :
    (SimpleGraph.edgeDistancesToBipartite A).Nonempty :=
  ⟨A.edgeSet.ncard, A.edgeSet, Set.Subset.rfl, delete_all_bipartite A, rfl⟩

lemma minEdgeDist_mem {G : SimpleGraph V} (A : G.Subgraph) :
    (SimpleGraph.minEdgeDistToBipartite A) ∈ (SimpleGraph.edgeDistancesToBipartite A) :=
  Nat.sInf_mem (edgeDistances_nonempty A)

lemma minEdgeDist_le {G : SimpleGraph V} (A : G.Subgraph) {E : Set (Sym2 V)}
    (hE : E ⊆ A.edgeSet) (hB : (A.deleteEdges E).coe.IsBipartite) :
    (SimpleGraph.minEdgeDistToBipartite A) ≤ E.ncard :=
  Nat.sInf_le ⟨E, hE, hB, rfl⟩

lemma finite_edges {G : SimpleGraph V} (A : G.Subgraph) (h : A.verts.Finite) :
    A.edgeSet.Finite := by
  letI := h.fintype
  rw [← A.image_coe_edgeSet_coe]
  exact (Set.toFinite _).image _

lemma minEdgeDist_le_vertices {G : SimpleGraph V} (A : G.Subgraph)
    (h : A.verts.Finite) : (SimpleGraph.minEdgeDistToBipartite A) ≤ (A.verts.ncard + 1).choose 2 := by
  classical
  letI := h.fintype
  apply (minEdgeDist_le A Set.Subset.rfl (delete_all_bipartite A)).trans
  rw [← A.image_coe_edgeSet_coe]
  apply (Set.ncard_image_le (Set.toFinite _)).trans
  apply (Set.ncard_le_card _).trans_eq
  simp only [Nat.card_eq_fintype_card, Sym2.card, Set.ncard, Set.encard, ENat.card_eq_coe_fintype_card, ENat.toNat_coe]

lemma distances_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (G.subgraphEdgeDistsToBipartite n) := by
  refine ⟨(n + 1).choose 2, ?_⟩
  rintro k ⟨A, hcard, hfinite, rfl⟩
  simpa [hcard] using minEdgeDist_le_vertices A hfinite

lemma minEdgeDist_le_max (G : SimpleGraph V) (A : G.Subgraph)
    (h : A.verts.Finite) :
    (SimpleGraph.minEdgeDistToBipartite A) ≤ G.maxSubgraphEdgeDistToBipartite A.verts.ncard :=
  le_csSup (distances_bddAbove G _) ⟨A, rfl, h, rfl⟩

lemma colorable_of_finite_induced (G : SimpleGraph V) (n : ℕ) (hn : 0 < n)
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable n) : G.Colorable n := by
  classical
  letI : TopologicalSpace (Fin n) := ⊥
  letI : DiscreteTopology (Fin n) := ⟨rfl⟩
  letI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
  let t : V × V → Set (V → Fin n) := fun e =>
    {c | G.Adj e.1 e.2 → c e.1 ≠ c e.2}
  have ht : ∀ e, IsClosed (t e) := by
    intro ⟨v, w⟩
    by_cases hvw : G.Adj v w
    · have hp : Continuous (fun c : V → Fin n => (c v, c w)) :=
        (continuous_apply v).prodMk (continuous_apply w)
      have hc := (isClosed_discrete {p : Fin n × Fin n | p.1 ≠ p.2}).preimage hp
      simpa [t, hvw] using hc
    · simpa [t, hvw] using (isClosed_univ : IsClosed (Set.univ : Set (V → Fin n)))
  have htfin : ∀ es : Finset (V × V), (⋂ e ∈ es, t e).Nonempty := by
    intro es
    let s : Finset V := es.image Prod.fst ∪ es.image Prod.snd
    obtain ⟨c⟩ := h s
    let c' : V → Fin n := fun v => if hv : v ∈ s then c ⟨v, hv⟩ else default
    refine ⟨c', ?_⟩
    simp only [Set.mem_iInter]
    intro e he
    have hv : e.1 ∈ s := Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
    have hw : e.2 ∈ s := Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    intro hadj
    simpa only [c', dif_pos hv, dif_pos hw] using
      (c.valid (show (G.induce (s : Set V)).Adj ⟨e.1, hv⟩ ⟨e.2, hw⟩ from hadj))
  obtain ⟨c, hc⟩ := CompactSpace.iInter_nonempty ht htfin
  exact ⟨SimpleGraph.Coloring.mk c fun {v w} hvw => (Set.mem_iInter.mp hc (v, w)) hvw⟩

lemma minEdgeDist_le_map {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G →g H) (hφ : Function.Injective φ) (A : G.Subgraph)
    (hA : A.verts.Finite) :
    SimpleGraph.minEdgeDistToBipartite A ≤
      SimpleGraph.minEdgeDistToBipartite (A.map φ) := by
  obtain ⟨E, hE, ⟨c⟩, hcard⟩ := minEdgeDist_mem (A.map φ)
  have hEf : E.Finite := (finite_edges (A.map φ) (hA.image φ)).subset hE
  let E' : Set (Sym2 V) := Sym2.map φ ⁻¹' E
  have hinj : Function.Injective (Sym2.map φ) := Sym2.map.injective hφ
  have hE' : E' ⊆ A.edgeSet := by
    intro e he
    have hm := hE he
    rw [Subgraph.edgeSet_map] at hm
    obtain ⟨e', he', heq⟩ := hm
    exact hinj heq ▸ he'
  have hcol : (A.deleteEdges E').coe.IsBipartite := by
    refine ⟨SimpleGraph.Coloring.mk (fun v => c ⟨φ v.val, ⟨v.val, v.property, rfl⟩⟩) ?_⟩
    intro v w hadj
    apply c.valid
    change (A.map φ).Adj (φ v.val) (φ w.val) ∧ s(φ v.val, φ w.val) ∉ E
    exact ⟨⟨v.val, w.val, hadj.1, rfl, rfl⟩, hadj.2⟩
  have hcard' : E'.ncard ≤ E.ncard := by
    apply Set.ncard_le_ncard_of_injOn (Sym2.map φ) (ht := hEf)
    · exact fun _ he => he
    · exact hinj.injOn
  exact (minEdgeDist_le A hE' hcol).trans (hcard'.trans_eq hcard)

lemma maxEdgeDist_le_of_injective_hom {W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G →g H) (hφ : Function.Injective φ) (n : ℕ) :
    G.maxSubgraphEdgeDistToBipartite n ≤ H.maxSubgraphEdgeDistToBipartite n := by
  apply csSup_le'
  rintro k ⟨A, hcard, hfinite, rfl⟩
  have hm := minEdgeDist_le_max H (A.map φ) (hfinite.image φ)
  have hn : (A.map φ).verts.ncard = n := by
    rw [Subgraph.map_verts, Set.ncard_image_of_injective _ hφ, hcard]
  exact (minEdgeDist_le_map φ hφ A hfinite).trans (hn ▸ hm)

lemma maxEdgeDist_induce_le (G : SimpleGraph V) (S : Set V) (n : ℕ) :
    (G.induce S).maxSubgraphEdgeDistToBipartite n ≤
      G.maxSubgraphEdgeDistToBipartite n :=
  maxEdgeDist_le_of_injective_hom (Embedding.induce S).toHom Subtype.val_injective n

def cutBadEdges {G : SimpleGraph V} (A : G.Subgraph) (c : V → Fin 2) : Set (Sym2 V) :=
  {e | e ∈ A.edgeSet ∧ (Sym2.map c e).IsDiag}

@[simp] lemma mem_cutBadEdges {G : SimpleGraph V} (A : G.Subgraph) (c : V → Fin 2)
    (v w : V) : s(v, w) ∈ cutBadEdges A c ↔ A.Adj v w ∧ c v = c w := by
  simp [cutBadEdges]

lemma cutBadEdges_subset {G : SimpleGraph V} (A : G.Subgraph) (c : V → Fin 2) :
    cutBadEdges A c ⊆ A.edgeSet := fun _ h => h.1

lemma cutBadEdges_bipartite {G : SimpleGraph V} (A : G.Subgraph) (c : V → Fin 2) :
    (A.deleteEdges (cutBadEdges A c)).coe.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => c v.val) ?_⟩
  intro v w hadj heq
  exact hadj.2 ((mem_cutBadEdges A c _ _).mpr ⟨hadj.1, heq⟩)

lemma minEdgeDist_le_cutBadEdges {G : SimpleGraph V} (A : G.Subgraph) (c : V → Fin 2) :
    SimpleGraph.minEdgeDistToBipartite A ≤ (cutBadEdges A c).ncard :=
  minEdgeDist_le A (cutBadEdges_subset A c) (cutBadEdges_bipartite A c)

lemma exists_optimal_cut {G : SimpleGraph V} (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ c : V → Fin 2, (cutBadEdges A c).ncard = SimpleGraph.minEdgeDistToBipartite A := by
  classical
  obtain ⟨E, hE, ⟨b⟩, hcard⟩ := minEdgeDist_mem A
  let c : V → Fin 2 := fun v => if hv : v ∈ A.verts then b ⟨v, hv⟩ else 0
  have hbad : cutBadEdges A c ⊆ E := by
    intro e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨hvw, hc⟩ := (mem_cutBadEdges A c v w).mp he
      have hv := A.edge_vert hvw
      have hw := A.edge_vert hvw.symm
      by_contra hn
      have hb := b.valid (show (A.deleteEdges E).coe.Adj ⟨v, hv⟩ ⟨w, hw⟩ from ⟨hvw, hn⟩)
      exact hb (by simpa only [c, dif_pos hv, dif_pos hw] using hc)
  refine ⟨c, le_antisymm ?_ (minEdgeDist_le_cutBadEdges A c)⟩
  exact (Set.ncard_le_ncard hbad ((finite_edges A hA).subset hE)).trans_eq hcard

lemma diagonal_rate (N D : ℕ → ℕ) (hD : Tendsto D atTop atTop)
    (hpos : ∀ i, 0 < D i) :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      ∀ i, f (N i) < D i := by
  classical
  let S : ℕ → Set ℕ := fun n => insert n {d | ∃ i, n ≤ N i ∧ d = D i - 1}
  have hS : ∀ n, (S n).Nonempty := fun n => ⟨n, Set.mem_insert _ _⟩
  let f : ℕ → ℕ := fun n => sInf (S n)
  have hle : ∀ n, f n ≤ n := fun n => Nat.sInf_le (Set.mem_insert _ _)
  have hdiag : ∀ i, f (N i) < D i := by
    intro i
    have hi : f (N i) ≤ D i - 1 :=
      Nat.sInf_le (Set.mem_insert_of_mem _ ⟨i, le_rfl, rfl⟩)
    have := hpos i
    omega
  have hmono : Monotone f := by
    intro n m hnm
    apply le_csInf (hS m)
    intro d hd
    rcases hd with rfl | ⟨i, hi, rfl⟩
    · exact (hle n).trans hnm
    · exact Nat.sInf_le (Set.mem_insert_of_mem _ ⟨i, hnm.trans hi, rfl⟩)
  refine ⟨f, hmono, ?_, hdiag⟩
  apply tendsto_atTop.mpr
  intro k
  obtain ⟨I, hI⟩ := eventually_atTop.mp ((tendsto_atTop.mp hD) (k+1))
  let B := (Finset.range I).sup N
  filter_upwards [eventually_ge_atTop (max k (B+1))] with n hn
  apply le_csInf (hS n)
  intro d hd
  rcases hd with rfl | ⟨i, hi, rfl⟩
  · exact (le_max_left _ _).trans hn
  · have hii : I ≤ i := by
      by_contra h
      have himem : i ∈ Finset.range I := Finset.mem_range.mpr (by omega)
      have hNi : N i ≤ B := Finset.le_sup himem
      have hBn : B+1 ≤ n := (le_max_right _ _).trans hn
      omega
    have := hI i hii
    omega

end Erdos74

/-
Proof outline. For each D, `finite_distance_witness` gives a uniform bound N(D)
such that every finite non-three-colorable graph of bipartization distance at
most D contains a subgraph of distance at least d > 0 on at most N(d) vertices.
The induction either extracts a full-distance witness from a bounded-radius
ball, or compresses a plateau between two balls to a graph of smaller distance.
A two-apex closure preserves non-three-colorability through a three-layer
coloring buffer, and an empty level transfers its small witnesses back.
The bounded-radius extraction uses short odd walks and a bounded branching tree.
Finally, `diagonal_rate` supplies a monotone divergent f with f(N(d)) < d.
Every graph respecting this profile is three-colorable, by finite witnesses
and coloring compactness, which contradicts the conjectured infinite chromatic
number.
-/

/- Cut distance, masking, and binary-color utilities. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u v
variable {V : Type u} {W : Type v}

abbrev badEdges (G : SimpleGraph V) (c : V → Fin 2) : Set (Sym2 V) :=
  cutBadEdges (⊤ : G.Subgraph) c

noncomputable def beta (G : SimpleGraph V) : ℕ :=
  SimpleGraph.minEdgeDistToBipartite (⊤ : G.Subgraph)

@[simp] lemma mem_badEdges (G : SimpleGraph V) (c : V → Fin 2) (x y : V) :
    s(x,y) ∈ badEdges G c ↔ G.Adj x y ∧ c x = c y := by simp [badEdges]

lemma beta_le_badEdges (G : SimpleGraph V) (c : V → Fin 2) :
    beta G ≤ (badEdges G c).ncard := minEdgeDist_le_cutBadEdges _ _

lemma optimal_badEdges [Finite V] (G : SimpleGraph V) :
    ∃ c : V → Fin 2, (badEdges G c).ncard = beta G :=
  exists_optimal_cut _ (Set.toFinite _)

lemma beta_mono [Finite V] {G H : SimpleGraph V} (h : G ≤ H) : beta G ≤ beta H := by
  obtain ⟨c, hc⟩ := optimal_badEdges H
  apply (beta_le_badEdges G c).trans
  rw [← hc]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    simp only [mem_badEdges] at he ⊢
    exact ⟨h he.1, he.2⟩

/-- Induced graph, with the vertices outside the set retained as isolated vertices. -/
def maskGraph (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := by constructor; rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩
  loopless := by constructor; intro x; exact fun h => G.irrefl h.1

@[simp] lemma maskGraph_adj (G : SimpleGraph V) (S : Set V) (x y : V) :
    (maskGraph G S).Adj x y ↔ G.Adj x y ∧ x ∈ S ∧ y ∈ S := Iff.rfl

lemma maskGraph_le (G : SimpleGraph V) (S : Set V) : maskGraph G S ≤ G :=
  fun _ _ h => h.1

lemma maskGraph_mono (G : SimpleGraph V) {S T : Set V} (h : S ⊆ T) :
    maskGraph G S ≤ maskGraph G T :=
  fun _ _ hadj => ⟨hadj.1, h hadj.2.1, h hadj.2.2⟩

@[simp] lemma maskGraph_univ (G : SimpleGraph V) : maskGraph G Set.univ = G := by
  ext; simp

@[simp] lemma maskGraph_maskGraph (G : SimpleGraph V) (S T : Set V) :
    maskGraph (maskGraph G S) T = maskGraph G (S ∩ T) := by
  ext; simp; tauto

lemma beta_spanningCoe [Finite V] {G : SimpleGraph V} (A : G.Subgraph) :
    beta A.spanningCoe = SimpleGraph.minEdgeDistToBipartite A := by
  have he : ∀ c : V → Fin 2, badEdges A.spanningCoe c = cutBadEdges A c := by
    intro c; ext e; induction e using Sym2.ind with
    | h x y => simp
  obtain ⟨c, hc⟩ := exists_optimal_cut A (Set.toFinite _)
  obtain ⟨d, hd⟩ := optimal_badEdges A.spanningCoe
  apply le_antisymm
  · exact (beta_le_badEdges A.spanningCoe c).trans_eq ((congrArg Set.ncard (he c)).trans hc)
  · rw [← hd, he]
    exact minEdgeDist_le_cutBadEdges A d

lemma maskGraph_eq_spanningCoe (G : SimpleGraph V) (S : Set V) :
    maskGraph G S = ((⊤ : G.Subgraph).induce S).spanningCoe := by
  ext x y
  simp [and_comm, and_assoc]

lemma beta_mask_le_profile [Finite V] (G : SimpleGraph V) (S : Set V) :
    beta (maskGraph G S) ≤ G.maxSubgraphEdgeDistToBipartite S.ncard := by
  rw [maskGraph_eq_spanningCoe, beta_spanningCoe]
  exact minEdgeDist_le_max G _ (Set.toFinite _)

lemma beta_eq_zero_iff [Finite V] (G : SimpleGraph V) : beta G = 0 ↔ G.IsBipartite := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := optimal_badEdges G
    have hempty : badEdges G c = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp (hc.trans h)
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro x y hadj heq
    have : s(x,y) ∈ badEdges G c := (mem_badEdges G c x y).mpr ⟨hadj, heq⟩
    simpa [hempty] using this
  · rintro ⟨c⟩
    have hempty : badEdges G c = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e
      induction e using Sym2.ind with
      | h x y => simpa using c.valid
    exact Nat.eq_zero_of_le_zero (by simpa [hempty] using beta_le_badEdges G c)

/-- The other binary color. -/
def flipTwo (c : Fin 2) : Fin 2 := ⟨1 - c.val, by omega⟩

@[simp] lemma flipTwo_ne (c : Fin 2) : flipTwo c ≠ c := by
  fin_cases c <;> decide

/-- A label constant along a bipartite annulus, normalized at height t. -/
def parityLabel (h : V → ℕ) (t : ℕ) (c : V → Fin 2) (x : V) : Fin 2 :=
  ⟨(c x + h x + t) % 2, Nat.mod_lt _ (by omega)⟩

lemma parityLabel_boundary (h : V → ℕ) (t : ℕ) (c : V → Fin 2)
    {x : V} (hx : h x = t) : parityLabel h t c x = c x := by
  apply Fin.ext
  simp only [parityLabel, Fin.val_mk]
  have := (c x).isLt
  omega

lemma parityLabel_step (h : V → ℕ) (t : ℕ) (c : V → Fin 2)
    {x y : V} (hc : c x ≠ c y) (hs : h x + 1 = h y ∨ h y + 1 = h x) :
    parityLabel h t c x = parityLabel h t c y := by
  apply Fin.ext
  have hx := (c x).isLt
  have hy := (c y).isLt
  have hne : (c x).val ≠ (c y).val := fun e => hc (Fin.ext e)
  simp only [parityLabel, Fin.val_mk]
  omega

lemma badEdges_mono {G H : SimpleGraph V} (h : G ≤ H) (c : V → Fin 2) :
    badEdges G c ⊆ badEdges H c := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    simp only [mem_badEdges] at he ⊢
    exact ⟨h he.1, he.2⟩

lemma plateau_optimal_cut [Finite V] (G : SimpleGraph V) (S T : Set V)
    (hsub : S ⊆ T) (heq : beta (maskGraph G S) = beta (maskGraph G T)) :
    ∃ c : V → Fin 2, (badEdges (maskGraph G T) c).ncard = beta (maskGraph G T) ∧
      badEdges (maskGraph G T) c ⊆ badEdges (maskGraph G S) c := by
  obtain ⟨c, hc⟩ := optimal_badEdges (maskGraph G T)
  refine ⟨c, hc, ?_⟩
  have hle := beta_le_badEdges (maskGraph G S) c
  rw [heq, ← hc] at hle
  exact (Set.eq_of_subset_of_ncard_le
    (badEdges_mono (maskGraph_mono G hsub) c) hle (Set.toFinite _)).symm.subset

end Erdos74

/- Layer closure and the three-color buffer extension. -/
open Filter SimpleGraph
namespace Erdos74
universe u v
variable {V : Type u} {C : Type v}

/-- Truncate a layered graph and attach one apex for each boundary label. -/
def layerClosure (G : SimpleGraph V) (h : V → ℕ) (t : ℕ) (label : V → C) :
    SimpleGraph (V ⊕ C) where
  Adj x y := match x, y with
    | .inl x, .inl y => G.Adj x y ∧ h x ≤ t ∧ h y ≤ t
    | .inl x, .inr c => h x = t ∧ label x = c
    | .inr c, .inl y => h y = t ∧ label y = c
    | .inr _, .inr _ => False
  symm := by
    constructor
    intro x y
    cases x <;> cases y <;> simp only
    · rintro ⟨ha, hx, hy⟩; exact ⟨ha.symm, hy, hx⟩
    · exact id
    · exact id
    · exact id
  loopless := by
    constructor
    intro x
    cases x <;> simp

/-- A third color different from a given color and zero. -/
def bufferColor (c : Fin 3) : Fin 3 := if c = 1 then 2 else 1

lemma bufferColor_ne (c : Fin 3) : bufferColor c ≠ c := by
  fin_cases c <;> decide

lemma bufferColor_ne_zero (c : Fin 3) : bufferColor c ≠ 0 := by
  fin_cases c <;> decide

/-- Extend a coloring across three buffer layers, then use a common alternating cut. -/
def layerExtension (h : V → ℕ) (t : ℕ) (label : V → C)
    (c : V ⊕ C → Fin 3) (x : V) : Fin 3 :=
  if h x ≤ t then c (.inl x)
  else if h x = t + 1 then c (.inr (label x))
  else if h x = t + 2 then bufferColor (c (.inr (label x)))
  else if h x % 2 = (t + 3) % 2 then 0 else 1

lemma layerExtension_valid_ordered (G : SimpleGraph V) (h : V → ℕ) (t : ℕ)
    (label : V → C) (c : (layerClosure G h t label).Coloring (Fin 3))
    (hstep : ∀ x y, G.Adj x y → t < h y → h x + 1 = h y ∨ h y + 1 = h x)
    (hlab : ∀ x y, G.Adj x y → t ≤ h x → h x ≤ h y → h y ≤ t + 3 → label x = label y)
    {x y : V} (hadj : G.Adj x y) (hxy : h x ≤ h y) :
    layerExtension h t label c x ≠ layerExtension h t label c y := by
  by_cases hy : h y ≤ t
  · have hx : h x ≤ t := hxy.trans hy
    simpa [layerExtension, hx, hy] using
      c.valid (show (layerClosure G h t label).Adj (.inl x) (.inl y) from ⟨hadj, hx, hy⟩)
  have hs : h y = h x + 1 := by
    have := hstep x y hadj (by omega)
    omega
  by_cases hx : h x ≤ t
  · have hxt : h x = t := by omega
    have hyt : h y = t + 1 := by omega
    have hl : label x = label y := hlab x y hadj (by omega) hxy (by omega)
    simpa [layerExtension, hx, hy, hyt, ← hl] using
      c.valid (show (layerClosure G h t label).Adj (.inl x) (.inr (label x)) from ⟨hxt, rfl⟩)
  by_cases hx1 : h x = t + 1
  · have hy2 : h y = t + 2 := by omega
    have hl : label x = label y := hlab x y hadj (by omega) hxy (by omega)
    simpa [layerExtension, hx, hy, hx1, hy2, ← hl] using
      (bufferColor_ne (c (.inr (label x)))).symm
  by_cases hx2 : h x = t + 2
  · have hy3 : h y = t + 3 := by omega
    simpa [layerExtension, hx, hy, hx1, hx2, hy3] using
      bufferColor_ne_zero (c (.inr (label x)))
  have hy1 : h y ≠ t + 1 := by omega
  have hy2 : h y ≠ t + 2 := by omega
  have hp : ¬ (h x % 2 = (t + 3) % 2 ↔ h y % 2 = (t + 3) % 2) := by omega
  simp only [layerExtension, if_neg hx, if_neg hy, if_neg hx1, if_neg hx2,
    if_neg hy1, if_neg hy2]
  split_ifs <;> simp_all

lemma colorable_of_layerClosure (G : SimpleGraph V) (h : V → ℕ) (t : ℕ)
    (label : V → C)
    (hstep : ∀ x y, G.Adj x y → t < h y → h x + 1 = h y ∨ h y + 1 = h x)
    (hlab : ∀ x y, G.Adj x y → t ≤ h x → h x ≤ h y → h y ≤ t + 3 → label x = label y)
    (hc : (layerClosure G h t label).Colorable 3) : G.Colorable 3 := by
  obtain ⟨c⟩ := hc
  refine ⟨SimpleGraph.Coloring.mk (layerExtension h t label c) ?_⟩
  intro x y hxy
  rcases le_total (h x) (h y) with hh | hh
  · exact layerExtension_valid_ordered G h t label c hstep hlab hxy hh
  · exact (layerExtension_valid_ordered G h t label c hstep hlab hxy.symm hh).symm

end Erdos74

/- Cuts of the two-apex closure and inheritance of its small profiles. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

lemma beta_layerClosure_le [Finite V] (G : SimpleGraph V) (h : V → ℕ)
    (t : ℕ) (c : V → Fin 2) :
    beta (layerClosure G h t (parityLabel h t c)) ≤
      (badEdges (maskGraph G {x | h x ≤ t}) c).ncard := by
  classical
  let J := layerClosure G h t (parityLabel h t c)
  let d : V ⊕ Fin 2 → Fin 2 := Sum.elim c flipTwo
  have hsub : badEdges J d ⊆ Sym2.map Sum.inl '' badEdges (maskGraph G {x | h x ≤ t}) c := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨ha, hd⟩ := (mem_badEdges J d x y).mp he
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          exact ⟨s(x,y), (mem_badEdges _ _ _ _).mpr ⟨ha, hd⟩, rfl⟩
        | inr z =>
          obtain ⟨ht, hz⟩ := ha
          have hcz : c x = z := (parityLabel_boundary h t c ht).symm.trans hz
          exact False.elim ((flipTwo_ne z).symm (by simpa [d, hcz] using hd))
      | inr z =>
        cases y with
        | inl y =>
          obtain ⟨ht, hz⟩ := ha
          have hcz : c y = z := (parityLabel_boundary h t c ht).symm.trans hz
          exact False.elim (flipTwo_ne z (by simpa [d, hcz] using hd))
        | inr w => exact False.elim ha
  exact (beta_le_badEdges J d).trans ((Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (Set.ncard_image_le (Set.toFinite _)))

lemma exists_missing_layer (S : Set V) (hS : S.Finite) (h : V → ℕ)
    (a t : ℕ) (hcard : S.ncard < t - a) :
    ∃ m, a < m ∧ m ≤ t ∧ ∀ x ∈ S, h x ≠ m := by
  by_contra! hn
  have hsub : Set.Ioc a t ⊆ h '' S := by
    intro m hm
    obtain ⟨x, hx, hxm⟩ := hn m hm.1 hm.2
    exact ⟨x, hx, hxm⟩
  have hb := (Set.ncard_le_ncard hsub (hS.image h)).trans (Set.ncard_image_le hS)
  have heq : (Set.Ioc a t).ncard = t - a := by
    rw [← Finset.coe_Ioc, Set.ncard_coe_finset, Nat.card_Ioc]
  omega

lemma ncard_inl_preimage_le [Finite V] (S : Set (V ⊕ Fin 2)) :
    (Sum.inl ⁻¹' S : Set V).ncard ≤ S.ncard :=
  Set.ncard_le_ncard_of_injOn Sum.inl (fun _ hx => hx)
    (fun _ _ _ _ he => Sum.inl_injective he) (Set.toFinite _)

/-- A missing level lets us splice an arbitrary inner cut with the plateau cut. -/
lemma layerClosure_small_cut [Finite V] (G : SimpleGraph V) (h : V → ℕ)
    (a t m : ℕ) (c d : V → Fin 2) (S : Set (V ⊕ Fin 2))
    (ham : a < m) (hmt : m ≤ t)
    (hgap : ∀ x, Sum.inl x ∈ S → h x ≠ m)
    (hlip : ∀ x y, G.Adj x y → h x ≤ h y + 1 ∧ h y ≤ h x + 1)
    (hbad : ∀ x y, G.Adj x y → h x ≤ t → h y ≤ t → c x = c y → h x ≤ a) :
    beta (maskGraph (layerClosure G h t (parityLabel h t c)) S) ≤
      (badEdges (maskGraph G (Sum.inl ⁻¹' S)) d).ncard := by
  classical
  let J := maskGraph (layerClosure G h t (parityLabel h t c)) S
  let e : V ⊕ Fin 2 → Fin 2 := Sum.elim (fun x => if h x < m then d x else c x) flipTwo
  have hsub : badEdges J e ⊆ Sym2.map Sum.inl '' badEdges (maskGraph G (Sum.inl ⁻¹' S)) d := by
    intro z hz
    induction z using Sym2.ind with
    | h x y =>
      obtain ⟨⟨ha, hxS, hyS⟩, he⟩ := (mem_badEdges J e x y).mp hz
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          obtain ⟨hxy, hxt, hyt⟩ := ha
          have hxm := hgap x hxS
          have hym := hgap y hyS
          have hh := hlip x y hxy
          by_cases hx : h x < m
          · have hy : h y < m := by omega
            have hed : d x = d y := by simpa [e, hx, hy] using he
            exact ⟨s(x,y), (mem_badEdges _ _ _ _).mpr ⟨⟨hxy, hxS, hyS⟩, hed⟩, rfl⟩
          · have hy : ¬ h y < m := by omega
            have hec : c x = c y := by simpa [e, hx, hy] using he
            have := hbad x y hxy hxt hyt hec
            omega
        | inr z =>
          obtain ⟨ht, hz⟩ := ha
          have hcx : c x = z := (parityLabel_boundary h t c ht).symm.trans hz
          have hx : ¬ h x < m := by omega
          exact False.elim ((flipTwo_ne z).symm (by simpa [e, hx, hcx] using he))
      | inr z =>
        cases y with
        | inl y =>
          obtain ⟨ht, hz⟩ := ha
          have hcy : c y = z := (parityLabel_boundary h t c ht).symm.trans hz
          have hy : ¬ h y < m := by omega
          exact False.elim (flipTwo_ne z (by simpa [e, hy, hcy] using he))
        | inr w => exact False.elim ha
  exact (beta_le_badEdges J e).trans ((Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (Set.ncard_image_le (Set.toFinite _)))

lemma beta_layerClosure_small_le [Finite V] (G : SimpleGraph V) (h : V → ℕ)
    (a t : ℕ) (c : V → Fin 2) (S : Set (V ⊕ Fin 2))
    (hsize : S.ncard < t - a)
    (hlip : ∀ x y, G.Adj x y → h x ≤ h y + 1 ∧ h y ≤ h x + 1)
    (hbad : ∀ x y, G.Adj x y → h x ≤ t → h y ≤ t → c x = c y → h x ≤ a) :
    beta (maskGraph (layerClosure G h t (parityLabel h t c)) S) ≤
      beta (maskGraph G (Sum.inl ⁻¹' S)) := by
  obtain ⟨m, ham, hmt, hm⟩ := exists_missing_layer (Sum.inl ⁻¹' S) (Set.toFinite _) h a t
    ((ncard_inl_preimage_le S).trans_lt hsize)
  obtain ⟨d, hd⟩ := optimal_badEdges (maskGraph G (Sum.inl ⁻¹' S))
  exact (layerClosure_small_cut G h a t m c d S ham hmt hm hlip hbad).trans_eq hd

end Erdos74

/- The layer-plateau compression lemma. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

/-- A plateau in the bipartization distance of nested balls can be compressed
without losing non-three-colorability or increasing any sufficiently small profile. -/
lemma layer_plateau_compression [Finite V] (G : SimpleGraph V) (h : V → ℕ)
    (a t b : ℕ) (hat : a < t) (htb : t + 3 ≤ b) (ha : 1 ≤ a)
    (hG : ¬ G.Colorable 3)
    (hlip : ∀ x y, G.Adj x y → h x ≤ h y + 1 ∧ h y ≤ h x + 1)
    (hstep : ∀ x y, G.Adj x y → 1 < h y → h x + 1 = h y ∨ h y + 1 = h x)
    (heq : beta (maskGraph G {x | h x ≤ a}) = beta (maskGraph G {x | h x ≤ b})) :
    ∃ J : SimpleGraph (V ⊕ Fin 2), ¬ J.Colorable 3 ∧
      beta J ≤ beta (maskGraph G {x | h x ≤ b}) ∧
      ∀ S : Set (V ⊕ Fin 2), S.ncard < t - a →
        beta (maskGraph J S) ≤ beta (maskGraph G (Sum.inl ⁻¹' S)) := by
  have hab : a ≤ b := by omega
  obtain ⟨c, hc, hbad⟩ := plateau_optimal_cut G {x | h x ≤ a} {x | h x ≤ b}
    (fun _ hx => hx.trans hab) heq
  have hcproper : ∀ x y, G.Adj x y → a < h x → h x ≤ b → h y ≤ b → c x ≠ c y := by
    intro x y hxy hax hxb hyb he
    have hb : s(x,y) ∈ badEdges (maskGraph G {v | h v ≤ b}) c :=
      (mem_badEdges _ _ _ _).mpr ⟨⟨hxy, hxb, hyb⟩, he⟩
    have hh := (mem_badEdges _ _ _ _).mp (hbad hb)
    exact (not_le_of_gt hax) hh.1.2.1
  let J := layerClosure G h t (parityLabel h t c)
  refine ⟨J, ?_, ?_, ?_⟩
  · intro hJ
    apply hG
    apply colorable_of_layerClosure G h t (parityLabel h t c) _ _ hJ
    · intro x y hxy hy
      exact hstep x y hxy (by omega)
    · intro x y hxy hxt hxyle hyt
      apply parityLabel_step h t c
      · exact hcproper x y hxy (by omega) (by omega) (by omega)
      · exact hstep x y hxy (by omega)
  · apply (beta_layerClosure_le G h t c).trans
    rw [← hc]
    exact Set.ncard_le_ncard (badEdges_mono
      (maskGraph_mono G (fun _ hx => hx.trans (by omega : t ≤ b))) c) (Set.toFinite _)
  · intro S hS
    apply beta_layerClosure_small_le G h a t c S hS hlip
    intro x y hxy hxt hyt he
    by_contra hx
    exact hcproper x y hxy (by omega) (by omega) (by omega) he

end Erdos74

/- A binary-compatible height function rooted at the endpoints of bad edges. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

lemma walk_binary_parity {B : SimpleGraph V} (c : V → Fin 2)
    (hc : ∀ x y, B.Adj x y → c x ≠ c y) {x y : V} (p : B.Walk x y) :
    (p.length + (c x).val) % 2 = (c y).val := by
  induction p with
  | nil => simp only [Walk.length_nil, Nat.zero_add]; exact Nat.mod_eq_of_lt (c _).isLt
  | @cons x y z hxy p ih =>
    have hx := (c x).isLt
    have hy := (c y).isLt
    have hne : (c x).val ≠ (c y).val := fun h => hc x y hxy (Fin.ext h)
    simp only [Walk.length_cons]
    omega

/-- The candidate weighted lengths of root walks. -/
def rootLengths (B : SimpleGraph V) (S : Set V) (c : V → Fin 2) (v : V) : Set ℕ :=
  {n | ∃ s ∈ S, ∃ p : B.Walk s v, n = p.length + (c s).val}

/-- Unreachable vertices are placed above the radius under consideration. -/
noncomputable def rootHeight (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (R : ℕ) (v : V) : ℕ := by
  classical
  exact if (rootLengths B S c v).Nonempty then sInf (rootLengths B S c v)
  else 2 * (R + 2) + (c v).val

lemma rootLengths_nonempty_of_mem (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    {v : V} (hv : v ∈ S) : (rootLengths B S c v).Nonempty :=
  ⟨(c v).val, v, hv, .nil, by simp⟩

lemma rootLengths_nonempty_adj (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    {x y : V} (hxy : B.Adj x y) (hx : (rootLengths B S c x).Nonempty) :
    (rootLengths B S c y).Nonempty := by
  obtain ⟨n, s, hs, p, hn⟩ := hx
  exact ⟨(p.append hxy.toWalk).length + (c s).val, s, hs, p.append hxy.toWalk, rfl⟩

lemma rootHeight_le_walk (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (R : ℕ) {s v : V} (hs : s ∈ S) (p : B.Walk s v) :
    rootHeight B S c R v ≤ p.length + (c s).val := by
  have hm : p.length + (c s).val ∈ rootLengths B S c v := ⟨s, hs, p, rfl⟩
  rw [rootHeight, if_pos ⟨_, hm⟩]
  exact Nat.sInf_le hm

lemma exists_min_rootWalk (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (R : ℕ) {v : V} (hv : (rootLengths B S c v).Nonempty) :
    ∃ s ∈ S, ∃ p : B.Walk s v, rootHeight B S c R v = p.length + (c s).val := by
  have hm := Nat.sInf_mem hv
  obtain ⟨s, hs, p, hp⟩ := hm
  exact ⟨s, hs, p, by simpa [rootHeight, hv] using hp⟩

lemma rootHeight_mem_le_one (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (R : ℕ) {s : V} (hs : s ∈ S) : rootHeight B S c R s ≤ 1 := by
  have := rootHeight_le_walk B S c R hs (.nil : B.Walk s s)
  simp only [Walk.length_nil, zero_add] at this
  exact this.trans (by omega)

lemma rootHeight_parity (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (hc : ∀ x y, B.Adj x y → c x ≠ c y) (R : ℕ) (v : V) :
    rootHeight B S c R v % 2 = (c v).val := by
  by_cases hv : (rootLengths B S c v).Nonempty
  · obtain ⟨s, hs, p, hp⟩ := exists_min_rootWalk B S c R hv
    rw [hp]
    exact walk_binary_parity c hc p
  · simp only [rootHeight, if_neg hv]
    have := (c v).isLt
    omega

lemma rootHeight_adj_lipschitz (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (R : ℕ) {x y : V} (hxy : B.Adj x y) :
    rootHeight B S c R x ≤ rootHeight B S c R y + 1 := by
  by_cases hy : (rootLengths B S c y).Nonempty
  · obtain ⟨s, hs, p, hp⟩ := exists_min_rootWalk B S c R hy
    have hl := rootHeight_le_walk B S c R hs (p.append hxy.symm.toWalk)
    simpa [Walk.length_append, hp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl
  · have hx : ¬ (rootLengths B S c x).Nonempty :=
      fun hx => hy (rootLengths_nonempty_adj B S c hxy hx)
    simp only [rootHeight, if_neg hx, if_neg hy]
    have := (c x).isLt
    omega

lemma rootHeight_adj_step (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (hc : ∀ x y, B.Adj x y → c x ≠ c y) (R : ℕ) {x y : V} (hxy : B.Adj x y) :
    rootHeight B S c R x + 1 = rootHeight B S c R y ∨
      rootHeight B S c R y + 1 = rootHeight B S c R x := by
  have hx := rootHeight_adj_lipschitz B S c R hxy
  have hy := rootHeight_adj_lipschitz B S c R hxy.symm
  have hxp := rootHeight_parity B S c hc R x
  have hyp := rootHeight_parity B S c hc R y
  have hne : (c x).val ≠ (c y).val := fun he => hc x y hxy (Fin.ext he)
  omega

lemma exists_rootWalk_of_low (B : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (R : ℕ) {v : V} (hv : rootHeight B S c R v ≤ R) :
    ∃ s ∈ S, ∃ p : B.Walk s v, p.length ≤ R ∧
      ∀ x ∈ p.support, rootHeight B S c R x ≤ R := by
  classical
  have hr : (rootLengths B S c v).Nonempty := by
    by_contra hn
    simp only [rootHeight, if_neg hn] at hv
    omega
  obtain ⟨s, hs, p, hp⟩ := exists_min_rootWalk B S c R hr
  refine ⟨s, hs, p, by omega, ?_⟩
  intro x hx
  have hb := rootHeight_le_walk B S c R hs (p.takeUntil x hx)
  have hl := p.length_takeUntil_le hx
  omega

/-- The properly cut edges. -/
def goodGraph (G : SimpleGraph V) (c : V → Fin 2) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ c x ≠ c y
  symm := by constructor; rintro x y ⟨hxy, hc⟩; exact ⟨hxy.symm, hc.symm⟩
  loopless := by constructor; intro x; simp

@[simp] lemma goodGraph_adj (G : SimpleGraph V) (c : V → Fin 2) (x y : V) :
    (goodGraph G c).Adj x y ↔ G.Adj x y ∧ c x ≠ c y := Iff.rfl

lemma goodGraph_le (G : SimpleGraph V) (c : V → Fin 2) : goodGraph G c ≤ G :=
  fun _ _ h => h.1

lemma rootHeight_G_lipschitz (G : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (hS : ∀ x y, G.Adj x y → c x = c y → x ∈ S) (R : ℕ)
    {x y : V} (hxy : G.Adj x y) :
    rootHeight (goodGraph G c) S c R x ≤ rootHeight (goodGraph G c) S c R y + 1 := by
  by_cases hc : c x = c y
  · have := rootHeight_mem_le_one (goodGraph G c) S c R (hS x y hxy hc)
    omega
  · exact rootHeight_adj_lipschitz (goodGraph G c) S c R ⟨hxy, hc⟩

lemma rootHeight_G_step (G : SimpleGraph V) (S : Set V) (c : V → Fin 2)
    (hS : ∀ x y, G.Adj x y → c x = c y → x ∈ S) (R : ℕ)
    {x y : V} (hxy : G.Adj x y) (hy : 1 < rootHeight (goodGraph G c) S c R y) :
    rootHeight (goodGraph G c) S c R x + 1 = rootHeight (goodGraph G c) S c R y ∨
      rootHeight (goodGraph G c) S c R y + 1 = rootHeight (goodGraph G c) S c R x := by
  have hc : c x ≠ c y := by
    intro hc
    have := rootHeight_mem_le_one (goodGraph G c) S c R (hS y x hxy.symm hc.symm)
    omega
  exact rootHeight_adj_step (goodGraph G c) S c (fun _ _ h => h.2) R ⟨hxy, hc⟩

end Erdos74

/- Endpoint sets of edge sets. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

def edgeEnds (E : Set (Sym2 V)) : Set V := {v | ∃ e ∈ E, v ∈ e}

@[simp] lemma mem_edgeEnds (E : Set (Sym2 V)) (v : V) :
    v ∈ edgeEnds E ↔ ∃ w, s(v,w) ∈ E := by
  constructor
  · rintro ⟨e, he, hv⟩
    induction e using Sym2.ind with
    | h x y =>
      simp only [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨y, he⟩
      · exact ⟨x, by simpa [Sym2.eq_swap] using he⟩
  · rintro ⟨w, hw⟩
    exact ⟨s(v,w), hw, by simp⟩

lemma edgeEnds_ncard_le [Finite V] (E : Set (Sym2 V)) :
    (edgeEnds E).ncard ≤ 2 * E.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype E := Fintype.ofFinite E
  let F := E.toFinset.biUnion Sym2.toFinset
  have heq : edgeEnds E = (F : Set V) := by
    ext v
    simp [edgeEnds, F]
  rw [heq, Set.ncard_coe_finset]
  calc
    F.card ≤ ∑ e ∈ E.toFinset, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ E.toFinset, 2 := by
      apply Finset.sum_le_sum
      intro e he
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = 2 * E.ncard := by rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card']; exact Nat.mul_comm _ _

lemma bad_edgeEnds (G : SimpleGraph V) (c : V → Fin 2) {x y : V}
    (hxy : G.Adj x y) (hc : c x = c y) : x ∈ edgeEnds (badEdges G c) :=
  (mem_edgeEnds _ _).mpr ⟨y, (mem_badEdges _ _ _ _).mpr ⟨hxy, hc⟩⟩

end Erdos74

/- A bounded branching tree extracts a bounded-size bipartization witness. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

/-- Size bound for the union of witnesses in a bounded-depth branching tree. -/
def kernelSize (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => L + 1 + L * kernelSize L n

/-- A short obstruction avoiding a prescribed set of already chosen edges. -/
def ShortCutObstruction (G : SimpleGraph V) (L : ℕ) (F : Finset (Sym2 V)) : Prop :=
  ∃ (U : Finset V) (E : Finset (Sym2 V)), U.card ≤ L + 1 ∧ E.card ≤ L ∧
    Disjoint E F ∧ ∀ c : V → Fin 2, ∃ e ∈ E, e ∈ badEdges (maskGraph G U) c

lemma kernel_tree [Finite V] (G : SimpleGraph V) (L D : ℕ)
    (hsupply : ∀ F : Finset (Sym2 V), F.card < D → ShortCutObstruction G L F) :
    ∀ (n : ℕ) (F : Finset (Sym2 V)), F.card + n ≤ D →
      ∃ U : Finset V, U.card ≤ kernelSize L n ∧
        ∀ c : V → Fin 2, ∃ E : Finset (Sym2 V), E.card = n ∧ Disjoint E F ∧
          ∀ e ∈ E, e ∈ badEdges (maskGraph G U) c := by
  classical
  intro n
  induction n with
  | zero =>
    intro F hF
    refine ⟨∅, by simp [kernelSize], fun c => ⟨∅, by simp, by simp, ?_⟩⟩
    simp
  | succ n ih =>
    intro F hF
    obtain ⟨U₀, E₀, hU₀, hE₀, hdisj, hhit⟩ := hsupply F (by omega)
    have hchild : ∀ e : Sym2 V, ∃ U : Finset V, U.card ≤ kernelSize L n ∧
        (e ∈ E₀ → ∀ c : V → Fin 2, ∃ E : Finset (Sym2 V), E.card = n ∧
          Disjoint E (insert e F) ∧ ∀ e ∈ E, e ∈ badEdges (maskGraph G U) c) := by
      intro e
      by_cases he : e ∈ E₀
      · have heF : e ∉ F := fun hf => Finset.disjoint_left.mp hdisj he hf
        have hcF : (insert e F).card + n ≤ D := by rw [Finset.card_insert_of_notMem heF]; omega
        obtain ⟨U, hU, hc⟩ := ih (insert e F) hcF
        exact ⟨U, hU, fun _ => hc⟩
      · exact ⟨∅, by simp, fun he' => (he he').elim⟩
    choose U hU hP using hchild
    let W := U₀ ∪ E₀.biUnion U
    refine ⟨W, ?_, ?_⟩
    · calc
        W.card ≤ U₀.card + (E₀.biUnion U).card := Finset.card_union_le _ _
        _ ≤ (L + 1) + ∑ e ∈ E₀, (U e).card := Nat.add_le_add hU₀ Finset.card_biUnion_le
        _ ≤ (L + 1) + ∑ e ∈ E₀, kernelSize L n :=
          Nat.add_le_add_left (Finset.sum_le_sum (fun e _ => hU e)) _
        _ = (L + 1) + E₀.card * kernelSize L n := by simp
        _ ≤ (L + 1) + L * kernelSize L n := by gcongr
        _ = kernelSize L (n + 1) := rfl
    · intro c
      obtain ⟨e, he, hbad⟩ := hhit c
      obtain ⟨E, hEc, hEF, hEB⟩ := hP e he c
      have heE : e ∉ E := fun heE => Finset.disjoint_left.mp hEF heE (by simp)
      have heF : e ∉ F := fun heF => Finset.disjoint_left.mp hdisj he heF
      refine ⟨insert e E, by simp [Finset.card_insert_of_notMem heE, hEc], ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro z hz hzF
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact heF hzF
        · exact Finset.disjoint_left.mp hEF hz (Finset.mem_insert_of_mem hzF)
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · apply badEdges_mono (maskGraph_mono G _) c hbad
          exact fun x hx => Finset.mem_union_left _ hx
        · apply badEdges_mono (maskGraph_mono G _) c (hEB z hz)
          intro x hx
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hx⟩)

lemma bounded_cut_kernel [Finite V] (G : SimpleGraph V) (L D : ℕ)
    (hsupply : ∀ F : Finset (Sym2 V), F.card < D → ShortCutObstruction G L F) :
    ∃ U : Finset V, U.card ≤ kernelSize L D ∧ D ≤ beta (maskGraph G U) := by
  classical
  obtain ⟨U, hU, hP⟩ := kernel_tree G L D hsupply D ∅ (by simp)
  obtain ⟨c, hc⟩ := optimal_badEdges (maskGraph G U)
  obtain ⟨E, hE, _, hEB⟩ := hP c
  refine ⟨U, hU, ?_⟩
  rw [← hc, ← hE, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hEB (Set.toFinite _)

end Erdos74

/- Radius covers, bounded-length walks, and short odd obstructions. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

def walkPower (G : SimpleGraph V) (L : ℕ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ p : G.Walk x y, p.length ≤ L
  symm := by
    constructor
    rintro x y ⟨hne, p, hp⟩
    exact ⟨hne.symm, p.reverse, by simpa using hp⟩
  loopless := by constructor; intro x; simp

lemma walkPower_lift (G : SimpleGraph V) (L : ℕ) {x y : V}
    (p : (walkPower G L).Walk x y) : ∃ q : G.Walk x y, q.length ≤ p.length * L := by
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x y z hxy p ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨_, r, hr⟩ := hxy
    refine ⟨r.append q, ?_⟩
    simp only [Walk.length_append, Walk.length_cons]
    nlinarith

/-- A radius cover by few centers bounds the length needed to connect any reachable pair. -/
lemma radius_cover_short_walk (G : SimpleGraph V) (T : Set V) (hT : T.Finite)
    (q R : ℕ) (hcard : T.ncard ≤ q)
    (hcover : ∀ x : V, ∃ r ∈ T, ∃ p : G.Walk x r, p.length ≤ R)
    {x y : V} (hxy : G.Reachable x y) :
    ∃ p : G.Walk x y, p.length ≤ q * (2 * R + 1) + 2 * R := by
  classical
  letI := hT.fintype
  choose r hr p hp using hcover
  let f : V → T := fun x => ⟨r x, hr x⟩
  let H := (walkPower G (2 * R + 1)).induce T
  have hf : ∀ {x y : V}, G.Adj x y → H.Reachable (f x) (f y) := by
    intro x y hxy
    by_cases he : f x = f y
    · rw [he]
    apply Adj.reachable
    refine ⟨?_, (p x).reverse.append (hxy.toWalk.append (p y)), ?_⟩
    · exact fun h => he (Subtype.ext h)
    · simp only [Walk.length_append, Walk.length_reverse, Adj.toWalk, Walk.length_cons, Walk.length_nil]
      have hx := hp x
      have hy := hp y
      omega
  have hreach : H.Reachable (f x) (f y) := by
    obtain ⟨w⟩ := hxy
    induction w with
    | nil => exact Reachable.rfl
    | cons h w ih => exact (hf h).trans ih
  obtain ⟨w, hw⟩ := hreach.exists_isPath
  have hwlen : w.length ≤ q := by
    have hh := hw.length_lt
    have heq : Fintype.card T = T.ncard := by exact Set.fintypeCard_eq_ncard T
    omega
  obtain ⟨w', hw'⟩ := walkPower_lift G (2 * R + 1) (w.map (Embedding.induce T).toHom)
  refine ⟨(p x).append (w'.append (p y).reverse), ?_⟩
  simp only [Walk.length_map] at hw'
  simp only [Walk.length_append, Walk.length_reverse]
  have hx := hp x
  have hy := hp y
  have hh := Nat.mul_le_mul_right (2 * R + 1) hwlen
  omega

lemma bounded_walks_odd_loop (G : SimpleGraph V) (K : ℕ)
    (hwalk : ∀ x y, G.Reachable x y → ∃ p : G.Walk x y, p.length ≤ K)
    (hG : ¬ G.IsBipartite) :
    ∃ x : V, ∃ p : G.Walk x x, Odd p.length ∧ p.length ≤ 2 * K + 1 := by
  classical
  let r : V → V := fun x => Quot.out (G.connectedComponentMk x)
  have hr : ∀ x, G.Reachable (r x) x := by
    intro x
    exact ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk x))
  choose p hp using fun x => hwalk (r x) x (hr x)
  let c : V → Fin 2 := fun x => ⟨(p x).length % 2, Nat.mod_lt _ (by omega)⟩
  have hbad : ∃ x y : V, G.Adj x y ∧ c x = c y := by
    by_contra! hn
    exact hG ⟨SimpleGraph.Coloring.mk c (fun h => hn _ _ h)⟩
  obtain ⟨x, y, hxy, hc⟩ := hbad
  have hroot : r x = r y := congrArg Quot.out (ConnectedComponent.sound hxy.reachable)
  let w : G.Walk (r x) (r x) :=
    ((p x).append (hxy.toWalk.append (p y).reverse)).copy rfl hroot.symm
  have hw : w.length = (p x).length + (1 + (p y).length) := by
    simp [w, Adj.toWalk, Nat.add_comm]
  have hcp : (p x).length % 2 = (p y).length % 2 := congrArg Fin.val hc
  refine ⟨r x, w, ?_, ?_⟩
  · rw [Nat.odd_iff, hw]
    omega
  · rw [hw]
    have hx := hp x
    have hy := hp y
    omega

lemma walk_parity_of_edges {G : SimpleGraph V} (c : V → Fin 2)
    {x y : V} (p : G.Walk x y)
    (hc : ∀ a b, s(a,b) ∈ p.edges → c a ≠ c b) :
    (p.length + (c x).val) % 2 = (c y).val := by
  induction p with
  | nil => simp only [Walk.length_nil, Nat.zero_add]; exact Nat.mod_eq_of_lt (c _).isLt
  | @cons x y z hxy p ih =>
    have hi := ih (fun a b he => hc a b (by simp [he]))
    have hx := (c x).isLt
    have hy := (c y).isLt
    have hne : (c x).val ≠ (c y).val := fun he => hc x y (by simp) (Fin.ext he)
    simp only [Walk.length_cons]
    omega

lemma odd_walk_bad_edge {G : SimpleGraph V} {x : V} (p : G.Walk x x)
    (hp : Odd p.length) (c : V → Fin 2) :
    ∃ a b, s(a,b) ∈ p.edges ∧ c a = c b := by
  by_contra! hn
  have hpar := walk_parity_of_edges c p hn
  have hodd := Nat.odd_iff.mp hp
  omega

lemma odd_walk_shortCutObstruction (G : SimpleGraph V) (F : Finset (Sym2 V))
    (L : ℕ) {x : V} (p : (G.deleteEdges (F : Set (Sym2 V))).Walk x x)
    (hp : Odd p.length) (hL : p.length ≤ L) : ShortCutObstruction G L F := by
  classical
  refine ⟨p.support.toFinset, p.edges.toFinset, ?_, ?_, ?_, ?_⟩
  · exact (List.toFinset_card_le _).trans (by simpa using Nat.add_le_add_right hL 1)
  · exact (List.toFinset_card_le _).trans (by simpa using hL)
  · apply Finset.disjoint_left.mpr
    intro e he heF
    have hmem := p.edges_subset_edgeSet (List.mem_toFinset.mp he)
    induction e using Sym2.ind with
    | h a b =>
      have hdel := (G.deleteEdges (F : Set (Sym2 V))).mem_edgeSet.mp hmem
      rw [deleteEdges_adj] at hdel
      exact hdel.2 heF
  · intro c
    obtain ⟨a, b, he, hc⟩ := odd_walk_bad_edge p hp c
    refine ⟨s(a,b), List.mem_toFinset.mpr he, (mem_badEdges _ _ _ _).mpr ⟨?_, hc⟩⟩
    exact ⟨(p.adj_of_mem_edges he).1, List.mem_toFinset.mpr (p.fst_mem_support_of_mem_edges he),
      List.mem_toFinset.mpr (p.snd_mem_support_of_mem_edges he)⟩

end Erdos74

/- A graph covered by a bounded number of bounded-radius balls has a small
witness for its entire bounded bipartization distance. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

lemma truncate_walk_delete (G : SimpleGraph V) (S : Set V) (F : Set (Sym2 V))
    {x s : V} (hs : s ∈ S) (p : G.Walk x s) :
    ∃ r ∈ S ∪ edgeEnds F, ∃ q : (G.deleteEdges F).Walk x r, q.length ≤ p.length := by
  classical
  induction p with
  | nil => exact ⟨_, Or.inl hs, .nil, by simp⟩
  | @cons x y z hxy p ih =>
    by_cases he : s(x,y) ∈ F
    · exact ⟨x, Or.inr ((mem_edgeEnds F x).mpr ⟨y, he⟩), .nil, by simp⟩
    · obtain ⟨r, hr, q, hq⟩ := ih hs
      exact ⟨r, hr, q.cons (deleteEdges_adj.mpr ⟨hxy, he⟩), by simpa using hq⟩

lemma beta_le_of_bipartite_delete [Finite V] (G : SimpleGraph V) (F : Set (Sym2 V))
    (hB : (G.deleteEdges F).IsBipartite) : beta G ≤ F.ncard := by
  obtain ⟨c⟩ := hB
  apply (beta_le_badEdges G c).trans
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨hxy, hc⟩ := (mem_badEdges G c x y).mp he
    by_contra hn
    exact c.valid (deleteEdges_adj.mpr ⟨hxy, hn⟩) hc

def radiusKernelSize (q R D : ℕ) : ℕ :=
  kernelSize (2 * ((q + 2 * D) * (2 * R + 1) + 2 * R) + 1) D

lemma bounded_radius_kernel [Finite V] (G : SimpleGraph V) (S : Set V)
    (q R D : ℕ) (hcard : S.ncard ≤ q)
    (hcover : ∀ x : V, ∃ r ∈ S, ∃ p : G.Walk x r, p.length ≤ R)
    (hD : D ≤ beta G) :
    ∃ U : Finset V, U.card ≤ radiusKernelSize q R D ∧ D ≤ beta (maskGraph G U) := by
  classical
  apply bounded_cut_kernel
  intro F hF
  have hB : ¬ (G.deleteEdges (F : Set (Sym2 V))).IsBipartite := by
    intro hB
    have hh := hD.trans (beta_le_of_bipartite_delete G F hB)
    rw [Set.ncard_coe_finset] at hh
    omega
  have hcov : ∀ x : V, ∃ r ∈ S ∪ edgeEnds (F : Set (Sym2 V)),
      ∃ p : (G.deleteEdges (F : Set (Sym2 V))).Walk x r, p.length ≤ R := by
    intro x
    obtain ⟨r, hr, p, hp⟩ := hcover x
    obtain ⟨r', hr', p', hp'⟩ := truncate_walk_delete G S F hr p
    exact ⟨r', hr', p', hp'.trans hp⟩
  have hc : (S ∪ edgeEnds (F : Set (Sym2 V))).ncard ≤ q + 2 * D := by
    have hends := edgeEnds_ncard_le (F : Set (Sym2 V))
    rw [Set.ncard_coe_finset] at hends
    have hu := Set.ncard_union_le S (edgeEnds (F : Set (Sym2 V)))
    omega
  obtain ⟨x, p, hp, hlen⟩ := bounded_walks_odd_loop (G.deleteEdges (F : Set (Sym2 V)))
    ((q + 2 * D) * (2 * R + 1) + 2 * R)
    (fun _ _ hh => radius_cover_short_walk _ _ (Set.toFinite _) _ _ hc hcov hh) hB
  exact odd_walk_shortCutObstruction G F _ p hp hlen

end Erdos74

/- Transport of finite cut distances through induced subgraphs and injective maps. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u v
variable {V : Type u} {W : Type v}

lemma beta_le_of_injective_hom [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) : beta G ≤ beta H := by
  obtain ⟨c, hc⟩ := optimal_badEdges H
  have hsub : Sym2.map f '' badEdges G (c ∘ f) ⊆ badEdges H c := by
    rintro e ⟨d, hd, rfl⟩
    induction d using Sym2.ind with
    | h x y =>
      obtain ⟨hxy, he⟩ := (mem_badEdges _ _ _ _).mp hd
      exact (mem_badEdges _ _ _ _).mpr ⟨f.map_adj hxy, he⟩
  apply (beta_le_badEdges G (c ∘ f)).trans
  rw [← hc, ← Set.ncard_image_of_injective _ (Sym2.map.injective hf)]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

lemma beta_mask_le_image [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (S : Set V) :
    beta (maskGraph G S) ≤ beta (maskGraph H (f '' S)) := by
  let g : maskGraph G S →g maskGraph H (f '' S) :=
    { toFun := f
      map_rel' := fun h => ⟨f.map_adj h.1, ⟨_, h.2.1, rfl⟩, ⟨_, h.2.2, rfl⟩⟩ }
  exact beta_le_of_injective_hom g hf

lemma beta_induce_eq_mask [Finite V] (G : SimpleGraph V) (S : Set V) :
    beta (G.induce S) = beta (maskGraph G S) := by
  classical
  apply le_antisymm
  · let f : G.induce S →g maskGraph G S :=
      { toFun := Subtype.val
        map_rel' := fun {x y} h => ⟨h, x.property, y.property⟩ }
    exact beta_le_of_injective_hom f Subtype.val_injective
  · obtain ⟨c, hc⟩ := optimal_badEdges (G.induce S)
    let d : V → Fin 2 := fun x => if hx : x ∈ S then c ⟨x, hx⟩ else 0
    have hsub : badEdges (maskGraph G S) d ⊆
        Sym2.map Subtype.val '' badEdges (G.induce S) c := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        obtain ⟨⟨hxy, hx, hy⟩, hd⟩ := (mem_badEdges _ _ _ _).mp he
        refine ⟨s(⟨x,hx⟩,⟨y,hy⟩), (mem_badEdges _ _ _ _).mpr ⟨hxy, ?_⟩, rfl⟩
        simpa [d, hx, hy] using hd
    apply (beta_le_badEdges (maskGraph G S) d).trans
    rw [← hc]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

end Erdos74

/- Applying the radius kernel to a weighted root ball. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u
variable {V : Type u}

lemma walk_induce_length {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (S : Set V) (hp : ∀ v ∈ p.support, v ∈ S) : (p.induce S hp).length = p.length := by
  rw [← Walk.length_map (Embedding.induce S).toHom, Walk.map_induce]

lemma root_ball_kernel [Finite V] (G B : SimpleGraph V) (hBG : B ≤ G)
    (S : Set V) (c : V → Fin 2) (q R D : ℕ) (hS : S.ncard ≤ q)
    (hD : D ≤ beta (maskGraph G {v | rootHeight B S c R v ≤ R})) :
    ∃ U : Set V, U.ncard ≤ radiusKernelSize q R D ∧ D ≤ beta (maskGraph G U) := by
  classical
  let A : Set V := {v | rootHeight B S c R v ≤ R}
  let T : Set A := Subtype.val ⁻¹' S
  have hT : T.ncard ≤ q := by
    apply le_trans _ hS
    exact Set.ncard_le_ncard_of_injOn Subtype.val (fun _ hx => hx)
      (fun _ _ _ _ he => Subtype.ext he) (Set.toFinite _)
  have hcov : ∀ x : A, ∃ r ∈ T, ∃ p : (G.induce A).Walk x r, p.length ≤ R := by
    intro x
    obtain ⟨s, hs, p, hp, hsupp⟩ := exists_rootWalk_of_low B S c R x.property
    let w := p.map (Hom.ofLE hBG)
    have hw : ∀ v ∈ w.support, v ∈ A := by
      intro v hv
      apply hsupp v
      simpa [w] using hv
    let z := w.induce A hw
    refine ⟨⟨s, hw s w.start_mem_support⟩, hs, z.reverse, ?_⟩
    simpa only [Walk.length_reverse, z, walk_induce_length, w, Walk.length_map] using hp
  have hDa : D ≤ beta (G.induce A) := by
    rw [beta_induce_eq_mask]
    exact hD
  obtain ⟨U, hU, hβ⟩ := bounded_radius_kernel (G.induce A) T q R D hT hcov hDa
  refine ⟨Subtype.val '' (U : Set A), ?_, ?_⟩
  · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    exact hU
  · exact hβ.trans (beta_mask_le_image (Embedding.induce A).toHom Subtype.val_injective U)

end Erdos74

/- A uniform hierarchy of finite witnesses for non-three-colorability. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u

lemma exists_adjacent_plateau (m : ℕ → ℕ) (hm : Monotone m) (D : ℕ)
    (hD : m D < D) : ∃ j < D, m j = m (j + 1) := by
  by_contra! hn
  have hbound : ∀ j ≤ D, j ≤ m j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hne := hn j (by omega)
      have hle : m j ≤ m (j + 1) := hm (by omega)
      have hi := ih (by omega)
      change j + 1 ≤ m (j + 1)
      omega
  have := hbound D le_rfl
  omega

/-- A deliberately generous recursive size bound. -/
def witnessSize : ℕ → ℕ
  | 0 => 0
  | D + 1 => witnessSize D + 1 +
      radiusKernelSize (2 * (D + 1)) (2 + (D + 1) * (2 * witnessSize D + 8)) (D + 1)

lemma witnessSize_monotone : Monotone witnessSize := by
  apply monotone_nat_of_le_succ
  intro D
  rw [witnessSize]
  omega

/-- Every finite non-three-colorable graph has a bounded-size witness for some
positive portion of its bipartization distance. -/
lemma finite_distance_witness (D : ℕ) :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V), ¬ G.Colorable 3 → beta G ≤ D →
      ∃ d, 0 < d ∧ d ≤ D ∧ ∃ S : Set V, S.ncard ≤ witnessSize d ∧ d ≤ beta (maskGraph G S) := by
  classical
  induction D with
  | zero =>
    intro V hV G hG hβ
    have hzero : beta G = 0 := Nat.eq_zero_of_le_zero hβ
    exact (hG (((beta_eq_zero_iff G).mp hzero).mono (by decide : 2 ≤ 3))).elim
  | succ D ih =>
    intro V hV G hG hβ
    by_cases hsmall : beta G ≤ D
    · obtain ⟨d, hd, hdD, S, hS, hSd⟩ := ih V G hG hsmall
      exact ⟨d, hd, by omega, S, hS, hSd⟩
    have hβeq : beta G = D + 1 := by omega
    obtain ⟨c, hc⟩ := optimal_badEdges G
    let S := edgeEnds (badEdges G c)
    let s := 2 * witnessSize D + 8
    let R := 2 + (D + 1) * s
    let h := rootHeight (goodGraph G c) S c R
    have hS : S.ncard ≤ 2 * (D + 1) := by
      have hh := edgeEnds_ncard_le (badEdges G c)
      simpa [hc, hβeq, S] using hh
    have hcover : ∀ x y, G.Adj x y → c x = c y → x ∈ S :=
      fun _ _ hxy hcc => bad_edgeEnds G c hxy hcc
    have hlip : ∀ x y, G.Adj x y → h x ≤ h y + 1 ∧ h y ≤ h x + 1 := by
      intro x y hxy
      exact ⟨rootHeight_G_lipschitz G S c hcover R hxy,
        rootHeight_G_lipschitz G S c hcover R hxy.symm⟩
    have hstep : ∀ x y, G.Adj x y → 1 < h y → h x + 1 = h y ∨ h y + 1 = h x := by
      intro x y hxy hy
      exact rootHeight_G_step G S c hcover R hxy hy
    by_cases hfull : D + 1 ≤ beta (maskGraph G {v | h v ≤ R})
    · obtain ⟨U, hU, hUd⟩ := root_ball_kernel G (goodGraph G c) (goodGraph_le G c)
        S c (2 * (D + 1)) R (D + 1) hS hfull
      refine ⟨D + 1, by omega, le_rfl, U, ?_, hUd⟩
      exact hU.trans (by rw [witnessSize]; change _ ≤ witnessSize D + 1 + radiusKernelSize _ R _; omega)
    · let m : ℕ → ℕ := fun j => beta (maskGraph G {v | h v ≤ 2 + j * s})
      have hm : Monotone m := by
        intro i j hij
        apply beta_mono (maskGraph_mono G _)
        intro x hx
        have hh := Nat.mul_le_mul_right s hij
        change h x ≤ 2 + j * s
        change h x ≤ 2 + i * s at hx
        omega
      have hmD : m (D + 1) < D + 1 := by change beta (maskGraph G {v | h v ≤ R}) < _; omega
      obtain ⟨j, hj, heq⟩ := exists_adjacent_plateau m hm (D + 1) hmD
      let a := 2 + j * s
      let b := 2 + (j + 1) * s
      let t := a + 2 * witnessSize D + 4
      have hat : a < t := by dsimp [t]; omega
      have htb : t + 3 ≤ b := by dsimp [t, a, b]; rw [Nat.add_mul]; dsimp [s]; omega
      have ha : 1 ≤ a := by dsimp [a]; omega
      obtain ⟨J, hJ, hJβ, hJsmall⟩ := layer_plateau_compression G h a t b hat htb ha hG
        hlip hstep heq
      have hJle : beta J ≤ D := by
        have hmb : m (j + 1) ≤ m (D + 1) := hm (by omega)
        change beta (maskGraph G {v | h v ≤ b}) ≤ _ at hmb
        omega
      obtain ⟨d, hd, hdD, U, hU, hUd⟩ := ih (V ⊕ Fin 2) J hJ hJle
      have hUsmall : U.ncard < t - a := by
        have hh := hU.trans (witnessSize_monotone hdD)
        dsimp [t]
        omega
      refine ⟨d, hd, by omega, Sum.inl ⁻¹' U, (ncard_inl_preimage_le U).trans hU, ?_⟩
      exact hUd.trans (hJsmall U hUsmall)

end Erdos74

/- Diagonalizing the finite-witness hierarchy disproves the conjecture. -/
open Filter SimpleGraph
namespace Erdos74
open Erdos74
universe u

lemma exists_rate_three_colorable :
    ∃ f : ℕ → ℕ, Monotone f ∧ Tendsto f atTop atTop ∧
      ∀ (V : Type u) (G : SimpleGraph V),
        (∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) → G.Colorable 3 := by
  classical
  obtain ⟨f, hmono, hf, hdiag⟩ := diagonal_rate (fun i => witnessSize (i + 1))
    (fun i => i + 1) (tendsto_add_atTop_nat 1) (fun i => Nat.succ_pos i)
  have hfinite : ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n) → G.Colorable 3 := by
    intro V hV G hprof
    by_contra hG
    obtain ⟨d, hd, _, S, hS, hdS⟩ := finite_distance_witness (beta G) V G hG le_rfl
    have hupper : beta (maskGraph G S) ≤ f S.ncard :=
      (beta_mask_le_profile G S).trans (hprof S.ncard)
    have hlower := hdS.trans (hupper.trans (hmono hS))
    have hdiag' := hdiag (d - 1)
    have hpred : d - 1 + 1 = d := by omega
    rw [hpred] at hdiag'
    omega
  refine ⟨f, hmono, hf, ?_⟩
  intro V G hprof
  apply colorable_of_finite_induced G 3 (by omega)
  intro S
  apply hfinite S (G.induce (S : Set V))
  intro n
  exact (maxEdgeDist_induce_le G (S : Set V) n).trans (hprof n)

/-- A sufficiently slowly diverging profile forces three-colorability. -/
theorem erdos_74.disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n)) := by
  obtain ⟨f, _, hf, hcolor⟩ := exists_rate_three_colorable.{u}
  intro h
  obtain ⟨V, G, hχ, hG⟩ := h f hf
  have hc := (hcolor V G hG).chromaticNumber_le
  rw [hχ] at hc
  exact (ENat.coe_lt_top 3).not_ge hc

end Erdos74

namespace Jig31Canonical

open Filter SimpleGraph
open scoped Topology

universe u

def edgeDistancesToBipartite {V : Type u} {G : SimpleGraph V}
    (A : G.Subgraph) : Set ℕ :=
  {k | ∃ E : Set (Sym2 V), E ⊆ A.edgeSet ∧
    IsBipartite (A.deleteEdges E).coe ∧ k = E.ncard}

noncomputable def minEdgeDistToBipartite {V : Type u} {G : SimpleGraph V}
    (A : G.Subgraph) : ℕ :=
  sInf (edgeDistancesToBipartite A)

def subgraphEdgeDistsToBipartite {V : Type u}
    (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  {k | ∃ A : G.Subgraph, A.verts.ncard = n ∧ A.verts.Finite ∧
    k = minEdgeDistToBipartite A}

noncomputable def maxSubgraphEdgeDistToBipartite {V : Type u}
    (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup (subgraphEdgeDistsToBipartite G n)

/-- Erdős Problem 74: arbitrarily slow divergent edge-deletion bounds
are compatible with infinite chromatic number. -/
abbrev statement : Prop :=
  ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    ∃ (V : Type u) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ n, maxSubgraphEdgeDistToBipartite G n ≤ f n

theorem edgeDistances_eq {V : Type u} {G : SimpleGraph V} (A : G.Subgraph) :
    edgeDistancesToBipartite A = Erdos74.SimpleGraph.edgeDistancesToBipartite A := by
  ext k
  simp only [edgeDistancesToBipartite, Erdos74.SimpleGraph.edgeDistancesToBipartite,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨E, hE, hB, hk⟩
    exact ⟨E, hE, hB, hk.symm⟩
  · rintro ⟨E, hE, hB, hk⟩
    exact ⟨E, hE, hB, hk.symm⟩

theorem minEdgeDist_eq {V : Type u} {G : SimpleGraph V} (A : G.Subgraph) :
    minEdgeDistToBipartite A = Erdos74.SimpleGraph.minEdgeDistToBipartite A := by
  unfold minEdgeDistToBipartite Erdos74.SimpleGraph.minEdgeDistToBipartite
  rw [edgeDistances_eq]

theorem subgraphEdgeDists_eq {V : Type u} (G : SimpleGraph V) (n : ℕ) :
    subgraphEdgeDistsToBipartite G n = Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite G n := by
  ext k
  simp only [subgraphEdgeDistsToBipartite,
    Erdos74.SimpleGraph.subgraphEdgeDistsToBipartite, Set.mem_setOf_eq, minEdgeDist_eq]
  constructor
  · rintro ⟨A, hn, hfin, hk⟩
    exact ⟨A, hn, hfin, hk.symm⟩
  · rintro ⟨A, hn, hfin, hk⟩
    exact ⟨A, hn, hfin, hk.symm⟩

theorem maxSubgraphEdgeDist_eq {V : Type u} (G : SimpleGraph V) (n : ℕ) :
    maxSubgraphEdgeDistToBipartite G n = Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n := by
  unfold maxSubgraphEdgeDistToBipartite Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite
  rw [subgraphEdgeDists_eq]

/-- Port of Epoch AI's published GPT-6 Astra refutation, with an exact bridge
from Jig31's definitions to the definitions used in the published proof. -/
theorem solution : ¬ statement.{u} := by
  intro h
  apply Erdos74.erdos_74.disproof.{u}
  intro f hf
  obtain ⟨V, G, hχ, hG⟩ := h f hf
  refine ⟨V, G, hχ, ?_⟩
  intro n
  rw [← maxSubgraphEdgeDist_eq]
  exact hG n


end Jig31Canonical

namespace Submissions.Erdos74AlmostBipartiteRefuted.EpochPort

universe u

/-- Re-verification of Epoch AI’s existing refutation against Jig’s exact root. -/
theorem proof : ¬ Jig31Canonical.statement.{u} := Jig31Canonical.solution.{u}

end Submissions.Erdos74AlmostBipartiteRefuted.EpochPort
