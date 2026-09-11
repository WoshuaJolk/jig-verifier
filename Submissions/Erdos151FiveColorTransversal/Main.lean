import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
The pointwise Erdős151 bound for finite graphs admitting a proper five-coloring.

This self-contained source assembles the support and C5 arguments under the
submission module's namespace. The mathematical proof is a classical coloring
reduction; no novelty or resolution of the unrestricted problem is claimed.
Exact-source verification of this assembled module is recorded separately.
-/

namespace Submissions.Erdos151FiveColorTransversal.Main

namespace Jig312Support

open SimpleGraph

def CliqueTransversal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ K : Finset V, 2 ≤ K.card →
    Maximal G.IsClique (K : Set V) →
      ∃ v ∈ K, v ∈ T

def GuaranteesTriangleFreeIndependentSet (n h : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    ∃ S : Finset (Fin n), h ≤ S.card ∧ G.IsIndepSet (S : Set (Fin n))

/-- Every maximal nontrivial clique of G contains an edge of F.
No global relation F ≤ G is necessary for the implication proved here. -/
def MeetsMaximalCliques {V : Type} [DecidableEq V]
    (G F : SimpleGraph V) : Prop :=
  ∀ K : Finset V, 2 ≤ K.card →
    Maximal G.IsClique (K : Set V) →
      ∃ u ∈ K, ∃ v ∈ K, F.Adj u v

/-- The complement of any F-independent set meets every supported G-clique. -/
theorem complement_is_cliqueTransversal
    {n : ℕ} {G F : SimpleGraph (Fin n)}
    (hSupport : MeetsMaximalCliques G F)
    {S : Finset (Fin n)}
    (hIndependent : F.IsIndepSet (S : Set (Fin n))) :
    CliqueTransversal G (Finset.univ \ S) := by
  classical
  intro K hKcard hKmax
  obtain ⟨u, huK, v, hvK, huv⟩ := hSupport K hKcard hKmax
  by_cases huS : u ∈ S
  · have hvS : v ∉ S := by
      intro hvS
      exact hIndependent huS hvS huv.ne huv
    exact ⟨v, hvK, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvS⟩⟩
  · exact ⟨u, huK, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huS⟩⟩

/-- Cardinality conversion using natural subtraction, including n=0. -/
theorem complement_card_bound
    {n h : ℕ} {S : Finset (Fin n)} (hSize : h ≤ S.card) :
    (Finset.univ \ S).card ≤ n - h := by
  classical
  calc
    (Finset.univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp
    _ ≤ n - h := Nat.sub_le_sub_left hSize n

/-- A separate per-h consequence. The final theorem below strengthens this
by choosing the transversal once, before h is quantified. -/
theorem supported_graph_bound_for_h
    {n h : ℕ} (G F : SimpleGraph (Fin n))
    (hTriangleFree : F.CliqueFree 3)
    (hSupport : MeetsMaximalCliques G F)
    (hGuarantee : GuaranteesTriangleFreeIndependentSet n h) :
    ∃ T : Finset (Fin n), CliqueTransversal G T ∧ T.card ≤ n - h := by
  classical
  obtain ⟨S, hSize, hIndependent⟩ := hGuarantee F hTriangleFree
  exact ⟨Finset.univ \ S,
    complement_is_cliqueTransversal hSupport hIndependent,
    complement_card_bound hSize⟩

/-- The exact uniform-transversal conclusion of the #312 root for a graph
equipped with a triangle-free support. The same T works for every admissible h. -/
theorem supported_graph_uniform_bound
    {n : ℕ} (G F : SimpleGraph (Fin n))
    (hTriangleFree : F.CliqueFree 3)
    (hSupport : MeetsMaximalCliques G F) :
    ∃ T : Finset (Fin n), CliqueTransversal G T ∧
      ∀ h : ℕ, GuaranteesTriangleFreeIndependentSet n h →
        T.card ≤ n - h := by
  classical
  obtain ⟨S, hMaximum⟩ := F.maximumIndepSet_exists
  refine ⟨Finset.univ \ S,
    complement_is_cliqueTransversal hSupport hMaximum.isIndepSet, ?_⟩
  intro h hGuarantee
  obtain ⟨A, hSize, hIndependent⟩ := hGuarantee F hTriangleFree
  have hToMaximum : h ≤ S.card :=
    hSize.trans (hMaximum.maximum A hIndependent)
  exact complement_card_bound hToMaximum

end Jig312Support

namespace Jig312FiveColors

open SimpleGraph
open Jig312Support

/-- Adjacency of the cycle with vertices 0,1,2,3,4 in that order. -/
abbrev CycleAdj (i j : Fin 5) : Prop :=
  (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val

theorem cycleAdj_symm {i j : Fin 5} (h : CycleAdj i j) : CycleAdj j i :=
  Or.symm h

/-- The red C5 has no triangle, including repeated-vertex possibilities. -/
theorem cycleAdj_no_triangle :
    ∀ i j k : Fin 5,
      CycleAdj i j → CycleAdj i k → CycleAdj j k → False := by
  decide

/-- On any three distinct colors, at least one edge belongs to the red C5.
Equivalently the complementary blue C5 is triangle-free. -/
theorem distinct_colors_have_red_edge :
    ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      CycleAdj i j ∨ CycleAdj i k ∨ CycleAdj j k := by
  decide

/-- The selected edge support: red edges, together with edges in no triangle.
This is a subgraph of G, so its irreflexivity comes directly from G. -/
def supportGraph {V : Type} (G : SimpleGraph V) (c : V → Fin 5) : SimpleGraph V where
  Adj u v := G.Adj u v ∧
    (CycleAdj (c u) (c v) ∨ ¬ ∃ w, G.Adj u w ∧ G.Adj v w)
  symm.symm u v h := by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hRed | hNoCommon
    · exact Or.inl (cycleAdj_symm hRed)
    · apply Or.inr
      rintro ⟨w, hvw, huw⟩
      exact hNoCommon ⟨w, huw, hvw⟩
  loopless.irrefl u h := G.irrefl h.1

/-- No properness assumption is needed for triangle-freeness of the support. -/
theorem supportGraph_triangleFree
    {V : Type} (G : SimpleGraph V) (c : V → Fin 5) :
    (supportGraph G c).CliqueFree 3 := by
  classical
  intro K hK
  obtain ⟨u, v, w, huv, huw, hvw, _⟩ :=
    SimpleGraph.is3Clique_iff.mp hK
  have hRedUV : CycleAdj (c u) (c v) := by
    rcases huv.2 with hRed | hNoCommon
    · exact hRed
    · exact False.elim (hNoCommon ⟨w, huw.1, hvw.1⟩)
  have hRedUW : CycleAdj (c u) (c w) := by
    rcases huw.2 with hRed | hNoCommon
    · exact hRed
    · exact False.elim (hNoCommon ⟨v, huv.1, hvw.1.symm⟩)
  have hRedVW : CycleAdj (c v) (c w) := by
    rcases hvw.2 with hRed | hNoCommon
    · exact hRed
    · exact False.elim (hNoCommon ⟨u, huv.1.symm, huw.1.symm⟩)
  exact cycleAdj_no_triangle (c u) (c v) (c w) hRedUV hRedUW hRedVW

/-- A maximal pair has no common neighbor. The argument explicitly uses
inclusion maximality of its clique, as in the #312 canonical definition. -/
theorem maximal_pair_no_common_neighbor
    {V : Type} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (hMax : Maximal G.IsClique (({u, v} : Finset V) : Set V)) :
    ¬ ∃ w, G.Adj u w ∧ G.Adj v w := by
  classical
  rintro ⟨w, huw, hvw⟩
  have hLarger : G.IsClique (insert w (({u, v} : Finset V) : Set V)) := by
    apply hMax.1.insert
    intro x hx _
    have hxPair : x = u ∨ x = v := by simpa using hx
    rcases hxPair with rfl | rfl
    · exact huw.symm
    · exact hvw.symm
  have hContain :
      insert w (({u, v} : Finset V) : Set V) ⊆
        (({u, v} : Finset V) : Set V) :=
    (SimpleGraph.isMaximalClique_iff.mp hMax).2 _ hLarger
      (by
        intro x hx
        exact Or.inr hx)
  have hwPair : w ∈ ({u, v} : Finset V) := hContain (by simp)
  have hwCases : w = u ∨ w = v := by simpa using hwPair
  rcases hwCases with rfl | rfl
  · exact G.irrefl huw
  · exact G.irrefl hvw

/-- Properness makes every maximal clique contain a selected support edge. -/
theorem supportGraph_meetsMaximalCliques
    {V : Type} [DecidableEq V] (G : SimpleGraph V) (c : V → Fin 5)
    (hProper : ∀ {u v : V}, G.Adj u v → c u ≠ c v) :
    MeetsMaximalCliques G (supportGraph G c) := by
  classical
  intro K hKcard hKmax
  rcases lt_or_eq_of_le hKcard with hLarge | hPair
  · obtain ⟨u, v, w, huK, hvK, hwK, huv, huw, hvw⟩ :=
      Finset.two_lt_card_iff.mp hLarge
    have hAdjUV : G.Adj u v := hKmax.1 huK hvK huv
    have hAdjUW : G.Adj u w := hKmax.1 huK hwK huw
    have hAdjVW : G.Adj v w := hKmax.1 hvK hwK hvw
    rcases distinct_colors_have_red_edge (c u) (c v) (c w)
        (hProper hAdjUV) (hProper hAdjUW) (hProper hAdjVW) with
      hRedUV | hRedUW | hRedVW
    · exact ⟨u, huK, v, hvK, hAdjUV, Or.inl hRedUV⟩
    · exact ⟨u, huK, w, hwK, hAdjUW, Or.inl hRedUW⟩
    · exact ⟨v, hvK, w, hwK, hAdjVW, Or.inl hRedVW⟩
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hPair.symm
    have hAdjUV : G.Adj u v := hKmax.1 (by simp) (by simp) huv
    exact ⟨u, by simp, v, by simp, hAdjUV,
      Or.inr (maximal_pair_no_common_neighbor hKmax)⟩

/-- Full pointwise #312 conclusion for a graph with an explicit proper
five-coloring. One transversal works uniformly for all admissible h. -/
theorem five_color_uniform_bound
    {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 5)
    (hProper : ∀ {u v : Fin n}, G.Adj u v → c u ≠ c v) :
    ∃ T : Finset (Fin n), CliqueTransversal G T ∧
      ∀ h : ℕ, GuaranteesTriangleFreeIndependentSet n h →
        T.card ≤ n - h := by
  exact supported_graph_uniform_bound G (supportGraph G c)
    (supportGraph_triangleFree G c)
    (supportGraph_meetsMaximalCliques G c hProper)

end Jig312FiveColors

open SimpleGraph
open Jig312Support

/-- The exact proposed five-color partial statement, with one transversal
working for every universally guaranteed triangle-free independent-set size. -/
theorem result :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (∃ c : Fin n → Fin 5, ∀ u v, G.Adj u v → c u ≠ c v) →
      ∃ T : Finset (Fin n), CliqueTransversal G T ∧
        ∀ h : ℕ, GuaranteesTriangleFreeIndependentSet n h →
          T.card ≤ n - h := by
  intro n G hColorable
  obtain ⟨c, hProper⟩ := hColorable
  apply Jig312FiveColors.five_color_uniform_bound G c
  intro u v huv
  exact hProper u v huv

end Submissions.Erdos151FiveColorTransversal.Main
