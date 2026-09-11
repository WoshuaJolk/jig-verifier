import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Function.Basic

namespace Submissions.E810WedgeBound.WedgeBound

open Finset

def edge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

def allEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun e => e.1 < e.2

def EveryC4Rainbow {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Prop :=
  ∀ v : Fin 4 → Fin n, Function.Injective v →
    (∀ i : Fin 4, edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩) ∈ E) →
    Function.Injective
      (fun i : Fin 4 => color (edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩)))

def monochromaticWedges {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun t => t.2.1 < t.2.2 ∧
    edge t.1 t.2.1 ∈ E ∧ edge t.1 t.2.2 ∈ E ∧
      color (edge t.1 t.2.1) = color (edge t.1 t.2.2)

theorem edge_comm {n : ℕ} (u v : Fin n) : edge u v = edge v u := by
  unfold edge
  split_ifs <;> simp_all <;> omega

theorem endpoints_ne {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ allEdges n) {u v : Fin n} (h : edge u v ∈ E) : u ≠ v := by
  intro huv
  subst v
  have hh := hE h
  simp [allEdges, edge] at hh

theorem unique_center {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) {x w y z : Fin n}
    (hyz : y ≠ z) (hxy : edge x y ∈ E) (hxz : edge x z ∈ E)
    (hwy : edge w y ∈ E) (hwz : edge w z ∈ E)
    (hc : color (edge x y) = color (edge x z)) : x = w := by
  by_contra hxw
  have hxy' := endpoints_ne hE hxy
  have hxz' := endpoints_ne hE hxz
  have hwy' := endpoints_ne hE hwy
  have hwz' := endpoints_ne hE hwz
  let v : Fin 4 → Fin n := fun i =>
    if i = 0 then y else if i = 1 then x else if i = 2 then z else w
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have he : ∀ i : Fin 4, edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩) ∈ E := by
    intro i
    fin_cases i <;> simp_all [v, edge_comm]
  have hi := hrain v hv he
  have heq : color (edge (v 0) (v 1)) = color (edge (v 1) (v 2)) := by
    simpa [v, edge_comm] using hc
  have h01 : (0 : Fin 4) = 1 := hi (by simpa using heq)
  exact (by decide : (0 : Fin 4) ≠ 1) h01

theorem proof (n : ℕ) (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) :
    (monochromaticWedges E color).card ≤ (allEdges n).card := by
  apply Finset.card_le_card_of_injOn (fun t : Fin n × Fin n × Fin n => t.2)
  · intro t ht
    have h := (Finset.mem_filter.mp ht).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h.1⟩
  · intro t ht s hs hts
    rcases t with ⟨x, y, z⟩
    rcases s with ⟨w, y', z'⟩
    simp only [Prod.mk.injEq] at hts
    rcases hts with ⟨rfl, rfl⟩
    have ht' := (Finset.mem_filter.mp ht).2
    have hs' := (Finset.mem_filter.mp hs).2
    have hxw := unique_center hE hrain (ne_of_lt ht'.1)
      ht'.2.1 ht'.2.2.1 hs'.2.1 hs'.2.2.1 ht'.2.2.2
    exact congrArg (fun a => (a, y, z)) hxw

end Submissions.E810WedgeBound.WedgeBound

namespace Submissions.E810ProperExtraction.IndependentBound

open Finset SimpleGraph

theorem cliqueFree_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {r : ℕ} (hr : 0 < r) (hc : G.CliqueFree (r + 1)) :
    2 * r * G.edgeFinset.card ≤ (r - 1) * (Fintype.card V) ^ 2 := by
  classical
  obtain ⟨H, _, hm⟩ := SimpleGraph.exists_isTuranMaximal (V := V) hr
  have he := hm.2 hc
  have ht := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := Fintype.card V) (r := r)
  have hi := ((SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp hm).some.card_edgeFinset_eq
  rw [← hi] at ht
  exact (Nat.mul_le_mul_left (2 * r) he).trans ht

/-- Standard average-degree independent-set bound, obtained from the pinned
Mathlib proof of Turán's theorem on the complement. No claim of novelty. -/
theorem exists_independent_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ s : Finset V, G.IsIndepSet s ∧
      (Fintype.card V) ^ 2 ≤ s.card * (Fintype.card V + 2 * G.edgeFinset.card) := by
  classical
  obtain ⟨s, hs⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  refine ⟨s, hs.isIndepSet, ?_⟩
  have hc : Gᶜ.CliqueFree (s.card + 1) := by
    intro t ht
    have hb := hs.maximum t (by simpa using ht.isClique)
    have he := ht.card_eq
    omega
  by_cases hr : s.card = 0
  · have hi : IsEmpty V := by simpa [hr] using hc
    letI := hi
    simp
  have hrp : 0 < s.card := Nat.pos_of_ne_zero hr
  have ht := cliqueFree_bound Gᶜ hrp hc
  have he : G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
    have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset :=
      SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
    have hu : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset :=
      SimpleGraph.edgeFinset_sup.symm.trans
        (SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top)
    rw [← Finset.card_union_of_disjoint hd, hu,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  have hchoose : 2 * (Fintype.card V).choose 2 =
      Fintype.card V * (Fintype.card V - 1) := by
    rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  have hn1 : Fintype.card V - 1 + 1 = Fintype.card V := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
  have hr1 : s.card - 1 + 1 = s.card := Nat.sub_add_cancel hrp
  nlinarith [congrArg (fun a => 2 * s.card * a) he,
    congrArg (fun a => s.card * a) hchoose,
    congrArg (fun a => a * (Fintype.card V) ^ 2) hr1,
    congrArg (fun a => s.card * Fintype.card V * a) hn1]

end Submissions.E810ProperExtraction.IndependentBound

namespace Submissions.E810ProperExtraction.Conflict

open Finset
open Submissions.E810WedgeBound.WedgeBound

abbrev EdgeVertex {n : ℕ} (E : Finset (Fin n × Fin n)) :=
  {e : Fin n × Fin n // e ∈ E}

def SharesEndpoint {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

theorem sharesEndpoint_symm {n : ℕ} {e f : Fin n × Fin n}
    (h : SharesEndpoint e f) : SharesEndpoint f e := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

def conflictGraph {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : SimpleGraph (EdgeVertex E) :=
  SimpleGraph.fromRel fun e f => SharesEndpoint e.1 f.1 ∧ color e.1 = color f.1

theorem conflictGraph_adj_iff {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} {e f : EdgeVertex E} :
    (conflictGraph E color).Adj e f ↔
      e ≠ f ∧ SharesEndpoint e.1 f.1 ∧ color e.1 = color f.1 := by
  change (e ≠ f ∧ ((SharesEndpoint e.1 f.1 ∧ color e.1 = color f.1) ∨
    (SharesEndpoint f.1 e.1 ∧ color f.1 = color e.1))) ↔ _
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h.1, h.2⟩
    · exact ⟨hne, sharesEndpoint_symm h.1, h.2.symm⟩
  · rintro ⟨hne, hshare, hcolor⟩
    exact ⟨hne, Or.inl ⟨hshare, hcolor⟩⟩

instance conflictGraphDecidableAdj {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : DecidableRel (conflictGraph E color).Adj := by
  intro e f
  change Decidable (e ≠ f ∧ ((SharesEndpoint e.1 f.1 ∧ color e.1 = color f.1) ∨
    (SharesEndpoint f.1 e.1 ∧ color f.1 = color e.1)))
  unfold SharesEndpoint
  infer_instance

def selectedEdges {n : ℕ} (E : Finset (Fin n × Fin n))
    (I : Finset (EdgeVertex E)) : Finset (Fin n × Fin n) :=
  I.map (Function.Embedding.subtype fun e => e ∈ E)

theorem selectedEdges_subset {n : ℕ} (E : Finset (Fin n × Fin n))
    (I : Finset (EdgeVertex E)) : selectedEdges E I ⊆ E := by
  intro e he
  exact Finset.property_of_mem_map_subtype I he

theorem selectedEdges_card {n : ℕ} (E : Finset (Fin n × Fin n))
    (I : Finset (EdgeVertex E)) : (selectedEdges E I).card = I.card := by
  exact Finset.card_map _

def ProperOn {n : ℕ} (F : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → SharesEndpoint e f → color e ≠ color f

theorem selectedEdges_proper {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} {I : Finset (EdgeVertex E)}
    (hI : (conflictGraph E color).IsIndepSet (I : Set (EdgeVertex E))) :
    ProperOn (selectedEdges E I) color := by
  intro e he f hf hef hshare hcolor
  rcases Finset.mem_map.mp he with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hf with ⟨b, hb, rfl⟩
  have hab : a ≠ b := by
    intro h
    exact hef (congrArg Subtype.val h)
  exact hI ha hb hab (conflictGraph_adj_iff.mpr ⟨hab, hshare, hcolor⟩)

theorem edge_left_injective {n : ℕ} (x : Fin n) :
    Function.Injective (edge x) := by
  intro y z h
  unfold edge at h
  split_ifs at h <;> simp_all [Prod.mk.injEq]

theorem sharesEndpoint_edge {n : ℕ} (x y z : Fin n) :
    SharesEndpoint (edge x y) (edge x z) := by
  unfold SharesEndpoint edge
  split_ifs <;> simp_all

theorem properOn_incident {n : ℕ} {F : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hproper : ProperOn F color)
    {x y z : Fin n} (hxy : edge x y ∈ F) (hxz : edge x z ∈ F)
    (hyz : y ≠ z) : color (edge x y) ≠ color (edge x z) := by
  apply hproper (edge x y) hxy (edge x z) hxz
  · intro h
    exact hyz (edge_left_injective x h)
  · exact sharesEndpoint_edge x y z

theorem selectedEdges_rainbow {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hrain : EveryC4Rainbow E color)
    (I : Finset (EdgeVertex E)) : EveryC4Rainbow (selectedEdges E I) color := by
  intro v hv he
  exact hrain v hv (fun i => selectedEdges_subset E I (he i))

theorem selectedEdges_properties {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) {I : Finset (EdgeVertex E)}
    (hI : (conflictGraph E color).IsIndepSet (I : Set (EdgeVertex E))) :
    selectedEdges E I ⊆ allEdges n ∧
      (selectedEdges E I).card = I.card ∧
      ProperOn (selectedEdges E I) color ∧
      EveryC4Rainbow (selectedEdges E I) color := by
  exact ⟨(selectedEdges_subset E I).trans hE, selectedEdges_card E I,
    selectedEdges_proper hI, selectedEdges_rainbow hrain I⟩

end Submissions.E810ProperExtraction.Conflict

namespace Submissions.E810ProperExtraction.ConflictCount

open Finset
open Submissions.E810WedgeBound.WedgeBound
open Submissions.E810ProperExtraction.Conflict

theorem shared_representation {n : ℕ} {e f : Fin n × Fin n}
    (he : e.1 < e.2) (hf : f.1 < f.2) (hne : e ≠ f)
    (hshare : SharesEndpoint e f) :
    ∃ x y z : Fin n, y ≠ z ∧ edge x y = e ∧ edge x z = f := by
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  change a < b at he
  change c < d at hf
  rcases hshare with h | h | h | h
  · change a = c at h
    subst c
    refine ⟨a, b, d, ?_, by simp [edge, he], by simp [edge, hf]⟩
    intro hbd
    exact hne (by simp [hbd])
  · change a = d at h
    subst d
    refine ⟨a, b, c, ?_, by simp [edge, he], ?_⟩
    · exact (ne_of_lt (hf.trans he)).symm
    · simp [edge, not_lt.mpr hf.le]
  · change b = c at h
    subst c
    refine ⟨b, a, d, ne_of_lt (he.trans hf), ?_, by simp [edge, hf]⟩
    simp [edge, not_lt.mpr he.le]
  · change b = d at h
    subst d
    refine ⟨b, a, c, ?_, ?_, ?_⟩
    · intro hac
      exact hne (by simp [hac])
    · simp [edge, not_lt.mpr he.le]
    · simp [edge, not_lt.mpr hf.le]

def wedgeToEdge {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n)
    (w : {t // t ∈ monochromaticWedges E color}) : Sym2 (EdgeVertex E) :=
  s(⟨edge w.1.1 w.1.2.1, (Finset.mem_filter.mp w.2).2.2.1⟩,
    ⟨edge w.1.1 w.1.2.2, (Finset.mem_filter.mp w.2).2.2.2.1⟩)

theorem conflictCount_le_wedges {n : ℕ} (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) (hE : E ⊆ allEdges n) :
    (conflictGraph E color).edgeFinset.card ≤ (monochromaticWedges E color).card := by
  classical
  have hsub : (conflictGraph E color).edgeFinset ⊆
      Finset.univ.image (wedgeToEdge E color) := by
    intro t ht
    rcases t with ⟨e, f⟩
    have hadj := SimpleGraph.mem_edgeFinset.mp ht
    have hcf := conflictGraph_adj_iff.mp hadj
    have he := (Finset.mem_filter.mp (hE e.2)).2
    have hf := (Finset.mem_filter.mp (hE f.2)).2
    have hne : e.1 ≠ f.1 := fun h => hcf.1 (Subtype.ext h)
    obtain ⟨x, y, z, hyz, hxy, hxz⟩ := shared_representation he hf hne hcf.2.1
    have hxyE : edge x y ∈ E := by rw [hxy]; exact e.2
    have hxzE : edge x z ∈ E := by rw [hxz]; exact f.2
    have hc : color (edge x y) = color (edge x z) := by
      rw [hxy, hxz]
      exact hcf.2.2
    by_cases hlt : y < z
    · have hw : (x, y, z) ∈ monochromaticWedges E color :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hxyE, hxzE, hc⟩
      refine Finset.mem_image.mpr ⟨⟨(x, y, z), hw⟩, Finset.mem_univ _, ?_⟩
      have heq : (⟨edge x y, hxyE⟩ : EdgeVertex E) = e := Subtype.ext hxy
      have hfq : (⟨edge x z, hxzE⟩ : EdgeVertex E) = f := Subtype.ext hxz
      change s(⟨edge x y, _⟩, ⟨edge x z, _⟩) = s(e, f)
      rw [heq, hfq]
    · have hlt' : z < y := lt_of_le_of_ne (le_of_not_gt hlt) hyz.symm
      have hw : (x, z, y) ∈ monochromaticWedges E color :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt', hxzE, hxyE, hc.symm⟩
      refine Finset.mem_image.mpr ⟨⟨(x, z, y), hw⟩, Finset.mem_univ _, ?_⟩
      have heq : (⟨edge x y, hxyE⟩ : EdgeVertex E) = e := Subtype.ext hxy
      have hfq : (⟨edge x z, hxzE⟩ : EdgeVertex E) = f := Subtype.ext hxz
      change s(⟨edge x z, _⟩, ⟨edge x y, _⟩) = s(e, f)
      rw [heq, hfq]
      exact Sym2.eq_swap
  calc
    (conflictGraph E color).edgeFinset.card ≤
        (Finset.univ.image (wedgeToEdge E color)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset {t // t ∈ monochromaticWedges E color}).card :=
      Finset.card_image_le
    _ = (monochromaticWedges E color).card := by simp

end Submissions.E810ProperExtraction.ConflictCount

namespace Submissions.E810ProperExtraction.Extraction

open Finset
open Submissions.E810WedgeBound.WedgeBound
open Submissions.E810ProperExtraction.Conflict
open Submissions.E810ProperExtraction.ConflictCount
open Submissions.E810ProperExtraction.IndependentBound

/-- Extract a proper subgraph, keeping the original colors and rainbow cycles.
The inequality records the density cost without division or positivity cases. -/
theorem proof (n : ℕ) (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) :
    ∃ F : Finset (Fin n × Fin n), F ⊆ E ∧ F ⊆ allEdges n ∧
      ProperOn F color ∧ EveryC4Rainbow F color ∧
      E.card ^ 2 ≤ F.card * (E.card + 2 * (allEdges n).card) := by
  classical
  obtain ⟨I, hI, hsize⟩ := exists_independent_bound (conflictGraph E color)
  have hcount := (conflictCount_le_wedges E color hE).trans
    (Submissions.E810WedgeBound.WedgeBound.proof n E color hE hrain)
  refine ⟨selectedEdges E I, selectedEdges_subset E I,
    (selectedEdges_subset E I).trans hE, selectedEdges_proper hI,
    selectedEdges_rainbow hrain I, ?_⟩
  have hs : E.card ^ 2 ≤ I.card *
      (E.card + 2 * (conflictGraph E color).edgeFinset.card) := by
    simpa only [EdgeVertex, Fintype.card_coe] using hsize
  rw [selectedEdges_card]
  exact hs.trans (Nat.mul_le_mul_left I.card
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hcount) E.card))

theorem allEdges_card_le_square (n : ℕ) : (allEdges n).card ≤ n ^ 2 := by
  calc
    (allEdges n).card ≤ (Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).card :=
      Finset.card_filter_le _ _
    _ = n ^ 2 := by simp [pow_two]

/-- A uniform positive-density witness has a uniform positive-density proper
subgraph. The constant is deliberately loose; no asymptotic hypothesis is lost. -/
theorem density (n : ℕ) (E : Finset (Fin n × Fin n))
    (color : Fin n × Fin n → Fin n) (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) (ε : ℝ) (hε : 0 < ε)
    (hd : ε * (n : ℝ) ^ 2 ≤ (E.card : ℝ)) :
    ∃ F : Finset (Fin n × Fin n), F ⊆ E ∧ F ⊆ allEdges n ∧
      ProperOn F color ∧ EveryC4Rainbow F color ∧
      (ε ^ 2 / 3) * (n : ℝ) ^ 2 ≤ (F.card : ℝ) := by
  obtain ⟨F, hFE, hFA, hproper, hrF, hsize⟩ := proof n E color hE hrain
  refine ⟨F, hFE, hFA, hproper, hrF, ?_⟩
  have ha := allEdges_card_le_square n
  have he := (Finset.card_le_card hE).trans ha
  have hden : E.card + 2 * (allEdges n).card ≤ 3 * n ^ 2 := by omega
  have hsize' : E.card ^ 2 ≤ 3 * F.card * n ^ 2 := by
    have hh := hsize.trans (Nat.mul_le_mul_left F.card hden)
    nlinarith only [hh]
  have hreal : (E.card : ℝ) ^ 2 ≤ 3 * (F.card : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast hsize'
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnn : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hsquare : (ε * (n : ℝ) ^ 2) ^ 2 ≤ (E.card : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hd
  apply (mul_le_mul_iff_left₀ hnn).mp
  nlinarith only [hreal, hsquare]

end Submissions.E810ProperExtraction.Extraction

namespace Submissions.E810ProperExtraction.Equivalence

open Filter Finset
open Submissions.E810WedgeBound.WedgeBound
open Submissions.E810ProperExtraction.Conflict

/-- The full root's existential-host, uniform-density, all-large-n proposition. -/
abbrev DenseRainbow : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    ∃ E : Finset (Fin n × Fin n), E ⊆ allEdges n ∧
      ε * (n : ℝ) ^ 2 ≤ (E.card : ℝ) ∧
      ∃ color : Fin n × Fin n → Fin n, EveryC4Rainbow E color

/-- The same quantifiers with a proper coloring required on the selected graph. -/
abbrev DenseProperRainbow : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    ∃ E : Finset (Fin n × Fin n), E ⊆ allEdges n ∧
      ε * (n : ℝ) ^ 2 ≤ (E.card : ℝ) ∧
      ∃ color : Fin n × Fin n → Fin n, ProperOn E color ∧ EveryC4Rainbow E color

theorem proof : DenseRainbow ↔ DenseProperRainbow := by
  constructor
  · rintro ⟨ε, hε, hevent⟩
    refine ⟨ε ^ 2 / 3, by positivity, ?_⟩
    apply hevent.mono
    intro n hn
    obtain ⟨E, hE, hd, color, hrain⟩ := hn
    obtain ⟨F, _, hFA, hproper, hrF, hdF⟩ :=
      Submissions.E810ProperExtraction.Extraction.density n E color hE hrain ε hε hd
    exact ⟨F, hFA, hdF, color, hproper, hrF⟩
  · rintro ⟨ε, hε, hevent⟩
    refine ⟨ε, hε, hevent.mono ?_⟩
    rintro n ⟨E, hE, hd, color, _, hrain⟩
    exact ⟨E, hE, hd, color, hrain⟩

end Submissions.E810ProperExtraction.Equivalence

/-
Source-only draft. This file was not built or executed by its authoring
subagent. It uses the exact existing ordered-edge encoding and predicates;
there are no canonical-target imports, admitted proofs, or IO tactics.
-/

namespace Submissions.E810Balanced.DoubleCover

open Finset
open Submissions.E810WedgeBound.WedgeBound
open Submissions.E810ProperExtraction.Conflict

/-- The symmetric relation obtained by putting both orientations of each edge
into a matrix on two separate copies of the original vertex set. -/
def doubleCover {n : ℕ} (E : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) :=
  E ∪ E.image Prod.swap

/-- Properness on matrix rows and columns, with a generic finite palette. -/
def MatrixProper {n q : ℕ} (R : Finset (Fin n × Fin n))
    (c : Fin n × Fin n → Fin q) : Prop :=
  ∀ p ∈ R, ∀ s ∈ R, p ≠ s →
    (p.1 = s.1 ∨ p.2 = s.2) → c p ≠ c s

/-- Every ordinary matrix rectangle has four different cyclic edge colors. -/
def RectRainbow {n q : ℕ} (R : Finset (Fin n × Fin n))
    (c : Fin n × Fin n → Fin q) : Prop :=
  ∀ x z y w : Fin n, x ≠ z → y ≠ w →
    (x, y) ∈ R → (z, y) ∈ R → (z, w) ∈ R → (x, w) ∈ R →
    Function.Injective
      (![c (x, y), c (z, y), c (z, w), c (x, w)] : Fin 4 → Fin q)

theorem edge_eq_of_mem {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ allEdges n) {p : Fin n × Fin n} (hp : p ∈ E) :
    edge p.1 p.2 = p := by
  rcases p with ⟨u, v⟩
  have huv : u < v := (Finset.mem_filter.mp (hE hp)).2
  simp [edge, huv]

theorem doubleCover_disjoint {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ allEdges n) : Disjoint E (E.image Prod.swap) := by
  apply Finset.disjoint_left.mpr
  intro e he hswap
  rcases Finset.mem_image.mp hswap with ⟨f, hf, hfe⟩
  have he_lt : e.1 < e.2 := (Finset.mem_filter.mp (hE he)).2
  have hf_lt : f.1 < f.2 := (Finset.mem_filter.mp (hE hf)).2
  have hfst : f.2 = e.1 := congrArg Prod.fst hfe
  have hsnd : f.1 = e.2 := congrArg Prod.snd hfe
  rw [hfst, hsnd] at hf_lt
  exact lt_asymm he_lt hf_lt

theorem doubleCover_card {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ allEdges n) : (doubleCover E).card = 2 * E.card := by
  unfold doubleCover
  rw [Finset.card_union_of_disjoint (doubleCover_disjoint hE),
    Finset.card_image_of_injective E Prod.swap_injective]
  omega

theorem mem_doubleCover_iff {n : ℕ} {E : Finset (Fin n × Fin n)}
    (hE : E ⊆ allEdges n) (u v : Fin n) :
    (u, v) ∈ doubleCover E ↔ edge u v ∈ E := by
  change (u, v) ∈ E ∪ E.image Prod.swap ↔ edge u v ∈ E
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · rw [edge_eq_of_mem hE h]
      exact h
    · rcases Finset.mem_image.mp h with ⟨f, hf, hfe⟩
      have hfst : f.2 = u := congrArg Prod.fst hfe
      have hsnd : f.1 = v := congrArg Prod.snd hfe
      have hnormal : edge f.2 f.1 = f := by
        rw [edge_comm, edge_eq_of_mem hE hf]
      rw [hfst, hsnd] at hnormal
      rw [hnormal]
      exact hf
  · intro h
    by_cases huv : u < v
    · apply Finset.mem_union.mpr
      exact Or.inl (by simpa [edge, huv] using h)
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_image.mpr
      refine ⟨(v, u), ?_, rfl⟩
      simpa [edge, huv] using h

theorem doubleCover_rainbow {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hE : E ⊆ allEdges n)
    (hrain : EveryC4Rainbow E color) :
    RectRainbow (doubleCover E) (fun p => color (edge p.1 p.2)) := by
  intro x z y w hxz hyw hxy hzy hzw hxw
  have hxyE : edge x y ∈ E := (mem_doubleCover_iff hE x y).mp hxy
  have hzyE : edge z y ∈ E := (mem_doubleCover_iff hE z y).mp hzy
  have hzwE : edge z w ∈ E := (mem_doubleCover_iff hE z w).mp hzw
  have hxwE : edge x w ∈ E := (mem_doubleCover_iff hE x w).mp hxw
  have hxy_ne : x ≠ y := endpoints_ne hE hxyE
  have hzy_ne : z ≠ y := endpoints_ne hE hzyE
  have hzw_ne : z ≠ w := endpoints_ne hE hzwE
  have hxw_ne : x ≠ w := endpoints_ne hE hxwE
  let v : Fin 4 → Fin n := ![x, y, z, w]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have he : ∀ i : Fin 4,
      edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩) ∈ E := by
    intro i
    fin_cases i <;> simp_all [v, edge_comm]
  have hi := hrain v hv he
  have hcolors :
      (fun i : Fin 4 => color (edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩))) =
        (![color (edge x y), color (edge z y), color (edge z w),
          color (edge x w)] : Fin 4 → Fin n) := by
    funext i
    fin_cases i <;> simp [v, edge_comm]
  rw [hcolors] at hi
  exact hi

theorem doubleCover_proper {n : ℕ} {E : Finset (Fin n × Fin n)}
    {color : Fin n × Fin n → Fin n} (hE : E ⊆ allEdges n)
    (hproper : ProperOn E color) :
    MatrixProper (doubleCover E) (fun p => color (edge p.1 p.2)) := by
  intro p hp s hs hne hshare
  rcases p with ⟨x, y⟩
  rcases s with ⟨z, w⟩
  have hxy : edge x y ∈ E := (mem_doubleCover_iff hE x y).mp hp
  have hzw : edge z w ∈ E := (mem_doubleCover_iff hE z w).mp hs
  rcases hshare with hrow | hcol
  · change x = z at hrow
    subst z
    have hyw : y ≠ w := by
      intro h
      apply hne
      cases h
      rfl
    exact properOn_incident hproper hxy hzw hyw
  · change y = w at hcol
    subst w
    have hxz : x ≠ z := by
      intro h
      apply hne
      cases h
      rfl
    have hyx : edge y x ∈ E := by
      rw [edge_comm y x]
      exact hxy
    have hyz : edge y z ∈ E := by
      rw [edge_comm y z]
      exact hzw
    have hc := properOn_incident hproper hyx hyz hxz
    rw [edge_comm y x, edge_comm y z] at hc
    exact hc

end Submissions.E810Balanced.DoubleCover

/-
Source-only draft of the reverse finite embedding. The authoring subagent
has not run Lean or a build on this file. The parent owns compilation and
verification. No canonical target is imported and no proof is admitted.
-/

namespace Submissions.E810Balanced.Embedding

open Finset
open Submissions.E810WedgeBound.WedgeBound
open Submissions.E810Balanced.DoubleCover

def left {n N : ℕ} (hsize : 2 * n ≤ N) (x : Fin n) : Fin N :=
  ⟨x.val, by have := x.isLt; omega⟩

def right {n N : ℕ} (hsize : 2 * n ≤ N) (y : Fin n) : Fin N :=
  ⟨n + y.val, by have := y.isLt; omega⟩

theorem left_injective {n N : ℕ} (hsize : 2 * n ≤ N) :
    Function.Injective (left hsize) := by
  intro x y hxy
  apply Fin.ext
  exact congrArg (fun z : Fin N => z.val) hxy

theorem right_injective {n N : ℕ} (hsize : 2 * n ≤ N) :
    Function.Injective (right hsize) := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  change n + x.val = n + y.val at hval
  omega

theorem left_lt_right {n N : ℕ} (hsize : 2 * n ≤ N)
    (x y : Fin n) : left hsize x < right hsize y := by
  change x.val < n + y.val
  have := x.isLt
  omega

theorem left_ne_right {n N : ℕ} (hsize : 2 * n ≤ N)
    (x y : Fin n) : left hsize x ≠ right hsize y :=
  ne_of_lt (left_lt_right hsize x y)

def edgeMap {n N : ℕ} (hsize : 2 * n ≤ N)
    (p : Fin n × Fin n) : Fin N × Fin N :=
  (left hsize p.1, right hsize p.2)

theorem edgeMap_injective {n N : ℕ} (hsize : 2 * n ≤ N) :
    Function.Injective (edgeMap hsize) := by
  intro p q hpq
  apply Prod.ext
  · exact left_injective hsize (congrArg Prod.fst hpq)
  · exact right_injective hsize (congrArg Prod.snd hpq)

def embedEdges {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) : Finset (Fin N × Fin N) :=
  R.image (edgeMap hsize)

theorem embedEdges_card {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) : (embedEdges hsize R).card = R.card := by
  unfold embedEdges
  exact Finset.card_image_of_injective R (edgeMap_injective hsize)

theorem embedEdges_subset {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) : embedEdges hsize R ⊆ allEdges N := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨p, _, rfl⟩
  apply Finset.mem_filter.mpr
  exact ⟨by simp [edgeMap], left_lt_right hsize p.1 p.2⟩

noncomputable def liftedColor {n N : ℕ} (hsize : 2 * n ≤ N) (hN : 0 < N)
    (c : Fin n × Fin n → Fin n) : Fin N × Fin N → Fin N :=
  Function.extend (edgeMap hsize) (fun p => left hsize (c p))
    (fun _ => ⟨0, hN⟩)

@[simp] theorem liftedColor_edgeMap {n N : ℕ} (hsize : 2 * n ≤ N)
    (hN : 0 < N) (c : Fin n × Fin n → Fin n) (p : Fin n × Fin n) :
    liftedColor hsize hN c (edgeMap hsize p) = left hsize (c p) := by
  unfold liftedColor
  exact (edgeMap_injective hsize).extend_apply
    (fun p => left hsize (c p)) (fun _ => ⟨0, hN⟩) p

@[simp] theorem edge_left_right {n N : ℕ} (hsize : 2 * n ≤ N)
    (x y : Fin n) :
    edge (left hsize x) (right hsize y) = edgeMap hsize (x, y) := by
  unfold edge
  rw [if_pos (left_lt_right hsize x y)]
  rfl

@[simp] theorem edge_right_left {n N : ℕ} (hsize : 2 * n ≤ N)
    (x y : Fin n) :
    edge (right hsize y) (left hsize x) = edgeMap hsize (x, y) := by
  rw [edge_comm]
  exact edge_left_right hsize x y

@[simp] theorem edgeMap_mem_iff {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    edgeMap hsize p ∈ embedEdges hsize R ↔ p ∈ R := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, hqp⟩
    have hqp' : q = p := edgeMap_injective hsize hqp
    simpa only [hqp'] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

@[simp] theorem edge_left_right_mem_iff {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) (x y : Fin n) :
    edge (left hsize x) (right hsize y) ∈ embedEdges hsize R ↔ (x, y) ∈ R := by
  rw [edge_left_right, edgeMap_mem_iff]

@[simp] theorem edge_right_left_mem_iff {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) (x y : Fin n) :
    edge (right hsize y) (left hsize x) ∈ embedEdges hsize R ↔ (x, y) ∈ R := by
  rw [edge_right_left, edgeMap_mem_iff]

theorem mem_embed_edge_iff {n N : ℕ} (hsize : 2 * n ≤ N)
    (R : Finset (Fin n × Fin n)) (u v : Fin N) :
    edge u v ∈ embedEdges hsize R ↔
      ∃ x y : Fin n, (x, y) ∈ R ∧
        ((u = left hsize x ∧ v = right hsize y) ∨
          (u = right hsize y ∧ v = left hsize x)) := by
  constructor
  · intro huvR
    rcases Finset.mem_image.mp huvR with ⟨⟨x, y⟩, hxy, he⟩
    by_cases huv : u < v
    · have hx : left hsize x = u := by
        have ht := congrArg Prod.fst he
        simpa [edgeMap, edge, huv] using ht
      have hy : right hsize y = v := by
        have ht := congrArg Prod.snd he
        simpa [edgeMap, edge, huv] using ht
      exact ⟨x, y, hxy, Or.inl ⟨hx.symm, hy.symm⟩⟩
    · have hx : left hsize x = v := by
        have ht := congrArg Prod.fst he
        simpa [edgeMap, edge, huv] using ht
      have hy : right hsize y = u := by
        have ht := congrArg Prod.snd he
        simpa [edgeMap, edge, huv] using ht
      exact ⟨x, y, hxy, Or.inr ⟨hy.symm, hx.symm⟩⟩
  · rintro ⟨x, y, hxy, hxyuv⟩
    rcases hxyuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (edge_left_right_mem_iff hsize R x y).mpr hxy
    · exact (edge_right_left_mem_iff hsize R x y).mpr hxy

theorem edge_from_left {n N : ℕ} (hsize : 2 * n ≤ N)
    {R : Finset (Fin n × Fin n)} {x : Fin n} {v : Fin N}
    (hv : edge (left hsize x) v ∈ embedEdges hsize R) :
    ∃ y : Fin n, v = right hsize y ∧ (x, y) ∈ R := by
  rcases (mem_embed_edge_iff hsize R (left hsize x) v).mp hv with
    ⟨a, b, hab, hends⟩
  rcases hends with ⟨hxa, hvb⟩ | ⟨hxb, hva⟩
  · have hxa' : x = a := left_injective hsize hxa
    subst a
    exact ⟨b, hvb, hab⟩
  · exact False.elim (left_ne_right hsize x b hxb)

theorem edge_from_right {n N : ℕ} (hsize : 2 * n ≤ N)
    {R : Finset (Fin n × Fin n)} {y : Fin n} {v : Fin N}
    (hv : edge (right hsize y) v ∈ embedEdges hsize R) :
    ∃ x : Fin n, v = left hsize x ∧ (x, y) ∈ R := by
  rcases (mem_embed_edge_iff hsize R (right hsize y) v).mp hv with
    ⟨a, b, hab, hends⟩
  rcases hends with ⟨hya, hvb⟩ | ⟨hyb, hva⟩
  · exact False.elim (left_ne_right hsize a y hya.symm)
  · have hyb' : y = b := right_injective hsize hyb
    subst b
    exact ⟨a, hva, hab⟩

theorem embed_rainbow {n N : ℕ} (hsize : 2 * n ≤ N) (hN : 0 < N)
    (R : Finset (Fin n × Fin n)) (c : Fin n × Fin n → Fin n)
    (hr : RectRainbow R c) :
    EveryC4Rainbow (embedEdges hsize R) (liftedColor hsize hN c) := by
  intro v hv he
  have h0 : edge (v 0) (v 1) ∈ embedEdges hsize R := by
    simpa using he (0 : Fin 4)
  have h1 : edge (v 1) (v 2) ∈ embedEdges hsize R := by
    simpa using he (1 : Fin 4)
  have h2 : edge (v 2) (v 3) ∈ embedEdges hsize R := by
    simpa using he (2 : Fin 4)
  have h3 : edge (v 3) (v 0) ∈ embedEdges hsize R := by
    simpa using he (3 : Fin 4)
  rcases (mem_embed_edge_iff hsize R (v 0) (v 1)).mp h0 with
    ⟨x, y, hxy, hstart⟩
  rcases hstart with ⟨hv0, hv1⟩ | ⟨hv0, hv1⟩
  · obtain ⟨z, hv2, hzy⟩ := edge_from_right hsize (R := R) (y := y)
      (v := v 2) (by simpa only [hv1] using h1)
    obtain ⟨w, hv3, hzw⟩ := edge_from_left hsize (R := R) (x := z)
      (v := v 3) (by simpa only [hv2] using h2)
    have hxw : (x, w) ∈ R := (edge_right_left_mem_iff hsize R x w).mp
      (by simpa only [hv3, hv0] using h3)
    have hxz : x ≠ z := by
      intro h
      have h02 : v 0 = v 2 := by rw [hv0, hv2, h]
      exact (by decide : (0 : Fin 4) ≠ 2) (hv h02)
    have hyw : y ≠ w := by
      intro h
      have h13 : v 1 = v 3 := by rw [hv1, hv3, h]
      exact (by decide : (1 : Fin 4) ≠ 3) (hv h13)
    let cols : Fin 4 → Fin n := ![c (x, y), c (z, y), c (z, w), c (x, w)]
    have hc : Function.Injective cols := hr x z y w hxz hyw hxy hzy hzw hxw
    have hseq :
        (fun i : Fin 4 => liftedColor hsize hN c
          (edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩))) =
          (fun i : Fin 4 => left hsize (cols i)) := by
      funext i
      fin_cases i <;> simp [cols, hv0, hv1, hv2, hv3]
    rw [hseq]
    exact (left_injective hsize).comp hc
  · obtain ⟨w, hv2, hxw⟩ := edge_from_left hsize (R := R) (x := x)
      (v := v 2) (by simpa only [hv1] using h1)
    obtain ⟨z, hv3, hzw⟩ := edge_from_right hsize (R := R) (y := w)
      (v := v 3) (by simpa only [hv2] using h2)
    have hzy : (z, y) ∈ R := (edge_left_right_mem_iff hsize R z y).mp
      (by simpa only [hv3, hv0] using h3)
    have hxz : x ≠ z := by
      intro h
      have h13 : v 1 = v 3 := by rw [hv1, hv3, h]
      exact (by decide : (1 : Fin 4) ≠ 3) (hv h13)
    have hyw : y ≠ w := by
      intro h
      have h02 : v 0 = v 2 := by rw [hv0, hv2, h]
      exact (by decide : (0 : Fin 4) ≠ 2) (hv h02)
    let cols : Fin 4 → Fin n := ![c (x, y), c (z, y), c (z, w), c (x, w)]
    have hc : Function.Injective cols := hr x z y w hxz hyw hxy hzy hzw hxw
    let rev : Fin 4 → Fin 4 := ![0, 3, 2, 1]
    have hrev : Function.Injective rev := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [rev]
    have hseq :
        (fun i : Fin 4 => liftedColor hsize hN c
          (edge (v i) (v ⟨(i.val + 1) % 4, by omega⟩))) =
          (fun i : Fin 4 => left hsize (cols (rev i))) := by
      funext i
      fin_cases i <;> simp [cols, rev, hv0, hv1, hv2, hv3]
    rw [hseq]
    exact (left_injective hsize).comp (hc.comp hrev)

theorem embed_exists {n N : ℕ} (hsize : 2 * n ≤ N) (hN : 0 < N)
    (R : Finset (Fin n × Fin n)) (c : Fin n × Fin n → Fin n)
    (hr : RectRainbow R c) :
    ∃ F : Finset (Fin N × Fin N), F ⊆ allEdges N ∧ F.card = R.card ∧
      ∃ color : Fin N × Fin N → Fin N, EveryC4Rainbow F color := by
  exact ⟨embedEdges hsize R, embedEdges_subset hsize R, embedEdges_card hsize R,
    liftedColor hsize hN c, embed_rainbow hsize hN R c hr⟩

end Submissions.E810Balanced.Embedding

namespace Submissions.E810Balanced.Forward

open Filter Finset
open Submissions.E810WedgeBound.WedgeBound
open Submissions.E810ProperExtraction.Conflict
open Submissions.E810Balanced.DoubleCover

/-- Balanced parts of size n, a palette of size n, and one uniform positive
density on every sufficiently large n. Matrix rectangles are ordinary C4s. -/
abbrev DenseBalanced : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
    ∃ R : Finset (Fin n × Fin n), δ * (n : ℝ) ^ 2 ≤ (R.card : ℝ) ∧
      ∃ c : Fin n × Fin n → Fin n, MatrixProper R c ∧ RectRainbow R c

theorem root_to_balanced
    (h : Submissions.E810ProperExtraction.Equivalence.DenseRainbow) :
    DenseBalanced := by
  obtain ⟨ε, hε, hevent⟩ :=
    Submissions.E810ProperExtraction.Equivalence.proof.mp h
  refine ⟨2 * ε, by positivity, hevent.mono ?_⟩
  rintro n ⟨E, hE, hd, color, hproper, hrain⟩
  refine ⟨doubleCover E, ?_, (fun p => color (edge p.1 p.2)),
    doubleCover_proper hE hproper, doubleCover_rainbow hE hrain⟩
  have hc : ((doubleCover E).card : ℝ) = 2 * (E.card : ℝ) := by
    exact_mod_cast doubleCover_card hE
  rw [hc]
  nlinarith

end Submissions.E810Balanced.Forward

namespace Submissions.E810Balanced.Equivalence

open Filter Finset
open Submissions.E810ProperExtraction.Equivalence
open Submissions.E810Balanced.DoubleCover
open Submissions.E810Balanced.Forward

theorem balanced_to_root (h : DenseBalanced) : DenseRainbow := by
  obtain ⟨δ, hδ, hevent⟩ := h
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨δ / 9, by positivity, Filter.eventually_atTop.mpr ?_⟩
  refine ⟨max 2 (2 * n₀), ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have htail : n₀ ≤ N / 2 := by
    have := le_trans (le_max_right 2 (2 * n₀)) hN
    omega
  obtain ⟨R, hd, c, _, hr⟩ := hn₀ (N / 2) htail
  have hsize : 2 * (N / 2) ≤ N := by omega
  have hpos : 0 < N := by omega
  obtain ⟨F, hF, hcard, color, hcolor⟩ :=
    Submissions.E810Balanced.Embedding.embed_exists hsize hpos R c hr
  refine ⟨F, hF, ?_, color, hcolor⟩
  have hthird : N ≤ 3 * (N / 2) := by omega
  have hreal : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by
    exact_mod_cast hthird
  have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ (N : ℝ) by positivity) hreal
  have hscaled := mul_le_mul_of_nonneg_left hsq (le_of_lt hδ)
  have hcardreal : (F.card : ℝ) = (R.card : ℝ) := by
    exact_mod_cast hcard
  rw [hcardreal]
  nlinarith

theorem proof : DenseRainbow ↔ DenseBalanced :=
  ⟨root_to_balanced, balanced_to_root⟩

end Submissions.E810Balanced.Equivalence

namespace Submissions.E810BalancedReduction.Proof

theorem proof :
    Submissions.E810ProperExtraction.Equivalence.DenseRainbow ↔
      Submissions.E810Balanced.Forward.DenseBalanced :=
  Submissions.E810Balanced.Equivalence.proof

end Submissions.E810BalancedReduction.Proof
