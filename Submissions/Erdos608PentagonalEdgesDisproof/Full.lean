import Mathlib
/-! Flattened from primateria/erdos608 commit b50849234b8de6cb5c642b5cb0479cab2e9e9908. -/

/-! Source module: Erdos608/Statement.lean -/
/-
Erdős problem 608 — statement (Phase-2 target #1).

Site statement (https://www.erdosproblems.com/608, last edited 2025-10-25):
"Let G be a graph with n vertices and > n²/4 many edges. Are there at least
(2/9)n² edges of G which are contained in a C₅?"

DISPROVED by the Füredi–Maleki construction, described in Grzesik–Hu–Volec,
"Minimum number of edges that occur in odd cycles" (arXiv:1605.09055): graphs
with > n²/4 edges and at most ((2+√2)/16)n² + O(n) pentagonal edges.

Design notes in STATEMENT.md alongside this file. All inequalities are cleared
to naturals; the vertex type is `Fin n`.
-/

namespace Erdos608

/-- `OnC5 G e`: the edge `e` lies on a pentagon of `G` — there are five
pairwise-distinct vertices, adjacent in cyclic order, such that `e` is one of
the five cycle edges. -/
def OnC5 {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∃ a b c d f : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ f ∧ c ≠ d ∧ c ≠ f ∧
    d ≠ f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d f ∧ G.Adj f a ∧
    (e = s(a, b) ∨ e = s(b, c) ∨ e = s(c, d) ∨ e = s(d, f) ∨ e = s(f, a))

/-- The pentagonal edges of `G`. -/
def pentEdges {V : Type*} (G : SimpleGraph V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | OnC5 G e}

/-- Erdős 608 in its intended (implicitly asymptotic) reading, denominators
cleared: for all sufficiently large `n`, every graph on `n` vertices with
more than `n²/4` edges has at least `(2/9)n²` edges contained in a `C₅`.
(This is the DISPROVED conjecture.)

The word-for-word `∀ n` reading is deliberately NOT used: it is degenerately
false at `n = 3` (`K₃` has `> 9/4` edges and no possible pentagon), which
would let a vacuous two-line proof "disprove" the problem. The eventually-form
below is the reading under which the site's DISPROVED verdict cites the
Füredi–Maleki construction. See STATEMENT.md §Design decisions. -/
def Conjecture : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (pentEdges G).ncard

/-
The campaign targets `disproof : ¬ Conjecture` and `strong_disproof` are
PROVED in `Erdos608/Main.lean` (statement bodies identical to the stubs
originally frozen here; stubs retired 2026-07-29 with Morris's approval —
see runs/phase2/erdos-608/{STATEMENT.md,CONSTRUCTION.md}).
-/

end Erdos608

/-! Source module: Erdos608/Construction.lean -/
/-
Erdős 608 — the witness construction, a rational specialization of the
Füredi–Maleki template (lemma-ladder items L1,
L2, L3b of runs/phase2/erdos-608/CONSTRUCTION.md).

`FM m` is a non-balanced blowup of the path A–B–C–D with a clique on D:
parts of size |A| = 4m, |B| = 7m, |C| = 7m, |D| = 10m (so n = 28m); edges are
all A×B, B×C, C×D pairs plus all pairs inside D.  A, B, C are independent
sets; no A×C, A×D, B×D edges.

Provided here:
* L1 : `V`, `FM`, `card_V` (`Fintype.card (V m) = 28m`).
* L2 : per-part degree lemmas, `sum_degrees`, `card_edgeFinset`, and
  `edgeSet_ncard` (`(FM m).edgeSet.ncard = 197m² − 5m`).
* L3b: `onC5_dd`, `onC5_cd`, `onC5_bc` — every D×D, C×D, B×C edge lies on a
  pentagon (for `1 ≤ m`).
-/

namespace Erdos608

/-! ## L1: the vertex type and the graph -/

/-- Vertex type of the Füredi–Maleki graph: the four blowup classes
A (`4m`), B (`7m`), C (`7m`), D (`10m`) as a nested sum. -/
abbrev V (m : ℕ) := Fin (4*m) ⊕ Fin (7*m) ⊕ Fin (7*m) ⊕ Fin (10*m)

/-- Position of a vertex along the pattern path a–b–c–d (A ↦ 0, …, D ↦ 3). -/
def tag {m : ℕ} : V m → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

@[simp] lemma tag_A {m : ℕ} (a : Fin (4*m)) : tag (Sum.inl a : V m) = 0 := rfl
@[simp] lemma tag_B {m : ℕ} (b : Fin (7*m)) : tag (Sum.inr (Sum.inl b) : V m) = 1 := rfl
@[simp] lemma tag_C {m : ℕ} (c : Fin (7*m)) :
    tag (Sum.inr (Sum.inr (Sum.inl c)) : V m) = 2 := rfl
@[simp] lemma tag_D {m : ℕ} (d : Fin (10*m)) :
    tag (Sum.inr (Sum.inr (Sum.inr d)) : V m) = 3 := rfl

/-- The witness graph — a rational specialization of the Füredi–Maleki
template: two distinct vertices are adjacent iff their
part tags are consecutive on the path (A–B, B–C, C–D) or both lie in D.
Since distinct parts have distinct tags, the `x ≠ y` conjunct is redundant on
the cross-part branches and encodes "adjacent iff distinct" inside D. -/
def FM (m : ℕ) : SimpleGraph (V m) where
  Adj x y := (tag y = tag x + 1 ∨ tag x = tag y + 1 ∨ (tag x = 3 ∧ tag y = 3)) ∧ x ≠ y
  symm := by
    rintro x y ⟨ht, hne⟩
    exact ⟨by tauto, hne.symm⟩
  loopless := by
    rintro x ⟨-, hne⟩
    exact hne rfl

/-- Definitional unfolding of `(FM m).Adj`. -/
lemma FM_adj {m : ℕ} {x y : V m} :
    (FM m).Adj x y ↔
      (tag y = tag x + 1 ∨ tag x = tag y + 1 ∨ (tag x = 3 ∧ tag y = 3)) ∧ x ≠ y :=
  Iff.rfl

instance FM.adjDecidable (m : ℕ) : DecidableRel ((FM m).Adj) := fun x y =>
  decidable_of_iff _ (FM_adj (m := m) (x := x) (y := y)).symm

lemma card_V (m : ℕ) : Fintype.card (V m) = 28*m := by
  simp only [V, Fintype.card_sum, Fintype.card_fin]
  omega

/-! ## Adjacency and disequality helpers (raw-constructor form) -/

lemma ne_DD {m : ℕ} {d d' : Fin (10*m)} (h : d ≠ d') :
    (Sum.inr (Sum.inr (Sum.inr d)) : V m) ≠ Sum.inr (Sum.inr (Sum.inr d')) := by
  simp [h]

lemma adj_AB {m : ℕ} (a : Fin (4*m)) (b : Fin (7*m)) :
    (FM m).Adj (Sum.inl a) (Sum.inr (Sum.inl b)) :=
  ⟨Or.inl rfl, by simp⟩

lemma adj_BC {m : ℕ} (b : Fin (7*m)) (c : Fin (7*m)) :
    (FM m).Adj (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inr (Sum.inl c))) :=
  ⟨Or.inl rfl, by simp⟩

lemma adj_CD {m : ℕ} (c : Fin (7*m)) (d : Fin (10*m)) :
    (FM m).Adj (Sum.inr (Sum.inr (Sum.inl c))) (Sum.inr (Sum.inr (Sum.inr d))) :=
  ⟨Or.inl rfl, by simp⟩

lemma adj_DD {m : ℕ} {d d' : Fin (10*m)} (h : d ≠ d') :
    (FM m).Adj (Sum.inr (Sum.inr (Sum.inr d))) (Sum.inr (Sum.inr (Sum.inr d'))) :=
  ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ne_DD h⟩

/-! ## L2: edge count via the degree sum -/

/-- Embedding of part A into the vertex type. -/
def eA (m : ℕ) : Fin (4*m) ↪ V m :=
  ⟨fun a => Sum.inl a, fun _ _ h => by simpa using h⟩

/-- Embedding of part B into the vertex type. -/
def eB (m : ℕ) : Fin (7*m) ↪ V m :=
  ⟨fun b => Sum.inr (Sum.inl b), fun _ _ h => by simpa using h⟩

/-- Embedding of part C into the vertex type. -/
def eC (m : ℕ) : Fin (7*m) ↪ V m :=
  ⟨fun c => Sum.inr (Sum.inr (Sum.inl c)), fun _ _ h => by simpa using h⟩

/-- Embedding of part D into the vertex type. -/
def eD (m : ℕ) : Fin (10*m) ↪ V m :=
  ⟨fun d => Sum.inr (Sum.inr (Sum.inr d)), fun _ _ h => by simpa using h⟩

@[simp] lemma eA_apply {m : ℕ} (a : Fin (4*m)) : eA m a = Sum.inl a := rfl
@[simp] lemma eB_apply {m : ℕ} (b : Fin (7*m)) : eB m b = Sum.inr (Sum.inl b) := rfl
@[simp] lemma eC_apply {m : ℕ} (c : Fin (7*m)) :
    eC m c = Sum.inr (Sum.inr (Sum.inl c)) := rfl
@[simp] lemma eD_apply {m : ℕ} (d : Fin (10*m)) :
    eD m d = Sum.inr (Sum.inr (Sum.inr d)) := rfl

lemma neighborFinset_A (m : ℕ) (a : Fin (4*m)) :
    (FM m).neighborFinset (Sum.inl a) = Finset.univ.map (eB m) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj]

lemma neighborFinset_B (m : ℕ) (b : Fin (7*m)) :
    (FM m).neighborFinset (Sum.inr (Sum.inl b)) =
      Finset.univ.map (eA m) ∪ Finset.univ.map (eC m) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj]

lemma neighborFinset_C (m : ℕ) (c : Fin (7*m)) :
    (FM m).neighborFinset (Sum.inr (Sum.inr (Sum.inl c))) =
      Finset.univ.map (eB m) ∪ Finset.univ.map (eD m) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj]

lemma neighborFinset_D (m : ℕ) (d : Fin (10*m)) :
    (FM m).neighborFinset (Sum.inr (Sum.inr (Sum.inr d))) =
      Finset.univ.map (eC m) ∪
        (Finset.univ.map (eD m)).erase (Sum.inr (Sum.inr (Sum.inr d))) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj, ne_comm]

lemma disjoint_eA_eC (m : ℕ) :
    Disjoint (Finset.univ.map (eA m)) (Finset.univ.map (eC m)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨c, -, hc⟩ := Finset.mem_map.mp hy
  simp at hc

lemma disjoint_eB_eD (m : ℕ) :
    Disjoint (Finset.univ.map (eB m)) (Finset.univ.map (eD m)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨d, -, hd⟩ := Finset.mem_map.mp hy
  simp at hd

lemma disjoint_eC_eD (m : ℕ) :
    Disjoint (Finset.univ.map (eC m)) (Finset.univ.map (eD m)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨d, -, hd⟩ := Finset.mem_map.mp hy
  simp at hd

lemma degree_A (m : ℕ) (a : Fin (4*m)) : (FM m).degree (Sum.inl a) = 7*m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_A,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma degree_B (m : ℕ) (b : Fin (7*m)) :
    (FM m).degree (Sum.inr (Sum.inl b)) = 11*m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_B,
    Finset.card_union_of_disjoint (disjoint_eA_eC m), Finset.card_map, Finset.card_map,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

lemma degree_C (m : ℕ) (c : Fin (7*m)) :
    (FM m).degree (Sum.inr (Sum.inr (Sum.inl c))) = 17*m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_C,
    Finset.card_union_of_disjoint (disjoint_eB_eD m), Finset.card_map, Finset.card_map,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

lemma degree_D (m : ℕ) (d : Fin (10*m)) :
    (FM m).degree (Sum.inr (Sum.inr (Sum.inr d))) = 7*m + (10*m - 1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_D,
    Finset.card_union_of_disjoint
      ((disjoint_eC_eD m).mono_right (Finset.erase_subset _ _)),
    Finset.card_map, Finset.card_erase_of_mem (by simp), Finset.card_map,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]

lemma sum_degrees (m : ℕ) :
    ∑ v : V m, (FM m).degree v = 394 * m ^ 2 - 10 * m := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [degree_A, degree_B, degree_C, degree_D, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rcases m with - | k
  · simp
  · have h1 : 7 * (k + 1) + (10 * (k + 1) - 1) = 17 * k + 16 := by omega
    rw [h1]
    symm
    apply Nat.sub_eq_of_eq_add
    ring

lemma card_edgeFinset (m : ℕ) :
    (FM m).edgeFinset.card = 197 * m ^ 2 - 5 * m := by
  have h := (FM m).sum_degrees_eq_twice_card_edges
  rw [sum_degrees] at h
  have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  generalize m ^ 2 = t at h h1 ⊢
  omega

/-- **L2.** The Füredi–Maleki graph on `28m` vertices has `197m² − 5m` edges
(so `4e > n²` for `m ≥ 6`). -/
lemma edgeSet_ncard (m : ℕ) : (FM m).edgeSet.ncard = 197 * m ^ 2 - 5 * m := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset]

/-! ## L3b: pentagon witnesses -/

/-- In `Fin (10*m)` with `1 ≤ m` there are three distinct elements avoiding
any two given ones (|D| = 10m ≥ 10 ≥ 5). -/
lemma exists_three (m : ℕ) (hm : 1 ≤ m) (x y : Fin (10*m)) :
    ∃ p q r : Fin (10*m),
      p ≠ x ∧ p ≠ y ∧ q ≠ x ∧ q ≠ y ∧ r ≠ x ∧ r ≠ y ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  have hxy : ({x, y} : Finset (Fin (10*m))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have hcompl : 8 ≤ ({x, y}ᶜ : Finset (Fin (10*m))).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp
    (show 0 < ({x, y}ᶜ : Finset (Fin (10*m))).card by omega)
  obtain ⟨q, hq⟩ := Finset.card_pos.mp
    (show 0 < (({x, y}ᶜ : Finset (Fin (10*m))).erase p).card by
      rw [Finset.card_erase_of_mem hp]; omega)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp
    (show 0 < ((({x, y}ᶜ : Finset (Fin (10*m))).erase p).erase q).card by
      rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem hp]; omega)
  simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hp hq hr
  exact ⟨p, q, r, hp.1, hp.2, hq.2.1, hq.2.2, hr.2.2.1, hr.2.2.2,
    hq.1.symm, hr.2.1.symm, hr.1.symm⟩

/-- **L3b, D×D.** Every edge inside the clique D lies on a pentagon:
five distinct D-vertices form a `C₅`. -/
lemma onC5_dd (m : ℕ) (hm : 1 ≤ m) :
    ∀ x y : Fin (10*m), x ≠ y →
      Erdos608.OnC5 (FM m)
        s(Sum.inr (Sum.inr (Sum.inr x)), Sum.inr (Sum.inr (Sum.inr y))) := by
  intro x y hxy
  obtain ⟨p, q, r, hpx, hpy, hqx, hqy, hrx, hry, hpq, hpr, hqr⟩ :=
    exists_three m hm x y
  exact ⟨Sum.inr (Sum.inr (Sum.inr x)), Sum.inr (Sum.inr (Sum.inr y)),
    Sum.inr (Sum.inr (Sum.inr p)), Sum.inr (Sum.inr (Sum.inr q)),
    Sum.inr (Sum.inr (Sum.inr r)),
    ne_DD hxy, ne_DD hpx.symm, ne_DD hqx.symm, ne_DD hrx.symm,
    ne_DD hpy.symm, ne_DD hqy.symm, ne_DD hry.symm,
    ne_DD hpq, ne_DD hpr, ne_DD hqr,
    adj_DD hxy, adj_DD hpy.symm, adj_DD hpq, adj_DD hqr, adj_DD hrx,
    Or.inl rfl⟩

/-- **L3b, C×D.** Every C×D edge lies on a pentagon: `c, d₁, d₂, d₃, d₄` with
`d₁ = y` and `d₂ d₃ d₄` three further distinct D-vertices. -/
lemma onC5_cd (m : ℕ) (hm : 1 ≤ m) :
    ∀ (x : Fin (7*m)) (y : Fin (10*m)),
      Erdos608.OnC5 (FM m)
        s(Sum.inr (Sum.inr (Sum.inl x)), Sum.inr (Sum.inr (Sum.inr y))) := by
  intro x y
  obtain ⟨p, q, r, hpy, -, hqy, -, hry, -, hpq, hpr, hqr⟩ := exists_three m hm y y
  exact ⟨Sum.inr (Sum.inr (Sum.inl x)), Sum.inr (Sum.inr (Sum.inr y)),
    Sum.inr (Sum.inr (Sum.inr p)), Sum.inr (Sum.inr (Sum.inr q)),
    Sum.inr (Sum.inr (Sum.inr r)),
    by simp, by simp, by simp, by simp,
    ne_DD hpy.symm, ne_DD hqy.symm, ne_DD hry.symm,
    ne_DD hpq, ne_DD hpr, ne_DD hqr,
    adj_CD x y, adj_DD hpy.symm, adj_DD hpq, adj_DD hqr, (adj_CD x r).symm,
    Or.inl rfl⟩

/-- **L3b, B×C.** Every B×C edge lies on a pentagon: `b, c₁, d₁, d₂, c₂` with
`c₂ ≠ c₁` a second C-vertex and `d₁ ≠ d₂` two D-vertices. -/
lemma onC5_bc (m : ℕ) (hm : 1 ≤ m) :
    ∀ (x y : Fin (7*m)),
      Erdos608.OnC5 (FM m)
        s(Sum.inr (Sum.inl x), Sum.inr (Sum.inr (Sum.inl y))) := by
  intro x y
  obtain ⟨c₂, hc⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Fin (7*m)) by rw [Fintype.card_fin]; omega) y
  obtain ⟨d₁, d₂, hd⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card (Fin (10*m)) by rw [Fintype.card_fin]; omega)
  exact ⟨Sum.inr (Sum.inl x), Sum.inr (Sum.inr (Sum.inl y)),
    Sum.inr (Sum.inr (Sum.inr d₁)), Sum.inr (Sum.inr (Sum.inr d₂)),
    Sum.inr (Sum.inr (Sum.inl c₂)),
    by simp, by simp, by simp, by simp,
    by simp, by simp,
    by simp [Ne.symm hc],
    ne_DD hd,
    by simp, by simp,
    adj_BC x y, adj_CD y d₁, adj_DD hd, (adj_CD c₂ d₂).symm, (adj_BC x c₂).symm,
    Or.inl rfl⟩

end Erdos608

/-! Source module: Erdos608/PentCount.lean -/
/-
Erdős 608 — pentagonal edges of the Füredi–Maleki graph (lemma-ladder items
L3a and L4 of runs/phase2/erdos-608/CONSTRUCTION.md).

* L3a (`not_onC5_AB`): no pentagon of `FM m` meets part A; in particular no
  A×B edge lies on a pentagon.  Reduced to a finite tag computation
  (`tag_pentagon_no_zero`, 4⁵ cases by `decide`): adjacency forces
  consecutive tags or a loop step at 3, and a closed 5-walk on the pattern
  path 0–1–2–3-with-loop-at-3 uses an odd number of loop steps, hence visits
  3; a round trip 3 → 0 → 3 alone costs six non-loop steps — one more than a
  pentagon has.
* L4 (`pentEdges_ncard`): `(pentEdges (FM m)).ncard = 169·m² − 5·m` for
  `1 ≤ m`: the pentagonal edges are exactly the edges outside the A×B block
  (L3a gives ⊆, L3b's `onC5_bc`/`onC5_cd`/`onC5_dd` give ⊇), and the A×B
  block has `28·m²` edges.
-/

namespace Erdos608

/-! ## L3a: no pentagon meets part A -/

lemma tag_le_three {m : ℕ} (v : V m) : tag v ≤ 3 := by
  rcases v with a | b | c | d <;> simp

/-- `tag`, packaged as `Fin 4` (for `decide`-friendly statements). -/
def tagF {m : ℕ} (v : V m) : Fin 4 := ⟨tag v, by have := tag_le_three v; omega⟩

@[simp] lemma tagF_val {m : ℕ} (v : V m) : (tagF v).val = tag v := rfl

/-- Finite-arithmetic core of L3a: the five adjacency-shaped constraints of a
closed 5-walk on the tag pattern (path `0–1–2–3` with a loop at `3`) rule out
tag `0` at every position. -/
lemma tag_pentagon_no_zero :
    ∀ t₀ t₁ t₂ t₃ t₄ : Fin 4,
      (t₁.val = t₀.val + 1 ∨ t₀.val = t₁.val + 1 ∨ (t₀.val = 3 ∧ t₁.val = 3)) →
      (t₂.val = t₁.val + 1 ∨ t₁.val = t₂.val + 1 ∨ (t₁.val = 3 ∧ t₂.val = 3)) →
      (t₃.val = t₂.val + 1 ∨ t₂.val = t₃.val + 1 ∨ (t₂.val = 3 ∧ t₃.val = 3)) →
      (t₄.val = t₃.val + 1 ∨ t₃.val = t₄.val + 1 ∨ (t₃.val = 3 ∧ t₄.val = 3)) →
      (t₀.val = t₄.val + 1 ∨ t₄.val = t₀.val + 1 ∨ (t₄.val = 3 ∧ t₀.val = 3)) →
      t₀.val ≠ 0 ∧ t₁.val ≠ 0 ∧ t₂.val ≠ 0 ∧ t₃.val ≠ 0 ∧ t₄.val ≠ 0 := by
  decide

/-- No vertex of a pentagon of `FM m` lies in part A (tag `0`). -/
lemma pent_tags_ne_zero {m : ℕ} {v₀ v₁ v₂ v₃ v₄ : V m}
    (h01 : (FM m).Adj v₀ v₁) (h12 : (FM m).Adj v₁ v₂) (h23 : (FM m).Adj v₂ v₃)
    (h34 : (FM m).Adj v₃ v₄) (h40 : (FM m).Adj v₄ v₀) :
    tag v₀ ≠ 0 ∧ tag v₁ ≠ 0 ∧ tag v₂ ≠ 0 ∧ tag v₃ ≠ 0 ∧ tag v₄ ≠ 0 :=
  tag_pentagon_no_zero (tagF v₀) (tagF v₁) (tagF v₂) (tagF v₃) (tagF v₄)
    (FM_adj.mp h01).1 (FM_adj.mp h12).1 (FM_adj.mp h23).1
    (FM_adj.mp h34).1 (FM_adj.mp h40).1

/-- **L3a.** No A×B edge of `FM m` lies on a pentagon. -/
lemma not_onC5_AB (m : ℕ) (a : Fin (4*m)) (b : Fin (7*m)) :
    ¬ Erdos608.OnC5 (FM m) s(Sum.inl a, Sum.inr (Sum.inl b)) := by
  rintro ⟨v₀, v₁, v₂, v₃, v₄, -, -, -, -, -, -, -, -, -, -,
    h01, h12, h23, h34, h40, hedge⟩
  obtain ⟨ht0, ht1, ht2, ht3, ht4⟩ := pent_tags_ne_zero h01 h12 h23 h34 h40
  have hmem : (Sum.inl a : V m) ∈ s(Sum.inl a, (Sum.inr (Sum.inl b) : V m)) :=
    Sym2.mem_iff.mpr (Or.inl rfl)
  rcases hedge with h | h | h | h | h <;> rw [h] at hmem <;>
      rcases Sym2.mem_iff.mp hmem with rfl | rfl
  · exact ht0 rfl
  · exact ht1 rfl
  · exact ht1 rfl
  · exact ht2 rfl
  · exact ht2 rfl
  · exact ht3 rfl
  · exact ht3 rfl
  · exact ht4 rfl
  · exact ht4 rfl
  · exact ht0 rfl

/-! ## L4: the A×B block and the pentagonal-edge count -/

/-- The A×B edges of `FM m`, as a `Finset` of `Sym2` pairs. -/
def ABblock (m : ℕ) : Finset (Sym2 (V m)) :=
  (Finset.univ ×ˢ Finset.univ).image
    (fun p : Fin (4*m) × Fin (7*m) => s(Sum.inl p.1, Sum.inr (Sum.inl p.2)))

lemma mem_ABblock (m : ℕ) (a : Fin (4*m)) (b : Fin (7*m)) :
    s(Sum.inl a, (Sum.inr (Sum.inl b) : V m)) ∈ ABblock m :=
  Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩

lemma mem_ABblock_iff {m : ℕ} {e : Sym2 (V m)} :
    e ∈ ABblock m ↔
      ∃ (a : Fin (4*m)) (b : Fin (7*m)), e = s(Sum.inl a, Sum.inr (Sum.inl b)) := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact mem_ABblock m a b

lemma ABpair_injective (m : ℕ) :
    Function.Injective (fun p : Fin (4*m) × Fin (7*m) =>
      s(Sum.inl p.1, (Sum.inr (Sum.inl p.2) : V m))) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain rfl := Sum.inl_injective h1
    obtain rfl := Sum.inl_injective (Sum.inr_injective h2)
    rfl
  · exact absurd h1 (by simp)

lemma ABblock_card (m : ℕ) : (ABblock m).card = 28 * m ^ 2 := by
  rw [ABblock, Finset.card_image_of_injective _ (ABpair_injective m),
    Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- Every edge of `FM m` outside the A×B block lies on a pentagon (the L3b
witnesses; the 16-way tag case analysis rules every other shape out). -/
lemma onC5_of_not_AB (m : ℕ) (hm : 1 ≤ m) (x y : V m)
    (he : (FM m).Adj x y) (hAB : s(x, y) ∉ ABblock m) :
    Erdos608.OnC5 (FM m) s(x, y) := by
  obtain ⟨htag, hne⟩ := FM_adj.mp he
  rcases x with a | b | c | d <;> rcases y with a' | b' | c' | d' <;>
      simp only [tag_A, tag_B, tag_C, tag_D] at htag <;>
      try (exfalso; omega)
  · exact absurd (mem_ABblock m a b') hAB
  · rw [Sym2.eq_swap] at hAB
    exact absurd (mem_ABblock m a' b) hAB
  · exact onC5_bc m hm b c'
  · rw [Sym2.eq_swap]
    exact onC5_bc m hm b' c
  · exact onC5_cd m hm c d'
  · rw [Sym2.eq_swap]
    exact onC5_cd m hm c' d
  · exact onC5_dd m hm d d' (by simpa using hne)

/-- The pentagonal edges of `FM m` are exactly the edges outside the A×B
block. -/
lemma pentEdges_FM (m : ℕ) (hm : 1 ≤ m) :
    pentEdges (FM m) = (FM m).edgeSet \ ↑(ABblock m) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [pentEdges, Set.mem_setOf_eq, Set.mem_diff, Finset.mem_coe]
    constructor
    · rintro ⟨he, hc5⟩
      refine ⟨he, fun hAB => ?_⟩
      obtain ⟨a, b, hab⟩ := mem_ABblock_iff.mp hAB
      rw [hab] at hc5
      exact not_onC5_AB m a b hc5
    · rintro ⟨he, hAB⟩
      -- `s(x, y) ∈ edgeSet` is definitionally `Adj x y` (`mem_edgeSet` is `Iff.rfl`)
      exact ⟨he, onC5_of_not_AB m hm x y he hAB⟩

/-- **L4.** The Füredi–Maleki graph has `169·m² − 5·m` pentagonal edges. -/
lemma pentEdges_ncard (m : ℕ) (hm : 1 ≤ m) :
    (Erdos608.pentEdges (FM m)).ncard = 169 * m ^ 2 - 5 * m := by
  have hsub : ↑(ABblock m) ⊆ (FM m).edgeSet := by
    intro e he
    obtain ⟨a, b, rfl⟩ := mem_ABblock_iff.mp (Finset.mem_coe.mp he)
    exact adj_AB a b
  rw [pentEdges_FM m hm, Set.ncard_diff hsub, edgeSet_ncard,
    Set.ncard_coe_finset, ABblock_card]
  have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  generalize m ^ 2 = t at h1 ⊢
  omega

end Erdos608

/-! Source module: Erdos608/Main.lean -/
/-
Erdős 608 — final assembly (lemma-ladder items L5 and L6 of
runs/phase2/erdos-608/CONSTRUCTION.md).

The witness graph `FM m` (a rational specialization of the Füredi–Maleki
template) lives on `V m` (a four-part sum type with
`28m` elements) while the campaign statements quantify over
`SimpleGraph (Fin n)`.  This module transports `FM m` to `Fin (28m)` along
the equivalence `toFin m := Fintype.equivFinOfCardEq (card_V m)` (as the
comap `FMFin m`), carries the two proved cardinalities across (the edge sets
correspond under the injection `Sym2.map (toFin m)`), and discharges the two
campaign targets:

* `disproof`        : `¬ Erdos608.Conjecture` — for `m ≥ 6` the graph
  `FMFin m` on `n = 28m` vertices has `4e = 788m² − 20m > 784m² = n²` edges
  but only `169m² − 5m` pentagonal edges, and
  `9(169m² − 5m) = 1521m² − 45m < 1568m² = 2n²`.
* `strong_disproof` : with `ε = 47/7056` the same witnesses give
  `pent ≤ (2/9 − ε)n²` (indeed `(2/9 − 47/7056)·784 = 169`).
-/

namespace Erdos608

/-! ## Transport of `OnC5`, `edgeSet` and `pentEdges` along an equivalence -/

section Transport

variable {α β : Type*}

/-- `OnC5` pushes forward through any injective adjacency-preserving map. -/
lemma OnC5.map {f : α → β} (hf : Function.Injective f)
    {G : SimpleGraph α} {G' : SimpleGraph β}
    (hadj : ∀ x y, G.Adj x y → G'.Adj (f x) (f y)) {s : Sym2 α}
    (h : OnC5 G s) : OnC5 G' (Sym2.map f s) := by
  obtain ⟨a, b, c, d, e, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde,
    h1, h2, h3, h4, h5, hedge⟩ := h
  refine ⟨f a, f b, f c, f d, f e, hf.ne hab, hf.ne hac, hf.ne had, hf.ne hae,
    hf.ne hbc, hf.ne hbd, hf.ne hbe, hf.ne hcd, hf.ne hce, hf.ne hde,
    hadj _ _ h1, hadj _ _ h2, hadj _ _ h3, hadj _ _ h4, hadj _ _ h5, ?_⟩
  rcases hedge with rfl | rfl | rfl | rfl | rfl <;> simp [Sym2.map_pair_eq]

/-- The edge set of the comap of `G` along `e.symm` is the image of the edge
set of `G` under `Sym2.map e`. -/
lemma edgeSet_comap_symm (e : α ≃ β) (G : SimpleGraph α) :
    (G.comap e.symm).edgeSet = Sym2.map e '' G.edgeSet := by
  ext s
  induction s using Sym2.ind with
  | _ i j =>
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj, Set.mem_image]
    constructor
    · intro h
      exact ⟨s(e.symm i, e.symm j), h, by simp [Sym2.map_pair_eq]⟩
    · rintro ⟨t, ht, heq⟩
      have hteq : t = s(e.symm i, e.symm j) := by
        have h' := congrArg (Sym2.map e.symm) heq
        rwa [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id, id_eq,
          Sym2.map_pair_eq] at h'
      rw [hteq] at ht
      exact ht

/-- The pentagonal edges of the comap of `G` along `e.symm` are the image of
the pentagonal edges of `G` under `Sym2.map e`. -/
lemma pentEdges_comap_symm (e : α ≃ β) (G : SimpleGraph α) :
    pentEdges (G.comap e.symm) = Sym2.map e '' pentEdges G := by
  ext s
  simp only [pentEdges, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hedge, hc5⟩
    rw [edgeSet_comap_symm] at hedge
    obtain ⟨t, ht, rfl⟩ := hedge
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have h' := OnC5.map e.symm.injective
      (G := G.comap e.symm) (G' := G) (fun x y h => h) hc5
    rwa [Sym2.map_map, Equiv.symm_comp_self, Sym2.map_id, id_eq] at h'
  · rintro ⟨t, ⟨ht, htc5⟩, rfl⟩
    constructor
    · rw [edgeSet_comap_symm]
      exact Set.mem_image_of_mem _ ht
    · exact OnC5.map e.injective (fun x y h => by simpa using h) htc5

end Transport

/-! ## The Füredi–Maleki graph on `Fin (28m)` -/

/-- The transfer equivalence `V m ≃ Fin (28m)`. -/
noncomputable def toFin (m : ℕ) : V m ≃ Fin (28 * m) :=
  Fintype.equivFinOfCardEq (card_V m)

/-- The witness graph transported to `Fin (28m)`: the comap of `FM m`
along `(toFin m).symm`. -/
noncomputable def FMFin (m : ℕ) : SimpleGraph (Fin (28 * m)) :=
  (FM m).comap (toFin m).symm

lemma FMFin_edgeSet_ncard (m : ℕ) :
    (FMFin m).edgeSet.ncard = 197 * m ^ 2 - 5 * m := by
  unfold FMFin
  rw [edgeSet_comap_symm,
    Set.ncard_image_of_injective _ (Sym2.map.injective (toFin m).injective)]
  exact edgeSet_ncard m

lemma FMFin_pentEdges_ncard (m : ℕ) (hm : 1 ≤ m) :
    (pentEdges (FMFin m)).ncard = 169 * m ^ 2 - 5 * m := by
  unfold FMFin
  rw [pentEdges_comap_symm,
    Set.ncard_image_of_injective _ (Sym2.map.injective (toFin m).injective)]
  exact pentEdges_ncard m hm

/-- For `m ≥ 6` the transported graph clears the edge threshold:
`n² < 4e` on `n = 28m` vertices. -/
lemma FMFin_threshold (m : ℕ) (hm : 6 ≤ m) :
    (28 * m) ^ 2 < 4 * (FMFin m).edgeSet.ncard := by
  rw [FMFin_edgeSet_ncard]
  have h6 : 6 * m ≤ m ^ 2 := by nlinarith
  have hsq : (28 * m) ^ 2 = 784 * m ^ 2 := by ring
  rw [hsq]
  generalize m ^ 2 = t at h6 ⊢
  omega

/-! ## L5: the main disproof -/

/-- **Main campaign target.** The Füredi–Maleki construction disproves
Erdős 608: no threshold `n₀` makes the conjectured bound hold for all
`n ≥ n₀`, since `FMFin m` (for `m ≥ max 6 n₀`) has more than `n²/4` edges
but fewer than `(2/9)n²` pentagonal edges. -/
theorem disproof : ¬ Erdos608.Conjecture := by
  unfold Conjecture
  rintro ⟨n₀, h⟩
  obtain ⟨m, hm6, hn₀⟩ : ∃ m, 6 ≤ m ∧ n₀ ≤ 28 * m :=
    ⟨max 6 n₀, le_max_left _ _, by omega⟩
  have hcon := h (28 * m) hn₀ (FMFin m) (FMFin_threshold m hm6)
  rw [FMFin_pentEdges_ncard m (by omega)] at hcon
  have h6 : 6 * m ≤ m ^ 2 := by nlinarith
  have hsq : (28 * m) ^ 2 = 784 * m ^ 2 := by ring
  rw [hsq] at hcon
  generalize m ^ 2 = t at h6 hcon
  omega

/-! ## L6: the strong disproof -/

/-- **Secondary campaign target.** With `ε = 47/7056` there are arbitrarily
large `n` and `n`-vertex graphs with more than `n²/4` edges but at most
`(2/9 − ε)n²` pentagonal edges. -/
theorem strong_disproof :
    ∃ ε : ℚ, 0 < ε ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ G : SimpleGraph (Fin n),
      n ^ 2 < 4 * G.edgeSet.ncard ∧
      ((Erdos608.pentEdges G).ncard : ℚ) ≤ (2 / 9 - ε) * (n : ℚ) ^ 2 := by
  refine ⟨47 / 7056, by norm_num, fun N => ?_⟩
  obtain ⟨m, hm6, hN⟩ : ∃ m, 6 ≤ m ∧ N ≤ 28 * m :=
    ⟨max 6 N, le_max_left _ _, by omega⟩
  refine ⟨28 * m, hN, FMFin m, FMFin_threshold m hm6, ?_⟩
  rw [FMFin_pentEdges_ncard m (by omega)]
  have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  have hle : 5 * m ≤ 169 * m ^ 2 := by nlinarith
  rw [Nat.cast_sub hle]
  push_cast
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  nlinarith [hm0]

end Erdos608

namespace Submissions.Erdos608PentagonalEdgesDisproof.Full

theorem proof : ¬ Erdos608.Conjecture :=
  Erdos608.disproof

end Submissions.Erdos608PentagonalEdgesDisproof.Full
