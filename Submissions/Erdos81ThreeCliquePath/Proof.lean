import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact consolidation of the six own-reviewed local components.
Restricted three-bag path result; no root closure or novelty is claimed.
The draft canonical proposition below is not yet a Jig canonical statement. -/

noncomputable section
namespace Submissions.Erdos81ThreeCliquePath.Proof

/-!
Generic exact edge-clique partition construction for #235.

Only the canonical partition definition is reproduced here; no Statements
module or supplied author proof is imported. Its fields agree literally with
the audited #235 root and the already checked own SplitLower module.

The construction keeps any finite pairwise disjoint family of vertex cliques
and adds the two-vertex set of each edge not lying within one of those cliques.
Coverage of the vertex set is unnecessary. Empty and singleton blocks are
permitted by the canonical definition and by this theorem.

Drafted against the local Lean v4.33.0 / Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d API, inspected read-only.
No compilation was run by the drafting subagent. The owning #235 task is
responsible for compilation, canonical comparison, and the axiom receipt.
-/

open scoped Sym2

namespace CliqueBlockPartition

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsEdgeCliquePartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : Prop :=
  (∀ clique ∈ parts, G.IsClique (clique : Set V)) ∧
    ∀ edge ∈ G.edgeFinset,
      ∃! clique : Finset V, clique ∈ parts ∧ edge ∈ clique.sym2

/-- Exactly the graph edges not wholly contained in an existing block. -/
noncomputable def leftoverEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (blocks : Finset (Finset V)) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => ¬ ∃ c ∈ blocks, e ∈ c.sym2)

@[simp]
theorem mem_leftoverEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (blocks : Finset (Finset V)) (e : Sym2 V) :
    e ∈ leftoverEdges G blocks ↔
      e ∈ G.edgeFinset ∧ ¬ ∃ c ∈ blocks, e ∈ c.sym2 := by
  classical
  simp only [leftoverEdges, Finset.mem_filter]

/-- The explicit family of parts used by the construction. -/
noncomputable def blockPartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (blocks : Finset (Finset V)) : Finset (Finset V) :=
  blocks ∪ (leftoverEdges G blocks).image Sym2.toFinset

omit [Fintype V] in
/-- Every unordered pair lies in the symmetric square of its own vertex set. -/
theorem mem_own_vertex_sym2 (e : Sym2 V) : e ∈ e.toFinset.sym2 := by
  apply Finset.mem_sym2_iff.mpr
  intro v hv
  exact Sym2.mem_toFinset.mpr hv

omit [Fintype V] in
/-- A nondiagonal edge in another pair's vertex set is that same pair. -/
theorem mem_vertex_sym2_iff_eq (e f : Sym2 V) (hne : ¬ e.IsDiag) :
    e ∈ f.toFinset.sym2 ↔ e = f := by
  revert hne
  refine Sym2.inductionOn₂ e f ?_
  intro a b c d hne
  have hab : a ≠ b := by
    simpa only [Sym2.mk_isDiag_iff] using hne
  rw [Sym2.toFinset_mk_eq, Finset.mk_mem_sym2_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨ha, hb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with hac | had <;> rcases hb with hbc | hbd
    · exact False.elim (hab (hac.trans hbc.symm))
    · exact Or.inl ⟨hac, hbd⟩
    · exact Or.inr ⟨had, hbc⟩
    · exact False.elim (hab (had.trans hbd.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The vertex set of an actual graph edge is a clique. -/
theorem isClique_edge_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    G.IsClique (e.toFinset : Set V) := by
  revert he
  refine Sym2.inductionOn e ?_
  intro x y he
  have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
  simpa only [Sym2.toFinset_mk_eq, Finset.coe_pair] using
    (SimpleGraph.isClique_pair.mpr (fun _ => hxy) : G.IsClique ({x, y} : Set V))

omit [Fintype V] in
/-- Disjoint vertex blocks cannot both contain any unordered pair. -/
theorem eq_block_of_common_pair (blocks : Finset (Finset V))
    (hdisjoint : (blocks : Set (Finset V)).PairwiseDisjoint id)
    (c d : Finset V) (hc : c ∈ blocks) (hd : d ∈ blocks)
    (e : Sym2 V) (hec : e ∈ c.sym2) (hed : e ∈ d.sym2) : c = d := by
  by_contra hcd
  have hdis : Disjoint c d := hdisjoint hc hd hcd
  have hvc : e.out.1 ∈ c :=
    Finset.mem_sym2_iff.mp hec _ (Sym2.out_fst_mem e)
  have hvd : e.out.1 ∈ d :=
    Finset.mem_sym2_iff.mp hed _ (Sym2.out_fst_mem e)
  exact Finset.disjoint_left.mp hdis hvc hvd

/-- The explicit construction satisfies the canonical exact partition predicate. -/
theorem isEdgeCliquePartition_blockPartition
    (G : SimpleGraph V) [DecidableRel G.Adj] (blocks : Finset (Finset V))
    (hclique : ∀ c ∈ blocks, G.IsClique (c : Set V))
    (hdisjoint : (blocks : Set (Finset V)).PairwiseDisjoint id) :
    IsEdgeCliquePartition G (blockPartition G blocks) := by
  classical
  constructor
  · intro c hc
    change c ∈ blocks ∪ (leftoverEdges G blocks).image Sym2.toFinset at hc
    rcases Finset.mem_union.mp hc with hblock | hedge
    · exact hclique c hblock
    · rcases Finset.mem_image.mp hedge with ⟨e, he, rfl⟩
      exact isClique_edge_vertices G e ((mem_leftoverEdges G blocks e).mp he).1
  · intro e he
    have hne : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeFinset he
    by_cases hinternal : ∃ c ∈ blocks, e ∈ c.sym2
    · obtain ⟨c, hc, hec⟩ := hinternal
      refine ⟨c, ⟨Finset.mem_union_left _ hc, hec⟩, ?_⟩
      intro d hd
      change d ∈ blocks ∪ (leftoverEdges G blocks).image Sym2.toFinset ∧
        e ∈ d.sym2 at hd
      rcases Finset.mem_union.mp hd.1 with hblock | hedge
      · exact eq_block_of_common_pair blocks hdisjoint d c hblock hc e hd.2 hec
      · rcases Finset.mem_image.mp hedge with ⟨f, hf, rfl⟩
        have hef : e = f := (mem_vertex_sym2_iff_eq e f hne).mp hd.2
        have hnot := ((mem_leftoverEdges G blocks f).mp hf).2
        exact False.elim (hnot ⟨c, hc, hef ▸ hec⟩)
    · have hleft : e ∈ leftoverEdges G blocks :=
        (mem_leftoverEdges G blocks e).mpr ⟨he, hinternal⟩
      refine ⟨e.toFinset, ⟨?_, mem_own_vertex_sym2 e⟩, ?_⟩
      · exact Finset.mem_union_right blocks (Finset.mem_image.mpr ⟨e, hleft, rfl⟩)
      · intro d hd
        change d ∈ blocks ∪ (leftoverEdges G blocks).image Sym2.toFinset ∧
          e ∈ d.sym2 at hd
        rcases Finset.mem_union.mp hd.1 with hblock | hedge
        · exact False.elim (hinternal ⟨d, hblock, hd.2⟩)
        · rcases Finset.mem_image.mp hedge with ⟨f, _hf, rfl⟩
          have hef : e = f := (mem_vertex_sym2_iff_eq e f hne).mp hd.2
          exact congrArg Sym2.toFinset hef.symm

/-- Duplicates can only improve the requested upper bound on the number of parts. -/
theorem card_blockPartition_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (blocks : Finset (Finset V)) :
    (blockPartition G blocks).card ≤ blocks.card + (leftoverEdges G blocks).card := by
  classical
  calc
    (blockPartition G blocks).card ≤
        blocks.card + ((leftoverEdges G blocks).image Sym2.toFinset).card :=
      Finset.card_union_le _ _
    _ ≤ blocks.card + (leftoverEdges G blocks).card :=
      Nat.add_le_add_left Finset.card_image_le _

/-- Generic interface for choosing vertex blocks and bounding the remaining edges. -/
theorem exists_partition_le_blocks_add_leftovers
    (G : SimpleGraph V) [DecidableRel G.Adj] (blocks : Finset (Finset V))
    (hclique : ∀ c ∈ blocks, G.IsClique (c : Set V))
    (hdisjoint : (blocks : Set (Finset V)).PairwiseDisjoint id) :
    ∃ parts : Finset (Finset V), IsEdgeCliquePartition G parts ∧
      parts.card ≤ blocks.card + (leftoverEdges G blocks).card :=
  ⟨blockPartition G blocks,
    isEdgeCliquePartition_blockPartition G blocks hclique hdisjoint,
    card_blockPartition_le G blocks⟩

end CliqueBlockPartition

/-!
Arithmetic component for the three-maximal-clique-path construction in #235.

Provenance: own hand argument in `three-clique-inequality-proof.md`, followed
by the shorter sum-of-squares reduction communicated to the owning #235 task.
The pinned local verifier uses Lean v4.33.0 and Mathlib revision
db584cd6d46c92f209a44c0f1c829460d327499d. Only the local Mathlib source/API was
inspected while drafting this file. The owning task records compilation and
transitive-axiom results separately in three-clique-arithmetic-verdict.json.

The main theorem is over all nonnegative real sextuples. It proves the exact
arithmetic inequality, not the graph partition construction or the arbitrary
chordal-graph root. No quarantined author module is imported.
-/


namespace ThreeCliqueArithmetic

def total (a b t x y z : ℝ) : ℝ := a + b + t + x + y + z

def middleForm (a b t x y _z : ℝ) : ℝ := a * (t + x) + b * (t + y)

def leftForm (_a b t x y z : ℝ) : ℝ := (t + x) * (y + z) + t * b + y * z

def rightForm (a _b t x y z : ℝ) : ℝ := (t + y) * (x + z) + t * a + x * z

/-- The average estimate applies whenever both private sizes exceed z. -/
theorem average_identity (a b t x y z : ℝ) :
    total a b t x y z ^ 2 -
        2 * (middleForm a b t x y z + leftForm a b t x y z +
          rightForm a b t x y z) =
      (t - a - b - z) ^ 2 + (x - y) ^ 2 +
        2 * y * (a - z) + 2 * x * (b - z) := by
  unfold total middleForm leftForm rightForm
  ring

/-- The two-form estimate applies when y ≤ x, b + y ≤ a + x, and b ≤ z. -/
theorem pair_identity (a b t x y z : ℝ) :
    4 * (total a b t x y z ^ 2 -
        3 * (middleForm a b t x y z + leftForm a b t x y z)) =
      (2 * (t - 3 * b + x - y) - (a + z - 2 * b - y)) ^ 2 +
        3 * (a + z - 2 * b - y) ^ 2 +
        12 * b * ((a + x - b - y) + (z - b) + (x - y)) +
        12 * a * y := by
  unfold total middleForm leftForm
  ring

/-- This is the boundary identity used by the original endpoint proof. -/
theorem zero_private_identity (a t x y z : ℝ) :
    4 * (total a 0 t x y z ^ 2 -
        3 * (middleForm a 0 t x y z + leftForm a 0 t x y z)) =
      ((a + y + z) - 2 * (t + x)) ^ 2 +
        3 * ((a + y + z) ^ 2 - (y + z) ^ 2) +
        3 * (y - z) ^ 2 := by
  unfold total middleForm leftForm
  ring

private theorem from_pair (m l r n : ℝ)
    (h : 3 * (m + l) ≤ n ^ 2) :
    6 * m ≤ n ^ 2 ∨ 6 * l ≤ n ^ 2 ∨ 6 * r ≤ n ^ 2 := by
  by_cases hm : 6 * m ≤ n ^ 2
  · exact Or.inl hm
  · exact Or.inr (Or.inl (by linarith))

private theorem from_average (m l r n : ℝ)
    (h : 2 * (m + l + r) ≤ n ^ 2) :
    6 * m ≤ n ^ 2 ∨ 6 * l ≤ n ^ 2 ∨ 6 * r ≤ n ^ 2 := by
  by_cases hm : 6 * m ≤ n ^ 2
  · exact Or.inl hm
  · by_cases hl : 6 * l ≤ n ^ 2
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr (by linarith))

/-- The positively correlated ordering is controlled by the two SOS identities. -/
theorem bound_of_aligned_order (a b t x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hba : b ≤ a) (hyx : y ≤ x) :
    6 * middleForm a b t x y z ≤ total a b t x y z ^ 2 ∨
      6 * leftForm a b t x y z ≤ total a b t x y z ^ 2 ∨
      6 * rightForm a b t x y z ≤ total a b t x y z ^ 2 := by
  by_cases hzb : b ≤ z
  · have hp : 0 ≤ b * ((a + x - b - y) + (z - b) + (x - y)) :=
      mul_nonneg hb (by linarith)
    have hay : 0 ≤ a * y := mul_nonneg ha hy
    have hpair :
        3 * (middleForm a b t x y z + leftForm a b t x y z) ≤
          total a b t x y z ^ 2 := by
      nlinarith [pair_identity a b t x y z,
        sq_nonneg (2 * (t - 3 * b + x - y) - (a + z - 2 * b - y)),
        sq_nonneg (a + z - 2 * b - y)]
    exact from_pair _ _ _ _ hpair
  · have hya : 0 ≤ y * (a - z) := mul_nonneg hy (by linarith)
    have hxb : 0 ≤ x * (b - z) := mul_nonneg hx (by linarith)
    have havg :
        2 * (middleForm a b t x y z + leftForm a b t x y z +
          rightForm a b t x y z) ≤ total a b t x y z ^ 2 := by
      nlinarith [average_identity a b t x y z,
        sq_nonneg (t - a - b - z), sq_nonneg (x - y)]
    exact from_average _ _ _ _ havg

/-- Averaging opposite orderings raises the middle form and the leaf average. -/
theorem averaging_middle_identity (a b t x y z : ℝ) :
    2 * (middleForm ((a + b) / 2) ((a + b) / 2) t
        ((x + y) / 2) ((x + y) / 2) z - middleForm a b t x y z) =
      (b - a) * (x - y) := by
  unfold middleForm
  ring

theorem averaging_leaf_identity (a b t x y z : ℝ) :
    4 * leftForm ((a + b) / 2) ((a + b) / 2) t
        ((x + y) / 2) ((x + y) / 2) z -
      2 * (leftForm a b t x y z + rightForm a b t x y z) =
        (x - y) ^ 2 := by
  unfold leftForm rightForm
  ring

theorem bound_of_y_le_x (a b t x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hyx : y ≤ x) :
    6 * middleForm a b t x y z ≤ total a b t x y z ^ 2 ∨
      6 * leftForm a b t x y z ≤ total a b t x y z ^ 2 ∨
      6 * rightForm a b t x y z ≤ total a b t x y z ^ 2 := by
  by_cases hba : b ≤ a
  · exact bound_of_aligned_order a b t x y z ha hb hx hy hba hyx
  · let A : ℝ := (a + b) / 2
    let X : ℝ := (x + y) / 2
    have hA : 0 ≤ A := by dsimp [A]; linarith
    have hX : 0 ≤ X := by dsimp [X]; linarith
    have hsize : total A A t X X z = total a b t x y z := by
      dsimp [A, X, total]
      ring
    have hsym : rightForm A A t X X z = leftForm A A t X X z := by
      unfold rightForm leftForm
      ring
    have hprod : 0 ≤ (b - a) * (x - y) :=
      mul_nonneg (by linarith) (by linarith)
    have hm : middleForm a b t x y z ≤ middleForm A A t X X z := by
      have hid := averaging_middle_identity a b t x y z
      change 2 * (middleForm A A t X X z - middleForm a b t x y z) =
        (b - a) * (x - y) at hid
      linarith
    have hleafid :
        4 * leftForm A A t X X z -
          2 * (leftForm a b t x y z + rightForm a b t x y z) =
            (x - y) ^ 2 := averaging_leaf_identity a b t x y z
    have lift_leaf
        (hH : 6 * leftForm A A t X X z ≤ total a b t x y z ^ 2) :
        6 * leftForm a b t x y z ≤ total a b t x y z ^ 2 ∨
          6 * rightForm a b t x y z ≤ total a b t x y z ^ 2 := by
      by_cases hL : 6 * leftForm a b t x y z ≤ total a b t x y z ^ 2
      · exact Or.inl hL
      · exact Or.inr (by nlinarith [sq_nonneg (x - y)])
    have hbound := bound_of_aligned_order A A t X X z hA hA hX hX le_rfl le_rfl
    simp only [hsize, hsym] at hbound
    rcases hbound with hM | hL | hR
    · exact Or.inl (by linarith)
    · exact Or.inr (lift_leaf hL)
    · exact Or.inr (lift_leaf hR)

/-- Universal real-sextuple arithmetic theorem, with no finite-grid premise.

The proof actually needs nonnegativity only for a, b, x, y; the explicit
six-variable nonnegative version below matches the graph construction.
-/
theorem one_form_le_sq (a b t x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    6 * middleForm a b t x y z ≤ total a b t x y z ^ 2 ∨
      6 * leftForm a b t x y z ≤ total a b t x y z ^ 2 ∨
      6 * rightForm a b t x y z ≤ total a b t x y z ^ 2 := by
  by_cases hyx : y ≤ x
  · exact bound_of_y_le_x a b t x y z ha hb hx hy hyx
  · have hxy : x ≤ y := by linarith
    have hs := bound_of_y_le_x b a t y x z hb ha hy hx hxy
    have hM : middleForm b a t y x z = middleForm a b t x y z := by
      unfold middleForm
      ring
    have hL : leftForm b a t y x z = rightForm a b t x y z := by
      unfold leftForm rightForm
      ring
    have hR : rightForm b a t y x z = leftForm a b t x y z := by
      unfold rightForm leftForm
      ring
    have hN : total b a t y x z = total a b t x y z := by
      unfold total
      ring
    simp only [hM, hL, hR, hN] at hs
    rcases hs with hmiddle | hright | hleft
    · exact Or.inl hmiddle
    · exact Or.inr (Or.inr hright)
    · exact Or.inr (Or.inl hleft)

/-- The precise nonnegative-sextuple inequality used by the hand construction. -/
theorem minimum_le_sq_div_six (a b t x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_ht : 0 ≤ t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (_hz : 0 ≤ z) :
    min (middleForm a b t x y z)
        (min (leftForm a b t x y z) (rightForm a b t x y z)) ≤
      total a b t x y z ^ 2 / 6 := by
  have hM : min (middleForm a b t x y z)
        (min (leftForm a b t x y z) (rightForm a b t x y z)) ≤
      middleForm a b t x y z := min_le_left _ _
  have hL : min (middleForm a b t x y z)
        (min (leftForm a b t x y z) (rightForm a b t x y z)) ≤
      leftForm a b t x y z :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hR : min (middleForm a b t x y z)
        (min (leftForm a b t x y z) (rightForm a b t x y z)) ≤
      rightForm a b t x y z :=
    (min_le_right _ _).trans (min_le_right _ _)
  rcases one_form_le_sq a b t x y z ha hb hx hy with hm | hl | hr
  · linarith
  · linarith
  · linarith

end ThreeCliqueArithmetic

/-!
Own finite-set bridge for the three-clique-path construction in Jig #235.
This development uses only pinned Mathlib APIs. The graph is required to have
exactly the edges supplied by the three stated clique bags. No chordal root
claim follows until that graph representation and the final bound are proved.
-/

open scoped Sym2
open Finset SimpleGraph

namespace ThreeCliqueGraph

variable {V : Type*} [DecidableEq V]

def between (U W : Finset V) : Finset (Sym2 V) :=
  (U ×ˢ W).image (fun p => s(p.1, p.2))

theorem mem_between {U W : Finset V} {x y : V} :
    s(x,y) ∈ between U W ↔
      (x ∈ U ∧ y ∈ W) ∨ (y ∈ U ∧ x ∈ W) := by
  simp only [between, mem_image, mem_product, Prod.exists, Sym2.eq_iff]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact ⟨x,y,⟨hx,hy⟩,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨y,x,⟨hy,hx⟩,Or.inr ⟨rfl,rfl⟩⟩

theorem card_between_le (U W : Finset V) :
    (between U W).card ≤ U.card * W.card := by
  exact (card_image_le).trans_eq (card_product U W)

/-- All possible edges in a union of three clique bags. Diagonal pairs are
irrelevant because the caller supplies a simple-graph edge. -/
def InBags (A B T X Y Z : Finset V) (e : Sym2 V) : Prop :=
  e ∈ (A ∪ T ∪ X).sym2 ∨ e ∈ (T ∪ X ∪ Y ∪ Z).sym2 ∨
    e ∈ (B ∪ T ∪ Y).sym2

theorem middle_cross_cover (A B T X Y Z : Finset V) (e : Sym2 V)
    (h : InBags A B T X Y Z e)
    (hM : e ∉ (T ∪ X ∪ Y ∪ Z).sym2)
    (hA : e ∉ A.sym2) (hB : e ∉ B.sym2) :
    e ∈ between A (T ∪ X) ∪ between B (T ∪ Y) := by
  induction e using Sym2.ind with | _ x y =>
    simp only [InBags, mk_mem_sym2_iff, mem_union, mem_between] at *
    rcases h with h | h | h
    · rcases h with ⟨hx,hy⟩
      rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy <;> aesop
    · exact (hM h).elim
    · rcases h with ⟨hx,hy⟩
      rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy <;> aesop

theorem left_cross_cover (A B T X Y Z : Finset V) (e : Sym2 V)
    (h : InBags A B T X Y Z e)
    (hL : e ∉ (A ∪ T ∪ X).sym2)
    (hB : e ∉ (B ∪ Y).sym2) (hZ : e ∉ Z.sym2) :
    e ∈ between (T ∪ X) (Y ∪ Z) ∪ between T B ∪ between Y Z := by
  induction e using Sym2.ind with | _ x y =>
    simp only [InBags, mk_mem_sym2_iff, mem_union, mem_between] at *
    rcases h with h | h | h
    · exact (hL h).elim
    · rcases h with ⟨hx,hy⟩
      rcases hx with ((hx | hx) | hx) | hx <;>
        rcases hy with ((hy | hy) | hy) | hy <;> aesop
    · rcases h with ⟨hx,hy⟩
      rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy <;> aesop

theorem right_cross_cover (A B T X Y Z : Finset V) (e : Sym2 V)
    (h : InBags A B T X Y Z e)
    (hA : e ∉ (A ∪ X).sym2)
    (hR : e ∉ (B ∪ T ∪ Y).sym2) (hZ : e ∉ Z.sym2) :
    e ∈ between (T ∪ Y) (X ∪ Z) ∪ between T A ∪ between X Z := by
  induction e using Sym2.ind with | _ x y =>
    simp only [InBags, mk_mem_sym2_iff, mem_union, mem_between] at *
    rcases h with h | h | h
    · rcases h with ⟨hx,hy⟩
      rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy <;> aesop
    · rcases h with ⟨hx,hy⟩
      rcases hx with ((hx | hx) | hx) | hx <;>
        rcases hy with ((hy | hy) | hy) | hy <;> aesop
    · exact (hR h).elim

theorem middle_cross_card (A B T X Y : Finset V) :
    (between A (T ∪ X) ∪ between B (T ∪ Y)).card ≤
      A.card * (T.card + X.card) + B.card * (T.card + Y.card) := by
  calc
    _ ≤ (between A (T ∪ X)).card + (between B (T ∪ Y)).card := card_union_le _ _
    _ ≤ A.card * (T ∪ X).card + B.card * (T ∪ Y).card :=
      Nat.add_le_add (card_between_le _ _) (card_between_le _ _)
    _ ≤ _ := Nat.add_le_add
      (Nat.mul_le_mul_left _ (card_union_le _ _))
      (Nat.mul_le_mul_left _ (card_union_le _ _))

theorem left_cross_card (B T X Y Z : Finset V) :
    (between (T ∪ X) (Y ∪ Z) ∪ between T B ∪ between Y Z).card ≤
      (T.card + X.card) * (Y.card + Z.card) + T.card * B.card + Y.card * Z.card := by
  calc
    _ ≤ (between (T ∪ X) (Y ∪ Z) ∪ between T B).card + (between Y Z).card :=
      card_union_le _ _
    _ ≤ ((between (T ∪ X) (Y ∪ Z)).card + (between T B).card) +
        (between Y Z).card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ ((T ∪ X).card * (Y ∪ Z).card + T.card * B.card) + Y.card * Z.card :=
      Nat.add_le_add (Nat.add_le_add (card_between_le _ _) (card_between_le _ _))
        (card_between_le _ _)
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul (card_union_le _ _) (card_union_le _ _)) _) _

def SixDisjoint (A B T X Y Z : Finset V) : Prop :=
  Disjoint A B ∧ Disjoint A T ∧ Disjoint A X ∧ Disjoint A Y ∧ Disjoint A Z ∧
  Disjoint B T ∧ Disjoint B X ∧ Disjoint B Y ∧ Disjoint B Z ∧
  Disjoint T X ∧ Disjoint T Y ∧ Disjoint T Z ∧
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z

theorem three_disjoint (P Q R : Finset V)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R) :
    (({P,Q,R} : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  intro c hc d hd hcd
  simp only [mem_coe, mem_insert, mem_singleton] at hc hd
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    simp_all [Function.id_def, disjoint_comm]

theorem three_card_le (P Q R : Finset V) :
    ({P,Q,R} : Finset (Finset V)).card ≤ 3 := by
  have h1 := card_insert_le P ({Q,R} : Finset (Finset V))
  have h2 := card_insert_le Q ({R} : Finset (Finset V))
  simp only [card_singleton] at h2
  omega

theorem middle_disjoint (A B T X Y Z : Finset V) (h : SixDisjoint A B T X Y Z) :
    (({T ∪ X ∪ Y ∪ Z,A,B} : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  apply three_disjoint <;>
    (try simp only [disjoint_union_left]) <;>
    rcases h with ⟨hAB,hAT,hAX,hAY,hAZ,hBT,hBX,hBY,hBZ,hTX,hTY,hTZ,hXY,hXZ,hYZ⟩ <;>
    aesop (add safe Disjoint.symm)

theorem left_disjoint (A B T X Y Z : Finset V) (h : SixDisjoint A B T X Y Z) :
    (({A ∪ T ∪ X,B ∪ Y,Z} : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  apply three_disjoint <;>
    (try simp only [disjoint_union_left, disjoint_union_right]) <;>
    rcases h with ⟨hAB,hAT,hAX,hAY,hAZ,hBT,hBX,hBY,hBZ,hTX,hTY,hTZ,hXY,hXZ,hYZ⟩ <;>
    aesop (add safe Disjoint.symm)

theorem right_disjoint (A B T X Y Z : Finset V) (h : SixDisjoint A B T X Y Z) :
    (({A ∪ X,B ∪ T ∪ Y,Z} : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  apply three_disjoint <;>
    (try simp only [disjoint_union_left, disjoint_union_right]) <;>
    rcases h with ⟨hAB,hAT,hAX,hAY,hAZ,hBT,hBX,hBY,hBZ,hTX,hTY,hTZ,hXY,hXZ,hYZ⟩ <;>
    aesop (add safe Disjoint.symm)

theorem six_card_sum_le [Fintype V] (A B T X Y Z : Finset V)
    (h : SixDisjoint A B T X Y Z) :
    A.card + B.card + T.card + X.card + Y.card + Z.card ≤ Fintype.card V := by
  have hcard : (A ∪ B ∪ T ∪ X ∪ Y ∪ Z).card =
      A.card + B.card + T.card + X.card + Y.card + Z.card := by
    rcases h with ⟨hAB,hAT,hAX,hAY,hAZ,hBT,hBX,hBY,hBZ,hTX,hTY,hTZ,hXY,hXZ,hYZ⟩
    have h1 : Disjoint (A ∪ B) T := by simp [disjoint_union_left,hAT,hBT]
    have h2 : Disjoint (A ∪ B ∪ T) X := by simp [disjoint_union_left,hAX,hBX,hTX]
    have h3 : Disjoint (A ∪ B ∪ T ∪ X) Y := by simp [disjoint_union_left,hAY,hBY,hTY,hXY]
    have h4 : Disjoint (A ∪ B ∪ T ∪ X ∪ Y) Z := by simp [disjoint_union_left,hAZ,hBZ,hTZ,hXZ,hYZ]
    rw [card_union_of_disjoint h4,card_union_of_disjoint h3,card_union_of_disjoint h2,
      card_union_of_disjoint h1,card_union_of_disjoint hAB]
  rw [← hcard,← card_univ]
  exact card_le_card (subset_univ _)

end ThreeCliqueGraph

/-!
The three explicit exact edge-clique partitions for the six-region graph
representation used in #235. The region order is A B T X Y Z throughout.

Dependencies are the own-authored generic construction and finite-set bridge,
read in full before this draft. No external proof source is imported. The
generic construction was reported compiled by the owner; the owner's remaining
bridge checks and this module's compilation are separate pending receipts.
No build, public write, or GUI action was performed by the drafting subagent.

No vertex-cover hypothesis is needed. Vertices outside the regions cannot
have incident graph edges under hedge; the generic construction itself also
handles arbitrary uncovered edges when used independently.
-/

open scoped Sym2
open Finset SimpleGraph CliqueBlockPartition ThreeCliqueGraph

namespace ThreeCliquePartitions

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem leftover_not_internal (G : SimpleGraph V) [DecidableRel G.Adj]
    (blocks : Finset (Finset V)) (e : Sym2 V) (he : e ∈ leftoverEdges G blocks)
    (c : Finset V) (hc : c ∈ blocks) : e ∉ c.sym2 := by
  intro hint
  exact ((mem_leftoverEdges G blocks e).mp he).2 ⟨c, hc, hint⟩

/-- Own the middle bag, and retain A and B as the other vertex blocks. -/
theorem exists_middle_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B T X Y Z : Finset V)
    (hdisjoint : SixDisjoint A B T X Y Z)
    (hL : G.IsClique ((A ∪ T ∪ X : Finset V) : Set V))
    (hM : G.IsClique ((T ∪ X ∪ Y ∪ Z : Finset V) : Set V))
    (hR : G.IsClique ((B ∪ T ∪ Y : Finset V) : Set V))
    (hedge : ∀ e ∈ G.edgeFinset, InBags A B T X Y Z e) :
    ∃ parts : Finset (Finset V), IsEdgeCliquePartition G parts ∧
      parts.card ≤ 3 + (A.card * (T.card + X.card) +
        B.card * (T.card + Y.card)) := by
  classical
  let blocks : Finset (Finset V) := {T ∪ X ∪ Y ∪ Z, A, B}
  have hA : G.IsClique (A : Set V) := hL.subset (by
    intro v hv
    exact mem_union_left X (mem_union_left T hv))
  have hB : G.IsClique (B : Set V) := hR.subset (by
    intro v hv
    exact mem_union_left Y (mem_union_left T hv))
  have hclique : ∀ c ∈ blocks, G.IsClique (c : Set V) := by
    intro c hc
    simp only [blocks, mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hM
    · exact hA
    · exact hB
  have hblocks : blocks.card ≤ 3 := three_card_le _ _ _
  have hd : (blocks : Set (Finset V)).PairwiseDisjoint id :=
    middle_disjoint A B T X Y Z hdisjoint
  have hsub : leftoverEdges G blocks ⊆
      between A (T ∪ X) ∪ between B (T ∪ Y) := by
    intro e he
    apply middle_cross_cover A B T X Y Z e
      (hedge e ((mem_leftoverEdges G blocks e).mp he).1)
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
  have hcross : (leftoverEdges G blocks).card ≤
      A.card * (T.card + X.card) + B.card * (T.card + Y.card) :=
    (card_le_card hsub).trans (middle_cross_card A B T X Y)
  obtain ⟨parts, hp, hcard⟩ :=
    exists_partition_le_blocks_add_leftovers G blocks hclique hd
  exact ⟨parts, hp, hcard.trans (Nat.add_le_add hblocks hcross)⟩

/-- Own the left bag, and retain B∪Y and Z as the other vertex blocks. -/
theorem exists_left_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B T X Y Z : Finset V)
    (hdisjoint : SixDisjoint A B T X Y Z)
    (hL : G.IsClique ((A ∪ T ∪ X : Finset V) : Set V))
    (hM : G.IsClique ((T ∪ X ∪ Y ∪ Z : Finset V) : Set V))
    (hR : G.IsClique ((B ∪ T ∪ Y : Finset V) : Set V))
    (hedge : ∀ e ∈ G.edgeFinset, InBags A B T X Y Z e) :
    ∃ parts : Finset (Finset V), IsEdgeCliquePartition G parts ∧
      parts.card ≤ 3 + ((T.card + X.card) * (Y.card + Z.card) +
        T.card * B.card + Y.card * Z.card) := by
  classical
  let blocks : Finset (Finset V) := {A ∪ T ∪ X, B ∪ Y, Z}
  have hBY : G.IsClique ((B ∪ Y : Finset V) : Set V) := hR.subset (by
    intro v hv
    rcases mem_union.mp hv with hvB | hvY
    · exact mem_union_left Y (mem_union_left T hvB)
    · exact mem_union_right (B ∪ T) hvY)
  have hZ : G.IsClique (Z : Set V) := hM.subset (by
    intro v hv
    exact mem_union_right (T ∪ X ∪ Y) hv)
  have hclique : ∀ c ∈ blocks, G.IsClique (c : Set V) := by
    intro c hc
    simp only [blocks, mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hL
    · exact hBY
    · exact hZ
  have hblocks : blocks.card ≤ 3 := three_card_le _ _ _
  have hd : (blocks : Set (Finset V)).PairwiseDisjoint id :=
    left_disjoint A B T X Y Z hdisjoint
  have hsub : leftoverEdges G blocks ⊆
      between (T ∪ X) (Y ∪ Z) ∪ between T B ∪ between Y Z := by
    intro e he
    apply left_cross_cover A B T X Y Z e
      (hedge e ((mem_leftoverEdges G blocks e).mp he).1)
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
  have hcross : (leftoverEdges G blocks).card ≤
      (T.card + X.card) * (Y.card + Z.card) + T.card * B.card + Y.card * Z.card :=
    (card_le_card hsub).trans (left_cross_card B T X Y Z)
  obtain ⟨parts, hp, hcard⟩ :=
    exists_partition_le_blocks_add_leftovers G blocks hclique hd
  exact ⟨parts, hp, hcard.trans (Nat.add_le_add hblocks hcross)⟩

/-- Own the right bag, and retain A∪X and Z as the other vertex blocks. -/
theorem exists_right_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B T X Y Z : Finset V)
    (hdisjoint : SixDisjoint A B T X Y Z)
    (hL : G.IsClique ((A ∪ T ∪ X : Finset V) : Set V))
    (hM : G.IsClique ((T ∪ X ∪ Y ∪ Z : Finset V) : Set V))
    (hR : G.IsClique ((B ∪ T ∪ Y : Finset V) : Set V))
    (hedge : ∀ e ∈ G.edgeFinset, InBags A B T X Y Z e) :
    ∃ parts : Finset (Finset V), IsEdgeCliquePartition G parts ∧
      parts.card ≤ 3 + ((T.card + Y.card) * (X.card + Z.card) +
        T.card * A.card + X.card * Z.card) := by
  classical
  let blocks : Finset (Finset V) := {A ∪ X, B ∪ T ∪ Y, Z}
  have hAX : G.IsClique ((A ∪ X : Finset V) : Set V) := hL.subset (by
    intro v hv
    rcases mem_union.mp hv with hvA | hvX
    · exact mem_union_left X (mem_union_left T hvA)
    · exact mem_union_right (A ∪ T) hvX)
  have hZ : G.IsClique (Z : Set V) := hM.subset (by
    intro v hv
    exact mem_union_right (T ∪ X ∪ Y) hv)
  have hclique : ∀ c ∈ blocks, G.IsClique (c : Set V) := by
    intro c hc
    simp only [blocks, mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hAX
    · exact hR
    · exact hZ
  have hblocks : blocks.card ≤ 3 := three_card_le _ _ _
  have hd : (blocks : Set (Finset V)).PairwiseDisjoint id :=
    right_disjoint A B T X Y Z hdisjoint
  have hsub : leftoverEdges G blocks ⊆
      between (T ∪ Y) (X ∪ Z) ∪ between T A ∪ between X Z := by
    intro e he
    apply right_cross_cover A B T X Y Z e
      (hedge e ((mem_leftoverEdges G blocks e).mp he).1)
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
    · exact leftover_not_internal G blocks e he _ (by simp [blocks])
  have hcross : (leftoverEdges G blocks).card ≤
      (T.card + Y.card) * (X.card + Z.card) + T.card * A.card + X.card * Z.card :=
    (card_le_card hsub).trans (left_cross_card A T Y X Z)
  obtain ⟨parts, hp, hcard⟩ :=
    exists_partition_le_blocks_add_leftovers G blocks hclique hd
  exact ⟨parts, hp, hcard.trans (Nat.add_le_add hblocks hcross)⟩

end ThreeCliquePartitions

/-!
Finite graph consequence of the checked universal arithmetic inequality.
The six disjoint regions describe the bags L=A∪T∪X, M=T∪X∪Y∪Z,
R=B∪T∪Y of a three-clique path. Isolated vertices outside all regions
are allowed. This is a restricted-class result, not the arbitrary chordal root.
-/

open Finset SimpleGraph

namespace ThreeCliquePathBound

theorem nat_one_form_le_sq (a b t x y z : ℕ) :
    6 * (a * (t+x) + b * (t+y)) ≤ (a+b+t+x+y+z)^2 ∨
    6 * ((t+x)*(y+z) + t*b + y*z) ≤ (a+b+t+x+y+z)^2 ∨
    6 * ((t+y)*(x+z) + t*a + x*z) ≤ (a+b+t+x+y+z)^2 := by
  have h := ThreeCliqueArithmetic.one_form_le_sq
    (a : ℝ) (b : ℝ) (t : ℝ) (x : ℝ) (y : ℝ) (z : ℝ)
    (Nat.cast_nonneg a) (Nat.cast_nonneg b) (Nat.cast_nonneg x) (Nat.cast_nonneg y)
  simp only [ThreeCliqueArithmetic.middleForm, ThreeCliqueArithmetic.leftForm,
    ThreeCliqueArithmetic.rightForm, ThreeCliqueArithmetic.total] at h
  exact_mod_cast h

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit six-region graph class: an exact partition with additive18 in
the six-times cardinality convention, i.e. at most n²/6+3 parts. -/
theorem exists_partition_additive_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T X Y Z : Finset V) (hd : ThreeCliqueGraph.SixDisjoint A B T X Y Z)
    (hL : G.IsClique ((A ∪ T ∪ X : Finset V) : Set V))
    (hM : G.IsClique ((T ∪ X ∪ Y ∪ Z : Finset V) : Set V))
    (hR : G.IsClique ((B ∪ T ∪ Y : Finset V) : Set V))
    (hedge : ∀ e ∈ G.edgeFinset, ThreeCliqueGraph.InBags A B T X Y Z e) :
    ∃ parts : Finset (Finset V), CliqueBlockPartition.IsEdgeCliquePartition G parts ∧
      6 * parts.card ≤ Fintype.card V ^ 2 + 18 := by
  have hn := ThreeCliqueGraph.six_card_sum_le A B T X Y Z hd
  have hs := Nat.pow_le_pow_left hn 2
  rcases nat_one_form_le_sq A.card B.card T.card X.card Y.card Z.card with h | h | h
  · obtain ⟨parts, hp, hcard⟩ :=
      ThreeCliquePartitions.exists_middle_partition G A B T X Y Z hd hL hM hR hedge
    exact ⟨parts,hp,by nlinarith⟩
  · obtain ⟨parts, hp, hcard⟩ :=
      ThreeCliquePartitions.exists_left_partition G A B T X Y Z hd hL hM hR hedge
    exact ⟨parts,hp,by nlinarith⟩
  · obtain ⟨parts, hp, hcard⟩ :=
      ThreeCliquePartitions.exists_right_partition G A B T X Y Z hd hL hM hR hedge
    exact ⟨parts,hp,by nlinarith⟩

/-- The canonical linear-error shape with the explicit constant C=18,
including the zero-vertex case. Its graph hypotheses remain restricted. -/
theorem exists_partition_linear_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B T X Y Z : Finset V) (hd : ThreeCliqueGraph.SixDisjoint A B T X Y Z)
    (hL : G.IsClique ((A ∪ T ∪ X : Finset V) : Set V))
    (hM : G.IsClique ((T ∪ X ∪ Y ∪ Z : Finset V) : Set V))
    (hR : G.IsClique ((B ∪ T ∪ Y : Finset V) : Set V))
    (hedge : ∀ e ∈ G.edgeFinset, ThreeCliqueGraph.InBags A B T X Y Z e) :
    ∃ parts : Finset (Finset V), CliqueBlockPartition.IsEdgeCliquePartition G parts ∧
      6 * parts.card ≤ Fintype.card V ^ 2 + 18 * Fintype.card V := by
  by_cases hn : Fintype.card V = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    refine ⟨∅, ?_, by simp⟩
    constructor
    · simp
    · intro e _he
      induction e using Sym2.ind with | _ x y => exact isEmptyElim x
  · have hpos : 1 ≤ Fintype.card V := by omega
    obtain ⟨parts,hp,hcard⟩ :=
      exists_partition_additive_bound G A B T X Y Z hd hL hM hR hedge
    exact ⟨parts,hp,by nlinarith⟩

end ThreeCliquePathBound

/-!
Representation bridge from an explicit three-bag path to the six-region
partition theorem for #235.

The assumptions are three finite clique bags L,M,R, the running-intersection
condition L ∩ R ⊆ M, and coverage of every graph edge by a bag. Coverage of
all vertices, maximality of the bags, and a separate chordality assumption are
not needed. This file does not assert that an arbitrary chordal graph has
such a three-bag representation.

This is an own-authored draft importing only the own source chain whose exact
APIs were read before drafting. No build, external executable, public write,
or GUI operation was run by the drafting subagent. The owner supplies the
compilation and transitive-axiom receipts.
-/

open Finset SimpleGraph

namespace ThreeCliqueBagBound

variable {V : Type*} [DecidableEq V]

/-- The six regions of a three-bag path are pairwise disjoint. -/
theorem regions_disjoint (L M R : Finset V) (hLR : L ∩ R ⊆ M) :
    ThreeCliqueGraph.SixDisjoint
      (L \ M) (R \ M) (L ∩ M ∩ R)
      ((L ∩ M) \ R) ((R ∩ M) \ L) (M \ (L ∪ R)) := by
  have hAB : Disjoint (L \ M) (R \ M) := by
    apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact (mem_sdiff.mp hvL).2
      (hLR (mem_inter.mpr ⟨(mem_sdiff.mp hvL).1, (mem_sdiff.mp hvR).1⟩))
  unfold ThreeCliqueGraph.SixDisjoint
  refine ⟨hAB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply Finset.disjoint_left.mpr <;>
    intro v hv hw <;>
    simp only [mem_sdiff, mem_inter, mem_union] at hv hw <;>
    aesop

theorem reconstruct_left (L M R : Finset V) :
    (L \ M) ∪ (L ∩ M ∩ R) ∪ ((L ∩ M) \ R) = L := by
  ext v
  by_cases hvL : v ∈ L <;> by_cases hvM : v ∈ M <;> by_cases hvR : v ∈ R <;>
    simp [hvL, hvM, hvR]

theorem reconstruct_middle (L M R : Finset V) :
    (L ∩ M ∩ R) ∪ ((L ∩ M) \ R) ∪ ((R ∩ M) \ L) ∪
      (M \ (L ∪ R)) = M := by
  ext v
  by_cases hvL : v ∈ L <;> by_cases hvM : v ∈ M <;> by_cases hvR : v ∈ R <;>
    simp [hvL, hvM, hvR]

theorem reconstruct_right (L M R : Finset V) :
    (R \ M) ∪ (L ∩ M ∩ R) ∪ ((R ∩ M) \ L) = R := by
  ext v
  by_cases hvL : v ∈ L <;> by_cases hvM : v ∈ M <;> by_cases hvR : v ∈ R <;>
    simp [hvL, hvM, hvR]

/-- An explicit representation certificate, reusable without graph hypotheses. -/
theorem exists_six_regions (L M R : Finset V) (hLR : L ∩ R ⊆ M) :
    ∃ A B T X Y Z : Finset V,
      ThreeCliqueGraph.SixDisjoint A B T X Y Z ∧
      A ∪ T ∪ X = L ∧ T ∪ X ∪ Y ∪ Z = M ∧ B ∪ T ∪ Y = R :=
  ⟨L \ M, R \ M, L ∩ M ∩ R, (L ∩ M) \ R, (R ∩ M) \ L,
    M \ (L ∪ R), regions_disjoint L M R hLR,
    reconstruct_left L M R, reconstruct_middle L M R, reconstruct_right L M R⟩

variable [Fintype V]

/-- A three-bag path has an exact edge-clique partition with at most n²/6+3 parts. -/
theorem exists_partition_additive_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (L M R : Finset V)
    (hL : G.IsClique (L : Set V)) (hM : G.IsClique (M : Set V))
    (hR : G.IsClique (R : Set V)) (hLR : L ∩ R ⊆ M)
    (hedge : ∀ e ∈ G.edgeFinset, e ∈ L.sym2 ∨ e ∈ M.sym2 ∨ e ∈ R.sym2) :
    ∃ parts : Finset (Finset V), CliqueBlockPartition.IsEdgeCliquePartition G parts ∧
      6 * parts.card ≤ Fintype.card V ^ 2 + 18 := by
  obtain ⟨A, B, T, X, Y, Z, hd, hleft, hmiddle, hright⟩ :=
    exists_six_regions L M R hLR
  apply ThreeCliquePathBound.exists_partition_additive_bound G A B T X Y Z hd
  · simpa only [hleft] using hL
  · simpa only [hmiddle] using hM
  · simpa only [hright] using hR
  · intro e he
    simpa only [ThreeCliqueGraph.InBags, hleft, hmiddle, hright] using hedge e he

/-- The canonical linear-error form with C=18, including the empty vertex type. -/
theorem exists_partition_linear_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (L M R : Finset V)
    (hL : G.IsClique (L : Set V)) (hM : G.IsClique (M : Set V))
    (hR : G.IsClique (R : Set V)) (hLR : L ∩ R ⊆ M)
    (hedge : ∀ e ∈ G.edgeFinset, e ∈ L.sym2 ∨ e ∈ M.sym2 ∨ e ∈ R.sym2) :
    ∃ parts : Finset (Finset V), CliqueBlockPartition.IsEdgeCliquePartition G parts ∧
      6 * parts.card ≤ Fintype.card V ^ 2 + 18 * Fintype.card V := by
  obtain ⟨A, B, T, X, Y, Z, hd, hleft, hmiddle, hright⟩ :=
    exists_six_regions L M R hLR
  apply ThreeCliquePathBound.exists_partition_linear_bound G A B T X Y Z hd
  · simpa only [hleft] using hL
  · simpa only [hmiddle] using hM
  · simpa only [hright] using hR
  · intro e he
    simpa only [ThreeCliqueGraph.InBags, hleft, hmiddle, hright] using hedge e he

end ThreeCliqueBagBound

namespace CanonicalDraft
open scoped Sym2
open Finset SimpleGraph

def IsEdgeCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parts : Finset (Finset V)) : Prop :=
  (∀ clique ∈ parts, G.IsClique (clique : Set V)) ∧
    ∀ edge ∈ G.edgeFinset,
      ∃! clique : Finset V, clique ∈ parts ∧ edge ∈ clique.sym2

abbrev statement : Prop := by
  classical
  exact ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ L M R : Finset (Fin n),
    G.IsClique (L : Set (Fin n)) → G.IsClique (M : Set (Fin n)) →
    G.IsClique (R : Set (Fin n)) → L ∩ R ⊆ M →
    (∀ e ∈ G.edgeFinset, e ∈ L.sym2 ∨ e ∈ M.sym2 ∨ e ∈ R.sym2) →
    ∃ parts : Finset (Finset (Fin n)), IsEdgeCliquePartition G parts ∧
      6 * parts.card ≤ n^2 + 18

end CanonicalDraft

theorem proof : CanonicalDraft.statement := by
  classical
  intro n G L M R hL hM hR hLR hedge
  simpa only [CanonicalDraft.IsEdgeCliquePartition,
    CliqueBlockPartition.IsEdgeCliquePartition, Fintype.card_fin] using
    ThreeCliqueBagBound.exists_partition_additive_bound G L M R hL hM hR hLR hedge

end Submissions.Erdos81ThreeCliquePath.Proof
end

#print axioms Submissions.Erdos81ThreeCliquePath.Proof.proof
