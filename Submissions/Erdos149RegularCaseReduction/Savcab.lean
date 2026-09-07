import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

universe u

namespace Submissions.Erdos149RegularCaseReduction.Savcab

def strongConflict {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f :=
    e ≠ f ∧
      ((G.lineGraph).Adj e f ∨
        ∃ middle : G.edgeSet,
          (G.lineGraph).Adj e middle ∧ (G.lineGraph).Adj middle f)
  symm := ⟨by
    intro e f h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hef | ⟨middle, hem, hmf⟩
    · exact Or.inl hef.symm
    · exact Or.inr ⟨middle, hmf.symm, hem.symm⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

noncomputable def maximumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  open scoped Classical in G.maxDegree

def StrongColorable {V : Type*} (G : SimpleGraph V) (colors : ℕ) : Prop :=
  (strongConflict G).Colorable colors

open SimpleGraph
open scoped Classical

/-- An injective graph homomorphism preserves all canonical strong conflicts. -/
def strongConflictCopy {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : Copy G H) : Copy (strongConflict G) (strongConflict H) where
  toHom :=
    { toFun := f.toLineGraphEmbedding
      map_rel' := by
        intro e g h
        refine ⟨fun he => h.1 (f.toLineGraphEmbedding.injective he), ?_⟩
        rcases h.2 with h | ⟨m, hem, hmg⟩
        · exact Or.inl (f.toLineGraphEmbedding.toHom.map_rel h)
        · exact Or.inr ⟨f.toLineGraphEmbedding m,
            f.toLineGraphEmbedding.toHom.map_rel hem,
            f.toLineGraphEmbedding.toHom.map_rel hmg⟩ }
  injective' := f.toLineGraphEmbedding.injective

theorem strongColorable_restrict {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : Copy G H) {k : ℕ} (h : StrongColorable H k) : StrongColorable G k :=
  h.of_hom (strongConflictCopy f).toHom

/-- Double the graph and match corresponding vertices exactly when they are deficient. -/
noncomputable def double {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ) :
    SimpleGraph (V ⊕ V) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inr v, .inr w => G.Adj v w
    | .inl v, .inr w => v = w ∧ G.degree v < D
    | .inr v, .inl w => v = w ∧ G.degree v < D
  symm := ⟨by
    rintro (v | v) (w | w) h
    · exact h.symm
    · exact ⟨h.1.symm, h.1 ▸ h.2⟩
    · exact ⟨h.1.symm, h.1 ▸ h.2⟩
    · exact h.symm⟩
  loopless := ⟨by rintro (v | v) h <;> exact G.loopless.irrefl v h⟩

def doubleCopy {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ) :
    Copy G (double G D) where
  toHom := ⟨Sum.inl, fun h => h⟩
  injective' := Sum.inl_injective

lemma double_degree_left {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ) (v : V) :
    (double G D).degree (.inl v) = G.degree v + if G.degree v < D then 1 else 0 := by
  classical
  have hn : (double G D).neighborFinset (.inl v) =
      (G.neighborFinset v).image Sum.inl ∪
        (if G.degree v < D then {Sum.inr v} else ∅) := by
    ext w
    rw [mem_neighborFinset]
    cases w <;> by_cases h : G.degree v < D <;> simp [double, h, eq_comm]
  rw [← card_neighborFinset_eq_degree, hn]
  have hd : Disjoint ((G.neighborFinset v).image Sum.inl)
      (if G.degree v < D then {Sum.inr v} else ∅) := by
    by_cases h : G.degree v < D <;> simp [h]
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ Sum.inl_injective]
  rw [card_neighborFinset_eq_degree]
  split_ifs <;> simp

lemma double_degree_right {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℕ) (v : V) :
    (double G D).degree (.inr v) = G.degree v + if G.degree v < D then 1 else 0 := by
  classical
  have hn : (double G D).neighborFinset (.inr v) =
      (G.neighborFinset v).image Sum.inr ∪
        (if G.degree v < D then {Sum.inl v} else ∅) := by
    ext w
    rw [mem_neighborFinset]
    cases w <;> by_cases h : G.degree v < D <;> simp [double, h, eq_comm]
  rw [← card_neighborFinset_eq_degree, hn]
  have hd : Disjoint ((G.neighborFinset v).image Sum.inr)
      (if G.degree v < D then {Sum.inl v} else ∅) := by
    by_cases h : G.degree v < D <;> simp [h]
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ Sum.inr_injective]
  rw [card_neighborFinset_eq_degree]
  split_ifs <;> simp

/-- Iterating the doubling construction removes one unit of degree deficit per step. -/
theorem exists_regular_extension_aux (t : ℕ) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (D : ℕ),
      (∀ v, G.degree v ≤ D) → (∀ v, D ≤ G.degree v + t) →
      ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
        H.IsRegularOfDegree D ∧ Nonempty (Copy G H) := by
  induction t with
  | zero =>
    intro V _ G D hu hl
    let e := Fintype.equivFin V
    let H := G.map e
    refine ⟨Fintype.card V, H, ?_, ⟨(Iso.map e G).toCopy⟩⟩
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    convert ((Iso.map e G).degree_eq v).trans
      ((hu v).antisymm (by simpa using hl v)) using 1
    congr 1
    exact Subsingleton.elim _ _
  | succ t ih =>
    intro V _ G D hu hl
    have hup : ∀ w, (double G D).degree w ≤ D := by
      rintro (v | v)
      · rw [double_degree_left]
        have := hu v
        split_ifs <;> omega
      · rw [double_degree_right]
        have := hu v
        split_ifs <;> omega
    have hlo : ∀ w, D ≤ (double G D).degree w + t := by
      rintro (v | v)
      · rw [double_degree_left]
        have := hl v
        split_ifs <;> omega
      · rw [double_degree_right]
        have := hl v
        split_ifs <;> omega
    obtain ⟨n, H, hreg, ⟨f⟩⟩ := ih (double G D) D hup hlo
    exact ⟨n, H, hreg, ⟨f.comp (doubleCopy G D)⟩⟩

/-- Every finite graph of maximum degree at most `D` lies in a finite `D`-regular graph. -/
theorem exists_regular_extension {V : Type u} [Fintype V] (G : SimpleGraph V) (D : ℕ)
    (hu : ∀ v, G.degree v ≤ D) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      H.IsRegularOfDegree D ∧ Nonempty (Copy G H) :=
  exists_regular_extension_aux D G D hu (fun v => Nat.le_add_left D (G.degree v))

/-- The exact canonical root proposition, without its unproved target. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    StrongColorable G ((5 * (maximumDegree G) ^ 2) / 4)

/-- The same bound restricted to finite regular graphs. -/
def regularStatement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    (∃ D : ℕ, G.IsRegularOfDegree D) →
    StrongColorable G ((5 * (maximumDegree G) ^ 2) / 4)

/-- The full strong chromatic-index conjecture is equivalent to its regular-graph case. -/
theorem regular_reduction : statement ↔ regularStatement := by
  constructor
  · intro h n G _
    exact h n G
  · intro h n G
    rcases isEmpty_or_nonempty (Fin n) with hV | hV
    · let := hV
      have : IsEmpty G.edgeSet := inferInstance
      exact Colorable.of_isEmpty _
    · let := hV
      have hu : ∀ v, G.degree v ≤ maximumDegree G := by
        intro v
        exact G.degree_le_maxDegree v
      obtain ⟨m, H, hr, ⟨f⟩⟩ := exists_regular_extension G (maximumDegree G) hu
      have : Nonempty (Fin m) := ⟨f (Classical.arbitrary (Fin n))⟩
      have hm : maximumDegree H = maximumDegree G := by
        unfold maximumDegree
        exact hr.maxDegree_eq
      have hc := h m H ⟨maximumDegree G, hr⟩
      rw [hm] at hc
      exact strongColorable_restrict f hc


end Submissions.Erdos149RegularCaseReduction.Savcab
