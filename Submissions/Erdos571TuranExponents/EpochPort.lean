/-
Adapted 2026-09-05 for Jig330 from the proof by GPT-6 Astra in the Epoch AI
FrontierMath Erdős campaign (Tom Adamczewski and Thomas F. Bloom).
Public source: https://github.com/tadamcz/erdos571
Pinned commit: 661cc1d842c54661f55046d27abef531d0583b1e
Original module: Erdos571/Resolutions/Erdos571_325usd_42h.lean
Apache-2.0; accompanying LICENSE and NOTICE retained in campaign-discrete/erdos571-public.
Local changes: narrow Mathlib imports and port from Lean 4.28 to Jig's pinned Lean 4.33.
This is a port of existing mathematics, not a new solution discovered in this campaign.
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.all false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


/-!
# Erdős Problem 571

*References:*
- [erdosproblems.com/571](https://www.erdosproblems.com/571)

The proof constructs balanced rooted models for all rational parameters.
Its upper-bound closure replaces old edges by paths of arbitrary length,
adds two color-class hubs, and commutes with positive rooted powers.
-/

section -- RootedUnionDensity

/- Balance is preserved by unions of injective copies agreeing on their roots. -/
open Finset SimpleGraph
namespace RootedUnionDensity

variable {A R V I : Type*} [Fintype A] [Fintype R] [DecidableEq V]

noncomputable def interiors (f : A ⊕ R ↪ V) : Finset V := by
  classical
  exact univ.image (fun a => f (Sum.inl a))

noncomputable def copyEdges (G : SimpleGraph (A ⊕ R)) (f : A ⊕ R ↪ V) :
    Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.image (Sym2.map f)

noncomputable def incident (G : SimpleGraph (A ⊕ R)) (s : Finset A) :
    Finset (Sym2 (A ⊕ R)) := by
  classical
  exact G.edgeFinset.filter (fun e => ∃ a ∈ s, Sum.inl a ∈ e)

lemma mem_interiors (f : A ⊕ R ↪ V) (v : V) :
    v ∈ interiors f ↔ ∃ a, f (Sum.inl a) = v := by
  classical
  simp [interiors]

lemma endpoint_support (G : SimpleGraph (A ⊕ R)) (f : A ⊕ R ↪ V)
    {e : Sym2 V} (he : e ∈ copyEdges G f) {v : V} (hv : v ∈ e) :
    v ∈ interiors f ∨ ∃ r, f (Sum.inr r) = v := by
  classical
  obtain ⟨e, he, rfl⟩ := mem_image.mp he
  obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hv
  cases x with
  | inl a => exact Or.inl ((mem_interiors f _).mpr ⟨a,rfl⟩)
  | inr r => exact Or.inr ⟨r,rfl⟩

/-- Insert one copy into an already-supported edge set. -/
lemma insert_density (G : SimpleGraph (A ⊕ R)) (ρ : ℚ)
    (hbalance : ∀ s : Finset A, ρ * s.card ≤ (incident G s).card)
    (f : A ⊕ R ↪ V) (r : R → V) (hf : ∀ x, f (Sum.inr x) = r x)
    (U : Finset V) (E : Finset (Sym2 V))
    (hsupport : ∀ e ∈ E, ∀ v ∈ e, v ∈ U ∨ ∃ x, r x = v)
    (hdensity : ρ * U.card ≤ E.card) :
    ρ * (U ∪ interiors f).card ≤ (E ∪ copyEdges G f).card := by
  classical
  let s := univ.filter (fun a : A => f (Sum.inl a) ∉ U)
  have hnew : interiors f \ U = s.image (fun a => f (Sum.inl a)) := by
    ext v
    simp only [Finset.mem_sdiff, mem_interiors, mem_image, s, mem_filter, mem_univ,
      true_and]
    aesop
  have hvc : (U ∪ interiors f).card = U.card + s.card := by
    have hh := card_sdiff_add_card_eq_card (subset_union_left (s₁ := U) (s₂ := interiors f))
    rw [union_sdiff_left, hnew,
      card_image_of_injective _ (show Function.Injective (fun a : A => f (Sum.inl a)) from
        f.injective.comp Sum.inl_injective)] at hh
    omega
  have hnewedges : (incident G s).image (Sym2.map f) ⊆ copyEdges G f \ E := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    obtain ⟨hdG, a, ha, had⟩ := mem_filter.mp hd
    refine Finset.mem_sdiff.mpr ⟨mem_image.mpr ⟨d,hdG,rfl⟩, ?_⟩
    intro hold
    have hmem : f (Sum.inl a) ∈ Sym2.map f d := Sym2.mem_map.mpr ⟨_,had,rfl⟩
    rcases hsupport _ hold _ hmem with hU | ⟨x, hx⟩
    · exact (mem_filter.mp ha).2 hU
    · have heq : Sum.inr x = Sum.inl a := f.injective ((hf x).trans hx)
      exact Sum.inr_ne_inl heq
  have hec : (incident G s).card ≤ (copyEdges G f \ E).card := by
    simpa only [card_image_of_injective _ (Sym2.map.injective f.injective)] using
      card_le_card hnewedges
  have hEc : (E ∪ copyEdges G f).card = E.card + (copyEdges G f \ E).card := by
    have hh := card_sdiff_add_card_eq_card (subset_union_left (s₁ := E) (s₂ := copyEdges G f))
    rw [union_sdiff_left] at hh
    omega
  rw [hvc, hEc, Nat.cast_add, Nat.cast_add, mul_add]
  have hb := hbalance s
  have hec' : ((incident G s).card : ℚ) ≤ (copyEdges G f \ E).card := by exact_mod_cast hec
  linarith

/-- The union of common-root copies of a balanced rooted graph has at least
`ρ` edges per distinct internal vertex. Overlaps of interiors are allowed. -/
lemma union_density (G : SimpleGraph (A ⊕ R)) (ρ : ℚ)
    (hbalance : ∀ s : Finset A, ρ * s.card ≤ (incident G s).card)
    (f : I → (A ⊕ R ↪ V)) (r : R → V) (T : Finset I)
    (hf : ∀ i ∈ T, ∀ x, f i (Sum.inr x) = r x) :
    ρ * (T.biUnion (fun i => interiors (f i))).card ≤
      (T.biUnion (fun i => copyEdges G (f i))).card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hfT : ∀ i ∈ T, ∀ x, f i (Sum.inr x) = r x := fun i hi => hf i (mem_insert_of_mem hi)
    have hs : ∀ e ∈ T.biUnion (fun j => copyEdges G (f j)), ∀ v ∈ e,
        v ∈ T.biUnion (fun j => interiors (f j)) ∨ ∃ x, r x = v := by
      intro e he v hv
      obtain ⟨j, hj, he⟩ := mem_biUnion.mp he
      rcases endpoint_support G (f j) he hv with hv | ⟨x,hx⟩
      · exact Or.inl (mem_biUnion.mpr ⟨j,hj,hv⟩)
      · exact Or.inr ⟨x, (hfT j hj x).symm.trans hx⟩
    simpa only [biUnion_insert, union_comm] using
      insert_density G ρ hbalance (f i) r (hf i (mem_insert_self _ _))
        _ _ hs (ih hfT)

end RootedUnionDensity

end -- RootedUnionDensity

section -- GraphSubdivision

/- Subdivision and the transformation of rooted balance. -/
open Finset SimpleGraph
namespace GraphSubdivision
universe u

variable {V : Type u} (G : SimpleGraph V)
abbrev Edge := G.edgeSet


section Finite
variable [Fintype V] [DecidableEq V] [Fintype (Edge G)]


noncomputable def incidentEdges (s : Finset V) : Finset (Edge G) := by
  classical
  exact univ.filter (fun e => ∃ v ∈ s, v ∈ e.val)


end Finite

section Rooted
variable {A R : Type u} (F : SimpleGraph (A ⊕ R))


variable [Fintype A] [Fintype R] [Fintype (Edge F)] [DecidableEq A] [DecidableEq R]

lemma old_incident_count (s : Finset A) :
    (incidentEdges F (s.image Sum.inl)).card = (RootedUnionDensity.incident F s).card := by
  classical
  apply card_bij (fun e _ => e.val)
  · intro e he
    simp only [incidentEdges,mem_filter,mem_univ,true_and,mem_image] at he
    obtain ⟨v,⟨a,ha,rfl⟩,hv⟩ := he
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset]
    exact ⟨e.property,a,ha,hv⟩
  · intro e he f hf h
    exact Subtype.ext h
  · intro e he
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset] at he
    refine ⟨⟨e,he.1⟩,?_,rfl⟩
    simp only [incidentEdges,mem_filter,mem_univ,true_and]
    obtain ⟨a,ha,hae⟩ := he.2
    exact ⟨Sum.inl a,mem_image.mpr ⟨a,ha,rfl⟩,hae⟩


end Rooted
end GraphSubdivision

end -- GraphSubdivision

section -- ColoredEdges

/- Canonically orient the edges of a two-colored simple graph. -/
open SimpleGraph
namespace ColoredEdges
set_option maxHeartbeats 1500000
universe u
variable {W : Type u} {F : SimpleGraph W} (c : F.Coloring (Fin 2))
abbrev Edge := GraphSubdivision.Edge F

noncomputable def left (e : Edge (F := F)) : W := if c e.val.out.1=0 then e.val.out.1 else e.val.out.2
noncomputable def right (e : Edge (F := F)) : W := if c e.val.out.1=0 then e.val.out.2 else e.val.out.1

lemma out_adj (e : Edge (F := F)) : F.Adj e.val.out.1 e.val.out.2 := by
  change s(e.val.out.1,e.val.out.2)∈F.edgeSet
  have he : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
  rw [he]
  exact e.property

lemma left_color (e : Edge (F := F)) : c (left c e)=0 := by
  have hne := c.valid (out_adj e)
  dsimp [left]
  split_ifs with h
  · exact h
  · omega

lemma right_color (e : Edge (F := F)) : c (right c e)=1 := by
  have hne := c.valid (out_adj e)
  dsimp [right]
  split_ifs <;> omega

lemma pair (e : Edge (F := F)) : s(left c e,right c e)=e.val := by
  dsimp [left,right]
  split_ifs
  · exact e.val.out_eq
  · exact (Sym2.eq_swap).trans e.val.out_eq

lemma adj (e : Edge (F := F)) : F.Adj (left c e) (right c e) := by
  change s(left c e,right c e)∈F.edgeSet
  rw [pair]
  exact e.property

lemma mem_iff (e : Edge (F := F)) (w : W) : w∈e.val ↔ w=left c e ∨ w=right c e := by
  rw [← pair c e,Sym2.mem_iff]

lemma left_unique (e : Edge (F := F)) {w : W} (hw : w∈e.val) (hc : c w=0) : w=left c e := by
  rcases (mem_iff c e w).mp hw with h | h
  · exact h
  · rw [h,right_color] at hc; exact (by decide : (1 : Fin 2)≠0) hc |>.elim

lemma right_unique (e : Edge (F := F)) {w : W} (hw : w∈e.val) (hc : c w=1) : w=right c e := by
  rcases (mem_iff c e w).mp hw with h | h
  · rw [h,left_color] at hc; exact (by decide : (0 : Fin 2)≠1) hc |>.elim
  · exact h


end ColoredEdges

end -- ColoredEdges

section -- FinitePathIncidences

/- Incident-edge inequalities for a path with a finite set of selected internal vertices. -/
open Finset
namespace FinitePathIncidences
set_option maxHeartbeats 1500000
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- There are `k` internal vertices and `k+1` edges.  Vertex `v` meets
edges `v.castSucc` and `v.succ`. -/
def incident (k : ℕ) (x z : Prop) (T : Finset (Fin k)) : Finset (Fin (k+1)) :=
  univ.filter (fun i => (i=0 ∧ x) ∨ (i=Fin.last k ∧ z) ∨ ∃ v∈T, i=v.castSucc ∨ i=v.succ)

lemma mem_incident (k : ℕ) (x z : Prop) (T : Finset (Fin k)) (i : Fin (k+1)) :
    i∈incident k x z T ↔ (i=0 ∧ x) ∨ (i=Fin.last k ∧ z) ∨ ∃ v∈T, i=v.castSucc ∨ i=v.succ := by
  simp only [incident,mem_filter,mem_univ,true_and]

lemma left_mem (k : ℕ) (x z : Prop) (T : Finset (Fin k)) (hx : x) : 0∈incident k x z T :=
  (mem_incident k x z T 0).mpr (Or.inl ⟨rfl,hx⟩)

lemma right_mem (k : ℕ) (x z : Prop) (T : Finset (Fin k)) (hz : z) : Fin.last k∈incident k x z T :=
  (mem_incident k x z T _).mpr (Or.inr (Or.inl ⟨rfl,hz⟩))

lemma castSucc_mem (k : ℕ) (x z : Prop) (T : Finset (Fin k)) (v : Fin k) (hv : v∈T) :
    v.castSucc∈incident k x z T :=
  (mem_incident k x z T _).mpr (Or.inr (Or.inr ⟨v,hv,Or.inl rfl⟩))

lemma succ_mem (k : ℕ) (x z : Prop) (T : Finset (Fin k)) (v : Fin k) (hv : v∈T) :
    v.succ∈incident k x z T :=
  (mem_incident k x z T _).mpr (Or.inr (Or.inr ⟨v,hv,Or.inr rfl⟩))


lemma internal_add_one_le (k : ℕ) (x z : Prop) (T : Finset (Fin k)) (hT : T.Nonempty) :
    T.card+1≤(incident k x z T).card := by
  let v := T.max' hT
  let L := T.image Fin.castSucc
  have hv : v∈T := max'_mem T hT
  have hnot : v.succ∉L := by
    intro hh
    obtain ⟨w,hw,he⟩ := mem_image.mp hh
    have hle := le_max' T w hw
    have hval := congrArg Fin.val he
    change w.val=v.val+1 at hval
    have hh : w.val≤v.val := hle
    omega
  have hsub : insert v.succ L⊆incident k x z T := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact succ_mem k x z T v hv
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hi
      exact castSucc_mem k x z T w hw
  have hcard : (insert v.succ L).card=T.card+1 := by
    rw [card_insert_of_notMem hnot]
    simp only [L,card_image_of_injective _ (Fin.castSucc_injective (n := k))]
  rw [← hcard]
  exact card_le_card hsub

lemma endpoint_plus_internal (k : ℕ) (x z : Prop) (T : Finset (Fin k)) :
    (if x∨z then 1 else 0)+T.card≤(incident k x z T).card := by
  by_cases hT : T.Nonempty
  · have hh := internal_add_one_le k x z T hT
    split_ifs <;> omega
  · have he : T=∅ := not_nonempty_iff_eq_empty.mp hT
    subst T
    simp only [card_empty,add_zero]
    split_ifs with hx
    · apply card_pos.mpr
      rcases hx with hx | hz
      · exact ⟨0,left_mem k x z ∅ hx⟩
      · exact ⟨Fin.last k,right_mem k x z ∅ hz⟩
    · exact Nat.zero_le _

lemma internal_ratio (k : ℕ) (x z : Prop) (T : Finset (Fin k)) :
    (k+1)*T.card≤k*(incident k x z T).card := by
  by_cases hT : T.Nonempty
  · have hh := internal_add_one_le k x z T hT
    have hc : T.card≤k := by simpa only [Fintype.card_fin] using card_le_univ T
    have hm := Nat.mul_le_mul_left k hh
    nlinarith only [hc,hm]
  · rw [not_nonempty_iff_eq_empty.mp hT,card_empty,mul_zero]
    exact Nat.zero_le _

end
end FinitePathIncidences

end -- FinitePathIncidences

section -- HubPathSubdivision

/- Two color-class hubs attached to arbitrary-length edge replacement paths.
This module is finite graph infrastructure, not an extremal upper theorem. -/
open Finset SimpleGraph
namespace HubPathSubdivision
set_option maxHeartbeats 2500000
universe u
variable {W : Type u} {F : SimpleGraph W} (c : F.Coloring (Fin 2))
abbrev E := GraphSubdivision.Edge F
abbrev CoreVertex (k : ℕ) := W ⊕ (E (F := F) × Fin k)
abbrev Vertex (k : ℕ) := Fin 2 ⊕ CoreVertex (F := F) k

noncomputable def point (k : ℕ) (e : E (F := F)) (i : Fin (k+2)) : CoreVertex (F := F) k :=
  if h0 : i.val=0 then Sum.inl (ColoredEdges.left c e)
  else if hlast : i.val=k+1 then Sum.inl (ColoredEdges.right c e)
  else Sum.inr (e,⟨i.val-1,by have := i.isLt; omega⟩)

lemma point_zero (k : ℕ) (e : E (F := F)) : point c k e 0=Sum.inl (ColoredEdges.left c e) := by
  simp [point]

lemma point_last (k : ℕ) (e : E (F := F)) :
    point c k e (Fin.last (k+1))=Sum.inl (ColoredEdges.right c e) := by simp [point]

lemma point_mid_iff (k : ℕ) (e f : E (F := F)) (i : Fin (k+2)) (j : Fin k) :
    point c k e i=Sum.inr (f,j) ↔ e=f ∧ i.val=j.val+1 := by
  dsimp only [point]
  split_ifs with h0 hl
  · simp only [Sum.inl_ne_inr,false_iff,not_and]
    intro _
    omega
  · simp only [Sum.inl_ne_inr,false_iff,not_and]
    intro _
    have := j.isLt
    omega
  · simp only [Sum.inr.injEq,Prod.mk.injEq,Fin.ext_iff]
    have := i.isLt
    apply and_congr Iff.rfl
    omega

lemma point_mid (k : ℕ) (e : E (F := F)) (j : Fin k) :
    point c k e j.succ.castSucc=Sum.inr (e,j) :=
  (point_mid_iff c k e e _ j).mpr ⟨rfl,rfl⟩

lemma left_ne_right (e : E (F := F)) : ColoredEdges.left c e≠ColoredEdges.right c e :=
  (ColoredEdges.adj c e).ne

noncomputable def level (k : ℕ) (e : E (F := F)) : CoreVertex (F := F) k → ℕ := by
  classical
  exact Sum.elim (fun w => if w=ColoredEdges.left c e then 0 else k+1) (fun p => p.2.val+1)

lemma point_level (k : ℕ) (e : E (F := F)) (i : Fin (k+2)) :
    level c k e (point c k e i)=i.val := by
  classical
  dsimp only [point]
  split_ifs with h0 hl
  · simp [level,h0]
  · simp [level,(left_ne_right c e).symm,hl]
  · simp only [level,Sum.elim_inr]
    omega

lemma point_injective (k : ℕ) (e : E (F := F)) : Function.Injective (point c k e) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg (level c k e) he
  simpa only [point_level] using hh

noncomputable def coreEdge (k : ℕ) (e : E (F := F)) (i : Fin (k+1)) : Sym2 (CoreVertex (F := F) k) :=
  s(point c k e i.castSucc,point c k e i.succ)

lemma coreEdge_middle (k : ℕ) (hk : 0<k) (e : E (F := F)) (i : Fin (k+1)) :
    ∃ j : Fin k, Sum.inr (e,j)∈coreEdge c k e i := by
  by_cases hi : i.val=0
  · let j : Fin k := ⟨0,hk⟩
    have he : point c k e i.succ=Sum.inr (e,j) :=
      (point_mid_iff c k e e _ j).mpr ⟨rfl,by change i.val+1=0+1; omega⟩
    refine ⟨j,?_⟩
    rw [← he]
    exact Sym2.mem_mk_right _ _
  · let j : Fin k := ⟨i.val-1,by have := i.isLt; omega⟩
    have he : point c k e i.castSucc=Sum.inr (e,j) :=
      (point_mid_iff c k e e _ j).mpr ⟨rfl,by change i.val=i.val-1+1; omega⟩
    refine ⟨j,?_⟩
    rw [← he]
    exact Sym2.mem_mk_left _ _

lemma middle_mem_coreEdge (k : ℕ) (e f : E (F := F)) (j : Fin k) (i : Fin (k+1))
    (h : Sum.inr (e,j)∈coreEdge c k f i) : e=f := by
  rcases Sym2.mem_iff.mp h with h | h
  · exact ((point_mid_iff c k f e i.castSucc j).mp h.symm).1.symm
  · exact ((point_mid_iff c k f e i.succ j).mp h.symm).1.symm

lemma coreEdge_injective (k : ℕ) : Function.Injective (fun p : E (F := F) × Fin (k+1) => coreEdge c k p.1 p.2) := by
  rintro ⟨e,i⟩ ⟨f,j⟩ h
  dsimp only at h
  have hef : e=f := by
    by_cases hk : k=0
    · subst k
      have hi : i=0 := by apply Fin.ext; have := i.isLt; change i.val=0; omega
      have hj : j=0 := by apply Fin.ext; have := j.isLt; change j.val=0; omega
      have he : coreEdge c 0 e i=Sym2.map Sum.inl e.val := by
        rw [hi]
        rw [← ColoredEdges.pair c e]
        simp [coreEdge,point]
      have hf : coreEdge c 0 f j=Sym2.map Sum.inl f.val := by
        rw [hj]
        rw [← ColoredEdges.pair c f]
        simp [coreEdge,point]
      rw [he,hf] at h
      exact Subtype.ext (Sym2.map.injective Sum.inl_injective h)
    · obtain ⟨l,hl⟩ := coreEdge_middle c k (Nat.pos_of_ne_zero hk) e i
      rw [h] at hl
      exact middle_mem_coreEdge c k e f l j hl
  subst f
  have hij : i=j := by
    have hh : s(i.castSucc,i.succ)=s(j.castSucc,j.succ) :=
      Sym2.map.injective (point_injective c k e) h
    rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Fin.castSucc_injective (k+1) h1
    · have h1' := congrArg Fin.val h1
      have h2' := congrArg Fin.val h2
      simp only [Fin.val_castSucc,Fin.val_succ] at h1' h2'
      omega
  exact Prod.ext rfl hij

noncomputable def graph (k : ℕ) : SimpleGraph (Vertex (F := F) k) where
  Adj u v := match u,v with
    | Sum.inl _,Sum.inl _ => False
    | Sum.inl i,Sum.inr a => match a with
      | Sum.inl w => c w=i
      | Sum.inr _ => False
    | Sum.inr a,Sum.inl i => match a with
      | Sum.inl w => c w=i
      | Sum.inr _ => False
    | Sum.inr a,Sum.inr b => ∃ e i, s(a,b)=coreEdge c k e i
  symm := by
    constructor
    intro u v h
    rcases u with i | a | e <;> rcases v with j | b | f
    all_goals first | exact h | simpa only [Sym2.eq_swap] using h
  loopless := by
    constructor
    intro u
    rcases u with i | a
    · exact not_false
    · rintro ⟨e,j,h⟩
      have hne : point c k e j.castSucc≠point c k e j.succ := by
        intro he
        have hh := congrArg Fin.val (point_injective c k e he)
        simp only [Fin.val_castSucc,Fin.val_succ] at hh
        omega
      rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact hne (h1.symm.trans h2)
      · exact hne (h2.symm.trans h1)

lemma coreEdge_adj (k : ℕ) (e : E (F := F)) (i : Fin (k+1)) :
    (graph c k).Adj (Sum.inr (point c k e i.castSucc)) (Sum.inr (point c k e i.succ)) := by
  change ∃ e' i', s(point c k e i.castSucc,point c k e i.succ)=coreEdge c k e' i'
  exact ⟨e,i,rfl⟩


def parity (n : ℕ) : Fin 2 := ⟨n%2,by omega⟩
def oldPaint (k : ℕ) (i : Fin 2) : Fin 2 := if i=0 then 0 else parity (k+1)
def flip (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

lemma flip_ne (i : Fin 2) : flip i≠i := by fin_cases i <;> decide

lemma parity_ne_succ (n : ℕ) : parity n≠parity (n+1) := by
  intro h
  have hh := congrArg Fin.val h
  dsimp only [parity] at hh
  omega

noncomputable def corePaint (k : ℕ) : CoreVertex (F := F) k → Fin 2 :=
  Sum.elim (fun w => oldPaint k (c w)) (fun p => parity (p.2.val+1))

lemma point_paint (k : ℕ) (e : E (F := F)) (i : Fin (k+2)) :
    corePaint c k (point c k e i)=parity i.val := by
  dsimp only [point]
  split_ifs with h0 hl
  · simp [corePaint,oldPaint,ColoredEdges.left_color,h0,parity]
  · simp [corePaint,oldPaint,ColoredEdges.right_color,hl]
  · simp only [corePaint,Sum.elim_inr]
    congr 1
    omega

noncomputable def color (k : ℕ) : (graph c k).Coloring (Fin 2) :=
  Coloring.mk (Sum.elim (fun i => flip (oldPaint k i)) (corePaint c k)) (by
    intro u v h
    rcases u with i | a <;> rcases v with j | b
    · exact h.elim
    · cases b with
      | inl w =>
        change c w=i at h
        change flip (oldPaint k i)≠oldPaint k (c w)
        rw [h]
        exact flip_ne _
      | inr e => exact h.elim
    · cases a with
      | inl w =>
        change c w=j at h
        change oldPaint k (c w)≠flip (oldPaint k j)
        rw [h]
        exact (flip_ne _).symm
      | inr e => exact h.elim
    · obtain ⟨e,l,h⟩ := h
      have hne : corePaint c k (point c k e l.castSucc)≠corePaint c k (point c k e l.succ) := by
        rw [point_paint,point_paint]
        exact parity_ne_succ l.val
      rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hne
      · exact hne.symm)

lemma point_reachable (k : ℕ) (e : E (F := F)) (i : Fin (k+2)) :
    (graph c k).Reachable (Sum.inr (point c k e 0)) (Sum.inr (point c k e i)) := by
  induction i using Fin.induction with
  | zero => exact Reachable.refl _
  | succ i ih => exact ih.trans (coreEdge_adj c k e i).reachable

lemma endpoints_reachable (k : ℕ) (e : E (F := F)) :
    (graph c k).Reachable (Sum.inr (Sum.inl (ColoredEdges.left c e)))
      (Sum.inr (Sum.inl (ColoredEdges.right c e))) := by
  simpa only [point_zero,point_last] using point_reachable c k e (Fin.last (k+1))

lemma old_edge_reachable (k : ℕ) {x y : W} (hxy : F.Adj x y) :
    (graph c k).Reachable (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl y)) := by
  let e : E (F := F) := ⟨s(x,y),hxy⟩
  have hx := (ColoredEdges.mem_iff c e x).mp (Sym2.mem_mk_left _ _)
  have hy := (ColoredEdges.mem_iff c e y).mp (Sym2.mem_mk_right _ _)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx,hy]
  · exact endpoints_reachable c k e
  · exact (endpoints_reachable c k e).symm

lemma old_reachable (k : ℕ) {x y : W} (h : F.Reachable x y) :
    (graph c k).Reachable (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inl y)) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x y z hxy p ih => exact (old_edge_reachable c k hxy).trans ih

lemma connected (k : ℕ) (hF : F.Connected) (hsur : Function.Surjective c) :
    (graph c k).Connected := by
  obtain ⟨x⟩ := hF.nonempty
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Sum.inr (Sum.inl x),?_⟩
  intro v
  rcases v with i | y | ⟨e,j⟩
  · obtain ⟨w,hw⟩ := hsur i
    exact (old_reachable c k (hF x w)).trans
      (show (graph c k).Adj (Sum.inr (Sum.inl w)) (Sum.inl i) from hw).reachable
  · exact old_reachable c k (hF x y)
  · have hh := point_reachable c k e j.succ.castSucc
    rw [point_zero,point_mid] at hh
    exact (old_reachable c k (hF x (ColoredEdges.left c e))).trans hh

end HubPathSubdivision

end -- HubPathSubdivision

section -- HubPathIncidences

/- Summed path-incidence inequalities for arbitrary-length replacement paths. -/
open Finset SimpleGraph
namespace HubPathIncidences
set_option maxHeartbeats 2000000
universe u
variable {W : Type u} {F : SimpleGraph W} (c : F.Coloring (Fin 2))
abbrev E := GraphSubdivision.Edge F
noncomputable section
local instance : DecidableEq W := Classical.decEq _
local instance : DecidableEq (E (F := F)) := Classical.decEq _

variable (k : ℕ)

def midFiber (T : Finset (E (F := F) × Fin k)) (e : E (F := F)) : Finset (Fin k) :=
  univ.filter (fun i => (e,i)∈T)

def edgeFiber (S : Finset W) (T : Finset (E (F := F) × Fin k)) (e : E (F := F)) : Finset (Fin (k+1)) :=
  FinitePathIncidences.incident k (ColoredEdges.left c e∈S) (ColoredEdges.right c e∈S) (midFiber k T e)

variable [Fintype (E (F := F))]

def incidences (S : Finset W) (T : Finset (E (F := F) × Fin k)) : Finset (E (F := F) × Fin (k+1)) :=
  univ.filter (fun p => p.2∈edgeFiber c k S T p.1)

lemma incidences_count (S : Finset W) (T : Finset (E (F := F) × Fin k)) :
    (incidences c k S T).card=∑ e, (edgeFiber c k S T e).card := by
  simp only [incidences,card_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro e _
  symm
  rw [← card_filter]
  congr 1
  ext i
  simp

lemma midpoint_count (T : Finset (E (F := F) × Fin k)) : T.card=∑ e, (midFiber k T e).card := by
  have hT : univ.filter (fun p => p∈T)=T := by ext p; simp
  conv_lhs => rw [← hT]
  simp only [card_filter,Fintype.sum_prod_type,midFiber]

lemma old_count (S : Finset W) : (GraphSubdivision.incidentEdges F S).card=
    ∑ e : E (F := F), if ColoredEdges.left c e∈S ∨ ColoredEdges.right c e∈S then 1 else 0 := by
  simp only [GraphSubdivision.incidentEdges,card_filter]
  apply sum_congr rfl
  intro e _
  congr 1
  apply propext
  constructor
  · rintro ⟨w,hw,hwe⟩
    rcases (ColoredEdges.mem_iff c e w).mp hwe with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  · rintro (h | h)
    · exact ⟨ColoredEdges.left c e,h,(ColoredEdges.mem_iff c e _).mpr (Or.inl rfl)⟩
    · exact ⟨ColoredEdges.right c e,h,(ColoredEdges.mem_iff c e _).mpr (Or.inr rfl)⟩

lemma old_plus_midpoints (S : Finset W) (T : Finset (E (F := F) × Fin k)) :
    (GraphSubdivision.incidentEdges F S).card+T.card≤(incidences c k S T).card := by
  rw [old_count c,midpoint_count,incidences_count,← sum_add_distrib]
  apply sum_le_sum
  intro e _
  have hh := FinitePathIncidences.endpoint_plus_internal k
    (ColoredEdges.left c e∈S) (ColoredEdges.right c e∈S) (midFiber k T e)
  by_cases he : ColoredEdges.left c e∈S ∨ ColoredEdges.right c e∈S
  · simpa only [if_pos he,edgeFiber] using hh
  · simpa only [if_neg he,edgeFiber] using hh

lemma midpoint_ratio (S : Finset W) (T : Finset (E (F := F) × Fin k)) :
    (k+1)*T.card≤k*(incidences c k S T).card := by
  rw [midpoint_count,incidences_count,mul_sum,mul_sum]
  apply sum_le_sum
  intro e _
  exact FinitePathIncidences.internal_ratio k _ _ (midFiber k T e)

lemma selected (S : Finset W) (T : Finset (E (F := F) × Fin k)) (p : E (F := F) × Fin (k+1))
    (hp : p∈incidences c k S T) :
    ∃ v∈S.disjSum T, v∈HubPathSubdivision.coreEdge c k p.1 p.2 := by
  obtain ⟨e,i⟩ := p
  have hh := (mem_filter.mp hp).2
  change i∈FinitePathIncidences.incident k _ _ _ at hh
  rcases (FinitePathIncidences.mem_incident k _ _ _ i).mp hh with ⟨hi,hs⟩ | ⟨hi,hs⟩ | ⟨j,hj,hi⟩
  · refine ⟨Sum.inl (ColoredEdges.left c e),by simpa using hs,?_⟩
    subst i
    have he : HubPathSubdivision.point c k e (0 : Fin (k+1)).castSucc=Sum.inl (ColoredEdges.left c e) :=
      HubPathSubdivision.point_zero c k e
    rw [← he]
    exact Sym2.mem_mk_left _ _
  · refine ⟨Sum.inl (ColoredEdges.right c e),by simpa using hs,?_⟩
    subst i
    have he : HubPathSubdivision.point c k e (Fin.last k).succ=Sum.inl (ColoredEdges.right c e) :=
      HubPathSubdivision.point_last c k e
    rw [← he]
    exact Sym2.mem_mk_right _ _
  · have hj' : (e,j)∈T := (mem_filter.mp hj).2
    refine ⟨Sum.inr (e,j),by simpa using hj',?_⟩
    rcases hi with rfl | rfl
    · have he : HubPathSubdivision.point c k e j.castSucc.succ=Sum.inr (e,j) :=
        (HubPathSubdivision.point_mid_iff c k e e _ j).mpr ⟨rfl,rfl⟩
      rw [← he]
      exact Sym2.mem_mk_right _ _
    · rw [← HubPathSubdivision.point_mid c k e j]
      exact Sym2.mem_mk_left _ _

end
end HubPathIncidences

end -- HubPathIncidences

section -- HubPathBalanceArithmetic

/- The numerical balance inequality for an arbitrary-length two-hub replacement. -/
namespace HubPathBalanceArithmetic

lemma balance (a b k x y I J N : ℕ)
    (hold : b*x≤a*I) (hpath : I+y≤J) (hmid : (k+1)*y≤k*J) (hspoke : J+x≤N) :
    (a+(k+1)*b)*(x+y)≤(a+k*b)*N := by
  have hp := Nat.mul_le_mul_left a hpath
  have hm := Nat.mul_le_mul_left b hmid
  have hs := Nat.mul_le_mul_left (a+k*b) hspoke
  nlinarith only [hold,hp,hm,hs]

end HubPathBalanceArithmetic

end -- HubPathBalanceArithmetic

section -- EdgeLinks

/- Counting four-cycles through the links of edges. -/
open Finset SimpleGraph
namespace EdgeLinks
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

def two (x y : V) : ℕ := (univ.filter (fun z => G.Adj x z ∧ G.Adj y z)).card

def three (x y : V) : Finset (V × V) :=
  univ.filter (fun p => G.Adj x p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 y)

def properThree (x y : V) : Finset (V × V) :=
  (three G x y).filter (fun p => p.1 ≠ y ∧ p.2 ≠ x)

lemma degree_sum (x : V) : G.degree x = ∑ y, if G.Adj x y then 1 else 0 := by
  simp [← G.card_neighborFinset_eq_degree,neighborFinset_eq_filter]

lemma sum_two : ∑ x, ∑ y, two G x y = ∑ z, G.degree z ^ 2 := by
  symm
  calc
    _ = ∑ z, ∑ x, ∑ y, if G.Adj z x ∧ G.Adj z y then 1 else 0 := by
      apply sum_congr rfl
      intro z hz
      rw [pow_two, degree_sum]
      simp_rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      split_ifs <;> simp_all
    _ = ∑ x, ∑ y, ∑ z, if G.Adj x z ∧ G.Adj y z then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
      simp_rw [G.adj_comm]
    _ = _ := by simp only [two,card_filter]

lemma two_sq (x y : V) : two G x y ^ 2 =
    ∑ u, ∑ v, if (G.Adj x u ∧ G.Adj y u) ∧ (G.Adj x v ∧ G.Adj y v) then 1 else 0 := by
  rw [pow_two]
  simp only [two,card_filter,sum_mul,mul_sum]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  split_ifs <;> simp_all

lemma four_eq_sum_three : (∑ x, ∑ y, two G x y ^ 2) =
    ∑ x, ∑ u, if G.Adj x u then (three G u x).card else 0 := by
  calc
    _ = ∑ x, ∑ y, ∑ u, ∑ v,
        if (G.Adj x u ∧ G.Adj y u) ∧ (G.Adj x v ∧ G.Adj y v) then 1 else 0 := by
      simp only [two_sq]
    _ = ∑ x, ∑ u, ∑ y, ∑ v,
        if G.Adj x u ∧ G.Adj u y ∧ G.Adj y v ∧ G.Adj v x then 1 else 0 := by
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
      apply sum_congr rfl
      intro u hu
      apply sum_congr rfl
      intro y hy
      apply sum_congr rfl
      intro v hv
      congr 1
      simp only [G.adj_comm,and_assoc,and_comm,and_left_comm]
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro u hu
      by_cases hxu : G.Adj x u
      · simp only [hxu,true_and,if_true,three,card_filter,Fintype.sum_prod_type]
      · simp [hxu]

lemma min_degree_four_le [Nonempty V] (δ : ℕ) (hδ : ∀ v, δ ≤ G.degree v) :
    δ^4 ≤ ∑ x, ∑ y, two G x y ^ 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (V × V)))
    (f := fun p => two G p.1 p.2)
  simp only [card_univ,Fintype.card_prod,Fintype.sum_prod_type] at hcs
  norm_cast at hcs
  have hl : Fintype.card V * δ^2 ≤ ∑ x, ∑ y, two G x y := by
    rw [sum_two]
    calc
      _ = ∑ _z : V, δ^2 := by simp
      _ ≤ _ := sum_le_sum (fun z hz => Nat.pow_le_pow_left (hδ z) 2)
  have hpow := Nat.pow_le_pow_left hl 2
  have hm : Fintype.card V ^ 2 * δ^4 ≤
      Fintype.card V ^ 2 * (∑ x, ∑ y, two G x y ^ 2) := by
    calc
      _ = (Fintype.card V * δ^2)^2 := by ring
      _ ≤ _ := hpow.trans hcs
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hm (pow_pos Fintype.card_pos 2)

lemma three_le_proper_add_degrees (x y : V) :
    (three G x y).card ≤ (properThree G x y).card + G.degree x + G.degree y := by
  let B₁ := (three G x y).filter (fun p => p.1 = y)
  let B₂ := (three G x y).filter (fun p => p.2 = x)
  have hc : three G x y ⊆ properThree G x y ∪ B₁ ∪ B₂ := by
    intro p hp
    by_cases h₁ : p.1 = y
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp,h₁⟩))
    by_cases h₂ : p.2 = x
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,h₂⟩)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,h₁,h₂⟩))
  have hB₁ : B₁.card ≤ G.degree y := by
    rw [← G.card_neighborFinset_eq_degree]
    apply card_le_card_of_injOn Prod.snd
    · intro p hp
      have hh := (mem_filter.mp hp).1
      have he := (mem_filter.mp hp).2
      have ha := (mem_filter.mp hh).2.2.1
      rw [he] at ha
      exact (G.mem_neighborFinset y p.2).mpr ha
    · intro p hp q hq he
      exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) he
  have hB₂ : B₂.card ≤ G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      have hh := (mem_filter.mp hp).1
      exact (G.mem_neighborFinset x p.1).mpr (mem_filter.mp hh).2.1
    · intro p hp q hq he
      exact Prod.ext he ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
  have hh := (card_le_card hc).trans (card_union_le _ _)
  have hh' := card_union_le (properThree G x y) B₁
  omega

/-- A graph in which each edge closes at most `M` injective length-three paths
satisfies this fourth-moment degree inequality. -/
lemma degree_bound [Nonempty V] (δ Δ M : ℕ)
    (hδ : ∀ v, δ ≤ G.degree v) (hΔ : ∀ v, G.degree v ≤ Δ)
    (hlinks : ∀ x y, G.Adj x y → (properThree G x y).card ≤ M) :
    δ^4 ≤ Fintype.card V * Δ * (M + 2*Δ) := by
  have hp (x y : V) (hxy : G.Adj x y) : (three G x y).card ≤ M+2*Δ := by
    have hh := three_le_proper_add_degrees G x y
    have hm := hlinks x y hxy
    have hx := hΔ x
    have hy := hΔ y
    omega
  calc
    δ^4 ≤ ∑ x, ∑ y, two G x y ^ 2 := min_degree_four_le G δ hδ
    _ = ∑ x, ∑ u, if G.Adj x u then (three G u x).card else 0 := four_eq_sum_three G
    _ ≤ ∑ x, ∑ u, if G.Adj x u then M+2*Δ else 0 := by
      apply sum_le_sum
      intro x hx
      apply sum_le_sum
      intro u hu
      split_ifs with hxu
      · exact hp u x hxu.symm
      · rfl
    _ = ∑ x, G.degree x * (M+2*Δ) := by
      apply sum_congr rfl
      intro x hx
      rw [degree_sum,sum_mul]
      simp
    _ ≤ ∑ _x : V, Δ * (M+2*Δ) := sum_le_sum (fun x hx => Nat.mul_le_mul_right _ (hΔ x))
    _ = _ := by simp [mul_assoc]

lemma real_degree_bound [Nonempty V] (δ Δ : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hδ : ∀ v, δ ≤ G.degree v) (hΔ : ∀ v, G.degree v ≤ Δ)
    (hlinks : ∀ x y, G.Adj x y → ((properThree G x y).card : ℝ) ≤ M) :
    (δ : ℝ)^4 ≤ (Fintype.card V : ℝ) * Δ * (M + 2*Δ) := by
  have hnat : ∀ x y, G.Adj x y → (properThree G x y).card ≤ ⌊M⌋₊ := by
    intro x y hxy
    exact (Nat.le_floor_iff hM).mpr (hlinks x y hxy)
  have hh : (δ : ℝ)^4 ≤ (Fintype.card V : ℝ) * Δ * ((⌊M⌋₊ : ℝ) + 2*Δ) := by
    exact_mod_cast degree_bound G δ Δ ⌊M⌋₊ hδ hΔ hnat
  exact hh.trans (by gcongr; exact Nat.floor_le hM)

end EdgeLinks

end -- EdgeLinks

section -- Regularization

/- Finite sampling and almost-regular dense subgraphs. -/
open Finset SimpleGraph
namespace Regularization
set_option maxHeartbeats 1000000

/-- Among all `k`-subsets, one carries at least a `k / |s|` fraction of any real
weight sum. This is the deterministic averaging step used in regularization. -/
lemma weighted_subset {A : Type*} [DecidableEq A] (s : Finset A) (w : A → ℝ)
    (k : ℕ) (hk : k ≤ s.card) :
    ∃ t ⊆ s, t.card = k ∧ (k : ℝ) * (∑ a ∈ s, w a) ≤ (s.card : ℝ) * ∑ a ∈ t, w a := by
  induction s using Finset.strongInductionOn generalizing k
  rename_i s ih
  by_cases hk0 : k = 0
  · subst k
    exact ⟨∅,empty_subset _,by simp,by simp⟩
  by_cases hkeq : k = s.card
  · exact ⟨s,Subset.refl _,hkeq.symm,by simp [hkeq]⟩
  have hs : s.Nonempty := card_pos.mp (by omega)
  obtain ⟨a,ha,hmin⟩ := s.exists_min_image w hs
  have hks : k ≤ (s.erase a).card := by rw [card_erase_of_mem ha]; omega
  obtain ⟨t,ht,hcard,htsum⟩ := ih (s.erase a) (erase_ssubset ha) k hks
  have hm : (0 : ℝ) < (s.erase a).card := by exact_mod_cast (by omega : 0 < (s.erase a).card)
  have hminsum : ((s.erase a).card : ℝ) * w a ≤ ∑ b ∈ s.erase a, w b := by
    calc
      _ = ∑ _b ∈ s.erase a, w a := by simp
      _ ≤ _ := sum_le_sum (fun b hb => hmin b (mem_of_mem_erase hb))
  have hweight : (k : ℝ) * w a ≤ ∑ b ∈ t, w b := by
    apply le_of_mul_le_mul_left _ hm
    calc
      ((s.erase a).card : ℝ) * ((k : ℝ) * w a) = (k : ℝ) * ((s.erase a).card * w a) := by ring
      _ ≤ (k : ℝ) * ∑ b ∈ s.erase a, w b := mul_le_mul_of_nonneg_left hminsum (Nat.cast_nonneg k)
      _ ≤ _ := htsum
  refine ⟨t,ht.trans (erase_subset _ _),hcard,?_⟩
  have hsum : (∑ b ∈ s, w b) = (∑ b ∈ s.erase a, w b) + w a := (sum_erase_add _ _ ha).symm
  have hcardS : (s.card : ℝ) = (s.erase a).card + 1 := by exact_mod_cast (card_erase_add_one ha).symm
  rw [hsum,hcardS]
  nlinarith

section Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]

def cross (s t : Finset V) : ℕ := ∑ y ∈ t, (s.filter (fun x => H.Adj x y)).card

lemma cross_univ (s : Finset V) : cross H s univ = ∑ x ∈ s, H.degree x := by
  simp only [cross,card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  simp [← H.card_neighborFinset_eq_degree,neighborFinset_eq_filter]

lemma cross_le_induced_edges (s t : Finset V) :
    cross H s t ≤ 2 * (H.induce (↑(s∪t) : Set V)).edgeFinset.card := by
  let C : Finset (V × V) := (s ×ˢ t).filter (fun p => H.Adj p.1 p.2)
  have hC : C.card = cross H s t := by
    simp only [C,card_filter,sum_product,cross]
    rw [sum_comm]
  let f : C → (H.induce (↑(s∪t) : Set V)).Dart := fun p => {
    toProd := (⟨p.val.1,mem_union_left _ (mem_product.mp (mem_filter.mp p.property).1).1⟩,
      ⟨p.val.2,mem_union_right _ (mem_product.mp (mem_filter.mp p.property).1).2⟩)
    adj := (mem_filter.mp p.property).2 }
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d : (H.induce (↑(s∪t) : Set V)).Dart => d.fst.val) hpq
    · exact congrArg (fun d : (H.induce (↑(s∪t) : Set V)).Dart => d.snd.val) hpq
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe,hC,SimpleGraph.dart_card_eq_twice_card_edges] at hh
  exact hh

/-- The degree mass of any set can be witnessed on an induced subgraph with at
most twice as many vertices. -/
lemma capture_degree_mass (s : Finset V) :
    ∃ u : Finset V, s ⊆ u ∧ u.card ≤ 2*s.card ∧
      (s.card : ℝ) * (∑ v ∈ s, (H.degree v : ℝ)) ≤
        2 * Fintype.card V * ((H.induce (↑u : Set V)).edgeFinset.card : ℝ) := by
  obtain ⟨t,ht,htcard,hw⟩ := weighted_subset univ
    (fun y : V => ((s.filter (fun x => H.Adj x y)).card : ℝ)) s.card (card_le_univ s)
  have hsumeq : (∑ y : V, (s.filter (fun x => H.Adj x y)).card) = ∑ v ∈ s, H.degree v :=
    cross_univ H s
  simp only [card_univ,← Nat.cast_sum] at hw
  rw [hsumeq] at hw
  refine ⟨s∪t,subset_union_left,?_,?_⟩
  · have hh := card_union_le s t
    omega
  · have hc : (cross H s t : ℝ) ≤ 2 * ((H.induce (↑(s∪t) : Set V)).edgeFinset.card : ℝ) := by
      exact_mod_cast cross_le_induced_edges H s t
    rw [← Nat.cast_sum]
    calc
      _ ≤ (Fintype.card V : ℝ) * (cross H s t : ℝ) := hw
      _ ≤ (Fintype.card V : ℝ) * (2 * ((H.induce (↑(s∪t) : Set V)).edgeFinset.card : ℝ)) := by gcongr
      _ = _ := by ring
lemma small_set_degree_mass (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 0 ≤ C)
    (hdensity : ∀ u : Finset V,
      ((H.induce (↑u : Set V)).edgeFinset.card : ℝ) ≤ C * (u.card : ℝ)^γ)
    (s : Finset V) (hs : s.Nonempty) :
    (∑ v ∈ s, (H.degree v : ℝ)) ≤
      2 * Fintype.card V * C * (2 : ℝ)^γ * (s.card : ℝ)^(γ-1) := by
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  obtain ⟨u,hsu,huc,hcap⟩ := capture_degree_mass H s
  have hpow : (u.card : ℝ)^γ ≤ (2*(s.card : ℝ))^γ := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by linarith)
    exact_mod_cast huc
  have hmul : (s.card : ℝ) * (∑ v ∈ s, (H.degree v : ℝ)) ≤
      (s.card : ℝ) * (2 * Fintype.card V * C * (2 : ℝ)^γ * (s.card : ℝ)^(γ-1)) := by
    calc
      _ ≤ 2 * Fintype.card V * ((H.induce (↑u : Set V)).edgeFinset.card : ℝ) := hcap
      _ ≤ 2 * Fintype.card V * (C * (u.card : ℝ)^γ) := by gcongr; exact hdensity u
      _ ≤ 2 * Fintype.card V * (C * (2*(s.card : ℝ))^γ) := by gcongr
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) hspos.le]
        have he : (s.card : ℝ)^γ = (s.card : ℝ)^(γ-1) * s.card := by
          calc
            _ = (s.card : ℝ)^((γ-1)+1) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hspos,Real.rpow_one]
        rw [he]
        ring
  exact le_of_mul_le_mul_left hmul hspos

/-- If no induced subgraph has greater normalized density, vertices whose degrees
are much larger than average carry at most half the degree mass. -/
lemma high_degree_mass [Nonempty V] (γ C : ℝ) (L : ℕ)
    (hγ : 1 < γ) (hC : 0 ≤ C)
    (he : (H.edgeFinset.card : ℝ) = C * (Fintype.card V : ℝ)^γ)
    (hepos : 0 < H.edgeFinset.card)
    (hL : 4*(2 : ℝ)^γ ≤ (L : ℝ)^(γ-1))
    (hdensity : ∀ u : Finset V,
      ((H.induce (↑u : Set V)).edgeFinset.card : ℝ) ≤ C * (u.card : ℝ)^γ) :
    2 * (∑ v ∈ univ.filter (fun v => 2*L*H.edgeFinset.card < Fintype.card V * H.degree v),
      (H.degree v : ℝ)) ≤ H.edgeFinset.card := by
  let s := univ.filter (fun v => 2*L*H.edgeFinset.card < Fintype.card V * H.degree v)
  change 2 * (∑ v ∈ s, (H.degree v : ℝ)) ≤ H.edgeFinset.card
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast (Fintype.card_pos (α := V))
  have hE : (0 : ℝ) < H.edgeFinset.card := by exact_mod_cast hepos
  have htotal : (∑ v ∈ s, (H.degree v : ℝ)) ≤ 2*H.edgeFinset.card := by
    calc
      _ ≤ ∑ v : V, (H.degree v : ℝ) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
      _ = _ := by exact_mod_cast H.sum_degrees_eq_twice_card_edges
  have hcard : (s.card : ℝ) * L ≤ Fintype.card V := by
    have hm : (s.card : ℝ) * (2*L*H.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * ∑ v ∈ s, (H.degree v : ℝ) := by
      rw [mul_sum]
      calc
        _ = ∑ _v ∈ s, (2*L*H.edgeFinset.card : ℝ) := by simp [mul_comm]
        _ ≤ _ := sum_le_sum (by
          intro v hv
          exact_mod_cast ((mem_filter.mp hv).2).le)
    have hh : ((s.card : ℝ)*L) * (2*H.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * (2*H.edgeFinset.card : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right hh (by positivity)
  by_cases hs : s.Nonempty
  · have hmass := small_set_degree_mass H γ C hγ.le hC hdensity s hs
    have hp : (4*(2 : ℝ)^γ) * (s.card : ℝ)^(γ-1) ≤ (Fintype.card V : ℝ)^(γ-1) := by
      calc
        _ ≤ (L : ℝ)^(γ-1) * (s.card : ℝ)^(γ-1) := by gcongr
        _ = ((s.card : ℝ)*L)^(γ-1) := by rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]; ring
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hcard (by linarith)
    calc
      2 * (∑ v ∈ s, (H.degree v : ℝ)) ≤
          2 * (2 * Fintype.card V * C * (2 : ℝ)^γ * (s.card : ℝ)^(γ-1)) := by gcongr
      _ = C * Fintype.card V * ((4*(2 : ℝ)^γ) * (s.card : ℝ)^(γ-1)) := by ring
      _ ≤ C * Fintype.card V * (Fintype.card V : ℝ)^(γ-1) := by gcongr
      _ = H.edgeFinset.card := by
        rw [he]
        have hpN : (Fintype.card V : ℝ)^γ = (Fintype.card V : ℝ) * (Fintype.card V : ℝ)^(γ-1) := by
          calc
            _ = (Fintype.card V : ℝ)^(1+(γ-1)) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hN,Real.rpow_one]
        rw [hpN]
        ring
  · simp [not_nonempty_iff_eq_empty.mp hs]
lemma delete_vertices_edge_bound (s : Finset V) :
    H.edgeFinset.card ≤ (H.induce (↑s : Set V)ᶜ).edgeFinset.card + ∑ v ∈ s, H.degree v := by
  let D := s.biUnion (fun v => H.incidenceFinset v)
  have hkeep : (H.edgeFinset ∩ sᶜ.sym2).card = (H.induce (↑s : Set V)ᶜ).edgeFinset.card := by
    have hh := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := H) (s := (↑s : Set V)ᶜ))
    simpa using hh.symm
  have hcover : H.edgeFinset ⊆ (H.edgeFinset ∩ sᶜ.sym2) ∪ D := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : H.Adj a b := by simpa using he
      by_cases ha : a ∈ s
      · apply mem_union_right
        apply mem_biUnion.mpr
        exact ⟨a,ha,by simp [H.mem_incidenceFinset,H.mk'_mem_incidenceSet_iff,hab]⟩
      by_cases hb : b ∈ s
      · apply mem_union_right
        apply mem_biUnion.mpr
        exact ⟨b,hb,by simp [H.mem_incidenceFinset,H.mk'_mem_incidenceSet_iff,hab]⟩
      apply mem_union_left
      exact mem_inter.mpr ⟨he,by simp [ha,hb]⟩
  calc
    H.edgeFinset.card ≤ ((H.edgeFinset ∩ sᶜ.sym2) ∪ D).card := card_le_card hcover
    _ ≤ (H.edgeFinset ∩ sᶜ.sym2).card + D.card := card_union_le _ _
    _ ≤ (H.induce (↑s : Set V)ᶜ).edgeFinset.card + ∑ v ∈ s, (H.incidenceFinset v).card := by
      rw [hkeep]
      exact Nat.add_le_add_left card_biUnion_le _
    _ = _ := by simp
end Sampling

lemma copy_degree_le {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) (v : V) : G.degree v ≤ H.degree (f v) := by
  rw [← G.card_neighborSet_eq_degree,← H.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_embedding (f.mapNeighborSet v)

universe u

/-- Peeling vertices of degree below `d` loses at most `d-1` edges per deleted
vertex. The remaining graph is allowed to be empty. -/
lemma minimum_degree_core {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) :
    ∃ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      ∃ f : Copy G H, (∀ v, d ≤ G.degree v) ∧
        H.edgeFinset.card + (d-1)*Fintype.card W ≤
          G.edgeFinset.card + (d-1)*Fintype.card V := by
  classical
  have aux : ∀ m : ℕ, ∀ (V : Type u) [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj],
      Fintype.card V = m →
      ∃ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
        ∃ f : Copy G H, (∀ v, d ≤ G.degree v) ∧
          H.edgeFinset.card + (d-1)*Fintype.card W ≤
            G.edgeFinset.card + (d-1)*Fintype.card V := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro V _ H _ hm
      by_cases hmin : ∀ v, d ≤ H.degree v
      · exact ⟨V,inferInstance,H,inferInstance,Copy.id H,hmin,le_rfl⟩
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      letI : Nonempty V := ⟨v⟩
      have hpos : 0 < m := by rw [← hm]; exact Fintype.card_pos
      have hc : Fintype.card ({v}ᶜ : Set V) = m-1 := by
        rw [Fintype.card_compl_set]
        simp [hm]
      obtain ⟨W,hW,G,hG,f,hmin,hcount⟩ := ih (m-1) (by omega) ({v}ᶜ : Set V) (H.induce {v}ᶜ) hc
      refine ⟨W,hW,G,hG,(Copy.induce H {v}ᶜ).comp f,hmin,?_⟩
      rw [H.card_edgeFinset_induce_compl_singleton,H.card_edgeFinset_deleteIncidenceSet,hc] at hcount
      rw [hm]
      have hdeg := H.degree_le_card_edgeFinset v
      have hdpred : H.degree v ≤ d-1 := by omega
      have heq : (d-1)*(m-1)+(d-1) = (d-1)*m := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
  exact aux (Fintype.card V) V H rfl

/-- A graph of maximum normalized induced density has an almost-regular subgraph
whose minimum degree is at least one quarter of the original edge/vertex ratio. -/
lemma almost_regular_of_density_max {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (γ C : ℝ) (L : ℕ) (hγ : 1 < γ) (hC : 0 ≤ C)
    (he : (H.edgeFinset.card : ℝ) = C * (Fintype.card V : ℝ)^γ)
    (hepos : 0 < H.edgeFinset.card)
    (hL : 4*(2 : ℝ)^γ ≤ (L : ℝ)^(γ-1))
    (hdensity : ∀ s : Finset V,
      ((H.induce (↑s : Set V)).edgeFinset.card : ℝ) ≤ C * (s.card : ℝ)^γ) :
    ∃ (W : Type u) (_ : Fintype W) (_ : Nonempty W)
      (G : SimpleGraph W) (_ : DecidableRel G.Adj), ∃ f : Copy G H, ∃ d : ℕ,
      0 < d ∧ (∀ v, d ≤ G.degree v) ∧ (∀ v, G.degree v ≤ 8*L*d) ∧
      H.edgeFinset.card ≤ 4*Fintype.card V*d := by
  classical
  let N := Fintype.card V
  let E := H.edgeFinset.card
  have hN : (0 : ℝ) < N := by exact_mod_cast (Fintype.card_pos (α := V))
  have hE : (0 : ℝ) < E := by exact_mod_cast hepos
  let s := univ.filter (fun v => 2*L*E < N*H.degree v)
  let J := H.induce (↑s : Set V)ᶜ
  have hmass : 2*(∑ v ∈ s, (H.degree v : ℝ)) ≤ E :=
    high_degree_mass H γ C L hγ hC he hepos hL hdensity
  have hdel : (E : ℝ) ≤ J.edgeFinset.card + ∑ v ∈ s, (H.degree v : ℝ) := by
    exact_mod_cast delete_vertices_edge_bound H s
  have hJ : (E : ℝ) ≤ 2*J.edgeFinset.card := by linarith
  let d := ⌈(E : ℝ)/(4*N)⌉₊
  have hx : (0 : ℝ) < (E : ℝ)/(4*N) := by positivity
  have hdlo : (E : ℝ)/(4*N) ≤ (d : ℝ) := Nat.le_ceil _
  have hdhi : (d : ℝ) < (E : ℝ)/(4*N)+1 := Nat.ceil_lt_add_one hx.le
  have hdpos : 0 < d := by
    have hdreal : (0 : ℝ) < d := hx.trans_le hdlo
    exact_mod_cast hdreal
  have hceil : E ≤ 4*N*d := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 4*N)).mp hdlo
    have hh' : (E : ℝ) ≤ (4*N)*d := by nlinarith
    exact_mod_cast hh'
  have hcost : (4 : ℝ)*N*(d-1 : ℕ) < E := by
    have hcast : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast]
    have hh : (d : ℝ)-1 < (E : ℝ)/(4*N) := by linarith
    have hh' := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4*N)).mp hh
    nlinarith
  obtain ⟨W,hW,G,hG,f,hmin,hcount⟩ := minimum_degree_core J d
  have hcardJ : Fintype.card ((↑s : Set V)ᶜ : Set V) ≤ N := by
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hcount' : J.edgeFinset.card ≤ G.edgeFinset.card + (d-1)*N := by
    have hh := Nat.mul_le_mul_left (d-1) hcardJ
    omega
  have hGpos : 0 < G.edgeFinset.card := by
    have hh : (J.edgeFinset.card : ℝ) ≤ G.edgeFinset.card + (d-1 : ℕ)*N := by exact_mod_cast hcount'
    have hGr : (0 : ℝ) < G.edgeFinset.card := by nlinarith
    exact_mod_cast hGr
  have hWpos : 0 < Fintype.card W := by
    have hh := G.card_edgeFinset_le_card_choose_two
    by_contra hn
    have hz : Fintype.card W = 0 := by omega
    simp only [hz,Nat.choose_zero_succ,Nat.le_zero] at hh
    omega
  letI : Nonempty W := Fintype.card_pos_iff.mp hWpos
  refine ⟨W,hW,inferInstance,G,hG,(Copy.induce H (↑s : Set V)ᶜ).comp f,d,hdpos,hmin,?_,hceil⟩
  intro v
  have hc₁ := copy_degree_le f v
  have hc₂ := copy_degree_le (Copy.induce H (↑s : Set V)ᶜ) (f v)
  have hv : (f v).val ∉ s := (f v).property
  have hhigh : N*H.degree (f v).val ≤ 2*L*E := by
    by_contra hh
    exact hv (mem_filter.mpr ⟨mem_univ _,Nat.lt_of_not_ge hh⟩)
  have hmul : N*H.degree (f v).val ≤ N*(8*L*d) := by
    calc
      _ ≤ 2*L*E := hhigh
      _ ≤ 2*L*(4*N*d) := Nat.mul_le_mul_left _ hceil
      _ = _ := by ring
  have hdH := Nat.le_of_mul_le_mul_left hmul (Fintype.card_pos (α := V))
  exact hc₁.trans (hc₂.trans hdH)

section MaximumDensity
variable {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Flatten two nested induced vertex sets. -/
def flattenIso (s : Finset V) (t : Finset s) :
    (H.induce (↑s : Set V)).induce (↑t : Set s) ≃g
      H.induce (↑(t.image Subtype.val) : Set V) where
  toFun v := ⟨v.val.val,mem_image.mpr ⟨v.val,v.property,rfl⟩⟩
  invFun v := ⟨⟨v.val,by
    obtain ⟨w,hw,he⟩ := mem_image.mp v.property
    rw [← he]
    exact w.property⟩,by
    obtain ⟨w,hw,he⟩ := mem_image.mp v.property
    have hh : (⟨v.val,by
      obtain ⟨z,hz,hze⟩ := mem_image.mp v.property
      rw [← hze]
      exact z.property⟩ : s) = w := Subtype.ext he.symm
    simpa only [Finset.mem_coe, hh] using hw⟩
  left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl
  map_rel_iff' := by intro v w; rfl

/-- A nonzero finite graph has an induced subgraph attaining maximum normalized
edge density, together with the corresponding bound on all its induced subgraphs. -/
lemma maximum_density [Nonempty V] (γ : ℝ) (hγ : 0 < γ)
    (hepos : 0 < H.edgeFinset.card) :
    ∃ s : Finset V, s.Nonempty ∧ 0 < (H.induce (↑s : Set V)).edgeFinset.card ∧
      ∃ C : ℝ, 0 < C ∧
        ((H.induce (↑s : Set V)).edgeFinset.card : ℝ) = C * (s.card : ℝ)^γ ∧
        (H.edgeFinset.card : ℝ) ≤ C * (Fintype.card V : ℝ)^γ ∧
        (∀ t : Finset s,
          (((H.induce (↑s : Set V)).induce (↑t : Set s)).edgeFinset.card : ℝ) ≤
            C * (t.card : ℝ)^γ) := by
  classical
  let density (s : Finset V) : ℝ := ((H.induce (↑s : Set V)).edgeFinset.card : ℝ) / (s.card : ℝ)^γ
  obtain ⟨s,hs,hmax⟩ := (univ : Finset (Finset V)).exists_max_image density (by simp)
  have huniv : (H.induce (↑(univ : Finset V) : Set V)).edgeFinset.card = H.edgeFinset.card := by
    let e : H.induce (↑(univ : Finset V) : Set V) ≃g H := {
      toFun := Subtype.val
      invFun := fun v => ⟨v,mem_univ v⟩
      left_inv := fun v => Subtype.ext rfl
      right_inv := fun v => rfl
      map_rel_iff' := by intro v w; rfl }
    exact e.card_edgeFinset_eq
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast (Fintype.card_pos (α := V))
  have hCpos : 0 < density s := by
    have hpos : 0 < density (univ : Finset V) := by
      dsimp [density]
      rw [huniv]
      exact div_pos (by exact_mod_cast hepos) (Real.rpow_pos_of_pos hN γ)
    exact hpos.trans_le (hmax univ (mem_univ _))
  have hsne : s.Nonempty := by
    by_contra hh
    have hz : s = ∅ := not_nonempty_iff_eq_empty.mp hh
    simp only [density,hz,card_empty,Nat.cast_zero,Real.zero_rpow (ne_of_gt hγ),div_zero] at hCpos
    exact (lt_irrefl 0) hCpos
  have hsp : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  have heq : ((H.induce (↑s : Set V)).edgeFinset.card : ℝ) = density s * (s.card : ℝ)^γ := by
    dsimp [density]
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hsp γ).ne']
  have hse : 0 < (H.induce (↑s : Set V)).edgeFinset.card := by
    have hh : (0 : ℝ) < (H.induce (↑s : Set V)).edgeFinset.card :=
      lt_of_lt_of_eq (mul_pos hCpos (Real.rpow_pos_of_pos hsp γ)) heq.symm
    exact_mod_cast hh
  have hall (t : Finset V) :
      ((H.induce (↑t : Set V)).edgeFinset.card : ℝ) ≤ density s * (t.card : ℝ)^γ := by
    by_cases ht : t.Nonempty
    · have htp : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
      exact (div_le_iff₀ (Real.rpow_pos_of_pos htp γ)).mp (hmax t (mem_univ _))
    · have ht0 : t = ∅ := not_nonempty_iff_eq_empty.mp ht
      subst t
      have he0 : (H.induce (↑(∅ : Finset V) : Set V)).edgeFinset.card = 0 := by
        have hh := (H.induce (↑(∅ : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
        simpa using hh
      simp only [he0,Nat.cast_zero,card_empty,Real.zero_rpow (ne_of_gt hγ),mul_zero,le_refl]
  refine ⟨s,hsne,hse,density s,hCpos,heq,?_,?_⟩
  · simpa only [huniv,card_univ] using hall univ
  · intro t
    rw [(flattenIso H s t).card_edgeFinset_eq]
    have hh := hall (t.image Subtype.val)
    rwa [card_image_of_injective _ Subtype.val_injective] at hh
end MaximumDensity

/-- Transfer a degree bound for almost-regular copies to an edge bound for the
original graph, without a logarithmic loss. -/
lemma edge_bound_of_almost_regular {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (γ A : ℝ) (L : ℕ)
    (hγ : 1 < γ) (hA : 0 ≤ A) (hL : 4*(2 : ℝ)^γ ≤ (L : ℝ)^(γ-1))
    (hbound : ∀ (W : Type u) [Fintype W] [Nonempty W]
      (G : SimpleGraph W) [DecidableRel G.Adj], Copy G H → ∀ d : ℕ,
      0 < d → (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ 8*L*d) →
      (d : ℝ) ≤ A * (Fintype.card W : ℝ)^(γ-1)) :
    (H.edgeFinset.card : ℝ) ≤ 4*A * (Fintype.card V : ℝ)^γ := by
  classical
  by_cases he0 : H.edgeFinset.card = 0
  · rw [he0,Nat.cast_zero]
    positivity
  have hepos : 0 < H.edgeFinset.card := Nat.pos_of_ne_zero he0
  obtain ⟨s,hs,hse,C,hC,heq,hH,hmax⟩ := maximum_density H γ (by linarith) hepos
  let J := H.induce (↑s : Set V)
  obtain ⟨v,hv⟩ := hs
  letI : Nonempty s := ⟨⟨v,hv⟩⟩
  have heJ : (J.edgeFinset.card : ℝ) = C * (Fintype.card s : ℝ)^γ := by simpa using heq
  obtain ⟨W,hW,hWne,G,hG,f,d,hdpos,hdmin,hdmax,hed⟩ :=
    almost_regular_of_density_max J γ C L hγ hC.le heJ hse hL hmax
  have hd := hbound W G ((Copy.induce H (↑s : Set V)).comp f) d hdpos hdmin hdmax
  have hcard : Fintype.card W ≤ s.card := by
    simpa using Fintype.card_le_of_embedding f.toEmbedding
  have hd' : (d : ℝ) ≤ A * (s.card : ℝ)^(γ-1) := by
    apply hd.trans
    apply mul_le_mul_of_nonneg_left _ hA
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcard) (by linarith)
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr ⟨v,hv⟩
  have hmul : C * (s.card : ℝ)^γ ≤ (4*A) * (s.card : ℝ)^γ := by
    calc
      _ = (J.edgeFinset.card : ℝ) := heq.symm
      _ ≤ 4*(s.card : ℝ)*d := by
        have hsc : Fintype.card (↑s : Set V) = s.card := Fintype.card_coe s
        rw [hsc] at hed
        exact_mod_cast hed
      _ ≤ 4*(s.card : ℝ)*(A*(s.card : ℝ)^(γ-1)) := by gcongr
      _ = _ := by
        have hp : (s.card : ℝ)^γ = (s.card : ℝ) * (s.card : ℝ)^(γ-1) := by
          calc
            _ = (s.card : ℝ)^(1+(γ-1)) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hspos,Real.rpow_one]
        rw [hp]
        ring
  have hCbound : C ≤ 4*A := le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hspos γ)
  exact hH.trans (mul_le_mul_of_nonneg_right hCbound (Real.rpow_nonneg (Nat.cast_nonneg _) _))

lemma exists_regularization_constant (γ : ℝ) (hγ : 1 < γ) :
    ∃ L : ℕ, 4*(2 : ℝ)^γ ≤ (L : ℝ)^(γ-1) := by
  have hβ : 0 < γ-1 := by linarith
  obtain ⟨L,hL⟩ := exists_nat_gt ((4*(2 : ℝ)^γ)^((γ-1)⁻¹))
  refine ⟨L,?_⟩
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hL.le hβ.le
  rw [← Real.rpow_mul (by positivity),inv_mul_cancel₀ hβ.ne',Real.rpow_one] at hh
  exact hh

end Regularization

end -- Regularization

section -- MaxCut

/- A bipartite subgraph retaining at least half the edges. -/
open Finset SimpleGraph
namespace MaxCut
set_option maxHeartbeats 1000000

section Bits
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma half_colorings (x y : V) (hxy : x ≠ y) :
    2 * (univ.filter (fun c : V → Bool => c x ≠ c y)).card = Fintype.card (V → Bool) := by
  let flip (c : V → Bool) := Function.update c x (!(c x))
  have hinv : Function.Involutive flip := by
    intro c
    funext v
    by_cases hv : v = x
    · subst v
      simp [flip]
    · simp [flip,Function.update_apply,hv]
  have hflip (c : V → Bool) : flip c x ≠ flip c y ↔ c x = c y := by
    simp only [flip,Function.update_self,Function.update_of_ne hxy.symm]
    cases c x <;> cases c y <;> decide
  have heq : (univ.filter (fun c : V → Bool => c x ≠ c y)).card =
      (univ.filter (fun c : V → Bool => ¬c x ≠ c y)).card := by
    apply card_bij (fun c _ => flip c)
    · intro c hc
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      intro hh
      exact (mem_filter.mp hc).2 ((hflip c).mp hh)
    · intro c hc d hd he
      exact hinv.injective he
    · intro c hc
      refine ⟨flip c,mem_filter.mpr ⟨mem_univ _,?_⟩,hinv c⟩
      exact (hflip c).mpr (not_not.mp (mem_filter.mp hc).2)
  have hh := card_filter_add_card_filter_not (s := (univ : Finset (V → Bool)))
    (fun c => c x ≠ c y)
  rw [← heq,card_univ] at hh
  omega
end Bits

section Graph
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

def cut (c : V → Bool) : SimpleGraph V where
  Adj x y := H.Adj x y ∧ c x ≠ c y
  symm := by constructor; intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by constructor; intro x h; exact h.2 rfl

instance (c : V → Bool) : DecidableRel (cut H c).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma cut_le (c : V → Bool) : cut H c ≤ H := fun _ _ h => h.1

lemma cut_bipartite (c : V → Bool) : (cut H c).IsBipartite := by
  let col : (cut H c).Coloring Bool := Coloring.mk c (fun h => h.2)
  simpa using col.colorable

lemma sum_cut_edges : (∑ c : V → Bool, 2*(cut H c).edgeFinset.card) =
    Fintype.card (V → Bool) * H.edgeFinset.card := by
  have hs : (∑ c : V → Bool, 2*(cut H c).edgeFinset.card) =
      ∑ p : V × V, if H.Adj p.1 p.2 then
        (univ.filter (fun c : V → Bool => c p.1 ≠ c p.2)).card else 0 := by
    calc
      _ = ∑ c : V → Bool, ∑ p : V × V,
          if H.Adj p.1 p.2 ∧ c p.1 ≠ c p.2 then 1 else 0 := by
        apply sum_congr rfl
        intro c hc
        rw [SimpleGraph.two_mul_card_edgeFinset,card_filter]
        rfl
      _ = ∑ p : V × V, ∑ c : V → Bool,
          if H.Adj p.1 p.2 ∧ c p.1 ≠ c p.2 then 1 else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro p hp
        by_cases ha : H.Adj p.1 p.2 <;> simp [ha,card_filter]
  have hh : 2*(∑ c : V → Bool, 2*(cut H c).edgeFinset.card) =
      Fintype.card (V → Bool) * (2*H.edgeFinset.card) := by
    rw [hs,mul_sum]
    calc
      _ = ∑ p : V × V, if H.Adj p.1 p.2 then Fintype.card (V → Bool) else 0 := by
        apply sum_congr rfl
        intro p hp
        split_ifs with ha
        · exact half_colorings p.1 p.2 ha.ne
        · simp
      _ = Fintype.card (V → Bool) * (2*H.edgeFinset.card) := by
        rw [SimpleGraph.two_mul_card_edgeFinset,card_filter,mul_sum]
        apply sum_congr rfl
        intro p hp
        split_ifs <;> simp
  nlinarith only [hh]

lemma exists_bipartite_subgraph :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G ≤ H ∧ G.IsBipartite ∧ H.edgeFinset.card ≤ 2*G.edgeFinset.card := by
  have hs : (∑ _c : V → Bool, H.edgeFinset.card) ≤ ∑ c : V → Bool, 2*(cut H c).edgeFinset.card := by
    rw [sum_cut_edges]
    simp
  obtain ⟨c,hc,he⟩ := exists_le_of_sum_le (by simp : (univ : Finset (V → Bool)).Nonempty) hs
  exact ⟨cut H c,inferInstance,cut_le H c,cut_bipartite H c,he⟩
end Graph

end MaxCut

end -- MaxCut

section -- SuspensionBounds

/- The connected bipartite suspension and its edge links. -/
open Finset SimpleGraph
namespace SuspensionBounds
set_option maxHeartbeats 1000000

section Coloring
variable {V : Type*} {G : SimpleGraph V}

lemma walk_color_eq (c d : G.Coloring (Fin 2)) {x y : V}
    (p : G.Walk x y) (h : c x = d x) : c y = d y := by
  induction p with
  | nil => exact h
  | @cons x y z hxy p ih =>
    apply ih
    have hc := c.valid hxy
    have hd := d.valid hxy
    omega

lemma coloring_perm (hG : G.Connected) (c d : G.Coloring (Fin 2)) :
    ∃ e : Fin 2 ≃ Fin 2, ∀ v, e (c v) = d v := by
  classical
  let v := Classical.choice hG.nonempty
  let e : Fin 2 ≃ Fin 2 := Equiv.swap (c v) (d v)
  let c' : G.Coloring (Fin 2) := Coloring.mk (fun w => e (c w))
    (by intro x y hxy he; exact c.valid hxy (e.injective he))
  refine ⟨e,?_⟩
  intro w
  obtain ⟨p⟩ := hG v w
  exact walk_color_eq c' d p (by
    change e (c v) = d v
    exact Equiv.swap_apply_left _ _)
end Coloring

/-- Add one new vertex of each color, join them, and join each new vertex to all
old vertices of the opposite color. -/
def suspend {V : Type*} {F : SimpleGraph V} (c : F.Coloring (Fin 2)) :
    SimpleGraph (Fin 2 ⊕ V) where
  Adj u v := match u,v with
    | Sum.inl i, Sum.inl j => i ≠ j
    | Sum.inl i, Sum.inr v => i ≠ c v
    | Sum.inr u, Sum.inl j => c u ≠ j
    | Sum.inr u, Sum.inr v => F.Adj u v
  symm := by
    constructor
    intro u v h
    cases u <;> cases v
    · exact h.symm
    · exact h.symm
    · exact h.symm
    · exact h.symm
  loopless := by constructor; intro u h; cases u; exact h rfl; exact h.ne rfl


/-- Extend a copy using two new distinct vertices with the necessary adjacencies. -/
def extend {V W : Type*} {F : SimpleGraph V} {H : SimpleGraph W}
    (c : F.Coloring (Fin 2)) (f : Copy F H) (x : Fin 2 ↪ W)
    (havoid : ∀ i v, x i ≠ f v)
    (hxx : H.Adj (x 0) (x 1))
    (hx : ∀ i v, i ≠ c v → H.Adj (x i) (f v)) : Copy (suspend c) H where
  toHom := {
    toFun := Sum.elim x f
    map_rel' := by
      intro u v h
      cases u with
      | inl i =>
        cases v with
        | inl j =>
          fin_cases i <;> fin_cases j
          · exact False.elim (h rfl)
          · exact hxx
          · exact hxx.symm
          · exact False.elim (h rfl)
        | inr v => exact hx i v h
      | inr u =>
        cases v with
        | inl j => exact (hx j u h.symm).symm
        | inr v => exact f.toHom.map_rel' h }
  injective' := by
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (x.injective h)
      | inr v => exact False.elim (havoid i v h)
    | inr u =>
      cases v with
      | inl j => exact False.elim (havoid j u h.symm)
      | inr v => exact congrArg Sum.inr (f.injective h)

/-- A relation regarded as a bipartite graph on a disjoint sum. -/
def biGraph {A B : Type*} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj u v := match u,v with
    | Sum.inl a, Sum.inr b => R a b
    | Sum.inr b, Sum.inl a => R a b
    | _,_ => False
  symm := by constructor; intro u v h; cases u <;> cases v <;> exact h
  loopless := by constructor; intro u h; cases u <;> exact h

instance {A B : Type*} (R : A → B → Prop) [∀ a b, Decidable (R a b)] :
    DecidableRel (biGraph R).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [biGraph] <;> infer_instance

def biColor {A B : Type*} (R : A → B → Prop) : (biGraph R).Coloring (Fin 2) :=
  Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) (by
    intro u v h
    cases u <;> cases v <;> simp_all [biGraph])

lemma biGraph_edge_card {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (R : A → B → Prop) [∀ a b, Decidable (R a b)] :
    (biGraph R).edgeFinset.card = (univ.filter (fun p : A × B => R p.1 p.2)).card := by
  let f : A × B → Sym2 (A ⊕ B) := fun p => s(Sum.inl p.1,Sum.inr p.2)
  have hf : Function.Injective f := by
    intro p q hpq
    simpa [f,Sym2.eq_iff,Prod.ext_iff] using hpq
  have he : (biGraph R).edgeFinset = (univ.filter (fun p : A × B => R p.1 p.2)).image f := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      cases u <;> cases v <;> simp [f,biGraph,Sym2.eq_iff]
  rw [he,card_image_of_injective _ hf]

section Link
variable {V : Type*} (H : SimpleGraph V) (x y : V)

abbrev Left := {a : V // H.Adj y a ∧ a ≠ x}
abbrev Right := {b : V // H.Adj x b ∧ b ≠ y}

def link : SimpleGraph (Left H x y ⊕ Right H x y) :=
  biGraph (fun a b => H.Adj a.val b.val)

instance [DecidableRel H.Adj] : DecidableRel (link H x y).Adj := inferInstanceAs (DecidableRel (biGraph _).Adj)

lemma no_triangle (hbip : H.IsBipartite) (hxy : H.Adj x y) (z : V)
    (hxz : H.Adj x z) (hyz : H.Adj y z) : False := by
  obtain ⟨c⟩ := hbip
  have h₁ := c.valid hxy
  have h₂ := c.valid hxz
  have h₃ := c.valid hyz
  omega

def linkCopy (hbip : H.IsBipartite) (hxy : H.Adj x y) : Copy (link H x y) H where
  toHom := {
    toFun := Sum.elim Subtype.val Subtype.val
    map_rel' := by
      intro u v h
      cases u <;> cases v
      · exact False.elim h
      · exact h
      · change H.Adj _ _ at h
        exact h.symm
      · exact False.elim h }
  injective' := by
    intro u v he
    cases u with
    | inl a =>
      cases v with
      | inl b => exact congrArg Sum.inl (Subtype.ext he)
      | inr b =>
        have ha := a.property.1
        have hb := b.property.1
        change a.val = b.val at he
        rw [← he] at hb
        exact False.elim (no_triangle H x y hbip hxy a.val hb ha)
    | inr a =>
      cases v with
      | inl b =>
        have ha := a.property.1
        have hb := b.property.1
        change a.val = b.val at he
        rw [← he] at hb
        exact False.elim (no_triangle H x y hbip hxy a.val ha hb)
      | inr b => exact congrArg Sum.inr (Subtype.ext he)

lemma linkCopy_ne (hbip : H.IsBipartite) (hxy : H.Adj x y)
    (v : Left H x y ⊕ Right H x y) :
    linkCopy H x y hbip hxy v ≠ x ∧ linkCopy H x y hbip hxy v ≠ y := by
  cases v with
  | inl a => exact ⟨a.property.2,a.property.1.ne.symm⟩
  | inr b => exact ⟨b.property.1.ne.symm,b.property.2⟩

lemma link_vertex_count [Fintype V] [DecidableEq V] [DecidableRel H.Adj] :
    Fintype.card (Left H x y ⊕ Right H x y) ≤ H.degree x + H.degree y := by
  have hL : Fintype.card (Left H x y) ≤ H.degree y := by
    rw [← H.card_neighborSet_eq_degree]
    exact Fintype.card_le_of_injective (fun a : Left H x y => (⟨a.val,a.property.1⟩ : H.neighborSet y))
      (by intro a b h; exact Subtype.ext (congrArg (fun z : H.neighborSet y => z.val) h))
  have hR : Fintype.card (Right H x y) ≤ H.degree x := by
    rw [← H.card_neighborSet_eq_degree]
    exact Fintype.card_le_of_injective (fun b : Right H x y => (⟨b.val,b.property.1⟩ : H.neighborSet x))
      (by intro a b h; exact Subtype.ext (congrArg (fun z : H.neighborSet x => z.val) h))
  rw [Fintype.card_sum]
  omega
/-- A connected forbidden graph in an edge link extends to its suspension. -/
lemma suspend_contained_of_link {W : Type*} {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2))
    (hbip : H.IsBipartite) (hxy : H.Adj x y) (f : Copy F (link H x y)) :
    suspend c ⊑ H := by
  classical
  let d : F.Coloring (Fin 2) := Coloring.mk
    (fun w => biColor (fun a : Left H x y => fun b : Right H x y => H.Adj a.val b.val) (f w))
    (by intro u v huv; exact (biColor _).valid (f.toHom.map_rel' huv))
  obtain ⟨e,he⟩ := coloring_perm hF c d
  let X : Fin 2 ↪ V := {
    toFun := fun i => if i = 0 then x else y
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [hxy.ne,hxy.ne.symm] }
  let g : Copy F H := (linkCopy H x y hbip hxy).comp f
  have hXadj (i j : Fin 2) (hij : i ≠ j) : H.Adj (X i) (X j) := by
    fin_cases i <;> fin_cases j <;> simp_all [X,hxy,hxy.symm]
  refine ⟨extend c g (e.toEmbedding.trans X) ?_ ?_ ?_⟩
  · intro i w
    have hw := linkCopy_ne H x y hbip hxy (f w)
    change (if e i = 0 then x else y) ≠ linkCopy H x y hbip hxy (f w)
    split_ifs
    · exact hw.1.symm
    · exact hw.2.symm
  · exact hXadj (e 0) (e 1) (fun hh => (by decide : (0 : Fin 2) ≠ 1) (e.injective hh))
  · intro i w hi
    have hne : e i ≠ d w := by
      rw [← he w]
      exact fun hh => hi (e.injective hh)
    change e i ≠ Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) (f w) at hne
    change H.Adj (if e i = 0 then x else y) (linkCopy H x y hbip hxy (f w))
    cases hfw : f w with
    | inl a =>
      have h0 : e i ≠ 0 := by simpa only [hfw,Sum.elim_inl] using hne
      rw [if_neg h0]
      exact a.property.1
    | inr b =>
      have h1 : e i ≠ 1 := by simpa only [hfw,Sum.elim_inr] using hne
      have h0 : e i = 0 := by omega
      rw [if_pos h0]
      exact b.property.1

lemma link_free {W : Type*} {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2))
    (hbip : H.IsBipartite) (hxy : H.Adj x y) (hfree : (suspend c).Free H) :
    F.Free (link H x y) := by
  rintro ⟨f⟩
  exact hfree (suspend_contained_of_link H x y hF c hbip hxy f)
lemma link_edge_card [Fintype V] [DecidableEq V] [DecidableRel H.Adj] :
    (link H x y).edgeFinset.card = (EdgeLinks.properThree H x y).card := by
  change (biGraph (fun a : Left H x y => fun b : Right H x y => H.Adj a.val b.val)).edgeFinset.card = _
  rw [biGraph_edge_card]
  apply card_bij (fun p _ => (p.2.val,p.1.val))
  · intro p hp
    have hrel := (mem_filter.mp hp).2
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,p.2.property.1,?_,p.1.property.1.symm⟩,
      p.2.property.2,p.1.property.2⟩
    exact hrel.symm
  · intro p hp q hq he
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.snd he)
    · exact Subtype.ext (congrArg Prod.fst he)
  · intro p hp
    have hpath := (mem_filter.mp (mem_filter.mp hp).1).2
    have hne := (mem_filter.mp hp).2
    refine ⟨(⟨p.2,hpath.2.2.symm,hne.2⟩,⟨p.1,hpath.1,hne.1⟩),?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,hpath.2.1.symm⟩
end Link


lemma suspension_real_degree_bound {V W : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2))
    (hbip : H.IsBipartite) (hfree : (suspend c).Free H)
    (δ Δ : ℕ) (hδ : ∀ v, δ ≤ H.degree v) (hΔ : ∀ v, H.degree v ≤ Δ)
    (α C : ℝ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hbound : ∀ m : ℕ, (extremalNumber m F : ℝ) ≤ C * (m : ℝ)^α) :
    (δ : ℝ)^4 ≤ (Fintype.card V : ℝ) * Δ * (C * (2*Δ : ℝ)^α + 2*Δ) := by
  apply EdgeLinks.real_degree_bound H δ Δ (C * (2*Δ : ℝ)^α) (by positivity) hδ hΔ
  intro x y hxy
  have hfree' := link_free H x y hF c hbip hxy hfree
  have hc : Fintype.card (Left H x y ⊕ Right H x y) ≤ 2*Δ := by
    have hh := link_vertex_count H x y
    have hx := hΔ x
    have hy := hΔ y
    omega
  rw [← link_edge_card H x y]
  calc
    ((link H x y).edgeFinset.card : ℝ) ≤
      extremalNumber (Fintype.card (Left H x y ⊕ Right H x y)) F := by
        exact_mod_cast card_edgeFinset_le_extremalNumber hfree'
    _ ≤ C * (Fintype.card (Left H x y ⊕ Right H x y) : ℝ)^α := hbound _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hα
      exact_mod_cast hc

/-- The expected transformed degree exponent holds for almost-regular bipartite
hosts avoiding the suspension. No lower bound for that suspension is asserted. -/
lemma suspension_almost_regular_bound {V W : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2))
    (hbip : H.IsBipartite) (hfree : (suspend c).Free H)
    (δ K : ℕ) (hδpos : 0 < δ)
    (hδ : ∀ v, δ ≤ H.degree v) (hΔ : ∀ v, H.degree v ≤ K*δ)
    (α C : ℝ) (hα : 1 ≤ α) (hC : 0 ≤ C)
    (hbound : ∀ m : ℕ, (extremalNumber m F : ℝ) ≤ C * (m : ℝ)^α) :
    (δ : ℝ)^(3-α) ≤
      (Fintype.card V : ℝ) * K * (C * (2*K : ℝ)^α + 2*K) := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast hδpos
  have hd1 : (1 : ℝ) ≤ δ := by exact_mod_cast hδpos
  have hp : (δ : ℝ) ≤ (δ : ℝ)^α := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 hα
  have hh := suspension_real_degree_bound H hF c hbip hfree δ (K*δ) hδ hΔ α C
    (by linarith) hC hbound
  push_cast at hh
  have hmul : (δ : ℝ)^(3-α) * (δ : ℝ)^(α+1) ≤
      ((Fintype.card V : ℝ) * K * (C * (2*K : ℝ)^α + 2*K)) * (δ : ℝ)^(α+1) := by
    calc
      _ = (δ : ℝ)^4 := by
        rw [← Real.rpow_add hd,show 3-α+(α+1) = (4 : ℝ) by ring]
        norm_num
      _ ≤ (Fintype.card V : ℝ) * (K*δ) * (C * (2*(K*δ) : ℝ)^α + 2*(K*δ)) := hh
      _ = (Fintype.card V : ℝ) * K * δ * (C * (2*K : ℝ)^α * (δ : ℝ)^α + 2*K*δ) := by
        rw [show (2*(K*δ) : ℝ) = (2*K)*δ by ring,Real.mul_rpow (by positivity) hd.le]
        ring
      _ ≤ (Fintype.card V : ℝ) * K * δ *
          (C * (2*K : ℝ)^α * (δ : ℝ)^α + 2*K*(δ : ℝ)^α) := by gcongr
      _ = _ := by
        rw [Real.rpow_add hd,Real.rpow_one]
        ring
  exact le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hd (α+1))

universe u v

/-- The connected bipartite suspension transforms an upper exponent `α` into
`1 + 1/(3-α)` on arbitrary bipartite hosts; regularization incurs only a constant. -/
lemma suspension_bipartite_upper {W : Type v} {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2))
    (α C : ℝ) (hα : 1 ≤ α) (hα₂ : α < 2) (hC : 0 ≤ C)
    (hbound : ∀ m : ℕ, (extremalNumber m F : ℝ) ≤ C * (m : ℝ)^α) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (V : Type u) [Fintype V] [Nonempty V] [DecidableEq V]
      (H : SimpleGraph V) [DecidableRel H.Adj], H.IsBipartite → (suspend c).Free H →
        (H.edgeFinset.card : ℝ) ≤ D * (Fintype.card V : ℝ)^(1+1/(3-α)) := by
  classical
  let γ : ℝ := 1+1/(3-α)
  have hβ : 0 < 3-α := by linarith
  have hγ : 1 < γ := by
    dsimp [γ]
    have hp : (0 : ℝ) < 1/(3-α) := one_div_pos.mpr hβ
    linarith
  obtain ⟨L,hL⟩ := Regularization.exists_regularization_constant γ hγ
  let K : ℕ := 8*L
  let B : ℝ := K * (C * (2*K : ℝ)^α + 2*K)
  let A : ℝ := B^((3-α)⁻¹)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := Real.rpow_nonneg hB _
  refine ⟨4*A,by positivity,?_⟩
  intro V _ _ _ H _ hbip hfree
  apply Regularization.edge_bound_of_almost_regular H γ A L hγ hA hL
  intro U _ _ G _ f d hdpos hdmin hdmax
  have hGbip : G.IsBipartite := SimpleGraph.Colorable.of_hom f.toHom hbip
  have hGfree : (suspend c).Free G := by
    intro hh
    exact hfree (hh.trans ⟨f⟩)
  have hh := suspension_almost_regular_bound G hF c hGbip hGfree d K hdpos hdmin hdmax
    α C hα hC hbound
  have hh' : (d : ℝ)^(3-α) ≤ B * Fintype.card U := by
    calc
      _ ≤ (Fintype.card U : ℝ) * K * (C * (2*K : ℝ)^α + 2*K) := hh
      _ = _ := by dsimp [B]; ring
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg d) _) hh' (inv_nonneg.mpr hβ.le)
  rw [← Real.rpow_mul (Nat.cast_nonneg d),mul_inv_cancel₀ hβ.ne',Real.rpow_one,
    Real.mul_rpow hB (Nat.cast_nonneg _)] at hr
  simpa [A,γ,one_div] using hr

/-- A genuine single-graph upper-bound transformation. This proves only an upper
bound; a matching lower bound for the suspension requires a separate argument. -/
lemma suspension_upper {W : Type v} {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2))
    (α C : ℝ) (hα : 1 ≤ α) (hα₂ : α < 2) (hC : 0 ≤ C)
    (hbound : ∀ m : ℕ, (extremalNumber m F : ℝ) ≤ C * (m : ℝ)^α) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ,
      (extremalNumber m (suspend c) : ℝ) ≤ D * (m : ℝ)^(1+1/(3-α)) := by
  classical
  obtain ⟨D,hD,hbip⟩ := suspension_bipartite_upper.{0,v} hF c α C hα hα₂ hC hbound
  refine ⟨2*D,by positivity,?_⟩
  intro m
  by_cases hm : m = 0
  · subst m
    have hz : extremalNumber 0 (suspend c) = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← Fintype.card_fin 0,extremalNumber_le_iff]
      intro H _ hH
      simpa using H.card_edgeFinset_le_card_choose_two
    rw [hz,Nat.cast_zero]
    positivity
  · letI : Nonempty (Fin m) := ⟨⟨0,Nat.pos_of_ne_zero hm⟩⟩
    rw [← Fintype.card_fin m]
    apply (extremalNumber_le_iff_of_nonneg (suspend c) (by positivity :
      (0 : ℝ) ≤ (2*D) * (Fintype.card (Fin m) : ℝ)^(1+1/(3-α)))).mpr
    intro H _ hH
    obtain ⟨G,hG,hGH,hGbip,hcount⟩ := MaxCut.exists_bipartite_subgraph H
    have hGfree : (suspend c).Free G := by
      intro hh
      exact hH (hh.trans ⟨Copy.ofLE G H hGH⟩)
    have hg := hbip (Fin m) G hGbip hGfree
    have hc : (H.edgeFinset.card : ℝ) ≤ 2*G.edgeFinset.card := by exact_mod_cast hcount
    nlinarith

lemma extremal_le_sq {W : Type*} (F : SimpleGraph W) (n : ℕ) :
    extremalNumber n F ≤ n^2 := by
  rw [← Fintype.card_fin n,extremalNumber_le_iff]
  intro H _ hH
  exact H.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ 2)

/-- For an extremal-number function, an asymptotic power upper bound can be made
uniform, including the finitely many small inputs. -/
lemma uniform_bound_of_isBigO {W : Type*} (F : SimpleGraph W) (α : ℝ) (hα : 0 ≤ α)
    (h : Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (extremalNumber n F : ℝ)) (fun n : ℕ => (n : ℝ)^α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (extremalNumber n F : ℝ) ≤ C * (n : ℝ)^α := by
  obtain ⟨c,hc⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hc
  let C : ℝ := |c| + (N : ℝ)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hz : extremalNumber 0 F = 0 := by simpa using extremal_le_sq F 0
    rw [hz,Nat.cast_zero]
    positivity
  by_cases hn : N ≤ n
  · have hh : (extremalNumber n F : ℝ) ≤ c*(n : ℝ)^α := by
      simpa only [Real.norm_natCast,Real.norm_eq_abs,Nat.abs_cast,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hN n hn
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hc' := le_abs_self c
    dsimp [C]
    nlinarith [sq_nonneg (N : ℝ)]
  · have hp : (1 : ℝ) ≤ (n : ℝ)^α :=
      Real.one_le_rpow (by exact_mod_cast (Nat.pos_of_ne_zero hn0)) hα
    have hsmall : (extremalNumber n F : ℝ) ≤ (N : ℝ)^2 := by
      have hh := (extremal_le_sq F n).trans (Nat.pow_le_pow_left (by omega : n ≤ N) 2)
      exact_mod_cast hh
    have hCN : (N : ℝ)^2 ≤ C := by dsimp [C]; linarith [abs_nonneg c]
    calc
      _ ≤ (N : ℝ)^2 := hsmall
      _ ≤ C := hCN
      _ ≤ C * (n : ℝ)^α := by simpa using mul_le_mul_of_nonneg_left hp hC

/-- The asymptotic upper-exponent transformation for connected bipartite suspension. -/
lemma suspension_isBigO {W : Type v} {F : SimpleGraph W}
    (hF : F.Connected) (c : F.Coloring (Fin 2)) (α : ℝ) (hα : 1 ≤ α) (hα₂ : α < 2)
    (h : Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (extremalNumber n F : ℝ)) (fun n : ℕ => (n : ℝ)^α)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (extremalNumber n (suspend c) : ℝ))
      (fun n : ℕ => (n : ℝ)^(1+1/(3-α))) := by
  obtain ⟨C,hC,hbound⟩ := uniform_bound_of_isBigO F α (by linarith) h
  obtain ⟨D,hD,hd⟩ := suspension_upper hF c α C hα hα₂ hC hbound
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨D,Filter.Eventually.of_forall ?_⟩
  intro n
  simpa only [Real.norm_natCast,Real.norm_eq_abs,Nat.abs_cast,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hd n

end SuspensionBounds

end -- SuspensionBounds

section -- UltrafilterField

/- Field extensions obtained from ultrafilter germs. -/
open Filter
namespace UltrafilterField
variable {I K : Type*} [Field K] (u : Ultrafilter I)

noncomputable instance field : Field (Germ (u : Filter I) K) where
  __ := (inferInstance : CommRing (Germ (u : Filter I) K))
  __ := (inferInstance : DivInvMonoid (Germ (u : Filter I) K))
  nnqsmul q a := (q.num : Germ (u : Filter I) K) / q.den * a
  qsmul q a := (q.num : Germ (u : Filter I) K) / q.den * a
  exists_pair_ne := ⟨0,1,zero_ne_one⟩
  mul_inv_cancel := by
    intro x hx
    induction x using Germ.inductionOn with
    | h f =>
      have hne : ∀ᶠ i in (u : Filter I), f i ≠ 0 := by
        apply Ultrafilter.eventually_not.mpr
        intro he
        exact hx (Germ.coe_eq.mpr he)
      apply Germ.coe_eq.mpr
      filter_upwards [hne] with i hi
      exact mul_inv_cancel₀ hi
  inv_zero := by
    change ((fun _ : I => (0 : K)⁻¹) : Germ (u : Filter I) K) =
      ((fun _ : I => (0 : K)) : Germ (u : Filter I) K)
    exact Germ.coe_eq.mpr (Eventually.of_forall (fun _ => inv_zero))

/-- The embedding of the original field as constant germs. -/
def constHom : K →+* Germ (u : Filter I) K where
  toFun := Germ.const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable instance algebra : Algebra K (Germ (u : Filter I) K) := (constHom u).toAlgebra

lemma algebraMap_eq (c : K) : algebraMap K (Germ (u : Filter I) K) c = Germ.const c := rfl

lemma aeval_eq {σ : Type*} (x : I → σ → K) (p : MvPolynomial σ K) :
    MvPolynomial.aeval (fun j => ((fun i => x i j) : Germ (u : Filter I) K)) p =
      ((fun i => MvPolynomial.eval (x i) p) : Germ (u : Filter I) K) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, MvPolynomial.eval_C, algebraMap_eq]; rfl
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    rfl
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]
    rfl

lemma aeval_zero_of_forall {σ : Type*} (x : I → σ → K) (p : MvPolynomial σ K)
    (h : ∀ i, MvPolynomial.eval (x i) p = 0) :
    MvPolynomial.aeval (fun j => ((fun i => x i j) : Germ (u : Filter I) K)) p = 0 := by
  rw [aeval_eq]
  exact Germ.coe_eq.mpr (Eventually.of_forall h)


lemma polynomial_aeval_eq (f : I → K) (p : Polynomial K) :
    Polynomial.aeval (f : Germ (u : Filter I) K) p =
      ((fun i => p.eval (f i)) : Germ (u : Filter I) K) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.eval_add, hp, hq]
    rfl
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial, algebraMap_eq]
    rfl

/-- An injective coordinate yields a transcendental element at any cofinite ultrafilter. -/
lemma transcendental_of_injective (hu : (u : Filter I) ≤ cofinite)
    (f : I → K) (hf : Function.Injective f) : Transcendental K (f : Germ (u : Filter I) K) := by
  apply transcendental_iff.mpr
  intro p hp
  by_contra hp0
  have hfinite : {i : I | p.eval (f i) = 0}.Finite := by
    exact (Polynomial.finite_setOf_isRoot hp0).preimage hf.injOn
  have hne : ∀ᶠ i in (u : Filter I), p.eval (f i) ≠ 0 := by
    apply Filter.Eventually.filter_mono hu
    simpa only [eventually_cofinite, not_not] using hfinite
  rw [polynomial_aeval_eq] at hp
  obtain ⟨i,hi,hzi⟩ := (hne.and (Germ.coe_eq.mp hp)).exists
  exact hi hzi

/-- Finite sets of polynomial equalities true at a germ point are simultaneously
true at one of its representatives. -/
lemma finite_equalities {σ : Type*} (x : I → σ → K)
    (P : Finset (MvPolynomial σ K))
    (h : ∀ p ∈ P, MvPolynomial.aeval (fun j => ((fun i => x i j) : Germ (u : Filter I) K)) p = 0) :
    ∃ i, ∀ p ∈ P, MvPolynomial.eval (x i) p = 0 := by
  have he : ∀ p ∈ P, ∀ᶠ i in (u : Filter I), MvPolynomial.eval (x i) p = 0 := by
    intro p hp
    exact Germ.coe_eq.mp ((aeval_eq u x p).symm.trans (h p hp))
  exact ((eventually_all_finset P).mpr he).exists

end UltrafilterField

end -- UltrafilterField

section -- GenericPoint

/- Infinite sets of field-valued tuples admit transcendental points in field extensions. -/
open Filter MvPolynomial
namespace GenericPoint
universe u v
variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]

lemma infinite_coordinate {S : Set (σ → K)} (hS : S.Infinite) :
    ∃ j : σ, ((fun x : σ → K => x j) '' S).Infinite := by
  by_contra h
  push_neg at h
  apply hS
  apply (Set.Finite.pi' h).subset
  intro x hx j
  exact ⟨x,hx,rfl⟩

/-- A field extension contains a point preserving all polynomial identities on `S`,
with at least one coordinate transcendental over the original field. Every finite
set of equalities at this point is witnessed by an actual point of `S`. -/
lemma exists_transcendental_point (S : Set (σ → K)) (hS : S.Infinite) :
    ∃ L : Type u, ∃ _ : Field L, ∃ _ : Algebra K L, ∃ x : σ → L,
      (∀ p : MvPolynomial σ K, (∀ y ∈ S, eval y p = 0) → aeval x p = 0) ∧
      (∀ P : Finset (MvPolynomial σ K), (∀ p ∈ P, aeval x p = 0) →
        ∃ y ∈ S, ∀ p ∈ P, eval y p = 0) ∧
      ∃ j, Transcendental K (x j) := by
  classical
  obtain ⟨j,hj⟩ := infinite_coordinate hS
  let T : Set K := (fun x : σ → K => x j) '' S
  haveI : Infinite T := hj.to_subtype
  have hx : ∀ t : T, ∃ y ∈ S, y j = t.val := fun t => t.property
  choose y hy hcoord using hx
  let u : Ultrafilter T := Ultrafilter.of cofinite
  let L := Germ (u : Filter T) K
  let x : σ → L := fun i => ((fun t => y t i) : Germ (u : Filter T) K)
  refine ⟨L,inferInstance,inferInstance,x,?_,?_,?_⟩
  · intro p hp
    exact UltrafilterField.aeval_zero_of_forall u y p (fun t => hp (y t) (hy t))
  · intro P hP
    obtain ⟨t,ht⟩ := UltrafilterField.finite_equalities u y P hP
    exact ⟨y t,hy t,ht⟩
  · refine ⟨j,?_⟩
    have hf : (fun t : T => y t j) = Subtype.val := funext hcoord
    change Transcendental K ((fun t : T => y t j) : Germ (u : Filter T) K)
    rw [hf]
    exact UltrafilterField.transcendental_of_injective u (Ultrafilter.of_le cofinite)
      Subtype.val Subtype.val_injective

end GenericPoint

end -- GenericPoint

section -- IndependentPoints

/- Independent solutions in field extensions, constructed from an infinite set of tuples. -/
open MvPolynomial
namespace IndependentPoints
universe u v

variable {K E L : Type u} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    {σ : Type v}

/-- Polynomial identities on `S` hold at `x`, and every finite collection of
polynomial equalities at `x` has a witness in `S`. -/
def Compatible (S : Set (σ → K)) (x : σ → L) : Prop :=
  (∀ p : MvPolynomial σ K, (∀ y ∈ S, eval y p = 0) → aeval x p = 0) ∧
  (∀ P : Finset (MvPolynomial σ K), (∀ p ∈ P, aeval x p = 0) →
    ∃ y ∈ S, ∀ p ∈ P, eval y p = 0)

lemma aeval_map (x : σ → L) (p : MvPolynomial σ K) :
    aeval x (map (algebraMap K E) p) = aeval x p := by
  simp only [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K E L]

lemma eval_map_coords (y : σ → K) (p : MvPolynomial σ K) :
    eval (algebraMap K E ∘ y) (map (algebraMap K E) p) =
      algebraMap K E (eval y p) := by
  have hh := aeval_map (K := K) (E := E) (L := E) (algebraMap K E ∘ y) p
  rw [MvPolynomial.aeval_eq_eval] at hh
  rw [hh, aeval_algebraMap_apply E, MvPolynomial.aeval_eq_eval]

lemma Compatible.map {S : Set (σ → K)} {x : σ → E} (hx : Compatible S x) :
    Compatible S (algebraMap E L ∘ x) := by
  constructor
  · intro p hp
    rw [aeval_algebraMap_apply L, hx.1 p hp, map_zero]
  · intro P hP
    apply hx.2 P
    intro p hp
    have h := hP p hp
    rw [aeval_algebraMap_apply L] at h
    exact (algebraMap E L).injective (h.trans (map_zero _).symm)

lemma Compatible.descend {S : Set (σ → K)} {x : σ → L}
    (hx : Compatible ((fun y : σ → K => algebraMap K E ∘ y) '' S) x) :
    Compatible S x := by
  classical
  constructor
  · intro p hp
    rw [← aeval_map (E := E)]
    apply hx.1
    rintro y ⟨z,hz,rfl⟩
    rw [eval_map_coords, hp z hz, map_zero]
  · intro P hP
    obtain ⟨y,hy,he⟩ := hx.2 (P.image (MvPolynomial.map (algebraMap K E))) (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      rw [aeval_map]
      exact hP q hq)
    obtain ⟨z,hz,rfl⟩ := hy
    refine ⟨z,hz,?_⟩
    intro p hp
    have h := he _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    rw [eval_map_coords] at h
    exact (algebraMap K E).injective (h.trans (map_zero _).symm)

lemma infinite_image {S : Set (σ → K)} (hS : S.Infinite) :
    ((fun y : σ → K => algebraMap K E ∘ y) '' S).Infinite := by
  apply hS.image
  intro x _ y _ h
  funext i
  exact (algebraMap K E).injective (congrFun h i)

/-- From any infinite set of tuples, obtain any prescribed finite number of compatible
points with one selected coordinate from each point algebraically independent over `K`. -/
lemma independent_points [Fintype σ] (S : Set (σ → K)) (hS : S.Infinite) (k : ℕ) :
    ∃ L : Type u, ∃ _ : Field L, ∃ _ : Algebra K L,
      ∃ x : Fin k → σ → L, ∃ j : Fin k → σ,
        (∀ i, Compatible S (x i)) ∧ AlgebraicIndependent K (fun i => x i (j i)) := by
  classical
  induction k with
  | zero =>
    refine ⟨K,inferInstance,inferInstance,Fin.elim0,Fin.elim0,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact algebraicIndependent_empty_type_iff.mpr (algebraMap K K).injective
  | succ k ih =>
    obtain ⟨E,hEF,hEA,x,j,hx,hi⟩ := ih
    letI := hEF
    letI := hEA
    let S' := (fun y : σ → K => algebraMap K E ∘ y) '' S
    have hS' : S'.Infinite := infinite_image hS
    obtain ⟨L,hLF,hLA,y,hy₁,hy₂,t,ht⟩ := GenericPoint.exists_transcendental_point S' hS'
    letI := hLF
    letI := hLA
    letI : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
    letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hy : Compatible S y := Compatible.descend (E := E) ⟨hy₁,hy₂⟩
    have hxi (i : Fin k) : Compatible S (algebraMap E L ∘ x i) := (hx i).map
    have hiy : AlgebraicIndependent E (fun _ : Fin 1 => y t) :=
      algebraicIndependent_unique_type_iff.mpr ht
    have hii := hi.sumElim_comp hiy
    let e : Fin (k+1) ≃ Fin 1 ⊕ Fin k :=
      (finSumFinEquiv : Fin k ⊕ Fin 1 ≃ Fin (k+1)).symm.trans (Equiv.sumComm _ _)
    let xs : Fin 1 ⊕ Fin k → σ → L := Sum.elim (fun _ => y) (fun i => algebraMap E L ∘ x i)
    let js : Fin 1 ⊕ Fin k → σ := Sum.elim (fun _ => t) j
    refine ⟨L,hLF,inferInstance,xs ∘ e,js ∘ e,?_,?_⟩
    · intro i
      change Compatible S (xs (e i))
      cases e i with
      | inl a => exact hy
      | inr b => exact hxi b
    · convert hii.comp e e.injective using 1
      funext i
      change xs (e i) (js (e i)) =
        Sum.elim (fun _ : Fin 1 => y t) (fun i => algebraMap E L (x i (j i))) (e i)
      cases e i <;> rfl

end IndependentPoints

end -- IndependentPoints

section -- PolynomialBipartite

/- Polynomial bipartite graphs over arbitrary fields and compatible coordinate placements. -/
open MvPolynomial Finset SimpleGraph
namespace PolynomialBipartite
universe u v w
variable {K : Type u} [Field K] {τ : Type v} {J : Type*}

abbrev Point (K : Type*) (τ : Type*) := τ → K
abbrev Vertex (K : Type*) (τ : Type*) := Point K τ ⊕ Point K τ
abbrev Variables (τ : Type*) := τ ⊕ τ

def color : Vertex K τ → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
def coord : Vertex K τ → Point K τ := Sum.elim id id

def place {W : Type*} (κ : W → Fin 2) (y : W × τ → K) (w : W) : Vertex K τ :=
  if κ w = 0 then Sum.inl (fun t => y (w,t)) else Sum.inr (fun t => y (w,t))

lemma color_place {W : Type*} (κ : W → Fin 2) (y : W × τ → K) (w : W) :
    color (place κ y w) = κ w := by
  by_cases h : κ w = 0
  · simp [place,h,color]
  · have hh : κ w = 1 := by omega
    simp [place,h,color,hh]

lemma coord_place {W : Type*} (κ : W → Fin 2) (y : W × τ → K) (w : W) :
    coord (place κ y w) = fun t => y (w,t) := by
  simp only [place]
  split_ifs <;> rfl

lemma vertex_ext {x y : Vertex K τ} (hc : color x = color y) (hp : coord x = coord y) : x = y := by
  cases x <;> cases y <;> simp_all [color,coord]

def graph (P : J → MvPolynomial (Variables τ) K) : SimpleGraph (Vertex K τ) where
  Adj u v := match u,v with
    | Sum.inl x, Sum.inr y => ∀ j, eval (Sum.elim x y) (P j) = 0
    | Sum.inr y, Sum.inl x => ∀ j, eval (Sum.elim x y) (P j) = 0
    | _, _ => False
  symm := by constructor; intro u v h; cases u <;> cases v <;> exact h
  loopless := by constructor; intro v; cases v <;> exact not_false


def pairVariables {W : Type*} (u v : W) : Variables τ → W × τ :=
  Sum.elim (fun t => (u,t)) (fun t => (v,t))

lemma eval_edge {W : Type*} (u v : W) (y : W × τ → K) (P : MvPolynomial (Variables τ) K) :
    eval y (rename (pairVariables u v) P) =
      eval (Sum.elim (fun t => y (u,t)) (fun t => y (v,t))) P := by
  rw [eval_rename]
  have h : y ∘ pairVariables u v = Sum.elim (fun t => y (u,t)) (fun t => y (v,t)) := by
    funext z; cases z <;> rfl
  rw [h]

section Extension
variable {L : Type u} [Field L] [Algebra K L]

lemma aeval_edge {W : Type*} (u v : W) (y : W × τ → L) (P : MvPolynomial (Variables τ) K) :
    aeval y (rename (pairVariables u v) P) =
      eval (Sum.elim (fun t => y (u,t)) (fun t => y (v,t))) (map (algebraMap K L) P) := by
  simp only [aeval_def, eval₂_rename, eval_map]
  have h : y ∘ pairVariables u v = Sum.elim (fun t => y (u,t)) (fun t => y (v,t)) := by
    funext z; cases z <;> rfl
  rw [h]

/-- Compatible points preserve injectivity of placements, including the vector disequalities. -/
lemma compatible_injective {W : Type*} [Fintype τ]
    (κ : W → Fin 2) (S : Set (W × τ → K)) (y : W × τ → L)
    (hy : IndependentPoints.Compatible S y)
    (hinj : ∀ z ∈ S, Function.Injective (place κ z)) : Function.Injective (place κ y) := by
  classical
  intro u v huv
  have hc : κ u = κ v := by simpa only [color_place] using congrArg color huv
  have he : ∀ t, y (u,t) = y (v,t) := by
    intro t
    simpa only [coord_place] using congrFun (congrArg coord huv) t
  let D : Finset (MvPolynomial (W × τ) K) :=
    univ.image (fun t => X (u,t) - X (v,t))
  obtain ⟨z,hz,hze⟩ := hy.2 D (by
    intro p hp
    obtain ⟨t,_,rfl⟩ := mem_image.mp hp
    simp only [map_sub, aeval_X, sub_eq_zero]
    exact he t)
  apply hinj z hz
  apply vertex_ext
  · simpa only [color_place] using hc
  · funext t
    have hh := hze _ (mem_image.mpr ⟨t,mem_univ _,rfl⟩)
    simpa only [coord_place, map_sub, eval_X, sub_eq_zero] using hh

/-- Compatible points preserve all polynomial graph adjacency constraints. -/
lemma compatible_hom {W : Type*} (G : SimpleGraph W) (κ : W → Fin 2)
    (P : J → MvPolynomial (Variables τ) K)
    (S : Set (W × τ → K)) (y : W × τ → L) (hS : S.Nonempty)
    (hy : IndependentPoints.Compatible S y)
    (hh : ∀ z ∈ S, ∀ u v, G.Adj u v → (graph P).Adj (place κ z u) (place κ z v)) :
    ∀ u v, G.Adj u v →
      (graph (fun j => map (algebraMap K L) (P j))).Adj (place κ y u) (place κ y v) := by
  intro u v huv
  by_cases hu : κ u = 0 <;> by_cases hv : κ v = 0
  · obtain ⟨z,hz⟩ := hS
    have hg := hh z hz u v huv
    simpa only [place,if_pos hu,if_pos hv,graph] using hg
  · simp only [place, if_pos hu, if_neg hv, graph]
    change ∀ j, eval (Sum.elim (fun t => y (u,t)) (fun t => y (v,t)))
      (map (algebraMap K L) (P j)) = 0
    intro j
    rw [← aeval_edge]
    apply hy.1
    intro z hz
    rw [eval_edge]
    have hg := hh z hz u v huv
    exact (show ∀ j, eval (Sum.elim (fun t => z (u,t)) (fun t => z (v,t))) (P j) = 0 by
      simpa only [place,if_pos hu,if_neg hv,graph] using hg) j
  · simp only [place, if_neg hu, if_pos hv, graph]
    change ∀ j, eval (Sum.elim (fun t => y (v,t)) (fun t => y (u,t)))
      (map (algebraMap K L) (P j)) = 0
    intro j
    rw [← aeval_edge]
    apply hy.1
    intro z hz
    rw [eval_edge]
    have hg := hh z hz u v huv
    exact (show ∀ j, eval (Sum.elim (fun t => z (v,t)) (fun t => z (u,t))) (P j) = 0 by
      simpa only [place,if_neg hu,if_pos hv,graph] using hg) j
  · obtain ⟨z,hz⟩ := hS
    have hg := hh z hz u v huv
    simpa only [place,if_neg hu,if_neg hv,graph] using hg

lemma compatible_fixed_coordinate {W : Type*} (S : Set (W × τ → K)) (y : W × τ → L)
    (hy : IndependentPoints.Compatible S y) (w : W) (t : τ) (c : K)
    (hc : ∀ z ∈ S, z (w,t) = c) : y (w,t) = algebraMap K L c := by
  have hh := hy.1 (X (w,t)-C c) (by
    intro z hz
    simp only [map_sub, eval_X, eval_C, sub_eq_zero]
    exact hc z hz)
  simpa only [map_sub, aeval_X, aeval_C, sub_eq_zero] using hh
end Extension
end PolynomialBipartite

end -- PolynomialBipartite

section -- AlgebraicGeneratorBounds

/- Algebraic independence cannot exceed the size of a generating tuple. -/
namespace AlgebraicGeneratorBounds
open AlgebraicIndependent

variable {K L I J : Type*} [Field K] [Field L] [Algebra K L] [Fintype I] [Fintype J]

lemma independent_card_le_generators (x : I → L) (hx : AlgebraicIndependent K x)
    (z : J → L) (hmem : ∀ i, x i ∈ IntermediateField.adjoin K (Set.range z)) :
    Fintype.card I ≤ Fintype.card J := by
  classical
  let M := AlgebraicIndependent.matroid K L
  have hi : M.Indep (Set.range x) := matroid_indep_iff.mpr hx.to_subtype_range
  have hs : Set.range x ⊆ M.closure (Set.range z) := by
    rintro y ⟨i,rfl⟩
    rw [matroid_closure_eq]
    apply IntermediateField.isAlgebraic_adjoin_iff.mp
    exact isAlgebraic_algebraMap (⟨x i,hmem i⟩ : IntermediateField.adjoin K (Set.range z))
  have hh := hi.cardinalMk_le_cRk_of_subset hs
  rw [M.cRk_closure] at hh
  have hcard := hh.trans (M.cRk_le_cardinalMk (Set.range z))
  have hcard' : Fintype.card (Set.range x) ≤ Fintype.card (Set.range z) := by
    simpa only [Cardinal.mk_fintype, Nat.cast_le] using hcard
  have hxcard : Fintype.card (Set.range x) = Fintype.card I := by
    exact Fintype.card_congr (Equiv.ofInjective x hx.injective).symm
  have hzcard : Fintype.card (Set.range z) ≤ Fintype.card J :=
    Fintype.card_le_of_surjective (fun j => (⟨z j,Set.mem_range_self j⟩ : Set.range z))
      (by rintro ⟨y,⟨j,rfl⟩⟩; exact ⟨j,rfl⟩)
  omega

lemma nested_adjoin_mem (v : I → L) (z : J → L) {c : L}
    (hc : c ∈ Algebra.adjoin (IntermediateField.adjoin K (Set.range v)) (Set.range z)) :
    c ∈ IntermediateField.adjoin K (Set.range (Sum.elim v z)) := by
  let T := IntermediateField.adjoin K (Set.range (Sum.elim v z))
  have hv : IntermediateField.adjoin K (Set.range v) ≤ T := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨i,rfl⟩
    exact IntermediateField.subset_adjoin K _ ⟨Sum.inl i,rfl⟩
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    exact IntermediateField.subset_adjoin K _ ⟨Sum.inr j,rfl⟩
  | algebraMap r => exact hv r.property
  | add x y _ _ hx hy => exact T.add_mem hx hy
  | mul x y _ _ hx hy => exact T.mul_mem hx hy

end AlgebraicGeneratorBounds

end -- AlgebraicGeneratorBounds

section -- PolynomialSampling

/- Elementary interpolation and uniform evaluations of bounded-degree random polynomials. -/
open Finset MvPolynomial
namespace PolynomialSampling

section Interpolation
variable {σ F I : Type*} [Field F] [Fintype I] [DecidableEq I]

lemma separator {x y : σ → F} (h : x ≠ y) :
    ∃ p : MvPolynomial σ F, p.totalDegree ≤ 1 ∧ eval x p = 1 ∧ eval y p = 0 := by
  classical
  obtain ⟨c,hc⟩ : ∃ c, x c ≠ y c := Function.ne_iff.mp h
  refine ⟨C ((x c-y c)⁻¹) * (X c-C (y c)), ?_, ?_, ?_⟩
  · calc
      _ ≤ (C ((x c-y c)⁻¹) : MvPolynomial σ F).totalDegree +
          (X c-C (y c)).totalDegree := totalDegree_mul _ _
      _ ≤ 0 + max (X c : MvPolynomial σ F).totalDegree (C (y c) : MvPolynomial σ F).totalDegree := by
        simpa only [totalDegree_C, zero_add] using totalDegree_sub (X c) (C (y c))
      _ = 1 := by simp
  · simp [sub_ne_zero.mpr hc]
  · simp

lemma basis_polynomial (x : I → (σ → F)) (hx : Function.Injective x) (i : I) :
    ∃ p : MvPolynomial σ F, p.totalDegree ≤ Fintype.card I - 1 ∧
      ∀ j, eval (x j) p = if j = i then 1 else 0 := by
  classical
  have hs : ∀ j : I, ∃ p : MvPolynomial σ F,
      p.totalDegree ≤ 1 ∧ eval (x i) p = 1 ∧ (j ≠ i → eval (x j) p = 0) := by
    intro j
    by_cases hji : j = i
    · refine ⟨1, by simp, by simp, ?_⟩
      exact fun h => (h hji).elim
    · obtain ⟨p,hp,hi,hj⟩ := separator (fun h => hji (hx h).symm)
      exact ⟨p,hp,hi,fun _ => hj⟩
  choose p hp hi hj using hs
  refine ⟨∏ j ∈ univ.erase i, p j, ?_, ?_⟩
  · calc
      _ ≤ ∑ j ∈ univ.erase i, (p j).totalDegree := totalDegree_finset_prod _ _
      _ ≤ ∑ _j ∈ univ.erase i, 1 := sum_le_sum (fun j _ => hp j)
      _ = _ := by simp
  · intro j
    rw [map_prod]
    by_cases hji : j = i
    · subst j
      simp [hi]
    · rw [if_neg hji]
      exact prod_eq_zero (mem_erase.mpr ⟨hji,mem_univ j⟩) (hj j hji)

/-- Any values at `m` distinct points admit an interpolant of total degree at most `m-1`.
No lower bound on the field cardinality is needed. -/
lemma interpolate (x : I → (σ → F)) (hx : Function.Injective x) (v : I → F) :
    ∃ p : MvPolynomial σ F, p.totalDegree ≤ Fintype.card I - 1 ∧
      ∀ i, eval (x i) p = v i := by
  classical
  choose p hp he using basis_polynomial x hx
  refine ⟨∑ i, C (v i) * p i, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simpa using hp i)
  · intro i
    simp only [map_sum, map_mul, eval_C, he]
    simp

/-- Simultaneous evaluation on the finite-dimensional space of polynomials of degree at most `d`. -/
noncomputable def evaluation (d : ℕ) (x : I → (σ → F)) :
    restrictTotalDegree σ F d →ₗ[F] (I → F) where
  toFun p i := eval (x i) p.val
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

lemma evaluation_surjective (d : ℕ) (x : I → (σ → F))
    (hx : Function.Injective x) (hd : Fintype.card I ≤ d+1) :
    Function.Surjective (evaluation d x) := by
  intro v
  obtain ⟨p,hp,he⟩ := interpolate x hx v
  refine ⟨⟨p, (mem_restrictTotalDegree _ _ _).mpr (hp.trans (by omega))⟩, ?_⟩
  exact funext he
end Interpolation

section Fibers
variable {M N : Type*} [AddGroup M] [AddGroup N]

/-- Translation identifies every nonempty fiber of a group homomorphism with its kernel. -/
def fiberEquivZero (f : M →+ N) (y : N) (z : M) (hz : f z = y) :
    {x // f x = y} ≃ {x // f x = 0} where
  toFun x := ⟨x.val-z, by simp [x.property,hz]⟩
  invFun x := ⟨x.val+z, by simp [x.property,hz]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

lemma card_fiber_eq [Fintype M] [Fintype N] (f : M →+ N)
    (hf : Function.Surjective f) (y : N) :
    Nat.card {x // f x = y} = Nat.card {x // f x = 0} := by
  obtain ⟨z,hz⟩ := hf y
  exact Nat.card_congr (fiberEquivZero f y z hz)

lemma card_eq_mul_card_fiber [Fintype M] [Fintype N] (f : M →+ N)
    (hf : Function.Surjective f) (y : N) :
    Fintype.card M = Fintype.card N * Nat.card {x // f x = y} := by
  classical
  have hc : ∀ v : N, Fintype.card {x // f x = v} = Nat.card {x // f x = y} := by
    intro v
    rw [← Nat.card_eq_fintype_card]
    exact (card_fiber_eq f hf v).trans (card_fiber_eq f hf y).symm
  calc
    Fintype.card M = Fintype.card ((v : N) × {x // f x = v}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ v : N, Fintype.card {x // f x = v} := Fintype.card_sigma
    _ = _ := by simp only [hc, sum_const, card_univ, smul_eq_mul]
end Fibers

section Uniform
variable {σ F I : Type*} [Field F] [Fintype F] [Fintype σ] [Fintype I]

noncomputable instance boundedPolynomialFintype (d : ℕ) :
    Fintype (restrictTotalDegree σ F d) := by
  haveI := Module.finite_of_finite F (M := restrictTotalDegree σ F d)
  exact Fintype.ofFinite _


/-- Evaluate a system of `a` independently sampled polynomials. -/
noncomputable def systemEvaluation (a d : ℕ) (x : I → (σ → F)) :
    (Fin a → restrictTotalDegree σ F d) →ₗ[F] (Fin a → I → F) where
  toFun p j := evaluation d x (p j)
  map_add' p q := by ext j i; simp [evaluation]
  map_smul' c p := by ext j i; simp [evaluation]

lemma systemEvaluation_surjective (a d : ℕ) (x : I → (σ → F))
    (hx : Function.Injective x) (hd : Fintype.card I ≤ d+1) :
    Function.Surjective (systemEvaluation a d x) := by
  classical
  intro v
  have h : ∀ j, ∃ p, evaluation d x p = v j := fun j => evaluation_surjective d x hx hd (v j)
  choose p hp using h
  exact ⟨p,funext hp⟩

lemma system_probability (a d : ℕ) (x : I → (σ → F))
    (hx : Function.Injective x) (hd : Fintype.card I ≤ d+1) (v : Fin a → I → F) :
    (Nat.card {p : Fin a → restrictTotalDegree σ F d //
        ∀ j i, eval (x i) (p j).val = v j i} : ℚ) /
      Fintype.card (Fin a → restrictTotalDegree σ F d) =
        1 / (Fintype.card F : ℚ) ^ (a * Fintype.card I) := by
  classical
  have hcount : Fintype.card (Fin a → restrictTotalDegree σ F d) =
      Fintype.card F ^ (a * Fintype.card I) *
        Nat.card {p : Fin a → restrictTotalDegree σ F d //
          ∀ j i, eval (x i) (p j).val = v j i} := by
    have h := card_eq_mul_card_fiber (systemEvaluation a d x).toAddMonoidHom
      (systemEvaluation_surjective a d x hx hd) v
    have heq : Nat.card {p // (systemEvaluation a d x).toAddMonoidHom p = v} =
        Nat.card {p : Fin a → restrictTotalDegree σ F d //
          ∀ j i, eval (x i) (p j).val = v j i} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun p =>
        _root_.funext_iff.trans (forall_congr' (fun j => _root_.funext_iff)))
    rw [heq] at h
    simpa only [Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h
  have hn : (0 : ℚ) < Fintype.card (Fin a → restrictTotalDegree σ F d) := by
    exact_mod_cast Fintype.card_pos
  have hq : (0 : ℚ) < (Fintype.card F : ℚ) ^ (a * Fintype.card I) := by
    exact_mod_cast pow_pos (Fintype.card_pos (α := F)) _
  apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hq)).mpr
  norm_cast
  simpa [mul_comm] using hcount.symm
end Uniform
end PolynomialSampling

end -- PolynomialSampling

section -- LinearRelations

/- Independent linear relations reduce the number of algebra generators needed for a tuple. -/
open Finset Module
namespace LinearRelations

variable {K L E M : Type*} [Field K] [Field L] [Algebra K L] [Fintype E] [Fintype M]

lemma independent_rows (B : Matrix E M K) (hB : Function.Surjective B.mulVec) :
    LinearIndependent K (fun e => B e) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hg' (m : M) : ∑ e, g e * B e m = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hg m
  obtain ⟨w,hw⟩ := hB (Pi.single i 1)
  calc
    g i = ∑ e, g e * (Pi.single i (1 : K) : E → K) e := by simp [Pi.single_apply]
    _ = ∑ e, g e * ∑ m, B e m * w m := by
      apply sum_congr rfl
      intro e _
      rw [← hw]
      rfl
    _ = ∑ m, (∑ e, g e * B e m) * w m := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro e _
      ring
    _ = 0 := by simp [hg']

lemma small_generating_set (B : Matrix E M K) (hB : Function.Surjective B.mulVec)
    (c : M → L) (hc : ∀ e, ∑ m, B e m • c m = 0) :
    ∃ d : ℕ, d + Fintype.card E ≤ Fintype.card M ∧
      ∃ z : Fin d → L, ∀ m, c m ∈ Algebra.adjoin K (Set.range z) := by
  classical
  let f : (M → K) →ₗ[K] L := ∑ m, (LinearMap.proj m).smulRight (c m)
  have hf (v : M → K) : f v = ∑ m, v m • c m := by
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  let row (e : E) : f.ker := ⟨B e, by rw [LinearMap.mem_ker, hf]; exact hc e⟩
  have hrow : LinearIndependent K row := by
    apply LinearIndependent.of_comp f.ker.subtype
    exact independent_rows B hB
  have he := hrow.fintype_card_le_finrank
  have hdim := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hdim
  let d := Module.finrank K f.range
  let basis := Module.finBasis K f.range
  let z : Fin d → L := fun i => (basis i).val
  refine ⟨d,by dsimp [d]; omega,z,?_⟩
  intro m
  have hcm : c m ∈ f.range := by
    refine ⟨Pi.single m 1,?_⟩
    rw [hf]
    simp [Pi.single_apply]
  let x : f.range := ⟨c m,hcm⟩
  have hx := congrArg Subtype.val (basis.sum_repr x)
  have hexp : c m = ∑ i : Fin d, (basis.repr x i) • z i := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hx.symm
  rw [hexp]
  apply Subalgebra.sum_mem
  intro i _
  apply Submodule.smul_mem (Algebra.adjoin K (Set.range z)).toSubmodule
  exact Algebra.subset_adjoin ⟨i,rfl⟩

end LinearRelations

end -- LinearRelations

section -- BoundedPolynomialCoefficients

/- Coefficient coordinates and linear elimination for bounded-degree polynomial equations. -/
open Finset MvPolynomial
namespace BoundedPolynomialCoefficients

variable {σ K L I : Type*} [Fintype σ] [Field K] [Field L] [Algebra K L] [Fintype I]

abbrev Exponent (σ : Type*) (d : ℕ) := {s : σ →₀ ℕ // s.sum (fun _ n => n) ≤ d}

noncomputable instance exponentFintype (d : ℕ) : Fintype (Exponent σ d) := by
  classical
  have hb (s : Exponent σ d) (i : σ) : s.val i ≤ d := by
    calc
      s.val i ≤ s.val.sum (fun _ n => n) := by
        rw [Finsupp.sum_fintype]
        · exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
        · simp
      _ ≤ d := s.property
  let f : Exponent σ d → (σ → Fin (d+1)) := fun s i => ⟨s.val i, Nat.lt_succ_of_le (hb s i)⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun h i)
  exact Fintype.ofInjective f hf

noncomputable def polynomial (d : ℕ) (c : Exponent σ d → K) : MvPolynomial σ K :=
  ∑ s, monomial s.val (c s)

lemma coeff_polynomial (d : ℕ) (c : Exponent σ d → K) (s : Exponent σ d) :
    coeff s.val (polynomial d c) = c s := by
  classical
  have he (z : Exponent σ d) : z.val = s.val ↔ z = s :=
    ⟨Subtype.ext,congrArg Subtype.val⟩
  simp only [polynomial, coeff_sum, coeff_monomial, he, sum_ite_eq', mem_univ, if_true]

lemma polynomial_degree (d : ℕ) (c : Exponent σ d → K) : (polynomial d c).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro s _
  exact (totalDegree_monomial_le _ _).trans s.property

lemma polynomial_coefficients (d : ℕ) (p : restrictTotalDegree σ K d) :
    polynomial d (fun s => coeff s.val p.val) = p.val := by
  classical
  ext s
  by_cases hs : s.sum (fun _ n => n) ≤ d
  · let t : Exponent σ d := ⟨s,hs⟩
    have he : ∀ z : Exponent σ d, z.val = s ↔ z = t := by
      intro z
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [polynomial, coeff_sum, coeff_monomial, he, sum_ite_eq', mem_univ, if_true]
    rfl
  · have hp : coeff s p.val = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      exact lt_of_le_of_lt ((mem_restrictTotalDegree _ _ _).mp p.property) (Nat.lt_of_not_ge hs)
    rw [hp, polynomial, coeff_sum]
    apply sum_eq_zero
    intro z _
    rw [coeff_monomial]
    split_ifs with h
    · exact (hs (h ▸ z.property)).elim
    · rfl

noncomputable def coefficientEquiv (d : ℕ) :
    (Exponent σ d → K) ≃ restrictTotalDegree σ K d where
  toFun c := ⟨polynomial d c,(mem_restrictTotalDegree σ d _).mpr (polynomial_degree d c)⟩
  invFun p s := coeff s.val p.val
  left_inv c := funext (coeff_polynomial d c)
  right_inv p := Subtype.ext (polynomial_coefficients d p)

noncomputable def evaluationMatrix (d : ℕ) (x : I → σ → K) : Matrix I (Exponent σ d) K :=
  fun i s => eval (x i) (monomial s.val 1)

lemma eval_polynomial (d : ℕ) (c : Exponent σ d → K) (x : σ → K) :
    eval x (polynomial d c) = ∑ s, eval x (monomial s.val (1 : K)) * c s := by
  classical
  simp only [polynomial, map_sum, eval_monomial]
  apply sum_congr rfl
  intro s _
  ring

lemma matrix_surjective (d : ℕ) (x : I → σ → K) (hx : Function.Injective x)
    (hd : Fintype.card I ≤ d+1) : Function.Surjective (evaluationMatrix d x).mulVec := by
  classical
  intro v
  obtain ⟨p,hp⟩ := PolynomialSampling.evaluation_surjective d x hx hd v
  refine ⟨fun s => coeff s.val p.val,?_⟩
  funext i
  have hh := congrFun hp i
  change eval (x i) p.val = v i at hh
  rw [← polynomial_coefficients d p, eval_polynomial] at hh
  exact hh

lemma mapped_eval_polynomial (d : ℕ) (c : Exponent σ d → L) (x : σ → K) :
    eval (fun i => algebraMap K L (x i)) (polynomial d c) =
      ∑ s, eval x (monomial s.val (1 : K)) • c s := by
  classical
  rw [eval_polynomial]
  apply sum_congr rfl
  intro s _
  simp only [eval_monomial, one_mul, Algebra.smul_def, map_finsuppProd, map_pow]


/-- Simultaneous evaluation eliminates `|J|*|I|` coefficient generators from a system. -/
lemma system_coefficient_generators {J : Type*} [Fintype J]
    (d : ℕ) (x : I → σ → K) (hx : Function.Injective x)
    (hd : Fintype.card I ≤ d+1) (c : J → Exponent σ d → L)
    (hc : ∀ j i, eval (fun t => algebraMap K L (x i t)) (polynomial d (c j)) = 0) :
    ∃ m : ℕ, m + Fintype.card J * Fintype.card I ≤
        Fintype.card J * Fintype.card (Exponent σ d) ∧
      ∃ z : Fin m → L, ∀ j s, c j s ∈ Algebra.adjoin K (Set.range z) := by
  classical
  let B : Matrix (J × I) (J × Exponent σ d) K :=
    fun ji zs => if ji.1 = zs.1 then evaluationMatrix d x ji.2 zs.2 else 0
  have hB : Function.Surjective B.mulVec := by
    intro v
    have hw : ∀ j : J, ∃ w : Exponent σ d → K,
        (evaluationMatrix d x).mulVec w = fun i => v (j,i) :=
      fun j => matrix_surjective d x hx hd (fun i => v (j,i))
    choose w hw using hw
    refine ⟨fun zs => w zs.1 zs.2,?_⟩
    funext ji
    have hh := congrFun (hw ji.1) ji.2
    simpa only [B, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul,
      zero_mul, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true] using hh
  have hrel (ji : J × I) : ∑ zs, B ji zs • c zs.1 zs.2 = 0 := by
    have hh := hc ji.1 ji.2
    rw [mapped_eval_polynomial] at hh
    simpa only [B, Fintype.sum_prod_type, ite_smul, zero_smul, sum_ite_irrel,
      sum_const_zero, sum_ite_eq, mem_univ, if_true, evaluationMatrix] using hh
  obtain ⟨m,hm,z,hz⟩ := LinearRelations.small_generating_set B hB (fun zs => c zs.1 zs.2) hrel
  refine ⟨m,?_,z,fun j s => hz (j,s)⟩
  simpa only [Fintype.card_prod] using hm

end BoundedPolynomialCoefficients

end -- BoundedPolynomialCoefficients

section -- GenericConstraints

/- A finite algebraic-independence bound for generic polynomial incidence constraints. -/
open BoundedPolynomialCoefficients AlgebraicGeneratorBounds
namespace GenericConstraints

variable {F L σ I J M T : Type*} [Field F] [Field L] [Algebra F L]
    [Fintype σ] [Fintype I] [Fintype J] [Fintype M] [Fintype T]

/-- Independent polynomial evaluations consume algebraic degrees of freedom.
This is the coefficient-counting step of the proposed generic-parameter argument. -/
lemma independent_extras_bound (d : ℕ) (v : M → L)
    (x : I → σ → IntermediateField.adjoin F (Set.range v)) (hx : Function.Injective x)
    (hd : Fintype.card I ≤ d+1) (c : J → Exponent σ d → L) (extra : T → L)
    (hc : ∀ j i, MvPolynomial.eval
      (fun t => algebraMap (IntermediateField.adjoin F (Set.range v)) L (x i t))
      (polynomial d (c j)) = 0)
    (hextra : ∀ t, extra t ∈ IntermediateField.adjoin F (Set.range v))
    (hind : AlgebraicIndependent F (Sum.elim (fun js : J × Exponent σ d => c js.1 js.2) extra)) :
    Fintype.card T + Fintype.card J * Fintype.card I ≤ Fintype.card M := by
  classical
  obtain ⟨m,hm,z,hz⟩ := system_coefficient_generators d x hx hd c hc
  have hv : IntermediateField.adjoin F (Set.range v) ≤
      IntermediateField.adjoin F (Set.range (Sum.elim v z)) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨i,rfl⟩
    exact IntermediateField.subset_adjoin F _ ⟨Sum.inl i,rfl⟩
  have hmem : ∀ i : (J × Exponent σ d) ⊕ T,
      Sum.elim (fun js : J × Exponent σ d => c js.1 js.2) extra i ∈
        IntermediateField.adjoin F (Set.range (Sum.elim v z)) := by
    intro i
    cases i with
    | inl js => exact nested_adjoin_mem v z (hz js.1 js.2)
    | inr t => exact hv (hextra t)
  have hcard := independent_card_le_generators _ hind (Sum.elim v z) hmem
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hcard
  omega

end GenericConstraints

end -- GenericConstraints

section -- PolynomialEdgeConstraints

/- Coordinate counts for finite subgraphs of a generic polynomial bipartite graph. -/
open Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
namespace PolynomialEdgeConstraints
universe u
variable {F L τ J T : Type*} [Field F] [Field L] [Algebra F L]
  [Fintype τ] [Fintype J] [Fintype T]

lemma edge_orientation (P : J → MvPolynomial (Variables τ) L)
    (e : Sym2 (Vertex L τ)) (he : e ∈ (graph P).edgeSet) :
    ∃ x y : τ → L, e = s(Sum.inl x, Sum.inr y) ∧
      ∀ j, eval (Sum.elim x y) (P j) = 0 := by
  induction e using Sym2.inductionOn with
  | _ v w =>
    cases v with
    | inl x =>
      cases w with
      | inl z => exact he.elim
      | inr y => exact ⟨x,y,rfl,he⟩
    | inr y =>
      cases w with
      | inl x => exact ⟨x,y,Sym2.eq_swap,he⟩
      | inr z => exact he.elim

/-- Every edge has a unique left-right evaluation tuple. -/
lemma edge_coordinates (P : J → MvPolynomial (Variables τ) L)
    (E : Finset (Sym2 (Vertex L τ))) (hE : ∀ e ∈ E, e ∈ (graph P).edgeSet) :
    ∃ x : E → Variables τ → L, Function.Injective x ∧
      (∀ e, e.val = s(Sum.inl (fun t => x e (Sum.inl t)),
        Sum.inr (fun t => x e (Sum.inr t)))) ∧
      ∀ j e, eval (x e) (P j) = 0 := by
  classical
  have hh (e : E) := edge_orientation P e.val (hE e.val e.property)
  choose l r he hp using hh
  refine ⟨fun e => Sum.elim (l e) (r e),?_,he,fun j e => hp e j⟩
  intro e f hef
  apply Subtype.ext
  rw [he e, he f]
  have hl : l e = l f := funext (fun t => congrFun hef (Sum.inl t))
  have hr : r e = r f := funext (fun t => congrFun hef (Sum.inr t))
  rw [hl,hr]

/-- Each independent edge evaluation consumes one coefficient degree of freedom
per defining polynomial. Extra independent scalars must fit into the remaining
vertex-coordinate degrees of freedom. -/
lemma independent_bound (d : ℕ) (c : J → Exponent (Variables τ) d → L)
    (U : Finset (Vertex L τ)) (E : Finset (Sym2 (Vertex L τ)))
    (hE : ∀ e ∈ E, e ∈ (graph (fun j => polynomial d (c j))).edgeSet)
    (hsupport : ∀ e ∈ E, ∀ v ∈ e, v ∈ U)
    (hd : E.card ≤ d+1) (extra : T → L)
    (hextra : ∀ t, ∃ v ∈ U, ∃ z : τ, extra t = coord v z)
    (hind : AlgebraicIndependent F
      (Sum.elim (fun js : J × Exponent (Variables τ) d => c js.1 js.2) extra)) :
    Fintype.card T + Fintype.card J * E.card ≤ U.card * Fintype.card τ := by
  classical
  obtain ⟨x,hx,he,hp⟩ := edge_coordinates (fun j => polynomial d (c j)) E hE
  let v : U × τ → L := fun z => coord z.1.val z.2
  let B := IntermediateField.adjoin F (Set.range v)
  have hm (w : Vertex L τ) (hw : w ∈ U) (t : τ) : coord w t ∈ B := by
    exact IntermediateField.subset_adjoin F _ ⟨(⟨w,hw⟩,t),rfl⟩
  have hxB (e : E) (t : Variables τ) : x e t ∈ B := by
    cases t with
    | inl z =>
      have hmem : Sum.inl (fun t => x e (Sum.inl t)) ∈ e.val := by
        rw [he]; exact Sym2.mem_mk_left _ _
      exact hm _ (hsupport _ e.property _ hmem) z
    | inr z =>
      have hmem : Sum.inr (fun t => x e (Sum.inr t)) ∈ e.val := by
        rw [he]; exact Sym2.mem_mk_right _ _
      exact hm _ (hsupport _ e.property _ hmem) z
  let x' : E → Variables τ → B := fun e t => ⟨x e t,hxB e t⟩
  have hx' : Function.Injective x' := by
    intro e f hef
    apply hx
    funext t
    exact congrArg Subtype.val (congrFun hef t)
  have hb := GenericConstraints.independent_extras_bound d v x' hx'
    (by simpa only [Fintype.card_coe] using hd) c extra
    (by intro j e; exact hp j e)
    (by intro t; obtain ⟨w,hw,z,hz⟩ := hextra t; rw [hz]; exact hm w hw z) hind
  simpa only [Fintype.card_prod, Fintype.card_coe] using hb

end PolynomialEdgeConstraints

end -- PolynomialEdgeConstraints

section -- GenericRootedFiber

/- Rooted-copy fibers in generic polynomial graphs are finite. -/
open Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
namespace GenericRootedFiber
universe u
variable {F : Type*} {K : Type u} [Field F] [Field K] [Algebra F K]
  {A R τ J : Type*} [Fintype A] [Fintype R] [Fintype τ] [Fintype J]

noncomputable def fiber (G : SimpleGraph (A ⊕ R)) (κ : A ⊕ R → Fin 2)
    (P : J → MvPolynomial (Variables τ) K) (root : R → τ → K) :
    Set ((A ⊕ R) × τ → K) :=
  {z | Function.Injective (place κ z) ∧
    (∀ u v, G.Adj u v → (graph P).Adj (place κ z u) (place κ z v)) ∧
    ∀ r t, z (Sum.inr r,t) = root r t}

lemma map_polynomial {L : Type*} [Field L] (f : K →+* L)
    (d : ℕ) (c : Exponent (Variables τ) d → K) :
    map f (polynomial d c) = polynomial d (fun s => f (c s)) := by
  simp only [polynomial, map_sum, map_monomial]

/-- Balance prevents positive-dimensional root fibers for generic coefficients.
The degree is only required to exceed the number of edges in a bounded union
of copies of the rooted graph. -/
lemma finite_fiber (G : SimpleGraph (A ⊕ R)) (κ : A ⊕ R → Fin 2)
    (d : ℕ) (c : J → Exponent (Variables τ) d → K)
    (hc : AlgebraicIndependent F (fun js : J × Exponent (Variables τ) d => c js.1 js.2))
    (ha : 0 < Fintype.card J)
    (hbalance : ∀ s : Finset A,
      Fintype.card τ * s.card ≤ Fintype.card J * (RootedUnionDensity.incident G s).card)
    (hd : (Fintype.card τ * Fintype.card R + 1) * Nat.card G.edgeSet ≤ d+1)
    (root : R → τ → K) :
    (fiber G κ (fun j => polynomial d (c j)) root).Finite := by
  classical
  by_contra hfin
  let k := Fintype.card τ * Fintype.card R + 1
  let S := fiber G κ (fun j => polynomial d (c j)) root
  have hS : S.Infinite := hfin
  obtain ⟨L,hLF,hLA,y,j,hy,hi⟩ := IndependentPoints.independent_points S hS k
  letI := hLF
  letI := hLA
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let c' : J → Exponent (Variables τ) d → L := fun j s => algebraMap K L (c j s)
  let P' : J → MvPolynomial (Variables τ) L := fun j => polynomial d (c' j)
  have hP' (j : J) : map (algebraMap K L) (polynomial d (c j)) = P' j :=
    map_polynomial _ _ _
  have hinj (i : Fin k) : Function.Injective (place κ (y i)) :=
    compatible_injective κ S (y i) (hy i) (fun z hz => hz.1)
  let f : Fin k → ((A ⊕ R) ↪ Vertex L τ) := fun i => ⟨place κ (y i),hinj i⟩
  have hfhom (i : Fin k) (u v : A ⊕ R) (huv : G.Adj u v) :
      (graph P').Adj (f i u) (f i v) := by
    have hh := compatible_hom G κ (fun j => polynomial d (c j)) S (y i)
      hS.nonempty (hy i) (fun z hz => hz.2.1) u v huv
    simpa only [hP', f, Function.Embedding.coeFn_mk] using hh
  let rL : R → Vertex L τ :=
    place (fun r => κ (Sum.inr r)) (fun z => algebraMap K L (root z.1 z.2))
  have hfroot (i : Fin k) (r : R) : f i (Sum.inr r) = rL r := by
    apply vertex_ext
    · simp only [f, rL, Function.Embedding.coeFn_mk, color_place]
    · funext t
      simp only [f, Function.Embedding.coeFn_mk, coord_place, rL]
      exact compatible_fixed_coordinate S (y i) (hy i) (Sum.inr r) t (root r t)
        (fun z hz => hz.2.2 r t)
  let I : Finset (Vertex L τ) := univ.biUnion (fun i => RootedUnionDensity.interiors (f i))
  let E : Finset (Sym2 (Vertex L τ)) :=
    univ.biUnion (fun i => RootedUnionDensity.copyEdges G (f i))
  let U : Finset (Vertex L τ) := I ∪ univ.image rL
  have huc : U.card ≤ I.card + Fintype.card R :=
    (card_union_le _ _).trans (Nat.add_le_add_left (card_image_le.trans_eq (card_univ)) _)
  have hE (e : Sym2 (Vertex L τ)) (he : e ∈ E) : e ∈ (graph P').edgeSet := by
    obtain ⟨i,_,he⟩ := mem_biUnion.mp he
    obtain ⟨e,hge,rfl⟩ := mem_image.mp he
    induction e using Sym2.inductionOn with
    | _ u v =>
      exact hfhom i u v (SimpleGraph.mem_edgeFinset.mp hge)
  have hsupport (e : Sym2 (Vertex L τ)) (he : e ∈ E) (v : Vertex L τ) (hv : v ∈ e) : v ∈ U := by
    obtain ⟨i,_,he⟩ := mem_biUnion.mp he
    rcases RootedUnionDensity.endpoint_support G (f i) he hv with hI | ⟨r,hr⟩
    · exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,hI⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨r,mem_univ _,(hfroot i r).symm.trans hr⟩)
  have hec : E.card ≤ k * Nat.card G.edgeSet := by
    calc
      E.card ≤ ∑ i : Fin k, (RootedUnionDensity.copyEdges G (f i)).card := card_biUnion_le
      _ = k * Nat.card G.edgeSet := by
        simp only [RootedUnionDensity.copyEdges,
          card_image_of_injective _ (Sym2.map.injective (f _).injective),
          sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
          SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin]
  have haQ : (0 : ℚ) < Fintype.card J := by exact_mod_cast ha
  have hb := RootedUnionDensity.union_density G ((Fintype.card τ : ℚ) / Fintype.card J)
    (fun s => by
      rw [div_mul_eq_mul_div, div_le_iff₀ haQ]
      have hh := hbalance s
      exact_mod_cast (by simpa only [Nat.mul_comm] using hh))
    f rL univ (fun i _ r => hfroot i r)
  change (Fintype.card τ : ℚ) / Fintype.card J * I.card ≤ E.card at hb
  rw [div_mul_eq_mul_div, div_le_iff₀ haQ] at hb
  have hbN : Fintype.card τ * I.card ≤ Fintype.card J * E.card := by
    have hh : (Fintype.card τ : ℚ) * I.card ≤ Fintype.card J * E.card := by
      simpa only [mul_comm] using hb
    exact_mod_cast hh
  have hind : AlgebraicIndependent F
      (Sum.elim (fun js : J × Exponent (Variables τ) d => c' js.1 js.2)
        (fun i => y i (j i))) := by
    have hh := (hc.sumElim_comp hi).comp
      (Equiv.sumComm (J × Exponent (Variables τ) d) (Fin k))
      (Equiv.sumComm _ _).injective
    convert hh using 1
    funext z
    cases z <;> rfl
  have hextra (i : Fin k) : ∃ v ∈ U, ∃ t : τ, y i (j i) = coord v t := by
    refine ⟨f i (j i).1,?_,(j i).2,?_⟩
    · cases h : (j i).1 with
      | inl a =>
        exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,
          (RootedUnionDensity.mem_interiors _ _).mpr ⟨a,rfl⟩⟩)
      | inr r =>
        exact mem_union_right _ (mem_image.mpr ⟨r,mem_univ _,(hfroot i r).symm⟩)
    · simp only [f, Function.Embedding.coeFn_mk, coord_place]
  have hbound := PolynomialEdgeConstraints.independent_bound d c' U E hE hsupport
    (hec.trans hd) (fun i => y i (j i)) hextra hind
  rw [Fintype.card_fin] at hbound
  have hmul := Nat.mul_le_mul_right (Fintype.card τ) huc
  dsimp only [k] at hbound
  nlinarith

end GenericRootedFiber

end -- GenericRootedFiber

section -- UniformFiberBound

/- A compactness argument for uniform finite bounds on polynomial fibers, via field ultrapowers. -/
open Filter MvPolynomial
namespace UniformFiberBound
universe u v w

/-- Polynomial equations and finite nonvanishing clauses. A clause asserts that at
least one of its polynomials is nonzero; this includes vector disequalities. -/
def Holds {K : Type u} [Field K] {σ : Type v}
    (P : Finset (MvPolynomial σ K)) (Q : Finset (Finset (MvPolynomial σ K)))
    {L : Type*} [Field L] [Algebra K L] (x : σ → L) : Prop :=
  (∀ p ∈ P, aeval x p = 0) ∧ ∀ q ∈ Q, ∃ p ∈ q, aeval x p ≠ 0

lemma holds_germ {K : Type u} [Field K] {σ : Type v} {I : Type*}
    (P : Finset (MvPolynomial σ K)) (Q : Finset (Finset (MvPolynomial σ K)))
    (u : Ultrafilter I) (x : I → σ → K) (h : ∀ᶠ i in (u : Filter I), Holds P Q (x i)) :
    Holds P Q (fun j => ((fun i => x i j) : Germ (u : Filter I) K)) := by
  constructor
  · intro p hp
    rw [UltrafilterField.aeval_eq]
    apply Germ.coe_eq.mpr
    filter_upwards [h] with i hi
    simpa only [aeval_eq_eval] using hi.1 p hp
  · intro q hq
    by_contra hh
    push_neg at hh
    have he : ∀ᶠ i in (u : Filter I), ∀ p ∈ q, eval (x i) p = 0 := by
      apply (eventually_all_finset q).mpr
      intro p hp
      have hh' := hh p hp
      rw [UltrafilterField.aeval_eq] at hh'
      exact Germ.coe_eq.mp hh'
    obtain ⟨i,hi,he⟩ := (h.and he).exists
    obtain ⟨p,hp,hp0⟩ := hi.2 q hq
    exact hp0 (by simpa only [aeval_eq_eval] using he p hp)

/-- If every fiber stays finite in every field extension, its sizes over the original
field are uniformly bounded. No algebraic-geometry counting theorem is assumed. -/
lemma uniform_bound {K : Type u} [Field K] {ρ : Type v} {τ : Type w} [Fintype τ]
    (P : Finset (MvPolynomial (ρ ⊕ τ) K))
    (Q : Finset (Finset (MvPolynomial (ρ ⊕ τ) K)))
    (hfinite : ∀ (L : Type u) [Field L] [Algebra K L] (r : ρ → L),
      Set.Finite {x : τ → L | Holds P Q (Sum.elim r x)}) :
    ∃ N : ℕ, ∀ r : ρ → K,
      Nat.card {x : τ → K // Holds P Q (Sum.elim r x)} ≤ N := by
  classical
  by_contra hbounded
  push_neg at hbounded
  have hchoose : ∀ n : ℕ, ∃ r : ρ → K,
      Nonempty (Fin (n+1) ↪ {x : τ → K // Holds P Q (Sum.elim r x)}) := by
    intro n
    obtain ⟨r,hr⟩ := hbounded n
    letI : Fintype {x : τ → K // Holds P Q (Sum.elim r x)} := (hfinite K r).fintype
    refine ⟨r,Function.Embedding.nonempty_of_card_le ?_⟩
    simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hr
  choose r er using hchoose
  let e (n : ℕ) := Classical.choice (er n)
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  let L := Germ (u : Filter ℕ) K
  let root : ρ → L := fun j => ((fun n => r n j) : Germ (u : Filter ℕ) K)
  let point (j n : ℕ) : τ → K := if h : j < n+1 then (e n ⟨j,h⟩).val else fun _ => 0
  let limit (j : ℕ) : τ → L := fun t => ((fun n => point j n t) : Germ (u : Filter ℕ) K)
  have hn (j : ℕ) : ∀ᶠ n in (u : Filter ℕ), j < n+1 := by
    apply Filter.Eventually.filter_mono (Ultrafilter.of_le atTop)
    filter_upwards [eventually_ge_atTop j] with n hn
    omega
  have hpoint (j : ℕ) : ∀ᶠ n in (u : Filter ℕ), Holds P Q (Sum.elim (r n) (point j n)) := by
    filter_upwards [hn j] with n hj
    dsimp only [point]
    rw [dif_pos hj]
    exact (e n ⟨j,hj⟩).property
  have hlimit (j : ℕ) : Holds P Q (Sum.elim root (limit j)) := by
    have hh := holds_germ P Q u (fun n => Sum.elim (r n) (point j n)) (hpoint j)
    convert hh using 1
    ext t
    cases t <;> rfl
  have hinj : Function.Injective limit := by
    intro i j hij
    have he : ∀ᶠ n in (u : Filter ℕ), point i n = point j n := by
      have he' : ∀ t : τ, ∀ᶠ n in (u : Filter ℕ), point i n t = point j n t :=
        fun t => Germ.coe_eq.mp (congrFun hij t)
      exact (eventually_all.mpr he').mono (fun _ h => funext h)
    obtain ⟨n,hnij,hnj,hni⟩ := (he.and ((hn j).and (hn i))).exists
    have hval : (e n ⟨i,hni⟩).val = (e n ⟨j,hnj⟩).val := by
      simpa only [point, dif_pos hni, dif_pos hnj] using hnij
    exact congrArg Fin.val ((e n).injective (Subtype.ext hval))
  haveI : Finite {x : τ → L // Holds P Q (Sum.elim root x)} := (hfinite L root).to_subtype
  haveI : Finite ℕ := Finite.of_injective
    (fun j => (⟨limit j,hlimit j⟩ : {x : τ → L // Holds P Q (Sum.elim root x)}))
    (fun i j h => hinj (congrArg Subtype.val h))
  exact not_finite ℕ

end UniformFiberBound

end -- UniformFiberBound

section -- PolynomialCopyConstraints

/- Finite polynomial constraints describing injective copies with a fixed color pattern. -/
open Finset MvPolynomial PolynomialBipartite
namespace PolynomialCopyConstraints
universe u
variable {K : Type u} [Field K] {W τ J : Type*}
  [Fintype W] [Fintype τ] [Fintype J]

noncomputable def edgePolys (κ : W → Fin 2) (P : J → MvPolynomial (Variables τ) K)
    (u v : W) : Finset (MvPolynomial (W × τ) K) := by
  classical
  exact if κ u = κ v then {1} else
    univ.image (fun j => rename (if κ u = 0 then pairVariables u v else pairVariables v u) (P j))

noncomputable def equations (G : SimpleGraph W) (κ : W → Fin 2)
    (P : J → MvPolynomial (Variables τ) K) : Finset (MvPolynomial (W × τ) K) := by
  classical
  exact univ.biUnion (fun uv : W × W => if G.Adj uv.1 uv.2 then edgePolys κ P uv.1 uv.2 else ∅)

noncomputable def clauses (κ : W → Fin 2) : Finset (Finset (MvPolynomial (W × τ) K)) := by
  classical
  exact (univ.filter (fun uv : W × W => uv.1 ≠ uv.2 ∧ κ uv.1 = κ uv.2)).image
    (fun uv => univ.image (fun t : τ => X (uv.1,t) - X (uv.2,t)))

variable {L : Type u} [Field L] [Algebra K L]

lemma edgePolys_iff (κ : W → Fin 2) (P : J → MvPolynomial (Variables τ) K)
    (y : W × τ → L) (u v : W) :
    (∀ p ∈ edgePolys κ P u v, aeval y p = 0) ↔
      (graph (fun j => map (algebraMap K L) (P j))).Adj (place κ y u) (place κ y v) := by
  classical
  by_cases hcol : κ u = κ v
  · have hnot : ¬(graph (fun j => map (algebraMap K L) (P j))).Adj
        (place κ y u) (place κ y v) := by
      simp only [place, ← hcol]
      split_ifs <;> exact not_false
    simp [edgePolys,hcol,hnot]
  · simp only [edgePolys, if_neg hcol, forall_mem_image, mem_univ, forall_const]
    by_cases hu : κ u = 0
    · have hv : κ v ≠ 0 := fun h => hcol (hu.trans h.symm)
      simp only [if_pos hu, aeval_edge, place, if_neg hv, graph]
    · have hv : κ v = 0 := by omega
      simp only [if_neg hu, aeval_edge, place, if_pos hv, graph]

lemma equations_iff (G : SimpleGraph W) (κ : W → Fin 2)
    (P : J → MvPolynomial (Variables τ) K) (y : W × τ → L) :
    (∀ p ∈ equations G κ P, aeval y p = 0) ↔
      ∀ u v, G.Adj u v →
        (graph (fun j => map (algebraMap K L) (P j))).Adj (place κ y u) (place κ y v) := by
  classical
  constructor
  · intro h u v huv
    apply (edgePolys_iff κ P y u v).mp
    intro p hp
    apply h p
    apply mem_biUnion.mpr
    exact ⟨(u,v),mem_univ _,by simpa only [if_pos huv] using hp⟩
  · intro h p hp
    obtain ⟨⟨u,v⟩,_,hp⟩ := mem_biUnion.mp hp
    by_cases huv : G.Adj u v
    · have he : p ∈ edgePolys κ P u v := by simpa only [if_pos huv] using hp
      exact (edgePolys_iff κ P y u v).mpr (h u v huv) p he
    · simpa only [if_neg huv, Finset.notMem_empty] using hp

lemma clauses_iff (κ : W → Fin 2) (y : W × τ → L) :
    (∀ q ∈ clauses (K := K) (τ := τ) κ, ∃ p ∈ q, aeval y p ≠ 0) ↔
      Function.Injective (place κ y) := by
  classical
  simp only [clauses, forall_mem_image, mem_filter, mem_univ, true_and, Prod.forall,
    exists_mem_image, mem_univ, true_and, map_sub, aeval_X, sub_ne_zero]
  constructor
  · intro h u v huv
    by_contra hne
    have hc : κ u = κ v := by simpa only [color_place] using congrArg color huv
    obtain ⟨t,ht⟩ := h u v ⟨hne,hc⟩
    exact ht (by simpa only [coord_place] using congrFun (congrArg coord huv) t)
  · intro h u v huv
    by_contra hn
    push_neg at hn
    apply huv.1
    apply h
    apply vertex_ext
    · simpa only [color_place] using huv.2
    · funext t
      simpa only [coord_place] using hn t

lemma holds_iff (G : SimpleGraph W) (κ : W → Fin 2)
    (P : J → MvPolynomial (Variables τ) K) (y : W × τ → L) :
    UniformFiberBound.Holds (equations G κ P) (clauses κ) y ↔
      Function.Injective (place κ y) ∧
      ∀ u v, G.Adj u v →
        (graph (fun j => map (algebraMap K L) (P j))).Adj (place κ y u) (place κ y v) := by
  rw [UniformFiberBound.Holds, equations_iff, clauses_iff, and_comm]

lemma holds_rename {σ ι : Type*} [DecidableEq (MvPolynomial ι K)] (f : σ → ι)
    (P : Finset (MvPolynomial σ K)) (Q : Finset (Finset (MvPolynomial σ K))) (y : ι → L) :
    UniformFiberBound.Holds (P.image (rename f)) (Q.image (fun q => q.image (rename f))) y ↔
      UniformFiberBound.Holds P Q (y ∘ f) := by
  classical
  simp only [UniformFiberBound.Holds, forall_mem_image, exists_mem_image, aeval_rename]

end PolynomialCopyConstraints

end -- PolynomialCopyConstraints

section -- GenericUniformFiber

/- Uniform bounds for rooted fibers of generic polynomial graphs. -/
open Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
  PolynomialCopyConstraints
namespace GenericUniformFiber
universe u
variable {F : Type*} {K : Type u} [Field F] [Field K] [Algebra F K]
  {A R τ J : Type*} [Fintype A] [Fintype R] [Fintype τ] [Fintype J]

def splitVariables : (A ⊕ R) × τ ≃ (R × τ) ⊕ (A × τ) :=
  (Equiv.sumProdDistrib A R τ).trans (Equiv.sumComm _ _)

def assemble {L : Type*} (r : R × τ → L) (x : A × τ → L) : (A ⊕ R) × τ → L :=
  Sum.elim r x ∘ splitVariables

lemma assemble_injective {L : Type*} (r : R × τ → L) :
    Function.Injective (assemble (A := A) r) := by
  intro x y h
  funext z
  exact congrFun h (Sum.inl z.1,z.2)

lemma uniform_bound (G : SimpleGraph (A ⊕ R)) (κ : A ⊕ R → Fin 2)
    (d : ℕ) (c : J → Exponent (Variables τ) d → K)
    (hc : AlgebraicIndependent F (fun js : J × Exponent (Variables τ) d => c js.1 js.2))
    (ha : 0 < Fintype.card J)
    (hbalance : ∀ s : Finset A,
      Fintype.card τ * s.card ≤ Fintype.card J * (RootedUnionDensity.incident G s).card)
    (hd : (Fintype.card τ * Fintype.card R + 1) * Nat.card G.edgeSet ≤ d+1) :
    ∃ N : ℕ, ∀ root : R → τ → K,
      Nat.card (GenericRootedFiber.fiber G κ (fun j => polynomial d (c j)) root) ≤ N := by
  classical
  letI : DecidableEq (Finset (MvPolynomial (R × τ ⊕ A × τ) K)) := Finset.decidableEq
  let P := equations G κ (fun j => polynomial d (c j))
  let Q := clauses (K := K) (τ := τ) κ
  let P' := P.image (rename (splitVariables (A := A) (R := R) (τ := τ)))
  let Q' := Q.image (fun q => q.image (rename (splitVariables (A := A) (R := R) (τ := τ))))
  have hfinite : ∀ (L : Type u) [Field L] [Algebra K L] (root : R × τ → L),
      Set.Finite {x : A × τ → L | UniformFiberBound.Holds P' Q' (Sum.elim root x)} := by
    intro L _ _ root
    letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
    letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let c' : J → Exponent (Variables τ) d → L := fun j s => algebraMap K L (c j s)
    have hc' : AlgebraicIndependent F
        (fun js : J × Exponent (Variables τ) d => c' js.1 js.2) :=
      hc.map' (f := IsScalarTower.toAlgHom F K L) (algebraMap K L).injective
    have hf := GenericRootedFiber.finite_fiber G κ d c' hc' ha hbalance hd
      (fun r t => root (r,t))
    apply Set.Finite.of_injOn (f := assemble root) _ (assemble_injective root).injOn hf
    intro x hx
    have hh := (holds_rename splitVariables P Q (Sum.elim root x)).mp (by simpa only [P', Q', Set.mem_setOf_eq] using hx)
    have he := (holds_iff G κ (fun j => polynomial d (c j)) (assemble root x)).mp hh
    refine ⟨he.1,?_,fun _ _ => rfl⟩
    simpa only [GenericRootedFiber.map_polynomial] using he.2
  obtain ⟨N,hN⟩ := UniformFiberBound.uniform_bound P' Q' hfinite
  refine ⟨N,?_⟩
  intro root
  let r : R × τ → K := fun z => root z.1 z.2
  let T := {x : A × τ → K // UniformFiberBound.Holds P' Q' (Sum.elim r x)}
  let S := GenericRootedFiber.fiber G κ (fun j => polynomial d (c j)) root
  haveI : Finite T := (hfinite K r).to_subtype
  have he (z : S) : assemble r (fun t => z.val (Sum.inl t.1,t.2)) = z.val := by
    funext t
    rcases t with ⟨w,t⟩
    cases w with
    | inl a => rfl
    | inr r => exact (z.property.2.2 r t).symm
  let f : S → T := fun z => ⟨fun t => z.val (Sum.inl t.1,t.2),by
    dsimp only [P', Q']
    apply (holds_rename splitVariables P Q _).mpr
    change UniformFiberBound.Holds P Q (assemble r (fun t => z.val (Sum.inl t.1,t.2)))
    rw [he z]
    apply (holds_iff G κ (fun j => polynomial d (c j)) z.val).mpr
    refine ⟨z.property.1,?_⟩
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using z.property.2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [← he x,← he y]
    exact congrArg (assemble r) (congrArg Subtype.val hxy)
  exact (Nat.card_le_card_of_injective f hf).trans (hN r)

end GenericUniformFiber

end -- GenericUniformFiber


section -- RootedPowers

/- Rooted powers and their relation to counts of common-root embeddings. -/
open Finset SimpleGraph
namespace RootedPowers
variable {A R V : Type*}

abbrev Vertex (A R : Type*) (t : ℕ) := (Fin t × A) ⊕ R

def graph (G : SimpleGraph (A ⊕ R)) (t : ℕ) : SimpleGraph (Vertex A R t) where
  Adj u v := match u,v with
    | Sum.inl x, Sum.inl y => x.1 = y.1 ∧ G.Adj (Sum.inl x.2) (Sum.inl y.2)
    | Sum.inl x, Sum.inr r => G.Adj (Sum.inl x.2) (Sum.inr r)
    | Sum.inr r, Sum.inl x => G.Adj (Sum.inr r) (Sum.inl x.2)
    | Sum.inr r, Sum.inr s => G.Adj (Sum.inr r) (Sum.inr s)
  symm := by
    constructor
    intro u v h
    cases u <;> cases v
    · exact ⟨h.1.symm,h.2.symm⟩
    · exact h.symm
    · exact h.symm
    · exact h.symm
  loopless := by
    constructor
    intro u h
    cases u
    · exact h.2.ne rfl
    · exact h.ne rfl

/-- One of the copies identified along the roots. -/
def layer (G : SimpleGraph (A ⊕ R)) (t : ℕ) (j : Fin t) : Copy G (graph G t) where
  toHom := {
    toFun := Sum.map (fun a => (j,a)) id
    map_rel' := by
      intro u v h
      cases u <;> cases v
      · exact ⟨rfl,h⟩
      · exact h
      · exact h
      · exact h }
  injective' := by
    intro u v h
    cases u <;> cases v <;> simp_all

/-- A smaller rooted power is a subgraph of a larger rooted power. -/
def inclusion (G : SimpleGraph (A ⊕ R)) {s t : ℕ} (h : s ≤ t) :
    Copy (graph G s) (graph G t) where
  toHom := {
    toFun := Sum.map (fun z => (Fin.castLE h z.1,z.2)) id
    map_rel' := by
      intro u v huv
      cases u <;> cases v
      · exact ⟨congrArg (Fin.castLE h) huv.1,huv.2⟩
      · exact huv
      · exact huv
      · exact huv }
  injective' := by
    intro u v huv
    cases u with
    | inl x =>
      cases v with
      | inl y =>
        have hh : (Fin.castLE h x.1,x.2) = (Fin.castLE h y.1,y.2) := Sum.inl.inj huv
        have hf : Fin.castLE h x.1 = Fin.castLE h y.1 := congrArg Prod.fst hh
        have hs : x.2 = y.2 := congrArg (fun z : Fin t × A => z.2) hh
        exact congrArg Sum.inl (Prod.ext (Fin.castLE_injective h hf) hs)
      | inr y => exact (Sum.inl_ne_inr huv).elim
    | inr x =>
      cases v with
      | inl y => exact (Sum.inr_ne_inl huv).elim
      | inr y => exact congrArg Sum.inr (Sum.inr.inj huv)

lemma graph_bipartite (G : SimpleGraph (A ⊕ R)) (hG : G.IsBipartite) (t : ℕ) :
    (graph G t).IsBipartite := by
  obtain ⟨c⟩ := hG
  refine ⟨Coloring.mk (fun v => match v with
    | Sum.inl x => c (Sum.inl x.2)
    | Sum.inr r => c (Sum.inr r)) ?_⟩
  intro u v h
  cases u <;> cases v
  · exact c.valid h.2
  · exact c.valid h
  · exact c.valid h
  · exact c.valid h

section Counting
variable [Fintype A] [Fintype R] [Fintype V] [DecidableEq V]


end Counting
end RootedPowers

end -- RootedPowers

section -- GenericPowerFree

/- A single rooted power is absent from a generic polynomial bipartite graph. -/
open Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
namespace GenericPowerFree
universe u
variable {F : Type*} {K : Type u} [Field F] [Field K] [Algebra F K]
  {A R τ J : Type*} [Fintype A] [Fintype R] [Fintype τ] [Fintype J]

lemma place_coord {W : Type*} (f : W → Vertex K τ) (w : W) :
    place (fun w => color (f w)) (fun z => coord (f z.1) z.2) w = f w := by
  apply vertex_ext
  · exact color_place _ _ _
  · exact coord_place _ _ _

lemma exists_power_free (G : SimpleGraph (A ⊕ R)) [Nonempty A]
    (d : ℕ) (c : J → Exponent (Variables τ) d → K)
    (hc : AlgebraicIndependent F (fun js : J × Exponent (Variables τ) d => c js.1 js.2))
    (ha : 0 < Fintype.card J)
    (hbalance : ∀ s : Finset A,
      Fintype.card τ * s.card ≤ Fintype.card J * (RootedUnionDensity.incident G s).card)
    (hd : (Fintype.card τ * Fintype.card R + 1) * Nat.card G.edgeSet ≤ d+1) :
    ∃ t : ℕ, 0 < t ∧ (RootedPowers.graph G t).Free (graph (fun j => polynomial d (c j))) := by
  classical
  have hbound (κ : A ⊕ R → Fin 2) := GenericUniformFiber.uniform_bound G κ d c hc ha hbalance hd
  choose N hN using hbound
  let M := ∑ κ : A ⊕ R → Fin 2, N κ
  refine ⟨M+1,by omega,?_⟩
  rintro ⟨f⟩
  let g (i : Fin (M+1)) := f.comp (RootedPowers.layer G (M+1) i)
  let root : R → τ → K := fun r => coord (f (Sum.inr r))
  let Fiber (κ : A ⊕ R → Fin 2) :=
    GenericRootedFiber.fiber G κ (fun j => polynomial d (c j)) root
  letI (κ : A ⊕ R → Fin 2) : Fintype (Fiber κ) :=
    (GenericRootedFiber.finite_fiber G κ d c hc ha hbalance hd root).fintype
  let data (i : Fin (M+1)) : Σ κ, Fiber κ :=
    ⟨fun w => color (g i w), ⟨fun z => coord (g i z.1) z.2,by
      constructor
      · intro u v huv
        exact (g i).injective (by change g i u = g i v; simpa only [place_coord] using huv)
      constructor
      · intro u v huv
        simp only [place_coord]
        exact (g i).toHom.map_rel' huv
      · intro r t
        rfl⟩⟩
  have hinj : Function.Injective data := by
    intro i j hij
    let a : A := Classical.choice inferInstance
    have hh := congrArg (fun z : Σ κ, Fiber κ => place z.1 z.2.val (Sum.inl a)) hij
    simp only [data, place_coord] at hh
    have he := f.injective hh
    exact congrArg Prod.fst (Sum.inl.inj he)
  have hcard := Fintype.card_le_of_injective data hinj
  have hcard' : Fintype.card (Σ κ, Fiber κ) ≤ M := by
    rw [Fintype.card_sigma]
    apply sum_le_sum
    intro κ _
    simpa only [Nat.card_eq_fintype_card] using hN κ root
  simp only [Fintype.card_fin] at hcard
  omega

end GenericPowerFree

end -- GenericPowerFree

section -- PolynomialGerm

/- Finite polynomial graph copies pass to ultrafilter germs. -/
open Filter Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
namespace PolynomialGerm
universe u
variable {I : Type*} {K : Type u} [Field K] (u : Ultrafilter I)

/-- The quotient homomorphism to the ring of germs. -/
def coeHom : (I → K) →+* Germ (u : Filter I) K where
  toFun f := (f : Germ (u : Filter I) K)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

lemma eval_polynomial_germ {σ : Type*} [Fintype σ] (d : ℕ)
    (x : I → σ → K) (c : I → Exponent σ d → K) :
    eval (fun t => coeHom u (fun i => x i t))
      (polynomial d (fun s => coeHom u (fun i => c i s))) =
        coeHom u (fun i => eval (x i) (polynomial d (c i))) := by
  classical
  simp only [eval_polynomial, eval_monomial, one_mul, Finsupp.prod]
  have he : (fun i => ∑ s : Exponent σ d, (∏ t ∈ s.val.support, (x i t)^(s.val t))*c i s) =
      ∑ s : Exponent σ d, (∏ t ∈ s.val.support, (fun i => x i t)^(s.val t))*(fun i => c i s) := by
    funext i
    simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]
  rw [he, map_sum]
  apply sum_congr rfl
  intro s _
  simp only [map_mul, map_prod, map_pow]

lemma color_ne_of_adj {τ J : Type*} (P : J → MvPolynomial (Variables τ) K)
    {x y : Vertex K τ} (h : (graph P).Adj x y) : color x ≠ color y := by
  cases x <;> cases y
  · exact h.elim
  · simp [color]
  · simp [color]
  · exact h.elim

lemma copy_germ {W τ J : Type*} [Fintype W] [Fintype τ] [Fintype J]
    (G : SimpleGraph W) (d : ℕ) (c : I → J → Exponent (Variables τ) d → K)
    (hcopy : ∀ᶠ i in (u : Filter I),
      Nonempty (G.Copy (graph (fun j => polynomial d (c i j))))) :
    Nonempty (G.Copy (graph (fun j => polynomial d (fun s => coeHom u (fun i => c i j s))))) := by
  classical
  let f (i : I) : W → Vertex K τ :=
    if h : Nonempty (G.Copy (graph (fun j => polynomial d (c i j))))
    then (fun w => (Classical.choice h).toHom w) else fun _ => Sum.inl (fun _ => 0)
  have hf : ∀ᶠ i in (u : Filter I), Function.Injective (f i) ∧
      ∀ a b, G.Adj a b → (graph (fun j => polynomial d (c i j))).Adj (f i a) (f i b) := by
    filter_upwards [hcopy] with i hi
    dsimp only [f]
    rw [dif_pos hi]
    exact ⟨(Classical.choice hi).injective,fun _ _ h => (Classical.choice hi).toHom.map_rel' h⟩
  obtain ⟨κ,hκ⟩ : ∃ κ : W → Fin 2, ∀ᶠ i in (u : Filter I), (fun w => color (f i w)) = κ :=
    Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (fun i => ⟨_,rfl⟩))
  let y : W × τ → Germ (u : Filter I) K := fun z => coeHom u (fun i => coord (f i z.1) z.2)
  have hinj : Function.Injective (place κ y) := by
    intro a b hab
    have hcol : κ a = κ b := by simpa only [color_place] using congrArg color hab
    have hcoord : ∀ᶠ i in (u : Filter I), coord (f i a) = coord (f i b) := by
      apply (eventually_all.mpr (fun t : τ => ?_)).mono (fun _ h => funext h)
      apply Germ.coe_eq.mp
      change y (a,t) = y (b,t)
      simpa only [coord_place] using congrFun (congrArg coord hab) t
    obtain ⟨i,hi,hci,hki⟩ := (hf.and (hcoord.and hκ)).exists
    apply hi.1
    apply vertex_ext
    · rw [congrFun hki a, congrFun hki b]
      exact hcol
    · exact hci
  have hproper (a b : W) (hab : G.Adj a b) : κ a ≠ κ b := by
    obtain ⟨i,hi,hki⟩ := (hf.and hκ).exists
    have hh := color_ne_of_adj _ (hi.2 a b hab)
    simpa only [congrFun hki a, congrFun hki b] using hh
  refine ⟨{ toHom := { toFun := place κ y, map_rel' := ?_ }, injective' := hinj }⟩
  intro a b hab
  have hp := hproper a b hab
  have hplace : ∀ᶠ i in (u : Filter I), ∀ w,
      place κ (fun z => coord (f i z.1) z.2) w = f i w := by
    filter_upwards [hκ] with i hi w
    rw [← hi]
    exact GenericPowerFree.place_coord (f i) w
  have hadj : ∀ᶠ i in (u : Filter I),
      (graph (fun j => polynomial d (c i j))).Adj
        (place κ (fun z => coord (f i z.1) z.2) a)
        (place κ (fun z => coord (f i z.1) z.2) b) := by
    filter_upwards [hf,hplace] with i hi hpi
    rw [hpi a,hpi b]
    exact hi.2 a b hab
  by_cases ha : κ a = 0
  · have hb : κ b ≠ 0 := fun h => hp (ha.trans h.symm)
    simp only [place, if_pos ha, if_neg hb, graph] at hadj ⊢
    intro j
    have he := eval_polynomial_germ u d
      (fun i => Sum.elim (coord (f i a)) (coord (f i b))) (fun i => c i j)
    have hcoords : (fun t => coeHom u (fun i =>
        Sum.elim (coord (f i a)) (coord (f i b)) t)) =
        Sum.elim (fun t => y (a,t)) (fun t => y (b,t)) := by
      funext t; cases t <;> rfl
    rw [hcoords] at he
    rw [he]
    exact Germ.coe_eq.mpr (hadj.mono (fun i hi => hi j))
  · have hb : κ b = 0 := by omega
    simp only [place, if_neg ha, if_pos hb, graph] at hadj ⊢
    intro j
    have he := eval_polynomial_germ u d
      (fun i => Sum.elim (coord (f i b)) (coord (f i a))) (fun i => c i j)
    have hcoords : (fun t => coeHom u (fun i =>
        Sum.elim (coord (f i b)) (coord (f i a)) t)) =
        Sum.elim (fun t => y (b,t)) (fun t => y (a,t)) := by
      funext t; cases t <;> rfl
    rw [hcoords] at he
    rw [he]
    exact Germ.coe_eq.mpr (hadj.mono (fun i hi => hi j))

end PolynomialGerm

end -- PolynomialGerm

section -- GenericObstruction

/- Compactness turns generic power-freeness into a finite coefficient obstruction. -/
open Filter Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
namespace GenericObstruction
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
  {A R τ J : Type*} [Fintype A] [Fintype R] [Fintype τ] [Fintype J]

/-- Some rooted power is excluded as soon as finitely many nonzero coefficient
polynomials remain nonzero. The proof is a compactness argument over `K`. -/
lemma finite_obstruction (G : SimpleGraph (A ⊕ R)) [Nonempty A]
    (d : ℕ) (ha : 0 < Fintype.card J)
    (hbalance : ∀ s : Finset A,
      Fintype.card τ * s.card ≤ Fintype.card J * (RootedUnionDensity.incident G s).card)
    (hd : (Fintype.card τ * Fintype.card R + 1) * Nat.card G.edgeSet ≤ d+1) :
    ∃ t : ℕ, ∃ P : Finset {p : MvPolynomial (J × Exponent (Variables τ) d) F // p ≠ 0},
      ∀ c : J × Exponent (Variables τ) d → K,
        (∀ p ∈ P, aeval c p.val ≠ 0) →
          (RootedPowers.graph G t).Free (graph (fun j => polynomial d (fun s => c (j,s)))) := by
  classical
  by_contra hn
  push_neg at hn
  let C := J × Exponent (Variables τ) d
  let NonzeroPoly := {p : MvPolynomial C F // p ≠ 0}
  let I := ℕ × Finset NonzeroPoly
  have hre (i : I) : ∃ c : C → K, (∀ p ∈ i.2, aeval c p.val ≠ 0) ∧
      Nonempty ((RootedPowers.graph G i.1).Copy (graph (fun j => polynomial d (fun s => c (j,s))))) := by
    obtain ⟨c,hc,hh⟩ := hn i.1 i.2
    exact ⟨c,hc,hh⟩
  choose c hc hcopy using hre
  let u : Ultrafilter I := Ultrafilter.of atTop
  let L := Germ (u : Filter I) K
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  letI : SMul K L := (inferInstance : Algebra K L).toSMul
  letI : SMul F L := (inferInstance : Algebra F L).toSMul
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let cg : C → L := fun s => PolynomialGerm.coeHom u (fun i => c i s)
  have heval (p : MvPolynomial C F) : aeval cg p =
      PolynomialGerm.coeHom u (fun i => aeval (c i) p) := by
    induction p using MvPolynomial.induction_on with
    | C r => simp only [aeval_C]; rfl
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      rfl
    | mul_X p s hp =>
      simp only [map_mul, hp, aeval_X]
      rfl
  have hind : AlgebraicIndependent F cg := by
    apply algebraicIndependent_iff.mpr
    intro p hp
    by_contra hp0
    have hh : ∀ᶠ i in (u : Filter I), aeval (c i) p ≠ 0 := by
      have he : ∀ᶠ i : I in atTop, (0,({⟨p,hp0⟩} : Finset NonzeroPoly)) ≤ i :=
        eventually_ge_atTop _
      filter_upwards [he.filter_mono (Ultrafilter.of_le atTop)] with i hi
      exact hc i ⟨p,hp0⟩ (hi.2 (mem_singleton_self _))
    rw [heval] at hp
    obtain ⟨i,hi,hzi⟩ := (hh.and (Germ.coe_eq.mp hp)).exists
    exact hi hzi
  obtain ⟨t,ht,hfree⟩ := GenericPowerFree.exists_power_free G d
    (fun j s => cg (j,s)) hind ha hbalance hd
  have hcontains : ∀ᶠ i in (u : Filter I),
      Nonempty ((RootedPowers.graph G t).Copy (graph (fun j => polynomial d (fun s => c i (j,s))))) := by
    have he : ∀ᶠ i : I in atTop, (t,(∅ : Finset NonzeroPoly)) ≤ i := eventually_ge_atTop _
    filter_upwards [he.filter_mono (Ultrafilter.of_le atTop)] with i hi
    exact ⟨(Classical.choice (hcopy i)).comp (RootedPowers.inclusion G hi.1)⟩
  exact hfree (PolynomialGerm.copy_germ u (RootedPowers.graph G t) d
    (fun i j s => c i (j,s)) hcontains)

lemma single_obstruction (G : SimpleGraph (A ⊕ R)) [Nonempty A]
    (d : ℕ) (ha : 0 < Fintype.card J)
    (hbalance : ∀ s : Finset A,
      Fintype.card τ * s.card ≤ Fintype.card J * (RootedUnionDensity.incident G s).card)
    (hd : (Fintype.card τ * Fintype.card R + 1) * Nat.card G.edgeSet ≤ d+1) :
    ∃ t : ℕ, 0 < t ∧ ∃ Q : MvPolynomial (J × Exponent (Variables τ) d) F,
      Q ≠ 0 ∧ ∀ c : J × Exponent (Variables τ) d → K, aeval c Q ≠ 0 →
        (RootedPowers.graph G t).Free (graph (fun j => polynomial d (fun s => c (j,s)))) := by
  classical
  obtain ⟨t,P,hP⟩ := finite_obstruction (F := F) (K := K) G d ha hbalance hd
  refine ⟨t+1,by omega,∏ p ∈ P, p.val,prod_ne_zero_iff.mpr (fun p _ => p.property),?_⟩
  intro c hc hcopy
  apply hP c _
  · exact ⟨(Classical.choice hcopy).comp (RootedPowers.inclusion G (Nat.le_succ t))⟩
  · rw [map_prod] at hc
    exact prod_ne_zero_iff.mp hc

end GenericObstruction

end -- GenericObstruction

section -- RandomPolynomialGraph

/- Bipartite random polynomial graphs and their exact bounded edge-independence. -/
open Finset SimpleGraph MvPolynomial
namespace RandomPolynomialGraph

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (b : ℕ)
abbrev Point := Fin b → F
abbrev Vertex := Point F b ⊕ Point F b
abbrev Variables := Fin b ⊕ Fin b
abbrev Sample (a d : ℕ) := Fin a → restrictTotalDegree (Variables b) F d

variable {F b}
def potentialEdge (xy : Point F b × Point F b) : Sym2 (Vertex F b) :=
  s(Sum.inl xy.1, Sum.inr xy.2)

lemma potentialEdge_injective : Function.Injective (potentialEdge (F := F) (b := b)) := by
  intro x y h
  apply Prod.ext_iff.mpr
  simpa only [potentialEdge, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, and_self, or_false, Prod.mk.injEq] using h

lemma potentialEdge_not_diag (xy : Point F b × Point F b) : ¬ (potentialEdge xy).IsDiag := by
  simp [potentialEdge, Sym2.isDiag_iff_proj_eq]

noncomputable def sampleEdges {a d : ℕ} (p : Sample F b a d) : Finset (Sym2 (Vertex F b)) :=
  (univ.filter (fun xy : Point F b × Point F b =>
    ∀ j, eval (Sum.elim xy.1 xy.2) (p j).val = 0)).image potentialEdge

lemma mem_sampleEdges {a d : ℕ} (p : Sample F b a d) (xy : Point F b × Point F b) :
    potentialEdge xy ∈ sampleEdges p ↔ ∀ j, eval (Sum.elim xy.1 xy.2) (p j).val = 0 := by
  classical
  rw [sampleEdges, mem_image]
  constructor
  · rintro ⟨z,hz,hze⟩
    have hzxy := potentialEdge_injective hze
    subst z
    exact (mem_filter.mp hz).2
  · intro h
    exact ⟨xy,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩

lemma sampleEdges_subset {a d : ℕ} (p : Sample F b a d) :
    sampleEdges p ⊆ univ.image potentialEdge := image_subset_image (filter_subset _ _)

lemma coordinate_injective : Function.Injective (fun xy : Point F b × Point F b =>
    (Sum.elim xy.1 xy.2 : Variables b → F)) := by
  intro x y h
  apply Prod.ext <;> funext i
  · exact congrFun h (Sum.inl i)
  · exact congrFun h (Sum.inr i)

/-- Encode a supported edge set by distinct points at which the defining polynomials are evaluated. -/
lemma edge_coordinates (E : Finset (Sym2 (Vertex F b)))
    (hE : E ⊆ univ.image potentialEdge) :
    ∃ x : E ↪ (Variables b → F), ∀ a d (p : Sample F b a d),
      E ⊆ sampleEdges p ↔ ∀ j i, eval (x i) (p j).val = 0 := by
  classical
  have hp : ∀ e : E, ∃ xy, potentialEdge xy = e.val := by
    intro e
    obtain ⟨xy,_,hxy⟩ := mem_image.mp (hE e.property)
    exact ⟨xy,hxy⟩
  choose xy hxy using hp
  let x : E ↪ (Variables b → F) := {
    toFun := fun e => Sum.elim (xy e).1 (xy e).2
    inj' := by
      intro e f h
      apply Subtype.ext
      have hpair := coordinate_injective h
      rw [← hxy e, ← hxy f, hpair] }
  refine ⟨x,?_⟩
  intro a d p
  constructor
  · intro h j i
    have hi := h i.property
    rw [← hxy i, mem_sampleEdges] at hi
    exact hi j
  · intro h e he
    let i : E := ⟨e,he⟩
    rw [← show potentialEdge (xy i) = e from hxy i, mem_sampleEdges]
    exact fun j => h j i

/-- A fixed set of at most `d+1` potential edges is present with probability `|F|^(-a|E|)`. -/
lemma edge_probability {a d : ℕ} (E : Finset (Sym2 (Vertex F b)))
    (hE : E ⊆ univ.image potentialEdge) (hd : E.card ≤ d+1) :
    (Nat.card {p : Sample F b a d // E ⊆ sampleEdges p} : ℚ) /
      Fintype.card (Sample F b a d) = 1/(Fintype.card F : ℚ)^(a*E.card) := by
  classical
  obtain ⟨x,hx⟩ := edge_coordinates E hE
  have heq : Nat.card {p : Sample F b a d // E ⊆ sampleEdges p} =
      Nat.card {p : Sample F b a d // ∀ j i, eval (x i) (p j).val = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (hx a d))
  rw [heq]
  simpa only [Fintype.card_coe, Pi.zero_apply, Sample] using PolynomialSampling.system_probability a d x
    x.injective (by simpa only [Fintype.card_coe] using hd) 0


lemma uniform_event {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    (∑ ω, (1 : ℚ)/Fintype.card Ω * if P ω then 1 else 0) =
      (Nat.card {ω // P ω} : ℚ) / Fintype.card Ω := by
  classical
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter, sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [mul_one_div]


noncomputable def graph {a d : ℕ} (p : Sample F b a d) : SimpleGraph (Vertex F b) :=
  fromEdgeSet (↑(sampleEdges p))

noncomputable instance {a d : ℕ} (p : Sample F b a d) : DecidableRel (graph p).Adj :=
  Classical.decRel _

lemma graph_edges {a d : ℕ} (p : Sample F b a d) : (graph p).edgeFinset = sampleEdges p := by
  classical
  apply Finset.coe_injective
  rw [coe_edgeFinset, graph, edgeSet_fromEdgeSet]
  ext e
  change (e ∈ sampleEdges p ∧ e ∉ Sym2.diagSet) ↔ e ∈ sampleEdges p
  constructor
  · exact And.left
  · intro he
    refine ⟨he,?_⟩
    obtain ⟨xy,_,rfl⟩ := mem_image.mp (sampleEdges_subset p he)
    simpa using potentialEdge_not_diag xy


lemma single_edge_probability (a d : ℕ) (xy : Point F b × Point F b) :
    (∑ p : Sample F b a d, (1 : ℚ)/Fintype.card (Sample F b a d) *
      if ∀ j, eval (Sum.elim xy.1 xy.2) (p j).val = 0 then 1 else 0) =
        1/(Fintype.card F : ℚ)^a := by
  classical
  have h := edge_probability (a := a) (d := d) {potentialEdge xy}
    (singleton_subset_iff.mpr (mem_image.mpr ⟨xy,mem_univ _,rfl⟩)) (by simp)
  simp only [card_singleton, mul_one] at h
  rw [uniform_event]
  convert h using 2
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun p => (singleton_subset_iff.trans (mem_sampleEdges p xy)).symm)


end RandomPolynomialGraph

end -- RandomPolynomialGraph

section -- FiniteVariance

/- Elementary second-moment estimates for finite uniform samples. -/
open Finset
namespace FiniteVariance
variable {Ω E : Type*} [Fintype Ω] [Nonempty Ω] [Fintype E]

noncomputable def avg (X : Ω → ℚ) : ℚ :=
  ∑ ω, (1 : ℚ) / Fintype.card Ω * X ω

lemma avg_const (c : ℚ) : avg (fun _ : Ω => c) = c := by
  have h : (Fintype.card Ω : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, sum_const, card_univ, nsmul_eq_mul]
  field_simp

lemma avg_add (X Y : Ω → ℚ) : avg (fun ω => X ω + Y ω) = avg X + avg Y := by
  simp only [avg, mul_add, sum_add_distrib]

lemma avg_sub (X Y : Ω → ℚ) : avg (fun ω => X ω - Y ω) = avg X - avg Y := by
  simp only [avg, mul_sub, sum_sub_distrib]

lemma avg_mul (c : ℚ) (X : Ω → ℚ) : avg (fun ω => c * X ω) = c * avg X := by
  simp only [avg, mul_left_comm _ c, mul_sum]

lemma avg_sum {I : Type*} [Fintype I] (X : Ω → I → ℚ) :
    avg (fun ω => ∑ i, X ω i) = ∑ i, avg (fun ω => X ω i) := by
  simp only [avg, mul_sum]
  exact sum_comm

lemma avg_mono {X Y : Ω → ℚ} (h : ∀ ω, X ω ≤ Y ω) : avg X ≤ avg Y :=
  sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (by positivity))

lemma avg_indicator (B : Ω → Prop) [DecidablePred B] :
    avg (fun ω => if B ω then 1 else 0) =
      (Nat.card {ω // B ω} : ℚ) / Fintype.card Ω := by
  classical
  simp only [avg, mul_ite, mul_one, mul_zero, ← sum_filter, sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [mul_one_div]

/-- Pairwise-independent Bernoulli events have second moment at most `μ²+μ`. -/
lemma indicator_moments (B : Ω → E → Prop) [DecidableRel B] (p : ℚ)
    (hfirst : ∀ e, avg (fun ω => if B ω e then 1 else 0) = p)
    (hsecond : ∀ e f, e ≠ f →
      avg (fun ω => if B ω e ∧ B ω f then 1 else 0) = p^2) :
    avg (fun ω => ∑ e, if B ω e then 1 else 0) = Fintype.card E * p ∧
    avg (fun ω => (∑ e, if B ω e then 1 else 0)^2) ≤
      (Fintype.card E * p)^2 + Fintype.card E * p := by
  classical
  constructor
  · rw [avg_sum]
    simp only [hfirst, sum_const, card_univ, nsmul_eq_mul]
  · have hexpand (ω : Ω) : (∑ e, if B ω e then (1 : ℚ) else 0)^2 =
        ∑ e, ∑ f, if B ω e ∧ B ω f then (1 : ℚ) else 0 := by
      rw [pow_two, sum_mul_sum]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro f _
      by_cases he : B ω e <;> by_cases hf : B ω f <;> simp [he,hf]
    simp_rw [hexpand, avg_sum]
    calc
      _ ≤ ∑ e : E, ∑ f : E, (p^2 + if e = f then p else 0) := by
        apply sum_le_sum
        intro e _
        apply sum_le_sum
        intro f _
        by_cases hef : e = f
        · subst f
          simp only [and_self, hfirst, if_true]
          nlinarith [sq_nonneg p]
        · rw [hsecond e f hef, if_neg hef, add_zero]
      _ = _ := by
        simp only [sum_add_distrib, sum_const, sum_ite_eq, mem_univ, if_true,
          card_univ, nsmul_eq_mul]
        ring

/-- A small exceptional set cannot contain all samples with at least half the
mean, when the variance is at most the mean and the mean is larger than eight. -/
lemma exists_dense_outside (X : Ω → ℚ) (B : Ω → Prop) [DecidablePred B] (μ : ℚ)
    (hμ : 8 < μ) (hmean : avg X = μ)
    (hsecond : avg (fun ω => (X ω)^2) ≤ μ^2 + μ)
    (hbad : avg (fun ω => if B ω then 1 else 0) < 1/2) :
    ∃ ω, ¬ B ω ∧ μ ≤ 2 * X ω := by
  classical
  by_contra hn
  push_neg at hn
  have hvar : avg (fun ω => (X ω - μ)^2) ≤ μ := by
    have he : (fun ω => (X ω - μ)^2) =
        (fun ω => (X ω)^2 - (2*μ)*X ω + μ^2) := by funext ω; ring
    rw [he, avg_add, avg_sub, avg_mul, avg_const, hmean]
    linarith
  have hpoint (ω : Ω) : μ^2/4 ≤ μ^2/4 * (if B ω then 1 else 0) + (X ω - μ)^2 := by
    by_cases hB : B ω
    · rw [if_pos hB, mul_one]
      nlinarith [sq_nonneg (X ω - μ)]
    · rw [if_neg hB, mul_zero, zero_add]
      have hh := hn ω hB
      have hm : 0 < μ := by linarith
      nlinarith [sq_nonneg (X ω), sq_nonneg (μ/2-X ω)]
  have hh := avg_mono hpoint
  rw [avg_const, avg_add, avg_mul] at hh
  have hp : 0 < μ^2/4 := by positivity
  have hbad' := mul_lt_mul_of_pos_left hbad hp
  nlinarith

end FiniteVariance

end -- FiniteVariance

section -- PolynomialEdgeVariance

/- Pairwise independence and edge-count concentration for random polynomial graphs. -/
open Finset SimpleGraph MvPolynomial RandomPolynomialGraph
namespace PolynomialEdgeVariance
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a b d : ℕ}

lemma pair_probability (hd : 1 ≤ d) (x y : Point F b × Point F b) (hxy : x ≠ y) :
    FiniteVariance.avg (fun p : Sample F b a d =>
      if (∀ j, eval (Sum.elim x.1 x.2) (p j).val = 0) ∧
        (∀ j, eval (Sum.elim y.1 y.2) (p j).val = 0) then 1 else 0) =
      (1/(Fintype.card F : ℚ)^a)^2 := by
  classical
  have he : potentialEdge x ≠ potentialEdge y := fun h => hxy (potentialEdge_injective h)
  have hh := edge_probability (a := a) (d := d) {potentialEdge x,potentialEdge y}
    (by intro e he; simp only [mem_insert, mem_singleton] at he
        rcases he with rfl | rfl <;> exact mem_image.mpr ⟨_,mem_univ _,rfl⟩)
    (by simp only [card_pair he]; omega)
  simp only [card_pair he] at hh
  rw [FiniteVariance.avg_indicator]
  have hcard : Nat.card {p : Sample F b a d //
      (∀ j, eval (Sum.elim x.1 x.2) (p j).val = 0) ∧
      (∀ j, eval (Sum.elim y.1 y.2) (p j).val = 0)} =
      Nat.card {p : Sample F b a d // {potentialEdge x,potentialEdge y} ⊆ sampleEdges p} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun p => by
      simp only [insert_subset_iff, singleton_subset_iff, mem_sampleEdges])
  rw [hcard, hh, one_div_pow, ← pow_mul]

lemma edge_moments (hd : 1 ≤ d) :
    FiniteVariance.avg (fun p : Sample F b a d => ((graph p).edgeFinset.card : ℚ)) =
      (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a ∧
    FiniteVariance.avg (fun p : Sample F b a d => ((graph p).edgeFinset.card : ℚ)^2) ≤
      ((Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a)^2 +
        (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a := by
  classical
  have hc (p : Sample F b a d) : ((graph p).edgeFinset.card : ℚ) =
      ∑ xy : Point F b × Point F b,
        if ∀ j, eval (Sum.elim xy.1 xy.2) (p j).val = 0 then (1 : ℚ) else 0 := by
    rw [graph_edges, sampleEdges, card_image_of_injective _ potentialEdge_injective]
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hh := FiniteVariance.indicator_moments
    (fun (p : Sample F b a d) (xy : Point F b × Point F b) =>
      ∀ j, eval (Sum.elim xy.1 xy.2) (p j).val = 0)
    (1/(Fintype.card F : ℚ)^a) (single_edge_probability a d)
    (fun x y hxy => pair_probability hd x y hxy)
  have hμ : (Fintype.card (Point F b × Point F b) : ℚ) *
      (1/(Fintype.card F : ℚ)^a) =
      (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a := by
    simp only [Fintype.card_prod, Point, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_pow, mul_one_div]
    rw [← pow_add]
    congr 2
    omega
  simpa only [← hc, hμ] using hh

end PolynomialEdgeVariance

end -- PolynomialEdgeVariance

section -- SchwartzZippelFinite

/- A finite-field Schwartz-Zippel bound for any finite variable type. -/
open Finset MvPolynomial
namespace SchwartzZippelFinite
variable {K σ : Type*} [Field K] [Fintype K] [Fintype σ] [DecidableEq K] [DecidableEq σ]

lemma avg_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω']
    (e : Ω ≃ Ω') (X : Ω' → ℚ) : FiniteVariance.avg (X ∘ e) = FiniteVariance.avg X := by
  unfold FiniteVariance.avg
  rw [Fintype.card_congr e]
  exact Equiv.sum_comp e (fun ω => (1 : ℚ) / Fintype.card Ω' * X ω)

lemma probability_le (p : MvPolynomial σ K) (hp : p ≠ 0) :
    FiniteVariance.avg (fun x : σ → K => if eval x p = 0 then 1 else 0) ≤
      (p.totalDegree : ℚ) / Fintype.card K := by
  classical
  let e := Fintype.equivFin σ
  let q := rename e p
  have hq : q ≠ 0 := by
    intro hq0
    apply hp
    apply rename_injective e e.injective
    simpa only [map_zero] using hq0
  let f : (Fin (Fintype.card σ) → K) ≃ (σ → K) := {
    toFun := fun x => x ∘ e
    invFun := fun x => x ∘ e.symm
    left_inv := by intro x; funext i; simp
    right_inv := by intro x; funext i; simp }
  have he (x : Fin (Fintype.card σ) → K) : eval (f x) p = eval x q := by
    rw [eval_rename]
    rfl
  rw [← avg_equiv f]
  simp only [Function.comp_def]
  rw [FiniteVariance.avg_indicator]
  have hc : Nat.card {x : Fin (Fintype.card σ) → K // eval (f x) p = 0} =
      (univ.filter (fun x : Fin (Fintype.card σ) → K => eval x q = 0)).card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, he]
  rw [hc, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hz := schwartz_zippel_totalDegree hq (univ : Finset K)
  have hz' : ((univ.filter (fun x : Fin (Fintype.card σ) → K => eval x q = 0)).card : ℚ) /
      (Fintype.card K : ℚ)^Fintype.card σ ≤ (q.totalDegree : ℚ) / Fintype.card K := by
    exact_mod_cast hz
  exact hz'.trans (div_le_div_of_nonneg_right (by exact_mod_cast totalDegree_rename_le e p) (by positivity))

end SchwartzZippelFinite

end -- SchwartzZippelFinite

section -- DenseGenericSamples

/- Dense polynomial graphs whose coefficients avoid a prescribed proper hypersurface. -/
open Finset MvPolynomial BoundedPolynomialCoefficients
namespace DenseGenericSamples
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a b d : ℕ}

abbrev CoeffIndex (a b d : ℕ) := Fin a × Exponent (RandomPolynomialGraph.Variables b) d

noncomputable def sampleEquiv (a b d : ℕ) :
    (CoeffIndex a b d → F) ≃ RandomPolynomialGraph.Sample F b a d where
  toFun c j := coefficientEquiv d (fun s => c (j,s))
  invFun p js := coeff js.2.val (p js.1).val
  left_inv c := by
    funext js
    exact coeff_polynomial d (fun s => c (js.1,s)) js.2
  right_inv p := by
    funext j
    exact Subtype.ext (polynomial_coefficients d (p j))

lemma graph_eq (p : RandomPolynomialGraph.Sample F b a d) :
    RandomPolynomialGraph.graph p = PolynomialBipartite.graph (fun j => (p j).val) := by
  classical
  ext u v
  change (s(u,v) ∈ (RandomPolynomialGraph.graph p).edgeSet) ↔ _
  rw [← SimpleGraph.mem_edgeFinset, RandomPolynomialGraph.graph_edges]
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      constructor
      · intro he
        obtain ⟨z,_,hz⟩ := mem_image.mp (RandomPolynomialGraph.sampleEdges_subset p he)
        simp only [RandomPolynomialGraph.potentialEdge, Sym2.eq_iff, Sum.inr_ne_inl,
          and_false, false_and, or_self] at hz
      · exact False.elim
    | inr y => exact RandomPolynomialGraph.mem_sampleEdges p (x,y)
  | inr y =>
    cases v with
    | inl x =>
      rw [Sym2.eq_swap]
      exact RandomPolynomialGraph.mem_sampleEdges p (x,y)
    | inr z =>
      constructor
      · intro he
        obtain ⟨z,_,hz⟩ := mem_image.mp (RandomPolynomialGraph.sampleEdges_subset p he)
        simp only [RandomPolynomialGraph.potentialEdge, Sym2.eq_iff, Sum.inl_ne_inr,
          false_and, and_false, or_self] at hz
      · exact False.elim

lemma exists_dense_avoiding (hd : 1 ≤ d)
    (P : MvPolynomial (CoeffIndex a b d) F) (hP : P ≠ 0)
    (hμ : 8 < (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a)
    (hdegree : 2 * P.totalDegree < Fintype.card F) :
    ∃ c : CoeffIndex a b d → F, eval c P ≠ 0 ∧
      Fintype.card F ^ (2*b) ≤ 2 * Fintype.card F ^ a *
        Nat.card (PolynomialBipartite.graph (fun j => polynomial d (fun s => c (j,s)))).edgeSet := by
  classical
  let e := sampleEquiv (F := F) a b d
  let X (c : CoeffIndex a b d → F) : ℚ :=
    ((RandomPolynomialGraph.graph (e c)).edgeFinset.card : ℚ)
  let μ : ℚ := (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a
  have hm := PolynomialEdgeVariance.edge_moments (F := F) (a := a) (b := b) hd
  have hmean : FiniteVariance.avg X = μ := by
    rw [show X = (fun p => ((RandomPolynomialGraph.graph p).edgeFinset.card : ℚ)) ∘ e from rfl,
      SchwartzZippelFinite.avg_equiv e]
    exact hm.1
  have hsecond : FiniteVariance.avg (fun c => (X c)^2) ≤ μ^2 + μ := by
    rw [show (fun c => (X c)^2) =
      (fun p => ((RandomPolynomialGraph.graph p).edgeFinset.card : ℚ)^2) ∘ e from rfl,
      SchwartzZippelFinite.avg_equiv e]
    exact hm.2
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hbad : FiniteVariance.avg (fun c : CoeffIndex a b d → F =>
      if eval c P = 0 then 1 else 0) < 1/2 := by
    apply (SchwartzZippelFinite.probability_le P hP).trans_lt
    apply (div_lt_iff₀ hq).mpr
    have hh : (2 : ℚ) * P.totalDegree < Fintype.card F := by exact_mod_cast hdegree
    linarith
  obtain ⟨c,hc,hden⟩ := FiniteVariance.exists_dense_outside X (fun c => eval c P = 0)
    μ hμ hmean hsecond hbad
  refine ⟨c,hc,?_⟩
  have hd' := (div_le_iff₀ (pow_pos hq a)).mp hden
  have hgraph : RandomPolynomialGraph.graph (e c) =
      PolynomialBipartite.graph (fun j => polynomial d (fun s => c (j,s))) := graph_eq (e c)
  have hcard : (RandomPolynomialGraph.graph (e c)).edgeFinset.card =
      Nat.card (PolynomialBipartite.graph (fun j => polynomial d (fun s => c (j,s)))).edgeSet := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, hgraph]
  change (Fintype.card F : ℚ)^(2*b) ≤ 2*X c*(Fintype.card F : ℚ)^a at hd'
  dsimp only [X] at hd'
  rw [hcard] at hd'
  have hh : (Fintype.card F : ℚ)^(2*b) ≤
      2*(Fintype.card F : ℚ)^a *
        Nat.card (PolynomialBipartite.graph (fun j => polynomial d (fun s => c (j,s)))).edgeSet := by
    nlinarith only [hd']
  exact_mod_cast hh

lemma mean_large (hb : 0 < b) (ha : a ≤ b) (hq : 8 < Fintype.card F) :
    8 < (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a := by
  have hq0 : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℚ) ≤ Fintype.card F := by exact_mod_cast (by omega : 1 ≤ Fintype.card F)
  have hp := pow_le_pow_right₀ hq1 (by omega : a+1 ≤ 2*b)
  rw [pow_succ] at hp
  have hh : (Fintype.card F : ℚ) ≤
      (Fintype.card F : ℚ)^(2*b)/(Fintype.card F : ℚ)^a := by
    apply (le_div_iff₀ (pow_pos hq0 a)).mpr
    simpa only [mul_comm] using hp
  exact lt_of_lt_of_le (by exact_mod_cast hq) hh

end DenseGenericSamples

end -- DenseGenericSamples

section -- PolynomialFieldEmbedding

/- Field embeddings induce injective copies of polynomial bipartite graphs. -/
open MvPolynomial PolynomialBipartite
namespace PolynomialFieldEmbedding
variable {K L τ J : Type*} [Field K] [Field L]

def vertexMap (f : K →+* L) : Vertex K τ → Vertex L τ :=
  Sum.map (fun x => f ∘ x) (fun x => f ∘ x)

lemma vertexMap_injective (f : K →+* L) : Function.Injective (vertexMap (τ := τ) f) := by
  apply Sum.map_injective.mpr
  constructor
  · intro x y h; funext t; exact f.injective (congrFun h t)
  · intro x y h; funext t; exact f.injective (congrFun h t)

lemma map_eval_pair (f : K →+* L) (x y : τ → K) (P : MvPolynomial (Variables τ) K) :
    eval (Sum.elim (f ∘ x) (f ∘ y)) (map f P) = f (eval (Sum.elim x y) P) := by
  rw [MvPolynomial.map_eval]
  have hh : f ∘ Sum.elim x y = Sum.elim (f ∘ x) (f ∘ y) := by
    funext t; cases t <;> rfl
  rw [hh]

def copy (f : K →+* L) (P : J → MvPolynomial (Variables τ) K) :
    SimpleGraph.Copy (graph P) (graph (fun j => map f (P j))) where
  toHom := {
    toFun := vertexMap f
    map_rel' := by
      intro u v huv
      cases u with
      | inl x =>
        cases v with
        | inl y => exact huv.elim
        | inr y =>
          intro j
          change eval (Sum.elim (f ∘ x) (f ∘ y)) (map f (P j)) = 0
          rw [map_eval_pair,huv j,map_zero]
      | inr y =>
        cases v with
        | inl x =>
          intro j
          change eval (Sum.elim (f ∘ x) (f ∘ y)) (map f (P j)) = 0
          rw [map_eval_pair,huv j,map_zero]
        | inr z => exact huv.elim }
  injective' := vertexMap_injective f

end PolynomialFieldEmbedding

end -- PolynomialFieldEmbedding

section -- GenericFiniteFieldLower

/- Dense finite-field graphs avoiding a single rooted power, without a point-counting theorem. -/
open Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients DenseGenericSamples
namespace GenericFiniteFieldLower
universe u
variable (F : Type u) [Field F]
  {A R : Type*} [Fintype A] [Fintype R]

lemma dense_specializations (G : SimpleGraph (A ⊕ R)) [Nonempty A]
    (a b d : ℕ) (ha : 0 < a) (hab : a ≤ b) (hd : 1 ≤ d)
    (hbalance : ∀ s : Finset A, b * s.card ≤ a * (RootedUnionDensity.incident G s).card)
    (hdegree : (b * Fintype.card R + 1) * Nat.card G.edgeSet ≤ d+1) :
    ∃ t Q : ℕ, 0 < t ∧ ∀ (E : Type u) [Field E] [Fintype E] [Algebra F E]
      [Algebra.IsAlgebraic F E], Q ≤ Fintype.card E →
      ∃ c : CoeffIndex a b d → E,
        (RootedPowers.graph G t).Free (graph (fun j => polynomial d (fun s => c (j,s)))) ∧
        Fintype.card E ^ (2*b) ≤ 2 * Fintype.card E ^ a *
          Nat.card (graph (fun j => polynomial d (fun s => c (j,s)))).edgeSet := by
  classical
  let K := AlgebraicClosure F
  obtain ⟨t,ht,P,hP,hfree⟩ := GenericObstruction.single_obstruction (F := F) (K := K)
    (τ := Fin b) (J := Fin a) G d
    (by simpa only [Fintype.card_fin] using ha)
    (by simpa only [Fintype.card_fin] using hbalance)
    (by simpa only [Fintype.card_fin] using hdegree)
  refine ⟨t,max 9 (2*P.totalDegree+1),ht,?_⟩
  intro E _ _ _ _ hE
  let ψ : E →ₐ[F] K := IsAlgClosed.lift
  let P' : MvPolynomial (CoeffIndex a b d) E := map (algebraMap F E) P
  have hP' : P' ≠ 0 := by
    intro hh
    apply hP
    apply map_injective (algebraMap F E) (algebraMap F E).injective
    simpa only [map_zero] using hh
  have hdeg : P'.totalDegree = P.totalDegree := by
    simp only [P', totalDegree, support_map_of_injective _ (algebraMap F E).injective]
  obtain ⟨c,hc,hden⟩ := DenseGenericSamples.exists_dense_avoiding (F := E) hd P' hP'
    (DenseGenericSamples.mean_large (by omega) hab (by omega)) (by rw [hdeg]; omega)
  have hc' : aeval c P ≠ 0 := by
    simpa only [P', eval_map, aeval_def] using hc
  have hcK : aeval (fun s => ψ (c s)) P ≠ 0 := by
    rw [← MvPolynomial.comp_aeval_apply c ψ P]
    exact fun hh => hc' (ψ.injective (hh.trans (map_zero ψ).symm))
  refine ⟨c,?_,hden⟩
  intro hf
  apply hfree (fun s => ψ (c s)) hcK
  obtain ⟨f⟩ := hf
  have hg := (PolynomialFieldEmbedding.copy ψ.toRingHom
    (fun j => polynomial d (fun s => c (j,s)))).comp f
  have heq : (fun j : Fin a => map ψ.toRingHom (polynomial d (fun s => c (j,s)))) =
      (fun j => polynomial d (fun s => ψ (c (j,s)))) := by
    funext j
    exact GenericRootedFiber.map_polynomial _ _ _
  rw [heq] at hg
  exact ⟨hg⟩

end GenericFiniteFieldLower

end -- GenericFiniteFieldLower

section -- TransferLowerBound

/- Transfer finite-field lower bounds to all sufficiently large vertex counts. -/
open Finset SimpleGraph Filter
namespace TransferLowerBound

lemma density_transfer {W : Type*} (G : SimpleGraph W) (a b n p : ℕ)
    (hp : 0 < p) (hn : 2 ≤ n) (hnp : n ≤ 2*p^b)
    (hlower : (p : ℝ)^(2*b) ≤ 2*(p : ℝ)^a*(extremalNumber (2*p^b) G : ℝ)) :
    (n : ℝ)^2 ≤ 16*(p : ℝ)^a*(extremalNumber n G : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hm : 2 ≤ 2*p^b := hn.trans hnp
  have hcn : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn
  have hcm : (0 : ℝ) < (2*p^b).choose 2 := by exact_mod_cast Nat.choose_pos hm
  have hc := (div_le_div_iff₀ hcm hcn).mp
    (antitoneOn_extremalNumber_div_choose_two G hn hm hnp)
  have hM : ((2*p^b).choose 2 : ℝ) ≤ 2*(p : ℝ)^(2*b) := by
    rw [Nat.cast_choose_two]
    push_cast
    rw [show 2*b = b+b by omega, pow_add]
    have hp0 : (0 : ℝ) ≤ (p : ℝ)^b := pow_nonneg hp'.le b
    nlinarith
  have hh : (n.choose 2 : ℝ) ≤ 4*(p : ℝ)^a*(extremalNumber n G : ℝ) := by
    apply le_of_mul_le_mul_left _ (pow_pos hp' (2*b))
    calc
      (p : ℝ)^(2*b)*(n.choose 2 : ℝ) ≤
          2*(p : ℝ)^a*((extremalNumber (2*p^b) G : ℝ)*(n.choose 2 : ℝ)) := by
        nlinarith only [mul_le_mul_of_nonneg_right hlower hcn.le]
      _ ≤ 2*(p : ℝ)^a*((extremalNumber n G : ℝ)*((2*p^b).choose 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 2*(p : ℝ)^a*((extremalNumber n G : ℝ)*(2*(p : ℝ)^(2*b))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hM (by positivity)) (by positivity)
      _ = (p : ℝ)^(2*b)*(4*(p : ℝ)^a*(extremalNumber n G : ℝ)) := by ring
  rw [Nat.cast_choose_two] at hh
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith


end TransferLowerBound

end -- TransferLowerBound

section -- DyadicLowerTransfer

/- Transfer finite-field graph bounds along powers of two to arbitrary vertex counts. -/
open Finset SimpleGraph Filter
namespace DyadicLowerTransfer

lemma power_at_root_scale (b Q n : ℕ) (hb : 0 < b) (hQ : 1 ≤ Q) (hn : Q^b ≤ n) :
    ∃ s : ℕ, 0 < s ∧ Q ≤ 2^s ∧ n ≤ 2*(2^s)^b ∧
      ((2^s : ℕ) : ℝ) ≤ 2*(n : ℝ)^((b : ℝ)⁻¹) := by
  let x := (n : ℝ)^((b : ℝ)⁻¹)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hxb : x^b = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by omega)
  have hQx : (Q : ℝ) ≤ x := by
    apply le_of_pow_le_pow_left₀ (by omega : b ≠ 0) hx0
    rw [hxb]
    exact_mod_cast hn
  have hx1 : 1 ≤ x := (by exact_mod_cast hQ : (1 : ℝ) ≤ Q).trans hQx
  obtain ⟨s,hs,hs'⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
  refine ⟨s+1,by omega,?_,?_,?_⟩
  · exact_mod_cast hQx.trans hs'.le
  · have hh := pow_le_pow_left₀ hx0 hs'.le b
    rw [hxb] at hh
    have hnp : n ≤ (2^(s+1))^b := by exact_mod_cast hh
    omega
  · push_cast
    rw [pow_succ]
    change (2 : ℝ)^s * 2 ≤ 2*x
    linarith

lemma power_isBigO_extremal {W : Type*} (G : SimpleGraph W) (a b Q : ℕ)
    (hb : 0 < b) (hQ : 1 ≤ Q)
    (hlower : ∀ s : ℕ, 0 < s → Q ≤ 2^s →
      ((2^s : ℕ) : ℝ)^(2*b) ≤ 2*((2^s : ℕ) : ℝ)^a *
        (extremalNumber (2*(2^s)^b) G : ℝ)) :
    Asymptotics.IsBigO atTop (fun n : ℕ => (n : ℝ)^(2-(a : ℝ)/b))
      (fun n : ℕ => (extremalNumber n G : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16*(2 : ℝ)^a, eventually_atTop.mpr ⟨max 2 (Q^b),?_⟩⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnQ : Q^b ≤ n := (le_max_right _ _).trans hn
  obtain ⟨s,hs,hsQ,hnp,hpbound⟩ := power_at_root_scale b Q n hb hQ hnQ
  have hd := TransferLowerBound.density_transfer G a b n (2^s) (by positivity)
    hn2 hnp (hlower s hs hsQ)
  have hnpow := pow_le_pow_left₀ (Nat.cast_nonneg (2^s)) hpbound a
  have hrpow : ((n : ℝ)^((b : ℝ)⁻¹))^a = (n : ℝ)^((a : ℝ)/b) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [mul_pow, hrpow] at hnpow
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), Nat.abs_cast]
  rw [Real.rpow_sub hn0, Real.rpow_two]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).mpr
  have hh := mul_le_mul_of_nonneg_right hnpow (show (0 : ℝ) ≤ extremalNumber n G by positivity)
  nlinarith only [hd,hh]

end DyadicLowerTransfer

end -- DyadicLowerTransfer

section -- UnconditionalRootedLower

/- The random-algebraic lower bound for any balanced rooted graph. -/
open Finset MvPolynomial PolynomialBipartite BoundedPolynomialCoefficients
namespace UnconditionalRootedLower
variable {A R : Type*} [Fintype A] [Fintype R]

/-- Balanced rooted graphs have a power with the predicted extremal lower bound.
This is only a lower bound; the corresponding single-power upper bound is not assumed. -/
lemma exists_power_lower (G : SimpleGraph (A ⊕ R)) [Nonempty A]
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hbalance : ∀ s : Finset A, b * s.card ≤ a * (RootedUnionDensity.incident G s).card) :
    ∃ t : ℕ, 0 < t ∧
      Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ)^(2-(a : ℝ)/b))
        (fun n : ℕ => (SimpleGraph.extremalNumber n (RootedPowers.graph G t) : ℝ)) := by
  classical
  let d := (b * Fintype.card R + 1) * Nat.card G.edgeSet + 1
  obtain ⟨t,Q,ht,hQ⟩ := GenericFiniteFieldLower.dense_specializations (ZMod 2)
    G a b d ha hab (by omega) hbalance (by omega)
  refine ⟨t,ht,?_⟩
  apply DyadicLowerTransfer.power_isBigO_extremal (RootedPowers.graph G t) a b (max 1 Q)
    (by omega) (le_max_left _ _)
  intro s hs hqs
  let E := GaloisField 2 s
  letI : Fintype E := Fintype.ofFinite E
  have hE : Fintype.card E = 2^s := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 s (by omega)
  obtain ⟨c,hfree,hden⟩ := hQ E (by rw [hE]; exact (le_max_right 1 Q).trans hqs)
  let H := graph (fun j => polynomial d (fun z => c (j,z)))
  have hV : Fintype.card (Vertex E (Fin b)) = 2*(2^s)^b := by
    simp only [Vertex, Point, Fintype.card_sum, Fintype.card_fun, Fintype.card_fin, hE]
    omega
  have he : Nat.card H.edgeSet ≤ SimpleGraph.extremalNumber (2*(2^s)^b) (RootedPowers.graph G t) := by
    have hh := SimpleGraph.card_edgeFinset_le_extremalNumber hfree
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, hV,
      Nat.card_eq_fintype_card] using hh
  rw [hE] at hden
  have hh := hden.trans (Nat.mul_le_mul_left (2*(2^s)^a) he)
  exact_mod_cast hh


end UnconditionalRootedLower

end -- UnconditionalRootedLower

section -- RootedSuspension

/- Suspension as a rooted-power operation, including its balance transformation. -/
open Finset SimpleGraph
namespace RootedSuspension
variable {A R : Type*}

def move : A ⊕ (Fin 2 ⊕ R) ≃ Fin 2 ⊕ (A ⊕ R) where
  toFun := Sum.elim (fun a => Sum.inr (Sum.inl a))
    (Sum.elim Sum.inl (fun r => Sum.inr (Sum.inr r)))
  invFun := Sum.elim (fun i => Sum.inr (Sum.inl i))
    (Sum.elim Sum.inl (fun r => Sum.inr (Sum.inr r)))
  left_inv := by intro v; cases v with
    | inl a => rfl
    | inr r => cases r <;> rfl
  right_inv := by intro v; cases v with
    | inl a => rfl
    | inr r => cases r <;> rfl

def graph {G : SimpleGraph (A ⊕ R)} (c : G.Coloring (Fin 2)) : SimpleGraph (A ⊕ (Fin 2 ⊕ R)) :=
  (SuspensionBounds.suspend c).comap move

def color {G : SimpleGraph (A ⊕ R)} (c : G.Coloring (Fin 2)) : (graph c).Coloring (Fin 2) :=
  Coloring.mk (fun v => Sum.elim id c (move v)) (by
    intro u v h
    change (SuspensionBounds.suspend c).Adj (move u) (move v) at h
    change Sum.elim id c (move u) ≠ Sum.elim id c (move v)
    cases hu : move u <;> cases hv : move v <;> rw [hu,hv] at h
    · exact h
    · exact h
    · exact h
    · exact c.valid h)

def old : A ⊕ R ↪ A ⊕ (Fin 2 ⊕ R) where
  toFun := Sum.map id Sum.inr
  inj' := Sum.map_injective.mpr ⟨Function.injective_id,Sum.inr_injective⟩

def powerColor {G : SimpleGraph (A ⊕ R)} (c : G.Coloring (Fin 2)) (t : ℕ) :
    (RootedPowers.graph G t).Coloring (Fin 2) :=
  Coloring.mk (Sum.elim (fun z => c (Sum.inl z.2)) (fun r => c (Sum.inr r))) (by
    intro u v h
    cases u <;> cases v
    · exact c.valid h.2
    · exact c.valid h
    · exact c.valid h
    · exact c.valid h)

def powerIso {G : SimpleGraph (A ⊕ R)} (c : G.Coloring (Fin 2)) (t : ℕ) :
    RootedPowers.graph (graph c) t ≃g SuspensionBounds.suspend (powerColor c t) where
  toEquiv := move
  map_rel_iff' := by
    intro u v
    cases u with
    | inl a =>
      cases v with
      | inl b => rfl
      | inr r => cases r <;> rfl
    | inr r =>
      cases r with
      | inl i => cases v with
        | inl a => rfl
        | inr s => cases s <;> rfl
      | inr r => cases v with
        | inl a => rfl
        | inr s => cases s <;> rfl

lemma suspend_connected {W : Type*} {G : SimpleGraph W} (c : G.Coloring (Fin 2)) :
    (SuspensionBounds.suspend c).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl 0,?_⟩
  intro v
  have he : (SuspensionBounds.suspend c).Adj (Sum.inl 0) (Sum.inl 1) := by
    change (0 : Fin 2) ≠ 1
    decide
  cases v with
  | inl i =>
    fin_cases i
    · exact Reachable.refl _
    · exact he.reachable
  | inr w =>
    by_cases hw : c w = 0
    · apply he.reachable.trans
      exact (show (SuspensionBounds.suspend c).Adj (Sum.inl 1) (Sum.inr w) by
        change (1 : Fin 2) ≠ c w; rw [hw]; decide).reachable
    · exact (show (SuspensionBounds.suspend c).Adj (Sum.inl 0) (Sum.inr w) from Ne.symm hw).reachable

lemma power_connected {G : SimpleGraph (A ⊕ R)} (c : G.Coloring (Fin 2)) (t : ℕ) :
    (RootedPowers.graph (graph c) t).Connected :=
  (powerIso c t).connected_iff.mpr (suspend_connected _)

section Balance
variable [Fintype A] [Fintype R] {G : SimpleGraph (A ⊕ R)}

lemma incident_gain (c : G.Coloring (Fin 2)) (s : Finset A) :
    (RootedUnionDensity.incident G s).card + s.card ≤ (RootedUnionDensity.incident (graph c) s).card := by
  classical
  let f : A → Sym2 (A ⊕ (Fin 2 ⊕ R)) :=
    fun a => s(Sum.inl a,Sum.inr (Sum.inl (c (Sum.inl a)).rev))
  let I := (RootedUnionDensity.incident G s).image (Sym2.map old)
  let N := s.image f
  have hI : I ⊆ RootedUnionDensity.incident (graph c) s := by
    intro e he
    obtain ⟨e,hge,rfl⟩ := mem_image.mp he
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset] at hge ⊢
    refine ⟨?_,?_⟩
    · rcases hge with ⟨heG,_,_,_⟩
      induction e using Sym2.inductionOn with
      | _ u v =>
        cases u <;> cases v <;> exact heG
    · obtain ⟨_,a,ha,hae⟩ := hge
      exact ⟨a,ha,Sym2.mem_map.mpr ⟨Sum.inl a,hae,rfl⟩⟩
  have hN : N ⊆ RootedUnionDensity.incident (graph c) s := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset]
    refine ⟨?_,a,ha,Sym2.mem_mk_left _ _⟩
    change c (Sum.inl a) ≠ (c (Sum.inl a)).rev
    generalize c (Sum.inl a) = i
    fin_cases i <;> decide
  have hdis : Disjoint I N := by
    apply Finset.disjoint_left.mpr
    intro e he hn
    obtain ⟨a,_,rfl⟩ := mem_image.mp hn
    obtain ⟨d,_,hd⟩ := mem_image.mp he
    have hmem : Sum.inr (Sum.inl (c (Sum.inl a)).rev) ∈ Sym2.map old d := by
      rw [hd]
      exact Sym2.mem_mk_right _ _
    obtain ⟨v,_,hv⟩ := Sym2.mem_map.mp hmem
    cases v <;> cases hv
  have hf : Function.Injective f := by
    intro a b hab
    have hh := (Sym2.eq_iff.mp hab).resolve_right (by simp [f])
    exact Sum.inl.inj hh.1

  have hcard : (I ∪ N).card = (RootedUnionDensity.incident G s).card + s.card := by
    rw [card_union_of_disjoint hdis]
    simp only [I,N,card_image_of_injective _ (Sym2.map.injective old.injective),
      card_image_of_injective _ hf]
  rw [← hcard]
  exact card_le_card (union_subset hI hN)

lemma balanced (c : G.Coloring (Fin 2)) (a b : ℕ)
    (hbalance : ∀ s : Finset A, b*s.card ≤ a*(RootedUnionDensity.incident G s).card) :
    ∀ s : Finset A, (b+a)*s.card ≤ a*(RootedUnionDensity.incident (graph c) s).card := by
  intro s
  have hh := Nat.mul_le_mul_left a (incident_gain c s)
  nlinarith [hbalance s]
end Balance

lemma upper_transform {G : SimpleGraph (A ⊕ R)} (c : G.Coloring (Fin 2))
    (a b t : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hconn : (RootedPowers.graph G t).Connected)
    (hupper : Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (extremalNumber n (RootedPowers.graph G t) : ℝ))
      (fun n : ℕ => (n : ℝ)^(2-(a : ℝ)/b))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (extremalNumber n (RootedPowers.graph (graph c) t) : ℝ))
      (fun n : ℕ => (n : ℝ)^(2-(a : ℝ)/(b+a))) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hα : 1 ≤ 2-(a : ℝ)/b := by have := (div_le_one hbR).mpr habR; linarith
  have hα₂ : 2-(a : ℝ)/b < 2 := by have := div_pos haR hbR; linarith
  have hh := SuspensionBounds.suspension_isBigO hconn (powerColor c t)
    (2-(a : ℝ)/b) hα hα₂ hupper
  have he : 1+1/(3-(2-(a : ℝ)/b)) = 2-(a : ℝ)/(b+a) := by
    have hd : (b : ℝ)+a ≠ 0 := by positivity
    have he0 : 3-(2-(a : ℝ)/b) = ((b : ℝ)+a)/b := by
      field_simp
      ring
    rw [he0,one_div_div]
    field_simp [hd]
    <;> ring
  simpa only [extremalNumber_congr_right (powerIso c t),he] using hh

end RootedSuspension

end -- RootedSuspension

section -- KSTUpper

/- A uniform Kővári–Sós–Turán upper bound, using tuple counts. -/
open Finset SimpleGraph
namespace KSTUpper

/-- The complete bipartite graph with the indicated two parts. -/
def graph (s t : ℕ) : SimpleGraph (Fin s ⊕ Fin t) where
  Adj u v := match u,v with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by constructor; intro u v h; cases u <;> cases v <;> exact h
  loopless := by constructor; intro v; cases v <;> exact not_false

lemma graph_bipartite (s t : ℕ) : (graph s t).IsBipartite := by
  refine ⟨Coloring.mk (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1)) ?_⟩
  intro u v h
  cases u <;> cases v <;> simp_all [graph]

section Counts
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma collision_count (s : ℕ) (i j : Fin s) (hij : i ≠ j) :
    (univ.filter (fun f : Fin s → V => f i = f j)).card ≤ Fintype.card V ^ (s-1) := by
  classical
  let B := {f : Fin s → V // f i = f j}
  let S := {k : Fin s // k ≠ j}
  let r : B → S → V := fun f k => f.val k.val
  have hr : Function.Injective r := by
    intro f g hfg
    apply Subtype.ext
    funext k
    by_cases hk : k = j
    · subst k
      exact f.property.symm.trans ((congrFun hfg ⟨i,hij⟩).trans g.property)
    · exact congrFun hfg ⟨k,hk⟩
  have hS : Fintype.card S = s-1 := by
    simp only [S, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have hh := Fintype.card_le_of_injective r hr
  simpa only [B, Fintype.card_subtype, Fintype.card_fun, hS] using hh

lemma noninjective_count (s : ℕ) :
    (univ.filter (fun f : Fin s → V => ¬ Function.Injective f)).card ≤
      s^2 * Fintype.card V ^ (s-1) := by
  classical
  let Bad := univ.filter (fun f : Fin s → V => ¬ Function.Injective f)
  let E (ij : Fin s × Fin s) :=
    univ.filter (fun f : Fin s → V => ij.1 ≠ ij.2 ∧ f ij.1 = f ij.2)
  have hsub : Bad ⊆ univ.biUnion E := by
    intro f hf
    have hh := (mem_filter.mp hf).2
    simp only [Function.Injective] at hh
    push_neg at hh
    obtain ⟨i,j,he,hij⟩ := hh
    exact mem_biUnion.mpr ⟨(i,j),mem_univ _,mem_filter.mpr ⟨mem_univ _,hij,he⟩⟩
  have hcard (ij : Fin s × Fin s) : (E ij).card ≤ Fintype.card V ^ (s-1) := by
    by_cases hij : ij.1 = ij.2
    · simp [E,hij]
    · have he : E ij = univ.filter (fun f : Fin s → V => f ij.1 = f ij.2) := by
        ext f
        simp only [E,mem_filter,mem_univ,true_and]
        exact and_iff_right hij
      rw [he]
      exact collision_count s ij.1 ij.2 hij
  calc
    Bad.card ≤ (univ.biUnion E).card := card_le_card hsub
    _ ≤ ∑ ij, (E ij).card := card_biUnion_le
    _ ≤ ∑ _ij : Fin s × Fin s, Fintype.card V ^ (s-1) := sum_le_sum (fun ij _ => hcard ij)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,pow_two]

variable (H : SimpleGraph V) [DecidableRel H.Adj]

def common (s : ℕ) (f : Fin s → V) : Finset V := univ.filter (fun v => ∀ i, H.Adj (f i) v)

lemma common_le (s t : ℕ) (hfree : (graph s t).Free H) (f : Fin s → V)
    (hf : Function.Injective f) : (common H s f).card ≤ t := by
  classical
  by_contra h
  have hle : t ≤ (common H s f).card := by omega
  obtain ⟨g⟩ : Nonempty (Fin t ↪ common H s f) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin,Fintype.card_coe] using hle)
  apply hfree
  refine ⟨{toHom := { toFun := Sum.elim f (fun j => (g j).val), map_rel' := ?_}, injective' := ?_}⟩
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact huv.elim
      | inr j => exact (mem_filter.mp (g j).property).2 i
    | inr i =>
      cases v with
      | inl j => exact ((mem_filter.mp (g i).property).2 j).symm
      | inr j => exact huv.elim
  · intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (hf huv)
      | inr j => exact ((mem_filter.mp (g j).property).2 i).ne huv |>.elim
    | inr i =>
      cases v with
      | inl j => exact ((mem_filter.mp (g i).property).2 j).ne huv.symm |>.elim
      | inr j => exact congrArg Sum.inr (g.injective (Subtype.ext huv))

lemma sum_degree_pow (s : ℕ) : ∑ v, H.degree v ^ s = ∑ f : Fin s → V, (common H s f).card := by
  classical
  have hc (v : V) : H.degree v ^ s =
      (univ.filter (fun f : Fin s → V => ∀ i, H.Adj (f i) v)).card := by
    let e : (Fin s → H.neighborSet v) ≃ {f : Fin s → V // ∀ i, H.Adj (f i) v} := {
      toFun f := ⟨fun i => (f i).val,fun i => (f i).property.symm⟩
      invFun f i := ⟨f.val i,(f.property i).symm⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fun, Fintype.card_fin, H.card_neighborSet_eq_degree,
      Fintype.card_subtype] using hh
  simp_rw [hc,common,card_filter]
  exact sum_comm

lemma sum_degree_pow_le (s t : ℕ) (hs : 0 < s) (hfree : (graph s t).Free H) :
    ∑ v, H.degree v ^ s ≤ (t+s^2) * Fintype.card V ^ s := by
  classical
  rw [sum_degree_pow]
  have hpoint (f : Fin s → V) : (common H s f).card ≤
      t + if ¬Function.Injective f then Fintype.card V else 0 := by
    by_cases hf : Function.Injective f
    · simp only [hf, not_true_eq_false, if_false, add_zero]
      exact common_le H s t hfree f hf
    · rw [if_pos hf]
      exact (card_le_card (filter_subset _ _)).trans (by simp)
  calc
    _ ≤ ∑ f : Fin s → V, (t + if ¬Function.Injective f then Fintype.card V else 0) :=
      sum_le_sum (fun f _ => hpoint f)
    _ = Fintype.card V ^ s * t +
        (univ.filter (fun f : Fin s → V => ¬Function.Injective f)).card * Fintype.card V := by
      simp only [sum_add_distrib, sum_const, card_univ,Fintype.card_fun,Fintype.card_fin,
        smul_eq_mul, ← sum_filter]
    _ ≤ Fintype.card V ^ s * t + s^2 * Fintype.card V ^ (s-1) * Fintype.card V :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (noninjective_count s)) _
    _ = _ := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hs]; ring
end Counts

lemma edge_bound {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (s t : ℕ) (hs : 0 < s)
    (hfree : (graph s t).Free H) :
    (H.edgeFinset.card : ℝ) ≤ (t+s^2+1) * (Fintype.card V : ℝ)^(2-(s : ℝ)⁻¹) := by
  let n : ℝ := Fintype.card V
  let C : ℝ := t+s^2+1
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have he : (0 : ℝ) ≤ H.edgeFinset.card := by positivity
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (s : ℝ),(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hm : (∑ v, (H.degree v : ℝ)^s) ≤ (t+s^2)*n^s := by
    dsimp only [n]
    exact_mod_cast sum_degree_pow_le H s t hs hfree
  have hj := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg univ hsR
    (fun v _ => (show (0 : ℝ) ≤ H.degree v by positivity))
  have hsum : (∑ v, (H.degree v : ℝ)) = 2 * H.edgeFinset.card := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  rw [hsum, Real.rpow_natCast, card_univ] at hj
  simp_rw [Real.rpow_natCast] at hj
  have hnp : (Fintype.card V : ℝ)^((s : ℝ)-1) = n^(s-1) := by
    have hcast : ((s-1 : ℕ) : ℝ) = (s : ℝ)-1 := by
      rw [Nat.cast_sub hs, Nat.cast_one]
    rw [← hcast, Real.rpow_natCast]
  rw [hnp] at hj
  have hrpow : (n^(2-(s : ℝ)⁻¹))^s = n^(2*s-1) := by
    rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2*s), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  apply le_of_pow_le_pow_left₀ (by omega : s ≠ 0) (by positivity)
  change (H.edgeFinset.card : ℝ)^s ≤ (C*n^(2-(s : ℝ)⁻¹))^s
  rw [mul_pow,hrpow]
  calc
    (H.edgeFinset.card : ℝ)^s ≤ (2*(H.edgeFinset.card : ℝ))^s :=
      pow_le_pow_left₀ he (by linarith) s
    _ ≤ n^(s-1) * ∑ v, (H.degree v : ℝ)^s := hj
    _ ≤ n^(s-1) * ((t+s^2)*n^s) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ n^(s-1) * (C*n^s) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [C]
      linarith
    _ = C*n^(2*s-1) := by
      rw [mul_left_comm, ← pow_add]
      congr 2
      omega
    _ ≤ C^s*n^(2*s-1) := mul_le_mul_of_nonneg_right
      (by simpa only [pow_one] using pow_le_pow_right₀ hC hs) (by positivity)

lemma upper (s t n : ℕ) (hs : 0 < s) (hn : 0 < n) :
    (extremalNumber n (graph s t) : ℝ) ≤ (t+s^2+1) * (n : ℝ)^(2-(s : ℝ)⁻¹) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro H _ hH
  exact edge_bound H s t hs hH

lemma upper_isBigO (s t : ℕ) (hs : 0 < s) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (extremalNumber n (graph s t) : ℝ))
      (fun n : ℕ => (n : ℝ)^(2-(s : ℝ)⁻¹)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨t+s^2+1,Filter.eventually_atTop.mpr ⟨1,?_⟩⟩
  intro n hn
  simpa only [Real.norm_eq_abs,Nat.abs_cast,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using upper s t n hs (by omega)

end KSTUpper

end -- KSTUpper

section -- RationalKST

/- Every exponent 2-1/s is a single-graph bipartite Turán exponent. -/
open Finset SimpleGraph
namespace RationalKST

lemma finite_realization {W : Type*} [Fintype W] (G : SimpleGraph W) (α : ℚ)
    (hG : G.IsBipartite)
    (hΘ : Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => (n : ℝ)^(α : ℝ))) :
    ∃ q : ℕ, ∃ H : SimpleGraph (Fin q), H.IsBipartite ∧
      Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ)^(α : ℝ)) := by
  let e := Fintype.equivFin W
  let H := G.map e.toEmbedding
  let i : G ≃g H := Iso.map e G
  refine ⟨Fintype.card W,H,?_,?_⟩
  · obtain ⟨c⟩ := hG
    exact ⟨Coloring.mk (fun v => c (i.symm v)) (fun h => c.valid (i.symm.toHom.map_rel' h))⟩
  · simpa only [extremalNumber_congr_right i] using hΘ

lemma star_balance (s : ℕ) (u : Finset (Fin 1)) :
    s*u.card ≤ 1*(RootedUnionDensity.incident (KSTUpper.graph 1 s) u).card := by
  classical
  by_cases hu : u.Nonempty
  · have hu1 : u.card = 1 := by
      have h₁ := card_le_univ u
      have h₂ := card_pos.mpr hu
      simp only [Fintype.card_fin] at h₁
      omega
    have hmem : (0 : Fin 1) ∈ u := by
      obtain ⟨i,hi⟩ := hu
      simpa only [Subsingleton.elim i 0] using hi
    let f : Fin s → Sym2 (Fin 1 ⊕ Fin s) := fun j => s(Sum.inl 0,Sum.inr j)
    have hf : Function.Injective f := by
      intro i j hij
      simpa only [f,Sym2.eq_iff,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
        false_and,and_self,and_true,true_and,or_false] using hij
    have hsub : univ.image f ⊆ RootedUnionDensity.incident (KSTUpper.graph 1 s) u := by
      intro e he
      obtain ⟨j,_,rfl⟩ := mem_image.mp he
      simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset]
      exact ⟨trivial,0,hmem,Sym2.mem_mk_left _ _⟩
    have hh := card_le_card hsub
    rw [card_image_of_injective _ hf,card_univ,Fintype.card_fin] at hh
    simpa only [hu1,mul_one,one_mul] using hh
  · rw [not_nonempty_iff_eq_empty.mp hu]
    simp

/-- A rooted power of a star is a complete bipartite graph. -/
def starPowerIso (s t : ℕ) :
    RootedPowers.graph (KSTUpper.graph 1 s) t ≃g KSTUpper.graph s t where
  toFun := Sum.elim (fun z => Sum.inr z.1) Sum.inl
  invFun := Sum.elim Sum.inr (fun i => Sum.inl (i,0))
  left_inv := by
    intro v
    cases v with
    | inl x => exact congrArg Sum.inl (Prod.ext rfl (Subsingleton.elim _ _))
    | inr y => rfl
  right_inv := by intro v; cases v <;> rfl
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;> simp [RootedPowers.graph,KSTUpper.graph]


end RationalKST

end -- RationalKST

section -- RootedUpperModels

/- Rooted upper-bound models; the lower bound is supplied by generic polynomial graphs. -/
open Finset SimpleGraph
namespace RootedUpperModels

structure Model (a b : ℕ) where
  A : Type
  R : Type
  [fintypeA : Fintype A]
  [fintypeR : Fintype R]
  [nonemptyA : Nonempty A]
  G : SimpleGraph (A ⊕ R)
  color : G.Coloring (Fin 2)
  balance : ∀ s : Finset A, b*s.card ≤ a*(RootedUnionDensity.incident G s).card
  connected : ∀ t : ℕ, 0 < t → (RootedPowers.graph G t).Connected
  upper : ∀ t : ℕ, 0 < t →
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (extremalNumber n (RootedPowers.graph G t) : ℝ))
      (fun n : ℕ => (n : ℝ)^(2-(a : ℝ)/b))

noncomputable def initial : Model 1 1 where
  A := Fin 1
  R := Fin 1
  G := KSTUpper.graph 1 1
  color := Classical.choice (KSTUpper.graph_bipartite 1 1)
  balance := RationalKST.star_balance 1
  connected t ht := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨Sum.inr 0,?_⟩
    intro v
    cases v with
    | inl a => exact (show (RootedPowers.graph (KSTUpper.graph 1 1) t).Adj
        (Sum.inr 0) (Sum.inl a) from trivial).reachable
    | inr r =>
      have hr : r = 0 := Subsingleton.elim _ _
      subst r
      exact Reachable.refl _
  upper t ht := by
    simpa only [Nat.cast_one,one_div,inv_one,
      extremalNumber_congr_right (RationalKST.starPowerIso 1 t)] using
        KSTUpper.upper_isBigO 1 t (by omega)

noncomputable def suspension {a b : ℕ} (M : Model a b) (ha : 0 < a) (hab : a ≤ b) : Model a (b+a) := by
  letI := M.fintypeA
  letI := M.fintypeR
  letI := M.nonemptyA
  exact {
    A := M.A
    R := Fin 2 ⊕ M.R
    G := RootedSuspension.graph M.color
    color := RootedSuspension.color M.color
    balance := RootedSuspension.balanced M.color a b M.balance
    connected := fun t _ => RootedSuspension.power_connected M.color t
    upper := fun t ht => by
      simpa only [Nat.cast_add] using RootedSuspension.upper_transform M.color a b t ha hab
        (M.connected t ht) (M.upper t ht) }

/-- A model gives an actual single forbidden graph with the corresponding two-sided exponent. -/
lemma realization {a b : ℕ} (M : Model a b) (ha : 0 < a) (hab : a ≤ b) :
    ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
      Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (extremalNumber n G : ℝ))
        (fun n : ℕ => (n : ℝ)^((2-(a : ℚ)/b : ℚ) : ℝ)) := by
  letI := M.fintypeA
  letI := M.fintypeR
  letI := M.nonemptyA
  obtain ⟨t,ht,hlo⟩ := UnconditionalRootedLower.exists_power_lower M.G a b ha hab M.balance
  apply RationalKST.finite_realization (RootedPowers.graph M.G t) (2-(a : ℚ)/b)
    (RootedPowers.graph_bipartite M.G ⟨M.color⟩ t)
  constructor
  · simpa only [Rat.cast_sub,Rat.cast_ofNat,Rat.cast_div,Rat.cast_natCast] using M.upper t ht
  · simpa only [Rat.cast_sub,Rat.cast_ofNat,Rat.cast_div,Rat.cast_natCast] using hlo

end RootedUpperModels

end -- RootedUpperModels

section -- RootedHubPathBasic

/- The arbitrary-length rooted hub replacement before promotion of root-edge interiors. -/
open Finset SimpleGraph
namespace RootedHubPathBasic
set_option maxHeartbeats 2500000
universe u
variable {A R : Type u} (F : SimpleGraph (A ⊕ R)) (k : ℕ)
abbrev E := GraphSubdivision.Edge F
abbrev Vertex := (A ⊕ (E F × Fin k)) ⊕ (R ⊕ Fin 2)

def move : Vertex F k ≃ HubPathSubdivision.Vertex (F := F) k where
  toFun := Sum.elim (Sum.elim (fun a => Sum.inr (Sum.inl (Sum.inl a))) (fun e => Sum.inr (Sum.inr e)))
    (Sum.elim (fun r => Sum.inr (Sum.inl (Sum.inr r))) Sum.inl)
  invFun := Sum.elim (fun i => Sum.inr (Sum.inr i))
    (Sum.elim (Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun r => Sum.inr (Sum.inl r)))
      (fun e => Sum.inl (Sum.inr e)))
  left_inv := by intro v; rcases v with (a | e) | (r | i) <;> rfl
  right_inv := by intro v; rcases v with i | (a | r) | e <;> rfl

noncomputable def graph (c : F.Coloring (Fin 2)) : SimpleGraph (Vertex F k) :=
  (HubPathSubdivision.graph c k).comap (move F k)

noncomputable def color (c : F.Coloring (Fin 2)) : (graph F k c).Coloring (Fin 2) :=
  Coloring.mk (fun v => HubPathSubdivision.color c k (move F k v))
    (fun h => (HubPathSubdivision.color c k).valid h)

def coreMap : HubPathSubdivision.CoreVertex (F := F) k ↪ Vertex F k :=
  Function.Embedding.inr.trans (move F k).symm.toEmbedding

lemma move_coreMap (v : HubPathSubdivision.CoreVertex (F := F) k) :
    move F k (coreMap F k v)=Sum.inr v := by
  rcases v with (a | r) | e <;> rfl

def hub : Fin 2 ↪ Vertex F k := ⟨fun i => Sum.inr (Sum.inr i),Sum.inr_injective.comp Sum.inr_injective⟩

lemma spoke_adj (c : F.Coloring (Fin 2)) (a : A) :
    (graph F k c).Adj (Sum.inl (Sum.inl a)) (hub F k (c (Sum.inl a))) := rfl

noncomputable def core (c : F.Coloring (Fin 2)) (p : E F × Fin (k+1)) : Sym2 (Vertex F k) :=
  Sym2.map (coreMap F k) (HubPathSubdivision.coreEdge c k p.1 p.2)

lemma core_injective (c : F.Coloring (Fin 2)) : Function.Injective (core F k c) :=
  (Sym2.map.injective (coreMap F k).injective).comp (HubPathSubdivision.coreEdge_injective c k)

lemma core_adj (c : F.Coloring (Fin 2)) (p : E F × Fin (k+1)) : core F k c p∈(graph F k c).edgeSet := by
  simpa only [core,HubPathSubdivision.coreEdge,Sym2.map_pair_eq,mem_edgeSet,graph,comap_adj,move_coreMap]
    using HubPathSubdivision.coreEdge_adj c k p.1 p.2

section Balance
noncomputable local instance : DecidableEq (A ⊕ R) := Classical.decEq _
variable [Fintype A] [Fintype R] [Fintype (E F)]

lemma selected_core (c : F.Coloring (Fin 2)) (S : Finset (A ⊕ (E F × Fin k)))
    (p : E F × Fin (k+1))
    (hp : p∈HubPathIncidences.incidences c k (S.toLeft.image Sum.inl) S.toRight) :
    ∃ a∈S, Sum.inl a∈core F k c p := by
  classical
  obtain ⟨v,hv,he⟩ := HubPathIncidences.selected c k (S.toLeft.image Sum.inl) S.toRight p hp
  cases v with
  | inl w =>
    obtain ⟨a,ha,rfl⟩ := mem_image.mp (inl_mem_disjSum.mp hv)
    refine ⟨Sum.inl a,mem_toLeft.mp ha,?_⟩
    exact Sym2.mem_map.mpr ⟨Sum.inl (Sum.inl a),he,rfl⟩
  | inr e =>
    refine ⟨Sum.inr e,mem_toRight.mp (inr_mem_disjSum.mp hv),?_⟩
    exact Sym2.mem_map.mpr ⟨Sum.inr e,he,rfl⟩

lemma hub_notMem_core (c : F.Coloring (Fin 2)) (p : E F × Fin (k+1)) (j : Fin 2) :
    hub F k j∉core F k c p := by
  intro h
  obtain ⟨v,hv,he⟩ := Sym2.mem_map.mp h
  have hh := congrArg (move F k) he
  rw [move_coreMap] at hh
  exact Sum.inr_ne_inl hh

lemma incident_gain (c : F.Coloring (Fin 2)) (S : Finset (A ⊕ (E F × Fin k))) :
    (HubPathIncidences.incidences c k (S.toLeft.image Sum.inl) S.toRight).card+S.toLeft.card≤
      (RootedUnionDensity.incident (graph F k c) S).card := by
  classical
  let f (a : A) : Sym2 (Vertex F k) := s(Sum.inl (Sum.inl a),hub F k (c (Sum.inl a)))
  let I := (HubPathIncidences.incidences c k (S.toLeft.image Sum.inl) S.toRight).image (core F k c)
  let N := S.toLeft.image f
  have hI : I⊆RootedUnionDensity.incident (graph F k c) S := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := mem_image.mp he
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset]
    exact ⟨core_adj F k c p,selected_core F k c S p hp⟩
  have hN : N⊆RootedUnionDensity.incident (graph F k c) S := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset]
    exact ⟨spoke_adj F k c a,Sum.inl a,mem_toLeft.mp ha,Sym2.mem_mk_left _ _⟩
  have hdis : Disjoint I N := by
    apply Finset.disjoint_left.mpr
    intro e he hn
    obtain ⟨a,_,rfl⟩ := mem_image.mp hn
    obtain ⟨p,_,he⟩ := mem_image.mp he
    apply hub_notMem_core F k c p (c (Sum.inl a))
    rw [he]
    exact Sym2.mem_mk_right _ _
  have hf : Function.Injective f := by
    intro a b he
    rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
    · exact Sum.inl.inj (Sum.inl.inj h)
    · exact (Sum.inl_ne_inr h).elim
  have hcard : (I∪N).card=(HubPathIncidences.incidences c k (S.toLeft.image Sum.inl) S.toRight).card+S.toLeft.card := by
    rw [card_union_of_disjoint hdis]
    simp only [I,N,card_image_of_injective _ (core_injective F k c),card_image_of_injective _ hf]
  rw [← hcard]
  exact card_le_card (union_subset hI hN)

lemma balanced (c : F.Coloring (Fin 2)) (a b : ℕ)
    (hbalance : ∀ s : Finset A, b*s.card≤a*(RootedUnionDensity.incident F s).card)
    (S : Finset (A ⊕ (E F × Fin k))) :
    (a+(k+1)*b)*S.card≤(a+k*b)*(RootedUnionDensity.incident (graph F k c) S).card := by
  classical
  have h1 := HubPathIncidences.old_plus_midpoints c k (S.toLeft.image Sum.inl) S.toRight
  have h2 := HubPathIncidences.midpoint_ratio c k (S.toLeft.image Sum.inl) S.toRight
  have he : (GraphSubdivision.incidentEdges F (S.toLeft.image Sum.inl)).card =
      (RootedUnionDensity.incident F S.toLeft).card := by
    convert GraphSubdivision.old_incident_count F S.toLeft using 1
    congr 1
    ext e
    simp only [GraphSubdivision.incidentEdges,mem_filter,mem_image]
  rw [he] at h1
  rw [← S.card_toLeft_add_card_toRight]
  exact HubPathBalanceArithmetic.balance a b k _ _ _ _ _ (hbalance S.toLeft) h1 h2 (incident_gain F k c S)

end Balance
end RootedHubPathBasic

end -- RootedHubPathBasic

section -- RootPromotion

/- Relabeling rooted graphs while promoting some internal vertices to roots. -/
open Finset SimpleGraph
namespace RootPromotion
universe u v
variable {A R : Type u} {B S : Type v}
  [Fintype A] [Fintype R] [Fintype B] [Fintype S]

lemma incident_card (G : SimpleGraph (A ⊕ R)) (e : (B ⊕ S) ≃ (A ⊕ R))
    (f : B ↪ A) (hf : ∀ b, e (Sum.inl b) = Sum.inl (f b)) (U : Finset B) :
    (RootedUnionDensity.incident (G.comap e) U).card =
      (RootedUnionDensity.incident G (U.map f)).card := by
  classical
  apply card_bij (fun d _ => Sym2.map e d)
  · intro d hd
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset] at hd ⊢
    obtain ⟨hd,b,hb,hbd⟩ := hd
    refine ⟨?_,f b,mem_map.mpr ⟨b,hb,rfl⟩,?_⟩
    · induction d using Sym2.inductionOn with
      | _ x y => exact hd
    · rw [← hf]
      exact Sym2.mem_map.mpr ⟨Sum.inl b,hbd,rfl⟩
  · intro d hd c hc he
    exact Sym2.map.injective e.injective he
  · intro d hd
    simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset] at hd
    obtain ⟨hd,a,ha,had⟩ := hd
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ha
    refine ⟨Sym2.map e.symm d,?_,?_⟩
    · simp only [RootedUnionDensity.incident,mem_filter,mem_edgeFinset]
      refine ⟨?_,b,hb,?_⟩
      · induction d using Sym2.inductionOn with
        | _ x y => simpa [comap_adj] using hd
      · apply Sym2.mem_map.mpr
        refine ⟨Sum.inl (f b),had,?_⟩
        rw [← hf,Equiv.symm_apply_apply]
    · induction d using Sym2.inductionOn with
      | _ x y => simp

lemma balanced (G : SimpleGraph (A ⊕ R)) (e : (B ⊕ S) ≃ (A ⊕ R))
    (f : B ↪ A) (hf : ∀ b, e (Sum.inl b) = Sum.inl (f b))
    (a b : ℕ) (hbalance : ∀ U : Finset A,
      b*U.card ≤ a*(RootedUnionDensity.incident G U).card) (U : Finset B) :
    b*U.card ≤ a*(RootedUnionDensity.incident (G.comap e) U).card := by
  classical
  rw [incident_card G e f hf]
  simpa only [card_map] using hbalance (U.map f)

end RootPromotion

end -- RootPromotion

section -- RootedSubdivision

/- Rooted subdivision with midpoint roots on root-to-root edges. -/
open Finset SimpleGraph
namespace RootedSubdivision
universe u
variable {A R : Type u} (F : SimpleGraph (A ⊕ R))

abbrev E := GraphSubdivision.Edge F

def internalEdge : Set (E F) := {e | ∃ a, Sum.inl a ∈ e.val}


lemma adj_layer (t : ℕ) (ht : 0 < t) {x y : RootedPowers.Vertex A R t}
    (hxy : (RootedPowers.graph F t).Adj x y) :
    ∃ i : Fin t, ∃ u v : A ⊕ R, F.Adj u v ∧
      RootedPowers.layer F t i u = x ∧ RootedPowers.layer F t i v = y := by
  cases x with
  | inl x => cases y with
    | inl y =>
      obtain ⟨he,hadj⟩ := hxy
      refine ⟨x.1,Sum.inl x.2,Sum.inl y.2,hadj,rfl,?_⟩
      exact congrArg Sum.inl (Prod.ext he rfl)
    | inr y => exact ⟨x.1,Sum.inl x.2,Sum.inr y,hxy,rfl,rfl⟩
  | inr x => cases y with
    | inl y => exact ⟨y.1,Sum.inr x,Sum.inl y.2,hxy,rfl,rfl⟩
    | inr y => exact ⟨⟨0,ht⟩,Sum.inr x,Sum.inr y,hxy,rfl,rfl⟩


end RootedSubdivision

end -- RootedSubdivision

section -- SubdivisionPowers

/- Subdivision commutes with rooted powers when root-edge midpoints remain roots. -/
open SimpleGraph
namespace SubdivisionPowers
set_option maxHeartbeats 1000000
universe u
variable {A R : Type u} (F : SimpleGraph (A ⊕ R))

abbrev E := RootedSubdivision.E F
abbrev I := RootedSubdivision.internalEdge F
abbrev J := (RootedSubdivision.internalEdge F)ᶜ

def forget (t : ℕ) : RootedPowers.Vertex A R t → A ⊕ R := Sum.map Prod.snd id

def edge (t : ℕ) (i : Fin t) : E F ↪ GraphSubdivision.Edge (RootedPowers.graph F t) :=
  (RootedPowers.layer F t i).mapEdgeSet

lemma edge_val (t : ℕ) (i : Fin t) (e : E F) :
    (edge F t i e).val = Sym2.map (RootedPowers.layer F t i) e.val := rfl

lemma forget_edge (t : ℕ) (i : Fin t) (e : E F) :
    Sym2.map (forget t) (edge F t i e).val = e.val := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ x y => cases x <;> cases y <;> rfl

lemma edge_inl (t : ℕ) (i j : Fin t) (a : A) (e : E F) :
    Sum.inl (i,a) ∈ (edge F t j e).val ↔ i = j ∧ Sum.inl a ∈ e.val := by
  rw [edge_val,Sym2.mem_map]
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | inl b =>
      have h : (j,b) = (i,a) := Sum.inl.inj he
      cases h
      exact ⟨rfl,hv⟩
    | inr r => exact (Sum.inr_ne_inl he).elim
  · rintro ⟨rfl,ha⟩
    exact ⟨Sum.inl a,ha,rfl⟩

lemma edge_inr (t : ℕ) (j : Fin t) (r : R) (e : E F) :
    Sum.inr r ∈ (edge F t j e).val ↔ Sum.inr r ∈ e.val := by
  rw [edge_val,Sym2.mem_map]
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | inl a => exact (Sum.inl_ne_inr he).elim
    | inr s => cases Sum.inr.inj he; exact hv
  · intro hr
    exact ⟨Sum.inr r,hr,rfl⟩

lemma edge_eq_iff (t : ℕ) (i j : Fin t) (e f : E F) :
    edge F t i e = edge F t j f ↔ e = f ∧ (i = j ∨ e ∉ I F) := by
  constructor
  · intro h
    have hef : e = f := by
      apply Subtype.ext
      have hh := congrArg (fun d => Sym2.map (forget t) d.val) h
      simpa only [forget_edge] using hh
    subst f
    refine ⟨rfl,?_⟩
    by_cases he : e ∈ I F
    · left
      obtain ⟨a,ha⟩ := he
      have hh : Sum.inl (i,a) ∈ (edge F t i e).val := (edge_inl F t i i a e).mpr ⟨rfl,ha⟩
      rw [h] at hh
      exact ((edge_inl F t i j a e).mp hh).1
    · exact Or.inr he
  · rintro ⟨rfl,hij | he⟩
    · subst j; rfl
    · apply Subtype.ext
      rcases e with ⟨e,heG⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
        cases x with
        | inl a => exact (he ⟨a,Sym2.mem_mk_left _ _⟩).elim
        | inr r => cases y with
          | inl a => exact (he ⟨a,Sym2.mem_mk_right _ _⟩).elim
          | inr s => rfl

def edgeMap (t : ℕ) (j : Fin t) : (Fin t × I F) ⊕ J F →
    GraphSubdivision.Edge (RootedPowers.graph F t) :=
  Sum.elim (fun p => edge F t p.1 p.2.val) (fun e => edge F t j e.val)

lemma edgeMap_injective (t : ℕ) (j : Fin t) : Function.Injective (edgeMap F t j) := by
  intro x y h
  cases x with
  | inl x => cases y with
    | inl y =>
      obtain ⟨he,hi⟩ := (edge_eq_iff F t x.1 y.1 x.2.val y.2.val).mp h
      have hij := hi.resolve_right (not_not.mpr x.2.property)
      exact congrArg Sum.inl (Prod.ext hij (Subtype.ext he))
    | inr y =>
      have he := ((edge_eq_iff F t x.1 j x.2.val y.val).mp h).1
      exact (y.property (he ▸ x.2.property)).elim
  | inr x => cases y with
    | inl y =>
      have he := ((edge_eq_iff F t j y.1 x.val y.2.val).mp h).1
      exact (x.property (he.symm ▸ y.2.property)).elim
    | inr y =>
      exact congrArg Sum.inr (Subtype.ext ((edge_eq_iff F t j j x.val y.val).mp h).1)

lemma edgeMap_surjective (t : ℕ) (j : Fin t) : Function.Surjective (edgeMap F t j) := by
  classical
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨i,u,v,huv,rfl,rfl⟩ := RootedSubdivision.adj_layer F t (Nat.zero_lt_of_lt j.isLt) he
    let e : E F := ⟨s(u,v),huv⟩
    have hh : edge F t i e = ⟨s(RootedPowers.layer F t i u,RootedPowers.layer F t i v),he⟩ := rfl
    by_cases hi : e ∈ I F
    · exact ⟨Sum.inl (i,⟨e,hi⟩),hh⟩
    · refine ⟨Sum.inr ⟨e,hi⟩,?_⟩
      exact ((edge_eq_iff F t j i e e).mpr ⟨rfl,Or.inr hi⟩).trans hh

noncomputable def edgeEquiv (t : ℕ) (j : Fin t) : (Fin t × I F) ⊕ J F ≃
    GraphSubdivision.Edge (RootedPowers.graph F t) :=
  Equiv.ofBijective (edgeMap F t j) ⟨edgeMap_injective F t j,edgeMap_surjective F t j⟩


end SubdivisionPowers

end -- SubdivisionPowers

section -- ChainCounting

/- Uniform counts for fixed-length vertex sequences, including coordinate fibers. -/
open Finset SimpleGraph
namespace ChainCounting
set_option maxHeartbeats 1000000
universe u
variable {V : Type u} (G : SimpleGraph V)

/-- A walk recorded by its ordered vertices. -/
def IsChain {n : ℕ} (p : Fin (n+1) → V) : Prop :=
  ∀ i : Fin n, G.Adj (p i.castSucc) (p i.succ)

instance {n : ℕ} [DecidableRel G.Adj] (p : Fin (n+1) → V) : Decidable (IsChain G p) :=
  inferInstanceAs (Decidable (∀ i : Fin n, G.Adj (p i.castSucc) (p i.succ)))

abbrev Chain (n : ℕ) := {p : Fin (n+1) → V // IsChain G p}
abbrev From (x : V) (n : ℕ) := {p : Chain G n // p.val 0 = x}
abbrev PathFrom (x : V) (n : ℕ) := {p : From G x n // Function.Injective p.val.val}

/-- A consecutive segment, retaining the walk condition. -/
def segment {n : ℕ} (p : Chain G n) (a k : ℕ) (h : a+k ≤ n) : Chain G k :=
  ⟨fun i => p.val ⟨a+i.val,by omega⟩, by
    intro i
    exact p.property ⟨a+i.val,by omega⟩⟩

@[simp] lemma segment_apply {n : ℕ} (p : Chain G n) (a k : ℕ) (h : a+k ≤ n)
    (i : Fin (k+1)) : (segment G p a k h).val i = p.val ⟨a+i.val,by omega⟩ := rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma from_zero (x : V) : Fintype.card (From G x 0) = 1 := by
  classical
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨⟨fun _ => x,fun i => Fin.elim0 i⟩,rfl⟩,?_⟩
  intro p
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  simpa [hi] using p.property

lemma from_le (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (x : V) :
    Fintype.card (From G x n) ≤ D^n := by
  classical
  induction n generalizing x with
  | zero => simp [from_zero]
  | succ n ih =>
    let f : From G x (n+1) → (Σ y : G.neighborSet x, From G y.val n) := fun p =>
      ⟨⟨p.val.val 1,by
        have hh := p.val.property (0 : Fin (n+1))
        simpa [Fin.castSucc_zero, p.property, Fin.succ, SimpleGraph.mem_neighborSet] using hh⟩,
        ⟨segment G p.val 1 n (by omega),rfl⟩⟩
    have hf : Function.Injective f := by
      intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact p.property.trans q.property.symm
      · have hh := congrArg (fun z : Σ y : G.neighborSet x, From G y.val n => z.2.val.val j) hpq
        simpa only [f,segment_apply,Nat.add_comm,Fin.succ] using hh
    calc
      _ ≤ Fintype.card (Σ y : G.neighborSet x, From G y.val n) :=
        Fintype.card_le_of_injective f hf
      _ = ∑ y : G.neighborSet x, Fintype.card (From G y.val n) := Fintype.card_sigma
      _ ≤ ∑ _y : G.neighborSet x, D^n := sum_le_sum (fun y _ => ih y.val)
      _ = G.degree x * D^n := by simp [G.card_neighborSet_eq_degree]
      _ ≤ D * D^n := Nat.mul_le_mul_right _ (hD x)
      _ = D^(n+1) := by rw [pow_succ]; ring


/-- Fixing any noninitial coordinate saves one neighbor choice. -/
lemma coordinate_le (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (x v : V)
    (i : Fin n) :
    Fintype.card {p : From G x n // p.val.val i.succ = v} ≤ D^(n-1) := by
  classical
  let f : {p : From G x n // p.val.val i.succ = v} →
      From G x i.val × From G v (n-(i.val+1)) := fun p =>
    (⟨segment G p.val.val 0 i.val (by omega),by simpa using p.val.property⟩,
     ⟨segment G p.val.val (i.val+1) (n-(i.val+1)) (by omega),by simpa [Fin.succ] using p.property⟩)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext j
    by_cases hj : j.val ≤ i.val
    · have hh := congrArg (fun z : From G x i.val × From G v (n-(i.val+1)) =>
        z.1.val.val ⟨j.val,by omega⟩) hpq
      simpa only [f,segment_apply,Nat.zero_add] using hh
    · have hh := congrArg (fun z : From G x i.val × From G v (n-(i.val+1)) =>
        z.2.val.val ⟨j.val-(i.val+1),by omega⟩) hpq
      have he : i.val+1+(j.val-(i.val+1)) = j.val := by omega
      simpa only [f,segment_apply,he] using hh
  calc
    _ ≤ Fintype.card (From G x i.val × From G v (n-(i.val+1))) :=
      Fintype.card_le_of_injective f hf
    _ = Fintype.card (From G x i.val) * Fintype.card (From G v (n-(i.val+1))) := Fintype.card_prod _ _
    _ ≤ D^i.val * D^(n-(i.val+1)) := Nat.mul_le_mul (from_le G D hD _ _) (from_le G D hD _ _)
    _ = D^(n-1) := by rw [← pow_add]; congr 1; omega


end ChainCounting

end -- ChainCounting

section -- HubPathCopies

/- Construct copies of arbitrary-length hub replacements from disjoint path data. -/
open SimpleGraph ChainCounting
namespace HubPathCopies
set_option maxHeartbeats 1500000
universe u v
variable {W : Type u} {F : SimpleGraph W} (c : F.Coloring (Fin 2))
variable {V : Type v} (H : SimpleGraph V) (k : ℕ)
abbrev E := GraphSubdivision.Edge F

noncomputable def copyOfData (z : Fin 2 → V) (f : W → V) (m : E (F := F) × Fin k → V)
    (hz : Function.Injective z) (hf : Function.Injective f) (hm : Function.Injective m)
    (hzf : ∀ i w, z i≠f w) (hzm : ∀ i e, z i≠m e) (hfm : ∀ w e, f w≠m e)
    (hpath : ∀ e (i : Fin (k+1)), H.Adj (Sum.elim f m (HubPathSubdivision.point c k e i.castSucc))
      (Sum.elim f m (HubPathSubdivision.point c k e i.succ)))
    (hhub : ∀ i w, c w=i → H.Adj (z i) (f w)) : Copy (HubPathSubdivision.graph c k) H where
  toHom := {
    toFun := Sum.elim z (Sum.elim f m)
    map_rel' := by
      intro u v h
      rcases u with i | a <;> rcases v with j | b
      · exact h.elim
      · cases b with
        | inl w => exact hhub i w h
        | inr e => exact h.elim
      · cases a with
        | inl w => exact (hhub j w h).symm
        | inr e => exact h.elim
      · obtain ⟨e,i,h⟩ := h
        rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hpath e i
        · exact (hpath e i).symm }
  injective' := hz.sumElim (hf.sumElim hm hfm) (by
    intro i a
    cases a with
    | inl w => exact hzf i w
    | inr e => exact hzm i e)

lemma point_eval (f : W → V) (p : E (F := F) → Chain H (k+1))
    (hstart : ∀ e, (p e).val 0=f (ColoredEdges.left c e))
    (hend : ∀ e, (p e).val (Fin.last (k+1))=f (ColoredEdges.right c e))
    (e : E (F := F)) (i : Fin (k+2)) :
    Sum.elim f (fun q : E (F := F) × Fin k => (p q.1).val q.2.succ.castSucc)
      (HubPathSubdivision.point c k e i)=(p e).val i := by
  dsimp only [HubPathSubdivision.point]
  split_ifs with h0 hl
  · have hi : i=0 := Fin.ext h0
    simpa only [hi,Sum.elim_inl] using (hstart e).symm
  · have hi : i=Fin.last (k+1) := Fin.ext hl
    simpa only [hi,Sum.elim_inl] using (hend e).symm
  · simp only [Sum.elim_inr]
    apply congrArg (p e).val
    apply Fin.ext
    simp only [Fin.val_castSucc,Fin.val_succ]
    omega

noncomputable def copyOfChains (z : Fin 2 → V) (f : W → V) (p : E (F := F) → Chain H (k+1))
    (hz : Function.Injective z) (hf : Function.Injective f)
    (hm : Function.Injective (fun e : E (F := F) × Fin k => (p e.1).val e.2.succ.castSucc))
    (hzf : ∀ i w, z i≠f w)
    (hzm : ∀ i e (j : Fin k), z i≠(p e).val j.succ.castSucc)
    (hfm : ∀ w e (j : Fin k), f w≠(p e).val j.succ.castSucc)
    (hstart : ∀ e, (p e).val 0=f (ColoredEdges.left c e))
    (hend : ∀ e, (p e).val (Fin.last (k+1))=f (ColoredEdges.right c e))
    (hhub : ∀ i w, c w=i → H.Adj (z i) (f w)) : Copy (HubPathSubdivision.graph c k) H :=
  copyOfData c H k z f (fun e => (p e.1).val e.2.succ.castSucc) hz hf hm hzf
    (fun i e => hzm i e.1 e.2) (fun w e => hfm w e.1 e.2) (by
      intro e i
      rw [point_eval c H k f p hstart hend,point_eval c H k f p hstart hend]
      exact (p e).property i) hhub

end HubPathCopies

end -- HubPathCopies


section -- ThreeHubSubdivision

/- Replace every old edge by a three-edge path and attach the two old-color hubs. -/
open Finset SimpleGraph
namespace ThreeHubSubdivision
set_option maxHeartbeats 2000000
universe u v
variable {W : Type u} {V : Type v} {F : SimpleGraph W} (c : F.Coloring (Fin 2))
abbrev Edge := GraphSubdivision.Edge F

noncomputable def endpoint (e : Edge (F := F)) (i : Fin 2) : W :=
  if i=0 then ColoredEdges.left c e else ColoredEdges.right c e

lemma endpoint_color (e : Edge (F := F)) (i : Fin 2) : c (endpoint c e i)=i := by
  fin_cases i <;> simp [endpoint,ColoredEdges.left_color,ColoredEdges.right_color]


variable (H : SimpleGraph V)


end ThreeHubSubdivision

end -- ThreeHubSubdivision

section -- ThreeHubCopyTransport

/- Transport copies through the three-edge, two-hub operation. -/
open SimpleGraph
namespace ThreeHubCopyTransport
set_option maxHeartbeats 2000000
universe u v
variable {W : Type u} {V : Type v} {F : SimpleGraph W} {J : SimpleGraph V}

lemma endpoint_mem (c : F.Coloring (Fin 2)) (e : GraphSubdivision.Edge F) (i : Fin 2) :
    ThreeHubSubdivision.endpoint c e i∈e.val := by
  apply (ColoredEdges.mem_iff c e _).mpr
  fin_cases i <;> simp [ThreeHubSubdivision.endpoint]

lemma endpoint_unique (c : F.Coloring (Fin 2)) (e : GraphSubdivision.Edge F) (i : Fin 2)
    {w : W} (hw : w∈e.val) (hc : c w=i) : w=ThreeHubSubdivision.endpoint c e i := by
  fin_cases i
  · exact ColoredEdges.left_unique c e hw hc
  · exact ColoredEdges.right_unique c e hw hc

lemma endpoint_map (c : F.Coloring (Fin 2)) (d : J.Coloring (Fin 2)) (f : Copy F J)
    (e : Fin 2 ≃ Fin 2) (he : ∀ w, e (c w)=d (f w)) (a : GraphSubdivision.Edge F) (i : Fin 2) :
    f (ThreeHubSubdivision.endpoint c a i)=ThreeHubSubdivision.endpoint d (f.mapEdgeSet a) (e i) := by
  apply endpoint_unique d (f.mapEdgeSet a) (e i)
  · change f (ThreeHubSubdivision.endpoint c a i)∈a.val.map f
    exact Sym2.mem_map.mpr ⟨ThreeHubSubdivision.endpoint c a i,endpoint_mem c a i,rfl⟩
  · rw [← he,ThreeHubSubdivision.endpoint_color]


end ThreeHubCopyTransport

end -- ThreeHubCopyTransport

section -- HubPathCopyTransport

/- Transport graph copies through arbitrary-length hub replacement, allowing a color swap. -/
open SimpleGraph
namespace HubPathCopyTransport
set_option maxHeartbeats 2500000
universe u v
variable {W : Type u} {V : Type v} {F : SimpleGraph W} {J : SimpleGraph V}

noncomputable def index (e : Fin 2 ≃ Fin 2) {n : ℕ} (i : Fin n) : Fin n :=
  if e 0=0 then i else i.rev

lemma index_injective (e : Fin 2 ≃ Fin 2) (n : ℕ) : Function.Injective (index e (n := n)) := by
  intro i j h
  dsimp only [index] at h
  split_ifs at h
  · exact h
  · exact Fin.rev_injective h

lemma rev_mid (k : ℕ) (j : Fin k) : (j.succ.castSucc : Fin (k+2)).rev=j.rev.succ.castSucc := by
  apply Fin.ext
  simp only [Fin.val_rev,Fin.val_castSucc,Fin.val_succ]
  have := j.isLt
  omega

lemma point_map (c : F.Coloring (Fin 2)) (d : J.Coloring (Fin 2)) (f : Copy F J)
    (e : Fin 2 ≃ Fin 2) (he : ∀ w, e (c w)=d (f w)) (k : ℕ)
    (a : GraphSubdivision.Edge F) (i : Fin (k+2)) :
    Sum.map f (Prod.map f.mapEdgeSet (index e)) (HubPathSubdivision.point c k a i)=
      HubPathSubdivision.point d k (f.mapEdgeSet a) (index e i) := by
  have h0 := ThreeHubCopyTransport.endpoint_map c d f e he a 0
  have h1 := ThreeHubCopyTransport.endpoint_map c d f e he a 1
  simp [ThreeHubSubdivision.endpoint] at h0 h1
  by_cases hei : e 0=0
  · have he1 : e 1=1 := by
      have hh := e.injective.ne (show (0 : Fin 2)≠1 by decide)
      rw [hei] at hh
      omega
    simp [hei] at h0
    simp [he1] at h1
    simp only [index,if_pos hei]
    dsimp only [HubPathSubdivision.point]
    split_ifs <;> simp [h0,h1,index,hei]
  · have he0 : e 0=1 := by omega
    have he1 : e 1=0 := by
      have hh := e.injective.ne (show (0 : Fin 2)≠1 by decide)
      rw [he0] at hh
      omega
    simp [he0] at h0
    simp [he1] at h1
    simp only [index,if_neg hei]
    by_cases hi0 : i.val=0
    · have hi : i=0 := Fin.ext hi0
      subst i
      simp only [HubPathSubdivision.point_zero,Sum.map_inl,h0,Fin.rev_zero,HubPathSubdivision.point_last]
    · by_cases hil : i.val=k+1
      · have hi : i=Fin.last (k+1) := Fin.ext hil
        subst i
        simp only [HubPathSubdivision.point_last,Sum.map_inl,h1,Fin.rev_last,HubPathSubdivision.point_zero]
      · let j : Fin k := ⟨i.val-1,by have := i.isLt; omega⟩
        have hi : i=j.succ.castSucc := by apply Fin.ext; change i.val=i.val-1+1; omega
        rw [hi,HubPathSubdivision.point_mid,rev_mid,HubPathSubdivision.point_mid]
        simp [index,hei]

noncomputable def mapCopy (c : F.Coloring (Fin 2)) (d : J.Coloring (Fin 2)) (f : Copy F J)
    (e : Fin 2 ≃ Fin 2) (he : ∀ w, e (c w)=d (f w)) (k : ℕ) :
    Copy (HubPathSubdivision.graph c k) (HubPathSubdivision.graph d k) where
  toHom := {
    toFun := Sum.map e (Sum.map f (Prod.map f.mapEdgeSet (index e)))
    map_rel' := by
      intro u v h
      rcases u with i | a <;> rcases v with j | b
      · exact h.elim
      · cases b with
        | inl w => change d (f w)=e i; exact (he w).symm.trans (congrArg e h)
        | inr a => exact h.elim
      · cases a with
        | inl w => change d (f w)=e j; exact (he w).symm.trans (congrArg e h)
        | inr a => exact h.elim
      · obtain ⟨a,i,h⟩ := h
        have hp : (HubPathSubdivision.graph d k).Adj
            (Sum.inr (Sum.map f (Prod.map f.mapEdgeSet (index e)) (HubPathSubdivision.point c k a i.castSucc)))
            (Sum.inr (Sum.map f (Prod.map f.mapEdgeSet (index e)) (HubPathSubdivision.point c k a i.succ))) := by
          rw [point_map c d f e he,point_map c d f e he]
          dsimp only [index]
          split_ifs
          · exact HubPathSubdivision.coreEdge_adj d k (f.mapEdgeSet a) i
          · rw [Fin.rev_castSucc,Fin.rev_succ]
            exact (HubPathSubdivision.coreEdge_adj d k (f.mapEdgeSet a) i.rev).symm
        rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hp
        · exact hp.symm }
  injective' := Sum.map_injective.mpr ⟨e.injective,Sum.map_injective.mpr
    ⟨f.injective,fun p q h => Prod.ext
      (f.mapEdgeSet.injective (congrArg Prod.fst h))
      (index_injective e k (congrArg (fun z : GraphSubdivision.Edge J × Fin k => z.2) h))⟩⟩

lemma copy_of_copy (hF : F.Connected) (c : F.Coloring (Fin 2)) (d : J.Coloring (Fin 2))
    (f : Copy F J) (k : ℕ) : HubPathSubdivision.graph c k ⊑ HubPathSubdivision.graph d k := by
  let d' : F.Coloring (Fin 2) := Coloring.mk (fun w => d (f w)) (fun h => d.valid (f.toHom.map_rel' h))
  obtain ⟨e,he⟩ := SuspensionBounds.coloring_perm hF c d'
  exact ⟨mapCopy c d f e he k⟩

end HubPathCopyTransport

end -- HubPathCopyTransport

section -- HubPathLayers

/- Every edge of a hub replacement of a positive rooted power lies in a
hub replacement of one old layer. -/
open SimpleGraph
namespace HubPathLayers
set_option maxHeartbeats 3000000
universe u
variable {A R : Type u} (F : SimpleGraph (A ⊕ R)) (c : F.Coloring (Fin 2)) (k t : ℕ)

noncomputable def layer (i : Fin t) : Copy (HubPathSubdivision.graph c k)
    (HubPathSubdivision.graph (RootedSuspension.powerColor c t) k) :=
  HubPathCopyTransport.mapCopy c (RootedSuspension.powerColor c t) (RootedPowers.layer F t i)
    (Equiv.refl _) (fun w => by cases w <;> rfl) k


lemma layer_point (i : Fin t) (e : GraphSubdivision.Edge F) (l : Fin (k+2)) :
    layer F c k t i (Sum.inr (HubPathSubdivision.point c k e l))=
      Sum.inr (HubPathSubdivision.point (RootedSuspension.powerColor c t) k (SubdivisionPowers.edge F t i e) l) := by
  have hh := HubPathCopyTransport.point_map c (RootedSuspension.powerColor c t) (RootedPowers.layer F t i)
    (Equiv.refl _) (fun w => by cases w <;> rfl) k e l
  simpa [HubPathCopyTransport.index,Equiv.refl_apply,if_pos rfl,layer,HubPathCopyTransport.mapCopy,
    Sum.map_inr,SubdivisionPowers.edge] using congrArg (Sum.inr (α := Fin 2)) hh

lemma old_layer (j : Fin t) (w : RootedPowers.Vertex A R t) :
    ∃ i : Fin t, ∃ v : A ⊕ R, RootedPowers.layer F t i v=w := by
  cases w with
  | inl p => exact ⟨p.1,Sum.inl p.2,rfl⟩
  | inr r => exact ⟨j,Sum.inr r,rfl⟩

lemma edge_layer (j : Fin t) (e : GraphSubdivision.Edge (RootedPowers.graph F t)) :
    ∃ i : Fin t, ∃ d : GraphSubdivision.Edge F, SubdivisionPowers.edge F t i d=e := by
  obtain ⟨d,hd⟩ := SubdivisionPowers.edgeMap_surjective F t j e
  cases d with
  | inl d => exact ⟨d.1,d.2.val,hd⟩
  | inr d => exact ⟨j,d.val,hd⟩

lemma adj_layer (j : Fin t) {x y : HubPathSubdivision.Vertex (F := RootedPowers.graph F t) k}
    (h : (HubPathSubdivision.graph (RootedSuspension.powerColor c t) k).Adj x y) :
    ∃ i : Fin t, ∃ u v : HubPathSubdivision.Vertex (F := F) k,
      (HubPathSubdivision.graph c k).Adj u v ∧ layer F c k t i u=x ∧ layer F c k t i v=y := by
  rcases x with h₀ | w <;> rcases y with h₁ | z
  · exact h.elim
  · cases z with
    | inl z =>
      obtain ⟨i,v,rfl⟩ := old_layer F t j z
      refine ⟨i,Sum.inl h₀,Sum.inr (Sum.inl v),?_,rfl,rfl⟩
      change c v=h₀
      cases v <;> exact h
    | inr z => exact h.elim
  · cases w with
    | inl w =>
      obtain ⟨i,v,rfl⟩ := old_layer F t j w
      refine ⟨i,Sum.inr (Sum.inl v),Sum.inl h₁,?_,rfl,rfl⟩
      change c v=h₁
      cases v <;> exact h
    | inr w => exact h.elim
  · obtain ⟨e,l,he⟩ := h
    obtain ⟨i,d,rfl⟩ := edge_layer F t j e
    rcases Sym2.eq_iff.mp he with ⟨hw,hz⟩ | ⟨hw,hz⟩
    · refine ⟨i,Sum.inr (HubPathSubdivision.point c k d l.castSucc),
        Sum.inr (HubPathSubdivision.point c k d l.succ),HubPathSubdivision.coreEdge_adj c k d l,?_,?_⟩
      · exact (layer_point F c k t i d l.castSucc).trans (congrArg Sum.inr hw.symm)
      · exact (layer_point F c k t i d l.succ).trans (congrArg Sum.inr hz.symm)
    · refine ⟨i,Sum.inr (HubPathSubdivision.point c k d l.succ),
        Sum.inr (HubPathSubdivision.point c k d l.castSucc),(HubPathSubdivision.coreEdge_adj c k d l).symm,?_,?_⟩
      · exact (layer_point F c k t i d l.succ).trans (congrArg Sum.inr hw.symm)
      · exact (layer_point F c k t i d l.castSucc).trans (congrArg Sum.inr hz.symm)

end HubPathLayers

end -- HubPathLayers

section -- RootedHubPath

/- Promote all replacement-path interiors on root-root edges. -/
open Finset SimpleGraph
namespace RootedHubPath
set_option maxHeartbeats 3000000
universe u
variable {A R : Type u} (F : SimpleGraph (A ⊕ R)) (k : ℕ)
abbrev I := RootedSubdivision.internalEdge F
abbrev J := (RootedSubdivision.internalEdge F)ᶜ
abbrev Internal := A ⊕ (I F × Fin k)
abbrev Roots := Fin 2 ⊕ (R ⊕ (J F × Fin k))
abbrev Vertex := Internal F k ⊕ Roots F k

noncomputable def promote : Vertex F k ≃ RootedHubPathBasic.Vertex F k := by
  classical
  exact {
    toFun := Sum.elim
      (Sum.elim (fun a => Sum.inl (Sum.inl a)) (fun e => Sum.inl (Sum.inr (e.1.val,e.2))))
      (Sum.elim (fun i => Sum.inr (Sum.inr i))
        (Sum.elim (fun r => Sum.inr (Sum.inl r)) (fun e => Sum.inl (Sum.inr (e.1.val,e.2)))))
    invFun := Sum.elim
      (Sum.elim (fun a => Sum.inl (Sum.inl a))
        (fun e => if h : e.1∈I F then Sum.inl (Sum.inr (⟨e.1,h⟩,e.2))
          else Sum.inr (Sum.inr (Sum.inr (⟨e.1,h⟩,e.2)))))
      (Sum.elim (fun r => Sum.inr (Sum.inr (Sum.inl r))) (fun i => Sum.inr (Sum.inl i)))
    left_inv := by
      intro v
      rcases v with (a | ⟨e,k⟩) | i | (r | ⟨e,k⟩)
      · rfl
      · simp [e.property]
      · rfl
      · rfl
      · simp [(show e.val∉I F from e.property)]
    right_inv := by
      intro v
      rcases v with (a | ⟨e,k⟩) | (r | i)
      · rfl
      · dsimp; split_ifs <;> rfl
      · rfl
      · rfl }

noncomputable def graph (c : F.Coloring (Fin 2)) : SimpleGraph (Vertex F k) :=
  (RootedHubPathBasic.graph F k c).comap (promote F k)

noncomputable def color (c : F.Coloring (Fin 2)) : (graph F k c).Coloring (Fin 2) :=
  Coloring.mk (fun v => RootedHubPathBasic.color F k c (promote F k v))
    (fun h => (RootedHubPathBasic.color F k c).valid h)

def internalMap : Internal F k ↪ A ⊕ (RootedSubdivision.E F × Fin k) where
  toFun := Sum.map id (Prod.map Subtype.val id)
  inj' := by
    intro x y h
    cases x with
    | inl a => cases y <;> simp_all
    | inr e => cases y with
      | inl a => simp_all
      | inr f =>
        have h0 : (e.1.val,e.2)=(f.1.val,f.2) := Sum.inr.inj h
        have h1 : e.1.val=f.1.val := congrArg Prod.fst h0
        have h2 : e.2=f.2 := congrArg (fun p : RootedSubdivision.E F × Fin k => p.2) h0
        exact congrArg Sum.inr (Prod.ext (Subtype.ext h1) h2)

lemma promote_internal (a : Internal F k) :
    promote F k (Sum.inl a)=Sum.inl (internalMap F k a) := by cases a <;> rfl

lemma balanced [Fintype A] [Fintype R] [Fintype (RootedSubdivision.E F)]
    [Fintype (I F)] [Fintype (J F)] (c : F.Coloring (Fin 2)) (a b : ℕ)
    (hbalance : ∀ S : Finset A, b*S.card≤a*(RootedUnionDensity.incident F S).card)
    (S : Finset (Internal F k)) :
    (a+(k+1)*b)*S.card≤(a+k*b)*(RootedUnionDensity.incident (graph F k c) S).card :=
  RootPromotion.balanced (RootedHubPathBasic.graph F k c) (promote F k)
    (internalMap F k) (promote_internal F k) (a+k*b) (a+(k+1)*b)
    (RootedHubPathBasic.balanced F k c a b hbalance) S

def powerSplit (t : ℕ) : RootedPowers.Vertex (Internal F k) (Roots F k) t ≃
    Fin 2 ⊕ (RootedPowers.Vertex A R t ⊕ (((Fin t × I F) ⊕ J F) × Fin k)) where
  toFun := Sum.elim (fun p => match p.2 with
    | Sum.inl a => Sum.inr (Sum.inl (Sum.inl (p.1,a)))
    | Sum.inr e => Sum.inr (Sum.inr (Sum.inl (p.1,e.1),e.2)))
    (Sum.elim Sum.inl (Sum.elim (fun r => Sum.inr (Sum.inl (Sum.inr r)))
      (fun e => Sum.inr (Sum.inr (Sum.inr e.1,e.2)))))
  invFun := Sum.elim (fun i => Sum.inr (Sum.inl i))
    (Sum.elim (Sum.elim (fun p => Sum.inl (p.1,Sum.inl p.2)) (fun r => Sum.inr (Sum.inr (Sum.inl r))))
      (fun p => match p.1 with
        | Sum.inl e => Sum.inl (e.1,Sum.inr (e.2,p.2))
        | Sum.inr e => Sum.inr (Sum.inr (Sum.inr (e,p.2)))))
  left_inv := by
    intro v
    rcases v with ⟨i,a | ⟨e,k⟩⟩ | i | (r | ⟨e,k⟩) <;> rfl
  right_inv := by
    intro v
    rcases v with i | (⟨i,a⟩ | r) | ⟨(⟨i,e⟩ | e),k⟩ <;> rfl

noncomputable def powerEquiv (t : ℕ) (j : Fin t) :
    RootedPowers.Vertex (Internal F k) (Roots F k) t ≃
      HubPathSubdivision.Vertex (F := RootedPowers.graph F t) k :=
  (powerSplit F k t).trans (Equiv.sumCongr (Equiv.refl _)
    (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (SubdivisionPowers.edgeEquiv F t j) (Equiv.refl _))))


noncomputable def hubIso (c : F.Coloring (Fin 2)) : graph F k c ≃g HubPathSubdivision.graph c k where
  __ := (promote F k).trans (RootedHubPathBasic.move F k)
  map_rel_iff' := by intro x y; rfl

lemma power_layer (c : F.Coloring (Fin 2)) (t : ℕ) (i j : Fin t) (v : Vertex F k) :
    powerEquiv F k t j (RootedPowers.layer (graph F k c) t i v)=
      HubPathLayers.layer F c k t i (hubIso F k c v) := by
  rcases v with (a | ⟨e,l⟩) | h | (r | ⟨e,l⟩)
  all_goals try rfl
  change Sum.inr (Sum.inr (SubdivisionPowers.edge F t j e.val,l))=
    Sum.inr (Sum.inr (SubdivisionPowers.edge F t i e.val,l))
  exact congrArg Sum.inr (congrArg Sum.inr (Prod.ext
    ((SubdivisionPowers.edge_eq_iff F t j i e.val e.val).mpr ⟨rfl,Or.inr e.property⟩) rfl))

noncomputable def powerIso (c : F.Coloring (Fin 2)) (t : ℕ) (j : Fin t) :
    RootedPowers.graph (graph F k c) t ≃g
      HubPathSubdivision.graph (RootedSuspension.powerColor c t) k where
  __ := powerEquiv F k t j
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      obtain ⟨i,u,v,huv,hux,hvy⟩ := HubPathLayers.adj_layer F c k t j h
      have hu : RootedPowers.layer (graph F k c) t i ((hubIso F k c).symm u)=x := by
        apply (powerEquiv F k t j).injective
        rw [power_layer,(hubIso F k c).apply_symm_apply]
        exact hux
      have hv : RootedPowers.layer (graph F k c) t i ((hubIso F k c).symm v)=y := by
        apply (powerEquiv F k t j).injective
        rw [power_layer,(hubIso F k c).apply_symm_apply]
        exact hvy
      rw [← hu,← hv]
      exact (RootedPowers.layer (graph F k c) t i).toHom.map_rel'
        ((hubIso F k c).symm.toCopy.toHom.map_rel' huv)
    · intro h
      obtain ⟨i,u,v,huv,rfl,rfl⟩ := RootedSubdivision.adj_layer (graph F k c) t (Nat.zero_lt_of_lt j.isLt) h
      change (HubPathSubdivision.graph (RootedSuspension.powerColor c t) k).Adj
        (powerEquiv F k t j (RootedPowers.layer (graph F k c) t i u))
        (powerEquiv F k t j (RootedPowers.layer (graph F k c) t i v))
      rw [power_layer,power_layer]
      exact (HubPathLayers.layer F c k t i).toHom.map_rel' ((hubIso F k c).toCopy.toHom.map_rel' huv)

end RootedHubPath

end -- RootedHubPath

section -- ChainOperations

/- Reversal, restriction, and lower bounds for injective vertex chains. -/
open Finset SimpleGraph
namespace ChainCounting
universe u
variable {V : Type u} (G : SimpleGraph V)

lemma segment_injective {n : ℕ} {p : Chain G n} (hp : Function.Injective p.val)
    (a k : ℕ) (h : a+k ≤ n) : Function.Injective (segment G p a k h).val := by
  intro i j hij
  have h := congrArg Fin.val (hp hij)
  apply Fin.ext
  dsimp at h
  omega

def reverse {n : ℕ} (p : Chain G n) : Chain G n :=
  ⟨fun i => p.val i.rev,by intro i; simpa only [Fin.rev_castSucc,Fin.rev_succ] using (p.property i.rev).symm⟩

@[simp] lemma reverse_apply {n : ℕ} (p : Chain G n) (i : Fin (n+1)) :
    (reverse G p).val i = p.val i.rev := rfl
@[simp] lemma reverse_reverse {n : ℕ} (p : Chain G n) : reverse G (reverse G p) = p := by
  apply Subtype.ext
  funext i
  simp

lemma reverse_injective {n : ℕ} {p : Chain G n} (hp : Function.Injective p.val) :
    Function.Injective (reverse G p).val := hp.comp Fin.rev_injective

/-- All vertices strictly between the endpoints. -/
def interior [DecidableEq V] {n : ℕ} (p : Chain G n) : Finset V :=
  univ.image (fun i : Fin (n-1) => p.val ⟨i.val+1,by omega⟩)

lemma interior_card_le [DecidableEq V] {n : ℕ} (p : Chain G n) :
    (interior G p).card ≤ n-1 := (card_image_le).trans_eq (by simp)

lemma mem_interior [DecidableEq V] {n : ℕ} (p : Chain G n) (v : V) :
    v ∈ interior G p ↔ ∃ i : Fin (n+1), 0 < i.val ∧ i.val < n ∧ p.val i = v := by
  constructor
  · intro hv
    obtain ⟨i,_,hi⟩ := mem_image.mp hv
    exact ⟨⟨i.val+1,by omega⟩,(by change 0 < i.val+1; omega),
      (by change i.val+1 < n; omega),hi⟩
  · rintro ⟨i,hi0,hin,hiv⟩
    refine mem_image.mpr ⟨⟨i.val-1,by omega⟩,mem_univ _,?_⟩
    have he : (⟨(i.val-1)+1,by omega⟩ : Fin (n+1)) = i := Fin.ext (by change (i.val-1)+1 = i.val; omega)
    simpa only [he] using hiv

lemma endpoints_notMem_interior [DecidableEq V] {n : ℕ} {p : Chain G n}
    (hp : Function.Injective p.val) : p.val 0 ∉ interior G p ∧ p.val (Fin.last n) ∉ interior G p := by
  constructor
  · intro h
    obtain ⟨i,hi,_,he⟩ := (mem_interior G p _).mp h
    have hh := congrArg Fin.val (hp he)
    change i.val = 0 at hh
    omega
  · intro h
    obtain ⟨i,_,hi,he⟩ := (mem_interior G p _).mp h
    have := congrArg Fin.val (hp he)
    simp at this
    omega

lemma split_injective {n a k : ℕ} (h : a+k = n) :
    Function.Injective (fun p : Chain G n =>
      (segment G p 0 a (by omega),segment G p a k (by omega))) := by
  intro p q hpq
  apply Subtype.ext
  funext i
  by_cases hi : i.val ≤ a
  · have hh := congrArg (fun z : Chain G a × Chain G k => z.1.val ⟨i.val,by omega⟩) hpq
    simpa only [segment_apply,Nat.zero_add] using hh
  · have hh := congrArg (fun z : Chain G a × Chain G k => z.2.val ⟨i.val-a,by omega⟩) hpq
    have he : a+(i.val-a) = i.val := by omega
    simpa only [segment_apply,he] using hh

section Lower
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Append a fresh neighbor to an injective chain. -/
def snocPath {x : V} {n : ℕ} (p : PathFrom G x n) (y : V)
    (hxy : G.Adj (p.val.val.val (Fin.last n)) y) (hy : ∀ i, y ≠ p.val.val.val i) :
    PathFrom G x (n+1) := by
  let f : Fin (n+1+1) → V := Fin.snoc (α := fun _ => V) p.val.val.val y
  have hfold (i : Fin (n+1)) : f i.castSucc = p.val.val.val i := Fin.snoc_castSucc _ _ _
  have hflast : f (Fin.last (n+1)) = y := Fin.snoc_last _ _
  refine ⟨⟨⟨f,?_⟩,?_⟩,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.succ_last,hflast,hfold]
      exact hxy
    · rw [← Fin.castSucc_succ,hfold,hfold]
      exact p.val.val.property i
  · exact (hfold 0).trans p.val.property
  · change Function.Injective f
    intro i j hij
    revert hij
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _; rfl
    · rw [hflast,hfold]
      exact fun h => (hy j h).elim
    · rw [hfold,hflast]
      exact fun h => (hy i h.symm).elim
    · rw [hfold,hfold]
      exact fun h => congrArg Fin.castSucc (p.property h)

@[simp] lemma snocPath_old {x : V} {n : ℕ} (p : PathFrom G x n) (y : V)
    (hxy : G.Adj (p.val.val.val (Fin.last n)) y) (hy : ∀ i, y ≠ p.val.val.val i)
    (i : Fin (n+1)) : (snocPath G p y hxy hy).val.val.val i.castSucc = p.val.val.val i := by
  simp only [snocPath,Fin.snoc_castSucc]

@[simp] lemma snocPath_last {x : V} {n : ℕ} (p : PathFrom G x n) (y : V)
    (hxy : G.Adj (p.val.val.val (Fin.last n)) y) (hy : ∀ i, y ≠ p.val.val.val i) :
    (snocPath G p y hxy hy).val.val.val (Fin.last (n+1)) = y := by
  simp only [snocPath,Fin.snoc_last]

lemma pathFrom_lower (d n : ℕ) (hdeg : ∀ v, d+n ≤ G.degree v) (x : V) :
    d^n ≤ Fintype.card (PathFrom G x n) := by
  classical
  induction n with
  | zero =>
    have hne : Nonempty (PathFrom G x 0) := ⟨⟨⟨⟨fun _ => x,fun i => Fin.elim0 i⟩,rfl⟩,
      fun i j _ => Fin.ext (by omega)⟩⟩
    simpa using Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr hne : 0 < Fintype.card (PathFrom G x 0))
  | succ n ih =>
    have hl := ih (fun v => (Nat.add_le_add_left (Nat.le_succ n) d).trans (hdeg v))
    let allowed (p : PathFrom G x n) := G.neighborFinset (p.val.val.val (Fin.last n)) \
      univ.image p.val.val.val
    have hallow (p : PathFrom G x n) : d ≤ (allowed p).card := by
      have hh := card_le_card_sdiff_add_card (s := G.neighborFinset (p.val.val.val (Fin.last n)))
        (t := univ.image p.val.val.val)
      have hi : (univ.image p.val.val.val).card ≤ n+1 := card_image_le.trans_eq (by simp)
      rw [G.card_neighborFinset_eq_degree] at hh
      have hd := hdeg (p.val.val.val (Fin.last n))
      dsimp only [allowed]
      omega
    let f : (Σ p : PathFrom G x n, {y // y ∈ allowed p}) → PathFrom G x (n+1) := fun py =>
      snocPath G py.1 py.2.val
        ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp py.2.property).1)
        (by intro i he; exact (mem_sdiff.mp py.2.property).2 (mem_image.mpr ⟨i,mem_univ _,he.symm⟩))
    have hf : Function.Injective f := by
      rintro ⟨p,y⟩ ⟨q,z⟩ he
      have hpq : p = q := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext i
        have hh := congrArg (fun r : PathFrom G x (n+1) => r.val.val.val i.castSucc) he
        simpa only [f,snocPath_old] using hh
      subst q
      have hyz : y = z := by
        apply Subtype.ext
        have hh := congrArg (fun r : PathFrom G x (n+1) => r.val.val.val (Fin.last (n+1))) he
        simpa only [f,snocPath_last] using hh
      subst z
      rfl
    calc
      d^(n+1) = d^n*d := pow_succ _ _
      _ ≤ Fintype.card (PathFrom G x n)*d := Nat.mul_le_mul_right _ hl
      _ = ∑ _p : PathFrom G x n, d := by simp
      _ ≤ ∑ p : PathFrom G x n, (allowed p).card := sum_le_sum (fun p _ => hallow p)
      _ = Fintype.card (Σ p : PathFrom G x n, {y // y ∈ allowed p}) := by simp
      _ ≤ _ := Fintype.card_le_of_injective f hf

end Lower
end ChainCounting

end -- ChainOperations

section -- FiniteLabelPacking

/- Packing arbitrary finite objects by avoiding their finite vertex labels. -/
open Finset
namespace FiniteLabelPacking
variable {A V : Type*} [DecidableEq V]

lemma select (ℓ k : ℕ) (P : Fin k → Set A) (L : A → Finset V)
    (hcard : ∀ i a, a ∈ P i → (L a).card ≤ ℓ)
    (havoid : ∀ i (S : Finset V), S.card ≤ ℓ*k → ∃ a ∈ P i, Disjoint (L a) S) :
    ∃ f : Fin k → A, (∀ i, f i ∈ P i) ∧
      ∀ i j, i ≠ j → Disjoint (L (f i)) (L (f j)) := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨f,hf,hdis⟩ := ih (fun i => P i.succ) (fun i a ha => hcard i.succ a ha)
      (fun i S hS => havoid i.succ S (by nlinarith))
    let S := univ.biUnion (fun i => L (f i))
    have hS : S.card ≤ ℓ*(k+1) := by
      calc
        _ ≤ ∑ i, (L (f i)).card := card_biUnion_le
        _ ≤ ∑ _i : Fin k, ℓ := sum_le_sum (fun i _ => hcard i.succ (f i) (hf i))
        _ = k*ℓ := by simp
        _ ≤ ℓ*(k+1) := by nlinarith
    obtain ⟨a,ha,haS⟩ := havoid 0 S hS
    let g : Fin (k+1) → A := Fin.cons a f
    have hg : ∀ i, g i ∈ P i := by
      intro i
      exact Fin.cases ha (fun i => hf i) i
    refine ⟨g,hg,?_⟩
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact fun h => (h rfl).elim
    · intro _
      change Disjoint (L a) (L (f j))
      exact haS.mono_right (subset_biUnion_of_mem (fun i => L (f i)) (mem_univ j))
    · intro _
      change Disjoint (L (f i)) (L a)
      exact (haS.mono_right (subset_biUnion_of_mem (fun i => L (f i)) (mem_univ i))).symm
    · intro hij
      exact hdis i j (fun h => hij (congrArg Fin.succ h))

lemma select_fintype {I : Type*} [Fintype I] (ℓ : ℕ) (P : I → Set A) (L : A → Finset V)
    (hcard : ∀ i a, a ∈ P i → (L a).card ≤ ℓ)
    (havoid : ∀ i (S : Finset V), S.card ≤ ℓ*Fintype.card I → ∃ a ∈ P i, Disjoint (L a) S) :
    ∃ f : I → A, (∀ i, f i ∈ P i) ∧
      ∀ i j, i ≠ j → Disjoint (L (f i)) (L (f j)) := by
  classical
  let e := (Fintype.equivFin I).symm
  obtain ⟨f,hf,hdis⟩ := select ℓ (Fintype.card I) (fun i => P (e i)) L
    (fun i a ha => hcard (e i) a ha) (fun i S hS => havoid (e i) S hS)
  refine ⟨fun i => f (e.symm i),fun i => by simpa only [Equiv.apply_symm_apply] using hf (e.symm i),?_⟩
  intro i j hij
  exact hdis (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))

lemma hit_le [Fintype A] (P : Finset A) (L : A → Finset V) (B : ℕ)
    (hB : ∀ v, (P.filter (fun a => v ∈ L a)).card ≤ B) (S : Finset V) :
    (P.filter (fun a => ¬ Disjoint (L a) S)).card ≤ S.card*B := by
  classical
  have hsub : P.filter (fun a => ¬ Disjoint (L a) S) ⊆
      S.biUnion (fun v => P.filter (fun a => v ∈ L a)) := by
    intro a ha
    have hp := (mem_filter.mp ha).1
    have hd := (mem_filter.mp ha).2
    rw [Finset.disjoint_left] at hd
    push_neg at hd
    obtain ⟨v,hv,hvS⟩ := hd
    exact mem_biUnion.mpr ⟨v,hvS,mem_filter.mpr ⟨hp,hv⟩⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ v ∈ S, (P.filter (fun a => v ∈ L a)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ S, B := sum_le_sum (fun v _ => hB v)
    _ = _ := by simp

lemma avoid_of_card [Fintype A] (P : Finset A) (L : A → Finset V) (B : ℕ)
    (hB : ∀ v, (P.filter (fun a => v ∈ L a)).card ≤ B) (S : Finset V)
    (hcard : S.card*B < P.card) : ∃ a ∈ P, Disjoint (L a) S := by
  classical
  have hh := (hit_le P L B hB S).trans_lt hcard
  obtain ⟨a,ha,haS⟩ := exists_mem_notMem_of_card_lt_card hh
  refine ⟨a,ha,?_⟩
  by_contra hd
  exact haS (mem_filter.mpr ⟨ha,hd⟩)

end FiniteLabelPacking

end -- FiniteLabelPacking

section -- GoodChains

/- Recursive good chains and the bounded-fiber mechanism for parallel paths. -/
open Finset SimpleGraph ChainCounting
namespace GoodChains
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
noncomputable section
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel _

noncomputable def Good (L : ℕ → ℕ) (n : ℕ) (p : Chain G n) : Prop := by
  classical
  let A (q : Chain G n) : Prop := Function.Injective q.val ∧
    ∀ a k : ℕ, (hk : k < n) → (h : a+k ≤ n) → Good L k (segment G q a k h)
  exact A p ∧ (univ.filter (fun q : Chain G n => A q ∧ q.val 0 = p.val 0 ∧
    q.val (Fin.last n) = p.val (Fin.last n))).card ≤ L n
termination_by n

noncomputable def Admissible (L : ℕ → ℕ) (n : ℕ) (p : Chain G n) : Prop :=
  Function.Injective p.val ∧
    ∀ a k : ℕ, (hk : k < n) → (h : a+k ≤ n) → Good G L k (segment G p a k h)

noncomputable def fiber (L : ℕ → ℕ) (n : ℕ) (x y : V) : Finset (Chain G n) := by
  classical
  exact univ.filter (fun p => Admissible G L n p ∧ p.val 0 = x ∧ p.val (Fin.last n) = y)

noncomputable def goodFiber (L : ℕ → ℕ) (n : ℕ) (x y : V) : Finset (Chain G n) := by
  classical
  exact univ.filter (fun p => Good G L n p ∧ p.val 0 = x ∧ p.val (Fin.last n) = y)

lemma good_iff (L : ℕ → ℕ) (n : ℕ) (p : Chain G n) :
    Good G L n p ↔ Admissible G L n p ∧ (fiber G L n (p.val 0) (p.val (Fin.last n))).card ≤ L n := by
  classical
  rw [Good]
  simp only [fiber,Admissible]

lemma mem_fiber (L : ℕ → ℕ) (n : ℕ) (x y : V) (p : Chain G n) :
    p ∈ fiber G L n x y ↔ Admissible G L n p ∧ p.val 0 = x ∧ p.val (Fin.last n) = y := by
  classical
  simp only [fiber,mem_filter,mem_univ,true_and]

lemma mem_goodFiber (L : ℕ → ℕ) (n : ℕ) (x y : V) (p : Chain G n) :
    p ∈ goodFiber G L n x y ↔ Good G L n p ∧ p.val 0 = x ∧ p.val (Fin.last n) = y := by
  classical
  simp only [goodFiber,mem_filter,mem_univ,true_and]

lemma goodFiber_le (L : ℕ → ℕ) (n : ℕ) (x y : V) : (goodFiber G L n x y).card ≤ L n := by
  classical
  by_cases h : (goodFiber G L n x y).Nonempty
  · obtain ⟨p,hp⟩ := h
    obtain ⟨hp,hx,hy⟩ := (mem_goodFiber G L n x y p).mp hp
    have hb := ((good_iff G L n p).mp hp).2
    rw [hx,hy] at hb
    apply le_trans (card_le_card (t := fiber G L n x y) ?_) hb
    intro q hq
    obtain ⟨hq,hqx,hqy⟩ := (mem_goodFiber G L n x y q).mp hq
    exact (mem_fiber G L n x y q).mpr ⟨((good_iff G L n q).mp hq).1,hqx,hqy⟩
  · rw [not_nonempty_iff_eq_empty.mp h,card_empty]
    exact Nat.zero_le _

lemma coordinate_le (L : ℕ → ℕ) (n : ℕ) (x y v : V) (i : Fin (n-1)) :
    ((fiber G L n x y).filter (fun p => p.val ⟨i.val+1,by omega⟩ = v)).card ≤
      L (i.val+1) * L (n-(i.val+1)) := by
  classical
  let P := (fiber G L n x y).filter (fun p => p.val ⟨i.val+1,by omega⟩ = v)
  let left (p : P) : {q // q ∈ goodFiber G L (i.val+1) x v} := by
    refine ⟨segment G p.val 0 (i.val+1) (by omega),?_⟩
    obtain ⟨hp,hx,hy⟩ := (mem_fiber G L n x y p.val).mp (mem_filter.mp p.property).1
    apply (mem_goodFiber G L (i.val+1) x v _).mpr
    refine ⟨hp.2 0 (i.val+1) (by omega) (by omega),hx,?_⟩
    simpa only [segment_apply,Fin.val_last,Nat.zero_add] using (mem_filter.mp p.property).2
  let right (p : P) : {q // q ∈ goodFiber G L (n-(i.val+1)) v y} := by
    refine ⟨segment G p.val (i.val+1) (n-(i.val+1)) (by omega),?_⟩
    obtain ⟨hp,hx,hy⟩ := (mem_fiber G L n x y p.val).mp (mem_filter.mp p.property).1
    apply (mem_goodFiber G L (n-(i.val+1)) v y _).mpr
    refine ⟨hp.2 (i.val+1) (n-(i.val+1)) (by omega) (by omega),(mem_filter.mp p.property).2,?_⟩
    have he : i.val+1+(n-(i.val+1)) = n := by omega
    simpa only [segment_apply,Fin.val_last,he,Fin.last] using hy
  let f (p : P) := (left p,right p)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply split_injective G (show (i.val+1)+(n-(i.val+1)) = n by omega)
    exact congrArg (fun z : {q // q ∈ goodFiber G L (i.val+1) x v} ×
      {q // q ∈ goodFiber G L (n-(i.val+1)) v y} => (z.1.val,z.2.val)) hpq
  calc
    _ = Fintype.card P := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ({q // q ∈ goodFiber G L (i.val+1) x v} ×
        {q // q ∈ goodFiber G L (n-(i.val+1)) v y}) := Fintype.card_le_of_injective f hf
    _ = (goodFiber G L (i.val+1) x v).card * (goodFiber G L (n-(i.val+1)) v y).card := by simp
    _ ≤ _ := Nat.mul_le_mul (goodFiber_le G L _ _ _) (goodFiber_le G L _ _ _)

lemma interior_incidence_le (L : ℕ → ℕ) (hL : Monotone L) (n : ℕ) (x y v : V) :
    ((fiber G L n x y).filter (fun p => v ∈ interior G p)).card ≤ (n-1)*(L (n-1))^2 := by
  classical
  let P (i : Fin (n-1)) := (fiber G L n x y).filter (fun p => p.val ⟨i.val+1,by omega⟩ = v)
  have hsub : (fiber G L n x y).filter (fun p => v ∈ interior G p) ⊆ univ.biUnion P := by
    intro p hp
    obtain ⟨i,_,hi⟩ := mem_image.mp (mem_filter.mp hp).2
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨(mem_filter.mp hp).1,hi⟩⟩
  have hP (i : Fin (n-1)) : (P i).card ≤ (L (n-1))^2 := by
    apply (coordinate_le G L n x y v i).trans
    rw [pow_two]
    exact Nat.mul_le_mul (hL (by omega)) (hL (by omega))
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i, (P i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin (n-1), (L (n-1))^2 := sum_le_sum (fun i _ => hP i)
    _ = _ := by simp

end
end GoodChains

end -- GoodChains

section -- ThetaChains

/- Thresholds and a path-family formulation of theta graphs. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace ThetaChains
set_option maxHeartbeats 1000000
universe u

def threshold (B : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1)*(B+1)*(threshold B n)^2+1

lemma threshold_pos (B n : ℕ) : 0 < threshold B n := by
  cases n <;> simp [threshold]

lemma threshold_mono (B : ℕ) : Monotone (threshold B) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [threshold]
  have hp := threshold_pos B n
  have hsq : threshold B n ≤ (threshold B n)^2 := by nlinarith
  have hc : 1 ≤ (n+1)*(B+1) := by nlinarith
  have hm := Nat.mul_le_mul_right ((threshold B n)^2) hc
  nlinarith

lemma threshold_large (B n : ℕ) (hn : 0 < n) :
    n*B*(threshold B (n-1))^2 < threshold B n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one,threshold]
  nlinarith

variable {V : Type u} (G : SimpleGraph V)


noncomputable section
local instance : DecidableEq V := Classical.decEq V
variable [Fintype V]

lemma fiber_avoiding (B n : ℕ) (hn : 0 < n) (x y : V)
    (hheavy : threshold B n < (fiber G (threshold B) n x y).card)
    (S : Finset V) (hS : S.card ≤ B) :
    ∃ p ∈ fiber G (threshold B) n x y, Disjoint (interior G p) S := by
  classical
  apply FiniteLabelPacking.avoid_of_card (fiber G (threshold B) n x y) (interior G)
    ((n-1)*(threshold B (n-1))^2)
    (fun v => interior_incidence_le G (threshold B) (threshold_mono B) n x y v) S
  have hh := Nat.mul_le_mul hS (Nat.sub_le n 1)
  have hm := Nat.mul_le_mul_right ((threshold B (n-1))^2) hh
  have hl := (threshold_large B n hn).trans hheavy
  nlinarith only [hm,hl]


end
end ThetaChains

end -- ThetaChains

section -- ChainComposition

/- Compatibility of chain restriction and reversal. -/
open Finset SimpleGraph
namespace ChainCounting
universe u
variable {V : Type u} (G : SimpleGraph V)

lemma segment_segment {n : ℕ} (p : Chain G n) (a k b j : ℕ)
    (h : a+k ≤ n) (h' : b+j ≤ k) :
    segment G (segment G p a k h) b j h' = segment G p (a+b) j (by omega) := by
  apply Subtype.ext
  funext i
  simp only [segment_apply]
  apply congrArg p.val
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

lemma segment_self {n : ℕ} (p : Chain G n) : segment G p 0 n (by omega) = p := by
  apply Subtype.ext
  funext i
  simp only [segment_apply,Nat.zero_add]

lemma reverse_segment {n : ℕ} (p : Chain G n) (a k : ℕ) (h : a+k ≤ n) :
    segment G (reverse G p) a k h =
      reverse G (segment G p (n-(a+k)) k (by omega)) := by
  apply Subtype.ext
  funext i
  simp only [segment_apply,reverse_apply]
  apply congrArg p.val
  apply Fin.ext
  simp only [Fin.val_rev,Fin.val_mk]
  omega

@[simp] lemma reverse_start {n : ℕ} (p : Chain G n) : (reverse G p).val 0 = p.val (Fin.last n) := by
  simp [reverse_apply]
@[simp] lemma reverse_last {n : ℕ} (p : Chain G n) : (reverse G p).val (Fin.last n) = p.val 0 := by
  simp [reverse_apply]

end ChainCounting

end -- ChainComposition

section -- GoodChainReversal

/- Symmetry of good and admissible chains, and minimal bad-subchain witnesses. -/
open Finset SimpleGraph ChainCounting
namespace GoodChains
set_option maxHeartbeats 1000000
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
noncomputable section
local instance : DecidableEq V := Classical.decEq V

lemma fiber_card_reverse (L : ℕ → ℕ) (n : ℕ)
    (hA : ∀ p : Chain G n, Admissible G L n (reverse G p) ↔ Admissible G L n p)
    (x y : V) : (fiber G L n x y).card = (fiber G L n y x).card := by
  classical
  have hi : Function.Injective (reverse G : Chain G n → Chain G n) := by
    intro p q h
    have hh := congrArg (reverse G) h
    simpa using hh
  have he : (fiber G L n x y).image (reverse G) = fiber G L n y x := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
      obtain ⟨hq,hx,hy⟩ := (mem_fiber G L n x y q).mp hq
      apply (mem_fiber G L n y x _).mpr
      exact ⟨(hA q).mpr hq,by simpa using hy,by simpa using hx⟩
    · intro hp
      obtain ⟨hp,hy,hx⟩ := (mem_fiber G L n y x p).mp hp
      refine mem_image.mpr ⟨reverse G p,?_,reverse_reverse G p⟩
      apply (mem_fiber G L n x y _).mpr
      exact ⟨(hA p).mpr hp,by simpa using hx,by simpa using hy⟩
  rw [← he,card_image_of_injective _ hi]

lemma good_reverse (L : ℕ → ℕ) (n : ℕ) (p : Chain G n) :
    Good G L n (reverse G p) ↔ Good G L n p := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hforward : ∀ p : Chain G n, Admissible G L n p → Admissible G L n (reverse G p) := by
      intro p hp
      refine ⟨reverse_injective G hp.1,?_⟩
      intro a k hk h
      rw [reverse_segment]
      exact (ih k hk _).mpr (hp.2 (n-(a+k)) k hk (by omega))
    have hA (p : Chain G n) : Admissible G L n (reverse G p) ↔ Admissible G L n p := by
      constructor
      · intro hp
        simpa using hforward (reverse G p) hp
      · exact hforward p
    rw [good_iff,good_iff,hA,reverse_start,reverse_last,
      fiber_card_reverse G L n hA (p.val (Fin.last n)) (p.val 0)]

lemma admissible_reverse (L : ℕ → ℕ) (n : ℕ) (p : Chain G n) :
    Admissible G L n (reverse G p) ↔ Admissible G L n p := by
  have hf : ∀ p : Chain G n, Admissible G L n p → Admissible G L n (reverse G p) := by
    intro p hp
    refine ⟨reverse_injective G hp.1,?_⟩
    intro a k hk h
    rw [reverse_segment]
    exact (good_reverse G L k _).mpr (hp.2 (n-(a+k)) k hk (by omega))
  exact ⟨fun hp => by simpa using hf (reverse G p) hp,hf p⟩

lemma fiber_symmetric (L : ℕ → ℕ) (n : ℕ) (x y : V) :
    (fiber G L n x y).card = (fiber G L n y x).card :=
  fiber_card_reverse G L n (admissible_reverse G L n) x y

/-- A bad injective chain contains an admissible chain with a heavy endpoint fiber. -/
lemma bad_witness (L : ℕ → ℕ) (n : ℕ) (p : Chain G n)
    (hp : Function.Injective p.val) (hbad : ¬ Good G L n p) :
    ∃ a j : ℕ, ∃ h : a+j ≤ n, Admissible G L j (segment G p a j h) ∧
      L j < (fiber G L j ((segment G p a j h).val 0)
        ((segment G p a j h).val (Fin.last j))).card := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hA : Admissible G L n p
    · have hh : L n < (fiber G L n (p.val 0) (p.val (Fin.last n))).card := by
        by_contra hh
        exact hbad ((good_iff G L n p).mpr ⟨hA,by omega⟩)
      exact ⟨0,n,by omega,by simpa [segment_self] using hA,by simpa [segment_self] using hh⟩
    · have hs : ¬ ∀ a k : ℕ, (hk : k < n) → (h : a+k ≤ n) → Good G L k (segment G p a k h) := by
        exact fun hs => hA ⟨hp,hs⟩
      push_neg at hs
      obtain ⟨a,k,hk,hlen,hkbad⟩ := hs
      obtain ⟨b,j,hbj,hj,hheavy⟩ := ih k hk (segment G p a k hlen)
        (segment_injective G hp a k hlen) hkbad
      refine ⟨a+b,j,by omega,?_,?_⟩
      · simpa only [segment_segment] using hj
      · simpa only [segment_segment] using hheavy


end
end GoodChains

end -- GoodChainReversal

section -- ChainExtensionCounts

/- Extending prescribed consecutive subchains costs at most one degree choice per
additional edge. -/
open Finset SimpleGraph
namespace ChainCounting
set_option maxHeartbeats 1000000
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
noncomputable section
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel _

def extensions (n a j : ℕ) (h : a+j ≤ n) (P : Finset (Chain G j)) : Finset (Chain G n) := by
  classical
  exact univ.filter (fun p => segment G p a j h ∈ P)

lemma extensions_le (D n a j : ℕ) (hD : ∀ v, G.degree v ≤ D) (h : a+j ≤ n)
    (P : Finset (Chain G j)) : (extensions G n a j h P).card ≤ P.card*D^(n-j) := by
  classical
  let E := extensions G n a j h P
  let center (p : E) : P := ⟨segment G p.val a j h,(mem_filter.mp p.property).2⟩
  let left (p : E) : From G ((center p).val.val 0) a :=
    ⟨reverse G (segment G p.val 0 a (by omega)),by simp [center,reverse_start,segment_apply]⟩
  let right (p : E) : From G ((center p).val.val (Fin.last j)) (n-(a+j)) :=
    ⟨segment G p.val (a+j) (n-(a+j)) (by omega),rfl⟩
  let C (q : P) := From G (q.val.val 0) a × From G (q.val.val (Fin.last j)) (n-(a+j))
  let f : E → Σ q : P, C q := fun p => ⟨center p,(left p,right p)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i.val ≤ a
    · have hh := congrArg (fun z : Σ q : P, C q =>
        (reverse G z.2.1.val).val ⟨i.val,by omega⟩) hpq
      simpa only [f,left,reverse_reverse,segment_apply,Nat.zero_add] using hh
    · by_cases hij : i.val ≤ a+j
      · have hh := congrArg (fun z : Σ q : P, C q => z.1.val.val ⟨i.val-a,by omega⟩) hpq
        have he : a+(i.val-a) = i.val := by omega
        simpa only [f,center,segment_apply,he] using hh
      · have hh := congrArg (fun z : Σ q : P, C q => z.2.2.val.val ⟨i.val-(a+j),by omega⟩) hpq
        have he : a+j+(i.val-(a+j)) = i.val := by omega
        simpa only [f,right,segment_apply,he] using hh
  have hC (q : P) : Fintype.card (C q) ≤ D^(n-j) := by
    calc
      _ = Fintype.card (From G (q.val.val 0) a) * Fintype.card (From G (q.val.val (Fin.last j)) (n-(a+j))) := Fintype.card_prod _ _
      _ ≤ D^a*D^(n-(a+j)) := Nat.mul_le_mul (from_le G D hD _ _) (from_le G D hD _ _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ = Fintype.card E := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Σ q : P, C q) := Fintype.card_le_of_injective f hf
    _ = ∑ q : P, Fintype.card (C q) := Fintype.card_sigma
    _ ≤ ∑ _q : P, D^(n-j) := sum_le_sum (fun q _ => hC q)
    _ = _ := by simp

end
end ChainCounting

end -- ChainExtensionCounts

section -- BasicChainCounting

/- Counting all simple chains by good endpoint fibers and extensions of heavy subchains. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace GeneralThetaCounting
set_option maxHeartbeats 2000000
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
noncomputable section
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel _

def paths (k : ℕ) : Finset (Chain G k) := by
  classical
  exact univ.filter (fun p => Function.Injective p.val)

lemma paths_lower (d k : ℕ) (hd : ∀ v, d+k ≤ G.degree v) :
    Fintype.card V*d^k ≤ (paths G k).card := by
  classical
  let f : (Σ x : V, PathFrom G x k) → (paths G k) := fun xp =>
    ⟨xp.2.val.val,mem_filter.mpr ⟨mem_univ _,xp.2.property⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨x,p⟩ ⟨y,q⟩ he
    have hpq : p.val.val = q.val.val := congrArg (fun z : paths G k => z.val) he
    have hxy : x = y := p.val.property.symm.trans ((congrArg (fun z : Chain G k => z.val 0) hpq).trans q.val.property)
    subst y
    have hpq' : p = q := Subtype.ext (Subtype.ext hpq)
    subst q
    rfl
  calc
    _ = ∑ _x : V, d^k := by simp
    _ ≤ ∑ x : V, Fintype.card (PathFrom G x k) := sum_le_sum (fun x _ => pathFrom_lower G d k hd x)
    _ = Fintype.card (Σ x : V, PathFrom G x k) := Fintype.card_sigma.symm
    _ ≤ Fintype.card (paths G k) := Fintype.card_le_of_injective f hf
    _ = _ := Fintype.card_coe _

lemma small_fiber (L : ℕ → ℕ) (j : ℕ) (hj : j ≤ 1) (x y : V) :
    (fiber G L j x y).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨_,hpx,hpy⟩ := (mem_fiber G L j x y p).mp hp
  obtain ⟨_,hqx,hqy⟩ := (mem_fiber G L j x y q).mp hq
  apply Subtype.ext
  funext i
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    exact hpx.trans hqx.symm
  · have hi' : i = Fin.last j := Fin.ext (by change i.val = j; omega)
    subst i
    exact hpy.trans hqy.symm

lemma heavy_length (B j : ℕ) (x y : V)
    (h : threshold B j < (fiber G (threshold B) j x y).card) : 2 ≤ j := by
  by_contra hj
  have hsmall := small_fiber G (threshold B) j (by omega) x y
  have hpos := threshold_pos B j
  omega

end
end GeneralThetaCounting

end -- BasicChainCounting


section -- FiniteDisjointSubfamily

/- A large pairwise-disjoint-label subfamily with explicit cardinality loss. -/
open Finset
namespace FiniteDisjointSubfamily
set_option maxHeartbeats 1500000
universe u v

lemma select {A : Type u} {V : Type v} [Fintype A] [DecidableEq V]
    (P : Finset A) (labels : A → Finset V) (a M : ℕ)
    (hne : ∀ p∈P, (labels p).Nonempty)
    (hsize : ∀ p∈P, (labels p).card≤a)
    (hM : ∀ v, (P.filter (fun p => v∈labels p)).card≤M) :
    ∃ Q : Finset A, Q⊆P ∧ (∀ p∈Q, ∀ q∈Q, p≠q → Disjoint (labels p) (labels q)) ∧
      P.card≤(a*M)*Q.card := by
  classical
  let S := P.powerset.filter (fun Q => ∀ p∈Q, ∀ q∈Q, p≠q → Disjoint (labels p) (labels q))
  have hS : S.Nonempty := ⟨∅,by simp [S]⟩
  obtain ⟨Q,hQ,hmax⟩ := exists_max_image S Finset.card hS
  have hQP : Q⊆P := mem_powerset.mp (mem_filter.mp hQ).1
  have hQdis := (mem_filter.mp hQ).2
  let U := Q.biUnion labels
  have hcover (p : A) (hp : p∈P) : ¬Disjoint (labels p) U := by
    intro hd
    have hdis (q : A) (hq : q∈Q) : Disjoint (labels p) (labels q) :=
      (disjoint_biUnion_right _ _ _).mp hd q hq
    have hpQ : p∉Q := by
      intro hpQ
      obtain ⟨v,hv⟩ := hne p hp
      exact disjoint_left.mp (hdis p hpQ) hv hv
    have hmem : insert p Q∈S := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hp hQP),?_⟩
      intro r hr s hs hrs
      rcases mem_insert.mp hr with hr | hr
      · subst r
        rcases mem_insert.mp hs with hs | hs
        · subst s
          exact (hrs rfl).elim
        · exact hdis s hs
      · rcases mem_insert.mp hs with hs | hs
        · subst s
          exact (hdis r hr).symm
        · exact hQdis r hr s hs hrs
    have hh := hmax (insert p Q) hmem
    rw [card_insert_of_notMem hpQ] at hh
    omega
  have hfilter : P.filter (fun p => ¬Disjoint (labels p) U)=P := by
    ext p
    simp only [mem_filter,and_iff_left_iff_imp]
    exact hcover p
  have hU : U.card≤a*Q.card := by
    apply card_biUnion_le.trans
    calc
      (∑ p∈Q, (labels p).card) ≤ ∑ _p∈Q, a := sum_le_sum (fun p hp => hsize p (hQP hp))
      _ = _ := by simp [Nat.mul_comm]
  have hhit := FiniteLabelPacking.hit_le P labels M hM U
  rw [hfilter] at hhit
  refine ⟨Q,hQP,hQdis,?_⟩
  exact (hhit.trans (Nat.mul_le_mul_right M hU)).trans_eq (by ring)

end FiniteDisjointSubfamily

end -- FiniteDisjointSubfamily

section -- HubLightPaths

/- Paths with all subpaths up to the core replacement length good.
The longer near-full subpaths are deliberately not required to be good. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace HubLightPaths
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V]
local instance : DecidableEq V := Classical.decEq _
variable (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _

abbrev Path (k : ℕ) := Chain H (k+3)

def Good (k : ℕ) (L : ℕ → ℕ) (p : Path H k) : Prop :=
  Function.Injective p.val ∧ ∀ a j : ℕ, (hj : j≤k+1) → (hlen : a+j≤k+3) →
    GoodChains.Good H L j (segment H p a j hlen)

def good (k : ℕ) (L : ℕ → ℕ) : Finset (Path H k) := by
  classical
  exact univ.filter (Good H k L)

def links (k : ℕ) (L : ℕ → ℕ) (x y : V) : Finset (Path H k) :=
  (good H k L).filter (fun p => p.val 0=x ∧ p.val (Fin.last (k+3))=y)

lemma mem_links (k : ℕ) (L : ℕ → ℕ) (x y : V) (p : Path H k) :
    p∈links H k L x y ↔ Good H k L p ∧ p.val 0=x ∧ p.val (Fin.last (k+3))=y := by
  simp only [links,good,mem_filter,mem_univ,true_and]

def first (k : ℕ) (p : Path H k) : V := p.val ⟨1,by omega⟩
def last (k : ℕ) (p : Path H k) : V := p.val ⟨k+2,by omega⟩
def middle (k : ℕ) (p : Path H k) (i : Fin k) : V := p.val ⟨i.val+2,by omega⟩

def core (k : ℕ) (p : Path H k) : Chain H (k+1) := segment H p 1 (k+1) (by omega)

lemma pair_bound (k : ℕ) (L : ℕ → ℕ) (x y : V) (z : V × V) :
    ((links H k L x y).filter (fun p => (first H k p,last H k p)=z)).card≤L (k+1) := by
  let P := (links H k L x y).filter (fun p => (first H k p,last H k p)=z)
  apply (card_le_card_of_injOn (core H k) ?_ ?_).trans (goodFiber_le H L (k+1) z.1 z.2)
  · intro p hp
    have hh := (mem_links H k L x y p).mp (mem_filter.mp hp).1
    have he := (mem_filter.mp hp).2
    apply (mem_goodFiber H L (k+1) z.1 z.2 _).mpr
    refine ⟨hh.1.2 1 (k+1) (by omega) (by omega),?_,?_⟩
    · exact congrArg Prod.fst he
    · simpa only [core,segment_apply,Fin.val_last,last,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
        using congrArg Prod.snd he
  · intro p hp q hq he
    have hp' := (mem_links H k L x y p).mp (mem_filter.mp hp).1
    have hq' := (mem_links H k L x y q).mp (mem_filter.mp hq).1
    apply Subtype.ext
    funext i
    by_cases hi0 : i.val=0
    · have hi : i=0 := Fin.ext hi0
      subst i
      exact hp'.2.1.trans hq'.2.1.symm
    · by_cases hil : i.val=k+3
      · have hi : i=Fin.last (k+3) := Fin.ext hil
        subst i
        exact hp'.2.2.trans hq'.2.2.symm
      · have hh := congrArg (fun p : Chain H (k+1) => p.val ⟨i.val-1,by have := i.isLt; omega⟩) he
        have hidx : 1+(i.val-1)=i.val := by omega
        simpa only [core,segment_apply,hidx] using hh

lemma coordinate_bound (k : ℕ) (L : ℕ → ℕ) (x y v : V) (i : Fin k) :
    ((links H k L x y).filter (fun p => middle H k p i=v)).card≤L (i.val+2)*L (k+1-i.val) := by
  let P := (links H k L x y).filter (fun p => middle H k p i=v)
  let left (p : P) : {q // q∈goodFiber H L (i.val+2) x v} := by
    refine ⟨segment H p.val 0 (i.val+2) (by omega),?_⟩
    have hp := (mem_links H k L x y p.val).mp (mem_filter.mp p.property).1
    apply (mem_goodFiber H L (i.val+2) x v _).mpr
    refine ⟨hp.1.2 0 (i.val+2) (by omega) (by omega),hp.2.1,?_⟩
    simpa only [segment_apply,Fin.val_last,Nat.zero_add,middle] using (mem_filter.mp p.property).2
  let right (p : P) : {q // q∈goodFiber H L (k+1-i.val) v y} := by
    refine ⟨segment H p.val (i.val+2) (k+1-i.val) (by omega),?_⟩
    have hp := (mem_links H k L x y p.val).mp (mem_filter.mp p.property).1
    apply (mem_goodFiber H L (k+1-i.val) v y _).mpr
    refine ⟨hp.1.2 (i.val+2) (k+1-i.val) (by omega) (by omega),(mem_filter.mp p.property).2,?_⟩
    have he : i.val+2+(k+1-i.val)=k+3 := by omega
    simpa only [segment_apply,Fin.val_last,he,Fin.last] using hp.2.2
  let f (p : P) := (left p,right p)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply split_injective H (show (i.val+2)+(k+1-i.val)=k+3 by omega)
    exact congrArg (fun z : {q // q∈goodFiber H L (i.val+2) x v} ×
      {q // q∈goodFiber H L (k+1-i.val) v y} => (z.1.val,z.2.val)) hpq
  calc
    _ = Fintype.card P := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ({q // q∈goodFiber H L (i.val+2) x v} ×
      {q // q∈goodFiber H L (k+1-i.val) v y}) := Fintype.card_le_of_injective f hf
    _ = (goodFiber H L (i.val+2) x v).card*(goodFiber H L (k+1-i.val) v y).card := by simp
    _ ≤ _ := Nat.mul_le_mul (goodFiber_le H L _ _ _) (goodFiber_le H L _ _ _)

lemma coordinate_le (k : ℕ) (L : ℕ → ℕ) (hL : Monotone L) (x y v : V) (i : Fin k) :
    ((links H k L x y).filter (fun p => middle H k p i=v)).card≤(L (k+1))^2 := by
  apply (coordinate_bound H k L x y v i).trans
  rw [pow_two]
  exact Nat.mul_le_mul (hL (by omega)) (hL (by omega))

end
end HubLightPaths

end -- HubLightPaths

section -- ChainAppend

/- Concatenating ordered vertex chains at a common endpoint. -/
open Finset SimpleGraph
namespace ChainCounting
universe u
variable {V : Type u} (G : SimpleGraph V)

private def appendFun {n m : ℕ} (p : Chain G n) (q : Chain G m) : Fin (n+m+1) → V :=
  fun i => if h : i.val ≤ n then p.val ⟨i.val,by omega⟩ else q.val ⟨i.val-n,by omega⟩

private lemma appendFun_left {n m : ℕ} (p : Chain G n) (q : Chain G m) (i : Fin (n+1)) :
    appendFun G p q ⟨i.val,by omega⟩ = p.val i := by
  simp only [appendFun,dif_pos (show i.val ≤ n by omega)]

private lemma appendFun_right {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) (i : Fin (m+1)) :
    appendFun G p q ⟨n+i.val,by omega⟩ = q.val i := by
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    simpa [Fin.last,appendFun] using h
  · have hlo : ¬ n+i.val ≤ n := by omega
    simp only [appendFun,dif_neg hlo,Nat.add_sub_cancel_left]

/-- Concatenation, without repeating the common endpoint. -/
def append {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) : Chain G (n+m) := by
  refine ⟨appendFun G p q,?_⟩
  intro i
  by_cases hi : i.val < n
  · have h₁ : i.castSucc = (⟨i.val,by omega⟩ : Fin (n+m+1)) := rfl
    have h₂ : i.succ = (⟨i.val+1,by omega⟩ : Fin (n+m+1)) := rfl
    rw [h₁,h₂,appendFun_left G p q ⟨i.val,by omega⟩,appendFun_left G p q ⟨i.val+1,by omega⟩]
    exact p.property ⟨i.val,hi⟩
  · have h₁ : i.castSucc = (⟨n+(i.val-n),by omega⟩ : Fin (n+m+1)) := Fin.ext (by simp; omega)
    have h₂ : i.succ = (⟨n+((i.val-n)+1),by omega⟩ : Fin (n+m+1)) := Fin.ext (by simp; omega)
    rw [h₁,h₂,appendFun_right G p q h ⟨i.val-n,by omega⟩,
      appendFun_right G p q h ⟨i.val-n+1,by omega⟩]
    exact q.property ⟨i.val-n,by omega⟩

lemma append_left {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) (i : Fin (n+1)) :
    (append G p q h).val ⟨i.val,by omega⟩ = p.val i := appendFun_left G p q i

lemma append_right {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) (i : Fin (m+1)) :
    (append G p q h).val ⟨n+i.val,by omega⟩ = q.val i := appendFun_right G p q h i

@[simp] lemma append_start {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) : (append G p q h).val 0 = p.val 0 := append_left G p q h 0

@[simp] lemma append_last {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) : (append G p q h).val (Fin.last (n+m)) = q.val (Fin.last m) :=
  append_right G p q h (Fin.last m)

lemma append_injective {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) (hp : Function.Injective p.val) (hq : Function.Injective q.val)
    (hcross : ∀ i j, p.val i = q.val j → i = Fin.last n ∧ j = 0) :
    Function.Injective (append G p q h).val := by
  intro i j hij
  change appendFun G p q i = appendFun G p q j at hij
  simp only [appendFun] at hij
  split_ifs at hij with hi hj hj
  · have hh := congrArg Fin.val (hp hij)
    apply Fin.ext
    exact hh
  · have hh := (hcross _ _ hij).2
    have hz := congrArg Fin.val hh
    change j.val-n = 0 at hz
    omega
  · have hh := (hcross _ _ hij.symm).2
    have hz := congrArg Fin.val hh
    change i.val-n = 0 at hz
    omega
  · have hh := congrArg Fin.val (hq hij)
    apply Fin.ext
    dsimp only [Fin.val_mk] at hh
    omega

lemma append_vertex {n m : ℕ} (p : Chain G n) (q : Chain G m)
    (h : p.val (Fin.last n) = q.val 0) (i : Fin (n+m+1)) :
    (∃ j : Fin (n+1), (append G p q h).val i = p.val j) ∨
      ∃ j : Fin (m+1), (append G p q h).val i = q.val j := by
  by_cases hi : i.val ≤ n
  · exact Or.inl ⟨⟨i.val,by omega⟩,append_left G p q h ⟨i.val,by omega⟩⟩
  · refine Or.inr ⟨⟨i.val-n,by omega⟩,?_⟩
    have he : i = (⟨n+(i.val-n),by omega⟩ : Fin (n+m+1)) := Fin.ext (by simp; omega)
    exact (congrArg (append G p q h).val he).trans (append_right G p q h ⟨i.val-n,by omega⟩)

end ChainCounting

end -- ChainAppend

section -- ChainConcatenation

/- Joining a simple chain of internally disjoint replacement paths. -/
open Finset SimpleGraph
namespace ChainCounting
universe u
variable {V : Type u} [DecidableEq V] (G : SimpleGraph V)

lemma vertex_cases {n : ℕ} (p : Chain G n) (i : Fin (n+1)) :
    p.val i = p.val 0 ∨ p.val i = p.val (Fin.last n) ∨ p.val i ∈ interior G p := by
  by_cases hi0 : i.val = 0
  · exact Or.inl (congrArg p.val (Fin.ext hi0))
  · by_cases hin : i.val = n
    · exact Or.inr (Or.inl (congrArg p.val (Fin.ext hin)))
    · exact Or.inr (Or.inr ((mem_interior G p _).mpr ⟨i,by omega,by omega,rfl⟩))

/-- Concatenation of replacement paths. Besides injectivity, record where every
vertex came from; this makes simultaneous liftings straightforward to verify. -/
lemma concatenate (ℓ m : ℕ) (b : Fin (m+1) → V) (f : Fin m → Chain G ℓ)
    (hb : Function.Injective b)
    (hf : ∀ e, Function.Injective (f e).val ∧ (f e).val 0 = b e.castSucc ∧
      (f e).val (Fin.last ℓ) = b e.succ)
    (havoid : ∀ e r, b r ∉ interior G (f e))
    (hdis : ∀ e d, e ≠ d → Disjoint (interior G (f e)) (interior G (f d))) :
    ∃ p : Chain G (m*ℓ), Function.Injective p.val ∧ p.val 0 = b 0 ∧
      p.val (Fin.last (m*ℓ)) = b (Fin.last m) ∧
      ∀ i, (∃ r, p.val i = b r) ∨ ∃ e, p.val i ∈ interior G (f e) := by
  induction m with
  | zero =>
    refine ⟨⟨fun _ => b 0,fun i => by have hi := i.isLt; omega⟩,?_,rfl,rfl,?_⟩
    · intro i j _
      exact Fin.ext (by omega)
    · intro i
      exact Or.inl ⟨0,rfl⟩
  | succ m ih =>
    let b' : Fin (m+1) → V := fun i => b i.castSucc
    let f' : Fin m → Chain G ℓ := fun e => f e.castSucc
    have hb' : Function.Injective b' := hb.comp (Fin.castSucc_injective _)
    have hf' (e : Fin m) : Function.Injective (f' e).val ∧ (f' e).val 0 = b' e.castSucc ∧
        (f' e).val (Fin.last ℓ) = b' e.succ := by
      simpa only [b',f',Fin.castSucc_succ] using hf e.castSucc
    obtain ⟨p,hp,hp0,hplast,hcover⟩ := ih b' f' hb' hf'
      (fun e r => havoid e.castSucc r.castSucc)
      (fun e d hed => hdis e.castSucc d.castSucc (fun h => hed ((Fin.castSucc_injective _) h)))
    let q := f (Fin.last m)
    have hq := hf (Fin.last m)
    have he : p.val (Fin.last (m*ℓ)) = q.val 0 := hplast.trans hq.2.1.symm
    have hnew : ∀ i, p.val i ≠ b (Fin.last (m+1)) := by
      intro i hi
      rcases hcover i with ⟨r,hr⟩ | ⟨e,he'⟩
      · have hh := hb (hr.symm.trans hi)
        have hh' := congrArg Fin.val hh
        dsimp only [Fin.val_castSucc,Fin.val_last] at hh'
        omega
      · have havoid' := havoid e.castSucc (Fin.last (m+1))
        exact havoid' (hi ▸ he')
    have hnewinterior : ∀ i, p.val i ∉ interior G q := by
      intro i hi
      rcases hcover i with ⟨r,hr⟩ | ⟨e,he'⟩
      · change p.val i = b r.castSucc at hr
        exact havoid (Fin.last m) r.castSucc (hr ▸ hi)
      · have hdis' := hdis e.castSucc (Fin.last m) (by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_castSucc,Fin.val_last] at this
          omega)
        exact Finset.disjoint_left.mp hdis' he' hi
    have hcross : ∀ i j, p.val i = q.val j → i = Fin.last (m*ℓ) ∧ j = 0 := by
      intro i j hij
      have hj : j = 0 := by
        rcases vertex_cases G q j with hj0 | hjlast | hjmid
        · exact hq.1 hj0
        · have hh : p.val i = b (Fin.last (m+1)) := by
            simpa only [Fin.succ_last] using hij.trans (hjlast.trans hq.2.2)
          exact (hnew i hh).elim
        · exact (hnewinterior i (hij.symm ▸ hjmid)).elim
      refine ⟨hp ?_,hj⟩
      rw [hj] at hij
      exact hij.trans he.symm
    rw [Nat.succ_mul]
    refine ⟨append G p q he,append_injective G p q he hp hq.1 hcross,?_,?_,?_⟩
    · simpa only [append_start,b',Fin.castSucc_zero] using hp0
    · simpa only [append_last,Fin.succ_last] using hq.2.2
    · intro i
      rcases append_vertex G p q he i with ⟨j,hj⟩ | ⟨j,hj⟩
      · rcases hcover j with ⟨r,hr⟩ | ⟨e,he'⟩
        · exact Or.inl ⟨r.castSucc,hj.trans hr⟩
        · exact Or.inr ⟨e.castSucc,hj.symm ▸ he'⟩
      · rcases vertex_cases G q j with hj0 | hjlast | hjmid
        · exact Or.inl ⟨(Fin.last m).castSucc,hj.trans (hj0.trans hq.2.1)⟩
        · exact Or.inl ⟨(Fin.last m).succ,hj.trans (hjlast.trans hq.2.2)⟩
        · exact Or.inr ⟨Fin.last m,hj.symm ▸ hjmid⟩

end ChainCounting

end -- ChainConcatenation

section -- HeavyShadow

/- Lifting theta graphs from the shadow of heavy admissible paths. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace HeavyShadow
set_option maxHeartbeats 2000000
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
noncomputable section

def heavy (B j : ℕ) (x y : V) : Prop :=
  x ≠ y ∧ threshold B j < (fiber G (threshold B) j x y).card

def graph (B j : ℕ) : SimpleGraph V where
  Adj := heavy G B j
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rw [← fiber_symmetric G (threshold B) j x y]
    exact h.2
  loopless := by constructor; intro x h; exact h.1 rfl


end
end HeavyShadow

end -- HeavyShadow

section -- AdmissibleChainCounts

/- Prefix-sensitive counts for admissible paths with a fixed initial vertex. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace AdmissibleChainCounts
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

lemma prefix_bound (L : ℕ → ℕ) (n D : ℕ) (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (i : Fin (n+1)) (hi : i.val<n) (v : V) :
    (P.filter (fun p => p.val i=v)).card≤L i.val*D^(n-i.val) := by
  let A := P.filter (fun p => p.val i=v)
  let left (p : A) : {q // q∈goodFiber H L i.val x v} := by
    refine ⟨segment H p.val 0 i.val (by omega),?_⟩
    obtain ⟨hp,hx⟩ := hP p.val (mem_filter.mp p.property).1
    apply (mem_goodFiber H L i.val x v _).mpr
    refine ⟨hp.2 0 i.val hi (by omega),hx,?_⟩
    simpa only [segment_apply,Fin.val_last,Nat.zero_add] using (mem_filter.mp p.property).2
  let right (p : A) : From H v (n-i.val) :=
    ⟨segment H p.val i.val (n-i.val) (by omega),by simpa using (mem_filter.mp p.property).2⟩
  let f (p : A) := (left p,right p)
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply split_injective H (show i.val+(n-i.val)=n by omega)
    exact congrArg (fun z : {q // q∈goodFiber H L i.val x v} × From H v (n-i.val) =>
      (z.1.val,z.2.val)) he
  calc
    _ = Fintype.card A := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ({q // q∈goodFiber H L i.val x v} × From H v (n-i.val)) :=
      Fintype.card_le_of_injective f hf
    _ = (goodFiber H L i.val x v).card*Fintype.card (From H v (n-i.val)) := by simp
    _ ≤ _ := Nat.mul_le_mul (goodFiber_le H L _ _ _) (from_le H D hD _ _)

lemma two_coordinates_bound (L : ℕ → ℕ) (n D : ℕ) (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (a b : Fin (n+1)) (hab : a.val<b.val) (v w : V) :
    (P.filter (fun p => p.val a=v ∧ p.val b=w)).card≤L a.val*D^(n-a.val-1) := by
  let A := P.filter (fun p => p.val a=v ∧ p.val b=w)
  let i : Fin (n-a.val) := ⟨b.val-a.val-1,by omega⟩
  let left (p : A) : {q // q∈goodFiber H L a.val x v} := by
    refine ⟨segment H p.val 0 a.val (by omega),?_⟩
    obtain ⟨hp,hx⟩ := hP p.val (mem_filter.mp p.property).1
    apply (mem_goodFiber H L a.val x v _).mpr
    refine ⟨hp.2 0 a.val (by omega) (by omega),hx,?_⟩
    simpa only [segment_apply,Fin.val_last,Nat.zero_add] using (mem_filter.mp p.property).2.1
  let right (p : A) : {q : From H v (n-a.val) // q.val.val i.succ=w} := by
    refine ⟨⟨segment H p.val a.val (n-a.val) (by omega),?_⟩,?_⟩
    · simpa using (mem_filter.mp p.property).2.1
    · have he : (⟨a.val+i.succ.val,by omega⟩ : Fin (n+1))=b := by
        apply Fin.ext
        dsimp only [i,Fin.val_succ]
        omega
      simpa only [segment_apply,he] using (mem_filter.mp p.property).2.2
  let f (p : A) := (left p,right p)
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply split_injective H (show a.val+(n-a.val)=n by omega)
    exact congrArg (fun z : {q // q∈goodFiber H L a.val x v} ×
      {q : From H v (n-a.val) // q.val.val i.succ=w} => (z.1.val,z.2.val.val)) he
  calc
    _ = Fintype.card A := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ({q // q∈goodFiber H L a.val x v} ×
        {q : From H v (n-a.val) // q.val.val i.succ=w}) := Fintype.card_le_of_injective f hf
    _ = (goodFiber H L a.val x v).card*Fintype.card {q : From H v (n-a.val) // q.val.val i.succ=w} := by simp
    _ ≤ _ := Nat.mul_le_mul (goodFiber_le H L _ _ _) (ChainCounting.coordinate_le H D hD _ _ _ i)

lemma index_image_bound (n D : ℕ) (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, p.val 0=x) (hD : ∀ v, H.degree v≤D) (i : Fin (n+1)) :
    (P.image (fun p => p.val i)).card≤D^i.val := by
  let f (p : P) : From H x i.val := ⟨segment H p.val 0 i.val (by omega),hP p.val p.property⟩
  have hsub : P.image (fun p => p.val i) ⊆ univ.image (fun q : From H x i.val => q.val.val (Fin.last i.val)) := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨f ⟨p,hp⟩,mem_univ _,by simp only [f,segment_apply,Fin.val_last,Nat.zero_add]⟩
  exact (card_le_card hsub).trans (card_image_le.trans (card_univ.trans_le (from_le H D hD _ _)))

end
end AdmissibleChainCounts

end -- AdmissibleChainCounts

section -- FiniteWeightedCommon

/- Weighted common-neighborhood selection with injective ordered choices. -/
open Finset
namespace FiniteWeightedCommon
set_option maxHeartbeats 2000000
universe u v
noncomputable section
variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
local instance : DecidableEq Y := Classical.decEq _

def tuples (S : Finset Y) (k : ℕ) : Finset (Fin k → Y) :=
  univ.filter (fun f => Function.Injective f ∧ ∀ i, f i∈S)

lemma tuples_card (S : Finset Y) (k : ℕ) :
    (tuples S k).card=(univ.filter (fun f : Fin k → S => Function.Injective f)).card := by
  classical
  apply card_bij (fun f hf i => (⟨f i,(mem_filter.mp hf).2.2 i⟩ : S))
  · intro f hf
    exact mem_filter.mpr ⟨mem_univ _,fun i j h => (mem_filter.mp hf).2.1 (congrArg Subtype.val h)⟩
  · intro f hf g hg h
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro f hf
    refine ⟨fun i => (f i).val,mem_filter.mpr ⟨mem_univ _,?_,fun i => (f i).property⟩,rfl⟩
    intro i j h
    exact (mem_filter.mp hf).2 (Subtype.ext h)

lemma tuples_lower (S : Finset Y) (k d : ℕ) (hk : 0<k)
    (hd : 2*k^2≤d) (hS : d≤S.card) : d^k≤2*(tuples S k).card := by
  classical
  rw [tuples_card]
  have hb := KSTUpper.noninjective_count (V := S) k
  have hs := card_filter_add_card_filter_not (s := (univ : Finset (Fin k → S))) Function.Injective
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] at hb hs
  have hm := Nat.mul_le_mul_right (S.card^(k-1)) (hd.trans hS)
  have hp : S.card*S.card^(k-1)=S.card^k := by rw [← pow_succ',Nat.sub_add_cancel hk]
  have hl : d^k≤S.card^k := Nat.pow_le_pow_left hS k
  nlinarith only [hb,hs,hm,hp,hl]

variable (N : X → Finset Y) (w : X → ℕ)

def weight (k : ℕ) (f : Fin k → Y) : ℕ :=
  ∑ x, if ∀ i, f i∈N x then w x else 0

lemma weighted_count (k : ℕ) :
    (∑ f ∈ univ.filter (fun f : Fin k → Y => Function.Injective f), weight N w k f)=
      ∑ x, w x*(tuples (N x) k).card := by
  classical
  simp only [weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [tuples,card_filter,mul_sum]
  simp only [sum_filter]
  apply sum_congr rfl
  intro f _
  split_ifs <;> simp_all

lemma exists_weight (k d K : ℕ) (hk : 0<k) (hd : 2*k^2≤d)
    (hN : ∀ x, 0<w x → d≤(N x).card)
    (hlarge : 2*K*Fintype.card Y^k < d^k*(∑ x, w x)) :
    ∃ f : Fin k → Y, Function.Injective f ∧ K<weight N w k f := by
  classical
  by_contra hn
  push_neg at hn
  have hup : (∑ f ∈ univ.filter (fun f : Fin k → Y => Function.Injective f), weight N w k f)≤
      Fintype.card Y^k*K := by
    calc
      _ ≤ ∑ _f ∈ univ.filter (fun f : Fin k → Y => Function.Injective f), K :=
        sum_le_sum (fun f hf => hn f (mem_filter.mp hf).2)
      _ ≤ Fintype.card Y^k*K := by
        simp only [sum_const,nsmul_eq_mul]
        exact Nat.mul_le_mul_right K (card_filter_le _ _ |>.trans_eq (by simp))
  have hlo : d^k*(∑ x, w x)≤2*(∑ x, w x*(tuples (N x) k).card) := by
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro x _
    by_cases hw : w x=0
    · simp [hw]
    · have hh := Nat.mul_le_mul_left (w x) (tuples_lower (N x) k d hk hd (hN x (Nat.pos_of_ne_zero hw)))
      nlinarith only [hh]
  rw [weighted_count] at hup
  nlinarith only [hup,hlo,hlarge]

end
end FiniteWeightedCommon

end -- FiniteWeightedCommon

section -- FiniteDenseWeightedLink

/- A dense weighted bipartite relation has a useful weighted fan. -/
open Finset
namespace FiniteDenseWeightedLink
set_option maxHeartbeats 2500000
universe u v
noncomputable section
variable {A : Type u} {Z : Type v} [Fintype A] [Fintype Z]
local instance : DecidableEq Z := Classical.decEq _

lemma select (N : Z → Finset A) (m : Z → ℕ) (j d D : ℕ) (hj : 2≤j)
    (hA : Fintype.card A≤D) (hm : (∑ z, m z)≤D^(j-1))
    (hE : 2*d*D^(j-1)<∑ z, m z*(N z).card) :
    ∃ a : A, ∃ T : Finset Z,
      (∀ z∈T, a∈N z ∧ d≤((N z).erase a).card) ∧
      d*D^(j-2)<∑ z∈T, m z := by
  let w (a : A) (z : Z) := if d<(N z).card ∧ a∈N z then m z else 0
  have hrow : (∑ a, ∑ z, w a z)=∑ z, if d<(N z).card then m z*(N z).card else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    by_cases hz : d<(N z).card
    · simp only [w,hz,true_and,if_true]
      rw [sum_ite_mem]
      simp [mul_comm]
    · simp [w,hz]
  have hpoint (z : Z) : m z*(N z).card≤d*m z+(if d<(N z).card then m z*(N z).card else 0) := by
    split_ifs with hz
    · omega
    · have hh := Nat.mul_le_mul_left (m z) (Nat.le_of_not_gt hz)
      nlinarith only [hh]
  have hb := sum_le_sum (s := (univ : Finset Z)) (fun z _ => hpoint z)
  rw [sum_add_distrib,← mul_sum,← hrow] at hb
  have hm' := Nat.mul_le_mul_left d hm
  have hhigh : d*D^(j-1)<∑ a, ∑ z, w a z := by nlinarith only [hE,hb,hm']
  have hex : ∃ a : A, d*D^(j-2)<∑ z, w a z := by
    by_contra hn
    push_neg at hn
    have hh : (∑ a, ∑ z, w a z)≤Fintype.card A*(d*D^(j-2)) := by
      calc
        _ ≤ ∑ _a : A, d*D^(j-2) := sum_le_sum (fun a _ => hn a)
        _ = _ := by simp
    have hscale := Nat.mul_le_mul_right (d*D^(j-2)) hA
    have he : D*(d*D^(j-2))=d*D^(j-1) := by
      rw [mul_left_comm,← pow_succ']
      congr 2
      omega
    rw [he] at hscale
    omega
  obtain ⟨a,ha⟩ := hex
  let T := univ.filter (fun z => d<(N z).card ∧ a∈N z)
  refine ⟨a,T,?_,?_⟩
  · intro z hz
    have hz' := (mem_filter.mp hz).2
    refine ⟨hz'.2,?_⟩
    have he := card_erase_add_one hz'.2
    omega
  · simpa only [T,sum_filter,w] using ha

end
end FiniteDenseWeightedLink

end -- FiniteDenseWeightedLink

section -- WeightedAdmissibleSelection

/- Threshold normalization for weighted common-neighborhood selection. -/
open Finset
namespace WeightedAdmissibleSelection
set_option maxHeartbeats 2500000
universe u v
noncomputable section
variable {A : Type u} {Z : Type v} [Fintype A] [Fintype Z]
local instance : DecidableEq Z := Classical.decEq _

lemma normalize (s d D κ K L J : ℕ) (hd : 0<d) (hD : D≤κ*d)
    (hJ : 2*K*κ^(s+1)*L^2<J) :
    2*K*L^2*D^(s+1)<J*d^(s+1) := by
  have hp := Nat.pow_le_pow_left hD (s+1)
  rw [mul_pow] at hp
  have hh := Nat.mul_lt_mul_of_pos_right hJ (Nat.pow_pos (n := s+1) hd)
  have hm := Nat.mul_le_mul_left (2*K*L^2) hp
  nlinarith only [hh,hm]

lemma select (N : Z → Finset A) (m w : Z → ℕ) (T : Finset Z)
    (j s d D κ K L J : ℕ) (hj : 2≤j) (hs : 0<s) (hDpos : 0<D) (hL : 0<L)
    (hd : 2*s^2≤d) (hA : Fintype.card A≤D) (hD : D≤κ*d)
    (hJ : 2*K*κ^(s+1)*L^2<J)
    (hm : ∀ z∈T, m z≤L) (hw : ∀ z∈T, J≤w z)
    (hN : ∀ z∈T, d≤(N z).card)
    (hT : d*D^(j-2)<∑ z∈T, m z) :
    ∃ f : Fin s → A, Function.Injective f ∧
      K*L*D^(j-1)<∑ z∈T, if ∀ i, f i∈N z then w z else 0 := by
  let w' (z : Z) := if z∈T then w z else 0
  have hdpos : 0<d := by nlinarith
  have hweight : J*(∑ z∈T, m z)≤L*(∑ z, w' z) := by
    rw [mul_sum,show (∑ z, w' z)=∑ z∈T, w z by simp [w',← sum_filter],mul_sum]
    apply sum_le_sum
    intro z hz
    have hh := Nat.mul_le_mul (hm z hz) (hw z hz)
    nlinarith only [hh]
  have hnorm := normalize s d D κ K L J hdpos hD hJ
  have hnorm' := Nat.mul_lt_mul_of_pos_right hnorm (Nat.pow_pos (n := j-2) hDpos)
  have hT' := Nat.mul_le_mul_left J hT.le
  have hT'' := Nat.mul_le_mul_left (d^s) (hT'.trans hweight)
  have hpow : D^(s+1)*D^(j-2)=D^(j-1)*D^s := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  have hdpow : d^(s+1)=d^s*d := pow_succ _ _
  have hlargeD : (2*(K*L*D^(j-1))*D^s)*L < (d^s*(∑ z, w' z))*L := by
    rw [mul_assoc (2*K*L^2) (D^(s+1)),hpow,hdpow] at hnorm'
    nlinarith only [hnorm',hT'']
  have hlarge : 2*(K*L*D^(j-1))*Fintype.card A^s<d^s*(∑ z, w' z) := by
    have hh := (Nat.mul_lt_mul_right hL).mp hlargeD
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA s)).trans_lt hh
  obtain ⟨f,hf,hwf⟩ := FiniteWeightedCommon.exists_weight N w' s d (K*L*D^(j-1)) hs hd
    (by
      intro z hz
      have hzT : z∈T := by by_contra hn; simp [w',hn] at hz
      exact hN z hzT) hlarge
  refine ⟨f,hf,?_⟩
  have he : FiniteWeightedCommon.weight N w' s f=∑ z∈T, if ∀ i, f i∈N z then w z else 0 := by
    calc
      _ = ∑ z, if z∈T then (if ∀ i, f i∈N z then w z else 0) else 0 := by
        apply sum_congr rfl
        intro z _
        dsimp only [w']
        split_ifs <;> rfl
      _ = _ := by rw [sum_ite_mem]; simp
  rwa [he] at hwf

end
end WeightedAdmissibleSelection

end -- WeightedAdmissibleSelection

section -- AdmissibleHeavyLinks

/- Weighted local links of admissible heavy paths. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace AdmissibleHeavyLinks
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _
local instance (v : V) : DecidableEq (H.neighborSet v) := Classical.decEq _

def bad (B j : ℕ) : Finset (Chain H j) := by
  classical
  exact univ.filter (fun p => Admissible H (threshold B) j p ∧
    HeavyShadow.heavy H B j (p.val 0) (p.val (Fin.last j)))

lemma mem_bad (B j : ℕ) (p : Chain H j) : p∈bad H B j ↔
    Admissible H (threshold B) j p ∧ HeavyShadow.heavy H B j (p.val 0) (p.val (Fin.last j)) := by
  classical
  simp only [bad,mem_filter,mem_univ,true_and]

def neighbors (B j : ℕ) (v z : V) : Finset (H.neighborSet v) := by
  classical
  exact univ.filter (fun a => HeavyShadow.heavy H B j a.val z)

def multiplicity (B j : ℕ) (v z : V) : ℕ :=
  (goodFiber H (threshold B) (j-1) v z).card

def mass (B j : ℕ) (v : V) : ℕ := ∑ z, multiplicity H B j v z*(neighbors H B j v z).card

lemma multiplicity_le (B j : ℕ) (v z : V) : multiplicity H B j v z≤threshold B (j-1) :=
  goodFiber_le H (threshold B) _ _ _

lemma multiplicity_sum (B j D : ℕ) (hD : ∀ v, H.degree v≤D) (v : V) :
    (∑ z, multiplicity H B j v z)≤D^(j-1)  := by
  classical
  let Q := Σ z : V, {q // q∈goodFiber H (threshold B) (j-1) v z}
  let f : Q → From H v (j-1) := fun q =>
    ⟨q.2.val,((mem_goodFiber H (threshold B) (j-1) v q.1 q.2.val).mp q.2.property).2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨z,p⟩ ⟨w,q⟩ he
    have hpq : p.val=q.val := congrArg Subtype.val he
    have hz := ((mem_goodFiber H (threshold B) (j-1) v z p.val).mp p.property).2.2
    have hw := ((mem_goodFiber H (threshold B) (j-1) v w q.val).mp q.property).2.2
    have hzw : z=w := hz.symm.trans ((congrArg (fun p : Chain H (j-1) => p.val (Fin.last (j-1))) hpq).trans hw)
    subst w
    exact congrArg (Sigma.mk z) (Subtype.ext hpq)
  have hh := (Fintype.card_le_of_injective f hf).trans (from_le H D hD _ _)
  simpa only [Q,Fintype.card_sigma,Fintype.card_coe,multiplicity] using hh

lemma bad_le_mass (B j : ℕ) (hj : 2≤j) : (bad H B j).card≤∑ v, mass H B j v  := by
  classical
  let Bad := bad H B j
  let Q := Σ v : V, Σ z : V, {q // q∈goodFiber H (threshold B) (j-1) v z} × (neighbors H B j v z)
  let f (p : Bad) : Q := by
    let v := p.val.val ⟨1,by omega⟩
    let z := p.val.val (Fin.last j)
    have hp := (mem_filter.mp (show p.val∈bad H B j from p.property)).2
    refine ⟨v,z,⟨segment H p.val 1 (j-1) (by omega),?_⟩,⟨⟨p.val.val 0,?_⟩,?_⟩⟩
    · apply (mem_goodFiber H (threshold B) (j-1) v z _).mpr
      refine ⟨hp.1.2 1 (j-1) (by omega) (by omega),rfl,?_⟩
      apply congrArg p.val.val
      apply Fin.ext
      change 1+(j-1)=j
      omega
    · exact (p.val.property ⟨0,by omega⟩).symm
    · exact mem_filter.mpr ⟨mem_univ _,hp.2⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hfirst := congrArg (fun z : Q => z.2.2.2.val.val) he
    have htail := congrArg (fun z : Q => z.2.2.1.val) he
    by_cases hi : i.val=0
    · have hi' : i=0 := Fin.ext hi
      simpa only [hi'] using hfirst
    · have hh := congrArg (fun p : Chain H (j-1) => p.val ⟨i.val-1,by omega⟩) htail
      change p.val.val ⟨1+(i.val-1),by omega⟩=q.val.val ⟨1+(i.val-1),by omega⟩ at hh
      simpa only [show 1+(i.val-1)=i.val by omega] using hh
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Bad,Q,Fintype.card_coe,Fintype.card_sigma,Fintype.card_prod,mass,multiplicity] using hh

lemma dense_fan (B j d D : ℕ) (hj : 2≤j) (hD : ∀ v, H.degree v≤D) (v : V)
    (hlarge : 2*d*D^(j-1)< mass H B j v) :
    ∃ a : H.neighborSet v, ∃ T : Finset V,
      (∀ z∈T, HeavyShadow.heavy H B j a.val z ∧ d≤((neighbors H B j v z).erase a).card) ∧
      d*D^(j-2)<∑ z∈T, multiplicity H B j v z  := by
  classical
  obtain ⟨a,T,hT,hweight⟩ := FiniteDenseWeightedLink.select (neighbors H B j v) (multiplicity H B j v)
    j d D hj (by simpa only [H.card_neighborSet_eq_degree] using hD v) (multiplicity_sum H B j D hD v) hlarge
  refine ⟨a,T,?_,hweight⟩
  intro z hz
  refine ⟨(mem_filter.mp (hT z hz).1).2,?_⟩
  exact (hT z hz).2

end
end AdmissibleHeavyLinks

end -- AdmissibleHeavyLinks

section -- AdmissibleHubLightCount

/- Partition long injective paths into truncated-good paths and extensions of heavy subpaths. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace AdmissibleHubLightCount
set_option maxHeartbeats 2500000
universe u
noncomputable section
variable {V : Type u} [Fintype V]
local instance : DecidableEq V := Classical.decEq _
variable (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _

def badAt (k B : ℕ) (ij : Fin (k+4) × Fin (k+2)) : Finset (HubLightPaths.Path H k) :=
  if h : ij.1.val+ij.2.val≤k+3 then
    extensions H (k+3) ij.1.val ij.2.val h (AdmissibleHeavyLinks.bad H B ij.2.val)
  else ∅

lemma partition (k B : ℕ) :
    (GeneralThetaCounting.paths H (k+3)).card≤(HubLightPaths.good H k (threshold B)).card+
      ∑ ij : Fin (k+4) × Fin (k+2), (badAt H k B ij).card := by
  classical
  have hsub : GeneralThetaCounting.paths H (k+3)⊆HubLightPaths.good H k (threshold B) ∪
      univ.biUnion (badAt H k B) := by
    intro p hp
    have hinj := (mem_filter.mp hp).2
    by_cases hg : HubLightPaths.Good H k (threshold B) p
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hg⟩)
    · have hbad : ¬∀ a j : ℕ, (hj : j≤k+1) → (hlen : a+j≤k+3) →
          GoodChains.Good H (threshold B) j (segment H p a j hlen) := fun h => hg ⟨hinj,h⟩
      push_neg at hbad
      obtain ⟨a,j,hj,hlen,hbad⟩ := hbad
      obtain ⟨b,l,hbl,hadm,hheavy⟩ := bad_witness H (threshold B) j (segment H p a j hlen)
        (segment_injective H hinj a j hlen) hbad
      have hl : 2≤l := GeneralThetaCounting.heavy_length H B l _ _ hheavy
      have hlen' : a+b+l≤k+3 := by omega
      have hbad' : segment H p (a+b) l hlen'∈AdmissibleHeavyLinks.bad H B l := by
        apply (AdmissibleHeavyLinks.mem_bad H B l _).mpr
        have hinj' := segment_injective H hinj (a+b) l hlen'
        refine ⟨?_,hinj'.ne ?_,?_⟩
        · simpa only [segment_segment] using hadm
        · intro he
          have hh := congrArg Fin.val he
          change 0=l at hh
          omega
        · simpa only [segment_segment] using hheavy
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨(⟨a+b,by omega⟩,⟨l,by omega⟩),mem_univ _,?_⟩
      simp only [badAt,dif_pos hlen']
      exact mem_filter.mpr ⟨mem_univ _,hbad'⟩
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))

lemma badAt_le (k B D : ℕ) (hD : ∀ v, H.degree v≤D) (ij : Fin (k+4) × Fin (k+2)) :
    (badAt H k B ij).card≤(AdmissibleHeavyLinks.bad H B ij.2.val).card*D^(k+3-ij.2.val) := by
  dsimp only [badAt]
  split_ifs with h
  · exact extensions_le H D (k+3) ij.1.val ij.2.val hD h _
  · exact Nat.zero_le _

lemma count (k B d D : ℕ) (hd : ∀ v, d+(k+3)≤H.degree v) (hD : ∀ v, H.degree v≤D) :
    Fintype.card V*d^(k+3)≤(HubLightPaths.good H k (threshold B)).card+
      (k+4)*∑ j : Fin (k+2), (AdmissibleHeavyLinks.bad H B j.val).card*D^(k+3-j.val) := by
  have hh := (GeneralThetaCounting.paths_lower H d (k+3) hd).trans (partition H k B)
  have hs : (∑ ij : Fin (k+4) × Fin (k+2), (badAt H k B ij).card)≤
      (k+4)*∑ j : Fin (k+2), (AdmissibleHeavyLinks.bad H B j.val).card*D^(k+3-j.val) := by
    calc
      _ ≤ ∑ ij : Fin (k+4) × Fin (k+2), (AdmissibleHeavyLinks.bad H B ij.2.val).card*D^(k+3-ij.2.val) :=
        sum_le_sum (fun ij _ => badAt_le H k B D hD ij)
      _ = _ := by rw [Fintype.sum_prod_type]; simp
  exact hh.trans (Nat.add_le_add_left hs _)

lemma bad_small (B j : ℕ) (hj : j≤1) : AdmissibleHeavyLinks.bad H B j=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := ((AdmissibleHeavyLinks.mem_bad H B j p).mp hp).2.2
  have hl := GeneralThetaCounting.heavy_length H B j _ _ hh
  omega

end
end AdmissibleHubLightCount

end -- AdmissibleHubLightCount

section -- HubLightSelection

/- Select paths with distinct core endpoint pairs and pairwise disjoint core interiors. -/
open Finset SimpleGraph ChainCounting
namespace HubLightSelection
open HubLightPaths
set_option maxHeartbeats 2500000
universe u
noncomputable section
variable {V : Type u} [Fintype V]
local instance : DecidableEq V := Classical.decEq _
variable (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _

def labels (k : ℕ) (p : Path H k) : Finset ((V × V) ⊕ V) :=
  insert (Sum.inl (first H k p,last H k p)) (univ.image (fun i : Fin k => Sum.inr (middle H k p i)))

lemma labels_nonempty (k : ℕ) (p : Path H k) : (labels H k p).Nonempty := insert_nonempty _ _

lemma labels_card (k : ℕ) (p : Path H k) : (labels H k p).card≤k+1 := by
  apply (card_insert_le _ _).trans
  have hh := card_image_le (s := (univ : Finset (Fin k))) (f := fun i => (Sum.inr (middle H k p i) : (V × V) ⊕ V))
  simpa only [card_univ,Fintype.card_fin] using Nat.add_le_add_right hh 1

lemma pair_mem (k : ℕ) (p : Path H k) : Sum.inl (first H k p,last H k p)∈labels H k p := mem_insert_self _ _

lemma middle_mem (k : ℕ) (p : Path H k) (i : Fin k) : Sum.inr (middle H k p i)∈labels H k p :=
  mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,rfl⟩)

lemma incidence (k : ℕ) (L : ℕ → ℕ) (hL : Monotone L) (x y : V) (z : (V × V) ⊕ V) :
    ((links H k L x y).filter (fun p => z∈labels H k p)).card≤L (k+1)+k*(L (k+1))^2 := by
  cases z with
  | inl z =>
    have he : (links H k L x y).filter (fun p => Sum.inl z∈labels H k p)=
        (links H k L x y).filter (fun p => (first H k p,last H k p)=z) := by
      ext p
      simp [labels,eq_comm]
    rw [he]
    exact (pair_bound H k L x y z).trans (Nat.le_add_right _ _)
  | inr z =>
    let P (i : Fin k) := (links H k L x y).filter (fun p => middle H k p i=z)
    have hsub : (links H k L x y).filter (fun p => Sum.inr z∈labels H k p)⊆univ.biUnion P := by
      intro p hp
      have hmem := (mem_filter.mp hp).2
      simp only [labels,mem_insert,Sum.inr_ne_inl,false_or,mem_image,mem_univ,true_and,Sum.inr.injEq] at hmem
      obtain ⟨i,hi⟩ := hmem
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨(mem_filter.mp hp).1,hi⟩⟩
    have hh : ((links H k L x y).filter (fun p => Sum.inr z∈labels H k p)).card≤k*(L (k+1))^2 := by
      calc
        _ ≤ (univ.biUnion P).card := card_le_card hsub
        _ ≤ ∑ i, (P i).card := card_biUnion_le
        _ ≤ ∑ _i : Fin k, (L (k+1))^2 := sum_le_sum (fun i _ => coordinate_le H k L hL x y z i)
        _ = _ := by simp
    exact hh.trans (Nat.le_add_left _ _)

lemma select (k : ℕ) (L : ℕ → ℕ) (hL : Monotone L) (x y : V)
    (P : Finset (Path H k)) (hP : P⊆links H k L x y) :
    ∃ Q : Finset (Path H k), Q⊆P ∧
      Set.InjOn (fun p : Path H k => (first H k p,last H k p)) Q ∧
      (∀ p∈Q, ∀ q∈Q, ∀ i j : Fin k, middle H k p i=middle H k q j → p=q ∧ i=j) ∧
      P.card≤((k+1)*(L (k+1)+k*(L (k+1))^2))*Q.card := by
  obtain ⟨Q,hQ,hdis,hcard⟩ := FiniteDisjointSubfamily.select P (labels H k) (k+1)
    (L (k+1)+k*(L (k+1))^2) (fun p _ => labels_nonempty H k p) (fun p _ => labels_card H k p)
    (fun z => (card_le_card (filter_subset_filter _ hP)).trans (incidence H k L hL x y z))
  refine ⟨Q,hQ,?_,?_,hcard⟩
  · intro p hp q hq he
    dsimp only at he
    by_contra hn
    apply disjoint_left.mp (hdis p hp q hq hn) (pair_mem H k p)
    rw [he]
    exact pair_mem H k q
  · intro p hp q hq i j he
    have hpq : p=q := by
      by_contra hn
      apply disjoint_left.mp (hdis p hp q hq hn) (middle_mem H k p i)
      rw [he]
      exact middle_mem H k q j
    subst q
    refine ⟨rfl,?_⟩
    have hinj := ((mem_links H k L x y p).mp (hP (hQ hp))).1.1
    have hh := congrArg Fin.val (hinj he)
    apply Fin.ext
    change i.val+2=j.val+2 at hh
    omega

end
end HubLightSelection

end -- HubLightSelection

section -- SelectedHubLink

/- A selected family of pinned paths supplies a copy of the corresponding hub replacement. -/
open Finset SimpleGraph ChainCounting
namespace SelectedHubLink
set_option maxHeartbeats 3000000
universe u
noncomputable section
variable {V : Type u} [Fintype V]
local instance : DecidableEq V := Classical.decEq _
variable (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _
variable (k : ℕ) (Q : Finset (HubLightPaths.Path H k))

def X : Finset V := Q.image (HubLightPaths.first H k)
def Y : Finset V := Q.image (HubLightPaths.last H k)
abbrev Vertex := X H k Q ⊕ Y H k Q

def first (p : Q) : X H k Q := ⟨HubLightPaths.first H k p.val,mem_image.mpr ⟨p.val,p.property,rfl⟩⟩
def last (p : Q) : Y H k Q := ⟨HubLightPaths.last H k p.val,mem_image.mpr ⟨p.val,p.property,rfl⟩⟩
def eval : Vertex H k Q → V := Sum.elim Subtype.val Subtype.val

def relation (a : X H k Q) (b : Y H k Q) : Prop :=
  ∃ p∈Q, a.val=HubLightPaths.first H k p ∧ b.val=HubLightPaths.last H k p

def graph : SimpleGraph (Vertex H k Q) := SuspensionBounds.biGraph (relation H k Q)
def color : (graph H k Q).Coloring (Fin 2) := SuspensionBounds.biColor _

def edge (p : Q) : GraphSubdivision.Edge (graph H k Q) :=
  ⟨s(Sum.inl (first H k Q p),Sum.inr (last H k Q p)),p.val,p.property,rfl,rfl⟩

lemma edge_injective (hp : Set.InjOn (fun p : HubLightPaths.Path H k =>
      (HubLightPaths.first H k p,HubLightPaths.last H k p)) Q) : Function.Injective (edge H k Q) := by
  intro p q he
  have hh := congrArg Subtype.val he
  rcases Sym2.eq_iff.mp hh with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · apply Subtype.ext
    exact hp p.property q.property (Prod.ext
      (congrArg Subtype.val (Sum.inl.inj hl)) (congrArg Subtype.val (Sum.inr.inj hr)))
  · exact (Sum.inl_ne_inr hl).elim

lemma edge_surjective : Function.Surjective (edge H k Q) := by
  intro e
  have hout : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
  have ha : (graph H k Q).Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1,e.val.out.2)∈(graph H k Q).edgeSet
    rw [hout]
    exact e.property
  cases h₁ : e.val.out.1 with
  | inl a => cases h₂ : e.val.out.2 with
    | inl b => rw [h₁,h₂] at ha; exact ha.elim
    | inr b =>
      rw [h₁,h₂] at ha
      obtain ⟨p,hp,hl,hr⟩ := ha
      refine ⟨⟨p,hp⟩,Subtype.ext ?_⟩
      apply Eq.trans _ hout
      rw [h₁,h₂]
      exact congrArg₂ (fun a b => s(a,b)) (congrArg Sum.inl (Subtype.ext hl.symm))
        (congrArg Sum.inr (Subtype.ext hr.symm))
  | inr a => cases h₂ : e.val.out.2 with
    | inl b =>
      rw [h₁,h₂] at ha
      obtain ⟨p,hp,hl,hr⟩ := ha
      refine ⟨⟨p,hp⟩,Subtype.ext ?_⟩
      apply Eq.trans _ hout
      rw [h₁,h₂]
      exact Sym2.eq_iff.mpr (Or.inr
        ⟨congrArg Sum.inl (Subtype.ext hl.symm),congrArg Sum.inr (Subtype.ext hr.symm)⟩)
    | inr b => rw [h₁,h₂] at ha; exact ha.elim

def edgeEquiv (hp : Set.InjOn (fun p : HubLightPaths.Path H k =>
      (HubLightPaths.first H k p,HubLightPaths.last H k p)) Q) :
    Q ≃ GraphSubdivision.Edge (graph H k Q) :=
  Equiv.ofBijective _ ⟨edge_injective H k Q hp,edge_surjective H k Q⟩

variable (L : ℕ → ℕ) (x y : V) (hQ : Q⊆HubLightPaths.links H k L x y)

include hQ in
lemma prop (p : Q) : HubLightPaths.Good H k L p.val ∧ p.val.val 0=x ∧ p.val.val (Fin.last (k+3))=y :=
  (HubLightPaths.mem_links H k L x y p.val).mp (hQ p.property)

include hQ in
lemma first_adj (p : Q) : H.Adj x (first H k Q p).val := by
  have hh := prop H k Q L x y hQ p
  rw [← hh.2.1]
  exact p.val.property 0

include hQ in
lemma last_adj (p : Q) : H.Adj y (last H k Q p).val := by
  have hh := prop H k Q L x y hQ p
  rw [← hh.2.2]
  exact (p.val.property ⟨k+2,by omega⟩).symm

include hQ in
lemma old_avoids (p : Q) :
    x≠(first H k Q p).val ∧ y≠(first H k Q p).val ∧
    x≠(last H k Q p).val ∧ y≠(last H k Q p).val := by
  have hh := prop H k Q L x y hQ p
  have hn0 : (0 : Fin (k+4))≠⟨1,by omega⟩ := by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_mk,Fin.val_last] at hh; omega
  have hn1 : (Fin.last (k+3) : Fin (k+4))≠⟨1,by omega⟩ := by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_mk,Fin.val_last] at hh; omega
  have hn2 : (0 : Fin (k+4))≠⟨k+2,by omega⟩ := by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_mk,Fin.val_last] at hh; omega
  have hn3 : (Fin.last (k+3) : Fin (k+4))≠⟨k+2,by omega⟩ := by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_mk,Fin.val_last] at hh; omega
  refine ⟨?_,?_,?_,?_⟩
  · exact fun h => hh.1.1.ne hn0 (hh.2.1.trans h)
  · exact fun h => hh.1.1.ne hn1 (hh.2.2.trans h)
  · exact fun h => hh.1.1.ne hn2 (hh.2.1.trans h)
  · exact fun h => hh.1.1.ne hn3 (hh.2.2.trans h)

include hQ in
lemma middle_avoids (p : Q) (i : Fin k) :
    x≠HubLightPaths.middle H k p.val i ∧ y≠HubLightPaths.middle H k p.val i := by
  have hh := prop H k Q L x y hQ p
  have hn0 : (0 : Fin (k+4))≠⟨i.val+2,by omega⟩ := by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_mk,Fin.val_last] at hh; omega
  have hn1 : (Fin.last (k+3) : Fin (k+4))≠⟨i.val+2,by omega⟩ := by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_mk,Fin.val_last] at hh; omega
  exact ⟨fun h => hh.1.1.ne hn0 (hh.2.1.trans h),fun h => hh.1.1.ne hn1 (hh.2.2.trans h)⟩

include hQ in
lemma copy (hne : Q.Nonempty) (b : V → Fin 2)
    (hb : ∀ p∈Q, b (HubLightPaths.first H k p)=0 ∧ b (HubLightPaths.last H k p)=1)
    (hp : Set.InjOn (fun p : HubLightPaths.Path H k => (HubLightPaths.first H k p,HubLightPaths.last H k p)) Q)
    (hm : ∀ p∈Q, ∀ q∈Q, ∀ i j : Fin k, HubLightPaths.middle H k p i=HubLightPaths.middle H k q j → p=q ∧ i=j)
    (hsep : ∀ p∈Q, ∀ q∈Q, ∀ i : Fin k,
      HubLightPaths.first H k p≠HubLightPaths.middle H k q i ∧
      HubLightPaths.last H k p≠HubLightPaths.middle H k q i) :
    HubPathSubdivision.graph (color H k Q) k ⊑ H := by
  let e := edgeEquiv H k Q hp
  let ev := eval H k Q
  let hubs : Fin 2 → V := fun i => if i=0 then x else y
  let p (a : GraphSubdivision.Edge (graph H k Q)) : Chain H (k+1) := HubLightPaths.core H k (e.symm a).val
  have hmid (a : GraphSubdivision.Edge (graph H k Q)) (i : Fin k) :
      (p a).val i.succ.castSucc=HubLightPaths.middle H k (e.symm a).val i := by
    simp only [p,HubLightPaths.core,segment_apply,Fin.val_castSucc,Fin.val_succ,HubLightPaths.middle]
    apply congrArg (e.symm a).val.val
    apply Fin.ext
    change 1+(i.val+1)=i.val+2
    omega
  have hevinj : Function.Injective ev := Subtype.val_injective.sumElim Subtype.val_injective (by
    intro a d he
    obtain ⟨r,hr,her⟩ := mem_image.mp a.property
    obtain ⟨s,hs,hes⟩ := mem_image.mp d.property
    have hh := congrArg b (her.trans (he.trans hes.symm))
    rw [(hb r hr).1,(hb s hs).2] at hh
    exact (by decide : (0 : Fin 2)≠1) hh)
  obtain ⟨p₀,hp₀⟩ := hne
  have hh₀ := prop H k Q L x y hQ ⟨p₀,hp₀⟩
  have hxy : x≠y := by
    intro he
    have hh := congrArg Fin.val (hh₀.1.1 (hh₀.2.1.trans (he.trans hh₀.2.2.symm)))
    change 0=k+3 at hh
    omega
  have hzinj : Function.Injective hubs := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hxy he).elim
    · exact (hxy he.symm).elim
    · rfl
  have hminj : Function.Injective (fun a : GraphSubdivision.Edge (graph H k Q) × Fin k => (p a.1).val a.2.succ.castSucc) := by
    rintro ⟨a,i⟩ ⟨d,j⟩ he
    dsimp only at he
    rw [hmid,hmid] at he
    have hh := hm (e.symm a).val (e.symm a).property (e.symm d).val (e.symm d).property i j he
    exact Prod.ext (e.symm.injective (Subtype.ext hh.1)) hh.2
  have hzf (i : Fin 2) (w : Vertex H k Q) : hubs i≠ev w := by
    cases w with
    | inl w =>
      obtain ⟨q,hq,he⟩ := mem_image.mp w.property
      have hh := old_avoids H k Q L x y hQ ⟨q,hq⟩
      fin_cases i
      · exact fun h => hh.1 (h.trans he.symm)
      · exact fun h => hh.2.1 (h.trans he.symm)
    | inr w =>
      obtain ⟨q,hq,he⟩ := mem_image.mp w.property
      have hh := old_avoids H k Q L x y hQ ⟨q,hq⟩
      fin_cases i
      · exact fun h => hh.2.2.1 (h.trans he.symm)
      · exact fun h => hh.2.2.2 (h.trans he.symm)
  have hzm (i : Fin 2) (a : GraphSubdivision.Edge (graph H k Q)) (j : Fin k) : hubs i≠(p a).val j.succ.castSucc := by
    rw [hmid]
    have hh := middle_avoids H k Q L x y hQ (e.symm a) j
    fin_cases i
    · exact hh.1
    · exact hh.2
  have hfm (w : Vertex H k Q) (a : GraphSubdivision.Edge (graph H k Q)) (j : Fin k) : ev w≠(p a).val j.succ.castSucc := by
    rw [hmid]
    cases w with
    | inl w =>
      obtain ⟨q,hq,he⟩ := mem_image.mp w.property
      exact fun h => (hsep q hq (e.symm a).val (e.symm a).property j).1 (he.trans h)
    | inr w =>
      obtain ⟨q,hq,he⟩ := mem_image.mp w.property
      exact fun h => (hsep q hq (e.symm a).val (e.symm a).property j).2 (he.trans h)
  have hend (a : GraphSubdivision.Edge (graph H k Q)) :
      ev (ColoredEdges.left (color H k Q) a)=HubLightPaths.first H k (e.symm a).val ∧
      ev (ColoredEdges.right (color H k Q) a)=HubLightPaths.last H k (e.symm a).val := by
    have hl := ColoredEdges.left_unique (color H k Q) (e (e.symm a))
      (Sym2.mem_mk_left (Sum.inl (first H k Q (e.symm a))) (Sum.inr (last H k Q (e.symm a)))) rfl
    have hr := ColoredEdges.right_unique (color H k Q) (e (e.symm a))
      (Sym2.mem_mk_right (Sum.inl (first H k Q (e.symm a))) (Sum.inr (last H k Q (e.symm a)))) rfl
    rw [e.apply_symm_apply] at hl hr
    exact ⟨(congrArg ev hl).symm,(congrArg ev hr).symm⟩
  refine ⟨HubPathCopies.copyOfChains (color H k Q) H k hubs ev p hzinj hevinj hminj hzf hzm hfm ?_ ?_ ?_⟩
  · intro a
    exact (hend a).1.symm
  · intro a
    have hh := (hend a).2.symm
    simpa only [p,HubLightPaths.core,segment_apply,Fin.val_last,HubLightPaths.last,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
  · intro i w hw
    cases w with
    | inl w =>
      obtain ⟨q,hq,he⟩ := mem_image.mp w.property
      have hi : i=0 := hw.symm
      subst i
      change H.Adj x w.val
      rw [← he]
      exact first_adj H k Q L x y hQ ⟨q,hq⟩
    | inr w =>
      obtain ⟨q,hq,he⟩ := mem_image.mp w.property
      have hi : i=1 := hw.symm
      subst i
      change H.Adj y w.val
      rw [← he]
      exact last_adj H k Q L x y hQ ⟨q,hq⟩

include hQ in
lemma vertices_card (D : ℕ) (hD : ∀ v, H.degree v≤D) : Fintype.card (Vertex H k Q)≤2*D := by
  have hx : (X H k Q).card≤H.degree x := by
    rw [← H.card_neighborFinset_eq_degree]
    apply card_le_card
    intro w hw
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
    exact (H.mem_neighborFinset _ _).mpr (first_adj H k Q L x y hQ ⟨p,hp⟩)
  have hy : (Y H k Q).card≤H.degree y := by
    rw [← H.card_neighborFinset_eq_degree]
    apply card_le_card
    intro w hw
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
    exact (H.mem_neighborFinset _ _).mpr (last_adj H k Q L x y hQ ⟨p,hp⟩)
  simp only [Fintype.card_sum,Fintype.card_coe]
  have hdx := hD x
  have hdy := hD y
  omega

end
end SelectedHubLink

end -- SelectedHubLink

section -- OrientedRolePartition

/- A quarter of any finite family of ordered distinct pairs has prescribed
roles under a suitable two-class vertex partition. -/
open Finset
namespace OrientedRolePartition
set_option maxHeartbeats 1500000
universe u v
noncomputable section
variable {A : Type u} {V : Type v} [Fintype V]
local instance : DecidableEq V := Classical.decEq _

lemma differing (P : Finset A) (x y : A → V) (hxy : ∀ a∈P, x a≠y a) :
    ∃ c : V → Bool, P.card≤2*(P.filter (fun a => c (x a)≠c (y a))).card := by
  have hs : (∑ c : V → Bool, 2*(P.filter (fun a => c (x a)≠c (y a))).card)=
      Fintype.card (V → Bool)*P.card := by
    calc
      _ = ∑ c : V → Bool, ∑ a∈P, 2*(if c (x a)≠c (y a) then 1 else 0) := by
        simp only [card_filter,mul_sum]
      _ = ∑ a∈P, ∑ c : V → Bool, 2*(if c (x a)≠c (y a) then 1 else 0) := sum_comm
      _ = ∑ _a∈P, Fintype.card (V → Bool) := by
        apply sum_congr rfl
        intro a ha
        rw [← mul_sum,← card_filter]
        exact MaxCut.half_colorings (x a) (y a) (hxy a ha)
      _ = _ := by simp; ring
  have hh : (∑ _c : V → Bool, P.card)≤∑ c : V → Bool, 2*(P.filter (fun a => c (x a)≠c (y a))).card := by
    rw [hs]
    simp
  obtain ⟨c,_,hc⟩ := exists_le_of_sum_le (by simp : (univ : Finset (V → Bool)).Nonempty) hh
  exact ⟨c,hc⟩

lemma exists_roles (P : Finset A) (x y : A → V) (hxy : ∀ a∈P, x a≠y a) :
    ∃ b : V → Fin 2, P.card≤4*(P.filter (fun a => b (x a)=0 ∧ b (y a)=1)).card := by
  obtain ⟨c,hc⟩ := differing P x y hxy
  let A₀ := P.filter (fun a => c (x a)=false ∧ c (y a)=true)
  let A₁ := P.filter (fun a => c (x a)=true ∧ c (y a)=false)
  have hs : P.filter (fun a => c (x a)≠c (y a))⊆A₀∪A₁ := by
    intro a ha
    obtain ⟨ha,hn⟩ := mem_filter.mp ha
    by_cases hx : c (x a)=false
    · have hy : c (y a)=true := by cases h : c (y a) <;> simp_all
      exact mem_union_left _ (mem_filter.mpr ⟨ha,hx,hy⟩)
    · have hx' : c (x a)=true := by cases h : c (x a) <;> simp_all
      have hy : c (y a)=false := by cases h : c (y a) <;> simp_all
      exact mem_union_right _ (mem_filter.mpr ⟨ha,hx',hy⟩)
  have hcount := (card_le_card hs).trans (card_union_le _ _)
  by_cases h : A₀.card≤A₁.card
  · let b : V → Fin 2 := fun v => if c v then 0 else 1
    have he : P.filter (fun a => b (x a)=0 ∧ b (y a)=1)=A₁ := by
      ext a
      simp only [A₁,mem_filter,b]
      cases c (x a) <;> cases c (y a) <;> simp
    refine ⟨b,?_⟩
    rw [he]
    omega
  · let b : V → Fin 2 := fun v => if c v then 1 else 0
    have he : P.filter (fun a => b (x a)=0 ∧ b (y a)=1)=A₀ := by
      ext a
      simp only [A₀,mem_filter,b]
      cases c (x a) <;> cases c (y a) <;> simp
    refine ⟨b,?_⟩
    rw [he]
    omega
end
end OrientedRolePartition

end -- OrientedRolePartition

section -- FiniteRolePartitions

/- Simultaneous role separation using independently chosen two-class partitions. -/
open Finset
namespace FiniteRolePartitions
set_option maxHeartbeats 1500000
universe u v w
variable {A : Type u} {V : Type v} [Fintype V]

lemma select_nat (n : ℕ) (P : Finset A) (x y : Fin n → A → V)
    (hxy : ∀ i a, a∈P → x i a≠y i a) :
    ∃ (b : Fin n → V → Fin 2) (Q : Finset A), Q⊆P ∧
      (∀ i a, a∈Q → b i (x i a)=0 ∧ b i (y i a)=1) ∧ P.card≤4^n*Q.card := by
  classical
  induction n generalizing P with
  | zero => exact ⟨Fin.elim0,P,subset_rfl,(fun i => Fin.elim0 i),by simp⟩
  | succ n ih =>
    obtain ⟨b0,h0⟩ := OrientedRolePartition.exists_roles P (x 0) (y 0) (hxy 0)
    let P0 := P.filter (fun a => b0 (x 0 a)=0 ∧ b0 (y 0 a)=1)
    obtain ⟨b,Q,hQ,hroles,hcard⟩ := ih P0 (fun i => x i.succ) (fun i => y i.succ)
      (fun i a ha => hxy i.succ a (mem_filter.mp ha).1)
    refine ⟨Fin.cons b0 b,Q,hQ.trans (filter_subset _ _),?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro a ha
        exact (mem_filter.mp (hQ ha)).2
      · exact hroles i
    · have hh := h0.trans (Nat.mul_le_mul_left 4 hcard)
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

lemma select {I : Type w} [Fintype I] (P : Finset A) (x y : I → A → V)
    (hxy : ∀ i a, a∈P → x i a≠y i a) :
    ∃ (b : I → V → Fin 2) (Q : Finset A), Q⊆P ∧
      (∀ i a, a∈Q → b i (x i a)=0 ∧ b i (y i a)=1) ∧ P.card≤4^(Fintype.card I)*Q.card := by
  classical
  let e := Fintype.equivFin I
  obtain ⟨b,Q,hQ,hr,hcard⟩ := select_nat (Fintype.card I) P
    (fun i => x (e.symm i)) (fun i => y (e.symm i)) (fun i a ha => hxy _ a ha)
  refine ⟨(fun i => b (e i)),Q,hQ,?_,hcard⟩
  intro i a ha
  simpa only [Equiv.symm_apply_apply] using hr (e i) a ha

end FiniteRolePartitions

end -- FiniteRolePartitions

section -- HubPathRoleSelection

/- Separate the two old-vertex roles from one another and from every core-interior coordinate. -/
open Finset SimpleGraph ChainCounting
namespace HubPathRoleSelection
open HubLightPaths
set_option maxHeartbeats 2000000
universe u
noncomputable section
variable {V : Type u} [Fintype V]
variable (H : SimpleGraph V)

lemma select (k : ℕ) (L : ℕ → ℕ) (x y : V) :
    ∃ (b : V → Fin 2) (Q : Finset (Path H k)), Q⊆links H k L x y ∧
      (∀ p∈Q, b (first H k p)=0 ∧ b (last H k p)=1) ∧
      (∀ p∈Q, ∀ q∈Q, ∀ i : Fin k,
        first H k p≠middle H k q i ∧ last H k p≠middle H k q i) ∧
      (links H k L x y).card≤4^(1+2*k)*Q.card := by
  let I := Unit ⊕ (Fin 2 × Fin k)
  let l : I → Path H k → V := Sum.elim (fun _ => first H k)
    (fun ij p => if ij.1=0 then first H k p else last H k p)
  let r : I → Path H k → V := Sum.elim (fun _ => last H k) (fun ij p => middle H k p ij.2)
  have hneq (i : I) (p : Path H k) (hp : p∈links H k L x y) : l i p≠r i p := by
    have hinj := ((mem_links H k L x y p).mp hp).1.1
    cases i with
    | inl a =>
      change first H k p≠last H k p
      apply hinj.ne
      intro he
      have hh := congrArg Fin.val he
      change 1=k+2 at hh
      omega
    | inr ij =>
      dsimp only [l,r,Sum.elim_inr]
      split_ifs
      · apply hinj.ne
        intro he
        have hh := congrArg Fin.val he
        change 1=ij.2.val+2 at hh
        omega
      · apply hinj.ne
        intro he
        have hh := congrArg Fin.val he
        change k+2=ij.2.val+2 at hh
        have := ij.2.isLt
        omega
  obtain ⟨b,Q,hQ,hroles,hcard⟩ := FiniteRolePartitions.select (links H k L x y) l r hneq
  refine ⟨b (Sum.inl ()),Q,hQ,?_,?_,?_⟩
  · intro p hp
    exact hroles (Sum.inl ()) p hp
  · intro p hp q hq i
    constructor
    · have hp' := (hroles (Sum.inr (0,i)) p hp).1
      have hq' := (hroles (Sum.inr (0,i)) q hq).2
      change b (Sum.inr (0,i)) (first H k p)=0 at hp'
      change b (Sum.inr (0,i)) (middle H k q i)=1 at hq'
      intro he
      rw [he,hq'] at hp'
      exact (by decide : (1 : Fin 2)≠0) hp'
    · have hp' := (hroles (Sum.inr (1,i)) p hp).1
      have hq' := (hroles (Sum.inr (1,i)) q hq).2
      change b (Sum.inr (1,i)) (last H k p)=0 at hp'
      change b (Sum.inr (1,i)) (middle H k q i)=1 at hq'
      intro he
      rw [he,hq'] at hp'
      exact (by decide : (1 : Fin 2)≠0) hp'
  · simpa only [I,Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,Fintype.card_fin] using hcard

end
end HubPathRoleSelection

end -- HubPathRoleSelection

section -- HubLightBounds

/- The full truncated-good path bound, for an arbitrary replacement length. -/
open Finset SimpleGraph ChainCounting HubLightPaths
namespace HubLightBounds
set_option maxHeartbeats 3000000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] (F : SimpleGraph W) (c : F.Coloring (Fin 2))
variable {V : Type v} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

def loss (k : ℕ) (L : ℕ → ℕ) : ℕ := 4^(1+2*k)*((k+1)*(L (k+1)+k*(L (k+1))^2))

lemma selected_bound (hF : F.Connected) (k D : ℕ) (L : ℕ → ℕ) (x y : V)
    (Q : Finset (Path H k)) (hQ : Q⊆links H k L x y)
    (b : V → Fin 2) (hb : ∀ p∈Q, b (first H k p)=0 ∧ b (last H k p)=1)
    (hp : Set.InjOn (fun p : Path H k => (first H k p,last H k p)) Q)
    (hm : ∀ p∈Q, ∀ q∈Q, ∀ i j : Fin k, middle H k p i=middle H k q j → p=q ∧ i=j)
    (hsep : ∀ p∈Q, ∀ q∈Q, ∀ i : Fin k, first H k p≠middle H k q i ∧ last H k p≠middle H k q i)
    (hD : ∀ v, H.degree v≤D) (hfree : (HubPathSubdivision.graph c k).Free H)
    (C α : ℝ) (hC : 0≤C) (hα : 0≤α)
    (hbound : ∀ n : ℕ, (extremalNumber n F : ℝ)≤C*(n : ℝ)^α) :
    (Q.card : ℝ)≤C*(2*(D : ℝ))^α := by
  by_cases hne : Q.Nonempty
  · let J := SelectedHubLink.graph H k Q
    have hJfree : F.Free J := by
      rintro ⟨f⟩
      have h1 := HubPathCopyTransport.copy_of_copy hF c (SelectedHubLink.color H k Q) f k
      have h2 := SelectedHubLink.copy H k Q L x y hQ hne b hb hp hm hsep
      exact hfree (h1.trans h2)
    have he : Q.card=Nat.card J.edgeSet := by
      rw [Nat.card_eq_fintype_card,← Fintype.card_coe Q]
      exact Fintype.card_congr (SelectedHubLink.edgeEquiv H k Q hp)
    have hj := SimpleGraph.card_edgeFinset_le_extremalNumber hJfree
    have hh : (Nat.card J.edgeSet : ℝ)≤(extremalNumber (Fintype.card (SelectedHubLink.Vertex H k Q)) F : ℝ) := by
      simpa only [← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card] using (show
        (J.edgeFinset.card : ℝ)≤(extremalNumber (Fintype.card (SelectedHubLink.Vertex H k Q)) F : ℝ) by exact_mod_cast hj)
    have hn : (Fintype.card (SelectedHubLink.Vertex H k Q) : ℝ)≤2*(D : ℝ) := by
      exact_mod_cast SelectedHubLink.vertices_card H k Q L x y hQ D hD
    rw [he]
    exact (hh.trans (hbound _)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hα) hC)
  · rw [not_nonempty_iff_eq_empty.mp hne,card_empty,Nat.cast_zero]
    positivity

lemma link_bound (hF : F.Connected) (k D : ℕ) (L : ℕ → ℕ) (hL : Monotone L)
    (x y : V) (hD : ∀ v, H.degree v≤D) (hfree : (HubPathSubdivision.graph c k).Free H)
    (C α : ℝ) (hC : 0≤C) (hα : 0≤α)
    (hbound : ∀ n : ℕ, (extremalNumber n F : ℝ)≤C*(n : ℝ)^α) :
    ((links H k L x y).card : ℝ)≤(loss k L : ℝ)*(C*(2*(D : ℝ))^α) := by
  obtain ⟨b,P,hP,hb,hsep,hcard⟩ := HubPathRoleSelection.select H k L x y
  obtain ⟨Q,hQ,hpair,hmid,hcount⟩ := HubLightSelection.select H k L hL x y P hP
  have hQbound := selected_bound F c H hF k D L x y Q (hQ.trans hP) b
    (fun p hp => hb p (hQ hp)) hpair hmid (fun p hp q hq i => hsep p (hQ hp) q (hQ hq) i)
    hD hfree C α hC hα hbound
  have hnat : (links H k L x y).card≤loss k L*Q.card := by
    exact (hcard.trans (Nat.mul_le_mul_left _ hcount)).trans_eq (by dsimp only [loss]; ring)
  have hreal : ((links H k L x y).card : ℝ)≤(loss k L : ℝ)*Q.card := by exact_mod_cast hnat
  exact hreal.trans (mul_le_mul_of_nonneg_left hQbound (Nat.cast_nonneg _))

lemma good_bound (hF : F.Connected) (k D : ℕ) (L : ℕ → ℕ) (hL : Monotone L)
    (hD : ∀ v, H.degree v≤D) (hfree : (HubPathSubdivision.graph c k).Free H)
    (C α : ℝ) (hC : 0≤C) (hα : 0≤α)
    (hbound : ∀ n : ℕ, (extremalNumber n F : ℝ)≤C*(n : ℝ)^α) :
    ((good H k L).card : ℝ)≤(loss k L : ℝ)*(Fintype.card V : ℝ)^2*(C*(2*(D : ℝ))^α) := by
  have he : (good H k L).card=∑ xy : V × V, (links H k L xy.1 xy.2).card := by
    have hh := card_eq_sum_card_fiberwise (s := good H k L) (t := (univ : Finset (V × V)))
      (fun p _ => mem_univ (p.val 0,p.val (Fin.last (k+3))))
    apply hh.trans
    apply sum_congr rfl
    rintro ⟨x,y⟩ _
    congr 1
    ext p
    simp only [links,mem_filter,Prod.mk.injEq]
  rw [he,Nat.cast_sum]
  apply (sum_le_sum (fun xy _ => link_bound F c H hF k D L hL xy.1 xy.2 hD hfree C α hC hα hbound)).trans_eq
  simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

end
end HubLightBounds

end -- HubLightBounds

section -- HubAdmissibleCount

/- The general hub path count with only an absorbable constant error. -/
open Finset SimpleGraph ChainCounting
namespace HubAdmissibleCount
set_option maxHeartbeats 2500000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] (F : SimpleGraph W) (c : F.Coloring (Fin 2))
variable {V : Type v} [Fintype V] (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _

lemma count (hF : F.Connected) (k B d D : ℕ) (hd : ∀ v, d+(k+3)≤H.degree v)
    (hD : ∀ v, H.degree v≤D) (hfree : (HubPathSubdivision.graph c k).Free H)
    (C α ε : ℝ) (hC : 0≤C) (hα : 0≤α) (hε : 0≤ε)
    (hbound : ∀ n : ℕ, (extremalNumber n F : ℝ)≤C*(n : ℝ)^α)
    (hsmall : ∀ j : ℕ, 2≤j → j≤k+1 → ((AdmissibleHeavyLinks.bad H B j).card : ℝ)≤
      ε*Fintype.card V*(D : ℝ)^j) :
    (Fintype.card V : ℝ)*(d : ℝ)^(k+3)≤
      (HubLightBounds.loss k (ThetaChains.threshold B) : ℝ)*C*2^α*(Fintype.card V : ℝ)^2*(D : ℝ)^α+
      (k+4 : ℕ)*(k+2 : ℕ)*ε*Fintype.card V*(D : ℝ)^(k+3) := by
  have hc : (Fintype.card V : ℝ)*(d : ℝ)^(k+3)≤(HubLightPaths.good H k (ThetaChains.threshold B)).card+
      (k+4 : ℕ)*∑ j : Fin (k+2), ((AdmissibleHeavyLinks.bad H B j.val).card : ℝ)*(D : ℝ)^(k+3-j.val) := by
    exact_mod_cast AdmissibleHubLightCount.count H k B d D hd hD
  have hgood := HubLightBounds.good_bound F c H hF k D (ThetaChains.threshold B) (ThetaChains.threshold_mono B)
    hD hfree C α hC hα hbound
  have hsum : (∑ j : Fin (k+2), ((AdmissibleHeavyLinks.bad H B j.val).card : ℝ)*(D : ℝ)^(k+3-j.val))≤
      (k+2 : ℕ)*(ε*Fintype.card V*(D : ℝ)^(k+3)) := by
    calc
      _ ≤ ∑ _j : Fin (k+2), ε*Fintype.card V*(D : ℝ)^(k+3) := by
        apply sum_le_sum
        intro j _
        by_cases hj : 2≤j.val
        · have hh := mul_le_mul_of_nonneg_right (hsmall j.val hj (by omega))
            (pow_nonneg (Nat.cast_nonneg D) (k+3-j.val))
          have he : (D : ℝ)^j.val*(D : ℝ)^(k+3-j.val)=(D : ℝ)^(k+3) := by
            rw [← pow_add,Nat.add_sub_of_le (by omega : j.val≤k+3)]
          simpa only [mul_assoc,he] using hh
        · rw [AdmissibleHubLightCount.bad_small H B j.val (by omega),card_empty,Nat.cast_zero,zero_mul]
          positivity
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (k+4))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) (Nat.cast_nonneg D)] at hgood
  nlinarith only [hc,hgood,hm]

end
end HubAdmissibleCount

end -- HubAdmissibleCount

section -- BipartiteReservoirPaths

/- Fixed-length paths inside two complete bipartite reservoirs, avoiding
an arbitrary finite set at all internal vertices. -/
open Finset SimpleGraph ChainCounting
namespace BipartiteReservoirPaths
set_option maxHeartbeats 2500000
universe u
noncomputable section
variable {V : Type u} (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _

def pool (A B : Finset V) (i : ℕ) : Finset V := if i%2=0 then A else B

lemma exists_path (A B S : Finset V) (m : ℕ) (hm : 0 < m) (x y : V)
    (hx : x∈A) (hy : y∈pool A B m) (hxy : x≠y)
    (hA : S.card+m+2≤A.card) (hB : S.card+m+2≤B.card)
    (hcomplete : ∀ a∈A, ∀ b∈B, H.Adj a b) :
    ∃ p : Chain H m, Function.Injective p.val ∧ p.val 0=x ∧ p.val (Fin.last m)=y ∧
      Disjoint (interior H p) S ∧ ∀ i, p.val i∈pool A B i.val := by
  classical
  let P (i : Fin (m-1)) : Set V := {v | v∈pool A B (i.val+1) ∧ v∉S ∧ v≠x ∧ v≠y}
  obtain ⟨g,hg,hdis⟩ := FiniteLabelPacking.select_fintype 1 P (fun v => ({v} : Finset V))
    (fun _ _ _ => by simp) (by
      intro i T hT
      have hT' : T.card≤ m-1 := by simpa using hT
      let U := S∪({x,y}∪T)
      have hU : U.card<S.card+m+2 := by
        have h₁ := card_union_le S ({x,y}∪T)
        have h₂ := card_union_le ({x,y} : Finset V) T
        have h₃ : ({x,y} : Finset V).card≤2 := (card_insert_le x {y}).trans (by simp)
        dsimp only [U]
        omega
      have hpool : S.card+m+2≤(pool A B (i.val+1)).card := by
        dsimp only [pool]
        split_ifs <;> assumption
      obtain ⟨v,hv,hvU⟩ := exists_mem_notMem_of_card_lt_card (hU.trans_le hpool)
      have hvS : v∉S := fun h => hvU (mem_union_left _ h)
      have hvx : v≠x := fun h => hvU (mem_union_right _ (mem_union_left _ (mem_insert.mpr (Or.inl h))))
      have hvy : v≠y := fun h => hvU (mem_union_right _ (mem_union_left _ (mem_insert_of_mem (mem_singleton.mpr h))))
      have hvT : v∉T := fun h => hvU (mem_union_right _ (mem_union_right _ h))
      exact ⟨v,⟨hv,hvS,hvx,hvy⟩,by simpa only [disjoint_singleton_left] using hvT⟩)
  have hgi : Function.Injective g := by
    intro i j he
    by_contra hn
    exact Finset.disjoint_left.mp (hdis i j hn) (mem_singleton_self _) (mem_singleton.mpr he)
  let f (i : Fin (m+1)) : V :=
    if h0 : i.val=0 then x else if hl : i.val=m then y else g ⟨i.val-1,by omega⟩
  have hf0 : f 0=x := by simp [f]
  have hflast : f (Fin.last m)=y := by simp [f,hm.ne']
  have hfm (i : Fin (m-1)) : f ⟨i.val+1,by omega⟩=g i := by
    dsimp only [f]
    rw [dif_neg (by omega),dif_neg (by omega)]
    congr 1
  have hfi : Function.Injective f := by
    intro i j he
    dsimp only [f] at he
    split_ifs at he with hi0 him hj0 hjm hj0 hjm
    · exact Fin.ext (by omega)
    · exact (hxy he).elim
    · exact ((hg _).2.2.1 he.symm).elim
    · exact (hxy he.symm).elim
    · exact Fin.ext (by omega)
    · exact ((hg _).2.2.2 he.symm).elim
    · exact ((hg _).2.2.1 he).elim
    · exact ((hg _).2.2.2 he).elim
    · have hh := congrArg Fin.val (hgi he)
      apply Fin.ext
      dsimp only [Fin.val_mk] at hh
      omega
  have hpool (i : Fin (m+1)) : f i∈pool A B i.val := by
    dsimp only [f]
    split_ifs with hi0 him
    · simpa [hi0,pool] using hx
    · simpa only [him] using hy
    · have hh := (hg ⟨i.val-1,by omega⟩).1
      simpa only [show i.val-1+1=i.val by omega] using hh
  have hchain : IsChain H f := by
    intro i
    have h₀ := hpool i.castSucc
    have h₁ := hpool i.succ
    have hi : i.val%2=0 ∨ i.val%2=1 := by omega
    rcases hi with hi | hi
    · have hnext : (i.val+1)%2≠0 := by omega
      simp only [pool,Fin.val_castSucc,Fin.val_succ,hi,if_pos rfl,if_neg hnext] at h₀ h₁
      exact hcomplete _ h₀ _ h₁
    · have hnext : (i.val+1)%2=0 := by omega
      simp only [pool,Fin.val_castSucc,Fin.val_succ,hi,hnext,if_pos rfl,show (1 : ℕ)≠0 by omega,if_false] at h₀ h₁
      exact (hcomplete _ h₁ _ h₀).symm
  refine ⟨⟨f,hchain⟩,hfi,hf0,hflast,?_,hpool⟩
  apply Finset.disjoint_left.mpr
  intro v hv hvS
  obtain ⟨i,hi0,him,he⟩ := (mem_interior H ⟨f,hchain⟩ v).mp hv
  have hi : (⟨(i.val-1)+1,by omega⟩ : Fin (m+1))=i := Fin.ext (by dsimp; omega)
  have hfg : f i=g ⟨i.val-1,by omega⟩ := by simpa only [hi] using hfm ⟨i.val-1,by omega⟩
  have he' : f i=v := he
  exact (hg ⟨i.val-1,by omega⟩).2.1 ((hfg.symm.trans he').symm ▸ hvS)


lemma select_paths {E : Type*} [Fintype E] (A B S : Finset V) (m : ℕ) (hm : 0 < m)
    (x y : E → V) (hx : ∀ e, x e∈A) (hy : ∀ e, y e∈pool A B m) (hxy : ∀ e, x e≠y e)
    (hA : S.card+(m-1)*Fintype.card E+m+2≤A.card)
    (hB : S.card+(m-1)*Fintype.card E+m+2≤B.card)
    (hcomplete : ∀ a∈A, ∀ b∈B, H.Adj a b) :
    ∃ p : E → Chain H m,
      (∀ e, Function.Injective (p e).val ∧ (p e).val 0=x e ∧ (p e).val (Fin.last m)=y e ∧
        Disjoint (interior H (p e)) S ∧ ∀ i, (p e).val i∈pool A B i.val) ∧
      ∀ e f, e≠f → Disjoint (interior H (p e)) (interior H (p f)) := by
  classical
  let P (e : E) : Set (Chain H m) := {p | Function.Injective p.val ∧ p.val 0=x e ∧
    p.val (Fin.last m)=y e ∧ Disjoint (interior H p) S ∧ ∀ i, p.val i∈pool A B i.val}
  obtain ⟨p,hp,hdis⟩ := FiniteLabelPacking.select_fintype (m-1) P (interior H)
    (fun _ p _ => interior_card_le H p) (by
      intro e T hT
      have hST : (S∪T).card+m+2≤S.card+(m-1)*Fintype.card E+m+2 := by
        have hh := card_union_le S T
        omega
      obtain ⟨q,hq,hq0,hql,hqS,hqp⟩ := exists_path H A B (S∪T) m hm (x e) (y e) (hx e) (hy e) (hxy e)
        (hST.trans hA) (hST.trans hB) hcomplete
      exact ⟨q,⟨hq,hq0,hql,hqS.mono_right subset_union_left,hqp⟩,hqS.mono_right subset_union_right⟩)
  exact ⟨p,hp,hdis⟩

end
end BipartiteReservoirPaths

end -- BipartiteReservoirPaths

section -- HeavyChainBundle

/- Lift a whole internally disjoint bundle of shadow paths, keeping a
prescribed finite set out of all new path interiors. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace HeavyChainBundle
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
universe u v
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
variable {E : Type v} [Fintype E]

lemma lift (B j m : ℕ) (hj : 0<j) (S : Finset V) (b : E → Chain (HeavyShadow.graph H B j) m)
    (hbinj : ∀ e, Function.Injective (b e).val)
    (hbS : ∀ e, Disjoint (interior (HeavyShadow.graph H B j) (b e)) S)
    (hbdis : ∀ e f, e≠f → Disjoint (interior (HeavyShadow.graph H B j) (b e))
      (interior (HeavyShadow.graph H B j) (b f)))
    (hB : (j-1)*(Fintype.card E*m)+S.card+Fintype.card E*(m+1)≤B) :
    ∃ p : E → Chain H (m*j),
      (∀ e, Function.Injective (p e).val ∧ (p e).val 0=(b e).val 0 ∧
        (p e).val (Fin.last (m*j))=(b e).val (Fin.last m) ∧ Disjoint (interior H (p e)) S) ∧
      ∀ e f, e≠f → Disjoint (interior H (p e)) (interior H (p f)) := by
  classical
  let Branches := univ.image (fun z : E × Fin (m+1) => (b z.1).val z.2)
  let U := S∪Branches
  have hBranches : Branches.card≤Fintype.card E*(m+1) := card_image_le.trans_eq (by simp)
  have hU : U.card≤S.card+Fintype.card E*(m+1) := (card_union_le S Branches).trans (Nat.add_le_add_left hBranches _)
  let P (e : E × Fin m) : Set (Chain H j) := {q |
    q∈fiber H (threshold B) j ((b e.1).val e.2.castSucc) ((b e.1).val e.2.succ) ∧
      Disjoint (interior H q) U}
  obtain ⟨r,hr,hrdis⟩ := FiniteLabelPacking.select_fintype (j-1) P (interior H)
    (fun _ q _ => interior_card_le H q) (by
      intro e T hT
      have hsize : (T∪U).card≤B := by
        have hh := card_union_le T U
        simp only [Fintype.card_prod,Fintype.card_fin] at hT
        omega
      obtain ⟨q,hq,hqdis⟩ := fiber_avoiding H B j hj _ _ ((b e.1).property e.2).2 (T∪U) hsize
      exact ⟨q,⟨hq,hqdis.mono_right subset_union_right⟩,hqdis.mono_right subset_union_left⟩)
  have hr' (e : E × Fin m) := (mem_fiber H (threshold B) j _ _ (r e)).mp (hr e).1
  have hbranch (e : E) (i : Fin (m+1)) : (b e).val i∈U :=
    mem_union_right _ (mem_image.mpr ⟨(e,i),mem_univ _,rfl⟩)
  have hconcat (e : E) : ∃ q : Chain H (m*j), Function.Injective q.val ∧ q.val 0=(b e).val 0 ∧
      q.val (Fin.last (m*j))=(b e).val (Fin.last m) ∧
      ∀ i, (∃ a, q.val i=(b e).val a) ∨ ∃ a, q.val i∈interior H (r (e,a)) := by
    exact concatenate H j m (b e).val (fun a => r (e,a)) (hbinj e)
      (fun a => ⟨(hr' (e,a)).1.1,(hr' (e,a)).2⟩)
      (fun a i hi => Finset.disjoint_left.mp (hr (e,a)).2 hi (hbranch e i))
      (fun a c hac => hrdis (e,a) (e,c) (fun h => hac (congrArg Prod.snd h)))
  choose p hp hp0 hplast hcover using hconcat
  have hmidcover (e : E) (v : V) (hv : v∈interior H (p e)) :
      v∈interior (HeavyShadow.graph H B j) (b e) ∨ ∃ a, v∈interior H (r (e,a)) := by
    obtain ⟨i,hi0,hil,he⟩ := (mem_interior H (p e) v).mp hv
    rcases hcover e i with ⟨a,ha⟩ | ⟨a,ha⟩
    · have hv0 : v≠(b e).val 0 := by
        intro h
        have hh := congrArg Fin.val ((hp e) (he.trans (h.trans (hp0 e).symm)))
        simp only [Fin.val_zero] at hh
        omega
      have hvl : v≠(b e).val (Fin.last m) := by
        intro h
        have hh := congrArg Fin.val ((hp e) (he.trans (h.trans (hplast e).symm)))
        simp only [Fin.val_last] at hh
        omega
      rcases vertex_cases (HeavyShadow.graph H B j) (b e) a with h0 | hl | hm
      · exact (hv0 (he.symm.trans (ha.trans h0))).elim
      · exact (hvl (he.symm.trans (ha.trans hl))).elim
      · exact Or.inl ((ha.symm.trans he) ▸ hm)
    · exact Or.inr ⟨a,he ▸ ha⟩
  have hav (e : E × Fin m) : Disjoint (interior H (r e)) S := (hr e).2.mono_right subset_union_left
  refine ⟨p,fun e => ⟨hp e,hp0 e,hplast e,?_⟩,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hvS
    rcases hmidcover e v hv with hv | ⟨a,ha⟩
    · exact Finset.disjoint_left.mp (hbS e) hv hvS
    · exact Finset.disjoint_left.mp (hav (e,a)) ha hvS
  · intro e f hef
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    rcases hmidcover e v hve with he | ⟨a,ha⟩ <;>
      rcases hmidcover f v hvf with hf | ⟨c,hc⟩
    · exact Finset.disjoint_left.mp (hbdis e f hef) he hf
    · obtain ⟨i,_,_,hi⟩ := (mem_interior (HeavyShadow.graph H B j) (b e) v).mp he
      exact Finset.disjoint_left.mp (hr (f,c)).2 hc (hi ▸ hbranch e i)
    · obtain ⟨i,_,_,hi⟩ := (mem_interior (HeavyShadow.graph H B j) (b f) v).mp hf
      exact Finset.disjoint_left.mp (hr (e,a)).2 ha (hi ▸ hbranch f i)
    · exact Finset.disjoint_left.mp (hrdis (e,a) (f,c) (fun h => hef (congrArg Prod.fst h))) ha hc

end
end HeavyChainBundle

end -- HeavyChainBundle

section -- AppendChainBundle

/- Append disjoint tails to an internally disjoint path bundle. -/
open Finset SimpleGraph ChainCounting
namespace AppendChainBundle
set_option maxHeartbeats 2500000
universe u v
noncomputable section
variable {V : Type u} (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
variable {E : Type v}

def cotail {l : ℕ} (q : Chain H l) : Finset V := insert (q.val 0) (interior H q)

lemma append_bundle (n l : ℕ) (p : E → Chain H n) (q : E → Chain H l)
    (hp : ∀ e, Function.Injective (p e).val) (hq : ∀ e, Function.Injective (q e).val)
    (hjoin : ∀ e, (p e).val (Fin.last n)=(q e).val 0)
    (hstart : ∀ e f i, (p e).val 0≠(q f).val i)
    (havoid : ∀ e f i, (q f).val i∉interior H (p e))
    (hpdis : ∀ e f, e≠f → Disjoint (interior H (p e)) (interior H (p f)))
    (hqdis : ∀ e f, e≠f → Disjoint (cotail H (q e)) (cotail H (q f))) :
    ∃ r : E → Chain H (n+l),
      (∀ e, Function.Injective (r e).val ∧ (r e).val 0=(p e).val 0 ∧
        (r e).val (Fin.last (n+l))=(q e).val (Fin.last l) ∧
        interior H (r e)⊆interior H (p e)∪cotail H (q e)) ∧
      ∀ e f, e≠f → Disjoint (interior H (r e)) (interior H (r f)) := by
  let r (e : E) := append H (p e) (q e) (hjoin e)
  have hr (e : E) : Function.Injective (r e).val := by
    apply append_injective H (p e) (q e) (hjoin e) (hp e) (hq e)
    intro i j he
    rcases vertex_cases H (p e) i with h0 | hl | hm
    · exact (hstart e e j (h0.symm.trans he)).elim
    · exact ⟨(hp e) hl,(hq e) (he.symm.trans (hl.trans (hjoin e)))⟩
    · exact (havoid e e j (he ▸ hm)).elim
  have hsub (e : E) : interior H (r e)⊆interior H (p e)∪cotail H (q e) := by
    intro v hv
    obtain ⟨i,hi0,hil,he⟩ := (mem_interior H (r e) v).mp hv
    have hv0 : v≠(p e).val 0 := by
      intro hv0
      have hh := congrArg Fin.val (hr e (he.trans (hv0.trans (append_start H (p e) (q e) (hjoin e)).symm)))
      simp only [Fin.val_zero] at hh
      omega
    have hvl : v≠(q e).val (Fin.last l) := by
      intro hvl
      have hh := congrArg Fin.val (hr e (he.trans (hvl.trans (append_last H (p e) (q e) (hjoin e)).symm)))
      simp only [Fin.val_last] at hh
      omega
    rcases append_vertex H (p e) (q e) (hjoin e) i with ⟨a,ha⟩ | ⟨a,ha⟩
    · rcases vertex_cases H (p e) a with h0 | hl | hm
      · exact (hv0 (he.symm.trans (ha.trans h0))).elim
      · exact mem_union_right _ (mem_insert.mpr (Or.inl (he.symm.trans (ha.trans (hl.trans (hjoin e))))))
      · exact mem_union_left _ ((ha.symm.trans he) ▸ hm)
    · rcases vertex_cases H (q e) a with h0 | hl | hm
      · exact mem_union_right _ (mem_insert.mpr (Or.inl (he.symm.trans (ha.trans h0))))
      · exact (hvl (he.symm.trans (ha.trans hl))).elim
      · exact mem_union_right _ (mem_insert_of_mem ((ha.symm.trans he) ▸ hm))
  have hcross (e f : E) : Disjoint (interior H (p e)) (cotail H (q f)) := by
    apply Finset.disjoint_left.mpr
    intro v hpv hqv
    rcases mem_insert.mp hqv with h0 | hm
    · exact havoid e f 0 (h0 ▸ hpv)
    · obtain ⟨i,_,_,he⟩ := (mem_interior H (q f) v).mp hm
      exact havoid e f i (he.symm ▸ hpv)
  refine ⟨r,fun e => ⟨hr e,append_start H (p e) (q e) (hjoin e),append_last H (p e) (q e) (hjoin e),hsub e⟩,?_⟩
  intro e f hef
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  rcases mem_union.mp (hsub e hve) with he | he <;> rcases mem_union.mp (hsub f hvf) with hf | hf
  · exact Finset.disjoint_left.mp (hpdis e f hef) he hf
  · exact Finset.disjoint_left.mp (hcross e f) he hf
  · exact Finset.disjoint_left.mp (hcross f e) hf he
  · exact Finset.disjoint_left.mp (hqdis e f hef) he hf

end
end AppendChainBundle

end -- AppendChainBundle

section -- ChainFront

/- All vertices of a path except its final endpoint, also for zero length. -/
open Finset SimpleGraph ChainCounting
namespace ChainFront
set_option maxHeartbeats 2000000
universe u v
noncomputable section
variable {V : Type u} (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _

def front {l : ℕ} (p : Chain H l) : Finset V := univ.image (fun i : Fin l => p.val i.castSucc)

lemma card_le {l : ℕ} (p : Chain H l) : (front H p).card≤l := card_image_le.trans_eq (by simp)

lemma mem_front {l : ℕ} (p : Chain H l) (v : V) :
    v∈front H p ↔ ∃ i : Fin (l+1), i.val<l ∧ p.val i=v := by
  constructor
  · rintro hv
    obtain ⟨i,_,hi⟩ := mem_image.mp hv
    exact ⟨i.castSucc,i.isLt,hi⟩
  · rintro ⟨i,hi,he⟩
    exact mem_image.mpr ⟨⟨i.val,hi⟩,mem_univ _,he⟩

lemma eq_cotail {l : ℕ} (hl : 0<l) (p : Chain H l) : front H p=AppendChainBundle.cotail H p := by
  ext v
  simp only [AppendChainBundle.cotail,mem_insert,mem_front,mem_interior]
  constructor
  · rintro ⟨i,hi,he⟩
    by_cases hi0 : i.val=0
    · left
      exact he.symm.trans (congrArg p.val (Fin.ext hi0))
    · right
      exact ⟨i,by omega,hi,he⟩
  · rintro (he | ⟨i,hi0,hi,he⟩)
    · exact ⟨0,hl,he.symm⟩
    · exact ⟨i,hi,he⟩


lemma append_bundle {E : Type v} (n l : ℕ) (p : E → Chain H n) (q : E → Chain H l)
    (hp : ∀ e, Function.Injective (p e).val) (hq : ∀ e, Function.Injective (q e).val)
    (hjoin : ∀ e, (p e).val (Fin.last n)=(q e).val 0)
    (hstart : ∀ e f i, (p e).val 0≠(q f).val i)
    (havoid : ∀ e f i, (q f).val i∉interior H (p e))
    (hpdis : ∀ e f, e≠f → Disjoint (interior H (p e)) (interior H (p f)))
    (hqdis : ∀ e f, e≠f → Disjoint (front H (q e)) (front H (q f))) :
    ∃ r : E → Chain H (n+l),
      (∀ e, Function.Injective (r e).val ∧ (r e).val 0=(p e).val 0 ∧
        (r e).val (Fin.last (n+l))=(q e).val (Fin.last l) ∧
        interior H (r e)⊆interior H (p e)∪front H (q e)) ∧
      ∀ e f, e≠f → Disjoint (interior H (r e)) (interior H (r f)) := by
  by_cases hl : l=0
  · subst l
    simp only [Nat.add_zero]
    exact ⟨p,fun e => ⟨hp e,rfl,hjoin e,subset_union_left⟩,hpdis⟩
  · have hlp : 0<l := by omega
    simp_rw [eq_cotail H hlp] at hqdis ⊢
    exact AppendChainBundle.append_bundle H n l p q hp hq hjoin hstart havoid hpdis hqdis

end
end ChainFront

end -- ChainFront

section -- HubPathBundleCopy

/- The bundle formulation of a hub-subdivision copy. -/
open Finset SimpleGraph ChainCounting
namespace HubPathBundleCopy
set_option maxHeartbeats 2000000
universe u v
variable {W : Type u} {F : SimpleGraph W} (c : F.Coloring (Fin 2))
variable {V : Type v} (H : SimpleGraph V) (k : ℕ)
noncomputable section
local instance : DecidableEq V := Classical.decEq _

lemma copy (z : Fin 2 → V) (f : W → V) (p : GraphSubdivision.Edge F → Chain H (k+1))
    (hz : Function.Injective z) (hf : Function.Injective f) (hzf : ∀ i w, z i≠f w)
    (hp : ∀ e, Function.Injective (p e).val)
    (hpdis : ∀ e d, e≠d → Disjoint (interior H (p e)) (interior H (p d)))
    (hzp : ∀ i e, z i∉interior H (p e)) (hfp : ∀ w e, f w∉interior H (p e))
    (hstart : ∀ e, (p e).val 0=f (ColoredEdges.left c e))
    (hend : ∀ e, (p e).val (Fin.last (k+1))=f (ColoredEdges.right c e))
    (hhub : ∀ i w, c w=i → H.Adj (z i) (f w)) : HubPathSubdivision.graph c k ⊑ H := by
  let m (e : GraphSubdivision.Edge F × Fin k) : V := (p e.1).val e.2.succ.castSucc
  have hm_mem (e : GraphSubdivision.Edge F × Fin k) : m e∈interior H (p e.1) := by
    apply (mem_interior H (p e.1) _).mpr
    exact ⟨e.2.succ.castSucc,by simp,by simp only [Fin.val_castSucc,Fin.val_succ]; omega,rfl⟩
  have hm : Function.Injective m := by
    intro e d he
    have hfirst : e.1=d.1 := by
      by_contra hn
      exact Finset.disjoint_left.mp (hpdis e.1 d.1 hn) (hm_mem e) (he.symm ▸ hm_mem d)
    have hsecond : e.2=d.2 := by
      have hh := hp d.1 (by simpa only [m,hfirst] using he)
      have hn := congrArg Fin.val hh
      apply Fin.ext
      change e.2.val+1=d.2.val+1 at hn
      omega
    exact Prod.ext hfirst hsecond
  have hzm (i : Fin 2) (e : GraphSubdivision.Edge F × Fin k) : z i≠m e := by
    intro he
    exact hzp i e.1 (he.symm ▸ hm_mem e)
  have hfm (w : W) (e : GraphSubdivision.Edge F × Fin k) : f w≠m e := by
    intro he
    exact hfp w e.1 (he.symm ▸ hm_mem e)
  exact ⟨HubPathCopies.copyOfChains c H k z f p hz hf hm hzf
    (fun i e j => hzm i (e,j)) (fun w e j => hfm w (e,j)) hstart hend hhub⟩

end
end HubPathBundleCopy

end -- HubPathBundleCopy

section -- HubReservoirAssembly

/- Assemble a hub-subdivision from heavy complete bipartite reservoirs and
an externally selected disjoint tail bundle. -/
open Finset SimpleGraph ChainCounting
namespace HubReservoirAssembly
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] {F : SimpleGraph W} (c : F.Coloring (Fin 2))
variable {V : Type v} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : Fintype (GraphSubdivision.Edge F) := Fintype.ofFinite _

lemma copy (B j m l k : ℕ) (hj : 0<j) (hm : 0 < m) (hlen : m*j+l=k+1)
    (A C S : Finset V) (z : Fin 2 → V) (f : W → V) (q : GraphSubdivision.Edge F → Chain H l)
    (hz : Function.Injective z) (hf : Function.Injective f) (hzf : ∀ i w, z i≠f w)
    (hspoke : ∀ i w, c w=i → H.Adj (z i) (f w))
    (hqinj : ∀ e, Function.Injective (q e).val)
    (hqend : ∀ e, (q e).val (Fin.last l)=f (ColoredEdges.right c e))
    (hqdis : ∀ e d, e≠d → Disjoint (ChainFront.front H (q e)) (ChainFront.front H (q d)))
    (hqold : ∀ w e, f w∉ChainFront.front H (q e))
    (hqhub : ∀ i e, z i∉ChainFront.front H (q e))
    (hleft : ∀ e, f (ColoredEdges.left c e)∈A)
    (hright : ∀ e, (q e).val 0∈BipartiteReservoirPaths.pool A C m)
    (hstart : ∀ e d i, f (ColoredEdges.left c e)≠(q d).val i)
    (hcomplete : ∀ a∈A, ∀ b∈C, (HeavyShadow.graph H B j).Adj a b)
    (hfS : ∀ w, f w∈S) (hzS : ∀ i, z i∈S) (hqS : ∀ e i, (q e).val i∈S)
    (hA : S.card+(m-1)*Nat.card (GraphSubdivision.Edge F)+m+2≤A.card)
    (hC : S.card+(m-1)*Nat.card (GraphSubdivision.Edge F)+m+2≤C.card)
    (hB : (j-1)*(Nat.card (GraphSubdivision.Edge F)*m)+S.card+Nat.card (GraphSubdivision.Edge F)*(m+1)≤B) :
    HubPathSubdivision.graph c k ⊑ H := by
  classical
  let E := GraphSubdivision.Edge F
  have hA' : S.card+(m-1)*Fintype.card E+m+2≤A.card := by simpa only [Nat.card_eq_fintype_card] using hA
  have hC' : S.card+(m-1)*Fintype.card E+m+2≤C.card := by simpa only [Nat.card_eq_fintype_card] using hC
  obtain ⟨b,hb,hbdis⟩ := BipartiteReservoirPaths.select_paths (HeavyShadow.graph H B j) A C S m hm
    (fun e : E => f (ColoredEdges.left c e)) (fun e : E => (q e).val 0)
    hleft hright (fun e => hstart e e 0) hA' hC' hcomplete
  obtain ⟨p,hp,hpdis⟩ := HeavyChainBundle.lift H B j m hj S b (fun e => (hb e).1)
    (fun e => (hb e).2.2.2.1) hbdis (by simpa only [Nat.card_eq_fintype_card] using hB)
  have hp0 (e : E) : (p e).val 0=f (ColoredEdges.left c e) := (hp e).2.1.trans (hb e).2.1
  have hpjoin (e : E) : (p e).val (Fin.last (m*j))=(q e).val 0 :=
    (hp e).2.2.1.trans (hb e).2.2.1
  have hpstart (e d : E) (i : Fin (l+1)) : (p e).val 0≠(q d).val i := by
    rw [hp0]
    exact hstart e d i
  have hpavoid (e d : E) (i : Fin (l+1)) : (q d).val i∉interior H (p e) := by
    intro hi
    exact Finset.disjoint_left.mp (hp e).2.2.2 hi (hqS d i)
  have hbundle := ChainFront.append_bundle H (m*j) l p q (fun e => (hp e).1) hqinj
    hpjoin hpstart hpavoid hpdis hqdis
  rw [hlen] at hbundle
  obtain ⟨r,hr,hrdis⟩ := hbundle
  apply HubPathBundleCopy.copy c H k z f r hz hf hzf (fun e => (hr e).1) hrdis
  · intro i e hi
    rcases mem_union.mp ((hr e).2.2.2 hi) with hpv | hqv
    · exact Finset.disjoint_left.mp (hp e).2.2.2 hpv (hzS i)
    · exact hqhub i e hqv
  · intro w e hw
    rcases mem_union.mp ((hr e).2.2.2 hw) with hpv | hqv
    · exact Finset.disjoint_left.mp (hp e).2.2.2 hpv (hfS w)
    · exact hqold w e hqv
  · intro e
    exact (hr e).2.1.trans (hp0 e)
  · intro e
    exact (hr e).2.2.1.trans (hqend e)
  · exact hspoke

end
end HubReservoirAssembly

end -- HubReservoirAssembly

section -- AdmissibleSuffixCounts

/- Labels beyond a pinned coordinate of an admissible path. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace AdmissibleSuffixCounts
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

def labels {n : ℕ} (a : Fin (n+1)) (p : Chain H n) : Finset V :=
  univ.image (fun i : Fin (n-a.val) => p.val ⟨a.val+i.val+1,by omega⟩)

lemma labels_card {n : ℕ} (a : Fin (n+1)) (p : Chain H n) : (labels H a p).card≤n-a.val :=
  card_image_le.trans_eq (by simp)

lemma mem_labels {n : ℕ} (a : Fin (n+1)) (p : Chain H n) (v : V) :
    v∈labels H a p ↔ ∃ i : Fin (n+1), a.val < i.val ∧ p.val i=v := by
  constructor
  · intro hv
    obtain ⟨i,_,hi⟩ := mem_image.mp hv
    exact ⟨⟨a.val+i.val+1,by omega⟩,by dsimp; omega,hi⟩
  · rintro ⟨i,hi,hiv⟩
    refine mem_image.mpr ⟨⟨i.val-a.val-1,by omega⟩,mem_univ _,?_⟩
    convert hiv using 1
    apply congrArg p.val
    apply Fin.ext
    dsimp
    omega

lemma pinned_notMem {n : ℕ} (a : Fin (n+1)) (p : Chain H n) (hp : Function.Injective p.val) :
    p.val a∉labels H a p := by
  intro hv
  obtain ⟨i,hi,he⟩ := (mem_labels H a p _).mp hv
  have hh := congrArg Fin.val (hp he)
  omega

lemma labels_succ {n : ℕ} (a : Fin (n+1)) (ha : a.val<n) (p : Chain H n) :
    labels H a p=insert (p.val ⟨a.val+1,by omega⟩) (labels H ⟨a.val+1,by omega⟩ p) := by
  ext v
  simp only [mem_insert,mem_labels]
  constructor
  · rintro ⟨i,hi,he⟩
    by_cases h : i.val=a.val+1
    · left
      exact he.symm.trans (congrArg p.val (Fin.ext h))
    · right
      exact ⟨i,by omega,he⟩
  · rintro (he | ⟨i,hi,he⟩)
    · exact ⟨⟨a.val+1,by omega⟩,by dsimp; omega,he.symm⟩
    · exact ⟨i,by omega,he⟩

lemma incidence (L : ℕ → ℕ) (n D : ℕ) (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (a : Fin (n+1)) (ha : a.val<n) (z v : V) :
    ((P.filter (fun p => p.val a=z)).filter (fun p => v∈labels H a p)).card≤
      (n-a.val)*(L a.val*D^(n-a.val-1)) := by
  let E (i : Fin (n-a.val)) := P.filter (fun p => p.val a=z ∧ p.val ⟨a.val+i.val+1,by omega⟩=v)
  have hsub : (P.filter (fun p => p.val a=z)).filter (fun p => v∈labels H a p) ⊆ univ.biUnion E := by
    intro p hp
    obtain ⟨i,_,hi⟩ := mem_image.mp (mem_filter.mp hp).2
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,
      (mem_filter.mp (mem_filter.mp hp).1).2,hi⟩⟩
  calc
    _ ≤ (univ.biUnion E).card := card_le_card hsub
    _ ≤ ∑ i, (E i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin (n-a.val), L a.val*D^(n-a.val-1) := by
      apply sum_le_sum
      intro i _
      exact AdmissibleChainCounts.two_coordinates_bound H L n D x P hP hD a
        ⟨a.val+i.val+1,by omega⟩ (by dsimp; omega) z v
    _ = _ := by simp

lemma next_image (n D : ℕ) (P : Finset (Chain H n)) (hD : ∀ v, H.degree v≤D)
    (a : Fin (n+1)) (ha : a.val<n) (z : V) :
    ((P.filter (fun p => p.val a=z)).image (fun p => p.val ⟨a.val+1,by omega⟩)).card≤D := by
  have hsub : (P.filter (fun p => p.val a=z)).image (fun p => p.val ⟨a.val+1,by omega⟩) ⊆ H.neighborFinset z := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    apply (H.mem_neighborFinset _ _).mpr
    have hh := p.property ⟨a.val,ha⟩
    change H.Adj (p.val a) _ at hh
    rwa [(mem_filter.mp hp).2] at hh
  exact (card_le_card hsub).trans ((H.card_neighborFinset_eq_degree z).trans_le (hD z))

end
end AdmissibleSuffixCounts

end -- AdmissibleSuffixCounts

section -- AdmissiblePinnedSelection

/- A large admissible path family has a large fiber at a permitted hub. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace AdmissiblePinnedSelection
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

lemma select (L : ℕ → ℕ) (hL : Monotone L) (n D K : ℕ) (hDpos : 1≤D)
    (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (a : Fin (n+1)) (ha : a.val<n)
    (S : Finset V) (hx : x∉S)
    (hlarge : (S.card+K)*L (n-1)*D^(n-1)<P.card) :
    ∃ z : V, z∉S ∧ K*L (n-1)*D^(n-a.val-1)<(P.filter (fun p => p.val a=z)).card := by
  let Bad := P.filter (fun p => p.val a∈S)
  let Q := P.filter (fun p => p.val a∉S)
  have hbad : Bad.card≤S.card*L (n-1)*D^(n-1) := by
    by_cases ha0 : a.val=0
    · have ha' : a=0 := Fin.ext ha0
      have he : Bad=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := (mem_filter.mp hp).2
        rw [ha',(hP p (mem_filter.mp hp).1).2] at hh
        exact hx hh
      rw [he,card_empty]
      exact Nat.zero_le _
    · have hsub : Bad⊆S.biUnion (fun v => P.filter (fun p => p.val a=v)) := by
        intro p hp
        exact mem_biUnion.mpr ⟨p.val a,(mem_filter.mp hp).2,mem_filter.mpr ⟨(mem_filter.mp hp).1,rfl⟩⟩
      have hb (v : V) : (P.filter (fun p => p.val a=v)).card≤L (n-1)*D^(n-1) := by
        exact (AdmissibleChainCounts.prefix_bound H L n D x P hP hD a ha v).trans
          (Nat.mul_le_mul (hL (by omega)) (Nat.pow_le_pow_right hDpos (by omega)))
      calc
        _ ≤ _ := card_le_card hsub
        _ ≤ ∑ v∈S, (P.filter (fun p => p.val a=v)).card := card_biUnion_le
        _ ≤ ∑ _v∈S, L (n-1)*D^(n-1) := sum_le_sum (fun v _ => hb v)
        _ = _ := by simp [mul_assoc]
  have hsplit : Bad.card+Q.card=P.card := card_filter_add_card_filter_not (s := P) (fun p => p.val a∈S)
  have hQ : K*L (n-1)*D^(n-1)<Q.card := by nlinarith only [hbad,hsplit,hlarge]
  have himage : (Q.image (fun p => p.val a)).card≤D^a.val :=
    AdmissibleChainCounts.index_image_bound H n D x Q
      (fun p hp => (hP p (mem_filter.mp hp).1).2) hD a
  by_contra hn
  push_neg at hn
  have hfiber (z : V) (hz : z∈Q.image (fun p => p.val a)) :
      (Q.filter (fun p => p.val a=z)).card≤K*L (n-1)*D^(n-a.val-1) := by
    obtain ⟨p,hp,he⟩ := mem_image.mp hz
    have hzS : z∉S := he ▸ (mem_filter.mp hp).2
    exact (card_le_card (by intro q hq; exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hq).1).1,(mem_filter.mp hq).2⟩)).trans (hn z hzS)
  have hb := card_le_mul_card_image_of_maps_to (s := Q) (t := Q.image (fun p => p.val a))
    (f := fun p => p.val a) (fun p hp => mem_image.mpr ⟨p,hp,rfl⟩)
    (K*L (n-1)*D^(n-a.val-1)) hfiber
  have hm := Nat.mul_le_mul_left (K*L (n-1)*D^(n-a.val-1)) himage
  have he : (K*L (n-1)*D^(n-a.val-1))*D^a.val=K*L (n-1)*D^(n-1) := by
    rw [mul_assoc,← pow_add]
    congr 2
    omega
  rw [he] at hm
  omega

end
end AdmissiblePinnedSelection

end -- AdmissiblePinnedSelection

section -- FiniteRowFans

/- Pack disjoint stars whose rays are finite labelled objects. -/
open Finset
namespace FiniteRowFans
set_option maxHeartbeats 2500000
universe u v
noncomputable section
variable {A : Type u} {V : Type v} [Fintype A]
local instance : DecidableEq V := Classical.decEq _

abbrev Star (A : Type u) (s : ℕ) := Fin s → A

def whole (row : A → V) (label : A → Finset V) (p : A) : Finset V := insert (row p) (label p)

def starLabels (row : A → V) (label : A → Finset V) (s : ℕ) (f : Star A s) : Finset V :=
  univ.biUnion (fun i => whole row label (f i))

def Valid (P : Finset A) (row : A → V) (label : A → Finset V) (s : ℕ) (f : Star A s) : Prop :=
  (∀ i, f i∈P) ∧ (∀ i j, row (f i)=row (f j)) ∧
    ∀ i j, i≠j → Disjoint (label (f i)) (label (f j))

lemma starLabels_card (row : A → V) (label : A → Finset V) (s ℓ : ℕ) (f : Star A s)
    (hcard : ∀ i, (label (f i)).card≤ℓ) (hrow : ∀ i j, row (f i)=row (f j)) :
    (starLabels row label s f).card≤1+s*ℓ := by
  by_cases hs : 0<s
  · have hsub : starLabels row label s f ⊆ insert (row (f ⟨0,hs⟩)) (univ.biUnion (fun i => label (f i))) := by
      intro v hv
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
      rcases mem_insert.mp hi with he | he
      · exact mem_insert.mpr (Or.inl (he.trans (hrow i ⟨0,hs⟩)))
      · exact mem_insert.mpr (Or.inr (mem_biUnion.mpr ⟨i,mem_univ _,he⟩))
    have hh := card_biUnion_le (s := (univ : Finset (Fin s))) (t := fun i => label (f i))
    have hb : (∑ i, (label (f i)).card)≤s*ℓ := by
      calc
        _ ≤ ∑ _i : Fin s, ℓ := sum_le_sum (fun i _ => hcard i)
        _ = _ := by simp
    exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by omega))
  · have he : s=0 := by omega
    subst s
    simp [starLabels]

lemma avoid (P : Finset A) (row : A → V) (label : A → Finset V) (s ℓ N M R : ℕ)
    (hs : 0<s) (hcard : ∀ p∈P, (label p).card≤ℓ)
    (hN : (P.image row).card≤N)
    (hM : ∀ v, (P.filter (fun p => v∈whole row label p)).card≤M)
    (hR : ∀ y v, ((P.filter (fun p => row p=y)).filter (fun p => v∈label p)).card≤R)
    (S : Finset V) (hP : N*(ℓ*s*R)+S.card*M<P.card) :
    ∃ f : Star A s, Valid P row label s f ∧ Disjoint (starLabels row label s f) S := by
  let Q := P.filter (fun p => Disjoint (whole row label p) S)
  have hbad := FiniteLabelPacking.hit_le P (whole row label) M hM S
  have hsplit := card_filter_add_card_filter_not (s := P) (fun p => Disjoint (whole row label p) S)
  have hQ : N*(ℓ*s*R)<Q.card := by dsimp only [Q]; omega
  have hrow : ∃ y∈P.image row, ℓ*s*R<(Q.filter (fun p => row p=y)).card := by
    by_contra hn
    push_neg at hn
    have hb := card_le_mul_card_image_of_maps_to (s := Q) (t := P.image row) (f := row)
      (fun p hp => mem_image.mpr ⟨p,(mem_filter.mp hp).1,rfl⟩) (ℓ*s*R) hn
    have hm := Nat.mul_le_mul_right (ℓ*s*R) hN
    nlinarith only [hb,hm,hQ]
  obtain ⟨y,hy,hlarge⟩ := hrow
  let T := Q.filter (fun p => row p=y)
  have hTR (v : V) : (T.filter (fun p => v∈label p)).card≤R := by
    apply (card_le_card ?_).trans (hR y v)
    intro p hp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1,
      (mem_filter.mp (mem_filter.mp hp).1).2⟩,(mem_filter.mp hp).2⟩
  obtain ⟨f,hf,hdis⟩ := FiniteLabelPacking.select ℓ s (fun _ => (↑T : Set A)) label
    (fun _ p hp => hcard p (mem_filter.mp (mem_filter.mp hp).1).1) (by
      intro i U hU
      apply FiniteLabelPacking.avoid_of_card T label R hTR U
      exact (Nat.mul_le_mul_right R hU).trans_lt hlarge)
  refine ⟨f,⟨fun i => (mem_filter.mp (mem_filter.mp (hf i)).1).1,?_,hdis⟩,?_⟩
  · intro i j
    exact (mem_filter.mp (hf i)).2.trans (mem_filter.mp (hf j)).2.symm
  · apply Finset.disjoint_left.mpr
    intro v hv hvS
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (mem_filter.mp (mem_filter.mp (hf i)).1).2 hi hvS

lemma select (P : Finset A) (row : A → V) (label : A → Finset V) (s t ℓ N M R : ℕ)
    (hs : 0<s) (hcard : ∀ p∈P, (label p).card≤ℓ)
    (hN : (P.image row).card≤N)
    (hM : ∀ v, (P.filter (fun p => v∈whole row label p)).card≤M)
    (hR : ∀ y v, ((P.filter (fun p => row p=y)).filter (fun p => v∈label p)).card≤R)
    (S : Finset V) (hP : N*(ℓ*s*R)+(S.card+(1+s*ℓ)*t)*M<P.card) :
    ∃ f : Fin t → Star A s, (∀ i, Valid P row label s (f i)) ∧
      (∀ i, Disjoint (starLabels row label s (f i)) S) ∧
      ∀ i j, i≠j → Disjoint (starLabels row label s (f i)) (starLabels row label s (f j)) := by
  let T : Set (Star A s) := {f | Valid P row label s f ∧ Disjoint (starLabels row label s f) S}
  obtain ⟨f,hf,hdis⟩ := FiniteLabelPacking.select (1+s*ℓ) t (fun _ => T) (starLabels row label s)
    (fun _ f hf => starLabels_card row label s ℓ f (fun i => hcard _ (hf.1.1 i)) hf.1.2.1) (by
      intro i U hU
      have hSU : (S∪U).card≤S.card+(1+s*ℓ)*t := (card_union_le _ _).trans (Nat.add_le_add_left hU _)
      obtain ⟨g,hg,hdis⟩ := avoid P row label s ℓ N M R hs hcard hN hM hR (S∪U)
        ((Nat.add_le_add_left (Nat.mul_le_mul_right M hSU) _).trans_lt hP)
      exact ⟨g,⟨hg,hdis.mono_right (subset_union_left)⟩,hdis.mono_right (subset_union_right)⟩)
  exact ⟨f,fun i => (hf i).1,fun i => (hf i).2,hdis⟩

end
end FiniteRowFans

end -- FiniteRowFans

section -- AdmissibleSuffixFans

/- Disjoint suffix fans of any positive arm length, selected from many
admissible paths with a common initial vertex. -/
open Finset SimpleGraph ChainCounting GoodChains AdmissibleSuffixCounts
namespace AdmissibleSuffixFans
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

def cost (n s t q : ℕ) : ℕ := s*n^2+(q+(1+s*n)*t)*n

lemma select_at (L : ℕ → ℕ) (hL : Monotone L) (n D s t : ℕ) (hs : 0<s)
    (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (a : Fin (n+1)) (ha : a.val+1<n) (z : V) (S : Finset V)
    (hlarge : cost n s t S.card*L (n-1)*D^(n-a.val-1)<(P.filter (fun p => p.val a=z)).card) :
    ∃ f : Fin t → Fin s → Chain H n,
      (∀ i, FiniteRowFans.Valid (P.filter (fun p => p.val a=z))
        (fun p => p.val ⟨a.val+1,by omega⟩) (labels H ⟨a.val+1,by omega⟩) s (f i)) ∧
      (∀ i, Disjoint (FiniteRowFans.starLabels (fun p => p.val ⟨a.val+1,by omega⟩)
        (labels H ⟨a.val+1,by omega⟩) s (f i)) S) ∧
      ∀ i j, i≠j → Disjoint (FiniteRowFans.starLabels (fun p => p.val ⟨a.val+1,by omega⟩)
        (labels H ⟨a.val+1,by omega⟩) s (f i)) (FiniteRowFans.starLabels (fun p => p.val ⟨a.val+1,by omega⟩)
        (labels H ⟨a.val+1,by omega⟩) s (f j)) := by
  let b : Fin (n+1) := ⟨a.val+1,by omega⟩
  let Q := P.filter (fun p => p.val a=z)
  let r := n-a.val-1
  let M := (n-a.val)*(L a.val*D^(n-a.val-1))
  let R := r*(L b.val*D^(r-1))
  have hr : 0<r := by dsimp [r]; omega
  have hcard (p : Chain H n) (hp : p∈Q) : (labels H b p).card≤r := by
    simpa only [b,r,Nat.sub_add_eq] using labels_card H b p
  have hN : (Q.image (fun p => p.val b)).card≤D := next_image H n D P hD a (by omega) z
  have hM (v : V) : (Q.filter (fun p => v∈FiniteRowFans.whole (fun p => p.val b) (labels H b) p)).card≤M := by
    have he (p : Chain H n) : FiniteRowFans.whole (fun p => p.val b) (labels H b) p=labels H a p :=
      (labels_succ H a (by omega) p).symm
    simp_rw [he]
    exact incidence H L n D x P hP hD a (by omega) z v
  have hR (y v : V) : ((Q.filter (fun p => p.val b=y)).filter (fun p => v∈labels H b p)).card≤R := by
    have hh := incidence H L n D x P hP hD b (by dsimp [b]; omega) y v
    have hsub : (Q.filter (fun p => p.val b=y)).filter (fun p => v∈labels H b p) ⊆
        (P.filter (fun p => p.val b=y)).filter (fun p => v∈labels H b p) := by
      intro p hp
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1,
        (mem_filter.mp (mem_filter.mp hp).1).2⟩,(mem_filter.mp hp).2⟩
    apply (card_le_card hsub).trans
    simpa only [R,r,b,Nat.sub_add_eq] using hh
  have hLa : L a.val≤L (n-1) := hL (by omega)
  have hLb : L b.val≤L (n-1) := hL (by dsimp [b]; omega)
  have hrn : r≤n := by dsimp [r]; omega
  have hDpow : D*D^(r-1)=D^r := by rw [← pow_succ',Nat.sub_add_cancel hr]
  have hterm₁ : D*(r*s*R)≤s*n^2*L (n-1)*D^r := by
    calc
      _ = s*r^2*L b.val*(D*D^(r-1)) := by dsimp only [R]; ring
      _ = s*r^2*L b.val*D^r := by rw [hDpow]
      _ ≤ _ := by gcongr
  have hterm₂ : (S.card+(1+s*r)*t)*M≤(S.card+(1+s*n)*t)*n*L (n-1)*D^r := by
    dsimp only [M]
    change (S.card+(1+s*r)*t)*((n-a.val)*(L a.val*D^r))≤_
    calc
      _ = (S.card+(1+s*r)*t)*(n-a.val)*L a.val*D^r := by ring
      _ ≤ _ := by gcongr; exact Nat.sub_le n a.val
  have hbound : D*(r*s*R)+(S.card+(1+s*r)*t)*M≤cost n s t S.card*L (n-1)*D^r := by
    dsimp only [cost]
    nlinarith only [hterm₁,hterm₂]
  exact FiniteRowFans.select Q (fun p => p.val b) (labels H b) s t r D M R hs hcard hN hM hR S
    (hbound.trans_lt hlarge)

lemma select (L : ℕ → ℕ) (hL : Monotone L) (n D s t : ℕ) (hs : 0<s) (hDpos : 1≤D)
    (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (a : Fin (n+1)) (ha : a.val+1<n) (S : Finset V) (hx : x∉S)
    (hlarge : (S.card+cost n s t S.card)*L (n-1)*D^(n-1)<P.card) :
    ∃ z : V, z∉S ∧ ∃ f : Fin t → Fin s → Chain H n,
      (∀ i, FiniteRowFans.Valid (P.filter (fun p => p.val a=z))
        (fun p => p.val ⟨a.val+1,by omega⟩) (labels H ⟨a.val+1,by omega⟩) s (f i)) ∧
      (∀ i, Disjoint (FiniteRowFans.starLabels (fun p => p.val ⟨a.val+1,by omega⟩)
        (labels H ⟨a.val+1,by omega⟩) s (f i)) S) ∧
      ∀ i j, i≠j → Disjoint (FiniteRowFans.starLabels (fun p => p.val ⟨a.val+1,by omega⟩)
        (labels H ⟨a.val+1,by omega⟩) s (f i)) (FiniteRowFans.starLabels (fun p => p.val ⟨a.val+1,by omega⟩)
        (labels H ⟨a.val+1,by omega⟩) s (f j)) := by
  obtain ⟨z,hz,hl⟩ := AdmissiblePinnedSelection.select H L hL n D (cost n s t S.card) hDpos
    x P hP hD a (by omega) S hx hlarge
  obtain ⟨f,hf⟩ := select_at H L hL n D s t hs x P hP hD a ha z S hl
  exact ⟨z,hz,f,hf⟩

end
end AdmissibleSuffixFans

end -- AdmissibleSuffixFans

section -- AdmissibleEndSelection

/- Zero-length tails: select distinct last vertices adjacent to a common hub. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace AdmissibleEndSelection
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

lemma select (L : ℕ → ℕ) (hL : Monotone L) (n D t : ℕ) (hn : 2≤n) (hDpos : 1≤D)
    (x : V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hD : ∀ v, H.degree v≤D) (S : Finset V) (hx : x∉S)
    (hlarge : (S.card+(S.card+t))*L (n-1)*D^(n-1)<P.card) :
    ∃ z : V, z∉S ∧ ∃ f : Fin t → Chain H n,
      (∀ i, f i∈P ∧ (f i).val ⟨n-1,by omega⟩=z ∧ (f i).val (Fin.last n)∉S) ∧
      Function.Injective (fun i => (f i).val (Fin.last n)) := by
  let a : Fin (n+1) := ⟨n-1,by omega⟩
  obtain ⟨z,hz,hlarge'⟩ := AdmissiblePinnedSelection.select H L hL n D (S.card+t) hDpos x P hP hD
    a (by dsimp [a]; omega) S hx hlarge
  let Q := P.filter (fun p => p.val a=z)
  let Y := Q.image (fun p => p.val (Fin.last n))
  have hlocal : (S.card+t)*L (n-1)<Q.card := by
    simpa only [a,show n-(n-1)-1=0 by omega,pow_zero,mul_one] using hlarge'
  have hfiber (y : V) : (Q.filter (fun p => p.val (Fin.last n)=y)).card≤L (n-1) := by
    have he : Q.filter (fun p => p.val (Fin.last n)=y)=P.filter (fun p => p.val a=z ∧ p.val (Fin.last n)=y) := by
      ext p
      simp only [Q,mem_filter,and_assoc]
    rw [he]
    have hh := AdmissibleChainCounts.two_coordinates_bound H L n D x P hP hD a (Fin.last n)
      (by dsimp [a]; omega) z y
    simpa only [a,show n-(n-1)-1=0 by omega,pow_zero,mul_one] using hh
  have hb := card_le_mul_card_image_of_maps_to (s := Q) (t := Y) (f := fun p => p.val (Fin.last n))
    (fun p hp => mem_image.mpr ⟨p,hp,rfl⟩) (L (n-1)) (fun y _ => hfiber y)
  have hY : t≤(Y\S).card := by
    have hsplit := card_le_card_sdiff_add_card (s := Y) (t := S)
    by_contra ht
    have hm := Nat.mul_le_mul_left (L (n-1)) (show Y.card≤S.card+t by omega)
    nlinarith only [hlocal,hb,hm]
  obtain ⟨g⟩ : Nonempty (Fin t ↪ ↑(Y\S)) := Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin,Fintype.card_coe] using hY)
  have hex (i : Fin t) : ∃ p∈Q, p.val (Fin.last n)=(g i).val :=
    mem_image.mp (mem_sdiff.mp (g i).property).1
  choose f hf hend using hex
  refine ⟨z,hz,f,fun i => ⟨(mem_filter.mp (hf i)).1,(mem_filter.mp (hf i)).2,?_⟩,?_⟩
  · rw [hend i]
    exact (mem_sdiff.mp (g i).property).2
  · intro i j he
    apply g.injective
    apply Subtype.ext
    exact (hend i).symm.trans (he.trans (hend j))

end
end AdmissibleEndSelection

end -- AdmissibleEndSelection

section -- SuffixFanData

/- A uniform interface for selected suffix fans, including zero-length arms. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace SuffixFanData
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} (H : SimpleGraph V)

structure Data (l s t : ℕ) (S : Finset V) (x : V) (Z : Set V) where
  hub : V
  old : Fin t → V
  tail : Fin t × Fin s → Chain H l
  old_injective : Function.Injective old
  spoke : ∀ i, H.Adj hub (old i)
  tail_injective : ∀ e, Function.Injective (tail e).val
  tail_end : ∀ e, (tail e).val (Fin.last l)=old e.1
  tail_start : ∀ e, (tail e).val 0∈Z
  front_disjoint : ∀ e f, e≠f → Disjoint (ChainFront.front H (tail e)) (ChainFront.front H (tail f))
  old_not_front : ∀ i e, old i∉ChainFront.front H (tail e)
  hub_not_tail : ∀ e i, hub≠(tail e).val i
  hub_avoid : hub∉S
  old_avoid : ∀ i, old i∉S
  tail_avoid : ∀ e i, (tail e).val i∉S
  initial_not_old : ∀ i, x≠old i
  initial_not_tail : ∀ e i, x≠(tail e).val i

variable [Fintype V]
local instance : DecidableRel H.Adj := Classical.decRel _

lemma zero (L : ℕ → ℕ) (hL : Monotone L) (n D s t : ℕ) (hn : 2≤n) (hDpos : 1≤D)
    (x : V) (Z : Set V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hZ : ∀ p∈P, p.val (Fin.last n)∈Z)
    (hD : ∀ v, H.degree v≤D) (S : Finset V) (hx : x∉S)
    (hlarge : (S.card+(S.card+t))*L (n-1)*D^(n-1)<P.card) (ht : 0<t) :
    ∃ F : Data H 0 s t S x Z, F.hub≠x := by
  obtain ⟨z,hz,f,hf,hinj⟩ := AdmissibleEndSelection.select H L hL n D t hn hDpos x P hP hD S hx hlarge
  let old (i : Fin t) := (f i).val (Fin.last n)
  let tail (e : Fin t × Fin s) : Chain H 0 := ⟨fun _ => old e.1,fun i => Fin.elim0 i⟩
  have hspoke (i : Fin t) : H.Adj z (old i) := by
    have hh := (f i).property ⟨n-1,by omega⟩
    change H.Adj ((f i).val ⟨n-1,by omega⟩) ((f i).val ⟨(n-1)+1,by omega⟩) at hh
    rw [(hf i).2.1] at hh
    simpa only [old,Nat.sub_add_cancel (by omega : 1≤n),Fin.last] using hh
  have hxi (i : Fin t) : x≠old i := by
    intro he
    have hh := congrArg Fin.val ((hP (f i) (hf i).1).1.1 ((hP (f i) (hf i).1).2.trans he))
    simp only [Fin.val_zero,Fin.val_last] at hh
    omega
  have hfront (e : Fin t × Fin s) : ChainFront.front H (tail e)=∅ := by simp [ChainFront.front]
  let F : Data H 0 s t S x Z := {
    hub := z
    old := old
    tail := tail
    old_injective := hinj
    spoke := hspoke
    tail_injective := fun e i j _ => Fin.ext (by omega)
    tail_end := fun _ => rfl
    tail_start := fun e => hZ (f e.1) (hf e.1).1
    front_disjoint := fun e f _ => by rw [hfront e,hfront f]; exact disjoint_empty_left _
    old_not_front := fun i e => by rw [hfront e]; exact notMem_empty _
    hub_not_tail := fun e i => (hspoke e.1).ne
    hub_avoid := hz
    old_avoid := fun i => (hf i).2.2
    tail_avoid := fun e _ => (hf e.1).2.2
    initial_not_old := hxi
    initial_not_tail := fun e _ => hxi e.1 }
  refine ⟨F,?_⟩
  intro he
  let i : Fin t := ⟨0,ht⟩
  have hh := congrArg Fin.val ((hP (f i) (hf i).1).1.1 ((hf i).2.1.trans (he.trans (hP (f i) (hf i).1).2.symm)))
  change n-1=0 at hh
  omega

end
end SuffixFanData

end -- SuffixFanData

section -- PositiveSuffixFanData

/- Convert selected admissible suffix stars into the uniform tail-data interface. -/
open Finset SimpleGraph ChainCounting GoodChains AdmissibleSuffixCounts
namespace SuffixFanData
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _

lemma positive (L : ℕ → ℕ) (hL : Monotone L) (n l D s t : ℕ) (hl : 0<l) (hln : l<n)
    (hs : 0<s) (hDpos : 1≤D) (x : V) (Z : Set V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hZ : ∀ p∈P, p.val (Fin.last n)∈Z)
    (hD : ∀ v, H.degree v≤D) (S : Finset V) (hx : x∉S)
    (hlarge : (S.card+AdmissibleSuffixFans.cost n s t S.card)*L (n-1)*D^(n-1)<P.card) :
    Nonempty (Data H l s t S x Z) := by
  classical
  let a : Fin (n+1) := ⟨n-l-1,by omega⟩
  have ha : a.val+1<n := by dsimp [a]; omega
  let b : Fin (n+1) := ⟨a.val+1,by omega⟩
  have hbl : b.val+l=n := by dsimp [a,b]; omega
  obtain ⟨z,hz,f,hf,hfS,hfdis⟩ := AdmissibleSuffixFans.select H L hL n D s t hs hDpos x P hP hD a ha S hx hlarge
  let row (p : Chain H n) := p.val b
  let star (i : Fin t) := FiniteRowFans.starLabels row (labels H b) s (f i)
  let old (i : Fin t) := row (f i ⟨0,hs⟩)
  let q (e : Fin t × Fin s) := reverse H (segment H (f e.1 e.2) b.val l (by omega))
  have hfp (i : Fin t) (j : Fin s) : f i j∈P := (mem_filter.mp ((hf i).1 j)).1
  have hfa (i : Fin t) (j : Fin s) : (f i j).val a=z := (mem_filter.mp ((hf i).1 j)).2
  have hadm (i : Fin t) (j : Fin s) := (hP (f i j) (hfp i j)).1
  have hrow (i : Fin t) (j : Fin s) : (f i j).val b=old i := (hf i).2.1 j ⟨0,hs⟩
  have hlabelstar (i : Fin t) (j : Fin s) : labels H b (f i j)⊆star i := by
    intro v hv
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_insert_of_mem hv⟩
  have holdstar (i : Fin t) : old i∈star i :=
    mem_biUnion.mpr ⟨⟨0,hs⟩,mem_univ _,mem_insert_self _ _⟩
  have hqstart (e : Fin t × Fin s) : (q e).val 0=(f e.1 e.2).val (Fin.last n) := by
    dsimp only [q]
    rw [reverse_start]
    simp only [segment_apply,Fin.val_last,hbl]
    rfl
  have hqend (e : Fin t × Fin s) : (q e).val (Fin.last l)=old e.1 := by
    dsimp only [q]
    rw [reverse_last]
    simpa only [segment_apply,Fin.val_zero,Nat.add_zero] using hrow e.1 e.2
  have hqinj (e : Fin t × Fin s) : Function.Injective (q e).val :=
    reverse_injective H (segment_injective H (hadm e.1 e.2).1 b.val l (by omega))
  have hqfront (e : Fin t × Fin s) : ChainFront.front H (q e)⊆labels H b (f e.1 e.2) := by
    intro v hv
    obtain ⟨i,hi,he⟩ := (ChainFront.mem_front H (q e) v).mp hv
    apply (mem_labels H b (f e.1 e.2) v).mpr
    refine ⟨⟨b.val+i.rev.val,by omega⟩,?_,he⟩
    simp only [Fin.val_rev]
    omega
  have hqstar (e : Fin t × Fin s) (i : Fin (l+1)) : (q e).val i∈star e.1 := by
    have hm : (q e).val i∈labels H a (f e.1 e.2) := by
      apply (mem_labels H a (f e.1 e.2) _).mpr
      refine ⟨⟨b.val+i.rev.val,by omega⟩,?_,rfl⟩
      dsimp only [b]
      omega
    rw [labels_succ H a (by omega)] at hm
    exact mem_biUnion.mpr ⟨e.2,mem_univ _,hm⟩
  have holdinj : Function.Injective old := by
    intro i j he
    by_contra hij
    exact Finset.disjoint_left.mp (hfdis i j hij) (holdstar i) (he.symm ▸ holdstar j)
  have hspoke (i : Fin t) : H.Adj z (old i) := by
    have hh := (f i ⟨0,hs⟩).property ⟨a.val,by omega⟩
    change H.Adj ((f i ⟨0,hs⟩).val a) ((f i ⟨0,hs⟩).val b) at hh
    rwa [hfa i ⟨0,hs⟩,hrow i ⟨0,hs⟩] at hh
  have hdis (e d : Fin t × Fin s) (hed : e≠d) : Disjoint (ChainFront.front H (q e)) (ChainFront.front H (q d)) := by
    rcases e with ⟨i,j⟩
    rcases d with ⟨i',j'⟩
    by_cases hii : i=i'
    · subst i'
      have hjj : j≠j' := fun h => hed (Prod.ext rfl h)
      exact ((hf i).2.2 j j' hjj).mono (hqfront (i,j)) (hqfront (i,j'))
    · exact (hfdis i i' hii).mono ((hqfront (i,j)).trans (hlabelstar i j))
        ((hqfront (i',j')).trans (hlabelstar i' j'))
  have holdnot (i : Fin t) (e : Fin t × Fin s) : old i∉ChainFront.front H (q e) := by
    intro hv
    by_cases hie : i=e.1
    · have hh := pinned_notMem H b (f e.1 e.2) (hadm e.1 e.2).1
      rw [hrow e.1 e.2] at hh
      exact hh (hie ▸ hqfront e hv)
    · exact Finset.disjoint_left.mp (hfdis i e.1 hie) (holdstar i)
        (hqfront e hv |> hlabelstar e.1 e.2)
  have hzq (e : Fin t × Fin s) (i : Fin (l+1)) : z≠(q e).val i := by
    intro he
    have hh := congrArg Fin.val ((hadm e.1 e.2).1 ((hfa e.1 e.2).trans he))
    change a.val=b.val+i.rev.val at hh
    dsimp only [b] at hh
    omega
  have hxq (e : Fin t × Fin s) (i : Fin (l+1)) : x≠(q e).val i := by
    intro he
    have hh := congrArg Fin.val ((hadm e.1 e.2).1 ((hP (f e.1 e.2) (hfp e.1 e.2)).2.trans he))
    change 0=b.val+i.rev.val at hh
    dsimp only [b] at hh
    omega
  have hxold (i : Fin t) : x≠old i := by
    intro he
    exact hxq (i,⟨0,hs⟩) (Fin.last l) (he.trans (hqend (i,⟨0,hs⟩)).symm)
  exact ⟨{
    hub := z
    old := old
    tail := q
    old_injective := holdinj
    spoke := hspoke
    tail_injective := hqinj
    tail_end := hqend
    tail_start := fun e => (hqstart e).symm ▸ hZ (f e.1 e.2) (hfp e.1 e.2)
    front_disjoint := hdis
    old_not_front := holdnot
    hub_not_tail := hzq
    hub_avoid := hz
    old_avoid := fun i hi => Finset.disjoint_left.mp (hfS i) (holdstar i) hi
    tail_avoid := fun e i hi => Finset.disjoint_left.mp (hfS e.1) (hqstar e i) hi
    initial_not_old := hxold
    initial_not_tail := hxq }⟩

end
end SuffixFanData

end -- PositiveSuffixFanData

section -- SuffixFanDataProperties

/- Vertex sets and uniform budgets for suffix fan data. -/
open Finset SimpleGraph ChainCounting GoodChains
namespace SuffixFanData
set_option maxHeartbeats 2500000
universe u
noncomputable section
variable {V : Type u} (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _

variable {l s t : ℕ} {S : Finset V} {x : V} {Z : Set V}

def Data.vertices (F : Data H l s t S x Z) : Finset V :=
  insert F.hub (univ.image F.old ∪ univ.biUnion (fun e => ChainFront.front H (F.tail e)))

lemma Data.hub_mem (F : Data H l s t S x Z) : F.hub∈F.vertices H := mem_insert_self _ _

lemma Data.old_mem (F : Data H l s t S x Z) (i : Fin t) : F.old i∈F.vertices H :=
  mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))


lemma Data.vertices_card (F : Data H l s t S x Z) : (F.vertices H).card≤1+t+t*s*l := by
  have h₁ := card_insert_le F.hub (univ.image F.old ∪ univ.biUnion (fun e => ChainFront.front H (F.tail e)))
  have h₂ := card_union_le (univ.image F.old) (univ.biUnion (fun e => ChainFront.front H (F.tail e)))
  have h₃ : (univ.image F.old).card≤t := card_image_le.trans_eq (by simp)
  have h₄ : (univ.biUnion (fun e => ChainFront.front H (F.tail e))).card≤t*s*l := by
    calc
      _ ≤ ∑ e, (ChainFront.front H (F.tail e)).card := card_biUnion_le
      _ ≤ ∑ _e : Fin t × Fin s, l := sum_le_sum (fun e _ => ChainFront.card_le H (F.tail e))
      _ = _ := by simp
  change (insert F.hub (univ.image F.old ∪ univ.biUnion (fun e => ChainFront.front H (F.tail e)))).card≤_
  omega

lemma Data.initial_not_vertices (F : Data H l s t S x Z) (hxh : F.hub≠x) : x∉F.vertices H := by
  intro hx
  rcases mem_insert.mp hx with he | he
  · exact hxh he.symm
  · rcases mem_union.mp he with he | he
    · obtain ⟨i,_,hi⟩ := mem_image.mp he
      exact F.initial_not_old i hi.symm
    · obtain ⟨e,_,he⟩ := mem_biUnion.mp he
      obtain ⟨i,_,hi⟩ := (ChainFront.mem_front H (F.tail e) x).mp he
      exact F.initial_not_tail e i hi.symm

lemma Data.zero_old_allowed {s t : ℕ} (F : Data H 0 s t S x Z) (hs : 0<s) (i : Fin t) : F.old i∈Z := by
  have hh := F.tail_start (i,⟨0,hs⟩)
  have he := F.tail_end (i,⟨0,hs⟩)
  change (F.tail (i,⟨0,hs⟩)).val 0=F.old i at he
  rwa [he] at hh

variable [Fintype V]
local instance : DecidableRel H.Adj := Classical.decRel _

def budget (n s t q : ℕ) : ℕ := 2*q+t+AdmissibleSuffixFans.cost n s t q


lemma choose (L : ℕ → ℕ) (hL : Monotone L) (n l D s t : ℕ) (hn : 2≤n) (hln : l<n)
    (hs : 0<s) (ht : 0<t) (hDpos : 1≤D) (x : V) (Z : Set V) (P : Finset (Chain H n))
    (hP : ∀ p∈P, Admissible H L n p ∧ p.val 0=x)
    (hZ : ∀ p∈P, p.val (Fin.last n)∈Z)
    (hD : ∀ v, H.degree v≤D) (S : Finset V) (hx : x∉S)
    (hlarge : budget n s t S.card*L (n-1)*D^(n-1)<P.card) : Nonempty (Data H l s t S x Z) := by
  by_cases hl : l=0
  · subst l
    obtain ⟨F,hF⟩ := zero H L hL n D s t hn hDpos x Z P hP hZ hD S hx (by
      apply lt_of_le_of_lt _ hlarge
      gcongr
      unfold budget
      omega) ht
    exact ⟨F⟩
  · apply positive H L hL n l D s t (by omega) hln hs hDpos x Z P hP hZ hD S hx
    apply lt_of_le_of_lt _ hlarge
    gcongr
    unfold budget
    omega

end
end SuffixFanData

end -- SuffixFanDataProperties

section -- TwoColorPlacement

/- Place the two color classes in two disjoint injective copies of the old vertex set. -/
namespace TwoColorPlacement
universe u v
variable {W : Type u} {V : Type v}

def place (c : W → Fin 2) (f g : W → V) (w : W) : V := if c w=0 then f w else g w

def hubs (x y : V) (i : Fin 2) : V := if i=0 then x else y

lemma place_zero (c : W → Fin 2) (f g : W → V) (w : W) (hw : c w=0) : place c f g w=f w := by
  simp only [place,if_pos hw]

lemma place_one (c : W → Fin 2) (f g : W → V) (w : W) (hw : c w=1) : place c f g w=g w := by
  simp [place,hw]

lemma place_injective (c : W → Fin 2) (f g : W → V) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ a b, f a≠g b) : Function.Injective (place c f g) := by
  intro a b he
  dsimp only [place] at he
  split_ifs at he
  · exact hf he
  · exact (hfg a b he).elim
  · exact (hfg b a he.symm).elim
  · exact hg he

lemma hubs_injective (x y : V) (hxy : x≠y) : Function.Injective (hubs x y) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [hubs]

lemma hubs_ne_place (c : W → Fin 2) (f g : W → V) (x y : V)
    (hxf : ∀ w, x≠f w) (hxg : ∀ w, x≠g w) (hyf : ∀ w, y≠f w) (hyg : ∀ w, y≠g w) :
    ∀ i w, hubs x y i≠place c f g w := by
  intro i w
  dsimp only [hubs,place]
  split_ifs <;> first | exact hxf w | exact hxg w | exact hyf w | exact hyg w

lemma spoke (H : SimpleGraph V) (c : W → Fin 2) (f g : W → V) (x y : V)
    (hxf : ∀ w, H.Adj x (f w)) (hyg : ∀ w, H.Adj y (g w)) :
    ∀ i w, c w=i → H.Adj (hubs x y i) (place c f g w) := by
  intro i w hi
  dsimp only [hubs,place]
  rw [hi]
  split_ifs
  · exact hxf w
  · exact hyg w

end TwoColorPlacement

end -- TwoColorPlacement

section -- HubFanReservoirCopy

/- A selected suffix fan and two heavy reservoirs force a hub subdivision. -/
open Finset SimpleGraph ChainCounting
namespace HubFanReservoirCopy
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 200000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] {F : SimpleGraph W} (c : F.Coloring (Fin 2))
variable {V : Type v} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : Fintype (GraphSubdivision.Edge F) := Fintype.ofFinite _

lemma copy (B j m l k s t : ℕ) (hj : 0<j) (hm : 0 < m) (hlen : m*j+l=k+1)
    (S : Finset V) (x : V) (Z : Set V) (T : SuffixFanData.Data H l s t S x Z)
    (wi : W ↪ Fin t) (ei : GraphSubdivision.Edge F ↪ Fin s)
    (u : W → V) (z₀ : V) (hu : Function.Injective u) (hzu : ∀ w, H.Adj z₀ (u w))
    (huS : ∀ w, u w∈S) (hzS : z₀∈S)
    (A C : Finset V) (huA : ∀ w, u w∈A)
    (hqC : ∀ e, (T.tail (wi (ColoredEdges.right c e),ei e)).val 0∈BipartiteReservoirPaths.pool A C m)
    (hcomplete : ∀ a∈A, ∀ b∈C, (HeavyShadow.graph H B j).Adj a b)
    (hA : Fintype.card W+2+Nat.card (GraphSubdivision.Edge F)*(l+1)+
      (m-1)*Nat.card (GraphSubdivision.Edge F)+m+2≤A.card)
    (hC : Fintype.card W+2+Nat.card (GraphSubdivision.Edge F)*(l+1)+
      (m-1)*Nat.card (GraphSubdivision.Edge F)+m+2≤C.card)
    (hB : (j-1)*(Nat.card (GraphSubdivision.Edge F)*m)+
      (Fintype.card W+2+Nat.card (GraphSubdivision.Edge F)*(l+1))+Nat.card (GraphSubdivision.Edge F)*(m+1)≤B) :
    HubPathSubdivision.graph c k ⊑ H := by
  classical
  let E := GraphSubdivision.Edge F
  let g (w : W) := T.old (wi w)
  let f := TwoColorPlacement.place c u g
  let z := TwoColorPlacement.hubs z₀ T.hub
  let q (e : E) := T.tail (wi (ColoredEdges.right c e),ei e)
  have hg : Function.Injective g := T.old_injective.comp wi.injective
  have hug (a b : W) : u a≠g b := by
    intro he
    apply T.old_avoid (wi b)
    change g b∈S
    exact he ▸ huS a
  have hzu' (w : W) : z₀≠u w := (hzu w).ne
  have hzg (w : W) : z₀≠g w := by
    intro he
    apply T.old_avoid (wi w)
    change g w∈S
    exact he ▸ hzS
  have hTu (w : W) : T.hub≠u w := by intro he; exact T.hub_avoid (he.symm ▸ huS w)
  have hTg (w : W) : T.hub≠g w := (T.spoke (wi w)).ne
  have hzz : z₀≠T.hub := by intro he; exact T.hub_avoid (he ▸ hzS)
  have hfi : Function.Injective f := TwoColorPlacement.place_injective c u g hu hg hug
  have hzi : Function.Injective z := TwoColorPlacement.hubs_injective z₀ T.hub hzz
  have hzf : ∀ i w, z i≠f w := TwoColorPlacement.hubs_ne_place c u g z₀ T.hub hzu' hzg hTu hTg
  have hspoke : ∀ i w, c w=i → H.Adj (z i) (f w) :=
    TwoColorPlacement.spoke H c u g z₀ T.hub hzu (fun w => T.spoke (wi w))
  have hfleft (e : E) : f (ColoredEdges.left c e)=u (ColoredEdges.left c e) :=
    TwoColorPlacement.place_zero c u g _ (ColoredEdges.left_color c e)
  have hfright (e : E) : f (ColoredEdges.right c e)=g (ColoredEdges.right c e) :=
    TwoColorPlacement.place_one c u g _ (ColoredEdges.right_color c e)
  have hqend (e : E) : (q e).val (Fin.last l)=f (ColoredEdges.right c e) := by
    rw [hfright]
    exact T.tail_end _
  have hqdis (e d : E) (hed : e≠d) : Disjoint (ChainFront.front H (q e)) (ChainFront.front H (q d)) :=
    T.front_disjoint _ _ (fun h => hed (ei.injective (congrArg Prod.snd h)))
  have hqold (w : W) (e : E) : f w∉ChainFront.front H (q e) := by
    dsimp only [f,TwoColorPlacement.place]
    split_ifs
    · intro hw
      obtain ⟨i,_,hi⟩ := (ChainFront.mem_front H (q e) _).mp hw
      exact T.tail_avoid _ i (hi.symm ▸ huS w)
    · exact T.old_not_front (wi w) _
  have hqhub (i : Fin 2) (e : E) : z i∉ChainFront.front H (q e) := by
    intro hv
    obtain ⟨a,_,ha⟩ := (ChainFront.mem_front H (q e) _).mp hv
    by_cases hi : i=0
    · have hh : (q e).val a=z₀ := by simpa only [z,TwoColorPlacement.hubs,if_pos hi] using ha
      exact T.tail_avoid _ a (hh.symm ▸ hzS)
    · have hh : (q e).val a=T.hub := by simpa only [z,TwoColorPlacement.hubs,if_neg hi] using ha
      exact T.hub_not_tail _ a hh.symm
  have hstart (e d : E) (i : Fin (l+1)) : f (ColoredEdges.left c e)≠(q d).val i := by
    rw [hfleft]
    intro he
    exact T.tail_avoid _ i (he ▸ huS _)
  let TailVertices := univ.biUnion (fun e : E => univ.image (q e).val)
  let S' := univ.image f ∪ (univ.image z ∪ TailVertices)
  have hTail : TailVertices.card≤Fintype.card E*(l+1) := by
    calc
      _ ≤ ∑ e, (univ.image (q e).val).card := card_biUnion_le
      _ ≤ ∑ _e : E, (l+1) := sum_le_sum (fun e _ => card_image_le.trans_eq (by simp))
      _ = _ := by simp
  have hS' : S'.card≤Fintype.card W+2+Nat.card E*(l+1) := by
    have h₁ := card_union_le (univ.image f) (univ.image z ∪ TailVertices)
    have h₂ := card_union_le (univ.image z) TailVertices
    have hf' : (univ.image f).card≤Fintype.card W := card_image_le.trans_eq (by simp)
    have hz' : (univ.image z).card≤2 := card_image_le.trans_eq (by simp)
    rw [Nat.card_eq_fintype_card]
    dsimp only [S']
    omega
  have hfS' (w : W) : f w∈S' := mem_union_left _ (mem_image.mpr ⟨w,mem_univ _,rfl⟩)
  have hzS' (i : Fin 2) : z i∈S' := mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
  have hqS' (e : E) (i : Fin (l+1)) : (q e).val i∈S' :=
    mem_union_right _ (mem_union_right _ (mem_biUnion.mpr ⟨e,mem_univ _,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩))
  apply HubReservoirAssembly.copy c H B j m l k hj hm hlen A C S' z f q hzi hfi hzf hspoke
    (fun e => T.tail_injective _) hqend hqdis hqold hqhub
    (fun e => by rw [hfleft]; exact huA _) hqC hstart hcomplete hfS' hzS' hqS'
  · exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hS' _) _) _).trans hA
  · exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hS' _) _) _).trans hC
  · exact (Nat.add_le_add_right (Nat.add_le_add_left hS' _) _).trans hB

end
end HubFanReservoirCopy

end -- HubFanReservoirCopy

section -- AdmissibleHeavyCommon

/- Many admissible heavy paths give a large family of admissible paths whose
endpoints are heavy-adjacent to a fixed set of ordinary neighbors. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace AdmissibleHeavyCommon
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _
local instance (v : V) : DecidableEq (H.neighborSet v) := Classical.decEq _

lemma threshold_room (B j s κ K : ℕ) (hj : 0<j) (hB : 2*K*κ^(s+1)≤B) :
    2*K*κ^(s+1)*(threshold B (j-1))^2<threshold B j := by
  have hh := threshold_large B j hj
  have hjB : B≤j*B := by nlinarith
  exact (Nat.mul_le_mul_right _ (hB.trans hjB)).trans_lt hh

lemma local_select (B j d D κ s K : ℕ) (hj : 2≤j) (hs : 0<s) (hDpos : 0<D)
    (hd : 2*s^2≤d) (hκ : D≤κ*d) (hB : 2*K*κ^(s+1)≤B)
    (hD : ∀ w, H.degree w≤D) (v : V)
    (hlarge : 2*d*D^(j-1)<AdmissibleHeavyLinks.mass H B j v) :
    ∃ a : H.neighborSet v, ∃ f : Fin s → H.neighborSet v,
      Function.Injective f ∧ (∀ i, f i≠a) ∧ ∃ P : Finset (Chain H j),
      (∀ p∈P, Admissible H (threshold B) j p ∧ p.val 0=a.val ∧
        ∀ i, HeavyShadow.heavy H B j (f i).val (p.val (Fin.last j))) ∧
      K*threshold B (j-1)*D^(j-1)<P.card := by
  classical
  obtain ⟨a,T,hT,hmass⟩ := AdmissibleHeavyLinks.dense_fan H B j d D hj hD v hlarge
  let N (z : V) := (AdmissibleHeavyLinks.neighbors H B j v z).erase a
  let w (z : V) := (fiber H (threshold B) j a.val z).card
  have hw (z : V) (hz : z∈T) : threshold B j≤w z := (hT z hz).1.2.le
  obtain ⟨f,hf,hweight⟩ := WeightedAdmissibleSelection.select N
    (AdmissibleHeavyLinks.multiplicity H B j v) w T j s d D κ K (threshold B (j-1)) (threshold B j)
    hj hs hDpos (threshold_pos B (j-1)) hd
    (by simpa only [H.card_neighborSet_eq_degree] using hD v) hκ
    (threshold_room B j s κ K (by omega) hB)
    (fun z _ => AdmissibleHeavyLinks.multiplicity_le H B j v z) hw
    (fun z hz => (hT z hz).2) hmass
  let E (z : V) : Finset (Chain H j) := if ∀ i, f i∈N z then fiber H (threshold B) j a.val z else ∅
  let P := T.biUnion E
  have hE (z : V) (p : Chain H j) (hp : p∈E z) :
      (∀ i, f i∈N z) ∧ p∈fiber H (threshold B) j a.val z := by
    by_cases hz : ∀ i, f i∈N z
    · exact ⟨hz,by simpa only [E,if_pos hz] using hp⟩
    · simp only [E,if_neg hz,notMem_empty] at hp
  have hdis : ∀ z∈T, ∀ y∈T, z≠y → Disjoint (E z) (E y) := by
    intro z _ y _ hzy
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hz := ((mem_fiber H (threshold B) j a.val z p).mp (hE z p hp).2).2.2
    have hy := ((mem_fiber H (threshold B) j a.val y p).mp (hE y p hq).2).2.2
    exact hzy (hz.symm.trans hy)
  have hcard : P.card=∑ z∈T, if ∀ i, f i∈N z then w z else 0 := by
    rw [show P=T.biUnion E from rfl,card_biUnion hdis]
    apply sum_congr rfl
    intro z _
    dsimp only [E,w]
    split_ifs <;> simp only [card_empty]
  have hP : ∀ p∈P, Admissible H (threshold B) j p ∧ p.val 0=a.val ∧
      ∀ i, HeavyShadow.heavy H B j (f i).val (p.val (Fin.last j)) := by
    intro p hp
    obtain ⟨z,hz,hpz⟩ := mem_biUnion.mp hp
    obtain ⟨hfz,hpf⟩ := hE z p hpz
    obtain ⟨hadm,hstart,hend⟩ := (mem_fiber H (threshold B) j a.val z p).mp hpf
    refine ⟨hadm,hstart,?_⟩
    intro i
    rw [hend]
    exact (mem_filter.mp (mem_erase.mp (hfz i)).2).2
  have hPlarge : K*threshold B (j-1)*D^(j-1)<P.card := by rwa [hcard]
  have hfa (i : Fin s) : f i≠a := by
    obtain ⟨p,hp⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hPlarge)
    obtain ⟨z,hz,hpz⟩ := mem_biUnion.mp hp
    exact (mem_erase.mp ((hE z p hpz).1 i)).1
  exact ⟨a,f,hf,hfa,P,hP,hPlarge⟩

lemma global (B j d D κ s K : ℕ) (hj : 2≤j) (hs : 0<s) (hDpos : 0<D)
    (hd : 2*s^2≤d) (hκ : D≤κ*d) (hB : 2*K*κ^(s+1)≤B)
    (hD : ∀ w, H.degree w≤D)
    (hlarge : Fintype.card V*(2*d*D^(j-1))<(AdmissibleHeavyLinks.bad H B j).card) :
    ∃ v : V, ∃ a : H.neighborSet v, ∃ f : Fin s → H.neighborSet v,
      Function.Injective f ∧ (∀ i, f i≠a) ∧ ∃ P : Finset (Chain H j),
      (∀ p∈P, Admissible H (threshold B) j p ∧ p.val 0=a.val ∧
        ∀ i, HeavyShadow.heavy H B j (f i).val (p.val (Fin.last j))) ∧
      K*threshold B (j-1)*D^(j-1)<P.card := by
  have hh := hlarge.trans_le (AdmissibleHeavyLinks.bad_le_mass H B j hj)
  have hex : ∃ v : V, 2*d*D^(j-1)<AdmissibleHeavyLinks.mass H B j v := by
    by_contra hn
    push_neg at hn
    have hb : (∑ v, AdmissibleHeavyLinks.mass H B j v)≤Fintype.card V*(2*d*D^(j-1)) := by
      calc
        _ ≤ ∑ _v : V, 2*d*D^(j-1) := sum_le_sum (fun v _ => hn v)
        _ = _ := by simp
    omega
  obtain ⟨v,hv⟩ := hex
  obtain ⟨a,f,hf,hfa,P,hP,hPlarge⟩ := local_select H B j d D κ s K hj hs hDpos hd hκ hB hD v hv
  exact ⟨v,a,f,hf,hfa,P,hP,hPlarge⟩

end
end AdmissibleHeavyCommon

end -- AdmissibleHeavyCommon

section -- HubHeavyConfiguration

/- Force an arbitrary longer two-hub subdivision from the common-heavy
configuration supplied by admissible-path averaging. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace HubHeavyConfiguration
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] {F : SimpleGraph W} (c : F.Coloring (Fin 2))

def reserve (F : SimpleGraph W) (r : ℕ) : ℕ :=
  Fintype.card W+2+Nat.card (GraphSubdivision.Edge F)*(r+1)+r*Nat.card (GraphSubdivision.Edge F)+r+3

def cost (F : SimpleGraph W) (r : ℕ) : ℕ :=
  2*(reserve F r+1)+reserve F r+
    SuffixFanData.budget r (Nat.card (GraphSubdivision.Edge F)+1) (Fintype.card W+1) (2+2*reserve F r)

def liftBudget (F : SimpleGraph W) (r : ℕ) : ℕ :=
  r*(Nat.card (GraphSubdivision.Edge F)*r)+(Fintype.card W+2+Nat.card (GraphSubdivision.Edge F)*(r+1))+
    Nat.card (GraphSubdivision.Edge F)*(r+1)

lemma reserve_pos (F : SimpleGraph W) (r : ℕ) : 0<reserve F r := by unfold reserve; omega
lemma reserve_vertices (F : SimpleGraph W) (r : ℕ) : Fintype.card W≤reserve F r := by unfold reserve; omega

lemma budget_mono (n n' s t q q' : ℕ) (hn : n≤n') (hq : q≤q') :
    SuffixFanData.budget n s t q≤SuffixFanData.budget n' s t q' := by
  unfold SuffixFanData.budget AdmissibleSuffixFans.cost
  gcongr

variable {V : Type v} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _
local instance : Fintype (GraphSubdivision.Edge F) := Fintype.ofFinite _

lemma copy (r j m l B D : ℕ) (hj : 2≤j) (hjr : j≤r) (hm : 0 < m) (hl : l<j)
    (hr : m*j+l=r) (hDpos : 1≤D) (hD : ∀ v, H.degree v≤D) (hB : liftBudget F r≤B)
    (v : V) (a : H.neighborSet v) (f : Fin (reserve F r) → H.neighborSet v)
    (hf : Function.Injective f) (hfa : ∀ i, f i≠a) (P : Finset (Chain H j))
    (hP : ∀ p∈P, Admissible H (threshold B) j p ∧ p.val 0=a.val ∧
      ∀ i, HeavyShadow.heavy H B j (f i).val (p.val (Fin.last j)))
    (hlarge : cost F r*threshold B (j-1)*D^(j-1)<P.card) :
    HubPathSubdivision.graph c (r-1) ⊑ H := by
  classical
  let E := GraphSubdivision.Edge F
  let N := reserve F r
  let A := univ.image (fun i => (f i).val)
  let S₀ := insert v A
  let Z : Set V := {z | ∀ i, HeavyShadow.heavy H B j (f i).val z}
  have hfval : Function.Injective (fun i => (f i).val) := Subtype.val_injective.comp hf
  have hAcard : A.card=N := by dsimp only [A]; rw [card_image_of_injective _ hfval]; simp [N]
  have hS₀card : S₀.card≤N+1 := (card_insert_le v A).trans (by omega)
  have haS₀ : a.val∉S₀ := by
    intro ha
    rcases mem_insert.mp ha with he | he
    · exact a.property.ne he.symm
    · obtain ⟨i,_,hi⟩ := mem_image.mp he
      exact hfa i (Subtype.ext hi)
  have hadm (p : Chain H j) (hp : p∈P) : Admissible H (threshold B) j p ∧ p.val 0=a.val :=
    ⟨(hP p hp).1,(hP p hp).2.1⟩
  have hZ (p : Chain H j) (hp : p∈P) : p.val (Fin.last j)∈Z := (hP p hp).2.2
  have hzero : (S₀.card+(S₀.card+N))*threshold B (j-1)*D^(j-1)<P.card := by
    apply lt_of_le_of_lt _ hlarge
    gcongr
    dsimp only [cost,N]
    omega
  obtain ⟨T₀,hT₀a⟩ := SuffixFanData.zero H (threshold B) (threshold_mono B) j D 1 N hj hDpos
    a.val Z P hadm hZ hD S₀ haS₀ hzero (reserve_pos F r)
  let S₁ := S₀∪T₀.vertices H
  have hS₁card : S₁.card≤2+2*N := by
    have hh := T₀.vertices_card H
    simp only [mul_zero,add_zero] at hh
    have hu := card_union_le S₀ (T₀.vertices H)
    dsimp only [S₁]
    omega
  have haS₁ : a.val∉S₁ := by
    intro ha
    rcases mem_union.mp ha with ha | ha
    · exact haS₀ ha
    · exact T₀.initial_not_vertices H hT₀a ha
  have htailcost : SuffixFanData.budget j (Nat.card E+1) (Fintype.card W+1) S₁.card≤cost F r := by
    have hh := budget_mono j r (Nat.card E+1) (Fintype.card W+1) S₁.card (2+2*N) hjr hS₁card
    exact hh.trans (by dsimp only [cost,N,E]; omega)
  obtain ⟨T₁⟩ := SuffixFanData.choose H (threshold B) (threshold_mono B) j l D (Nat.card E+1)
    (Fintype.card W+1) hj hl (by omega) (by omega) hDpos a.val Z P hadm hZ hD S₁ haS₁ (by
      exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ htailcost)).trans_lt hlarge)
  obtain ⟨wn⟩ : Nonempty (W ↪ Fin N) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_fin] using reserve_vertices F r)
  let wi : W ↪ Fin (Fintype.card W+1) := (Fintype.equivFin W).toEmbedding.trans
    ⟨Fin.castSucc,Fin.castSucc_injective _⟩
  obtain ⟨ei⟩ : Nonempty (E ↪ Fin (Nat.card E+1)) := Function.Embedding.nonempty_of_card_le (by
    simp only [Fintype.card_fin,Nat.card_eq_fintype_card]; omega)
  let C := univ.image T₀.old ∪ univ.image (fun e : E => (T₁.tail (wi (ColoredEdges.right c e),ei e)).val 0)
  have hCcard : N≤C.card := by
    have hh : (univ.image T₀.old).card=N := by rw [card_image_of_injective _ T₀.old_injective]; simp
    rw [← hh]
    exact card_le_card subset_union_left
  have hCZ (z : V) (hz : z∈C) : z∈Z := by
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      exact T₀.zero_old_allowed H (by omega) i
    · obtain ⟨e,_,rfl⟩ := mem_image.mp hz
      exact T₁.tail_start _
  have hcomplete : ∀ u∈A, ∀ z∈C, (HeavyShadow.graph H B j).Adj u z := by
    intro u hu z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hu
    exact hCZ z hz i
  have hstartC (e : E) : (T₁.tail (wi (ColoredEdges.right c e),ei e)).val 0∈C :=
    mem_union_right _ (mem_image.mpr ⟨e,mem_univ _,rfl⟩)
  have hmr : m≤r := by nlinarith only [hr,hj,Nat.zero_le l]
  have hlr : l≤r := by omega
  have hneed : Fintype.card W+2+Nat.card E*(l+1)+(m-1)*Nat.card E+m+2≤N := by
    calc
      _ ≤ Fintype.card W+2+Nat.card E*(r+1)+r*Nat.card E+r+2 := by gcongr; omega
      _ ≤ N := by dsimp only [N,reserve,E]; omega
  have hneedA := hneed.trans_eq hAcard.symm
  have hneedC := hneed.trans hCcard
  have hbudget : (j-1)*(Nat.card E*m)+(Fintype.card W+2+Nat.card E*(l+1))+Nat.card E*(m+1)≤B := by
    apply le_trans _ hB
    dsimp only [liftBudget,E]
    gcongr <;> omega
  have hlen : m*j+l=(r-1)+1 := by omega
  by_cases hm0 : m%2=0
  · let u (w : W) := T₀.old (wn w)
    have hu : Function.Injective u := T₀.old_injective.comp wn.injective
    have huS (w : W) : u w∈S₁ := mem_union_right _ (T₀.old_mem H (wn w))
    have hzS : T₀.hub∈S₁ := mem_union_right _ (T₀.hub_mem H)
    have huC (w : W) : u w∈C := mem_union_left _ (mem_image.mpr ⟨wn w,mem_univ _,rfl⟩)
    apply HubFanReservoirCopy.copy c H B j m l (r-1) (Nat.card E+1) (Fintype.card W+1)
      (by omega) hm hlen S₁ a.val Z T₁ wi ei u T₀.hub hu (fun w => T₀.spoke (wn w)) huS hzS C A huC
      (fun e => by simpa [BipartiteReservoirPaths.pool,hm0] using hstartC e)
      (fun z hz u hu => (hcomplete u hu z hz).symm) hneedC hneedA hbudget
  · let u (w : W) := (f (wn w)).val
    have hu : Function.Injective u := hfval.comp wn.injective
    have huA (w : W) : u w∈A := mem_image.mpr ⟨wn w,mem_univ _,rfl⟩
    have huS (w : W) : u w∈S₁ := mem_union_left _ (mem_insert_of_mem (huA w))
    have hzS : v∈S₁ := mem_union_left _ (mem_insert_self _ _)
    apply HubFanReservoirCopy.copy c H B j m l (r-1) (Nat.card E+1) (Fintype.card W+1)
      (by omega) hm hlen S₁ a.val Z T₁ wi ei u v hu (fun w => (f (wn w)).property) huS hzS A C huA
      (fun e => by simpa only [BipartiteReservoirPaths.pool,if_neg hm0] using hstartC e)
      hcomplete hneedA hneedC hbudget

end
end HubHeavyConfiguration

end -- HubHeavyConfiguration

section -- AdmissibleFiberDegree

/- Elementary endpoint bounds and the small-degree empty-heavy case. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace AdmissibleFiberDegree
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe u
noncomputable section
variable {V : Type u} [Fintype V] (H : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableRel H.Adj := Classical.decRel _

lemma fiber_le (L : ℕ → ℕ) (j D : ℕ) (hj : 0<j) (hD : ∀ v, H.degree v≤D) (x y : V) :
    (fiber H L j x y).card≤D^(j-1) := by
  classical
  let i : Fin j := ⟨j-1,by omega⟩
  let f (p : fiber H L j x y) : {q : From H x j // q.val.val i.succ=y} := by
    have hp := (mem_fiber H L j x y p.val).mp p.property
    refine ⟨⟨p.val,hp.2.1⟩,?_⟩
    have he : i.succ=Fin.last j := by apply Fin.ext; dsimp [i]; omega
    simpa only [he] using hp.2.2
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact congrArg (fun z : {q : From H x j // q.val.val i.succ=y} => z.val.val) he
  have hh := (Fintype.card_le_of_injective f hf).trans (ChainCounting.coordinate_le H D hD j x y i)
  simpa only [Fintype.card_coe] using hh

lemma budget_le_threshold (B j : ℕ) (hj : 0<j) : B≤threshold B j := by
  have hh := threshold_large B j hj
  have hL := threshold_pos B (j-1)
  have hm : 1≤j*(threshold B (j-1))^2 := by nlinarith
  have hb := Nat.mul_le_mul_left B hm
  nlinarith only [hh,hb]

lemma bad_empty (B j D : ℕ) (hj : 0<j) (hD : ∀ v, H.degree v≤D)
    (hsmall : D^(j-1)≤threshold B j) : AdmissibleHeavyLinks.bad H B j=∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := (mem_filter.mp hp).2.2.2
  exact (Nat.not_lt_of_ge ((fiber_le H (threshold B) j D hj hD _ _).trans hsmall)) hh

end
end AdmissibleFiberDegree

end -- AdmissibleFiberDegree

section -- HubAdmissiblePruning

/- Uniform pruning of admissible heavy paths at EVERY length up to the
replacement length in a forbidden two-hub subdivision. -/
open Finset SimpleGraph ChainCounting GoodChains ThetaChains
namespace HubAdmissiblePruning
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 200000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] {F : SimpleGraph W} (c : F.Coloring (Fin 2))
variable {V : Type v} [Fintype V] (H : SimpleGraph V)
local instance : DecidableRel H.Adj := Classical.decRel _

lemma scaled (r κ B D : ℕ) (hr : 2≤r) (hκ : 0<κ)
    (hB₀ : HubHeavyConfiguration.liftBudget F r≤B)
    (hB₁ : (4*κ*(HubHeavyConfiguration.reserve F r)^2)^(r-1)≤B)
    (hB₂ : 2*HubHeavyConfiguration.cost F r*(4*κ)^(HubHeavyConfiguration.reserve F r+1)≤B)
    (hfree : (HubPathSubdivision.graph c (r-1)).Free H) (hD : ∀ v, H.degree v≤D)
    (j : ℕ) (hj : 2≤j) (hjr : j≤r) :
    κ*(AdmissibleHeavyLinks.bad H B j).card≤Fintype.card V*D^j := by
  classical
  let N := HubHeavyConfiguration.reserve F r
  have hN : 0<N := HubHeavyConfiguration.reserve_pos F r
  by_cases hsmall : D<4*κ*N^2
  · have hbase : 1≤4*κ*N^2 := by nlinarith
    have hpow : D^(j-1)≤B := by
      calc
        _ ≤ (4*κ*N^2)^(j-1) := Nat.pow_le_pow_left hsmall.le _
        _ ≤ (4*κ*N^2)^(r-1) := Nat.pow_le_pow_right hbase (by omega)
        _ ≤ B := hB₁
    have he := AdmissibleFiberDegree.bad_empty H B j D (by omega) hD
      (hpow.trans (AdmissibleFiberDegree.budget_le_threshold B j (by omega)))
    rw [he,card_empty,mul_zero]
    exact Nat.zero_le _
  · have hlarge : 4*κ*N^2≤D := by omega
    let d := D/(2*κ)
    have hκ₂ : 0<2*κ := by omega
    have hd : 2*N^2≤d := by
      apply (Nat.le_div_iff_mul_le hκ₂).mpr
      nlinarith only [hlarge]
    have hdpos : 0<d := by nlinarith
    have hDpos : 0<D := by nlinarith only [hlarge,hκ,hN]
    have hrem : D<2*κ*(d+1) := by simpa only [d] using Nat.lt_mul_div_succ D hκ₂
    have hratio : D≤(4*κ)*d := by nlinarith only [hrem,hdpos]
    have hbound : (AdmissibleHeavyLinks.bad H B j).card≤Fintype.card V*(2*d*D^(j-1)) := by
      by_contra hn
      obtain ⟨v,a,f,hf,hfa,P,hP,hPcard⟩ := AdmissibleHeavyCommon.global H B j d D (4*κ) N
        (HubHeavyConfiguration.cost F r) hj hN hDpos hd hratio hB₂ hD (Nat.lt_of_not_ge hn)
      let m := r/j
      let l := r%j
      have hm : 0 < m := Nat.div_pos hjr (by omega)
      have hl : l<j := Nat.mod_lt r (by omega)
      have he : m*j+l=r := by dsimp only [m,l]; simpa only [Nat.mul_comm] using Nat.div_add_mod r j
      exact hfree (HubHeavyConfiguration.copy c H r j m l B D hj hjr hm hl he (by omega) hD hB₀
        v a f hf hfa P hP hPcard)
    have hdiv : 2*κ*d≤D := by simpa only [d] using Nat.mul_div_le D (2*κ)
    have hmul := Nat.mul_le_mul_left κ hbound
    have hmax := Nat.mul_le_mul_left (Fintype.card V*D^(j-1)) hdiv
    have hpow : D*D^(j-1)=D^j := by rw [← pow_succ',Nat.sub_add_cancel (by omega : 0<j)]
    nlinarith only [hmul,hmax,hpow]

lemma pruning (r : ℕ) (hr : 2≤r) (ε : ℝ) (hε : 0<ε) (B₀ : ℕ) :
    ∃ B : ℕ, B₀≤B ∧ ∀ (V : Type v) [Fintype V] (H : SimpleGraph V) (D : ℕ),
      (HubPathSubdivision.graph c (r-1)).Free H → (∀ v, Nat.card (H.neighborSet v)≤D) →
      ∀ j : ℕ, 2≤j → j≤r → ((AdmissibleHeavyLinks.bad H B j).card : ℝ)≤
        ε*Fintype.card V*(D : ℝ)^j := by
  obtain ⟨κ,hκR⟩ := exists_nat_gt (1/ε)
  have hκRpos : (0 : ℝ)<κ := (by positivity : (0 : ℝ)<1/ε).trans hκR
  have hκ : 0<κ := by exact_mod_cast hκRpos
  have hεκ : 1≤ε*κ := by
    have hh := (div_lt_iff₀ hε).mp hκR
    nlinarith only [hh]
  let N := HubHeavyConfiguration.reserve F r
  let B := B₀+HubHeavyConfiguration.liftBudget F r+(4*κ*N^2)^(r-1)+
    2*HubHeavyConfiguration.cost F r*(4*κ)^(N+1)
  refine ⟨B,by dsimp only [B]; omega,?_⟩
  intro V _ H D hfree hD j hj hjr
  classical
  have hdeg : ∀ v, H.degree v≤D := by simpa only [Nat.card_eq_fintype_card,H.card_neighborSet_eq_degree] using hD
  have hh := scaled c H r κ B D hr hκ (by dsimp only [B]; omega)
    (by dsimp only [B,N]; omega) (by dsimp only [B,N]; omega) hfree hdeg j hj hjr
  have hhR : (κ : ℝ)*(AdmissibleHeavyLinks.bad H B j).card≤Fintype.card V*(D : ℝ)^j := by exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_left hhR hε.le
  have hb := mul_le_mul_of_nonneg_right hεκ (Nat.cast_nonneg (AdmissibleHeavyLinks.bad H B j).card : (0 : ℝ)≤_)
  nlinarith only [hm,hb]

end
end HubAdmissiblePruning

end -- HubAdmissiblePruning

section -- PowerErrorAbsorption

/- Absorbing a strict power-saving error in a degree moment bound. -/
namespace PowerErrorAbsorption
set_option maxHeartbeats 1000000

noncomputable def constant (C E b ε : ℝ) : ℝ := (2*E)^(1/ε)+(2*C)^(1/b)

lemma constant_nonneg (C E b ε : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    0 ≤ constant C E b ε := by unfold constant; positivity

lemma bound (x N a b ε C E : ℝ) (hx : 0 < x) (hN : 1 ≤ N)
    (ha : 0 ≤ a) (hb : 0 < b) (hε : 0 < ε) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hmain : x^b ≤ C*N^a+E*x^(b-ε)) :
    x ≤ constant C E b ε * N^(a/b) := by
  have hNr : 1 ≤ N^(a/b) := Real.one_le_rpow hN (by positivity)
  have hconst := constant_nonneg C E b ε hC hE
  by_cases hsmall : x^ε ≤ 2*E
  · have hr := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hsmall (by positivity : 0 ≤ 1/ε)
    rw [← Real.rpow_mul hx.le,show ε*(1/ε) = 1 by field_simp,Real.rpow_one] at hr
    have hc : (2*E)^(1/ε) ≤ constant C E b ε :=
      le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    exact hr.trans (hc.trans (le_mul_of_one_le_right hconst hNr))
  · have hp := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hsmall))
      (Real.rpow_nonneg hx.le (b-ε))
    rw [← Real.rpow_add hx,show ε+(b-ε) = b by ring] at hp
    have hc : x^b ≤ 2*C*N^a := by nlinarith only [hmain,hp]
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hc (by positivity : 0 ≤ 1/b)
    rw [← Real.rpow_mul hx.le,show b*(1/b) = 1 by field_simp,Real.rpow_one,
      Real.mul_rpow (show 0 ≤ 2*C by positivity) (Real.rpow_nonneg (by linarith) a),
      ← Real.rpow_mul (show 0 ≤ N by linarith),show a*(1/b) = a/b by ring] at hr
    apply hr.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)

end PowerErrorAbsorption

end -- PowerErrorAbsorption

section -- HubPathDegree

/- General almost-regular degree bound for arbitrary-length two-hub replacements. -/
open Finset SimpleGraph
namespace HubPathDegree
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 200000
universe u v

lemma absorb (p : ℕ) (n d δ U α : ℝ) (hn : 0<n) (hd : 0<d) (hhalf : d≤2*δ)
    (hcount : n*δ^p≤n^2*U*d^α+(1/(2 : ℝ)^(p+1))*n*d^p) :
    d^((p : ℝ)-α)≤(2 : ℝ)^(p+1)*U*n := by
  have hp := pow_le_pow_left₀ hd.le hhalf p
  rw [mul_pow] at hp
  have hp' := mul_le_mul_of_nonneg_left hp (show 0≤2*n by positivity)
  have hh := mul_le_mul_of_nonneg_left hcount (show 0≤(2 : ℝ)^(p+1) by positivity)
  rw [mul_add] at hh
  have he : (2 : ℝ)^(p+1)*((1/(2 : ℝ)^(p+1))*n*d^p)=n*d^p := by
    field_simp
  rw [he] at hh
  have ht : (2 : ℝ)^(p+1)=2*(2 : ℝ)^p := by rw [pow_succ]; ring
  have hmain : n*d^p≤n*((2 : ℝ)^(p+1)*U*n*d^α) := by rw [ht] at hh ⊢; nlinarith only [hp',hh]
  have hpower : d^p≤(2 : ℝ)^(p+1)*U*n*d^α := (mul_le_mul_iff_right₀ hn).mp hmain
  have hid : d^((p : ℝ)-α)*d^α=d^p := by rw [← Real.rpow_add hd,sub_add_cancel,Real.rpow_natCast]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hd α)).mp
  simpa only [hid] using hpower

noncomputable section
variable {W : Type u} [Fintype W] (F : SimpleGraph W) (c : F.Coloring (Fin 2))

lemma almost_regular (hF : F.Connected) (k : ℕ) (hk : 1≤k) (α C : ℝ)
    (hα : 0≤α) (hα₂ : α<2) (hC : 0≤C)
    (hbound : ∀ n : ℕ, (extremalNumber n F : ℝ)≤C*(n : ℝ)^α) (R : ℕ) (hR : 0<R) :
    ∃ A : ℝ, 0≤A ∧ ∀ (V : Type v) [Fintype V] [Nonempty V] (H : SimpleGraph V) (δ : ℕ),
      0<δ → (HubPathSubdivision.graph c k).Free H →
      (∀ w, δ≤Nat.card (H.neighborSet w)) → (∀ w, Nat.card (H.neighborSet w)≤R*δ) →
      (δ : ℝ)≤A*(Nat.card V : ℝ)^(1/(((k+3 : ℕ) : ℝ)-α)) := by
  let ε : ℝ := 1/((2 : ℝ)^(k+4)*(k+4 : ℕ)*(k+2 : ℕ)*(R : ℝ)^(k+3))
  have hRR : (0 : ℝ)<R := by exact_mod_cast hR
  have hε : 0<ε := by dsimp [ε]; positivity
  have hcoef : (k+4 : ℕ)*(k+2 : ℕ)*ε*(R : ℝ)^(k+3)=1/(2 : ℝ)^(k+4) := by
    dsimp only [ε]
    have hR0 : (R : ℝ)≠0 := hRR.ne'
    have hk4 : ((k+4 : ℕ) : ℝ)≠0 := by positivity
    have hk2 : ((k+2 : ℕ) : ℝ)≠0 := by positivity
    field_simp
  obtain ⟨B,hB,hprune⟩ := HubAdmissiblePruning.pruning.{u,v} c (k+1) (by omega) ε hε 0
  let U : ℝ := (HubLightBounds.loss k (ThetaChains.threshold B) : ℝ)*C*2^α*(R : ℝ)^α
  let A : ℝ := 2*(k+3 : ℕ)+PowerErrorAbsorption.constant ((2 : ℝ)^(k+4)*U) 0 (((k+3 : ℕ) : ℝ)-α) 1
  have hU : 0≤U := by dsimp [U]; positivity
  have hA : 0≤A := by
    exact add_nonneg (by positivity) (PowerErrorAbsorption.constant_nonneg _ _ _ _ (by positivity) le_rfl)
  refine ⟨A,hA,?_⟩
  intro V _ _ H δ hδ hfree hmin hmax
  classical
  have hn : (0 : ℝ)<Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ)≤Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdR : (0 : ℝ)<δ := by exact_mod_cast hδ
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hden : 0<((k+3 : ℕ) : ℝ)-α := by push_cast; linarith
  have hnr : 1≤(Fintype.card V : ℝ)^(1/(((k+3 : ℕ) : ℝ)-α)) := Real.one_le_rpow hn1 (by positivity)
  rw [Nat.card_eq_fintype_card]
  by_cases hsmall : δ<2*(k+3)
  · have hdsmall : (δ : ℝ)≤2*(k+3 : ℕ) := by exact_mod_cast hsmall.le
    have hbase : (2*(k+3 : ℕ) : ℝ)≤A := le_add_of_nonneg_right
      (PowerErrorAbsorption.constant_nonneg _ _ _ _ (by positivity) le_rfl)
    exact hdsmall.trans (hbase.trans (le_mul_of_one_le_right hA hnr))
  have hlarge : 2*(k+3)≤δ := by omega
  have hD : ∀ w, H.degree w≤R*δ := by simpa only [Nat.card_eq_fintype_card,H.card_neighborSet_eq_degree] using hmax
  have hm : ∀ w, δ-(k+3)+(k+3)≤H.degree w := by
    simpa only [Nat.sub_add_cancel (by omega : k+3≤δ),Nat.card_eq_fintype_card,H.card_neighborSet_eq_degree] using hmin
  have hpr := hprune V H (R*δ) (by simpa using hfree) hmax
  have hc := HubAdmissibleCount.count F c H hF k B (δ-(k+3)) (R*δ) hm hD hfree C α ε hC hα hε.le hbound hpr
  have he : (((R*δ : ℕ) : ℝ)^α)=(R : ℝ)^α*(δ : ℝ)^α := by
    rw [Nat.cast_mul,Real.mul_rpow hRR.le hdR.le]
  have herr : (k+4 : ℕ)*(k+2 : ℕ)*ε*Fintype.card V*(((R*δ : ℕ) : ℝ)^(k+3))=
      (1/(2 : ℝ)^(k+4))*Fintype.card V*(δ : ℝ)^(k+3) := by
    rw [Nat.cast_mul,mul_pow]
    calc
      _ = ((k+4 : ℕ)*(k+2 : ℕ)*ε*(R : ℝ)^(k+3))*Fintype.card V*(δ : ℝ)^(k+3) := by ring
      _ = _ := by rw [hcoef]
  rw [he,herr] at hc
  have hcount : (Fintype.card V : ℝ)*((δ-(k+3) : ℕ) : ℝ)^(k+3)≤
      (Fintype.card V : ℝ)^2*U*(δ : ℝ)^α+(1/(2 : ℝ)^(k+4))*Fintype.card V*(δ : ℝ)^(k+3) := by
    dsimp only [U]
    nlinarith only [hc]
  have hhalf : (δ : ℝ)≤2*((δ-(k+3) : ℕ) : ℝ) := by exact_mod_cast (by omega : δ≤2*(δ-(k+3)))
  have hp := absorb (k+3) (Fintype.card V) δ (δ-(k+3) : ℕ) U α hn hdR hhalf hcount
  have hp' : (δ : ℝ)^(((k+3 : ℕ) : ℝ)-α)≤((2 : ℝ)^(k+4)*U)*(Fintype.card V : ℝ)^(1 : ℝ)+
      0*(δ : ℝ)^((((k+3 : ℕ) : ℝ)-α)-1) := by simpa only [Real.rpow_one,zero_mul,add_zero] using hp
  have hh := PowerErrorAbsorption.bound δ (Fintype.card V) 1 (((k+3 : ℕ) : ℝ)-α) 1 ((2 : ℝ)^(k+4)*U) 0
    hdR hn1 (by norm_num) hden (by norm_num) (by positivity) le_rfl hp'
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity : (0 : ℝ)≤2*(k+3 : ℕ))) (by positivity)

end
end HubPathDegree

end -- HubPathDegree

section -- BipartiteRegularization

/- Bipartite almost-regular tests suffice for a general edge bound. -/
open Finset SimpleGraph
namespace BipartiteRegularization
set_option maxHeartbeats 1500000
universe u


lemma bound (γ A : ℝ) (L : ℕ) (hγ : 1 < γ) (hA : 0 ≤ A)
    (hL : 4*(2 : ℝ)^γ ≤ (L : ℝ)^(γ-1))
    (P : ∀ (V : Type u) [Fintype V], SimpleGraph V → Prop)
    (hered : ∀ (V W : Type u) [Fintype V] [Fintype W] (H : SimpleGraph V) (G : SimpleGraph W),
      Copy G H → P V H → P W G)
    (hbound : ∀ (W : Type u) [Fintype W] [Nonempty W] (G : SimpleGraph W),
      G.Coloring (Fin 2) → P W G → ∀ d : ℕ,
      0 < d → (∀ v, d ≤ Nat.card (G.neighborSet v)) →
      (∀ v, Nat.card (G.neighborSet v) ≤ 8*L*d) →
      (d : ℝ) ≤ A*(Nat.card W : ℝ)^(γ-1)) :
    ∀ (V : Type u) [Fintype V] (H : SimpleGraph V), P V H →
      (Nat.card H.edgeSet : ℝ) ≤ 8*A*(Nat.card V : ℝ)^γ := by
  intro V _ H hP
  classical
  have he : Nat.card H.edgeSet = H.edgeFinset.card := by rw [Nat.card_eq_fintype_card]; exact H.card_edgeSet
  rw [he,Nat.card_eq_fintype_card]
  cases isEmpty_or_nonempty V with
  | inl h =>
    have hzero : H.edgeFinset.card = 0 := by
      have hh := H.card_edgeFinset_le_card_choose_two
      simpa using hh
    rw [hzero,Nat.cast_zero]
    positivity
  | inr h =>
    obtain ⟨J,hJ,hJH,hJB,heJ⟩ := MaxCut.exists_bipartite_subgraph H
    letI := hJ
    let cJ : J.Coloring (Fin 2) := Classical.choice hJB
    have hPJ := hered V V H J (Copy.ofLE J H hJH) hP
    have hreg : (J.edgeFinset.card : ℝ) ≤ 4*A*(Fintype.card V : ℝ)^γ := by
      apply Regularization.edge_bound_of_almost_regular J γ A L hγ hA hL
      intro W _ _ G _ f d hdpos hd hD
      let cG : G.Coloring (Fin 2) := Coloring.mk (fun v => cJ (f v))
        (fun h => cJ.valid (f.toHom.map_rel' h))
      have hh := hbound W G cG (hered V W J G f hPJ) d hdpos
        (fun v => by simpa only [Nat.card_eq_fintype_card,G.card_neighborSet_eq_degree] using hd v)
        (fun v => by simpa only [Nat.card_eq_fintype_card,G.card_neighborSet_eq_degree] using hD v)
      simpa only [Nat.card_eq_fintype_card] using hh
    have heJ' : (H.edgeFinset.card : ℝ) ≤ 2*J.edgeFinset.card := by exact_mod_cast heJ
    nlinarith only [hreg,heJ']

end BipartiteRegularization

end -- BipartiteRegularization

section -- HubPathBounds

/- The general upper transformation alpha -> 1+1/(k+3-alpha) for the two-hub
(k+1)-edge subdivision of a connected bipartite graph. -/
open Finset SimpleGraph Filter
namespace HubPathBounds
set_option maxHeartbeats 2500000
universe u v
noncomputable section
variable {W : Type u} [Fintype W] (F : SimpleGraph W) (c : F.Coloring (Fin 2))

lemma edge_bound (hF : F.Connected) (k : ℕ) (hk : 1≤k) (α C : ℝ) (hα : 0≤α) (hα₂ : α<2) (hC : 0≤C)
    (hbound : ∀ n : ℕ, (extremalNumber n F : ℝ)≤C*(n : ℝ)^α) :
    ∃ B : ℝ, 0≤B ∧ ∀ (V : Type v) [Fintype V] (H : SimpleGraph V),
      (HubPathSubdivision.graph c k).Free H →
      (Nat.card H.edgeSet : ℝ)≤B*(Nat.card V : ℝ)^(1+1/(((k+3 : ℕ) : ℝ)-α)) := by
  let γ : ℝ := 1+1/(((k+3 : ℕ) : ℝ)-α)
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hden : 0<((k+3 : ℕ) : ℝ)-α := by push_cast; linarith
  have hγ : 1<γ := by dsimp only [γ]; have := one_div_pos.mpr hden; linarith
  have hγ' : 0≤γ-1 := by linarith
  obtain ⟨M,hM⟩ := Regularization.exists_regularization_constant γ hγ
  have hM' : 4*(2 : ℝ)^γ≤((M+1 : ℕ) : ℝ)^(γ-1) := by
    exact hM.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ M) hγ')
  obtain ⟨A,hA,hdegree⟩ := HubPathDegree.almost_regular.{u,v} F c hF k hk α C hα hα₂ hC hbound (8*(M+1)) (by omega)
  refine ⟨8*A,mul_nonneg (by norm_num) hA,?_⟩
  apply BipartiteRegularization.bound γ A (M+1) hγ hA hM'
    (fun V _ H => (HubPathSubdivision.graph c k).Free H)
  · intro V V' _ _ H G f hfree h
    exact hfree (h.trans ⟨f⟩)
  · intro V _ _ H d hfree δ hδ hmin hmax
    have hh := hdegree V H δ hδ hfree hmin hmax
    simpa only [γ,add_sub_cancel_left] using hh

lemma upper_isBigO (hF : F.Connected) (k : ℕ) (hk : 1≤k) (α : ℝ) (hα : 0≤α) (hα₂ : α<2)
    (hupper : Asymptotics.IsBigO atTop (fun n : ℕ => (extremalNumber n F : ℝ))
      (fun n : ℕ => (n : ℝ)^α)) :
    Asymptotics.IsBigO atTop (fun n : ℕ => (extremalNumber n (HubPathSubdivision.graph c k) : ℝ))
      (fun n : ℕ => (n : ℝ)^(1+1/(((k+3 : ℕ) : ℝ)-α))) := by
  obtain ⟨C,hC,hbound⟩ := SuspensionBounds.uniform_bound_of_isBigO F α hα hupper
  obtain ⟨B,hB,hgraph⟩ := edge_bound.{u,0} F c hF k hk α C hα hα₂ hC hbound
  have hpoint (n : ℕ) : (extremalNumber n (HubPathSubdivision.graph c k) : ℝ)≤B*(n : ℝ)^(1+1/(((k+3 : ℕ) : ℝ)-α)) := by
    classical
    rw [← Fintype.card_fin n,extremalNumber_le_iff_of_nonneg _ (by positivity)]
    intro H _ hfree
    have hh := hgraph (Fin n) H hfree
    simpa only [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card] using hh
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨B,Eventually.of_forall ?_⟩
  intro n
  simpa only [Real.norm_eq_abs,Nat.abs_cast,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hpoint n

end
end HubPathBounds

end -- HubPathBounds

section -- RootedModelFacts

/- The verified rooted-model transformation (a,b) -> (a+b,a+2*b). -/
open Finset SimpleGraph
namespace RootedModelFacts
open RootedUpperModels
set_option maxHeartbeats 2000000

lemma model_has_edge {a b : ℕ} (M : Model a b) (hb : 0<b) : ∃ x y, M.G.Adj x y := by
  classical
  letI := M.fintypeA
  letI := M.fintypeR
  letI := M.nonemptyA
  let x := Classical.choice M.nonemptyA
  have hh := M.balance {x}
  rw [card_singleton,mul_one] at hh
  have hc : 0<(RootedUnionDensity.incident M.G {x}).card := by
    by_contra hn
    have hz : (RootedUnionDensity.incident M.G {x}).card=0 := by omega
    rw [hz,mul_zero] at hh
    omega
  obtain ⟨e,he⟩ := card_pos.mp hc
  have hadj := (mem_filter.mp he).1
  induction e using Sym2.inductionOn with
  | _ u v => exact ⟨u,v,mem_edgeFinset.mp hadj⟩

lemma color_surjective {W : Type*} (F : SimpleGraph W) (c : F.Coloring (Fin 2))
    (hedge : ∃ x y, F.Adj x y) : Function.Surjective c := by
  obtain ⟨x,y,hxy⟩ := hedge
  have hc := c.valid hxy
  intro i
  by_cases hx : c x=i
  · exact ⟨x,hx⟩
  · exact ⟨y,by change c x≠c y at hc; omega⟩

end RootedModelFacts

end -- RootedModelFacts

section -- RootedHubPathModels

/- The arbitrary rooted-model closure (a,b) -> (a+k*b,a+(k+1)*b). -/
open Finset SimpleGraph
namespace RootedHubPathModels
open RootedUpperModels
set_option maxHeartbeats 2500000

noncomputable def model {a b : ℕ} (M : Model a b) (ha : 0<a) (hab : a≤b) (k : ℕ) (hk : 1≤k) :
    Model (a+k*b) (a+(k+1)*b) := by
  classical
  letI := M.fintypeA
  letI := M.fintypeR
  letI := M.nonemptyA
  letI : Fintype (RootedSubdivision.E M.G) := Fintype.ofFinite _
  letI : Fintype (RootedHubPath.I M.G) := Fintype.ofFinite _
  letI : Fintype (RootedHubPath.J M.G) := Fintype.ofFinite _
  have hb : 0<b := ha.trans_le hab
  have hedge := RootedModelFacts.model_has_edge M hb
  refine {
    A := RootedHubPath.Internal M.G k
    R := RootedHubPath.Roots M.G k
    G := RootedHubPath.graph M.G k M.color
    color := RootedHubPath.color M.G k M.color
    balance := RootedHubPath.balanced M.G k M.color a b M.balance
    connected := ?_
    upper := ?_ }
  · intro t ht
    have he : ∃ x y, (RootedPowers.graph M.G t).Adj x y := by
      obtain ⟨x,y,hxy⟩ := hedge
      exact ⟨RootedPowers.layer M.G t ⟨0,ht⟩ x,RootedPowers.layer M.G t ⟨0,ht⟩ y,
        (RootedPowers.layer M.G t ⟨0,ht⟩).toHom.map_rel' hxy⟩
    exact (RootedHubPath.powerIso M.G k M.color t ⟨0,ht⟩).connected_iff.mpr
      (HubPathSubdivision.connected _ k (M.connected t ht) (RootedModelFacts.color_surjective _ _ he))
  · intro t ht
    have haR : (0 : ℝ)<a := by exact_mod_cast ha
    have hbR : (0 : ℝ)<b := by exact_mod_cast hb
    have habR : (a : ℝ)≤b := by exact_mod_cast hab
    have hα : 0≤2-(a : ℝ)/b := by have := (div_le_one hbR).mpr habR; linarith
    have hα₂ : 2-(a : ℝ)/b<2 := by have := div_pos haR hbR; linarith
    have hu := HubPathBounds.upper_isBigO (RootedPowers.graph M.G t) (RootedSuspension.powerColor M.color t)
      (M.connected t ht) k hk (2-(a : ℝ)/b) hα hα₂ (M.upper t ht)
    have he : 1+1/(((k+3 : ℕ) : ℝ)-(2-(a : ℝ)/b))=2-((a+k*b : ℕ) : ℝ)/(a+(k+1)*b : ℕ) := by
      have hd : (a : ℝ)+((k : ℝ)+1)*b≠0 := by positivity
      have hden : ((k+3 : ℕ) : ℝ)-(2-(a : ℝ)/b)=((a : ℝ)+((k : ℝ)+1)*b)/b := by
        push_cast
        field_simp
        ring
      rw [hden,one_div_div]
      push_cast
      field_simp
      ring
    simpa only [extremalNumber_congr_right (RootedHubPath.powerIso M.G k M.color t ⟨0,ht⟩),he] using hu

end RootedHubPathModels

end -- RootedHubPathModels

section -- UniversalHubModels

/- The arbitrary two-hub closure and suspension generate all rational
extremal exponents between one and two. -/
open Finset SimpleGraph
namespace UniversalHubModels
open RootedUpperModels
set_option maxHeartbeats 2500000

noncomputable def initial_scaled (a : ℕ) (ha : 0<a) : Model a a := by
  let M := RootedUpperModels.initial
  letI := M.fintypeA
  letI := M.fintypeR
  letI := M.nonemptyA
  exact {
    A := M.A
    R := M.R
    G := M.G
    color := M.color
    balance := fun S => by
      have hh := Nat.mul_le_mul_left a (M.balance S)
      simpa only [mul_one,one_mul] using hh
    connected := M.connected
    upper := fun t ht => by
      have haR : (a : ℝ)≠0 := by exact_mod_cast ha.ne'
      simpa only [Nat.cast_one,div_self haR,div_one,sub_self] using M.upper t ht }

noncomputable def transform {a b : ℕ} (M : Model a b) (ha : 0<a) (hab : a≤b) (k : ℕ) :
    Model (a+k*b) (a+(k+1)*b) := by
  by_cases hk : k=0
  · subst k
    simpa only [zero_mul,add_zero,zero_add,one_mul,Nat.add_comm] using RootedUpperModels.suspension M ha hab
  · exact RootedHubPathModels.model M ha hab k (by omega)

/-- The inverse negative-continued-fraction step, written without rational division. -/
lemma negative_step (a b : ℕ) (ha : 0<a) (hab : a<b) :
    ∃ k r : ℕ, r<a ∧ b+r=(k+2)*a := by
  let q := b/a
  have hdiv := Nat.mod_add_div b a
  have hrem : b%a<a := Nat.mod_lt b ha
  by_cases hz : b%a=0
  · have hmul : q*a=b := by dsimp only [q]; nlinarith only [hdiv,hz]
    have hq : 2≤q := by nlinarith only [hmul,hab,ha]
    refine ⟨q-2,0,ha,?_⟩
    rw [Nat.sub_add_cancel hq,Nat.add_zero]
    exact hmul.symm
  · have hq : 0<q := Nat.div_pos hab.le ha
    have hsub := Nat.sub_add_cancel hrem.le
    refine ⟨q-1,a-b%a,by omega,?_⟩
    have he : q-1+2=q+1 := by omega
    rw [he]
    dsimp only [q] at *
    nlinarith only [hdiv,hsub]

lemma all_models : ∀ b a : ℕ, 0<a → a≤b → Nonempty (Model a b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a ha hab
    by_cases he : a=b
    · subst a
      exact ⟨initial_scaled b ha⟩
    have hab' : a<b := by omega
    let p := b-a
    have hp : 0<p := by dsimp only [p]; omega
    have hpb : p<b := by dsimp only [p]; omega
    have hpa : p+a=b := by dsimp only [p]; omega
    obtain ⟨k,r,hr,hkr⟩ := negative_step p b hp hpb
    have hprev : p-r+r=p := Nat.sub_add_cancel hr.le
    obtain ⟨M⟩ := ih p hpb (p-r) (by omega) (Nat.sub_le p r)
    have M' := transform M (by omega) (Nat.sub_le p r) k
    have hnewA : p-r+k*p=a := by nlinarith only [hkr,hpa,hprev]
    have hnewB : p-r+(k+1)*p=b := by nlinarith only [hkr,hprev]
    rw [hnewA,hnewB] at M'
    exact ⟨M'⟩

lemma result (α : ℚ) (hα : 1≤α) (hα₂ : α<2) :
    ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
      Asymptotics.IsTheta Filter.atTop
        (fun n : ℕ => (extremalNumber n G : ℝ))
        (fun n : ℕ => (n : ℝ)^(α : ℝ)) := by
  let x : ℚ := 2-α
  have hx : 0<x := by dsimp only [x]; linarith
  have hx1 : x≤1 := by dsimp only [x]; linarith
  have hnum : 0<x.num := Rat.num_pos.mpr hx
  have hxcast : (x.num.natAbs : ℚ)/x.den=x := by
    have hn : (x.num.natAbs : ℚ)=x.num := by rw [← Int.cast_natCast,Int.natAbs_of_nonneg hnum.le]
    rw [hn,Rat.num_div_den]
  have ha : 0<x.num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  have hab : x.num.natAbs≤x.den := by
    have hd : (0 : ℚ)<x.den := by exact_mod_cast x.den_pos
    have hh : (x.num.natAbs : ℚ)≤x.den := (div_le_one hd).mp (by rwa [hxcast])
    exact_mod_cast hh
  obtain ⟨M⟩ := all_models x.den x.num.natAbs ha hab
  have he : α=2-(x.num.natAbs : ℚ)/x.den := by rw [hxcast]; dsimp only [x]; ring
  rw [he]
  exact RootedUpperModels.realization M ha hab

end UniversalHubModels

end -- UniversalHubModels

open Filter SimpleGraph

namespace Erdos571

/--
Show that for any rational $\alpha \in [1,2)$ there exists a bipartite graph $G$ such that\[\mathrm{ex}(n;G)\asymp n^{\alpha}.\]
-/
theorem erdos_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
      ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
        Asymptotics.IsTheta atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (α : ℝ)) := by
  exact UniversalHubModels.result

end Erdos571


/- Canonical Jig330 formulation and an independently checked equivalence bridge. -/

namespace Jig330Canonical
open SimpleGraph Filter

def HasTuranExponent (α : ℝ) : Prop :=
  ∃ v : ℕ, ∃ G : SimpleGraph (Fin v),
    G.IsBipartite ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∀ H : SimpleGraph (Fin n), ¬G ⊑ H →
          (H.edgeSet.ncard : ℝ) ≤ C * (n : ℝ) ^ α) ∧
        ∃ H : SimpleGraph (Fin n), ¬G ⊑ H ∧
          c * (n : ℝ) ^ α ≤ (H.edgeSet.ncard : ℝ)

abbrev statement : Prop :=
  ∀ α : ℚ, 1 ≤ α → α < 2 → HasTuranExponent (α : ℝ)

lemma hasTuranExponent_of_theta {α : ℝ} {v : ℕ} (G : SimpleGraph (Fin v))
    (hG : G.IsBipartite)
    (hΘ : Asymptotics.IsTheta atTop
      (fun n : ℕ => (extremalNumber n G : ℝ)) (fun n : ℕ => (n : ℝ) ^ α)) :
    HasTuranExponent α := by
  classical
  obtain ⟨C, hC, hu⟩ := hΘ.1.exists_pos
  obtain ⟨D, hD, hl⟩ := hΘ.2.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.bound.and hl.bound)
  refine ⟨v, G, hG, (2 * D)⁻¹, C, by positivity, hC, max N 1, ?_⟩
  intro n hn
  obtain ⟨hu, hl⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnpos _
  simp only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_pos hpow] at hu hl
  constructor
  · intro H hH
    have he : H.edgeFinset.card ≤ extremalNumber n G := by
      simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hH
    have hncard : H.edgeSet.ncard = H.edgeFinset.card := by
      rw [← coe_edgeFinset, Set.ncard_coe_finset]
    rw [hncard]
    exact le_trans (by exact_mod_cast he) hu
  · have hlt : (2 * D)⁻¹ * (n : ℝ) ^ α < (extremalNumber n G : ℝ) := by
      have hhalf : (2 * D)⁻¹ * (n : ℝ) ^ α < D⁻¹ * (n : ℝ) ^ α := by
        apply mul_lt_mul_of_pos_right _ hpow
        exact (inv_lt_inv₀ (by positivity) hD).mpr (by nlinarith)
      exact lt_of_lt_of_le hhalf ((inv_mul_le_iff₀ hD).mpr hl)
    obtain ⟨H, inst, hfree, hedge⟩ :=
      (lt_extremalNumber_iff_of_nonneg (V := Fin n) G
        (show (0 : ℝ) ≤ (2 * D)⁻¹ * (n : ℝ) ^ α by positivity)).mp
          (by simpa only [Fintype.card_fin] using hlt)
    refine ⟨H, hfree, ?_⟩
    rw [← coe_edgeFinset, Set.ncard_coe_finset]
    exact hedge.le

end Jig330Canonical


namespace Jig330Canonical

theorem target : statement := by
  intro α hα hα₂
  obtain ⟨v, G, hG, hTheta⟩ := Erdos571.erdos_571 α hα hα₂
  exact hasTuranExponent_of_theta G hG hTheta

end Jig330Canonical



/-
UPSTREAM NOTICE (retained verbatim)

Erdős problem #571 (rational exponents for Turán numbers of bipartite graphs): proof
Copyright 2026 Tom Adamczewski / Epoch AI

The formal statement was given to the AI system by the FrontierMath Erdős benchmark of Tom Adamczewski and
Thomas F. Bloom (LeanOpenProblems,
https://github.com/epoch-research/LeanOpenProblems, commit 77882c437ca1dfefab3b27fa00f1d29788100311), Epoch AI, MIT License.
The Lean proofs were produced by a pre-release version of GPT-6 Astra (OpenAI) running in that benchmark.

UPSTREAM APACHE-2.0 LICENSE (retained verbatim)

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

namespace Submissions.Erdos571TuranExponents.EpochPort
theorem proof : Jig330Canonical.statement := Jig330Canonical.target
end Submissions.Erdos571TuranExponents.EpochPort
