import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic
/-!
Attribution: inherited minimal-counterexample structure and cycle contraction
follow Carr, Bisch, jul059's strict-bound argument, and Jig statement10 (Cole).
The C4-free two-degenerate extremal idea also underlies Jig statement11
(davidtsong), which was independently filed and proved first.
References: https://arxiv.org/abs/2605.22844
https://ajbisch.github.io/papers/erdos-gyarfas.html
https://www.erdosproblems.com/forum/thread/64#post-8130
https://jig.so/p/399?s=10 and https://jig.so/p/399?s=11
The +5 variant additionally formalizes finite cases covered by prior searches;
it is not a claim of discovery of those finite exclusions.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/- BEGIN BoundaryFiveScratch -/
section

open Finset SimpleGraph

def pair5 : Fin 10 → Fin 5 × Fin 5
  | 0 => (0,1) | 1 => (0,2) | 2 => (0,3) | 3 => (0,4) | 4 => (1,2)
  | 5 => (1,3) | 6 => (1,4) | 7 => (2,3) | 8 => (2,4) | 9 => (3,4)

def badj (f : Fin 1024) (a b : Fin 5) : Bool :=
  decide (∃ i, (pair5 i = (a,b) ∨ pair5 i = (b,a)) ∧ f.val.testBit i)

def bdeg (f : Fin 1024) (a : Fin 5) : Nat :=
  (Finset.univ.filter fun b => badj f a b).card

def bs (n : Nat) : List (Fin n) := List.ofFn id

def bC4 (f : Fin 1024) : Bool :=
  (bs 5).any fun a => (bs 5).any fun b => (bs 5).any fun c => (bs 5).any fun d =>
    decide (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) &&
      badj f a b && badj f b c && badj f c d && badj f d a

def bRigid (f : Fin 1024) : Bool :=
  (bs 5).all fun a => (bs 5).all fun b =>
    decide (a = b) || (bs 5).any fun c =>
      decide (c ≠ a ∧ c ≠ b) && badj f a c && badj f c b

def bDegreeSum (f : Fin 1024) : Nat := (bs 5).map (bdeg f) |>.sum

def bGood (f : Fin 1024) : Bool :=
  bC4 f || (decide (bDegreeSum f ≤ 12) &&
    (!decide (bDegreeSum f = 12) || bRigid f))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem boolean_five_rigid_all : ((bs 1024).all bGood) = true := by
  decide

def rawCode (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : Nat :=
  Nat.bit (decide (G.Adj 0 1)) <| Nat.bit (decide (G.Adj 0 2)) <|
  Nat.bit (decide (G.Adj 0 3)) <| Nat.bit (decide (G.Adj 0 4)) <|
  Nat.bit (decide (G.Adj 1 2)) <| Nat.bit (decide (G.Adj 1 3)) <|
  Nat.bit (decide (G.Adj 1 4)) <| Nat.bit (decide (G.Adj 2 3)) <|
  Nat.bit (decide (G.Adj 2 4)) <| Nat.bit (decide (G.Adj 3 4)) 0

theorem bit_lt_two_pow (b : Bool) {n k : Nat} (h : n < 2 ^ k) :
    Nat.bit b n < 2 ^ (k + 1) := by
  cases b <;> simp [Nat.bit] <;> omega

theorem rawCode_lt (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : rawCode G < 1024 := by
  change rawCode G < 2 ^ 10
  simp only [rawCode]
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  apply bit_lt_two_pow
  norm_num

def graphCode (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : Fin 1024 :=
  ⟨rawCode G, rawCode_lt G⟩

theorem graphCode_testBit (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] (i : Fin 10) :
    (graphCode G).val.testBit i = G.Adj (pair5 i).1 (pair5 i).2 := by
  fin_cases i <;> simp [graphCode, rawCode, pair5, Nat.testBit_bit_zero,
    Nat.testBit_bit_succ]

theorem pair5_complete (a b : Fin 5) (h : a ≠ b) :
    ∃ i, pair5 i = (a,b) ∨ pair5 i = (b,a) := by
  fin_cases a <;> fin_cases b <;> simp_all <;> decide

theorem badj_graphCode (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] (a b : Fin 5) :
    badj (graphCode G) a b = true ↔ G.Adj a b := by
  simp only [badj, graphCode_testBit]
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, ha⟩
    rcases hi with hi | hi
    · simpa [hi] using ha
    · simpa [hi, G.adj_comm] using ha
  · intro ha
    obtain ⟨i, hi⟩ := pair5_complete a b ha.ne
    refine ⟨i, hi, ?_⟩
    rcases hi with hi | hi
    · simpa [hi] using ha
    · simpa [hi, G.adj_comm] using ha

def HasC4Fin {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

theorem five_degree_sum_le (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (hn : ¬ HasC4Fin G) : ∑ v, G.degree v ≤ 12 := by
  have hall := List.all_eq_true.mp boolean_five_rigid_all
  have hgood : bGood (graphCode G) = true :=
    hall (graphCode G) (List.mem_ofFn.mpr ⟨graphCode G, rfl⟩)
  have hbdeg : ∀ a, bdeg (graphCode G) a = G.degree a := by
    intro a
    unfold bdeg
    rw [← card_neighborFinset_eq_degree]
    apply congrArg Finset.card
    ext b
    simp [badj_graphCode, mem_neighborFinset]
  have hc4 : bC4 (graphCode G) = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    apply hn
    simp only [bC4, List.any_eq_true] at hc
    rcases hc with ⟨a, _, b, _, c, _, d, _, hc⟩
    simp only [Bool.and_eq_true, badj_graphCode] at hc
    rcases hc with ⟨⟨⟨hneq, hab⟩, hbc⟩, hcd⟩
    rcases hneq with ⟨hneq, hab'⟩
    rcases of_decide_eq_true hneq with ⟨hnab, hnac, hnad, hnbc, hnbd, hncd⟩
    exact ⟨a, b, c, d, hnab, hnac, hnad, hnbc, hnbd, hncd, hab', hab, hbc, hcd⟩
  simp only [bGood, hc4, Bool.false_or, Bool.and_eq_true] at hgood
  have hup : bDegreeSum (graphCode G) ≤ 12 := of_decide_eq_true hgood.1
  simp only [bDegreeSum, bs, List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq] at hup
  rw [Finset.sum_congr rfl (fun i _ => hbdeg i)] at hup
  exact hup

theorem five_rigid (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (hsum : 12 ≤ ∑ v, G.degree v) (hn : ¬ HasC4Fin G) :
    ∀ a b, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b ∧ G.Adj a c ∧ G.Adj c b := by
  have hall := List.all_eq_true.mp boolean_five_rigid_all
  have hgood : bGood (graphCode G) = true :=
    hall (graphCode G) (List.mem_ofFn.mpr ⟨graphCode G, rfl⟩)
  have hbdeg : ∀ a, bdeg (graphCode G) a = G.degree a := by
    intro a
    unfold bdeg
    rw [← card_neighborFinset_eq_degree]
    apply congrArg Finset.card
    ext b
    simp [bdeg, badj_graphCode, mem_neighborFinset]
  have hds : 12 ≤ bDegreeSum (graphCode G) := by
    simp only [bDegreeSum, bs, List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]
    rw [Finset.sum_congr rfl (fun i _ => hbdeg i)]
    exact hsum
  have hc4 : bC4 (graphCode G) = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    apply hn
    simp only [bC4, List.any_eq_true] at hc
    rcases hc with ⟨a, _, b, _, c, _, d, _, hc⟩
    simp only [Bool.and_eq_true, badj_graphCode] at hc
    rcases hc with ⟨⟨⟨hneq, hab⟩, hbc⟩, hcd⟩
    rcases hneq with ⟨hneq, hab'⟩
    rcases of_decide_eq_true hneq with ⟨hnab, hnac, hnad, hnbc, hnbd, hncd⟩
    exact ⟨a, b, c, d, hnab, hnac, hnad, hnbc, hnbd, hncd, hab', hab, hbc, hcd⟩
  have hr : bRigid (graphCode G) = true := by
    simp only [bGood, hc4, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hgood
    have hup : bDegreeSum (graphCode G) ≤ 12 := of_decide_eq_true hgood.1
    have heq : bDegreeSum (graphCode G) = 12 := by omega
    rcases hgood.2 with hne | hr
    · simp [heq] at hne
    · exact hr
  intro a b hab
  simp only [bRigid, List.all_eq_true] at hr
  have ha := hr a (List.mem_ofFn.mpr ⟨a, rfl⟩)
  have hb := ha b (List.mem_ofFn.mpr ⟨b, rfl⟩)
  simp only [Bool.or_eq_true, List.any_eq_true] at hb
  rcases hb with heq | ⟨c, _, hc⟩
  · exact (hab (of_decide_eq_true heq)).elim
  · simp only [Bool.and_eq_true, badj_graphCode] at hc
    rcases hc with ⟨⟨hneq, hac⟩, hcb⟩
    exact ⟨c, (of_decide_eq_true hneq).1, (of_decide_eq_true hneq).2, hac, hcb⟩

theorem five_generic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 5)
    (hn : ¬ HasC4Fin (G.comap (Fintype.equivFinOfCardEq hcard).symm)) :
    (∑ v, G.degree v ≤ 12) ∧
      (∑ v, G.degree v = 12 →
        ∀ a b, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b ∧ G.Adj a c ∧ G.Adj c b) := by
  classical
  let e : Fin 5 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let K : SimpleGraph (Fin 5) := G.comap e
  let iso : K ≃g G := SimpleGraph.Iso.comap e G
  have hupK := five_degree_sum_le K hn
  have hsum : (∑ x, K.degree x) = ∑ v, G.degree v := by
    simp only [← iso.degree_eq]
    exact Equiv.sum_comp iso.toEquiv (fun v => G.degree v)
  constructor
  · omega
  · intro heq a b hab
    have hrig := five_rigid K (by omega) hn (iso.symm a) (iso.symm b)
      (iso.symm.injective.ne hab)
    obtain ⟨c, hca, hcb, hac, hcb'⟩ := hrig
    refine ⟨iso c, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hca (iso.injective (by simpa using h))
    · intro h
      exact hcb (iso.injective (by simpa using h))
    · simpa using iso.map_rel_iff.mpr hac
    · simpa using iso.map_rel_iff.mpr hcb'

def HasC4Gen {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

theorem six_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 6)
    (hlow : ∃ v, G.degree v ≤ 2) (hn : ¬ HasC4Gen G) :
    G.edgeFinset.card ≤ 7 := by
  classical
  obtain ⟨v, hv⟩ := hlow
  let S : Set V := {v}ᶜ
  let H : SimpleGraph S := G.induce S
  have hScard : Fintype.card S = 5 := by
    dsimp [S]
    rw [Fintype.card_compl_set]
    simp [hcard]
  let e : Fin 5 ≃ S := (Fintype.equivFinOfCardEq hScard).symm
  let K : SimpleGraph (Fin 5) := H.comap e
  have hnK : ¬ HasC4Fin K := by
    rintro ⟨a, b, c, d, hnab, hnac, hnad, hnbc, hnbd, hncd, hab, hbc, hcd, hda⟩
    apply hn
    exact ⟨(e a).val, (e b).val, (e c).val, (e d).val,
      fun h => hnab (e.injective (Subtype.ext h)),
      fun h => hnac (e.injective (Subtype.ext h)),
      fun h => hnad (e.injective (Subtype.ext h)),
      fun h => hnbc (e.injective (Subtype.ext h)),
      fun h => hnbd (e.injective (Subtype.ext h)),
      fun h => hncd (e.injective (Subtype.ext h)), hab, hbc, hcd, hda⟩
  have hfive := five_generic H hScard hnK
  have hdel : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
    simpa [H, S] using (G.card_edgeFinset_induce_compl_singleton v).trans
      (G.card_edgeFinset_deleteIncidenceSet v)
  have hsumH := H.sum_degrees_eq_twice_card_edges
  have hvedge := G.degree_le_card_edgeFinset (v := v)
  by_contra hbound
  have heG : 8 ≤ G.edgeFinset.card := by omega
  have heH : H.edgeFinset.card ≤ 6 := by omega
  have heG8 : G.edgeFinset.card = 8 := by omega
  have hv2 : G.degree v = 2 := by omega
  have heH6 : H.edgeFinset.card = 6 := by omega
  have hsum12 : ∑ x, H.degree x = 12 := by omega
  have hrig := hfive.2 hsum12
  have hcardN : (G.neighborFinset v).card = 2 := by
    rw [card_neighborFinset_eq_degree, hv2]
  obtain ⟨a, b, hab, hnb⟩ := Finset.card_eq_two.mp hcardN
  have haN : a ∈ G.neighborFinset v := by rw [hnb]; simp
  have hbN : b ∈ G.neighborFinset v := by rw [hnb]; simp
  have hav : a ≠ v := ((G.mem_neighborFinset v a).mp haN).ne.symm
  have hbv : b ≠ v := ((G.mem_neighborFinset v b).mp hbN).ne.symm
  let aS : S := ⟨a, by simpa [S] using hav⟩
  let bS : S := ⟨b, by simpa [S] using hbv⟩
  have habS : aS ≠ bS := by
    intro h
    exact hab (congrArg Subtype.val h)
  obtain ⟨c, hca, hcb, hac, hcb'⟩ := hrig aS bS habS
  have hcv : c.val ≠ v := by
    have hcprop := c.property
    change c.val ∈ ({v}ᶜ : Set V) at hcprop
    exact fun h => hcprop (by simpa using h)
  change G.Adj a c.val at hac
  change G.Adj c.val b at hcb'
  apply hn
  exact ⟨v, a, c.val, b, ((G.mem_neighborFinset v a).mp haN).ne,
    hcv.symm, ((G.mem_neighborFinset v b).mp hbN).ne,
    by exact fun h => hca (Subtype.ext h.symm), hab,
    by exact fun h => hcb (Subtype.ext h),
    (G.mem_neighborFinset v a).mp haN, hac, hcb',
    (G.mem_neighborFinset v b).mp hbN |>.symm⟩

open scoped Classical

universe u

def DegenerateTwo' {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (W : Type u) [Fintype W] [Nonempty W] (f : W → V), Function.Injective f →
    ∃ w, ((G.comap f).neighborSet w).ncard ≤ 2

theorem c4free_degenerate_edge_bound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : DegenerateTwo' G)
    (hn : ¬ HasC4Gen G) (hsix : 6 ≤ Fintype.card V) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  classical
  generalize hc : Fintype.card V = n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv⟩ := hd V id Function.injective_id
    have hv' : G.degree v ≤ 2 := by
      have heq : (G.comap id).neighborSet v = G.neighborSet v := by
        ext x
        simp
      rw [heq] at hv
      have hdeg := G.card_neighborSet_eq_degree (v := v)
      rw [Set.fintypeCard_eq_ncard] at hdeg
      omega
    by_cases hn6 : n = 6
    · have hb := six_edge_bound G (hc.trans hn6) ⟨v, hv'⟩ hn
      omega
    · let S : Set V := {v}ᶜ
      let H : SimpleGraph S := G.induce S
      have hScard : Fintype.card S = n - 1 := by
        dsimp [S]
        rw [Fintype.card_compl_set]
        simp [hc]
      have hdH : DegenerateTwo' H := by
        intro W _ _ f hf
        exact hd W (Subtype.val ∘ f) (Subtype.val_injective.comp hf)
      have hnH : ¬ HasC4Gen H := by
        rintro ⟨a, b, c, d, hnab, hnac, hnad, hnbc, hnbd, hncd, hab, hbc, hcd, hda⟩
        apply hn
        exact ⟨a.val, b.val, c.val, d.val,
          Subtype.val_injective.ne hnab, Subtype.val_injective.ne hnac,
          Subtype.val_injective.ne hnad, Subtype.val_injective.ne hnbc,
          Subtype.val_injective.ne hnbd, Subtype.val_injective.ne hncd,
          hab, hbc, hcd, hda⟩
      have hrec := ih (n - 1) (by omega) H hdH hnH hScard (by omega)
      have hdel : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
        simpa [H, S] using (G.card_edgeFinset_induce_compl_singleton v).trans
          (G.card_edgeFinset_deleteIncidenceSet v)
      have hvedge := G.degree_le_card_edgeFinset (v := v)
      have hrecover : G.edgeFinset.card - G.degree v + G.degree v = G.edgeFinset.card :=
        Nat.sub_add_cancel hvedge
      omega

end
/- END BoundaryFiveScratch -/

/- BEGIN ErdosGyarfasBoundaryFourStructureProof -/
section
/-
Novel continuation of Jig P399 statement 9.  That statement proves
2|V| + 4 ≤ 3|V3| for a hypothetical lexicographically minimal
Erdős–Gyárfás counterexample.  Here we classify its equality boundary:
all high-degree vertices must be quartic, and, when there are at least two of
them, at most one cubic vertex can have no high-degree neighbor.

The generic counterexample, deletion, independence, two-thirds counting, and
no-four-cycle lemmas adapt Andrew Bisch's EGC.lean (2026-08-13).  The strict
contraction argument was posted by jul059 on the Erdős problem 64 forum; the
+3 bound was proposed in Jig statement 7; the parity +4 bound is Jig statement
9.  The new ingredient is a zero-incidence refinement of statement 9's
contraction count, followed by equality and parity analysis.  This remains a
structural restriction on hypothetical counterexamples, not a resolution of
the Erdős–Gyárfás conjecture.
-/


namespace BoundaryStructureInherited


namespace CycleDoubleWork

lemma interleave_nodup {A B : Type*} (l : List A) (f g : A → B)
    (hf : (l.map f).Nodup) (hg : (l.map g).Nodup)
    (hfg : ∀ x ∈ l, ∀ y ∈ l, f x ≠ g y) :
    (l.flatMap fun x => [f x, g x]).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hf hg
    have ht := ih hf.2 hg.2 (fun x hx y hy => hfg x (by simp [hx]) y (by simp [hy]))
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
    refine ⟨?_, ?_, ht⟩
    · simp only [List.mem_cons, List.mem_flatMap]
      intro h
      rcases h with h | ⟨x, hx, h | h⟩
      · exact hfg a (by simp) a (by simp) h
      · exact hf.1 (List.mem_map.mpr ⟨x, hx, h.symm⟩)
      · exact hfg a (by simp) x (by simp [hx]) (by simpa using h)
    · simp only [List.mem_flatMap, List.mem_cons]
      rintro ⟨x, hx, h | h⟩
      · exact hfg x (by simp [hx]) a (by simp) h.symm
      · exact hg.1 (List.mem_map.mpr ⟨x, hx, (by simpa using h : g a = g x).symm⟩)

variable {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}

noncomputable def doubleWalk (f : V → W) (m : H.Dart → W)
    (ha : ∀ d, G.Adj (f d.fst) (m d))
    (hb : ∀ d, G.Adj (m d) (f d.snd)) :
    {u v : V} → H.Walk u v → G.Walk (f u) (f v) := by
  intro u v p
  induction p with
  | nil => exact .nil
  | @cons u v w h p ih => exact .cons (ha ⟨(u,v), h⟩) (.cons (hb ⟨(u,v), h⟩) ih)

lemma double_length (f : V → W) (m : H.Dart → W) (ha hb)
    {u v : V} (p : H.Walk u v) :
    (doubleWalk (G := G) f m ha hb p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [doubleWalk] at ih; simp [doubleWalk, ih]; omega

lemma double_support (f : V → W) (m : H.Dart → W) (ha hb)
    {u v : V} (p : H.Walk u v) :
    (doubleWalk (G := G) f m ha hb p).support.tail =
      p.darts.flatMap (fun d => [m d, f d.snd]) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [doubleWalk, SimpleGraph.Walk.support_cons, List.tail_cons,
      SimpleGraph.Walk.darts_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    rw [← ih, SimpleGraph.Walk.cons_tail_support]
    rfl

theorem double_cycle (f : V → W) (hf : Function.Injective f)
    (m : H.Dart → W) (ha hb) {u : V} (p : H.Walk u u)
    (hp : p.IsCycle) (hm : (p.darts.map m).Nodup)
    (hsep : ∀ d ∈ p.darts, ∀ v, m d ≠ f v) :
    (doubleWalk (G := G) f m ha hb p).IsCycle := by
  have hn : (doubleWalk f m ha hb p).support.tail.Nodup := by
    rw [double_support]
    apply interleave_nodup _ _ _ hm
    · have hh := hp.support_nodup.map hf
      rw [← SimpleGraph.Walk.map_snd_darts, List.map_map] at hh
      exact hh
    · exact fun d hd e _ => hsep d hd e.snd
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨SimpleGraph.Walk.IsPath.mk' ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_tail_of_not_nil]
    · exact hn
    · intro h
      have hl := (double_length f m ha hb p)
      have hp3 := hp.three_le_length
      have hz := SimpleGraph.Walk.length_eq_zero_iff.mpr h
      omega
  · rw [double_length]
    have := hp.three_le_length
    omega

theorem double_cycle_of_edge_labels (f : V → W) (hf : Function.Injective f)
    (m : H.Dart → W) (ha hb) {u : V} (p : H.Walk u u)
    (hp : p.IsCycle)
    (hm : ∀ d e, m d = m e → d.edge = e.edge)
    (hsep : ∀ d, ∀ v, m d ≠ f v) :
    (doubleWalk (G := G) f m ha hb p).IsCycle := by
  apply double_cycle f hf m ha hb p hp
  · have he := hp.isTrail.edges_nodup
    rw [SimpleGraph.Walk.edges_eq_map_darts, List.Nodup, List.pairwise_map] at he
    rw [List.Nodup, List.pairwise_map]
    exact he.imp (fun h hme => h (hm _ _ hme))
  · exact fun d _ v => hsep d v

end CycleDoubleWork

namespace DegenerateEdgeBoundWork

open scoped Classical

universe u

def DegenerateTwo {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (W : Type u) [Fintype W] [Nonempty W] (f : W → V), Function.Injective f →
    ∃ w, (G.comap f).degree w ≤ 2

theorem edge_bound {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hd : DegenerateTwo G) (hn : 2 ≤ Fintype.card V) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V := by
  classical
  generalize hc : Fintype.card V = n at *
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases h2 : n = 2
    · have he := G.card_edgeFinset_le_card_choose_two
      rw [hc, h2] at he
      norm_num at he
      omega
    have hn3 : 3 ≤ n := by omega
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv⟩ := hd V id Function.injective_id
    change G.degree v ≤ 2 at hv
    let S : Set V := {v}ᶜ
    let H := G.induce S
    have hs : Fintype.card S = n - 1 := by
      dsimp [S]
      rw [Fintype.card_compl_set]
      simp [hc]
    have hH : DegenerateTwo H := by
      intro W _ _ f hf
      exact hd W (Subtype.val ∘ f) (Subtype.val_injective.comp hf)
    have he := ih (n - 1) (by omega) H hH hs (by omega)
    have hdel : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
      dsimp [H, S]
      rw [G.card_edgeFinset_induce_compl_singleton v,
        G.card_edgeFinset_deleteIncidenceSet v]
    have hvle := G.degree_le_card_edgeFinset (v := v)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he hdel hvle ⊢
    rw [hdel] at he
    omega

end DegenerateEdgeBoundWork

open Finset SimpleGraph

universe u

namespace EGC

/-! ### Power-of-two cycles -/

/-- A graph has a power-of-two cycle if it contains a cycle whose length is `2 ^ k`
for some `k`.  (In a simple graph any cycle has length ≥ 3, so `k ≥ 2` is automatic.) -/
def HasPow2Cycle {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ (w : W) (c : H.Walk w w), c.IsCycle ∧ ∃ k : ℕ, c.length = 2 ^ k

/-- Power-of-two cycles transfer along injective graph homomorphisms. -/
theorem HasPow2Cycle.map {W W' : Type*} {H : SimpleGraph W} {K : SimpleGraph W'}
    (f : H →g K) (hf : Function.Injective f) : HasPow2Cycle H → HasPow2Cycle K := by
  rintro ⟨w, c, hc, k, hk⟩
  refine ⟨f w, c.map f, (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc, k, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  exact hk

/-- Power-of-two cycles transfer along subgraph inclusions (same vertex set). -/
theorem HasPow2Cycle.mono {W : Type*} {H K : SimpleGraph W} (hle : H ≤ K) :
    HasPow2Cycle H → HasPow2Cycle K :=
  HasPow2Cycle.map (.ofLE hle) (fun _ _ h => h)

/-- Power-of-two cycles in an induced subgraph give power-of-two cycles in the graph. -/
theorem HasPow2Cycle.of_induce {W : Type*} {H : SimpleGraph W} {s : Set W} :
    HasPow2Cycle (H.induce s) → HasPow2Cycle H := by
  rintro ⟨w, c, hc, k, hk⟩
  let f : H.induce s →g H := ⟨Subtype.val, fun {a b} hab => hab⟩
  have hf : Function.Injective f := Subtype.val_injective
  exact ⟨↑w, c.map f, (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc, k, by
    rwa [SimpleGraph.Walk.length_map]⟩

/-! ### Counterexamples and minimal counterexamples -/

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A counterexample to the Erdős–Gyárfás conjecture: a finite nonempty graph with
minimum degree at least 3 and no cycle of power-of-two length. -/
structure IsCounterexample : Prop where
  nonempty : Nonempty V
  degree_ge : ∀ v : V, 3 ≤ G.degree v
  no_pow2 : ¬ HasPow2Cycle G

/-- A *minimal* counterexample: a counterexample which is lexicographically minimal in
(order, size) among all counterexamples (on any finite vertex type in the same universe).
This matches the definition in the paper (and in Carr's note). -/
structure IsMinCex : Prop extends IsCounterexample G where
  minimal : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
    IsCounterexample H →
    Fintype.card V < Fintype.card W ∨
      (Fintype.card V = Fintype.card W ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard)

variable {G}

namespace IsMinCex

/-- A minimal counterexample has at least four vertices. -/
theorem four_le_card (hG : IsMinCex G) : 4 ≤ Fintype.card V := by
  obtain ⟨v⟩ := hG.nonempty
  have h1 := hG.degree_ge v
  have h2 := G.degree_lt_card_verts v
  omega

/-- Minimality, size version: a proper subgraph of a minimal counterexample on the same
vertex set with minimum degree ≥ 3 contains a power-of-two cycle.
(This is the way Lemma 1 is used for single-edge deletions.) -/
theorem min_size (hG : IsMinCex G) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hle : H ≤ G) (hne : H ≠ G) (hdeg : ∀ v, 3 ≤ H.degree v) : HasPow2Cycle H := by
  by_contra hno
  have hcex : IsCounterexample H := ⟨hG.nonempty, hdeg, hno⟩
  rcases hG.minimal V H hcex with h | ⟨-, h⟩
  · exact lt_irrefl _ h
  · have hsub : H.edgeSet ⊆ G.edgeSet := edgeSet_mono hle
    have hfin : G.edgeSet.Finite := G.edgeSet.toFinite
    have : G.edgeSet = H.edgeSet := (Set.eq_of_subset_of_ncard_le hsub h hfin).symm
    exact hne (edgeSet_injective this.symm)

/-- Minimality, order version: a graph on strictly fewer vertices with minimum degree ≥ 3
contains a power-of-two cycle. -/
theorem min_order (hG : IsMinCex G) (W : Type u) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hW : Nonempty W) (hcard : Fintype.card W < Fintype.card V)
    (hdeg : ∀ w, 3 ≤ H.degree w) : HasPow2Cycle H := by
  by_contra hno
  rcases hG.minimal W H ⟨hW, hdeg, hno⟩ with h | ⟨h, -⟩ <;> omega

end IsMinCex

/-! ### Deleting a small set of vertices (the paper's Lemma 1, vertex-deletion form) -/

section Induce

variable [DecidableEq V]

/-- Adjacency in an induced subgraph is decidable. -/
instance instDecidableRelInduceAdj (s : Set V) :
    DecidableRel (G.induce s).Adj := fun a b =>
  decidable_of_iff (G.Adj ↑a ↑b) Iff.rfl

/-- The degree of a vertex of `G.induce {x | x ∉ T}` counts the neighbors outside `T`. -/
theorem degree_induce_compl (T : Finset V) (w : ↥({x : V | x ∉ T} : Set V)) :
    (G.induce ({x : V | x ∉ T} : Set V)).degree w = ((G.neighborFinset ↑w) \ T).card := by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun a _ => (↑a : V)) ?_ ?_ ?_
  · rintro ⟨a, ha⟩ hmem
    rw [mem_neighborFinset] at hmem
    rw [Finset.mem_sdiff, mem_neighborFinset]
    exact ⟨hmem, ha⟩
  · exact fun a _ b _ h => Subtype.ext h
  · rintro y hy
    rw [Finset.mem_sdiff, mem_neighborFinset] at hy
    exact ⟨⟨y, hy.2⟩, by rw [mem_neighborFinset]; exact hy.1, rfl⟩

/-- **Lemma 1, vertex-deletion form.**  Deleting a nonempty set `T` of at most two vertices
from a minimal counterexample leaves some vertex `x ∉ T` with at most two neighbors
outside `T`. -/
theorem IsMinCex.exists_low_degree_delete (hG : IsMinCex G) (T : Finset V)
    (hT : T.Nonempty) (hTcard : T.card ≤ 2) :
    ∃ x, x ∉ T ∧ ((G.neighborFinset x) \ T).card ≤ 2 := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  -- the vertex set of the deleted graph is nonempty …
  have hcard4 := hG.four_le_card
  have huniv : (Finset.univ \ T).card = Fintype.card V - T.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hex : ∃ x : V, x ∉ T := by
    have : 0 < (Finset.univ \ T).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp this
    exact ⟨x, (Finset.mem_sdiff.mp hx).2⟩
  obtain ⟨x₀, hx₀⟩ := hex
  have hne : Nonempty ↥({x : V | x ∉ T} : Set V) := ⟨⟨x₀, hx₀⟩⟩
  -- … and strictly smaller than `V`
  obtain ⟨t₀, ht₀⟩ := hT
  have hlt : Fintype.card ↥({x : V | x ∉ T} : Set V) < Fintype.card V := by
    have hts : ¬ t₀ ∈ ({x : V | x ∉ T} : Set V) := by
      simp only [Set.mem_setOf_eq, not_not]
      exact ht₀
    exact Fintype.card_subtype_lt (p := fun x => x ∈ ({x : V | x ∉ T} : Set V)) hts
  -- all degrees of the deleted graph are ≥ 3, by assumption
  have hdeg : ∀ w : ↥({x : V | x ∉ T} : Set V),
      3 ≤ (G.induce ({x : V | x ∉ T} : Set V)).degree w := by
    rintro w
    rw [degree_induce_compl]
    have := hcon _ w.2
    omega
  -- so minimality produces a power-of-two cycle in it, hence in `G`: contradiction
  exact hG.no_pow2 <| HasPow2Cycle.of_induce <|
    hG.min_order _ (G.induce ({x : V | x ∉ T} : Set V)) hne hlt hdeg

end Induce

/-! ### Lemma 2 -/

section Lemma2

variable [DecidableEq V]

/-- **Lemma 2 (ii)** (Carr).  Every vertex of a minimal counterexample is adjacent to a
vertex of degree exactly 3. -/
theorem IsMinCex.exists_cubic_neighbor (hG : IsMinCex G) (v : V) :
    ∃ x, G.Adj v x ∧ G.degree x = 3 := by
  obtain ⟨x, hxT, hx⟩ :=
    hG.exists_low_degree_delete (T := {v}) (Finset.singleton_nonempty v) (by simp)
  have hxv : x ≠ v := by simpa using hxT
  have hdx := hG.degree_ge x
  have hsd : G.neighborFinset x \ {v} = (G.neighborFinset x).erase v := by
    ext y; simp [Finset.mem_sdiff, Finset.mem_erase, and_comm]
  by_cases hadj : G.Adj x v
  · refine ⟨x, hadj.symm, ?_⟩
    have hv_mem : v ∈ G.neighborFinset x := (G.mem_neighborFinset x v).mpr hadj
    rw [hsd, Finset.card_erase_of_mem hv_mem, card_neighborFinset_eq_degree] at hx
    omega
  · exfalso
    have hv_nmem : v ∉ G.neighborFinset x := by
      rw [mem_neighborFinset]; exact hadj
    rw [hsd, Finset.erase_eq_of_notMem hv_nmem, card_neighborFinset_eq_degree] at hx
    omega

/-- **Lemma 2 (i)** (Markström, Carr).  In a minimal counterexample, no two vertices of
degree at least 4 are adjacent, i.e. `V≥4` is an independent set. -/
theorem IsMinCex.not_adj_of_four_le_degree (hG : IsMinCex G) {u w : V}
    (hu : 4 ≤ G.degree u) (hw : 4 ≤ G.degree w) : ¬ G.Adj u w := by
  intro hadj
  have huw : u ≠ w := hadj.ne
  set H : SimpleGraph V := G.deleteEdges {s(u, w)} with hH
  haveI : DecidableRel H.Adj := fun a b =>
    decidable_of_iff (G.Adj a b ∧ ¬ s(a, b) = s(u, w)) (by
      rw [hH, deleteEdges_adj, Set.mem_singleton_iff])
  -- neighbor sets of the edge-deleted graph
  have hnbu : H.neighborFinset u = (G.neighborFinset u).erase w := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨hGy, hne⟩
      refine ⟨fun hyw => hne (Or.inl ⟨rfl, hyw⟩), hGy⟩
    · rintro ⟨hyw, hGy⟩
      refine ⟨hGy, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hyw h
      · exact huw h
  have hnbw : H.neighborFinset w = (G.neighborFinset w).erase u := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨hGy, hne⟩
      refine ⟨fun hyu => hne (Or.inr ⟨rfl, hyu⟩), hGy⟩
    · rintro ⟨hyu, hGy⟩
      refine ⟨hGy, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact huw h.symm
      · exact hyu h
  have hnbo : ∀ x, x ≠ u → x ≠ w → H.neighborFinset x = G.neighborFinset x := by
    intro x hxu hxw
    ext y
    rw [mem_neighborFinset, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hxu h1
      · exact hxw h1
  -- the deleted graph still has minimum degree ≥ 3
  have hdeg : ∀ v, 3 ≤ H.degree v := by
    intro x
    rcases eq_or_ne x u with rfl | hxu
    · rw [← card_neighborFinset_eq_degree, hnbu,
        Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj),
        card_neighborFinset_eq_degree]
      omega
    rcases eq_or_ne x w with rfl | hxw
    · rw [← card_neighborFinset_eq_degree, hnbw,
        Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj.symm),
        card_neighborFinset_eq_degree]
      omega
    · rw [← card_neighborFinset_eq_degree, hnbo x hxu hxw,
        card_neighborFinset_eq_degree]
      exact hG.degree_ge x
  -- it is a proper subgraph
  have hne : H ≠ G := by
    intro h
    have : H.Adj u w := h ▸ hadj
    rw [hH, deleteEdges_adj] at this
    exact this.2 (Set.mem_singleton _)
  -- contradiction with minimality
  exact hG.no_pow2 <| HasPow2Cycle.mono (deleteEdges_le _) <|
    hG.min_size H (deleteEdges_le _) hne hdeg

end Lemma2

/-! ### Theorem 3: the 2/3 bound -/

/-- **The counting step of Theorem 3**, isolated: if a finite graph has minimum degree ≥ 3,
its vertices of degree ≥ 4 form an independent set, and every cubic vertex has a cubic
neighbor, then at least two thirds of its vertices are cubic:  `2·|V| ≤ 3·|V₃|`. -/
theorem two_thirds_count
    (hdeg : ∀ v, 3 ≤ G.degree v)
    (hindep : ∀ u w, 4 ≤ G.degree u → 4 ≤ G.degree w → ¬ G.Adj u w)
    (hdom : ∀ v, G.degree v = 3 → ∃ x, G.Adj v x ∧ G.degree x = 3) :
    2 * Fintype.card V ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  -- `V₃` and `V₄` partition the vertex set
  have hpart : (Finset.univ.filter fun v => G.degree v = 3).card
      + (Finset.univ.filter fun v => 4 ≤ G.degree v).card = Fintype.card V := by
    have heq : (Finset.univ.filter fun v => ¬ G.degree v = 3)
        = (Finset.univ.filter fun v => 4 ≤ G.degree v) := by
      apply Finset.filter_congr
      intro v _
      have := hdeg v
      omega
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun v => G.degree v = 3)
    rw [heq, Finset.card_univ] at h0
    exact h0
  set V3 : Finset V := Finset.univ.filter (fun v => G.degree v = 3) with hV3
  set V4 : Finset V := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hV4
  -- every neighbor of a vertex of `V₄` is cubic
  have hnb4 : ∀ u ∈ V4, ∀ x, G.Adj u x → G.degree x = 3 := by
    intro u hu x hx
    have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
    have h3 := hdeg x
    rcases Nat.lt_or_ge (G.degree x) 4 with h | h
    · omega
    · exact absurd hx (hindep u x hu4 h)
  -- hence the degree sum over `V₄` counts edges into `V₃` …
  have hleft : ∀ u ∈ V4, G.degree u = (V3.filter (fun v => G.Adj u v)).card := by
    intro u hu
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    rw [mem_neighborFinset, Finset.mem_filter, hV3, Finset.mem_filter]
    constructor
    · intro h; exact ⟨⟨Finset.mem_univ x, hnb4 u hu x h⟩, h⟩
    · exact fun h => h.2
  -- … and the double count can be flipped
  have hswap : ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card
      = ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  -- each cubic vertex sends at most two edges to `V₄`
  have hup : ∀ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card ≤ 2 := by
    intro v hv
    have hv3 : G.degree v = 3 := (Finset.mem_filter.mp hv).2
    obtain ⟨x, hvx, hx3⟩ := hdom v hv3
    have hsub : V4.filter (fun u => G.Adj u v) ⊆ (G.neighborFinset v).erase x := by
      intro y hy
      rw [Finset.mem_filter, hV4, Finset.mem_filter] at hy
      rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, hy.2.symm⟩
      rintro rfl
      omega
    calc (V4.filter (fun u => G.Adj u v)).card
        ≤ ((G.neighborFinset v).erase x).card := Finset.card_le_card hsub
      _ = G.degree v - 1 := by
          rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v x).mpr hvx),
            card_neighborFinset_eq_degree]
      _ ≤ 2 := by omega
  -- put the counts together
  have hlow : 4 * V4.card ≤ ∑ u ∈ V4, G.degree u := by
    have := Finset.card_nsmul_le_sum V4 (fun u => G.degree u) 4
      (fun u hu => (Finset.mem_filter.mp hu).2)
    simpa [mul_comm] using this
  have hhigh : ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card ≤ 2 * V3.card := by
    have := Finset.sum_le_card_nsmul V3 (fun v => (V4.filter (fun u => G.Adj u v)).card) 2 hup
    simpa [mul_comm] using this
  have hsum : ∑ u ∈ V4, G.degree u = ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card :=
    Finset.sum_congr rfl hleft
  -- 4|V₄| ≤ 2|V₃|, and |V₃| + |V₄| = |V|, so 2|V| ≤ 3|V₃|
  have : 4 * V4.card ≤ 2 * V3.card := by
    calc 4 * V4.card ≤ ∑ u ∈ V4, G.degree u := hlow
      _ = ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by rw [hsum, hswap]
      _ ≤ 2 * V3.card := hhigh
  omega

/-- **Theorem 3.**  At least two thirds of the vertices of a minimal counterexample to the
Erdős–Gyárfás conjecture have degree exactly 3:  `2·|V(G)| ≤ 3·|V₃|`. -/
theorem IsMinCex.two_thirds [DecidableEq V] (hG : IsMinCex G) :
    2 * Fintype.card V ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card :=
  two_thirds_count hG.degree_ge (fun _ _ hu hw => hG.not_adj_of_four_le_degree hu hw)
    (fun v _ => hG.exists_cubic_neighbor v)

/-- Theorem 3, restated over `ℚ`:  `|V₃| ≥ (2/3)·|V(G)|`. -/
theorem IsMinCex.two_thirds_rat [DecidableEq V] (hG : IsMinCex G) :
    (2 / 3 : ℚ) * Fintype.card V
      ≤ ((Finset.univ.filter fun v => G.degree v = 3).card : ℚ) := by
  have h := hG.two_thirds
  have h' : (2 * Fintype.card V : ℚ)
      ≤ 3 * ((Finset.univ.filter fun v => G.degree v = 3).card : ℚ) := by
    exact_mod_cast h
  linarith

/-! ### Proposition 4 -/

/-- A minimal counterexample contains no 4-cycle (since `4 = 2²`): given the four sides of
a quadrilateral with distinct opposite corners, we get a contradiction. -/
theorem IsMinCex.no_c4 (hG : IsMinCex G) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  apply hG.no_pow2
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ c := hbc.ne
  have h3 : c ≠ d := hcd.ne
  have h4 : d ≠ a := hda.ne
  -- the six pairwise inequalities between the four edges of the quadrilateral
  have d1 : s(a, b) ≠ s(b, c) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact h1 h
    · exact hac h
  have d2 : s(a, b) ≠ s(c, d) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact hac h
    · exact h4 h.symm
  have d3 : s(a, b) ≠ s(d, a) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨-, h⟩)
    · exact h4 h.symm
    · exact hbd h
  have d4 : s(b, c) ≠ s(c, d) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact h2 h
    · exact hbd h
  have d5 : s(b, c) ≠ s(d, a) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact hbd h
    · exact h1 h.symm
  have d6 : s(c, d) ≠ s(d, a) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact h3 h
    · exact hac h.symm
  refine ⟨a, .cons hab (.cons hbc (.cons hcd (.cons hda .nil))), ?_, 2, by simp⟩
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp [d1, d2, d3, d4, d5, d6]
  · simp [h2, h3, h4, hbd, h1.symm, hac.symm]


theorem equality_structure
    (hdeg : ∀ v, 3 ≤ G.degree v)
    (hindep : ∀ u w, 4 ≤ G.degree u → 4 ≤ G.degree w → ¬ G.Adj u w)
    (hdom : ∀ v, G.degree v = 3 → ∃ x, G.Adj v x ∧ G.degree x = 3) :
    2 * Fintype.card V = 3 * (Finset.univ.filter fun v => G.degree v = 3).card →
    (∀ v, G.degree v = 3 →
      ((Finset.univ.filter fun u => 4 ≤ G.degree u).filter fun u => G.Adj u v).card = 2) := by
  intro hequality
  classical
  -- `V₃` and `V₄` partition the vertex set
  have hpart : (Finset.univ.filter fun v => G.degree v = 3).card
      + (Finset.univ.filter fun v => 4 ≤ G.degree v).card = Fintype.card V := by
    have heq : (Finset.univ.filter fun v => ¬ G.degree v = 3)
        = (Finset.univ.filter fun v => 4 ≤ G.degree v) := by
      apply Finset.filter_congr
      intro v _
      have := hdeg v
      omega
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun v => G.degree v = 3)
    rw [heq, Finset.card_univ] at h0
    exact h0
  set V3 : Finset V := Finset.univ.filter (fun v => G.degree v = 3) with hV3
  set V4 : Finset V := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hV4
  -- every neighbor of a vertex of `V₄` is cubic
  have hnb4 : ∀ u ∈ V4, ∀ x, G.Adj u x → G.degree x = 3 := by
    intro u hu x hx
    have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
    have h3 := hdeg x
    rcases Nat.lt_or_ge (G.degree x) 4 with h | h
    · omega
    · exact absurd hx (hindep u x hu4 h)
  -- hence the degree sum over `V₄` counts edges into `V₃` …
  have hleft : ∀ u ∈ V4, G.degree u = (V3.filter (fun v => G.Adj u v)).card := by
    intro u hu
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    rw [mem_neighborFinset, Finset.mem_filter, hV3, Finset.mem_filter]
    constructor
    · intro h; exact ⟨⟨Finset.mem_univ x, hnb4 u hu x h⟩, h⟩
    · exact fun h => h.2
  -- … and the double count can be flipped
  have hswap : ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card
      = ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  -- each cubic vertex sends at most two edges to `V₄`
  have hup : ∀ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card ≤ 2 := by
    intro v hv
    have hv3 : G.degree v = 3 := (Finset.mem_filter.mp hv).2
    obtain ⟨x, hvx, hx3⟩ := hdom v hv3
    have hsub : V4.filter (fun u => G.Adj u v) ⊆ (G.neighborFinset v).erase x := by
      intro y hy
      rw [Finset.mem_filter, hV4, Finset.mem_filter] at hy
      rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, hy.2.symm⟩
      rintro rfl
      omega
    calc (V4.filter (fun u => G.Adj u v)).card
        ≤ ((G.neighborFinset v).erase x).card := Finset.card_le_card hsub
      _ = G.degree v - 1 := by
          rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v x).mpr hvx),
            card_neighborFinset_eq_degree]
      _ ≤ 2 := by omega
  -- put the counts together
  have hlow : 4 * V4.card ≤ ∑ u ∈ V4, G.degree u := by
    have := Finset.card_nsmul_le_sum V4 (fun u => G.degree u) 4
      (fun u hu => (Finset.mem_filter.mp hu).2)
    simpa [mul_comm] using this
  have hhigh : ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card ≤ 2 * V3.card := by
    have := Finset.sum_le_card_nsmul V3 (fun v => (V4.filter (fun u => G.Adj u v)).card) 2 hup
    simpa [mul_comm] using this
  have hsum : ∑ u ∈ V4, G.degree u = ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card :=
    Finset.sum_congr rfl hleft
  -- 4|V₄| ≤ 2|V₃|, and |V₃| + |V₄| = |V|, so 2|V| ≤ 3|V₃|
  have : 4 * V4.card ≤ 2 * V3.card := by
    calc 4 * V4.card ≤ ∑ u ∈ V4, G.degree u := hlow
      _ = ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by rw [hsum, hswap]
      _ ≤ 2 * V3.card := hhigh
  have hsumeq : (∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card) = ∑ _v ∈ V3, 2 := by
    simp only [Finset.sum_const, smul_eq_mul]
    have hsumlow : 4 * V4.card ≤ ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by
      calc
        4 * V4.card ≤ ∑ u ∈ V4, G.degree u := hlow
        _ = _ := by rw [hsum, hswap]
    omega
  have heach := (Finset.sum_eq_sum_iff_of_le hup).mp hsumeq
  intro v hv
  exact heach v (by simp [V3, hv])

section Contraction
variable [DecidableEq V]

abbrev High (G : SimpleGraph V) [DecidableRel G.Adj] := {v : V // 4 ≤ G.degree v}

def contraction (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph (High G) where
  Adj u v := u ≠ v ∧ ∃ x, G.degree x = 3 ∧ G.Adj u.val x ∧ G.Adj x v.val
  symm.symm := by
    rintro u v ⟨hne, x, hx, hux, hxv⟩
    exact ⟨hne.symm, x, hx, hxv.symm, hux.symm⟩
  loopless.irrefl u h := h.1 rfl

theorem other_high (hG : IsMinCex G)
    (heq : 2 * Fintype.card V = 3 * (Finset.univ.filter fun v => G.degree v = 3).card)
    (u : High G) (x : V) (hux : G.Adj u.val x) :
    ∃ v : High G, v ≠ u ∧ G.Adj x v.val := by
  classical
  have hx3 : G.degree x = 3 := by
    have hd := hG.degree_ge x
    by_contra hn
    exact hG.not_adj_of_four_le_degree u.property (by omega) hux
  have hc := equality_structure hG.degree_ge
    (fun _ _ hu hw => hG.not_adj_of_four_le_degree hu hw)
    (fun v _ => hG.exists_cubic_neighbor v) heq x hx3
  let T := ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x)
  have hu : u.val ∈ T := by simp [T, u.property, hux]
  have hcT : T.card = 2 := hc
  have hpos : 0 < (T.erase u.val).card := by rw [Finset.card_erase_of_mem hu, hcT]; decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_erase.mp hv with ⟨hne, hv⟩
  have hparts : 4 ≤ G.degree v ∧ G.Adj v x := by simpa [T] using hv
  refine ⟨⟨v, hparts.1⟩, ?_, hparts.2.symm⟩
  intro hh
  exact hne (congrArg Subtype.val hh)

theorem middle_unique (hG : IsMinCex G) (u v : High G) (hne : u ≠ v)
    {x y : V} (hux : G.Adj u.val x) (hxv : G.Adj x v.val)
    (huy : G.Adj u.val y) (hyv : G.Adj y v.val) : x = y := by
  by_contra hxy
  exact hG.no_c4 hux hxv hyv.symm huy.symm
    (fun h => hne (Subtype.ext h)) hxy

theorem contraction_degree (hG : IsMinCex G)
    (heq : 2 * Fintype.card V = 3 * (Finset.univ.filter fun v => G.degree v = 3).card)
    (u : High G) :
    letI : DecidableRel (contraction G).Adj := Classical.decRel _
    G.degree u.val ≤ (contraction G).degree u := by
  classical
  let f : G.neighborSet u.val → (contraction G).neighborSet u := fun x =>
    let v := Classical.choose (other_high hG heq u x.val x.property)
    have hv := Classical.choose_spec (other_high hG heq u x.val x.property)
    ⟨v, hv.1.symm, x.val, by
      have hd := hG.degree_ge x.val
      by_contra hn
      exact hG.not_adj_of_four_le_degree u.property (by omega) x.property,
      x.property, hv.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hx := (f x).property
    have hy := (f y).property
    have hvx := Classical.choose_spec (other_high hG heq u x.val x.property)
    have hvy := Classical.choose_spec (other_high hG heq u y.val y.property)
    have hvals : (f x).val = (f y).val := congrArg Subtype.val h
    apply middle_unique hG u (f x).val hx.1 x.property hvx.2 y.property
    rw [hvals]
    exact hvy.2
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf

theorem high_card_lt (hG : IsMinCex G) : Fintype.card (High G) < Fintype.card V := by
  classical
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨x, _, hx⟩ := hG.exists_cubic_neighbor v
  exact Fintype.card_subtype_lt (p := fun x => 4 ≤ G.degree x) (x := x) (by omega)

theorem high_nonempty (hG : IsMinCex G)
    (heq : 2 * Fintype.card V = 3 * (Finset.univ.filter fun v => G.degree v = 3).card) :
    Nonempty (High G) := by
  classical
  by_contra hn
  have hall : ∀ v, G.degree v = 3 := by
    intro v
    have hd := hG.degree_ge v
    by_contra hne
    exact hn ⟨⟨v, by omega⟩⟩
  have hf : (Finset.univ.filter fun v => G.degree v = 3) = (Finset.univ : Finset V) := by
    ext v
    simp [hall]
  rw [hf, Finset.card_univ] at heq
  have := hG.four_le_card
  omega

noncomputable def middleLabel (d : (contraction G).Dart) : V :=
  Classical.choose d.adj.2

theorem middleLabel_spec (d : (contraction G).Dart) :
    G.degree (middleLabel d) = 3 ∧ G.Adj d.fst.val (middleLabel d) ∧
      G.Adj (middleLabel d) d.snd.val := Classical.choose_spec d.adj.2

theorem label_separated (d : (contraction G).Dart) (v : High G) :
    middleLabel d ≠ v.val := by
  intro hh
  have hd := (middleLabel_spec d).1
  rw [hh] at hd
  have := v.property
  omega

theorem label_edges_injective (hG : IsMinCex G)
    (heq : 2 * Fintype.card V = 3 * (Finset.univ.filter fun v => G.degree v = 3).card)
    (d e : (contraction G).Dart) (hh : middleLabel d = middleLabel e) :
    d.edge = e.edge := by
  classical
  let x := middleLabel d
  have hd := middleLabel_spec d
  have he := middleLabel_spec e
  rw [← hh] at he
  let T := ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x)
  have hc : T.card = 2 := equality_structure hG.degree_ge
    (fun _ _ hu hw => hG.not_adj_of_four_le_degree hu hw)
    (fun v _ => hG.exists_cubic_neighbor v) heq x hd.1
  have hdne : d.fst.val ≠ d.snd.val := fun h => d.adj.1 (Subtype.ext h)
  have hsub : {d.fst.val, d.snd.val} ⊆ T := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [T, x, d.fst.property, hd.2.1]
    · simp [T, x, d.snd.property, hd.2.2.symm]
  have hTeq : T = {d.fst.val, d.snd.val} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hc, hdne])).symm
  have hef : e.fst.val ∈ T := by simp [T, x, e.fst.property, he.2.1]
  have hes : e.snd.val ∈ T := by simp [T, x, e.snd.property, he.2.2.symm]
  rw [hTeq] at hef hes
  simp only [Finset.mem_insert, Finset.mem_singleton] at hef hes
  change s(d.fst, d.snd) = s(e.fst, e.snd)
  rw [Sym2.eq_iff]
  rcases hef with hf | hf <;> rcases hes with hs | hs
  · exact False.elim (e.adj.1 (Subtype.ext (hf.trans hs.symm)))
  · exact Or.inl ⟨Subtype.ext hf.symm, Subtype.ext hs.symm⟩
  · exact Or.inr ⟨Subtype.ext hs.symm, Subtype.ext hf.symm⟩
  · exact False.elim (e.adj.1 (Subtype.ext (hf.trans hs.symm)))

theorem IsMinCex.two_thirds_strict (hG : IsMinCex G) :
    2 * Fintype.card V < 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  have hle := hG.two_thirds
  by_contra hn
  have heq : 2 * Fintype.card V = 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by omega
  let H := contraction G
  obtain ⟨u, p, hp, k, hl⟩ := hG.min_order (High G) H
    (high_nonempty hG heq) (high_card_lt hG) (fun u => by
      have hd := contraction_degree hG heq u
      have hu := u.property
      exact le_trans (by omega : 3 ≤ G.degree u.val) hd)
  let f : High G → V := Subtype.val
  let m : H.Dart → V := middleLabel
  have ha : ∀ d : H.Dart, G.Adj (f d.fst) (m d) := fun d => (middleLabel_spec d).2.1
  have hb : ∀ d : H.Dart, G.Adj (m d) (f d.snd) := fun d => (middleLabel_spec d).2.2
  have hp' := CycleDoubleWork.double_cycle_of_edge_labels f Subtype.val_injective m ha hb p hp
    (label_edges_injective hG heq) label_separated
  apply hG.no_pow2
  refine ⟨u.val, CycleDoubleWork.doubleWalk f m ha hb p, hp', k + 1, ?_⟩
  rw [CycleDoubleWork.double_length, hl, pow_succ]
  omega

theorem high_neighbors_le_two (hG : IsMinCex G) (v : V) (hv3 : G.degree v = 3) :
    ((Finset.univ.filter fun u => 4 ≤ G.degree u).filter fun u => G.Adj u v).card ≤ 2 := by
  classical
  obtain ⟨x, hvx, hx3⟩ := hG.exists_cubic_neighbor v
  have hsub : ((Finset.univ.filter fun u => 4 ≤ G.degree u).filter fun u => G.Adj u v)
      ⊆ (G.neighborFinset v).erase x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.mem_erase, mem_neighborFinset]
    refine ⟨?_, hy.2.symm⟩
    rintro rfl
    omega
  calc
    _ ≤ ((G.neighborFinset v).erase x).card := Finset.card_le_card hsub
    _ = 2 := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v x).mpr hvx),
        card_neighborFinset_eq_degree, hv3]

theorem label_edges_injective_general (hG : IsMinCex G)
    (d e : (contraction G).Dart) (hh : middleLabel d = middleLabel e) :
    d.edge = e.edge := by
  classical
  let x := middleLabel d
  have hd := middleLabel_spec d
  have he := middleLabel_spec e
  rw [← hh] at he
  let T := ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x)
  have hc : T.card ≤ 2 := high_neighbors_le_two hG x hd.1
  have hdne : d.fst.val ≠ d.snd.val := fun h => d.adj.1 (Subtype.ext h)
  have hsub : {d.fst.val, d.snd.val} ⊆ T := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [T, x, d.fst.property, hd.2.1]
    · simp [T, x, d.snd.property, hd.2.2.symm]
  have hTeq : T = {d.fst.val, d.snd.val} :=
    (Finset.eq_of_subset_of_card_le hsub (by simpa [hdne] using hc)).symm
  have hef : e.fst.val ∈ T := by simp [T, x, e.fst.property, he.2.1]
  have hes : e.snd.val ∈ T := by simp [T, x, e.snd.property, he.2.2.symm]
  rw [hTeq] at hef hes
  simp only [Finset.mem_insert, Finset.mem_singleton] at hef hes
  change s(d.fst, d.snd) = s(e.fst, e.snd)
  rw [Sym2.eq_iff]
  rcases hef with hf | hf <;> rcases hes with hs | hs
  · exact False.elim (e.adj.1 (Subtype.ext (hf.trans hs.symm)))
  · exact Or.inl ⟨Subtype.ext hf.symm, Subtype.ext hs.symm⟩
  · exact Or.inr ⟨Subtype.ext hs.symm, Subtype.ext hf.symm⟩
  · exact False.elim (e.adj.1 (Subtype.ext (hf.trans hs.symm)))

theorem contraction_no_pow2 (hG : IsMinCex G) : ¬ HasPow2Cycle (contraction G) := by
  rintro ⟨u, p, hp, k, hl⟩
  let f : High G → V := Subtype.val
  let m : (contraction G).Dart → V := middleLabel
  have ha : ∀ d, G.Adj (f d.fst) (m d) := fun d => (middleLabel_spec d).2.1
  have hb : ∀ d, G.Adj (m d) (f d.snd) := fun d => (middleLabel_spec d).2.2
  have hp' := CycleDoubleWork.double_cycle_of_edge_labels f Subtype.val_injective m ha hb p hp
    (label_edges_injective_general hG) label_separated
  apply hG.no_pow2
  refine ⟨u.val, CycleDoubleWork.doubleWalk f m ha hb p, hp', k + 1, ?_⟩
  rw [CycleDoubleWork.double_length, hl, pow_succ]
  omega

theorem contraction_low_degree (hG : IsMinCex G)
    (W : Type u) [Fintype W] (f : W → High G) (hf : Function.Injective f)
    (hW : Nonempty W) :
    letI : DecidableRel ((contraction G).comap f).Adj := Classical.decRel _
    ∃ w, ((contraction G).comap f).degree w ≤ 2 := by
  classical
  by_contra hn
  have hdeg : ∀ w, 3 ≤ ((contraction G).comap f).degree w := by
    intro w
    have : ¬ ((contraction G).comap f).degree w ≤ 2 := fun h => hn ⟨w, h⟩
    omega
  have hc : Fintype.card W < Fintype.card V :=
    lt_of_le_of_lt (Fintype.card_le_of_injective f hf) (high_card_lt hG)
  have hp := hG.min_order W ((contraction G).comap f) hW hc hdeg
  exact contraction_no_pow2 hG (hp.map (SimpleGraph.Hom.comap f _) hf)

theorem degree_add_two_le_card (hG : IsMinCex G) (u : V) :
    G.degree u + 2 ≤ Fintype.card V := by
  classical
  obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp (by have := hG.degree_ge u; omega)
  have herase : 1 < ((G.neighborFinset v).erase u).card := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v u).mpr huv.symm),
      card_neighborFinset_eq_degree]
    have := hG.degree_ge v
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp herase
  rcases Finset.mem_erase.mp hy with ⟨hyu, hy⟩
  rcases Finset.mem_erase.mp hz with ⟨hzu, hz⟩
  have hvy := (G.mem_neighborFinset v y).mp hy
  have hvz := (G.mem_neighborFinset v z).mp hz
  have hn : ¬G.Adj u y ∨ ¬G.Adj u z := by
    by_contra h
    push_neg at h
    exact hG.no_c4 h.1 hvy.symm hvz h.2.symm huv.ne hyz
  obtain ⟨x, hxu, hux⟩ : ∃ x, x ≠ u ∧ ¬ G.Adj u x := by
    rcases hn with h | h
    · exact ⟨y, hyu, h⟩
    · exact ⟨z, hzu, h⟩
  have hsub : G.neighborFinset u ⊂ (Finset.univ : Finset V).erase u := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro w hw
      have ha := (G.mem_neighborFinset u w).mp hw
      simp [ha.ne.symm]
    · intro heq
      have hx : x ∈ G.neighborFinset u := by rw [heq]; simp [hxu]
      exact hux ((G.mem_neighborFinset u x).mp hx)
  have hh := Finset.card_lt_card hsub
  rw [card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ u),
    Finset.card_univ] at hh
  omega

theorem cubic_high_partition (hG : IsMinCex G) :
    (Finset.univ.filter fun v => G.degree v = 3).card + Fintype.card (High G) =
      Fintype.card V := by
  classical
  have heq : (Finset.univ.filter fun v => ¬ G.degree v = 3) =
      (Finset.univ.filter fun v => 4 ≤ G.degree v) := by
    apply Finset.filter_congr
    intro v _
    have := hG.degree_ge v
    omega
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
    (fun v => G.degree v = 3)
  rw [heq, Finset.card_univ] at hh
  simpa only [Fintype.card_subtype] using hh

theorem small_high_bound (hG : IsMinCex G) (hsmall : Fintype.card (High G) ≤ 1) :
    2 * Fintype.card V + 3 ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  have hpart := cubic_high_partition hG
  by_cases hh : Nonempty (High G)
  · obtain ⟨u⟩ := hh
    have hn := degree_add_two_le_card hG u.val
    have hu := u.property
    omega
  · have hz : Fintype.card (High G) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      exact hh (Fintype.card_pos_iff.mp hp)
    have hn := hG.four_le_card
    omega

theorem contraction_edge_bound (hG : IsMinCex G) (hn : 2 ≤ Fintype.card (High G)) :
    letI : DecidableRel (contraction G).Adj := Classical.decRel _
    (contraction G).edgeFinset.card + 3 ≤ 2 * Fintype.card (High G) := by
  classical
  apply DegenerateEdgeBoundWork.edge_bound
  · intro W _ hW f hf
    exact contraction_low_degree hG W f hf hW
  · exact hn

theorem cubic_high_neighbor_card_le_two (hG : IsMinCex G) {x : V}
    (hx : G.degree x = 3) :
    ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card ≤ 2 := by
  classical
  obtain ⟨z, hxz, hz⟩ := hG.exists_cubic_neighbor x
  have hs : ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x)
      ⊆ (G.neighborFinset x).erase z := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_erase, mem_neighborFinset]
    refine ⟨?_, hy.2.symm⟩
    rintro rfl
    omega
  have hc := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem (by simpa using hxz), card_neighborFinset_eq_degree, hx] at hc
  exact hc

theorem double_high_card_le_edges [DecidableEq V] (hG : IsMinCex G) :
    letI : DecidableRel (contraction G).Adj := Classical.decRel _
    ((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
      ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 2).card
      ≤ (contraction G).edgeFinset.card := by
  classical
  let D := ((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
      ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 2)
  have hp : ∀ x : D, ∃ a b : High G, a ≠ b ∧ G.Adj a.val x.val ∧ G.Adj x.val b.val := by
    intro x
    have hx := x.property
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hx.2
    have ha : a ∈ ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x.val) := by
      rw [he]; simp
    have hb : b ∈ ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x.val) := by
      rw [he]; simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact ⟨⟨a, ha.1⟩, ⟨b, hb.1⟩, (fun h => hab (congrArg Subtype.val h)), ha.2, hb.2.symm⟩
  choose a b hab ha hb using hp
  let f : D → (contraction G).edgeFinset := fun x =>
    ⟨s(a x, b x), by
      rw [mem_edgeFinset]
      exact ⟨hab x, x.val, (Finset.mem_filter.mp (Finset.mem_filter.mp x.property).1).2,
        ha x, hb x⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he : s(a x, b x) = s(a y, b y) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp he with he | he
    · apply middle_unique hG (a x) (b x) (hab x) (ha x) (hb x)
      · simpa [he.1] using ha y
      · simpa [he.2] using hb y
    · apply middle_unique hG (a x) (b x) (hab x) (ha x) (hb x)
      · simpa [he.1] using (hb y).symm
      · simpa [he.2] using (ha y).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem contraction_incidence_bound [DecidableEq V] (hG : IsMinCex G) :
    letI : DecidableRel (contraction G).Adj := Classical.decRel _
    4 * Fintype.card (High G) ≤
      (Finset.univ.filter fun x => G.degree x = 3).card + (contraction G).edgeFinset.card := by
  classical
  let V3 := Finset.univ.filter (fun v => G.degree v = 3)
  let V4 := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let c := fun x => (V4.filter fun v => G.Adj v x).card
  have hleft : ∀ u ∈ V4, G.degree u = (V3.filter (fun v => G.Adj u v)).card := by
    intro u hu
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    simp only [mem_neighborFinset, Finset.mem_filter, V3, Finset.mem_univ, true_and]
    constructor
    · intro hux
      refine ⟨?_, hux⟩
      have hd := hG.degree_ge x
      have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
      by_contra hn
      exact hG.not_adj_of_four_le_degree hu4 (by omega) hux
    · exact fun h => h.2
  have hswap : ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card = ∑ x ∈ V3, c x := by
    simp only [c]
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : 4 * V4.card ≤ ∑ x ∈ V3, c x := by
    calc
      _ ≤ ∑ u ∈ V4, G.degree u := by
        simpa [mul_comm] using Finset.card_nsmul_le_sum V4 (fun u => G.degree u) 4
          (fun u hu => (Finset.mem_filter.mp hu).2)
      _ = _ := by rw [Finset.sum_congr rfl hleft, hswap]
  have hup : ∑ x ∈ V3, c x ≤ V3.card + (V3.filter fun x => c x = 2).card := by
    calc
      _ ≤ ∑ x ∈ V3, (1 + if c x = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        have hc : c x ≤ 2 := cubic_high_neighbor_card_le_two hG (Finset.mem_filter.mp hx).2
        split_ifs <;> omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id]
  have hd := double_high_card_le_edges hG
  have hc : Fintype.card (High G) = V4.card := by simp [High, V4, Fintype.card_subtype]
  rw [hc]
  exact hlow.trans (hup.trans (Nat.add_le_add_left hd _))

theorem IsMinCex.cubic_bound_three (hG : IsMinCex G) :
    2 * Fintype.card V + 3 ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  by_cases hh : Fintype.card (High G) ≤ 1
  · exact small_high_bound hG hh
  · have hp := cubic_high_partition hG
    have he := contraction_edge_bound hG (by omega)
    have hi := contraction_incidence_bound hG
    omega

theorem high_degree_sum_upper [DecidableEq V] (hG : IsMinCex G) :
    letI : DecidableRel (contraction G).Adj := Classical.decRel _
    (∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) ≤
      (Finset.univ.filter fun x => G.degree x = 3).card + (contraction G).edgeFinset.card := by
  classical
  let V3 := Finset.univ.filter (fun v => G.degree v = 3)
  let V4 := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let c := fun x => (V4.filter fun v => G.Adj v x).card
  have hleft : ∀ u ∈ V4, G.degree u = (V3.filter (fun v => G.Adj u v)).card := by
    intro u hu
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    simp only [mem_neighborFinset, Finset.mem_filter, V3, Finset.mem_univ, true_and]
    constructor
    · intro hux
      refine ⟨?_, hux⟩
      have hd := hG.degree_ge x
      have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
      by_contra hn
      exact hG.not_adj_of_four_le_degree hu4 (by omega) hux
    · exact fun h => h.2
  have hswap : ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card = ∑ x ∈ V3, c x := by
    simp only [c]
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : 4 * V4.card ≤ ∑ x ∈ V3, c x := by
    calc
      _ ≤ ∑ u ∈ V4, G.degree u := by
        simpa [mul_comm] using Finset.card_nsmul_le_sum V4 (fun u => G.degree u) 4
          (fun u hu => (Finset.mem_filter.mp hu).2)
      _ = _ := by rw [Finset.sum_congr rfl hleft, hswap]
  have hup : ∑ x ∈ V3, c x ≤ V3.card + (V3.filter fun x => c x = 2).card := by
    calc
      _ ≤ ∑ x ∈ V3, (1 + if c x = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        have hc : c x ≤ 2 := cubic_high_neighbor_card_le_two hG (Finset.mem_filter.mp hx).2
        split_ifs <;> omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id]
  have hd := double_high_card_le_edges hG
  calc
    _ = ∑ x ∈ V3, c x := by rw [Finset.sum_congr rfl hleft, hswap]
    _ ≤ _ := hup.trans (Nat.add_le_add_left hd _)

theorem high_degree_sum_plus_zero_upper [DecidableEq V] (hG : IsMinCex G) :
    letI : DecidableRel (contraction G).Adj := Classical.decRel _
    (∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) +
      ((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
        ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 0).card ≤
      (Finset.univ.filter fun x => G.degree x = 3).card +
        (contraction G).edgeFinset.card := by
  classical
  let V3 := Finset.univ.filter (fun v => G.degree v = 3)
  let V4 := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let c := fun x => (V4.filter fun v => G.Adj v x).card
  have hleft : ∀ u ∈ V4, G.degree u = (V3.filter (fun v => G.Adj u v)).card := by
    intro u hu
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    simp only [mem_neighborFinset, Finset.mem_filter, V3, Finset.mem_univ, true_and]
    constructor
    · intro hux
      refine ⟨?_, hux⟩
      have hd := hG.degree_ge x
      have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
      by_contra hn
      exact hG.not_adj_of_four_le_degree hu4 (by omega) hux
    · exact fun h => h.2
  have hswap : ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card = ∑ x ∈ V3, c x := by
    simp only [c]
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  let Z := V3.filter fun x => c x = 0
  let D := V3.filter fun x => c x = 2
  have hrefined : (∑ x ∈ V3, c x) + Z.card ≤ V3.card + D.card := by
    calc
      (∑ x ∈ V3, c x) + Z.card =
          ∑ x ∈ V3, (c x + if c x = 0 then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [Z, Finset.sum_boole, Nat.cast_id]
      _ ≤ ∑ x ∈ V3, (1 + if c x = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        have hc : c x ≤ 2 := cubic_high_neighbor_card_le_two hG (Finset.mem_filter.mp hx).2
        split_ifs <;> omega
      _ = V3.card + D.card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, smul_eq_mul, mul_one, D, Finset.sum_boole, Nat.cast_id]
  have hd := double_high_card_le_edges hG
  change D.card ≤ (contraction G).edgeFinset.card at hd
  change (∑ u ∈ V4, G.degree u) + Z.card ≤
    V3.card + (contraction G).edgeFinset.card
  rw [Finset.sum_congr rfl hleft, hswap]
  exact hrefined.trans (Nat.add_le_add_left hd _)

theorem total_degree_split (hG : IsMinCex G) :
    (∑ v, G.degree v) =
      3 * (Finset.univ.filter fun v => G.degree v = 3).card +
      ∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u := by
  classical
  have heq : (Finset.univ.filter fun v => ¬ G.degree v = 3) =
      (Finset.univ.filter fun v => 4 ≤ G.degree v) := by
    apply Finset.filter_congr
    intro v _
    have := hG.degree_ge v
    omega
  have hh := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset V))
    (p := fun v => G.degree v = 3) (f := fun v => G.degree v)
  rw [heq] at hh
  rw [← hh]
  congr 1
  calc
    _ = ∑ _v ∈ (Finset.univ.filter fun v => G.degree v = 3), 3 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    _ = _ := by simp [mul_comm]

theorem high_degree_sum_lower (hG : IsMinCex G) :
    4 * Fintype.card (High G) ≤
      ∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u := by
  classical
  have := Finset.card_nsmul_le_sum (Finset.univ.filter fun u => 4 ≤ G.degree u)
    (fun u => G.degree u) 4 (fun u hu => (Finset.mem_filter.mp hu).2)
  simpa [High, Fintype.card_subtype, mul_comm] using this

theorem IsMinCex.cubic_bound_four (hG : IsMinCex G) :
    2 * Fintype.card V + 4 ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  have hp := cubic_high_partition hG
  have hthree := hG.cubic_bound_three
  by_contra hn
  have hboundary : (Finset.univ.filter fun v => G.degree v = 3).card =
      2 * Fintype.card (High G) + 3 := by omega
  have hs : (∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) =
      4 * Fintype.card (High G) := by
    have hlo := high_degree_sum_lower hG
    by_cases hbig : 2 ≤ Fintype.card (High G)
    · have hhi := high_degree_sum_upper hG
      have he := contraction_edge_bound hG hbig
      omega
    · have hpositive : 0 < Fintype.card (High G) := by
        by_contra hz
        have hc := hG.four_le_card
        omega
      have hcard : Fintype.card (High G) = 1 := by omega
      have hsize : Fintype.card V = 6 := by omega
      have heach : ∀ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u = 4 := by
        intro u hu
        have hl := (Finset.mem_filter.mp hu).2
        have hh := degree_add_two_le_card hG u
        omega
      calc
        _ = ∑ _u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), 4 :=
          Finset.sum_congr rfl heach
        _ = _ := by simp [High, Fintype.card_subtype, mul_comm]
  have hsum := total_degree_split hG
  have hhand := G.sum_degrees_eq_twice_card_edges
  omega

/-- Structure forced at the first boundary left open by `cubic_bound_four`.
Every high-degree vertex is actually quartic, and at most one cubic vertex can
have no high-degree neighbor. -/
theorem IsMinCex.boundary_four_structure (hG : IsMinCex G)
    (hboundary : 3 * (Finset.univ.filter fun v => G.degree v = 3).card =
      2 * Fintype.card V + 4) :
    (∀ u : V, 4 ≤ G.degree u → G.degree u = 4) ∧
      (2 ≤ Fintype.card (High G) →
      ((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
        ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 0).card ≤ 1) := by
  classical
  let V3 := Finset.univ.filter (fun v => G.degree v = 3)
  let V4 := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let D := ∑ u ∈ V4, G.degree u
  let h := Fintype.card (High G)
  have hV4card : V4.card = h := by
    simp [V4, h, High, Fintype.card_subtype]
  have hp := cubic_high_partition hG
  have hc : V3.card = 2 * h + 4 := by
    change V3.card + h = Fintype.card V at hp
    change 3 * V3.card = 2 * Fintype.card V + 4 at hboundary
    omega
  have hlo := high_degree_sum_lower hG
  change 4 * h ≤ D at hlo
  have hsum := total_degree_split hG
  change (∑ v, G.degree v) = 3 * V3.card + D at hsum
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hD : D = 4 * h := by
    by_cases hbig : 2 ≤ h
    · have hhi := high_degree_sum_upper hG
      change D ≤ V3.card + (contraction G).edgeFinset.card at hhi
      have he := contraction_edge_bound hG hbig
      omega
    · have hsmall : h ≤ 1 := by omega
      by_cases hz : h = 0
      · have hV4 : V4.card = 0 := by
          omega
        have hempty : V4 = ∅ := Finset.card_eq_zero.mp hV4
        simp [D, hempty, hz]
      · have hone : h = 1 := by omega
        have hn : Fintype.card V = 7 := by
          change V3.card + h = Fintype.card V at hp
          omega
        have hupper : D ≤ 5 := by
          have heach : ∀ u ∈ V4, G.degree u ≤ 5 := by
            intro u hu
            have hd := degree_add_two_le_card hG u
            omega
          have hs := Finset.sum_le_card_nsmul V4 (fun u => G.degree u) 5 heach
          have hV4 : V4.card = 1 := by
            omega
          change D ≤ 5
          simpa [hV4] using hs
        omega
  constructor
  · have hall : ∀ u ∈ V4, 4 ≤ G.degree u := fun u hu => (Finset.mem_filter.mp hu).2
    have hsumconst : (∑ _u ∈ V4, 4) = ∑ u ∈ V4, G.degree u := by
      change (∑ _u ∈ V4, 4) = D
      rw [hD]
      simp [V4, High, Fintype.card_subtype, h, mul_comm]
    have heach := (Finset.sum_eq_sum_iff_of_le hall).mp hsumconst
    intro u hu
    exact (heach u (by simp [V4, hu])).symm
  · have hrefined := high_degree_sum_plus_zero_upper hG
    change (2 ≤ h →
      (V3.filter fun x => (V4.filter fun v => G.Adj v x).card = 0).card ≤ 1)
    change D +
      ((V3.filter fun x => (V4.filter fun v => G.Adj v x).card = 0).card) ≤
      V3.card + (contraction G).edgeFinset.card at hrefined
    intro hbig
    have he := contraction_edge_bound hG hbig
    omega

end Contraction
end EGC

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

theorem pow2_iff {n : ℕ} {G : SimpleGraph (Fin n)} :
    HasPow2Cycle G ↔ EGC.HasPow2Cycle G := by
  constructor
  · rintro ⟨v, p, k, hc, _, hl⟩
    exact ⟨v, p, hc, k, hl⟩
  · rintro ⟨v, p, hc, k, hl⟩
    refine ⟨v, p, k, hc, ?_, hl⟩
    have hh := hc.three_le_length
    by_contra hn
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hl <;> omega

theorem to_generic {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : IsMinCex G) : EGC.IsMinCex G := by
  classical
  refine ⟨⟨?_, hG.1.2.1, ?_⟩, ?_⟩
  · exact ⟨⟨0, hG.1.1⟩⟩
  · exact fun h => hG.1.2.2 (pow2_iff.mpr h)
  · intro W inst H instH hH
    let e := (Fintype.equivFin W).symm
    let K : SimpleGraph (Fin (Fintype.card W)) := H.comap e
    let iso : K ≃g H := SimpleGraph.Iso.comap e H
    have hK : IsCex K := by
      refine ⟨Fintype.card_pos_iff.mpr hH.nonempty, ?_, ?_⟩
      · intro v
        rw [← iso.degree_eq v]
        exact hH.degree_ge (iso v)
      · intro h
        exact hH.no_pow2 ((pow2_iff.mp h).map iso.toHom iso.injective)
    have hh := hG.2 _ K hK
    have he : K.edgeFinset.card = H.edgeFinset.card := iso.card_edgeFinset_eq
    rcases hh with hlt | ⟨hc, hle⟩
    · exact Or.inl (by simpa using hlt)
    · refine Or.inr ⟨by simpa using hc, ?_⟩
      rw [he] at hle
      simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hle

theorem strict_proof :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    2 * n < 3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  intro n G inst hG
  simpa using (to_generic hG).two_thirds_strict

theorem bound_three_proof :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    2 * n + 3 ≤ 3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  intro n G inst hG
  simpa using (to_generic hG).cubic_bound_three

theorem proof :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    3 * (Finset.univ.filter fun v => G.degree v = 3).card = 2 * n + 4 →
      (∀ u : Fin n, 4 ≤ G.degree u → G.degree u = 4) ∧
        (2 ≤ (Finset.univ.filter fun v => 4 ≤ G.degree v).card →
          ((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
            ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v =>
              G.Adj v x).card = 0).card ≤ 1) := by
  intro n G inst hG hboundary
  have hboundary' : 3 * (Finset.univ.filter fun v => G.degree v = 3).card =
      2 * Fintype.card (Fin n) + 4 := by simpa using hboundary
  simpa only [EGC.High, Fintype.card_subtype] using
    (to_generic hG).boundary_four_structure hboundary'

end BoundaryStructureInherited

end
/- END ErdosGyarfasBoundaryFourStructureProof -/

/- BEGIN BoundaryOrderFinal -/
section

open Finset SimpleGraph

theorem hasPow2Cycle_of_c4 {V : Type*} {G : SimpleGraph V}
    (h : HasC4Gen G) :
    BoundaryStructureInherited.EGC.HasPow2Cycle G := by
  rcases h with ⟨a, b, c, d, hnab, hnac, hnad, hnbc, hnbd, hncd, hab, hbc, hcd, hda⟩
  refine ⟨a, .cons hab (.cons hbc (.cons hcd (.cons hda .nil))), ?_, 2, by simp⟩
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp [Sym2.eq_iff, hnab, hnac, hnad, hnbc, hnbd, hncd,
      hnab.symm, hnac.symm, hnad.symm, hnbc.symm, hnbd.symm, hncd.symm]
  · simp [hnab, hnac, hnad, hnbc, hnbd, hncd,
      hnab.symm, hnac.symm, hnad.symm, hnbc.symm, hnbd.symm, hncd.symm]

namespace BoundaryOrder

open BoundaryStructureInherited
open EGC

universe u

theorem generic_boundary_order {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : EGC.IsMinCex G)
    (hboundary : 3 * (Finset.univ.filter fun v => G.degree v = 3).card =
      2 * Fintype.card V + 4) :
    Fintype.card V ≤ 19 := by
  classical
  let V3 := Finset.univ.filter (fun v => G.degree v = 3)
  let h := Fintype.card (EGC.High G)
  have hp := cubic_high_partition hG
  have hc : V3.card = 2 * h + 4 := by
    change V3.card + h = Fintype.card V at hp
    change 3 * V3.card = 2 * Fintype.card V + 4 at hboundary
    omega
  have hh : h ≤ 5 := by
    by_contra hh
    have hsix : 6 ≤ h := by omega
    have hd : DegenerateTwo' (contraction G) := by
      intro W _ hW f hf
      obtain ⟨w, hw⟩ := contraction_low_degree hG W f hf hW
      refine ⟨w, ?_⟩
      rw [Set.ncard_eq_toFinset_card']
      exact hw
    have hnC4 : ¬ HasC4Gen (contraction G) := by
      intro hfour
      exact contraction_no_pow2 hG (hasPow2Cycle_of_c4 hfour)
    have heup := c4free_degenerate_edge_bound (contraction G) hd hnC4 hsix
    have helo := contraction_incidence_bound hG
    change 4 * h ≤ V3.card + (contraction G).edgeFinset.card at helo
    change (contraction G).edgeFinset.card + 5 ≤ 2 * h at heup
    omega
  change V3.card + h = Fintype.card V at hp
  omega

end BoundaryOrder

end
/- END BoundaryOrderFinal -/

/- BEGIN LargeHighSixBound -/
section

open SimpleGraph Finset
open BoundaryStructureInherited
open EGC

theorem large_high_six_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : EGC.IsMinCex G)
    (hsix : 6 ≤ Fintype.card (High G)) :
    2 * Fintype.card V + 6 ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  have hd : DegenerateTwo' (contraction G) := by
    intro W _ hW f hf
    obtain ⟨w, hw⟩ := contraction_low_degree hG W f hf hW
    refine ⟨w, ?_⟩
    rw [Set.ncard_eq_toFinset_card']
    exact hw
  have hnC4 : ¬ HasC4Gen (contraction G) := by
    intro hfour
    exact contraction_no_pow2 hG (hasPow2Cycle_of_c4 hfour)
  have heup := c4free_degenerate_edge_bound (contraction G) hd hnC4 hsix
  have hlo := high_degree_sum_lower hG
  have hhi := high_degree_sum_upper hG
  have hsplit := total_degree_split hG
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hp := cubic_high_partition hG
  omega


theorem large_order_six_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : EGC.IsMinCex G)
    (hn : 21 ≤ Fintype.card V) :
    2 * Fintype.card V + 6 ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  by_cases hh : 6 ≤ Fintype.card (High G)
  · exact large_high_six_bound G hG hh
  · have hp := cubic_high_partition hG
    omega


end
/- END LargeHighSixBound -/

/- BEGIN WeightedHighBound -/
section

open SimpleGraph Finset
open BoundaryStructureInherited
open EGC

theorem weighted_high_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : EGC.IsMinCex G)
    (hsix : 6 ≤ Fintype.card (High G)) :
    (∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) + 6 +
      2 * (((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
        ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 0).card / 2)
      ≤ (Finset.univ.filter fun x => G.degree x = 3).card + 2 * Fintype.card (High G) := by
  classical
  have hd : DegenerateTwo' (contraction G) := by
    intro W _ hW f hf
    obtain ⟨w, hw⟩ := contraction_low_degree hG W f hf hW
    refine ⟨w, ?_⟩
    rw [Set.ncard_eq_toFinset_card']
    exact hw
  have hnC4 : ¬ HasC4Gen (contraction G) := by
    intro hfour
    exact contraction_no_pow2 hG (hasPow2Cycle_of_c4 hfour)
  have heup := c4free_degenerate_edge_bound (contraction G) hd hnC4 hsix
  have hhi := high_degree_sum_plus_zero_upper hG
  have hsplit := total_degree_split hG
  have hhand := G.sum_degrees_eq_twice_card_edges
  omega


theorem weighted_cubic_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : EGC.IsMinCex G)
    (hsix : 6 ≤ Fintype.card (High G)) :
    2 * Fintype.card V + 6 +
      ((∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) -
        4 * Fintype.card (High G)) +
      2 * (((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
        ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 0).card / 2)
      ≤ 3 * (Finset.univ.filter fun x => G.degree x = 3).card := by
  have hw := weighted_high_bound G hG hsix
  have hlo := high_degree_sum_lower hG
  have hp := cubic_high_partition hG
  omega


theorem weighted_cubic_statement :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      BoundaryStructureInherited.IsMinCex G →
      6 ≤ (Finset.univ.filter fun u => 4 ≤ G.degree u).card →
      2 * n + 6 +
        ((∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) -
          4 * (Finset.univ.filter fun u => 4 ≤ G.degree u).card) +
        2 * (((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
          ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 0).card / 2)
        ≤ 3 * (Finset.univ.filter fun x => G.degree x = 3).card := by
  intro n G _ hG hsix
  have hh : 6 ≤ Fintype.card (High G) := by
    simpa only [High,Fintype.card_subtype] using hsix
  simpa only [High,Fintype.card_subtype,Fintype.card_fin] using
    weighted_cubic_bound G (to_generic hG) hh


end
/- END WeightedHighBound -/

namespace Submissions.ErdosGyarfasWeightedCubicBound.Cole
def proof := weighted_cubic_statement
end Submissions.ErdosGyarfasWeightedCubicBound.Cole
#print axioms Submissions.ErdosGyarfasWeightedCubicBound.Cole.proof
