import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos23DeterministicHalfCut.Direct

open scoped Classical symmDiff in
lemma toggle_singleton_involutive {V : Type} [DecidableEq V]
    (x : V) (S : Finset V) :
    (S ∆ {x}) ∆ {x} = S := by
  ext z
  simp [Finset.mem_symmDiff]

open scoped Classical symmDiff in
lemma toggle_separates_iff_not {V : Type} [DecidableEq V]
    {x y : V} (hxy : x ≠ y) (S : Finset V) :
    ((x ∈ S ∆ {x}) ≠ (y ∈ S ∆ {x})) ↔
      ¬((x ∈ S) ≠ (y ∈ S)) := by
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    simp [Finset.mem_symmDiff, hxy, hxy.symm, hx, hy]

open scoped Classical symmDiff in
lemma card_separating_eq_card_nonseparating
    {V : Type} [Fintype V] {x y : V} (hxy : x ≠ y) :
    (((Finset.univ : Finset V).powerset).filter fun S => (x ∈ S) ≠ (y ∈ S)).card =
      (((Finset.univ : Finset V).powerset).filter
        fun S => ¬((x ∈ S) ≠ (y ∈ S))).card := by
  classical
  let P := (Finset.univ : Finset V).powerset
  let A := P.filter fun S => (x ∈ S) ≠ (y ∈ S)
  let B := P.filter fun S => ¬((x ∈ S) ≠ (y ∈ S))
  change A.card = B.card
  refine Finset.card_bij'
      (fun S _ => S ∆ {x}) (fun S _ => S ∆ {x}) ?_ ?_ ?_ ?_
  · intro S hS
    have hSmem : S ∈ P := (Finset.mem_filter.mp hS).1
    have hsep : (x ∈ S) ≠ (y ∈ S) := (Finset.mem_filter.mp hS).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simp [P]
    · intro ht
      exact (toggle_separates_iff_not hxy S).mp ht hsep
  · intro S hS
    have hSmem : S ∈ P := (Finset.mem_filter.mp hS).1
    have hnsep : ¬((x ∈ S) ≠ (y ∈ S)) := (Finset.mem_filter.mp hS).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simp [P]
    · exact (toggle_separates_iff_not hxy S).mpr hnsep
  · intro S hS
    exact toggle_singleton_involutive x S
  · intro S hS
    exact toggle_singleton_involutive x S

open scoped Classical in
lemma two_mul_card_separating
    {V : Type} [Fintype V] {x y : V} (hxy : x ≠ y) :
    2 * (((Finset.univ : Finset V).powerset).filter
      fun S => (x ∈ S) ≠ (y ∈ S)).card =
      ((Finset.univ : Finset V).powerset).card := by
  classical
  let P := (Finset.univ : Finset V).powerset
  let A := P.filter fun S => (x ∈ S) ≠ (y ∈ S)
  let B := P.filter fun S => ¬((x ∈ S) ≠ (y ∈ S))
  have hab : A.card = B.card := by
    simpa [A, B, P] using card_separating_eq_card_nonseparating hxy
  have hpart : A.card + B.card = P.card := by
    simpa [A, B] using
      Finset.card_filter_add_card_filter_not
        (s := P) (fun S : Finset V => (x ∈ S) ≠ (y ∈ S))
  change 2 * A.card = P.card
  omega

open scoped Classical in
lemma two_mul_cut_card_eq_sum
    {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card =
      ∑ p ∈ (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2),
        if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0 := by
  classical
  let H := G.between (S : Set V) (Sᶜ : Finset V)
  let D := Finset.univ.filter fun p : V × V => G.Adj p.1 p.2
  have hedge := H.two_mul_card_edgeFinset
  change 2 * H.edgeFinset.card = _ 
  rw [hedge]
  have heq :
      Finset.univ.filter (fun p : V × V => H.Adj p.1 p.2) =
        D.filter fun p => (p.1 ∈ S) ≠ (p.2 ∈ S) := by
    ext p
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    change
      (H.Adj p.1 p.2) ↔
        (G.Adj p.1 p.2 ∧ ((p.1 ∈ S) ≠ (p.2 ∈ S)))
    simp only [H, SimpleGraph.between_adj, Finset.coe_compl,
      Set.mem_compl_iff, Finset.mem_coe]
    by_cases h₁ : p.1 ∈ S <;> by_cases h₂ : p.2 ∈ S <;> simp [h₁, h₂]
  rw [heq]
  rw [← Finset.sum_filter]
  simp [D]

open scoped Classical in
lemma sum_two_mul_cut_card
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    (∑ S ∈ (Finset.univ : Finset V).powerset,
      2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) =
        G.edgeFinset.card * (Finset.univ : Finset V).powerset.card := by
  classical
  let P := (Finset.univ : Finset V).powerset
  let D := Finset.univ.filter fun p : V × V => G.Adj p.1 p.2
  have hcut :
      (∑ S ∈ P,
        2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) =
          ∑ S ∈ P, ∑ p ∈ D,
            if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro S hS
    exact two_mul_cut_card_eq_sum G S
  have hinter :
      ∀ p ∈ D,
        2 * (∑ S ∈ P, if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0) =
          P.card := by
    intro p hp
    have hadj : G.Adj p.1 p.2 := by simpa [D] using hp
    have hne : p.1 ≠ p.2 := G.ne_of_adj hadj
    have hsep := two_mul_card_separating (V := V) hne
    have hsum :
        (∑ S ∈ P, if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0) =
          (P.filter fun S => (p.1 ∈ S) ≠ (p.2 ∈ S)).card := by
      rw [← Finset.sum_filter]
      simp
    rw [hsum]
    simpa [P] using hsep
  have hdouble :
      2 * (∑ S ∈ P,
        2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) =
          D.card * P.card := by
    rw [hcut, Finset.mul_sum]
    calc
      (∑ S ∈ P, 2 * ∑ p ∈ D,
          (if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0)) =
          ∑ S ∈ P, ∑ p ∈ D,
            2 * (if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mul_sum]
      _ = ∑ p ∈ D, ∑ S ∈ P,
            2 * (if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0) :=
        Finset.sum_comm
      _ = ∑ p ∈ D, 2 * ∑ S ∈ P,
            (if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
      _ = ∑ _p ∈ D, P.card :=
        Finset.sum_congr rfl fun p hp => hinter p hp
      _ = D.card * P.card := by simp
  have hDcard : D.card = 2 * G.edgeFinset.card := by
    simpa [D, mul_comm] using G.two_mul_card_edgeFinset.symm
  change (∑ S ∈ P,
      2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) =
    G.edgeFinset.card * P.card
  rw [hDcard] at hdouble
  have hdouble' :
      2 * (∑ S ∈ P,
        2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) =
          2 * (G.edgeFinset.card * P.card) := by
    simpa [mul_assoc] using hdouble
  rw [hcut]
  rw [hcut] at hdouble'
  exact Nat.mul_left_cancel (by norm_num) hdouble'

open scoped Classical in
theorem proof :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ (H : SimpleGraph V),
        H ≤ G ∧ H.IsBipartite ∧
          G.edgeFinset.card ≤ 2 * H.edgeFinset.card := by
  intro V _ G
  classical
  let P := (Finset.univ : Finset V).powerset
  by_contra! hnone
  have hPne : P.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [P]
  have hlt :
      (∑ S ∈ P,
        2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) <
          ∑ _S ∈ P, G.edgeFinset.card := by
    apply Finset.sum_lt_sum_of_nonempty hPne
    intro S hS
    have hle :
        G.between (S : Set V) (Sᶜ : Finset V) ≤ G :=
      G.between_le
    have hb :
        (G.between (S : Set V) (Sᶜ : Finset V)).IsBipartite := by
      apply G.between_isBipartite
      simpa [Finset.coe_compl] using
        (disjoint_compl_right : Disjoint (S : Set V) (S : Set V)ᶜ)
    have := hnone (G.between (S : Set V) (Sᶜ : Finset V)) hle hb
    convert this using 1
    congr 1
    apply congrArg Finset.card
    ext e
    simp only [mem_edgeFinset]
  have hsum := sum_two_mul_cut_card G
  change
    (∑ S ∈ P,
      2 * (G.between (S : Set V) (Sᶜ : Finset V)).edgeFinset.card) =
        G.edgeFinset.card * P.card at hsum
  have hconst : (∑ _S ∈ P, G.edgeFinset.card) =
      P.card * G.edgeFinset.card := by simp
  rw [hsum, hconst] at hlt
  have hirr :
      G.edgeFinset.card * P.card < G.edgeFinset.card * P.card := by
    simpa [mul_comm] using hlt
  exact Nat.lt_irrefl _ hirr

end Submissions.Erdos23DeterministicHalfCut.Direct
