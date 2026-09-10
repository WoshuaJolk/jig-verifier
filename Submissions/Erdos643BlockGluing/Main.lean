import Mathlib.Data.Finset.Card

/- Standalone local candidate. The canonical definitions match root v1.
The previously checked common-link proof is included because the verifier forbids
imports from another submission. No Statements module is imported. -/
namespace Submissions.Erdos643BlockGluing.Main

def Uniform {V : Type} [DecidableEq V]
    (t : ℕ) (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, A.card = t

def HasDisjointEqualUnion {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, ∃ D ∈ F,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    A ∪ B = C ∪ D ∧ Disjoint A B ∧ Disjoint C D

/-- An edge of the graph common to the links of u and v. -/
def CommonLinkPair {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) (u v : V) (P : Finset V) : Prop :=
  P.card = 2 ∧ u ∉ P ∧ v ∉ P ∧ insert u P ∈ F ∧ insert v P ∈ F

/-- Two disjoint edges in a common-link graph with distinct link vertices. -/
def HasCommonLinkMatching {V : Type} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∃ u v : V, u ≠ v ∧ ∃ P Q : Finset V,
    CommonLinkPair F u v P ∧ CommonLinkPair F u v Q ∧ Disjoint P Q

section
variable {V : Type} [DecidableEq V]

private theorem insert_ne_other {u v : V} {P Q : Finset V}
    (huv : u ≠ v) (huQ : u ∉ Q) : insert u P ≠ insert v Q := by
  intro h
  have hu : u ∈ insert v Q := h ▸ Finset.mem_insert_self u P
  exact (Finset.mem_insert.mp hu).elim huv huQ

private theorem insert_ne_same {u : V} {P Q : Finset V}
    (hP : P.Nonempty) (huP : u ∉ P) (hPQ : Disjoint P Q) :
    insert u P ≠ insert u Q := by
  obtain ⟨x, hx⟩ := hP
  intro h
  have hxQ : x ∈ insert u Q := h ▸ Finset.mem_insert_of_mem hx
  rcases Finset.mem_insert.mp hxQ with hxu | hxQ
  · exact huP (hxu ▸ hx)
  · exact Finset.disjoint_left.mp hPQ hx hxQ

/-- This implication does not require the ambient family to be uniform. -/
theorem obstruction_of_commonLinkMatching {F : Finset (Finset V)}
    (h : HasCommonLinkMatching F) : HasDisjointEqualUnion F := by
  rcases h with ⟨u, v, huv, P, Q,
    ⟨hP, huP, hvP, huPF, hvPF⟩,
    ⟨hQ, huQ, hvQ, huQF, hvQF⟩, hPQ⟩
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨insert u P, huPF, insert v Q, hvQF,
    insert v P, hvPF, insert u Q, huQF,
    insert_ne_other huv huQ, insert_ne_other huv huP,
    insert_ne_same hPne huP hPQ,
    insert_ne_same hQne hvQ hPQ.symm,
    insert_ne_other huv.symm hvQ, insert_ne_other huv.symm hvQ,
    ?_, ?_, ?_⟩
  · apply Finset.ext
    intro x
    simp only [Finset.mem_union, Finset.mem_insert]
    aesop
  · simp [Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      huv, huv.symm, huQ, hvP, hPQ]
  · simp [Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      huv, huv.symm, hvQ, huP, hPQ]

private theorem split_union {A B C D : Finset V} (h : A ∪ B = C ∪ D) :
    A = (A ∩ C) ∪ (A ∩ D) ∧
    B = (B ∩ C) ∪ (B ∩ D) ∧
    C = (A ∩ C) ∪ (B ∩ C) ∧
    D = (A ∩ D) ∪ (B ∩ D) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Finset.ext <;> intro x
  all_goals
    have hx : x ∈ A ∪ B ↔ x ∈ C ∪ D := by rw [h]
    simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢
    aesop

private theorem disjoint_inter_left {A B C D : Finset V}
    (h : Disjoint A B) : Disjoint (A ∩ C) (B ∩ D) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left h)

private theorem disjoint_inter_right {A B C D : Finset V}
    (h : Disjoint C D) : Disjoint (A ∩ C) (B ∩ D) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right h)

private theorem inter_card_lt_three {A B : Finset V}
    (hA : A.card = 3) (hB : B.card = 3) (hne : A ≠ B) :
    (A ∩ B).card < 3 := by
  by_contra hn
  have hi : A ∩ B = A := Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega)
  have hsub : A ⊆ B := by
    rw [← hi]
    exact Finset.inter_subset_right
  exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))

/-- Orient a forbidden decomposition so that one corner is a singleton. -/
private theorem commonLinkMatching_of_singleton_intersection
    {F : Finset (Finset V)} (hF : Uniform 3 F)
    {A B C D : Finset V} (hA : A ∈ F) (hB : B ∈ F)
    (hC : C ∈ F) (hD : D ∈ F) (hunion : A ∪ B = C ∪ D)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAC : (A ∩ C).card = 1) : HasCommonLinkMatching F := by
  obtain ⟨sA, sB, sC, sD⟩ := split_union hunion
  have cA : (A ∩ C).card + (A ∩ D).card = 3 := by
    rw [← Finset.card_union_of_disjoint (disjoint_inter_right hCD), ← sA]
    exact hF A hA
  have cB : (B ∩ C).card + (B ∩ D).card = 3 := by
    rw [← Finset.card_union_of_disjoint (disjoint_inter_right hCD), ← sB]
    exact hF B hB
  have cC : (A ∩ C).card + (B ∩ C).card = 3 := by
    rw [← Finset.card_union_of_disjoint (disjoint_inter_left hAB), ← sC]
    exact hF C hC
  have hAD : (A ∩ D).card = 2 := by omega
  have hBC : (B ∩ C).card = 2 := by omega
  have hBD : (B ∩ D).card = 1 := by omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hAC
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hBD
  have huAC : u ∈ A ∩ C := by rw [hu]; simp
  have hvBD : v ∈ B ∩ D := by rw [hv]; simp
  obtain ⟨huA, huC⟩ := Finset.mem_inter.mp huAC
  obtain ⟨hvB, hvD⟩ := Finset.mem_inter.mp hvBD
  have huv : u ≠ v := hAB.forall_ne_finset huA hvB
  have huAD : u ∉ A ∩ D := fun h =>
    Finset.disjoint_left.mp hCD huC (Finset.mem_inter.mp h).2
  have hvAD : v ∉ A ∩ D := fun h =>
    Finset.disjoint_left.mp hAB (Finset.mem_inter.mp h).1 hvB
  have huBC : u ∉ B ∩ C := fun h =>
    Finset.disjoint_left.mp hAB huA (Finset.mem_inter.mp h).1
  have hvBC : v ∉ B ∩ C := fun h =>
    Finset.disjoint_left.mp hCD (Finset.mem_inter.mp h).2 hvD
  have eA : A = insert u (A ∩ D) := by simpa only [hu, Finset.singleton_union] using sA
  have eB : B = insert v (B ∩ C) := by simpa only [hv, Finset.union_singleton] using sB
  have eC : C = insert u (B ∩ C) := by simpa only [hu, Finset.singleton_union] using sC
  have eD : D = insert v (A ∩ D) := by simpa only [hv, Finset.union_singleton] using sD
  refine ⟨u, v, huv, A ∩ D, B ∩ C, ?_, ?_, disjoint_inter_left hAB⟩
  · exact ⟨hAD, huAD, hvAD, eA ▸ hA, eD ▸ hD⟩
  · exact ⟨hBC, huBC, hvBC, eC ▸ hC, eB ▸ hB⟩

/-- Every forbidden quadruple of triples has a disjoint matching in a common link. -/
theorem commonLinkMatching_of_obstruction {F : Finset (Finset V)}
    (hF : Uniform 3 F) (h : HasDisjointEqualUnion F) : HasCommonLinkMatching F := by
  rcases h with ⟨A, hA, B, hB, C, hC, D, hD,
    hABne, hACne, hADne, hBCne, hBDne, hCDne, hunion, hAB, hCD⟩
  have sA := (split_union hunion).1
  have hsum : (A ∩ C).card + (A ∩ D).card = 3 := by
    rw [← Finset.card_union_of_disjoint (disjoint_inter_right hCD), ← sA]
    exact hF A hA
  have hltAC := inter_card_lt_three (hF A hA) (hF C hC) hACne
  have hltAD := inter_card_lt_three (hF A hA) (hF D hD) hADne
  have hor : (A ∩ C).card = 1 ∨ (A ∩ D).card = 1 := by omega
  rcases hor with hAC | hAD
  · exact commonLinkMatching_of_singleton_intersection hF hA hB hC hD hunion hAB hCD hAC
  · exact commonLinkMatching_of_singleton_intersection hF hA hB hD hC
      (hunion.trans (Finset.union_comm C D)) hAB hCD.symm hAD

theorem obstruction_iff_commonLinkMatching {F : Finset (Finset V)}
    (hF : Uniform 3 F) : HasDisjointEqualUnion F ↔ HasCommonLinkMatching F :=
  ⟨commonLinkMatching_of_obstruction hF, obstruction_of_commonLinkMatching⟩

/-- Exact avoidance reformulation; no asymptotic upper bound is asserted. -/
theorem free_iff_commonLinks_intersecting {F : Finset (Finset V)}
    (hF : Uniform 3 F) :
    ¬HasDisjointEqualUnion F ↔
      ∀ u v : V, u ≠ v → ∀ P Q : Finset V,
        CommonLinkPair F u v P → CommonLinkPair F u v Q → ¬Disjoint P Q := by
  constructor
  · intro hfree u v huv P Q hP hQ hPQ
    exact hfree (obstruction_of_commonLinkMatching ⟨u, v, huv, P, Q, hP, hQ, hPQ⟩)
  · intro hlinks hbad
    obtain ⟨u, v, huv, P, Q, hP, hQ, hPQ⟩ := commonLinkMatching_of_obstruction hF hbad
    exact hlinks u v huv P Q hP hQ hPQ

/-- Pair-linear block gluing preserves the exact forbidden-quadruple condition. -/
theorem block_gluing_avoids {F : Finset (Finset V)} (hF : Uniform 3 F)
    (blocks : Finset (Finset V))
    (hcover : ∀ A ∈ F, ∃ B ∈ blocks, A ⊆ B)
    (hseparated : ∀ B ∈ blocks, ∀ C ∈ blocks,
      2 ≤ (B ∩ C).card → B = C)
    (hlocal : ∀ B ∈ blocks,
      ¬HasDisjointEqualUnion (F.filter (fun A => A ⊆ B))) :
    ¬HasDisjointEqualUnion F := by
  intro hbad
  obtain ⟨u, v, huv, P, Q,
    ⟨hP, huP, hvP, huPF, hvPF⟩,
    ⟨hQ, huQ, hvQ, huQF, hvQF⟩, hPQ⟩ :=
    commonLinkMatching_of_obstruction hF hbad
  obtain ⟨B, hB, huPB⟩ := hcover _ huPF
  obtain ⟨C, hC, hvPC⟩ := hcover _ hvPF
  obtain ⟨D, hD, huQD⟩ := hcover _ huQF
  obtain ⟨E, hE, hvQE⟩ := hcover _ hvQF
  have same {R X Y : Finset V} (hX : X ∈ blocks) (hY : Y ∈ blocks)
      (hR : R.card = 2) (hRX : R ⊆ X) (hRY : R ⊆ Y) : X = Y := by
    apply hseparated X hX Y hY
    have hsub : R ⊆ X ∩ Y := fun x hx => Finset.mem_inter.mpr ⟨hRX hx, hRY hx⟩
    have := Finset.card_le_card hsub
    omega
  have hBC : B = C := same hB hC hP
    (fun x hx => huPB (Finset.mem_insert_of_mem hx))
    (fun x hx => hvPC (Finset.mem_insert_of_mem hx))
  subst C
  have hDE : D = E := same hD hE hQ
    (fun x hx => huQD (Finset.mem_insert_of_mem hx))
    (fun x hx => hvQE (Finset.mem_insert_of_mem hx))
  subst E
  have hpair : ({u, v} : Finset V).card = 2 := by simp [huv]
  have hpairB : ({u, v} : Finset V) ⊆ B := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact huPB (Finset.mem_insert_self _ _)
    · have : x = v := Finset.mem_singleton.mp hx
      subst x
      exact hvPC (Finset.mem_insert_self _ _)
  have hpairD : ({u, v} : Finset V) ⊆ D := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact huQD (Finset.mem_insert_self _ _)
    · have : x = v := Finset.mem_singleton.mp hx
      subst x
      exact hvQE (Finset.mem_insert_self _ _)
  have hBD : B = D := same hB hD hpair hpairB hpairD
  subst D
  apply hlocal B hB
  apply obstruction_of_commonLinkMatching
  exact ⟨u, v, huv, P, Q,
    ⟨hP, huP, hvP, Finset.mem_filter.mpr ⟨huPF, huPB⟩,
      Finset.mem_filter.mpr ⟨hvPF, hvPC⟩⟩,
    ⟨hQ, huQ, hvQ, Finset.mem_filter.mpr ⟨huQF, huQD⟩,
      Finset.mem_filter.mpr ⟨hvQF, hvQE⟩⟩, hPQ⟩

end
end Submissions.Erdos643BlockGluing.Main
