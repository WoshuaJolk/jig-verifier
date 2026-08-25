import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

def IsSunflower {α : Type*} (F : Set (Set α)) : Prop :=
  ∃ C, ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ≠ B → A ∩ B = C

lemma isSunflower_of_pairwise_disjoint {α : Type*} {F : Set (Set α)}
    (hF : F.PairwiseDisjoint id) : IsSunflower F := by
  refine ⟨∅, ?_⟩
  intro A hA B hB hne
  exact Set.disjoint_iff_inter_eq_empty.mp (hF hA hB hne)

namespace Submissions.Erdos20FactorialUpper.Classical

noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

section Matching
variable {α : Type*}

lemma exists_maximal_disjoint (F : Finset (Set α)) :
    ∃ D ⊆ F, (D : Set (Set α)).PairwiseDisjoint id ∧
      ∀ A ∈ F, A ∉ D → ∃ B ∈ D, ¬ Disjoint A B := by
  classical
  let C : Finset (Finset (Set α)) :=
    F.powerset.filter fun D => (D : Set (Set α)).PairwiseDisjoint id
  have hC : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C]
  obtain ⟨D, hDmax⟩ := C.exists_maximal hC
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hDmax
  refine ⟨D, hDmax.1.1, hDmax.1.2, ?_⟩
  intro A hAF hAD
  by_contra! h
  have hins : insert A D ⊆ F ∧
      ((insert A D : Finset (Set α)) : Set (Set α)).PairwiseDisjoint id := by
    refine ⟨Finset.insert_subset hAF hDmax.1.1, ?_⟩
    rw [Finset.coe_insert]
    exact hDmax.1.2.insert (by
      intro B hBD hne
      exact h B hBD)
  exact hDmax.not_gt hins (Finset.ssubset_insert hAD)

end Matching
end Submissions.Erdos20FactorialUpper.Classical

namespace Submissions.Erdos20FactorialUpper.Classical

lemma finset_erdos_rado {α : Type*} (k : ℕ) (hk : 2 ≤ k) :
    ∀ n (F : Finset (Set α)),
      (∀ A ∈ F, A.ncard = n + 1) →
      (k - 1) ^ (n + 1) * (n + 1).factorial < F.card →
      ∃ S ⊆ F, S.card = k ∧ IsSunflower (S : Set (Set α)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro F huni hcard
      have hkle : k ≤ F.card := by
        norm_num at hcard ⊢
        omega
      obtain ⟨S, hSF, hSc⟩ := Finset.exists_subset_card_eq hkle
      refine ⟨S, hSF, hSc, ?_⟩
      refine ⟨∅, ?_⟩
      intro A hA B hB hne
      have hAs : ∃ a, A = {a} := Set.ncard_eq_one.mp (by simpa using huni A (hSF hA))
      have hBs : ∃ b, B = {b} := Set.ncard_eq_one.mp (by simpa using huni B (hSF hB))
      obtain ⟨a, rfl⟩ := hAs
      obtain ⟨b, rfl⟩ := hBs
      simp_all
  | succ n ih =>
      intro F huni hcard
      obtain ⟨D, hDF, hDdis, hDmax⟩ := exists_maximal_disjoint F
      by_cases hlarge : k ≤ D.card
      · obtain ⟨S, hSD, hSc⟩ := Finset.exists_subset_card_eq hlarge
        exact ⟨S, hSD.trans hDF, hSc,
          isSunflower_of_pairwise_disjoint (fun A hA B hB hne => hDdis (hSD hA) (hSD hB) hne)⟩
      · have hDcard : D.card ≤ k - 1 := by omega
        have hfinite : ∀ (A : Set α), A ∈ F → A.Finite := by
          intro A hAF
          apply Set.finite_of_ncard_ne_zero
          rw [huni A hAF]
          omega
        let ft : Set α → Finset α := fun A => if h : A ∈ F then (hfinite A h).toFinset else ∅
        let U : Finset α := D.biUnion ft
        have hUcard : U.card ≤ (k - 1) * (n + 2) := by
          calc
            U.card ≤ D.card * (n + 2) := Finset.card_biUnion_le_card_mul D _ _ (by
              intro A hAD
              calc
                (ft A).card = A.ncard := by
                  rw [show ft A = (hfinite A (hDF hAD)).toFinset by simp [ft, hDF hAD]]
                  exact (Set.ncard_eq_toFinset_card A (hfinite A (hDF hAD))).symm
                _ = n + 2 := by simpa [Nat.add_assoc] using huni A (hDF hAD)
                _ ≤ n + 2 := le_rfl)
            _ ≤ (k - 1) * (n + 2) := Nat.mul_le_mul_right _ hDcard
        have hit : ∀ A ∈ F, ∃ x ∈ U, x ∈ A := by
          intro A hAF
          have hnemp : A.Nonempty := (Set.ncard_pos (hs := hfinite A hAF)).mp (by rw [huni A hAF]; omega)
          by_cases hAD : A ∈ D
          · obtain ⟨x, hx⟩ := hnemp
            refine ⟨x, ?_, hx⟩
            simp only [U, Finset.mem_biUnion]
            exact ⟨A, hAD, by simp [ft, hAF, hx]⟩
          · obtain ⟨B, hBD, hn⟩ := hDmax A hAF hAD
            obtain ⟨x, hxA, hxB⟩ := Set.not_disjoint_iff.mp hn
            refine ⟨x, ?_, hxA⟩
            simp only [U, Finset.mem_biUnion]
            exact ⟨B, hBD, by simp [ft, hDF hBD, hxB]⟩
        let p : ↥(F : Set (Set α)) → α := fun A => Classical.choose (hit A.1 A.2)
        have hpU : ∀ A : ↥(F : Set (Set α)), p A ∈ U := fun A => (Classical.choose_spec (hit A.1 A.2)).1
        have hpA : ∀ A : ↥(F : Set (Set α)), p A ∈ A.1 := fun A => (Classical.choose_spec (hit A.1 A.2)).2
        have hmul : U.card * ((k - 1) ^ (n + 1) * (n + 1).factorial) < F.card := by
          calc
            U.card * ((k - 1) ^ (n + 1) * (n + 1).factorial)
                ≤ ((k - 1) * (n + 2)) * ((k - 1) ^ (n + 1) * (n + 1).factorial) :=
                  Nat.mul_le_mul_right _ hUcard
            _ = (k - 1) ^ (n + 2) * (n + 2).factorial := by
                  simp only [Nat.factorial_succ, pow_succ]
                  ring
            _ < F.card := hcard
        have hattach : F.attach.card = F.card := Finset.card_attach
        obtain ⟨x, hxU, hxfib⟩ :=
          Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
            (s := F.attach) (t := U) (f := p) (fun A _ => hpU A) (by simpa [hattach] using hmul)
        let H := F.attach.filter fun A => p A = x
        have hHcard : (k - 1) ^ (n + 1) * (n + 1).factorial < H.card := by simpa [H] using hxfib
        let del : (A : Set α) → Set α := fun A => A \ {x}
        let G : Finset (Set α) := H.image fun A => del A.1
        have hdelinj : Set.InjOn (fun A : ↥(F : Set (Set α)) => del A.1) (H : Set _) := by
          intro A hAH B hBH heq
          apply Subtype.ext
          have hpxA : p A = x := (Finset.mem_filter.mp hAH).2
          have hpxB : p B = x := (Finset.mem_filter.mp hBH).2
          have hxA : x ∈ A.1 := by simpa [hpxA] using hpA A
          have hxB : x ∈ B.1 := by simpa [hpxB] using hpA B
          apply Set.ext
          intro y
          by_cases hy : y = x
          · subst y; simp [hxA, hxB]
          · simpa [del, hy] using Set.ext_iff.mp heq y
        have hGcard : G.card = H.card := Finset.card_image_iff.mpr (by
          intro A hAH B hBH heq
          exact hdelinj hAH hBH heq)
        have hGuni : ∀ C ∈ G, C.ncard = n + 1 := by
          intro C hCG
          simp only [G, Finset.mem_image] at hCG
          obtain ⟨A, hAH, rfl⟩ := hCG
          have hpxA : p A = x := (Finset.mem_filter.mp hAH).2
          have hxA : x ∈ A.1 := by simpa [hpxA] using hpA A
          have := Set.ncard_sdiff_singleton_add_one hxA (hfinite A.1 A.2)
          rw [huni A.1 A.2] at this
          exact Nat.add_right_cancel this
        obtain ⟨T, hTG, hTc, hTsun⟩ := ih G hGuni (by simpa [hGcard] using hHcard)
        let S : Finset (Set α) := T.image fun C => insert x C
        have hSinj : Set.InjOn (fun C : Set α => insert x C) (T : Set _) := by
          intro C hC E hE heq
          have hxC : x ∉ C := by
            obtain ⟨A, hAH, rfl⟩ := Finset.mem_image.mp (hTG hC)
            simp [del]
          have hxE : x ∉ E := by
            obtain ⟨A, hAH, rfl⟩ := Finset.mem_image.mp (hTG hE)
            simp [del]
          apply Set.ext
          intro y
          have hy := Set.ext_iff.mp heq y
          by_cases hyx : y = x
          · subst y; simp [hxC, hxE]
          · simpa [hyx] using hy
        refine ⟨S, ?_, ?_, ?_⟩
        · intro A hAS
          obtain ⟨C, hCT, rfl⟩ := Finset.mem_image.mp hAS
          obtain ⟨B, hBH, rfl⟩ := Finset.mem_image.mp (hTG hCT)
          have hpx : p B = x := (Finset.mem_filter.mp hBH).2
          have hxB : x ∈ B.1 := by simpa [hpx] using hpA B
          have : insert x (B.1 \ {x}) = B.1 := by ext y; by_cases hy : y = x <;> simp [hy, hxB]
          rw [this]
          exact B.2
        · simpa [S, Finset.card_image_iff.mpr hSinj] using hTc
        · obtain ⟨C, hC⟩ := hTsun
          refine ⟨insert x C, ?_⟩
          intro A hA B hB hne
          obtain ⟨A', hA'T, rfl⟩ := Finset.mem_image.mp hA
          obtain ⟨B', hB'T, rfl⟩ := Finset.mem_image.mp hB
          have hne' : A' ≠ B' := fun e => hne (congrArg (insert x) e)
          have hinter : insert x A' ∩ insert x B' = insert x (A' ∩ B') := by
            ext y
            by_cases hy : y = x <;> simp [hy]
          rw [hinter, hC hA'T hB'T hne']

/-- The non-vacuous, reusable family form of the classical Erdős--Rado bound. -/
theorem erdos_rado_sunflower {α : Type*}
    (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (F : Finset (Set α))
    (hcard : ∀ A ∈ F, A.ncard = n)
    (hsize : (k - 1) ^ n * n.factorial < F.card) :
    ∃ S ⊆ F, S.card = k ∧ IsSunflower (S : Set (Set α)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact finset_erdos_rado k hk m F hcard (by
    simpa only [Nat.succ_eq_add_one] using hsize)

theorem erdos_20.variants.erdos_rado_bound :
    ∀ n k, n > 0 → 2 ≤ k → f n k ≤ (k-1)^n * n.factorial + 1 := by
  intro n k hn hk
  apply Nat.sInf_le
  intro α F hF
  have hFfin : F.Finite := Set.finite_of_ncard_ne_zero (by omega)
  let FF := hFfin.toFinset
  obtain ⟨S, hSFF, hSc, hSsun⟩ := erdos_rado_sunflower n k hn hk FF (by
    intro A hAFF
    exact hF.1 A (by simpa [FF] using hAFF)) (by
    rw [← Set.ncard_eq_toFinset_card F hFfin]
    exact Nat.lt_of_succ_le hF.2)
  exact ⟨S, by
    intro A hAS
    have : A ∈ FF := hSFF hAS
    simpa [FF] using this, by simpa using hSc, hSsun⟩

/-- The classical transversal construction giving the factorial bound's standard lower side. -/
theorem exists_transversal_family_no_sunflower (n k : ℕ) (hk : 2 ≤ k) :
    ∃ F : Finset (Set (Fin n × Fin (k - 1))),
      F.card = (k - 1) ^ n ∧
      (∀ A ∈ F, A.ncard = n) ∧
      ∀ S : Finset (Set (Fin n × Fin (k - 1))),
        S ⊆ F → S.card = k → ¬ IsSunflower (S : Set (Set (Fin n × Fin (k - 1))) ) := by
  classical
  let graph : (Fin n → Fin (k - 1)) → Set (Fin n × Fin (k - 1)) :=
    fun f => Set.range fun i => (i, f i)
  have hgraph_inj : Function.Injective graph := by
    intro f g hfg
    funext i
    have hi : (i, f i) ∈ graph g := by
      rw [← hfg]
      exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hi
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact congrArg Prod.snd hj.symm
  let F : Finset (Set (Fin n × Fin (k - 1))) := Finset.univ.image graph
  have hFcard : F.card = (k - 1) ^ n := by
    have hi : (Finset.univ.image graph).card = Finset.univ.card :=
      Finset.card_image_iff.mpr (by
        intro f hf g hg hfg
        exact hgraph_inj hfg)
    rw [show F = Finset.univ.image graph from rfl, hi]
    simp
  have hFuni : ∀ A ∈ F, A.ncard = n := by
    intro A hAF
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hAF
    change (Set.range fun i => (i, f i)).ncard = n
    rw [Set.ncard_range_of_injective]
    · simp
    · intro i j hij
      exact congrArg Prod.fst hij
  refine ⟨F, hFcard, hFuni, ?_⟩
  intro S hSF hScard hsun
  obtain ⟨C, hC⟩ := hsun
  have hdecode : ∀ A : ↥S, ∃ f : Fin n → Fin (k - 1), graph f = A.1 := by
    intro A
    have hAF : A.1 ∈ F := hSF A.2
    obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hAF
    exact ⟨f, hf⟩
  choose decode hdecode_graph using hdecode
  have hdecode_inj : Function.Injective decode := by
    intro A B hab
    apply Subtype.ext
    rw [← hdecode_graph A, ← hdecode_graph B, hab]
  have hS_nontrivial : 2 ≤ S.card := by omega
  obtain ⟨A, hAS⟩ := S.card_pos.mp (by omega : 0 < S.card)
  let A0 : ↥S := ⟨A, hAS⟩
  have hall : ∀ B : ↥S, B = A0 := by
    intro B
    by_contra hBA
    have hsets_ne : B.1 ≠ A0.1 := by
      intro heq
      apply hBA
      exact Subtype.ext heq
    apply hsets_ne
    apply Set.ext
    intro p
    rcases p with ⟨i, x⟩
    have hp_graph_B : (i, x) ∈ graph (decode B) ↔ x = decode B i := by
      constructor
      · rintro ⟨j, hj⟩
        have hji : j = i := congrArg Prod.fst hj
        subst j
        exact (congrArg Prod.snd hj).symm
      · intro hx
        subst x
        exact ⟨i, rfl⟩
    have hp_graph_A : (i, x) ∈ graph (decode A0) ↔ x = decode A0 i := by
      constructor
      · rintro ⟨j, hj⟩
        have hji : j = i := congrArg Prod.fst hj
        subst j
        exact (congrArg Prod.snd hj).symm
      · intro hx
        subst x
        exact ⟨i, rfl⟩
    have hcollision : ∃ X Y : ↥S, X ≠ Y ∧ decode X i = decode Y i := by
      by_contra h
      push Not at h
      have hinj : Function.Injective (fun X : ↥S => decode X i) := by
        intro X Y heq
        by_contra hXY
        exact h X Y hXY heq
      have hc := Fintype.card_le_of_injective (f := fun X : ↥S => decode X i) hinj
      simp [hScard] at hc
      omega
    obtain ⟨X, Y, hXY, hval⟩ := hcollision
    have hpointX : (i, decode X i) ∈ X.1 := by
      rw [← hdecode_graph X]
      exact ⟨i, rfl⟩
    have hpointY : (i, decode X i) ∈ Y.1 := by
      rw [← hdecode_graph Y]
      exact ⟨i, Prod.ext rfl hval.symm⟩
    have hpointC : (i, decode X i) ∈ C := by
      rw [← hC X.2 Y.2 (fun e => hXY (Subtype.ext e))]
      exact ⟨hpointX, hpointY⟩
    have hBAinter : B.1 ∩ A0.1 = C := hC B.2 A0.2 hsets_ne
    have hpointBA : (i, decode X i) ∈ B.1 ∩ A0.1 := by
      rw [hBAinter]
      exact hpointC
    have hvalueBA : decode B i = decode A0 i := by
      have hbmem : (i, decode X i) ∈ graph (decode B) := by
        rw [hdecode_graph B]
        exact hpointBA.1
      obtain ⟨j, hj⟩ := hbmem
      have hji : j = i := congrArg Prod.fst hj
      subst j
      have hb : decode B i = decode X i := congrArg Prod.snd hj
      have hamem : (i, decode X i) ∈ graph (decode A0) := by
        rw [hdecode_graph A0]
        exact hpointBA.2
      obtain ⟨j, hj⟩ := hamem
      have hji : j = i := congrArg Prod.fst hj
      subst j
      have ha : decode A0 i = decode X i := congrArg Prod.snd hj
      exact hb.trans ha.symm
    rw [← hdecode_graph B, ← hdecode_graph A0]
    calc
      (i, x) ∈ graph (decode B) ↔ x = decode B i := hp_graph_B
      _ ↔ x = decode A0 i := by rw [hvalueBA]
      _ ↔ (i, x) ∈ graph (decode A0) := hp_graph_A.symm
  have hsubsingleton : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro X hX Y hY
    have hX0 := hall (⟨X, hX⟩ : ↥S)
    have hY0 := hall (⟨Y, hY⟩ : ↥S)
    exact congrArg Subtype.val (hX0.trans hY0.symm)
  omega

end Submissions.Erdos20FactorialUpper.Classical
