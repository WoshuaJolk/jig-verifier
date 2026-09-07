import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/- Classical family upper/lower bounds adapted from WoshuaJolk, Jig #16 statement2, artifact44a3b406-69fc-46cb-bc56-07617e08cb22. Product argument is standard prior art; no improved upper bound is claimed. -/
namespace Submissions.Erdos20SparseUniformity.Tensor

def IsSunflower {α : Type} (family : Set (Set α)) : Prop :=
  ∃ kernel : Set α, family.Pairwise fun left right => left ∩ right = kernel

lemma isSunflower_of_pairwise_disjoint {α : Type} {F : Set (Set α)}
    (hF : F.PairwiseDisjoint id) : IsSunflower F := by
  refine ⟨∅, ?_⟩
  intro A hA B hB hne
  exact Set.disjoint_iff_inter_eq_empty.mp (hF hA hB hne)


noncomputable def sunflowerThreshold (uniformity petals : ℕ) : ℕ :=
  sInf {bound : ℕ | ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = uniformity) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family,
        subfamily.ncard = petals ∧ IsSunflower subfamily}

def Forcing (n k bound : ℕ) : Prop :=
  ∀ {α : Type} (family : Set (Set α)),
    ((∀ member ∈ family, member.ncard = n) ∧ bound ≤ family.ncard) →
      ∃ subfamily ⊆ family, subfamily.ncard = k ∧ IsSunflower subfamily

section Matching
variable {α : Type}

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


lemma finset_erdos_rado {α : Type} (k : ℕ) (hk : 2 ≤ k) :
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
theorem erdos_rado_sunflower {α : Type}
    (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (F : Finset (Set α))
    (hcard : ∀ A ∈ F, A.ncard = n)
    (hsize : (k - 1) ^ n * n.factorial < F.card) :
    ∃ S ⊆ F, S.card = k ∧ IsSunflower (S : Set (Set α)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact finset_erdos_rado k hk m F hcard (by
    simpa only [Nat.succ_eq_add_one] using hsize)

theorem classical_bound_forcing (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    Forcing n k ((k - 1)^n * n.factorial + 1) := by
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


/-- The infimum in the canonical definition is attained: it is an actual
forcing threshold, not the default value of an empty infimum. -/
theorem threshold_mem (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    Forcing n k (sunflowerThreshold n k) := by
  change sInf {m | Forcing n k m} ∈ {m | Forcing n k m}
  apply Nat.sInf_mem (s := {m | Forcing n k m})
  exact ⟨(k - 1)^n * n.factorial + 1, @classical_bound_forcing n k hn hk⟩

/-- Classical Erdős–Rado upper and transversal lower bounds in the exact
canonical threshold convention. The lower bound is strict because a family
of `(k - 1)^n` members avoiding k petals exists. -/
theorem threshold_lower (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    (k - 1)^n < sunflowerThreshold n k := by
  classical
  obtain ⟨F, hFcard, hFuni, hFavoid⟩ := exists_transversal_family_no_sunflower n k hk
  by_contra hnot
  have hbound : sunflowerThreshold n k ≤ (F : Set (Set (Fin n × Fin (k - 1)))).ncard := by
    simpa [hFcard] using Nat.le_of_not_gt hnot
  obtain ⟨S, hSF, hScard, hSsun⟩ := threshold_mem n k hn hk
    (F : Set (Set (Fin n × Fin (k - 1)))) ⟨hFuni, hbound⟩
  have hSfin : S.Finite := F.finite_toSet.subset hSF
  let SF := hSfin.toFinset
  have hSFF : SF ⊆ F := by
    intro A hA
    exact hSF (by simpa [SF] using hA)
  have hSFcard : SF.card = k := by
    calc
      SF.card = S.ncard := (Set.ncard_eq_toFinset_card S hSfin).symm
      _ = k := hScard
  exact hFavoid SF hSFF hSFcard (by simpa [SF] using hSsun)

/-- Every uniform family avoiding k petals lies strictly below the least
forcing threshold. This also holds for infinite families under ncard's convention. -/
theorem card_lt_threshold (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    {α : Type} (F : Set (Set α))
    (huni : ∀ A ∈ F, A.ncard = n)
    (havoid : ∀ S ⊆ F, S.ncard = k → ¬ IsSunflower S) :
    F.ncard < sunflowerThreshold n k := by
  by_contra hnot
  obtain ⟨S, hSF, hScard, hSsun⟩ :=
    threshold_mem n k hn hk F ⟨huni, Nat.le_of_not_gt hnot⟩
  exact havoid S hSF hScard hSsun

/-- There is an extremal finite family of exactly threshold minus one
members. Existence is derived from the infimum, rather than assumed. -/
theorem exists_extremal (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) :
    ∃ (α : Type) (F : Set (Set α)), F.Finite ∧
      (∀ A ∈ F, A.ncard = n) ∧
      F.ncard = sunflowerThreshold n k - 1 ∧
      ∀ S ⊆ F, S.ncard = k → ¬ IsSunflower S := by
  have hpow : 0 < (k - 1)^n := pow_pos (by omega) _
  have hT : 1 < sunflowerThreshold n k := by
    have := threshold_lower n k hn hk
    omega
  have hnot : ¬ Forcing n k (sunflowerThreshold n k - 1) := by
    intro hforcing
    have hle : sunflowerThreshold n k ≤ sunflowerThreshold n k - 1 :=
      Nat.sInf_le hforcing
    omega
  simp only [Forcing, not_forall, not_exists, not_and] at hnot
  obtain ⟨α, F, ⟨huni, hsize⟩, havoid⟩ := hnot
  have hfinite : F.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hlt := card_lt_threshold n k hn hk F huni havoid
  exact ⟨α, F, hfinite, huni, by omega, havoid⟩

open Set

def join {α β : Type} (A : Set α) (B : Set β) : Set (α ⊕ β) :=
  Sum.inl '' A ∪ Sum.inr '' B

def product {α β : Type} (F : Set (Set α)) (G : Set (Set β)) : Set (Set (α ⊕ β)) :=
  (fun p : Set α × Set β => join p.1 p.2) '' (F ×ˢ G)

@[simp] theorem left_join {α β : Type} (A : Set α) (B : Set β) :
    Sum.inl ⁻¹' join A B = A := by
  simp [join, Set.preimage_image_eq A Sum.inl_injective]

@[simp] theorem right_join {α β : Type} (A : Set α) (B : Set β) :
    Sum.inr ⁻¹' join A B = B := by
  simp [join, Set.preimage_image_eq B Sum.inr_injective]

theorem join_injective {α β : Type} :
    Function.Injective (fun p : Set α × Set β => join p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · simpa using congrArg (fun s => Sum.inl ⁻¹' s) h
  · simpa using congrArg (fun s => Sum.inr ⁻¹' s) h

theorem product_ncard {α β : Type} (F : Set (Set α)) (G : Set (Set β)) :
    (product F G).ncard = F.ncard * G.ncard := by
  rw [product, join_injective.injOn.ncard_image, Set.ncard_prod]

theorem join_ncard {α β : Type} {A : Set α} {B : Set β}
    (hA : A.Finite) (hB : B.Finite) :
    (join A B).ncard = A.ncard + B.ncard := by
  rw [join, Set.ncard_union_eq Set.disjoint_image_inl_image_inr (hA.image _) (hB.image _),
    Set.ncard_image_of_injective A Sum.inl_injective,
    Set.ncard_image_of_injective B Sum.inr_injective]

theorem product_uniform {α β : Type} {F : Set (Set α)} {G : Set (Set β)}
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hF : ∀ A ∈ F, A.ncard = n) (hG : ∀ B ∈ G, B.ncard = m) :
    ∀ S ∈ product F G, S.ncard = n + m := by
  rintro S ⟨⟨A, B⟩, ⟨hA, hB⟩, rfl⟩
  rw [join_ncard (Set.finite_of_ncard_pos (by rw [hF A hA]; exact hn))
    (Set.finite_of_ncard_pos (by rw [hG B hB]; exact hm)), hF A hA, hG B hB]

/-- A projection with antichain image cannot have a nontrivial collision in an
indexed sunflower: once two projections coincide, all projections coincide. -/
theorem projection_injective_or_constant {ι α : Type} {H : Set ι} {f : ι → Set α}
    (hanti : ∀ i ∈ H, ∀ j ∈ H, f i ⊆ f j → f i = f j)
    (hsun : ∃ K, H.Pairwise fun i j => f i ∩ f j = K) :
    Set.InjOn f H ∨ ∃ K, ∀ i ∈ H, f i = K := by
  classical
  by_cases hinj : Set.InjOn f H
  · exact Or.inl hinj
  · right
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨i, hi, j, hj, heq, hne⟩ := hinj
    obtain ⟨K, hK⟩ := hsun
    have hiK : f i = K := by simpa [heq] using hK hi hj hne
    refine ⟨f i, ?_⟩
    intro l hl
    by_cases hli : l = i
    · exact congrArg f hli
    · apply Eq.symm
      apply hanti i hi l hl
      have hil := hK hi hl (Ne.symm hli)
      rw [← hiK] at hil
      exact fun x hx => (show x ∈ f i ∩ f l from hil.symm ▸ hx).2

theorem sunflower_preimage_image {α β : Type} {H : Set (Set β)}
    (hsun : IsSunflower H) (f : α → β) :
    IsSunflower ((fun S => f ⁻¹' S) '' H) := by
  obtain ⟨K, hK⟩ := hsun
  refine ⟨f ⁻¹' K, ?_⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
  have hab : A ≠ B := fun h => hne (congrArg (fun S => f ⁻¹' S) h)
  exact congrArg (fun S => f ⁻¹' S) (hK hA hB hab)

/-- The standard uniform tensor argument (e.g. Tang–Zhang, arXiv:2512.20055,
footnote to (1.2)) needs only one factor to be an antichain. -/
theorem product_no_sunflower_of_antichain {α β : Type}
    {F : Set (Set α)} {G : Set (Set β)} {r : ℕ}
    (hFA : ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B)
    (hF : ¬ ∃ H ⊆ F, H.ncard = r ∧ IsSunflower H)
    (hG : ¬ ∃ H ⊆ G, H.ncard = r ∧ IsSunflower H) :
    ¬ ∃ H ⊆ product F G, H.ncard = r ∧ IsSunflower H := by
  rintro ⟨H, hH, hcard, hsun⟩
  let left : Set (α ⊕ β) → Set α := fun S => Sum.inl ⁻¹' S
  let right : Set (α ⊕ β) → Set β := fun S => Sum.inr ⁻¹' S
  have hleft : ∀ S ∈ H, left S ∈ F := by
    intro S hS
    obtain ⟨⟨A, B⟩, ⟨hA, _⟩, rfl⟩ := hH hS
    simpa [left] using hA
  have hright : ∀ S ∈ H, right S ∈ G := by
    intro S hS
    obtain ⟨⟨A, B⟩, ⟨_, hB⟩, rfl⟩ := hH hS
    simpa [right] using hB
  have hproj : ∃ K, H.Pairwise fun S T => left S ∩ left T = K := by
    obtain ⟨K, hK⟩ := hsun
    refine ⟨Sum.inl ⁻¹' K, ?_⟩
    intro S hS T hT hne
    exact congrArg (fun U => Sum.inl ⁻¹' U) (hK hS hT hne)
  rcases projection_injective_or_constant
    (fun S hS T hT hsub => hFA _ (hleft S hS) _ (hleft T hT) hsub) hproj
    with hinj | ⟨K, hconst⟩
  · apply hF
    refine ⟨left '' H, ?_, ?_, sunflower_preimage_image hsun Sum.inl⟩
    · rintro _ ⟨S, hS, rfl⟩
      exact hleft S hS
    · exact hinj.ncard_image.trans hcard
  · have hinj : Set.InjOn right H := by
      intro S hS T hT heq
      have hleq : left S = left T := (hconst S hS).trans (hconst T hT).symm
      ext x
      cases x with
      | inl a => exact Set.ext_iff.mp hleq a
      | inr b => exact Set.ext_iff.mp heq b
    apply hG
    refine ⟨right '' H, ?_, ?_, sunflower_preimage_image hsun Sum.inr⟩
    · rintro _ ⟨S, hS, rfl⟩
      exact hright S hS
    · exact hinj.ncard_image.trans hcard

theorem product_no_sunflower {α β : Type}
    {F : Set (Set α)} {G : Set (Set β)} {n m r : ℕ}
    (hn : 0 < n) (_hm : 0 < m)
    (hFU : ∀ A ∈ F, A.ncard = n) (_hGU : ∀ B ∈ G, B.ncard = m)
    (hF : ¬ ∃ H ⊆ F, H.ncard = r ∧ IsSunflower H)
    (hG : ¬ ∃ H ⊆ G, H.ncard = r ∧ IsSunflower H) :
    ¬ ∃ H ⊆ product F G, H.ncard = r ∧ IsSunflower H := by
  apply product_no_sunflower_of_antichain ?_ hF hG
  intro A hA B hB hsub
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hFU A hA, hFU B hB])
    (Set.finite_of_ncard_pos (by rw [hFU B hB]; exact hn))


/-- Power amplification for a positive supermultiplicative sequence. -/
lemma power_le (a : ℕ → ℕ)
    (hmul : ∀ i j, 0 < i → 0 < j → a i * a j ≤ a (i + j))
    {k q : ℕ} (hk : 0 < k) (hq : 0 < q) :
    a k ^ q ≤ a (k * q) := by
  induction q with
  | zero => omega
  | succ q ih =>
    by_cases hq0 : q = 0
    · subst q
      simp
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      calc
        a k ^ (q + 1) = a k ^ q * a k := pow_succ _ _
        _ ≤ a (k * q) * a k := Nat.mul_le_mul_right _ (ih hqpos)
        _ ≤ a (k * q + k) := hmul _ _ (Nat.mul_pos hk hqpos) hk
        _ = a (k * (q + 1)) := by rw [Nat.mul_add, Nat.mul_one]

/-- Unboundedly many exponential upper bounds suffice for an exponential bound
at every positive index. The explicit squared base avoids analytic limits. -/
theorem sparse_implies_full (a : ℕ → ℕ)
    (hpos : ∀ i, 0 < i → 1 ≤ a i)
    (hmul : ∀ i j, 0 < i → 0 < j → a i * a j ≤ a (i + j))
    (C : ℕ) (hsparse : ∀ N, ∃ n, N ≤ n ∧ a n < C ^ n) :
    ∀ k, 0 < k → a k < (C * C) ^ k := by
  intro k hk
  obtain ⟨n, hn, hb⟩ := hsparse (2*k)
  have hnpos : 0 < n := by omega
  have hC : 0 < C := by
    by_contra h
    have : C = 0 := by omega
    simp [this, Nat.ne_of_gt hnpos] at hb
  let q := n / k
  have hq : 0 < q := Nat.div_pos (by omega) hk
  have hd : k * q + n % k = n := by
    simpa [q, Nat.mul_comm] using Nat.div_add_mod n k
  have hr : n % k < k := Nat.mod_lt _ hk
  have hkp : 0 < k*q := Nat.mul_pos hk hq
  have hkn : k ≤ k*q := by simpa using Nat.mul_le_mul_left k hq
  have htwice : n ≤ 2 * (k*q) := by omega
  have hamp : a k ^ q ≤ a n := by
    have hpow := power_le a hmul hk hq
    by_cases hz : n % k = 0
    · have : k*q = n := by omega
      simpa [this] using hpow
    · calc
        a k ^ q ≤ a (k*q) := hpow
        _ ≤ a (k*q) * a (n % k) := by
          simpa using Nat.mul_le_mul_left (a (k*q)) (hpos _ (Nat.pos_of_ne_zero hz))
        _ ≤ a (k*q + n % k) := hmul _ _ hkp (Nat.pos_of_ne_zero hz)
        _ = a n := congrArg a hd
  by_contra! hlarge
  have hlower : C^n ≤ a k ^ q := by
    calc
      C^n ≤ C^(2*(k*q)) := Nat.pow_le_pow_right hC htwice
      _ = ((C*C)^k)^q := by simp [mul_pow, ← pow_mul]; ring
      _ ≤ a k ^ q := Nat.pow_le_pow_left hlarge q
  exact (not_lt_of_ge (hlower.trans hamp)) hb

/-- The exact extremal size is supermultiplicative under disjoint products. -/
theorem threshold_supermultiplicative (n m r : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hr : 2 ≤ r) :
    (sunflowerThreshold n r - 1) * (sunflowerThreshold m r - 1) ≤
      sunflowerThreshold (n + m) r - 1 := by
  obtain ⟨α, F, _, hFU, hFC, hF⟩ := exists_extremal n r hn hr
  obtain ⟨β, G, _, hGU, hGC, hG⟩ := exists_extremal m r hm hr
  have hav : ∀ S ⊆ product F G, S.ncard = r → ¬ IsSunflower S := by
    intro S hS hc hs
    exact product_no_sunflower hn hm hFU hGU
      (by rintro ⟨T, hT, hc, hs⟩; exact hF T hT hc hs)
      (by rintro ⟨T, hT, hc, hs⟩; exact hG T hT hc hs) ⟨S, hS, hc, hs⟩
  have hb := card_lt_threshold (n + m) r (by omega) hr
    (product F G) (product_uniform hn hm hFU hGU) hav
  rw [product_ncard, hFC, hGC] at hb
  omega

/-- For any fixed r, unboundedly many uniformities with the same exponential
base already suffice. The bound at all positive uniformities has base C²+1. -/
theorem sparse_threshold_bound (r C : ℕ) (hr : 2 ≤ r)
    (hsparse : ∀ N, ∃ n, N ≤ n ∧ sunflowerThreshold n r < C^n) :
    ∀ n, 0 < n → sunflowerThreshold n r < (C*C+1)^n := by
  let a : ℕ → ℕ := fun n => sunflowerThreshold n r - 1
  have hpos : ∀ n, 0 < n → 1 ≤ a n := by
    intro n hn
    have := threshold_lower n r hn hr
    have hp : 0 < (r-1)^n := pow_pos (by omega) _
    dsimp [a]
    omega
  have hmul : ∀ i j, 0 < i → 0 < j → a i * a j ≤ a (i+j) := by
    intro i j hi hj
    exact threshold_supermultiplicative i j r hi hj hr
  have hs : ∀ N, ∃ n, N ≤ n ∧ a n < C^n := by
    intro N
    obtain ⟨n, hn, hb⟩ := hsparse N
    exact ⟨n, hn, lt_of_le_of_lt (Nat.sub_le _ _) hb⟩
  have hb := sparse_implies_full a hpos hmul C hs
  intro n hn
  have hsmall := hb n hn
  have hT : sunflowerThreshold n r ≤ (C*C)^n := by
    dsimp [a] at hsmall
    omega
  exact lt_of_le_of_lt hT (Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt hn))

theorem sparse_iff_full (r : ℕ) (hr : 2 ≤ r) :
    (∃ C : ℕ, ∀ n : ℕ, 0 < n → sunflowerThreshold n r < C^n) ↔
      (∃ C : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ sunflowerThreshold n r < C^n) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun N => ⟨N+1, by omega, hC (N+1) (by omega)⟩⟩
  · rintro ⟨C, hC⟩
    exact ⟨C*C+1, sparse_threshold_bound r C hr hC⟩
/-- Bound one genuinely forces zero or one petals, for every uniformity. -/
theorem small_petals_bound (n k : ℕ) (hk : k ≤ 1) :
    sunflowerThreshold n k ≤ 1 := by
  apply Nat.sInf_le
  intro α family h
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with rfl | rfl
  · refine ⟨∅, Set.empty_subset _, by simp, ∅, ?_⟩
    simp
  · obtain ⟨A, hA⟩ := Set.nonempty_of_ncard_ne_zero (s := family) (by omega)
    refine ⟨{A}, Set.singleton_subset_iff.mpr hA, by simp, ∅, ?_⟩
    simp

theorem small_petals_exponential (n k : ℕ) (hn : 0 < n) (hk : k ≤ 1) :
    sunflowerThreshold n k < 2 ^ n := by
  apply lt_of_le_of_lt (small_petals_bound n k hk)
  exact one_lt_pow₀ (by decide) (Nat.ne_of_gt hn)

abbrev exponential : Prop :=
  ∃ constants : ℕ → ℕ, ∀ uniformity petals : ℕ, uniformity > 0 →
    sunflowerThreshold uniformity petals < (constants petals) ^ uniformity

abbrev cofinal : Prop :=
  ∃ constants : ℕ → ℕ, ∀ petals cutoff : ℕ, ∃ uniformity : ℕ,
    cutoff ≤ uniformity ∧
      sunflowerThreshold uniformity petals < (constants petals) ^ uniformity

/-- The full ordinary sunflower conjecture is equivalent to finding a fixed
exponential base at arbitrarily large uniformities, separately for each petal count. -/
theorem proof : exponential ↔ cofinal := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro petals cutoff
    exact ⟨cutoff+1, by omega, hC (cutoff+1) petals (by omega)⟩
  · rintro ⟨C, hC⟩
    refine ⟨fun p => C p * C p + 2, ?_⟩
    intro n p hn
    by_cases hp : p ≤ 1
    · exact lt_of_lt_of_le (small_petals_exponential n p hn hp)
        (Nat.pow_le_pow_left (by omega : 2 ≤ C p * C p + 2) n)
    · exact lt_of_lt_of_le (sparse_threshold_bound p (C p) (by omega) (hC p) n hn)
        (Nat.pow_le_pow_left (by omega : C p * C p + 1 ≤ C p * C p + 2) n)

#print axioms proof
#print axioms threshold_supermultiplicative
#print axioms exists_extremal

end Submissions.Erdos20SparseUniformity.Tensor
