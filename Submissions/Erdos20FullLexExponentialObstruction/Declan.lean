import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace Submissions.Erdos20FullLexExponentialObstruction.Declan

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {α : Type*} [DecidableEq α]

def move (i j : α) (A : Finset α) : Finset α :=
  if i ∉ A ∧ j ∈ A then insert i (A.erase j) else A

def shiftMember (i j : α) (F : Finset (Finset α)) (A : Finset α) : Finset α :=
  if i ∉ A ∧ j ∈ A ∧ insert i (A.erase j) ∉ F then insert i (A.erase j) else A

def shift (i j : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.image (shiftMember i j F)

theorem move_of_mem (i j : α) (A : Finset α) (h : i ∈ A) : move i j A = A := by
  simp [move, h]

theorem mem_move (i j x : α) (A : Finset α) (hx : x ∈ A) (hxj : x ≠ j) :
    x ∈ move i j A := by
  unfold move
  split_ifs <;> simp_all

theorem move_card (i j : α) (A : Finset α) : (move i j A).card = A.card := by
  unfold move
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [h.1]), Finset.card_erase_of_mem h.2]
    have := Finset.card_pos.mpr ⟨j, h.2⟩
    omega
  · rfl

theorem target_mem_move (i j : α) (A : Finset α) :
    i ∈ move i j A ↔ i ∈ A ∨ j ∈ A := by
  unfold move
  split_ifs with h <;> simp_all <;> aesop

def moveList (i : α) (L : List α) (A : Finset α) :=
  L.foldl (fun B j => move i j B) A

theorem moveList_of_mem (i : α) (L : List α) (A : Finset α) (h : i ∈ A) :
    moveList i L A = A := by
  induction L generalizing A with
  | nil => rfl
  | cons j L ih =>
      change moveList i L (move i j A) = A
      rw [move_of_mem i j A h, ih A h]

theorem target_mem_moveList (i : α) (L : List α) (A : Finset α) :
    i ∈ moveList i L A ↔ i ∈ A ∨ ∃ j ∈ L, j ∈ A := by
  induction L generalizing A with
  | nil => simp [moveList]
  | cons j L ih =>
      by_cases hi : i ∈ A
      · simp [moveList_of_mem i _ A hi, hi]
      by_cases hj : j ∈ A
      · have hm : i ∈ move i j A := (target_mem_move i j A).mpr (Or.inr hj)
        change i ∈ moveList i L (move i j A) ↔ _
        rw [moveList_of_mem i L _ hm]
        simp [hm, hj]
      · have hm : move i j A = A := by simp [move, hj]
        change i ∈ moveList i L (move i j A) ↔ _
        rw [hm]
        simpa [hi, hj] using ih A

theorem moveList_card (i : α) (L : List α) (A : Finset α) :
    (moveList i L A).card = A.card := by
  induction L generalizing A with
  | nil => rfl
  | cons j L ih =>
      change (moveList i L (move i j A)).card = A.card
      rw [ih, move_card]

theorem mem_moveList (i x : α) (L : List α) (A : Finset α)
    (hx : x ∈ A) (hL : x ∉ L) : x ∈ moveList i L A := by
  induction L generalizing A with
  | nil => exact hx
  | cons j L ih =>
      have hs : x ≠ j ∧ x ∉ L := by simpa using hL
      exact ih (move i j A) (mem_move i j x A hx hs.1) hs.2

theorem move_subset {i j : α} {A U : Finset α} (hA : A ⊆ U) (hi : i ∈ U) :
    move i j A ⊆ U := by
  unfold move
  split_ifs
  · exact Finset.insert_subset hi (Finset.Subset.trans (Finset.erase_subset _ _) hA)
  · exact hA

theorem moveList_subset (i : α) (L : List α) (A U : Finset α)
    (hA : A ⊆ U) (hi : i ∈ U) : moveList i L A ⊆ U := by
  induction L generalizing A with
  | nil => exact hA
  | cons j L ih => exact ih _ (move_subset hA hi)

def tagged (B : α → Finset ℕ) (w : α) : Finset (ℕ ⊕ α) :=
  ((B w).image Sum.inl) ∪ {Sum.inr w}

def taggedFamily [Fintype α] (B : α → Finset ℕ) : Finset (Finset (ℕ ⊕ α)) :=
  Finset.univ.image (tagged B)

@[simp] theorem inl_mem_tagged (B : α → Finset ℕ) (w : α) (i : ℕ) :
    Sum.inl i ∈ tagged B w ↔ i ∈ B w := by simp [tagged]

@[simp] theorem inr_mem_tagged (B : α → Finset ℕ) (w v : α) :
    Sum.inr v ∈ tagged B w ↔ v = w := by simp [tagged, eq_comm]

theorem tagged_injective (B : α → Finset ℕ) : Function.Injective (tagged B) := by
  intro w v h
  have hw : Sum.inr w ∈ tagged B w := by simp
  rw [h] at hw
  simpa using hw

theorem tagged_card (B : α → Finset ℕ) (w : α) : (tagged B w).card = (B w).card + 1 := by
  rw [tagged, Finset.card_union_of_disjoint]
  · simp [Finset.card_image_of_injective _ Sum.inl_injective]
  · simp [Finset.disjoint_left]

theorem taggedFamily_card [Fintype α] (B : α → Finset ℕ) :
    (taggedFamily B).card = Fintype.card α := by
  simp [taggedFamily, Finset.card_image_of_injective _ (tagged_injective B)]

theorem replace_tagged (B : α → Finset ℕ) (w : α) (i j : ℕ) :
    insert (Sum.inl i) ((tagged B w).erase (Sum.inl j)) =
      tagged (fun v => insert i ((B v).erase j)) w := by
  ext x
  cases x <;> simp [tagged]

theorem shiftMember_tagged [Fintype α] (B : α → Finset ℕ) (w : α) (i j : ℕ) :
    shiftMember (Sum.inl i) (Sum.inl j) (taggedFamily B) (tagged B w) =
      tagged (fun v => move i j (B v)) w := by
  by_cases hi : i ∈ B w
  · simp [shiftMember, hi, tagged, move, hi]
  by_cases hj : j ∈ B w
  · have hn : insert (Sum.inl i) ((tagged B w).erase (Sum.inl j)) ∉ taggedFamily B := by
      rw [replace_tagged]
      intro h
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
      have ht : Sum.inr w ∈ tagged B v := by rw [hv]; simp
      have hvw : w = v := by simpa using ht
      subst v
      have ht : Sum.inl i ∈ tagged B w := by rw [hv]; simp
      exact hi (by simpa using ht)
    simp only [shiftMember, inl_mem_tagged, hi, not_false_eq_true, hj, hn, and_self, ↓reduceIte]
    rw [replace_tagged]
    simp [tagged, move, hi, hj]
  · simp [shiftMember, hi, hj, tagged, move, hi, hj]

theorem shift_tagged [Fintype α] (B : α → Finset ℕ) (i j : ℕ) :
    shift (Sum.inl i) (Sum.inl j) (taggedFamily B) =
      taggedFamily (fun w => move i j (B w)) := by
  simp only [shift, taggedFamily, Finset.image_image]
  congr 1
  funext w
  exact shiftMember_tagged B w i j


def bodySources (m i : ℕ) : List ℕ := (List.range m).filter (i < ·)
def bodySweep (m i : ℕ) (A : Finset ℕ) := moveList i (bodySources m i) A

@[simp] theorem mem_bodySources (m i j : ℕ) :
    j ∈ bodySources m i ↔ j < m ∧ i < j := by simp [bodySources]

theorem bodySweep_card (m i : ℕ) (A : Finset ℕ) :
    (bodySweep m i A).card = A.card := moveList_card _ _ _

theorem bodySweep_ground (m i : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range m)
    (hi : i < m) : bodySweep m i A ⊆ Finset.range m :=
  moveList_subset _ _ _ _ hA (Finset.mem_range.mpr hi)

theorem bodySweep_prefix (m i : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range m)
    (hc : i < A.card) (hp : Finset.range i ⊆ A) :
    Finset.range (i+1) ⊆ bodySweep m i A := by
  have hit : i ∈ bodySweep m i A := by
    rw [bodySweep, target_mem_moveList]
    by_cases hi : i ∈ A
    · exact Or.inl hi
    · right
      by_contra hn
      have hsub : A ⊆ Finset.range i := by
        intro j hj
        have hji : ¬ i < j := by
          intro hij
          exact hn ⟨j, mem_bodySources m i j |>.mpr ⟨Finset.mem_range.mp (hA hj), hij⟩, hj⟩
        have hne : j ≠ i := by intro heq; exact hi (heq ▸ hj)
        exact Finset.mem_range.mpr (by omega)
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
  intro x hx
  have hxi := Finset.mem_range.mp hx
  by_cases heq : x = i
  · simpa [heq] using hit
  · apply mem_moveList i x _ A (hp (Finset.mem_range.mpr (by omega)))
    simp only [mem_bodySources, not_and]
    omega

def shiftList (i : α) (L : List α) (F : Finset (Finset α)) :=
  L.foldl (fun F j => shift i j F) F

theorem shift_eq_self_of_common (i j : α) (F : Finset (Finset α))
    (h : ∀ A ∈ F, i ∈ A) : shift i j F = F := by
  unfold shift
  have hf : ∀ A ∈ F, shiftMember i j F A = A := by
    intro A hA
    simp [shiftMember, h A hA]
  simpa using (Finset.image_congr (fun A hA => hf A hA))

theorem shiftList_eq_self_of_common (i : α) (L : List α) (F : Finset (Finset α))
    (h : ∀ A ∈ F, i ∈ A) : shiftList i L F = F := by
  induction L with
  | nil => rfl
  | cons j L ih =>
      change shiftList i L (shift i j F) = F
      rw [shift_eq_self_of_common i j F h, ih]

theorem shiftList_tagged [Fintype α] (i : ℕ) (L : List ℕ) (B : α → Finset ℕ) :
    shiftList (Sum.inl i) (L.map Sum.inl) (taggedFamily B) =
      taggedFamily (fun w => moveList i L (B w)) := by
  induction L generalizing B with
  | nil => rfl
  | cons j L ih =>
      change shiftList (Sum.inl i) (L.map Sum.inl)
        (shift (Sum.inl i) (Sum.inl j) (taggedFamily B)) = _
      rw [shift_tagged, ih]
      rfl

def fullBodyPass (m : ℕ) (tags : List α) (i : ℕ) (F : Finset (Finset (ℕ ⊕ α))) :=
  shiftList (Sum.inl i) ((bodySources m i).map Sum.inl ++ tags.map Sum.inr) F

theorem fullBodyPass_tagged [Fintype α] (m i : ℕ) (tags : List α) (B : α → Finset ℕ)
    (hA : ∀ w, B w ⊆ Finset.range m) (hc : ∀ w, i < (B w).card)
    (hp : ∀ w, Finset.range i ⊆ B w) :
    fullBodyPass m tags i (taggedFamily B) =
      taggedFamily (fun w => bodySweep m i (B w)) := by
  unfold fullBodyPass
  rw [shiftList, List.foldl_append]
  change shiftList (Sum.inl i) (tags.map Sum.inr)
    (shiftList (Sum.inl i) ((bodySources m i).map Sum.inl) (taggedFamily B)) = _
  rw [shiftList_tagged]
  apply shiftList_eq_self_of_common
  intro A hA'
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hA'
  rw [inl_mem_tagged]
  apply bodySweep_prefix m i (B w) (hA w) (hc w) (hp w)
  simp

def bodyStages (m : ℕ) : ℕ → (α → Finset ℕ) → (α → Finset ℕ)
  | 0, B => B
  | t+1, B => fun w => bodySweep m t (bodyStages m t B w)

theorem bodyStages_invariant (m r t : ℕ) (B : α → Finset ℕ) (ht : t ≤ r) (hr : r ≤ m)
    (hA : ∀ w, B w ⊆ Finset.range m) (hc : ∀ w, (B w).card = r) :
    ∀ w, (bodyStages m t B w).card = r ∧ bodyStages m t B w ⊆ Finset.range m ∧
      Finset.range t ⊆ bodyStages m t B w := by
  induction t with
  | zero => intro w; exact ⟨hc w, hA w, by simp⟩
  | succ t ih =>
      have hit := ih (by omega)
      intro w
      obtain ⟨hcard, hground, hprefix⟩ := hit w
      exact ⟨(bodySweep_card m t _).trans hcard,
        bodySweep_ground m t _ hground (by omega),
        bodySweep_prefix m t _ hground (by omega) hprefix⟩

theorem bodyStages_final (m r : ℕ) (B : α → Finset ℕ) (hr : r ≤ m)
    (hA : ∀ w, B w ⊆ Finset.range m) (hc : ∀ w, (B w).card = r) :
    bodyStages m r B = fun _ => Finset.range r := by
  funext w
  obtain ⟨hcard, _, hprefix⟩ := bodyStages_invariant m r r B le_rfl hr hA hc w
  symm
  apply Finset.eq_of_subset_of_card_le hprefix
  simpa using hcard.le

theorem firstPasses_tagged [Fintype α] (m r t : ℕ) (tags : List α) (B : α → Finset ℕ)
    (ht : t ≤ r) (hr : r ≤ m) (hA : ∀ w, B w ⊆ Finset.range m)
    (hc : ∀ w, (B w).card = r) :
    (List.range t).foldl (fun F i => fullBodyPass m tags i F) (taggedFamily B) =
      taggedFamily (bodyStages m t B) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
      have hinv := bodyStages_invariant m r t B (by omega) hr hA hc
      exact fullBodyPass_tagged m t tags _ (fun w => (hinv w).2.1)
        (fun w => by rw [(hinv w).1]; omega) (fun w => (hinv w).2.2)


theorem recover_move (i j : α) (A : Finset α) (hi : i ∉ A) (hj : j ∈ A) :
    insert j ((insert i (A.erase j)).erase i) = A := by
  have hij : i ≠ j := by intro h; exact hi (h ▸ hj)
  ext x
  by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all

theorem shiftMember_injective (i j : α) (F : Finset (Finset α)) :
    Set.InjOn (shiftMember i j F) ↑F := by
  intro A hA B hB heq
  unfold shiftMember at heq
  split_ifs at heq with ha hb hb
  · have h := congrArg (fun S => insert j (S.erase i)) heq
    rw [recover_move i j A ha.1 ha.2.1, recover_move i j B hb.1 hb.2.1] at h
    exact h
  · exact False.elim (ha.2.2 (heq ▸ hB))
  · exact False.elim (hb.2.2 (heq.symm ▸ hA))
  · exact heq

theorem shift_card (i j : α) (F : Finset (Finset α)) :
    (shift i j F).card = F.card :=
  Finset.card_image_of_injOn (shiftMember_injective i j F)

theorem shiftMember_card (i j : α) (F : Finset (Finset α)) (A : Finset α) :
    (shiftMember i j F A).card = A.card := by
  unfold shiftMember
  split_ifs with h
  · have hm : move i j A = insert i (A.erase j) := by simp [move, h.1, h.2.1]
    rw [← hm, move_card]
  · rfl

theorem shiftMember_common (i j : α) (F : Finset (Finset α)) (A K : Finset α)
    (hK : K ⊆ A) (hj : j ∉ K) : K ⊆ shiftMember i j F A := by
  intro x hx
  unfold shiftMember
  split_ifs
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by intro h; exact hj (h ▸ hx), hK hx⟩)
  · exact hK hx

def perform (L : List (α × α)) (F : Finset (Finset α)) :=
  L.foldl (fun F p => shift p.1 p.2 F) F

theorem perform_card (L : List (α × α)) (F : Finset (Finset α)) :
    (perform L F).card = F.card := by
  induction L generalizing F with
  | nil => rfl
  | cons p L ih =>
      change (perform L (shift p.1 p.2 F)).card = F.card
      rw [ih, shift_card]

theorem perform_uniform_common (L : List (α × α)) (F : Finset (Finset α))
    (K : Finset α) (r : ℕ) (hF : ∀ A ∈ F, A.card = r ∧ K ⊆ A)
    (hL : ∀ p ∈ L, p.2 ∉ K) :
    ∀ A ∈ perform L F, A.card = r ∧ K ⊆ A := by
  induction L generalizing F with
  | nil => exact hF
  | cons p L ih =>
      apply ih
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        exact ⟨(shiftMember_card _ _ _ _).trans (hF B hB).1,
          shiftMember_common _ _ _ _ _ (hF B hB).2 (hL p (by simp))⟩
      · intro q hq
        exact hL q (by simp [hq])

theorem uniform_common_sunflower (K : Finset α) (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.card = K.card + 1 ∧ K ⊆ A) :
    ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ∩ B = K := by
  intro A hA B hB hne
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxK
    have hxA := Finset.mem_inter.mp hx |>.1
    have hxB := Finset.mem_inter.mp hx |>.2
    have hKA : insert x K = A := by
      apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hxA (hF A hA).2)
      rw [Finset.card_insert_of_notMem hxK, (hF A hA).1]
    have hKB : insert x K = B := by
      apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hxB (hF B hB).2)
      rw [Finset.card_insert_of_notMem hxK, (hF B hB).1]
    exact hne (hKA.symm.trans hKB)
  · exact Finset.subset_inter (hF A hA).2 (hF B hB).2

def bodySchedule (m : ℕ) (tags : List α) (targets : List ℕ) : List ((ℕ ⊕ α) × (ℕ ⊕ α)) :=
  targets.flatMap fun i =>
    (((bodySources m i).map Sum.inl ++ tags.map Sum.inr).map fun j => (Sum.inl i, j))

def tagSchedule (tags : List α) : List ((ℕ ⊕ α) × (ℕ ⊕ α)) :=
  tags.rec [] (fun a L ih => L.map (fun b => (Sum.inr a, Sum.inr b)) ++ ih)

/-- Every pair in the order body vertices 0,...,2k−1, then the supplied tag list,
ordered first by target and then source. Splitting targets at k is only notation. -/
def fullSchedule (k : ℕ) (tags : List α) : List ((ℕ ⊕ α) × (ℕ ⊕ α)) :=
  bodySchedule (2*k) tags (List.range k) ++
  bodySchedule (2*k) tags (List.range' k k) ++ tagSchedule tags

def core (k : ℕ) : Finset (ℕ ⊕ α) := (Finset.range k).image Sum.inl

@[simp] theorem inl_mem_core (k i : ℕ) : (Sum.inl i : ℕ ⊕ α) ∈ core k ↔ i < k := by
  simp [core]

@[simp] theorem inr_not_mem_core (k : ℕ) (a : α) : Sum.inr a ∉ core k := by simp [core]

@[simp] theorem core_card (k : ℕ) : (core k : Finset (ℕ ⊕ α)).card = k := by
  simp [core, Finset.card_image_of_injective _ Sum.inl_injective]

theorem perform_map_pair (i : α) (L : List α) (F : Finset (Finset α)) :
    perform (L.map (fun j => (i,j))) F = shiftList i L F := by
  simp [perform, shiftList, List.foldl_map]

theorem perform_bodySchedule (m : ℕ) (tags : List α) (targets : List ℕ)
    (F : Finset (Finset (ℕ ⊕ α))) :
    perform (bodySchedule m tags targets) F =
      targets.foldl (fun F i => fullBodyPass m tags i F) F := by
  induction targets generalizing F with
  | nil => rfl
  | cons i L ih =>
      simp only [bodySchedule, List.flatMap_cons, perform, List.foldl_append]
      change perform (bodySchedule m tags L)
        (perform (((bodySources m i).map Sum.inl ++ tags.map Sum.inr).map fun j => (Sum.inl i,j)) F) = _
      rw [perform_map_pair, ih]
      rfl

theorem tagSchedule_sources (k : ℕ) (tags : List α) :
    ∀ p ∈ tagSchedule tags, p.2 ∉ core k := by
  induction tags with
  | nil => simp [tagSchedule]
  | cons a L ih =>
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
        simp
      · exact ih p hp

theorem remaining_sources (k : ℕ) (tags : List α) :
    ∀ p ∈ bodySchedule (2*k) tags (List.range' k k) ++ tagSchedule tags,
      p.2 ∉ core k := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨i, hi, hpi⟩ := List.mem_flatMap.mp hp
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hpi
    subst p
    rcases List.mem_append.mp hj with hbody | htag
    · obtain ⟨b, hb, heqb⟩ := List.mem_map.mp hbody
      subst j
      obtain ⟨d, hd, hid⟩ := List.mem_range'.mp hi
      have hbi := ((mem_bodySources (2*k) i b).mp hb).2
      simp only [inl_mem_core]
      omega
    · obtain ⟨b, _, heqb⟩ := List.mem_map.mp htag
      subst j
      simp
  · exact tagSchedule_sources k tags p hp

theorem generic_full_lex [Fintype α] (k : ℕ) (tags : List α) (B : α → Finset ℕ)
    (hA : ∀ w, B w ⊆ Finset.range (2*k)) (hc : ∀ w, (B w).card = k) :
    (perform (fullSchedule k tags) (taggedFamily B)).card = Fintype.card α ∧
    (∀ A ∈ perform (fullSchedule k tags) (taggedFamily B), A.card = k+1) ∧
    (∀ A ∈ perform (fullSchedule k tags) (taggedFamily B),
      ∀ D ∈ perform (fullSchedule k tags) (taggedFamily B), A ≠ D → A ∩ D = core k) := by
  refine ⟨by rw [perform_card, taggedFamily_card], ?_⟩
  have hprefix : perform (bodySchedule (2*k) tags (List.range k)) (taggedFamily B) =
      taggedFamily (fun _ => Finset.range k) := by
    rw [perform_bodySchedule, firstPasses_tagged (2*k) k k tags B le_rfl (by omega) hA hc,
      bodyStages_final (2*k) k B (by omega) hA hc]
  have hcommon : ∀ A ∈ perform (fullSchedule k tags) (taggedFamily B),
      A.card = (core k : Finset (ℕ ⊕ α)).card + 1 ∧ core k ⊆ A := by
    rw [fullSchedule, List.append_assoc, perform, List.foldl_append]
    change ∀ A ∈ perform (bodySchedule (2*k) tags (List.range' k k) ++ tagSchedule tags)
      (perform (bodySchedule (2*k) tags (List.range k)) (taggedFamily B)), _
    rw [hprefix]
    apply perform_uniform_common
    · intro A hA'
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hA'
      refine ⟨?_, ?_⟩
      · rw [tagged_card, Finset.card_range, core_card]
      · exact Finset.subset_union_left
    · exact remaining_sources k tags
  exact ⟨fun A hA' => by simpa using (hcommon A hA').1,
    uniform_common_sunflower _ _ hcommon⟩


abbrev Word (k : ℕ) := Fin k → Bool

def coordinate {k : ℕ} (i : Fin k) (b : Bool) : ℕ := 2*i.val + if b then 1 else 0

theorem coordinate_injective {k : ℕ} (i j : Fin k) (b c : Bool)
    (h : coordinate i b = coordinate j c) : i = j ∧ b = c := by
  cases b <;> cases c <;> simp only [coordinate, Bool.false_eq_true, ↓reduceIte] at h
  · exact ⟨Fin.ext (by omega), rfl⟩
  · omega
  · omega
  · exact ⟨Fin.ext (by omega), rfl⟩

def binaryBody {k : ℕ} (w : Word k) : Finset ℕ :=
  Finset.univ.image (fun i => coordinate i (w i))

@[simp] theorem coordinate_mem_binaryBody {k : ℕ} (w : Word k) (i : Fin k) (b : Bool) :
    coordinate i b ∈ binaryBody w ↔ b = w i := by
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    obtain ⟨hji, hb⟩ := coordinate_injective j i (w j) b hj
    subst j
    exact hb.symm
  · intro h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [h]⟩

theorem binaryBody_card {k : ℕ} (w : Word k) : (binaryBody w).card = k := by
  rw [binaryBody, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact (coordinate_injective i j (w i) (w j) h).1

theorem binaryBody_ground {k : ℕ} (w : Word k) : binaryBody w ⊆ Finset.range (2*k) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hi := i.isLt
  apply Finset.mem_range.mpr
  cases h : w i <;> simp [coordinate, h] <;> omega

def initialFamily (k : ℕ) := taggedFamily (binaryBody (k := k))

noncomputable def allTags (k : ℕ) : List (Word k) :=
  List.ofFn ((Fintype.equivFin (Word k)).symm)

theorem allTags_nodup (k : ℕ) : (allTags k).Nodup := by
  rw [allTags, List.nodup_ofFn]
  exact (Fintype.equivFin (Word k)).symm.injective

theorem mem_allTags (k : ℕ) (w : Word k) : w ∈ allTags k := by
  rw [allTags, List.mem_ofFn]
  exact ⟨(Fintype.equivFin (Word k)) w, (Fintype.equivFin (Word k)).symm_apply_apply w⟩

@[simp] theorem allTags_length (k : ℕ) : (allTags k).length = 2^k := by
  simp [allTags, Word]

def IsSunflower (F : Finset (Finset α)) : Prop :=
  ∃ K, ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ∩ B = K

theorem initial_no_equal_triple {k : ℕ} (u v w : Word k)
    (h₁ : tagged binaryBody u ∩ tagged binaryBody v = tagged binaryBody u ∩ tagged binaryBody w)
    (h₂ : tagged binaryBody u ∩ tagged binaryBody v = tagged binaryBody v ∩ tagged binaryBody w) : u = v := by
  funext i
  have a := congrArg (fun S : Finset (ℕ ⊕ Word k) => Sum.inl (coordinate i false) ∈ S) h₁
  have b := congrArg (fun S : Finset (ℕ ⊕ Word k) => Sum.inl (coordinate i true) ∈ S) h₁
  have c := congrArg (fun S : Finset (ℕ ⊕ Word k) => Sum.inl (coordinate i false) ∈ S) h₂
  have d := congrArg (fun S : Finset (ℕ ⊕ Word k) => Sum.inl (coordinate i true) ∈ S) h₂
  simp only [Finset.mem_inter, inl_mem_tagged, coordinate_mem_binaryBody] at a b c d
  cases hu : u i <;> cases hv : v i <;> cases hw : w i <;> simp_all

theorem initial_no_three (k : ℕ) :
    ∀ G ⊆ initialFamily k, 3 ≤ G.card → ¬ IsSunflower G := by
  intro G hG hcard ⟨K, hK⟩
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < G.card)
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (hG hA)
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hG hB)
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp (hG hC)
  have huv := hK _ hA _ hB hAB
  have huw := hK _ hA _ hC hAC
  have hvw := hK _ hB _ hC hBC
  exact hAB (congrArg (tagged binaryBody)
    (initial_no_equal_triple u v w (huv.trans huw.symm) (huv.trans hvw.symm)))

noncomputable def finalFamily (k : ℕ) := perform (fullSchedule k (allTags k)) (initialFamily k)

abbrev statement : Prop :=
  ∀ k : ℕ,
    (initialFamily k).card = 2^k ∧
    (∀ A ∈ initialFamily k, A.card = k+1) ∧
    (∀ G ⊆ initialFamily k, 3 ≤ G.card → ¬ IsSunflower G) ∧
    (allTags k).Nodup ∧ (∀ w : Word k, w ∈ allTags k) ∧
    (finalFamily k).card = 2^k ∧
    (∀ A ∈ finalFamily k, A.card = k+1) ∧
    (∀ A ∈ finalFamily k, ∀ B ∈ finalFamily k, A ≠ B → A ∩ B = core k)

theorem proof : statement := by
  intro k
  have hlex := generic_full_lex k (allTags k) (binaryBody (k := k)) binaryBody_ground binaryBody_card
  refine ⟨?_, ?_, initial_no_three k, allTags_nodup k, mem_allTags k, ?_, hlex.2⟩
  · simp [initialFamily, taggedFamily_card, Word]
  · intro A hA
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hA
    rw [tagged_card, binaryBody_card]
  · simpa [finalFamily, initialFamily, Word] using hlex.1

#print axioms proof

end Submissions.Erdos20FullLexExponentialObstruction.Declan
