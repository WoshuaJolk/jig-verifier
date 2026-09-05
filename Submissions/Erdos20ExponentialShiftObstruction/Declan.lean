import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace Submissions.Erdos20ExponentialShiftObstruction.Declan

abbrev Word (k : ℕ) := Fin k → Bool
abbrev Vertex (k : ℕ) := (Fin k × Bool) ⊕ Word k

def edge {k : ℕ} (collapsed : Finset (Fin k)) (w : Word k) : Finset (Vertex k) :=
  (Finset.univ.image fun i : Fin k => Sum.inl (i, if i ∈ collapsed then false else w i)) ∪
    {Sum.inr w}

def family (k : ℕ) (collapsed : Finset (Fin k)) : Finset (Finset (Vertex k)) :=
  Finset.univ.image (edge collapsed)

@[simp] theorem inl_mem_edge {k : ℕ} (S : Finset (Fin k)) (w : Word k)
    (i : Fin k) (b : Bool) :
    Sum.inl (i,b) ∈ edge S w ↔ b = if i ∈ S then false else w i := by
  simp [edge, eq_comm]

@[simp] theorem inr_mem_edge {k : ℕ} (S : Finset (Fin k)) (w v : Word k) :
    Sum.inr v ∈ edge S w ↔ v = w := by
  simp [edge, eq_comm]

theorem edge_injective {k : ℕ} (S : Finset (Fin k)) : Function.Injective (edge S) := by
  intro w v h
  have hw : Sum.inr w ∈ edge S w := by simp
  rw [h] at hw
  simpa using hw

theorem family_card (k : ℕ) (S : Finset (Fin k)) : (family k S).card = 2 ^ k := by
  rw [family, Finset.card_image_of_injective _ (edge_injective S)]
  simp [Word]

theorem edge_card {k : ℕ} (S : Finset (Fin k)) (w : Word k) :
    (edge S w).card = k + 1 := by
  rw [edge, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective]
    · simp
    · intro i j h
      exact congrArg Prod.fst (Sum.inl.inj h)
  · simp [Finset.disjoint_left]

theorem no_three_equal_intersections {k : ℕ} (u v w : Word k)
    (h₁ : edge ∅ u ∩ edge ∅ v = edge ∅ u ∩ edge ∅ w)
    (h₂ : edge ∅ u ∩ edge ∅ v = edge ∅ v ∩ edge ∅ w) : u = v := by
  funext i
  have a := congrArg (fun s : Finset (Vertex k) => Sum.inl (i,false) ∈ s) h₁
  have b := congrArg (fun s : Finset (Vertex k) => Sum.inl (i,true) ∈ s) h₁
  have c := congrArg (fun s : Finset (Vertex k) => Sum.inl (i,false) ∈ s) h₂
  have d := congrArg (fun s : Finset (Vertex k) => Sum.inl (i,true) ∈ s) h₂
  simp only [Finset.mem_inter, inl_mem_edge, Finset.notMem_empty, ↓reduceIte] at a b c d
  cases hu : u i <;> cases hv : v i <;> cases hw : w i <;>
    simp_all

/-- The standard elementary set-family shift: move `y` to `x` only when
`x` is absent and the new member is not already in the family. -/
def shiftMember {k : ℕ} (i : Fin k) (F : Finset (Finset (Vertex k)))
    (A : Finset (Vertex k)) : Finset (Vertex k) :=
  if Sum.inl (i,false) ∉ A ∧ Sum.inl (i,true) ∈ A ∧
      insert (Sum.inl (i,false)) (A.erase (Sum.inl (i,true))) ∉ F then
    insert (Sum.inl (i,false)) (A.erase (Sum.inl (i,true)))
  else A

def shift {k : ℕ} (i : Fin k) (F : Finset (Finset (Vertex k))) :
    Finset (Finset (Vertex k)) := F.image (shiftMember i F)

theorem edge_insert_of_already_false {k : ℕ} (S : Finset (Fin k)) (w : Word k)
    (i : Fin k) (h : i ∈ S ∨ w i = false) : edge (insert i S) w = edge S w := by
  ext x
  cases x with
  | inl p =>
      rcases p with ⟨j,b⟩
      by_cases hij : j = i
      · subst j
        rcases h with h | h <;> simp [h]
      · simp [hij]
  | inr v => simp

theorem replace_edge {k : ℕ} (S : Finset (Fin k)) (w : Word k)
    (i : Fin k) (hi : i ∉ S) (hw : w i = true) :
    insert (Sum.inl (i,false)) ((edge S w).erase (Sum.inl (i,true))) =
      edge (insert i S) w := by
  ext x
  cases x with
  | inl p =>
      rcases p with ⟨j,b⟩
      by_cases hij : j = i
      · subst j
        cases b <;> simp [hi, hw]
      · simp [hij]
  | inr v => simp

theorem inserted_edge_not_mem {k : ℕ} (S : Finset (Fin k)) (w : Word k)
    (i : Fin k) (hi : i ∉ S) (hw : w i = true) :
    edge (insert i S) w ∉ family k S := by
  intro h
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
  have ht : Sum.inr w ∈ edge S v := by rw [hv]; simp
  have hvw : w = v := by simpa using ht
  subst v
  have hb : Sum.inl (i,false) ∈ edge S w := by rw [hv]; simp
  simp [hi, hw] at hb

theorem shiftMember_edge {k : ℕ} (S : Finset (Fin k)) (w : Word k) (i : Fin k) :
    shiftMember i (family k S) (edge S w) = edge (insert i S) w := by
  by_cases hi : i ∈ S
  · rw [edge_insert_of_already_false S w i (Or.inl hi)]
    simp [shiftMember, hi]
  · cases hw : w i with
    | false =>
        rw [edge_insert_of_already_false S w i (Or.inr hw)]
        simp [shiftMember, hi, hw]
    | true =>
        have hn := inserted_edge_not_mem S w i hi hw
        rw [← replace_edge S w i hi hw] at hn
        simp only [shiftMember, inl_mem_edge, hi, ↓reduceIte, hw,
          not_false_eq_true, and_self, hn]
        exact replace_edge S w i hi hw

theorem shift_family {k : ℕ} (S : Finset (Fin k)) (i : Fin k) :
    shift i (family k S) = family k (insert i S) := by
  unfold shift
  conv_lhs => rw [family, Finset.image_image]
  unfold family
  congr 1
  funext w
  exact shiftMember_edge S w i

def performShifts {k : ℕ} (L : List (Fin k)) (F : Finset (Finset (Vertex k))) :
    Finset (Finset (Vertex k)) := L.foldr shift F

theorem performShifts_family {k : ℕ} (L : List (Fin k)) (S : Finset (Fin k)) :
    performShifts L (family k S) = family k (S ∪ L.toFinset) := by
  induction L with
  | nil => simp [performShifts]
  | cons i L ih =>
      simp only [performShifts, List.foldr_cons] at *
      rw [ih, shift_family]
      congr 1
      ext j
      simp only [Finset.mem_insert, Finset.mem_union, List.toFinset_cons]
      aesop

def IsSunflower {k : ℕ} (F : Finset (Finset (Vertex k))) : Prop :=
  ∃ K : Finset (Vertex k), ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ∩ B = K

theorem initial_has_no_three_sunflower (k : ℕ) :
    ∀ G ⊆ family k ∅, 3 ≤ G.card → ¬ IsSunflower G := by
  intro G hG hcard ⟨K, hK⟩
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < G.card)
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (hG hA)
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hG hB)
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp (hG hC)
  have hUV := hK _ hA _ hB hAB
  have hUW := hK _ hA _ hC hAC
  have hVW := hK _ hB _ hC hBC
  have huv := no_three_equal_intersections u v w (hUV.trans hUW.symm) (hUV.trans hVW.symm)
  exact hAB (congrArg (edge ∅) huv)

def core (k : ℕ) : Finset (Vertex k) :=
  Finset.univ.image (fun i : Fin k => Sum.inl (i,false))

theorem final_intersection {k : ℕ} (u v : Word k) (huv : u ≠ v) :
    edge Finset.univ u ∩ edge Finset.univ v = core k := by
  ext x
  cases x with
  | inl p =>
      rcases p with ⟨i,b⟩
      cases b <;> simp [core]
  | inr w =>
      simp only [Finset.mem_inter, inr_mem_edge, core, Finset.mem_image,
        Finset.mem_univ, true_and, Sum.inl_ne_inr, exists_false, iff_false, not_and]
      intro hwu hwv
      exact huv (hwu.symm.trans hwv)

theorem final_is_sunflower (k : ℕ) : IsSunflower (family k Finset.univ) := by
  refine ⟨core k, ?_⟩
  intro A hA B hB hAB
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
  apply final_intersection
  intro huv
  exact hAB (congrArg (edge Finset.univ) huv)

theorem all_shifts (k : ℕ) :
    performShifts (List.finRange k) (family k ∅) = family k Finset.univ := by
  simp [performShifts_family]

/-- A rank-`k+1` family of `2^k` sets has no sunflower of three or more
members, while `k` ordinary elementary shifts turn it into a sunflower
of exactly `2^k` members. The shifts are all `(i,true) → (i,false)`.
This obstructs preservation of a rank-independent sunflower-size bound
under arbitrary sequences of ordinary shifts. It does not settle the
exponential sunflower conjecture. -/
abbrev statement : Prop :=
  ∀ k : ℕ,
    (family k ∅).card = 2 ^ k ∧
    (∀ A ∈ family k ∅, A.card = k + 1) ∧
    (∀ G ⊆ family k ∅, 3 ≤ G.card → ¬ IsSunflower G) ∧
    (List.finRange k).length = k ∧
    (performShifts (List.finRange k) (family k ∅)).card = 2 ^ k ∧
    IsSunflower (performShifts (List.finRange k) (family k ∅))

theorem proof : statement := by
  intro k
  refine ⟨family_card k ∅, ?_, initial_has_no_three_sunflower k, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hA
    exact edge_card ∅ w
  · simp
  · rw [all_shifts]
    exact family_card k Finset.univ
  · rw [all_shifts]
    exact final_is_sunflower k

#print axioms proof

end Submissions.Erdos20ExponentialShiftObstruction.Declan
