import Init

/-!
# Finite hypergraph core removal, by direct peeling

A proof of `Statements.FiniteHypergraphCoreRemoval.statement`.

Edges are lists of naturals and may repeat; the only hypothesis is that no edge is empty.

* If every vertex of `V` already has `L < M * degree`, take `core = V`: the removed set is empty
  and no nonempty edge is live on an empty vertex set.
* Otherwise pick `x ∈ V` with `M * degree E V x ≤ L`, delete every copy of `x`, and recurse.
  An edge inside the new removed set either avoids `x` (so it was inside the old removed set)
  or contains `x` (so it is live on `V` and counted by `degree E V x`).
-/

namespace Submissions.FiniteHypergraphCoreRemoval.Peel

def active (edge vertices : List Nat) : Bool :=
  edge.all (fun x => vertices.contains x)

def live (edges : List (List Nat)) (vertices : List Nat) : List (List Nat) :=
  edges.filter (fun edge => active edge vertices)

def degree (edges : List (List Nat)) (vertices : List Nat) (x : Nat) : Nat :=
  (live edges vertices).countP (fun edge => edge.contains x)

def difference (vertices core : List Nat) : List Nat :=
  vertices.filter (fun x => !(core.contains x))

abbrev statement : Prop :=
  ∀ (edges : List (List Nat)) (M L : Nat) (vertices : List Nat),
    (∀ edge ∈ edges, edge ≠ []) →
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree edges core x) ∧
      M * (live edges (difference vertices core)).length ≤
        L * (difference vertices core).length

/-! ## Membership bookkeeping -/

theorem active_iff (e V : List Nat) : active e V = true ↔ ∀ y, y ∈ e → y ∈ V := by
  simp [active, List.all_eq_true]

theorem mem_difference (V C : List Nat) (y : Nat) :
    y ∈ difference V C ↔ y ∈ V ∧ y ∉ C := by
  simp [difference]

theorem live_length (E : List (List Nat)) (V : List Nat) :
    (live E V).length = E.countP (fun e => active e V) := by
  simp [live, List.countP_eq_length_filter]

theorem degree_eq (E : List (List Nat)) (V : List Nat) (x : Nat) :
    degree E V x = E.countP (fun e => e.contains x && active e V) := by
  simp [degree, live, List.countP_filter]

theorem countP_le_add {α : Type} (E : List α) (p q t : α → Bool)
    (h : ∀ e, e ∈ E → p e = true → q e = true ∨ t e = true) :
    E.countP p ≤ E.countP q + E.countP t := by
  induction E with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    have ha := h a List.mem_cons_self
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> cases ht : t a <;> simp_all <;> omega

/-! ## The two cases of the peeling step -/

/-- Nothing nonempty is live on the empty vertex set. -/
theorem live_nil (E : List (List Nat)) (hE : ∀ e, e ∈ E → e ≠ []) : live E [] = [] := by
  simp only [live, List.filter_eq_nil_iff]
  intro e he hact
  rw [active_iff] at hact
  cases e with
  | nil => exact hE [] he rfl
  | cons a t => exact absurd (hact a List.mem_cons_self) (by simp)

theorem difference_self (V : List Nat) : difference V V = [] := by
  simp [difference, List.filter_eq_nil_iff]

/-- One peeling step: removing all copies of a low-degree vertex `x` keeps the budget. -/
theorem peel_step (E : List (List Nat)) (M L : Nat) (V C : List Nat) (x : Nat)
    (hxV : x ∈ V) (hx : M * degree E V x ≤ L)
    (hC : ∀ y, y ∈ C → y ∈ V.filter (fun y => y != x))
    (hbudget : M * (live E (difference (V.filter (fun y => y != x)) C)).length ≤
        L * (difference (V.filter (fun y => y != x)) C).length) :
    M * (live E (difference V C)).length ≤ L * (difference V C).length := by
  have hxC : x ∉ C := by
    intro h
    have := hC x h
    simp at this
  -- the removed set grows by at least one element
  have hlen : (difference (V.filter (fun y => y != x)) C).length + 1 ≤
      (difference V C).length := by
    have heq : difference (V.filter (fun y => y != x)) C =
        (difference V C).filter (fun y => y != x) := by
      simp [difference, List.filter_filter, Bool.and_comm]
    rw [heq]
    have hxR : x ∈ difference V C := (mem_difference V C x).mpr ⟨hxV, hxC⟩
    exact List.length_filter_lt_length_iff_exists.mpr ⟨x, hxR, by simp⟩
  -- every edge inside the new removed set is inside the old one or counted at `x`
  have hedges : (live E (difference V C)).length ≤
      (live E (difference (V.filter (fun y => y != x)) C)).length + degree E V x := by
    rw [live_length, live_length, degree_eq]
    apply countP_le_add
    intro e _ hact
    rw [active_iff] at hact
    by_cases hxe : x ∈ e
    · right
      have hV : active e V = true :=
        (active_iff e V).mpr (fun y hy => ((mem_difference V C y).mp (hact y hy)).1)
      simp [hxe, hV]
    · left
      apply (active_iff _ _).mpr
      intro y hy
      have hyR := (mem_difference V C y).mp (hact y hy)
      apply (mem_difference _ C y).mpr
      refine ⟨?_, hyR.2⟩
      have hne : y ≠ x := fun h => hxe (h ▸ hy)
      simp [hyR.1, hne]
  calc M * (live E (difference V C)).length
      ≤ M * ((live E (difference (V.filter (fun y => y != x)) C)).length + degree E V x) :=
        Nat.mul_le_mul_left M hedges
    _ = M * (live E (difference (V.filter (fun y => y != x)) C)).length + M * degree E V x :=
        Nat.mul_add _ _ _
    _ ≤ L * (difference (V.filter (fun y => y != x)) C).length + L :=
        Nat.add_le_add hbudget hx
    _ = L * ((difference (V.filter (fun y => y != x)) C).length + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ L * (difference V C).length := Nat.mul_le_mul_left L hlen

/-! ## Peeling, for any edge list without an empty edge -/

theorem peel (E : List (List Nat)) (hE : ∀ e, e ∈ E → e ≠ []) (M L : Nat) :
    ∀ (n : Nat) (V : List Nat), V.length ≤ n →
      ∃ core : List Nat, List.Sublist core V ∧
        (∀ x, x ∈ core → L < M * degree E core x) ∧
        M * (live E (difference V core)).length ≤ L * (difference V core).length := by
  intro n
  induction n with
  | zero =>
    intro V hV
    have hnil : V = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hV)
    subst hnil
    refine ⟨[], List.Sublist.refl _, ?_, ?_⟩
    · intro x hx
      simp at hx
    · rw [difference_self, live_nil E hE]
      simp
  | succ n ih =>
    intro V hV
    by_cases hall : ∀ x, x ∈ V → L < M * degree E V x
    · refine ⟨V, List.Sublist.refl _, hall, ?_⟩
      rw [difference_self, live_nil E hE]
      simp
    · have hex : ∃ x, x ∈ V ∧ M * degree E V x ≤ L := by
        apply Classical.byContradiction
        intro hne
        apply hall
        intro x hx
        apply Classical.byContradiction
        intro hlt
        exact hne ⟨x, hx, Nat.le_of_not_lt hlt⟩
      obtain ⟨x, hxV, hx⟩ := hex
      have hlt : (V.filter (fun y => y != x)).length < V.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨x, hxV, by simp⟩
      obtain ⟨C, hCsub, hCdeg, hCbudget⟩ :=
        ih (V.filter (fun y => y != x)) (by omega)
      refine ⟨C, hCsub.trans List.filter_sublist, hCdeg, ?_⟩
      exact peel_step E M L V C x hxV hx (fun y hy => hCsub.subset hy) hCbudget

theorem proof : statement := fun edges M L vertices hE =>
  peel edges hE M L vertices.length vertices (Nat.le_refl _)

end Submissions.FiniteHypergraphCoreRemoval.Peel
