import Init

namespace Submissions.J6P26FiniteAPCoreRemoval.Main

namespace Jig26.FiniteCorePeeling

def active (edge vertices : List Nat) : Bool :=
  edge.all (fun x => vertices.contains x)

def live (edges : List (List Nat)) (vertices : List Nat) : List (List Nat) :=
  edges.filter (fun edge => active edge vertices)

def degree (edges : List (List Nat)) (vertices : List Nat) (x : Nat) : Nat :=
  (live edges vertices).countP (fun edge => edge.contains x)

def removeVertex (vertices : List Nat) (x : Nat) : List Nat :=
  vertices.filter (fun y => decide (y ≠ x))

theorem active_iff (edge vertices : List Nat) :
    active edge vertices = true ↔ edge ⊆ vertices := by
  simp only [active, List.all_eq_true, List.contains_iff_mem]
  constructor
  · intro h x hx
    exact h x hx
  · intro h x hx
    exact h hx

theorem active_remove (edge vertices : List Nat) (x : Nat) :
    active edge (removeVertex vertices x) =
      (active edge vertices && !(edge.contains x)) := by
  apply Bool.eq_iff_iff.mpr
  rw [active_iff, Bool.and_eq_true, active_iff]
  have hn : (!(edge.contains x)) = true ↔ x ∉ edge := by
    simp [List.contains_iff_mem]
  rw [hn]
  constructor
  · intro h
    constructor
    · intro y hy
      exact (List.mem_filter.mp (h hy)).1
    · intro hx
      have hxv := h hx
      simpa [removeVertex] using hxv
  · intro h y hy
    apply List.mem_filter.mpr
    exact ⟨h.1 hy, by
      simp only [decide_eq_true_eq]
      intro heq
      exact h.2 (heq ▸ hy)⟩

theorem live_remove (edges : List (List Nat)) (vertices : List Nat) (x : Nat) :
    live edges (removeVertex vertices x) =
      (live edges vertices).filter (fun edge => !(edge.contains x)) := by
  unfold live
  rw [List.filter_filter]
  apply List.filter_congr
  intro edge _
  rw [active_remove]
  exact Bool.and_comm _ _

theorem deletion_identity (edges : List (List Nat)) (vertices : List Nat) (x : Nat) :
    (live edges vertices).length =
      (live edges (removeVertex vertices x)).length + degree edges vertices x := by
  rw [live_remove]
  have h := List.length_eq_countP_add_countP
    (fun edge : List Nat => edge.contains x) (l := live edges vertices)
  simp only [List.countP_eq_length_filter] at h
  simp only [degree, List.countP_eq_length_filter]
  simpa [Nat.add_comm] using h

theorem remove_shorter (vertices : List Nat) (x : Nat) (hx : x ∈ vertices) :
    (removeVertex vertices x).length < vertices.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨x, hx, by simp⟩

theorem exists_core (edges : List (List Nat)) (vertices : List Nat) (M L : Nat) :
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree edges core x) ∧
      M * (live edges vertices).length + L * core.length ≤
        M * (live edges core).length + L * vertices.length := by
  classical
  have aux : ∀ n : Nat, ∀ vs : List Nat, vs.length = n →
      ∃ core : List Nat,
        List.Sublist core vs ∧
        (∀ x ∈ core, L < M * degree edges core x) ∧
        M * (live edges vs).length + L * core.length ≤
          M * (live edges core).length + L * vs.length := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro vs hlen
      by_cases hcore : ∀ x ∈ vs, L < M * degree edges vs x
      · exact ⟨vs, List.Sublist.refl _, hcore, Nat.le_refl _⟩
      · simp only [Classical.not_forall, Classical.not_imp_iff_and_not, Nat.not_lt] at hcore
        obtain ⟨x, hx, hd⟩ := hcore
        have hs := remove_shorter vs x hx
        obtain ⟨core, hsub, hdegree, hbudget⟩ :=
          ih (removeVertex vs x).length (by omega) (removeVertex vs x) rfl
        refine ⟨core, hsub.trans List.filter_sublist, hdegree, ?_⟩
        have hid := deletion_identity edges vs x
        have hstep : M * (live edges vs).length ≤
            M * (live edges (removeVertex vs x)).length + L := by
          rw [hid, Nat.mul_add]
          omega
        have hsize := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hs)
        simp only [Nat.mul_succ] at hsize
        omega
  exact aux vertices.length vertices rfl

theorem core_destroyed_budget (edges : List (List Nat)) (vertices : List Nat)
    (M L : Nat) :
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree edges core x) ∧
      M * ((live edges vertices).length - (live edges core).length) ≤
        L * (vertices.length - core.length) := by
  obtain ⟨core, hsub, hd, hb⟩ := exists_core edges vertices M L
  refine ⟨core, hsub, hd, ?_⟩
  have hlen := hsub.length_le
  have hmul := Nat.mul_le_mul_left L hlen
  rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
  omega

def difference (vertices core : List Nat) : List Nat :=
  vertices.filter (fun x => !(core.contains x))

theorem mem_difference (x : Nat) (vertices core : List Nat) :
    x ∈ difference vertices core ↔ x ∈ vertices ∧ x ∉ core := by
  simp [difference, List.contains_iff_mem]

theorem difference_length (vertices core : List Nat)
    (hv : vertices.Nodup) (hs : List.Sublist core vertices) :
    (difference vertices core).length + core.length = vertices.length := by
  let kept := vertices.filter (fun x => core.contains x)
  have hk : kept.Nodup := List.Sublist.nodup List.filter_sublist hv
  have hc : core.Nodup := hs.nodup hv
  have hkc : kept ⊆ core := by
    intro x hx
    exact List.contains_iff_mem.mp (List.mem_filter.mp hx).2
  have hck : core ⊆ kept := by
    intro x hx
    exact List.mem_filter.mpr ⟨hs.subset hx, List.contains_iff_mem.mpr hx⟩
  have hle := hk.length_le_of_subset hkc
  have hge := hc.length_le_of_subset hck
  have heq : kept.length = core.length := by omega
  have h := List.length_eq_countP_add_countP
    (fun x : Nat => core.contains x) (l := vertices)
  simp only [List.countP_eq_length_filter] at h
  have h' : vertices.length = kept.length + (difference vertices core).length := by
    simpa [kept, difference] using h
  omega

theorem disjoint_live_budget (edges : List (List Nat))
    (vertices left right : List Nat)
    (hl : left ⊆ vertices) (hr : right ⊆ vertices)
    (hdis : ∀ x, x ∈ left → x ∈ right → False)
    (hne : ∀ edge ∈ edges, edge ≠ []) :
    (live edges left).length + (live edges right).length ≤
      (live edges vertices).length := by
  revert hne
  induction edges with
  | nil => simp [live]
  | cons edge edges ih =>
    intro hne
    have ht := ih (fun e he => hne e (by simp [he]))
    have hleft : active edge left = true → active edge vertices = true := by
      intro ha
      exact (active_iff _ _).mpr (fun _ hx => hl ((active_iff _ _).mp ha hx))
    have hright : active edge right = true → active edge vertices = true := by
      intro ha
      exact (active_iff _ _).mpr (fun _ hx => hr ((active_iff _ _).mp ha hx))
    have hnot : ¬(active edge left = true ∧ active edge right = true) := by
      intro h
      cases edge with
      | nil => exact hne [] (by simp) rfl
      | cons x xs =>
        exact hdis x ((active_iff _ _).mp h.1 (by simp))
          ((active_iff _ _).mp h.2 (by simp))
    cases ha : active edge left <;> cases hb : active edge right <;>
      cases hc : active edge vertices <;> simp_all [live] <;> omega

theorem core_removed_budget (edges : List (List Nat)) (vertices : List Nat)
    (M L : Nat) (hv : vertices.Nodup) (hne : ∀ edge ∈ edges, edge ≠ []) :
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree edges core x) ∧
      M * (live edges (difference vertices core)).length ≤
        L * (difference vertices core).length := by
  obtain ⟨core, hsub, hd, hb⟩ := core_destroyed_budget edges vertices M L
  refine ⟨core, hsub, hd, ?_⟩
  have hleft : difference vertices core ⊆ vertices := by
    intro x hx
    exact ((mem_difference _ _ _).mp hx).1
  have hdis : ∀ x, x ∈ difference vertices core → x ∈ core → False := by
    intro x hx hc
    exact ((mem_difference _ _ _).mp hx).2 hc
  have he := disjoint_live_budget edges vertices (difference vertices core) core
    hleft hsub.subset hdis hne
  have hcount : (live edges (difference vertices core)).length ≤
      (live edges vertices).length - (live edges core).length := by omega
  have hmul := Nat.mul_le_mul_left M hcount
  have hlen := difference_length vertices core hv hsub
  have hdlen : vertices.length - core.length = (difference vertices core).length := by
    omega
  rw [hdlen] at hb
  exact Nat.le_trans hmul hb

theorem empty_edge_obstruction :
    (live [[]] (difference [] [])).length = 1 ∧
      (difference [] []).length = 0 := by
  decide

def uniqueEdges : List (List Nat) → List (List Nat)
  | [] => []
  | edge :: edges =>
    let rest := uniqueEdges edges
    if edge ∈ rest then rest else edge :: rest

theorem mem_uniqueEdges (edge : List Nat) (edges : List (List Nat)) :
    edge ∈ uniqueEdges edges ↔ edge ∈ edges := by
  induction edges generalizing edge with
  | nil => simp [uniqueEdges]
  | cons e es ih =>
    simp only [uniqueEdges]
    split <;> simp_all

theorem nodup_uniqueEdges (edges : List (List Nat)) :
    (uniqueEdges edges).Nodup := by
  induction edges with
  | nil => simp [uniqueEdges]
  | cons e es ih =>
    simp only [uniqueEdges]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨by assumption, ih⟩

def rawAPEdges (N : Nat) : List (List Nat) :=
  (List.range (N + 1)).flatMap fun a =>
    (List.range (N + 1)).flatMap fun d =>
      if 0 < d ∧ a + 2 * d ≤ N then [[a, a + d, a + 2 * d]] else []

def apEdges (N : Nat) : List (List Nat) := uniqueEdges (rawAPEdges N)

theorem mem_apEdges (N : Nat) (edge : List Nat) :
    edge ∈ apEdges N ↔
      ∃ a d : Nat, 0 < d ∧ a + 2 * d ≤ N ∧ edge = [a, a + d, a + 2 * d] := by
  rw [apEdges, mem_uniqueEdges]
  simp only [rawAPEdges, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨a, ha, d, hd, he⟩
    by_cases hp : 0 < d ∧ a + 2 * d ≤ N
    · simp only [if_pos hp, List.mem_singleton] at he
      exact ⟨a, d, hp.1, hp.2, he⟩
    · simp [hp] at he
  · rintro ⟨a, d, hp, ha, rfl⟩
    refine ⟨a, by omega, d, by omega, ?_⟩
    simp [hp, ha]

theorem nodup_apEdges (N : Nat) : (apEdges N).Nodup :=
  nodup_uniqueEdges _

theorem nonempty_apEdges (N : Nat) : ∀ edge ∈ apEdges N, edge ≠ [] := by
  intro edge he
  obtain ⟨a, d, hp, ha, rfl⟩ := (mem_apEdges N edge).mp he
  simp

theorem ap_core_removed_budget (N M L : Nat) (vertices : List Nat)
    (hv : vertices.Nodup) :
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree (apEdges N) core x) ∧
      M * (live (apEdges N) (difference vertices core)).length ≤
        L * (difference vertices core).length := by
  exact core_removed_budget (apEdges N) vertices M L hv (nonempty_apEdges N)

end Jig26.FiniteCorePeeling


open Jig26.FiniteCorePeeling

theorem result (N M L : Nat) (vertices : List Nat)
    (hv : vertices.Nodup) :
    ∃ core : List Nat,
      List.Sublist core vertices ∧
      (∀ x ∈ core, L < M * degree (apEdges N) core x) ∧
      M * (live (apEdges N) (difference vertices core)).length ≤
        L * (difference vertices core).length :=
  Jig26.FiniteCorePeeling.ap_core_removed_budget N M L vertices hv

end Submissions.J6P26FiniteAPCoreRemoval.Main
