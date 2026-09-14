import Init

namespace Submissions.J4P16DefectMatching.Proof

def Defect {I X : Type} (R : I → I → X → Prop) (s : I) (x : X) : Prop :=
  ∃ i j, i ≠ j ∧ R s i x ∧ R s j x

def Family {I X : Type} (A : X → Prop) (R : I → I → X → Prop) : Option I → X → Prop
  | none => A
  | some i => R i i

theorem disjoint_defects_force_common_intersections {I X : Type}
    (A C : X → Prop) (R : I → I → X → Prop)
    (trace : ∀ s i x, (R s i x ∧ A x) ↔ C x)
    (compatible : ∀ s t i j x, R s i x → R t j x → R s j x)
    (disjoint : ∀ s t, s ≠ t → ∀ x, ¬ A x → Defect R s x → Defect R t x → False) :
    ∀ u v, u ≠ v → ∀ x,
      (Family A R u x ∧ Family A R v x) ↔ C x := by
  intro u v huv x
  cases u with
  | none =>
    cases v with
    | none => exact False.elim (huv rfl)
    | some j =>
      constructor
      · intro h
        exact (trace j j x).mp ⟨h.2, h.1⟩
      · intro h
        have ht := (trace j j x).mpr h
        exact ⟨ht.2, ht.1⟩
  | some i =>
    cases v with
    | none => exact trace i i x
    | some j =>
      have hij : i ≠ j := fun h => huv (congrArg some h)
      constructor
      · intro h
        by_cases ha : A x
        · exact (trace i i x).mp ⟨h.1, ha⟩
        · have hi : Defect R i x :=
            ⟨i, j, hij, h.1, compatible i j i j x h.1 h.2⟩
          have hj : Defect R j x :=
            ⟨i, j, hij, compatible j i j i x h.2 h.1, h.2⟩
          exact False.elim (disjoint i j hij x ha hi hj)
      · intro hc
        exact ⟨((trace i i x).mpr hc).1, ((trace j j x).mpr hc).1⟩

theorem disjoint_defects_give_distinct_members {I X : Type}
    (A C : X → Prop) (R : I → I → X → Prop)
    (trace : ∀ s i x, (R s i x ∧ A x) ↔ C x)
    (compatible : ∀ s t i j x, R s i x → R t j x → R s j x)
    (disjoint : ∀ s t, s ≠ t → ∀ x, ¬ A x → Defect R s x → Defect R t x → False)
    (outside : ∀ i, ∃ x, R i i x ∧ ¬ A x) :
    ∀ u v, Family A R u = Family A R v → u = v := by
  intro u v heq
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some j =>
      rcases outside j with ⟨x, hx, ha⟩
      have hh : A x = R j j x := congrArg (fun f => f x) heq
      exact False.elim (ha (hh.mpr hx))
  | some i =>
    cases v with
    | none =>
      rcases outside i with ⟨x, hx, ha⟩
      have hh : R i i x = A x := congrArg (fun f => f x) heq
      exact False.elim (ha (hh.mp hx))
    | some j =>
      by_cases hij : i = j
      · exact congrArg some hij
      · rcases outside i with ⟨x, hx, ha⟩
        have hh : R i i x = R j j x := congrArg (fun f => f x) heq
        have hopt : (some i : Option I) ≠ some j := fun h => hij (Option.some.inj h)
        have hc := (disjoint_defects_force_common_intersections A C R trace
          compatible disjoint (some i) (some j) hopt x).mp ⟨hx, hh.mp hx⟩
        exact False.elim (ha ((trace i i x).mpr hc).2)

theorem anchored_defect_recombination {I X : Type}
    (A C : X → Prop) (R : I → I → X → Prop)
    (trace : ∀ s i x, (R s i x ∧ A x) ↔ C x)
    (compatible : ∀ s t i j x, R s i x → R t j x → R s j x)
    (disjoint : ∀ s t, s ≠ t → ∀ x, ¬ A x → Defect R s x → Defect R t x → False)
    (outside : ∀ i, ∃ x, R i i x ∧ ¬ A x) :
    (∀ u v, Family A R u = Family A R v → u = v) ∧
    (∀ u v, u ≠ v → ∀ x,
      (Family A R u x ∧ Family A R v x) ↔ C x) :=
  ⟨disjoint_defects_give_distinct_members A C R trace compatible disjoint outside,
    disjoint_defects_force_common_intersections A C R trace compatible disjoint⟩


theorem solves :
(∀ {I X : Type}
    (A C : X → Prop) (R : I → I → X → Prop)
    (trace : ∀ s i x, (R s i x ∧ A x) ↔ C x)
    (compatible : ∀ s t i j x, R s i x → R t j x → R s j x)
    (disjoint : ∀ s t, s ≠ t → ∀ x, ¬ A x → Defect R s x → Defect R t x → False)
    (outside : ∀ i, ∃ x, R i i x ∧ ¬ A x),
(∀ u v, Family A R u = Family A R v → u = v) ∧
    (∀ u v, u ≠ v → ∀ x,
      (Family A R u x ∧ Family A R v x) ↔ C x)) := by
  exact @anchored_defect_recombination

end Submissions.J4P16DefectMatching.Proof
