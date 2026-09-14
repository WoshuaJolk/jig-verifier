import Init

namespace Submissions.J4P16WitnessProjection.Proof

def Two (p q r : Prop) : Prop :=
  (p ∧ q ∧ ¬r) ∨ (p ∧ ¬q ∧ r) ∨ (¬p ∧ q ∧ r)

def Project {I X : Type} (family : I → X → Prop) (keep : X → Prop)
    (i : I) (x : X) : Prop := keep x ∧ family i x

def RetainsWitnesses {I X : Type} (family : I → X → Prop) (keep : X → Prop) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∃ x, keep x ∧ Two (family i x) (family j x) (family k x)

def StrongThreeFree {I X : Type} (family : I → X → Prop) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∃ x, Two (family i x) (family j x) (family k x)

theorem retained_witnesses_preserve {I X : Type}
    (family : I → X → Prop) (keep : X → Prop)
    (h : RetainsWitnesses family keep) :
    StrongThreeFree (Project family keep) := by
  intro i j k hij hik hjk
  obtain ⟨x, hx, hw⟩ := h i j k hij hik hjk
  refine ⟨x, ?_⟩
  cases hw with
  | inl z =>
    exact Or.inl ⟨⟨hx, z.1⟩, ⟨hx, z.2.1⟩, fun a => z.2.2 a.2⟩
  | inr z =>
    cases z with
    | inl z =>
      exact Or.inr (Or.inl ⟨⟨hx, z.1⟩, (fun a => z.2.1 a.2), ⟨hx, z.2.2⟩⟩)
    | inr z =>
      exact Or.inr (Or.inr ⟨(fun a => z.1 a.2), ⟨hx, z.2.1⟩, ⟨hx, z.2.2⟩⟩)

-- This is the logical content of the at-most-two-preimages bound.
theorem no_three_equal_projected_rows {I X : Type}
    (family : I → X → Prop) (keep : X → Prop)
    (h : RetainsWitnesses family keep)
    (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (eqij : ∀ x, Project family keep i x ↔ Project family keep j x)
    (eqik : ∀ x, Project family keep i x ↔ Project family keep k x) : False := by
  obtain ⟨x, hw⟩ := retained_witnesses_preserve family keep h i j k hij hik hjk
  cases hw with
  | inl z => exact z.2.2 ((eqik x).mp z.1)
  | inr z =>
    cases z with
    | inl z => exact z.2.1 ((eqij x).mp z.1)
    | inr z => exact z.1 ((eqij x).mpr z.2.1)


theorem solves :
(∀ {I X : Type}
    (family : I → X → Prop) (keep : X → Prop)
    (h : RetainsWitnesses family keep),
StrongThreeFree (Project family keep)) ∧
(∀ {I X : Type}
    (family : I → X → Prop) (keep : X → Prop)
    (h : RetainsWitnesses family keep)
    (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (eqij : ∀ x, Project family keep i x ↔ Project family keep j x)
    (eqik : ∀ x, Project family keep i x ↔ Project family keep k x),
False) := by
  exact ⟨@retained_witnesses_preserve, @no_three_equal_projected_rows⟩

end Submissions.J4P16WitnessProjection.Proof
