import Init

namespace Submissions.J5P16PrivateCodeGraft.Proof

def Two (p q r : Prop) : Prop :=
  (p ∧ q ∧ ¬r) ∨ (p ∧ ¬q ∧ r) ∨ (¬p ∧ q ∧ r)

def ThreeFree {W P : Type} (privateSet : W → P → Prop) : Prop :=
  ∀ u v w, u ≠ v → u ≠ w → v ≠ w →
    ∃ x, Two (privateSet u x) (privateSet v x) (privateSet w x)

def OuterSeparates {I O : Type} (outer : I → O → Prop) : Prop :=
  ∀ i j k, ¬(i = j ∧ j = k) →
    ∃ x, Two (outer i x) (outer j x) (outer k x)

def Graft {I W O P E : Type}
    (outer : I → O → Prop) (privateSet : W → P → Prop)
    (shared : W → E → Prop) (i : I) (w : W) :
    Sum O (Sum (I × P) E) → Prop
  | Sum.inl x => outer i x
  | Sum.inr (Sum.inl x) => i = x.1 ∧ privateSet w x.2
  | Sum.inr (Sum.inr x) => shared w x

-- The shared code has NO hypotheses: existing multiplicity-two witnesses survive.
theorem shared_code_preserves_three_free {I W O P E : Type} [DecidableEq I]
    (outer : I → O → Prop) (privateSet : W → P → Prop)
    (shared : W → E → Prop)
    (ho : OuterSeparates outer) (hp : ThreeFree privateSet)
    (i j k : I) (u v w : W)
    (huv : i = j → u ≠ v) (huw : i = k → u ≠ w)
    (hvw : j = k → v ≠ w) :
    ∃ x, Two (Graft outer privateSet shared i u x)
      (Graft outer privateSet shared j v x)
      (Graft outer privateSet shared k w x) := by
  by_cases hij : i = j
  · by_cases hjk : j = k
    · subst j
      subst k
      obtain ⟨x, hx⟩ := hp u v w (huv rfl) (huw rfl) (hvw rfl)
      refine ⟨Sum.inr (Sum.inl (i, x)), ?_⟩
      cases hx with
      | inl h =>
        exact Or.inl ⟨⟨rfl, h.1⟩, ⟨rfl, h.2.1⟩, fun z => h.2.2 z.2⟩
      | inr h =>
        cases h with
        | inl h =>
          exact Or.inr (Or.inl ⟨⟨rfl, h.1⟩, (fun z => h.2.1 z.2), ⟨rfl, h.2.2⟩⟩)
        | inr h =>
          exact Or.inr (Or.inr ⟨(fun z => h.1 z.2), ⟨rfl, h.2.1⟩, ⟨rfl, h.2.2⟩⟩)
    · obtain ⟨x, hx⟩ := ho i j k (fun h => hjk h.2)
      exact ⟨Sum.inl x, hx⟩
  · obtain ⟨x, hx⟩ := ho i j k (fun h => hij h.1)
    exact ⟨Sum.inl x, hx⟩

theorem solves {I W O P E : Type} [DecidableEq I]
    (outer : I → O → Prop) (privateSet : W → P → Prop)
    (shared : W → E → Prop)
    (ho : OuterSeparates outer) (hp : ThreeFree privateSet)
    (i j k : I) (u v w : W)
    (huv : i = j → u ≠ v) (huw : i = k → u ≠ w)
    (hvw : j = k → v ≠ w) :
    ∃ x, Two (Graft outer privateSet shared i u x)
      (Graft outer privateSet shared j v x)
      (Graft outer privateSet shared k w x) := by
  exact shared_code_preserves_three_free outer privateSet shared ho hp i j k u v w huv huw hvw

end Submissions.J5P16PrivateCodeGraft.Proof
