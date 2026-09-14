import Init

namespace Submissions.J4P41PartialCauchy.Proof.P41PartialCauchy

def Consistent {G : Type} (add : G → G → G) (D : G → Prop)
    (φ : G → Int) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → add a b = add c d →
    φ a + φ b = φ c + φ d

theorem bridge_consistent {G : Type} (add : G → G → G)
    (D : G → Prop) (φ : G → Int)
    (local_add : ∀ x y, D x → D y → D (add x y) → φ (add x y) = φ x + φ y)
    (bridge : ∀ a b c d, D a → D b → D c → D d → add a b = add c d →
      ∃ t u v w, D t ∧ D u ∧ D v ∧ D w ∧
        add t u = a ∧ add t v = c ∧ add u b = w ∧ add v d = w) :
    Consistent add D φ := by
  intro a b c d ha hb hc hd eq
  obtain ⟨t, u, v, w, ht, hu, hv, hw, htu, htv, hub, hvd⟩ :=
    bridge a b c d ha hb hc hd eq
  have h₁ := local_add t u ht hu (htu.symm ▸ ha)
  have h₂ := local_add t v ht hv (htv.symm ▸ hc)
  have h₃ := local_add u b hu hb (hub.symm ▸ hw)
  have h₄ := local_add v d hv hd (hvd.symm ▸ hw)
  rw [htu] at h₁
  rw [htv] at h₂
  rw [hub] at h₃
  rw [hvd] at h₄
  omega

def extend {G : Type} (φ : G → Int) (l r : G → G) (x : G) : Int :=
  φ (l x) + φ (r x)

theorem extension_pair {G : Type} (add : G → G → G) (D : G → Prop)
    (φ : G → Int) (l r : G → G)
    (hl : ∀ x, D (l x)) (hr : ∀ x, D (r x))
    (split : ∀ x, add (l x) (r x) = x) (consistent : Consistent add D φ)
    (a b : G) (ha : D a) (hb : D b) :
    extend φ l r (add a b) = φ a + φ b := by
  exact consistent (l (add a b)) (r (add a b)) a b
    (hl _) (hr _) ha hb (split _)

theorem extension_additive {G : Type} (add : G → G → G) (neg : G → G)
    (D : G → Prop) (φ : G → Int) (l r : G → G)
    (hl : ∀ x, D (l x)) (hr : ∀ x, D (r x))
    (split : ∀ x, add (l x) (r x) = x) (consistent : Consistent add D φ)
    (antisymmetric : ∀ t, D t → φ t + φ (neg t) = 0)
    (merge : ∀ x y, ∃ t a b, D t ∧ D a ∧ D b ∧ D (neg t) ∧
      add t a = x ∧ add b (neg t) = y ∧ add a b = add x y)
    (x y : G) : extend φ l r (add x y) = extend φ l r x + extend φ l r y := by
  obtain ⟨t, a, b, ht, ha, hb, hnt, hx, hy, hxy⟩ := merge x y
  have h₁ := extension_pair add D φ l r hl hr split consistent t a ht ha
  have h₂ := extension_pair add D φ l r hl hr split consistent b (neg t) hb hnt
  have h₃ := extension_pair add D φ l r hl hr split consistent a b ha hb
  rw [hx] at h₁
  rw [hy] at h₂
  rw [hxy] at h₃
  have h₄ := antisymmetric t ht
  omega

end Submissions.J4P41PartialCauchy.Proof.P41PartialCauchy

namespace Submissions.J4P41PartialCauchy.Proof

theorem proof :
  (∀ {G : Type} (add : G → G → G)
    (D : G → Prop) (φ : G → Int)
    (local_add : ∀ x y, D x → D y → D (add x y) → φ (add x y) = φ x + φ y)
    (bridge : ∀ a b c d, D a → D b → D c → D d → add a b = add c d →
      ∃ t u v w, D t ∧ D u ∧ D v ∧ D w ∧
        add t u = a ∧ add t v = c ∧ add u b = w ∧ add v d = w),
    P41PartialCauchy.Consistent add D φ) ∧
  (∀ {G : Type} (add : G → G → G) (neg : G → G)
    (D : G → Prop) (φ : G → Int) (l r : G → G)
    (hl : ∀ x, D (l x)) (hr : ∀ x, D (r x))
    (split : ∀ x, add (l x) (r x) = x) (consistent : P41PartialCauchy.Consistent add D φ)
    (antisymmetric : ∀ t, D t → φ t + φ (neg t) = 0)
    (merge : ∀ x y, ∃ t a b, D t ∧ D a ∧ D b ∧ D (neg t) ∧
      add t a = x ∧ add b (neg t) = y ∧ add a b = add x y)
    (x y : G),
    P41PartialCauchy.extend φ l r (add x y) = P41PartialCauchy.extend φ l r x + P41PartialCauchy.extend φ l r y) :=
  ⟨@P41PartialCauchy.bridge_consistent, @P41PartialCauchy.extension_additive⟩

end Submissions.J4P41PartialCauchy.Proof
