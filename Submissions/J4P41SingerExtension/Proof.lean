import Init


namespace Submissions.J4P41SingerExtension.Proof.P41SingerExtension

def Sidon {G : Type} (op : G → G → G) (D : G → Prop) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → op a b = op c d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

def WeakSidon {G : Type} (op : G → G → G) (D : G → Prop) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → a≠b → c≠d →
    op a b = op c d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

-- No finite-field existence assumption is formalized here. These abstract
-- hypotheses are separately obtained from the classical trace construction.
theorem zero_absent {G : Type} (op : G → G → G) (D : G → Prop) (z : G)
    (hz : ∀ x, op z x=x) (hs : Sidon op D)
    (hd : ∀ x, D x → D (op x x))
    (a : G) (ha : D a) (hne : a≠z) : ¬D z := by
  intro hzero
  have hh := hs a a z (op a a) ha ha hzero (hd a ha) (hz (op a a)).symm
  rcases hh with hh | hh
  · exact hne hh.1
  · exact hne hh.2

theorem restricted_sum_outside {G : Type} (op : G → G → G) (D : G → Prop)
    (hs : Sidon op D) (hd : ∀ x, D x → ∃ w, D w ∧ op w w=x)
    (a b : G) (ha : D a) (hb : D b) (hne : a≠b) : ¬D (op a b) := by
  intro hm
  obtain ⟨w,hw,he⟩ := hd (op a b) hm
  have hh := hs a b w w ha hb hw hw he.symm
  rcases hh with hh | hh
  · exact hne (hh.1.trans hh.2.symm)
  · exact hne (hh.1.trans hh.2.symm)

theorem adjoin_zero_weak {G : Type} (op : G → G → G) (D : G → Prop) (z : G)
    (hl : ∀ x, op z x=x) (hr : ∀ x, op x z=x)
    (hs : Sidon op D) (hd : ∀ x, D x → ∃ w, D w ∧ op w w=x) :
    WeakSidon op (fun x => D x ∨ x=z) := by
  intro a b c d ha hb hc hdd hab hcd he
  have hout := restricted_sum_outside op D hs hd
  rcases ha with ha | rfl <;> rcases hb with hb | rfl <;>
    rcases hc with hc | rfl <;> rcases hdd with hdd | rfl
  · exact hs a b c d ha hb hc hdd he
  · exact False.elim (hout a b ha hb hab (by rw [he, hr]; exact hc))
  · exact False.elim (hout a b ha hb hab (by rw [he, hl]; exact hdd))
  · exact False.elim (hcd rfl)
  · exact False.elim (hout c d hc hdd hcd (by rw [←he, hr]; exact ha))
  · exact Or.inl ⟨by simpa only [hr] using he, rfl⟩
  · exact Or.inr ⟨by simpa only [hr,hl] using he, rfl⟩
  · exact False.elim (hcd rfl)
  · exact False.elim (hout c d hc hdd hcd (by rw [←he, hl]; exact hb))
  · exact Or.inr ⟨rfl, by simpa only [hr,hl] using he⟩
  · exact Or.inl ⟨rfl, by simpa only [hl] using he⟩
  · exact False.elim (hcd rfl)
  · exact False.elim (hab rfl)
  · exact False.elim (hab rfl)
  · exact False.elim (hab rfl)
  · exact False.elim (hab rfl)

-- This is the actual integer AP obstruction after choosing representatives.
theorem AP_contains_added_point (D : Int → Prop) (z : Int)
    (hs : Sidon (fun a b : Int => a+b) D)
    (a b c : Int) (ha : D a ∨ a=z) (hb : D b ∨ b=z)
    (hc : D c ∨ c=z) (hab : a<b) (he : a+c=2*b) :
    a=z ∨ b=z ∨ c=z := by
  by_cases haz : a=z
  · exact Or.inl haz
  by_cases hbz : b=z
  · exact Or.inr (Or.inl hbz)
  by_cases hcz : c=z
  · exact Or.inr (Or.inr hcz)
  have h1 : D a := ha.resolve_right haz
  have h2 : D b := hb.resolve_right hbz
  have h3 : D c := hc.resolve_right hcz
  have hh := hs a c b b h1 h3 h2 h2 (by change a+c=b+b; omega)
  rcases hh with hh | hh <;> omega

-- Pigeonhole / incidence counts are supplied by the separate paper proof.
theorem weak_turnover_bound (q configs removed : Int)
    (hcount : 2*configs=q) (hhit : configs≤2*removed) :
    q≤4*removed := by omega


end Submissions.J4P41SingerExtension.Proof.P41SingerExtension

namespace Submissions.J4P41SingerExtension.Proof

theorem proof :
  (∀ {G : Type} (op : G → G → G) (D : G → Prop) (z : G)
    (hz : ∀ x, op z x=x) (hs : P41SingerExtension.Sidon op D)
    (hd : ∀ x, D x → D (op x x))
    (a : G) (ha : D a) (hne : a≠z),
    ¬D z) ∧
  (∀ {G : Type} (op : G → G → G) (D : G → Prop)
    (hs : P41SingerExtension.Sidon op D) (hd : ∀ x, D x → ∃ w, D w ∧ op w w=x)
    (a b : G) (ha : D a) (hb : D b) (hne : a≠b),
    ¬D (op a b)) ∧
  (∀ {G : Type} (op : G → G → G) (D : G → Prop) (z : G)
    (hl : ∀ x, op z x=x) (hr : ∀ x, op x z=x)
    (hs : P41SingerExtension.Sidon op D) (hd : ∀ x, D x → ∃ w, D w ∧ op w w=x),
    P41SingerExtension.WeakSidon op (fun x => D x ∨ x=z)) ∧
  (∀ (D : Int → Prop) (z : Int)
    (hs : P41SingerExtension.Sidon (fun a b : Int => a+b) D)
    (a b c : Int) (ha : D a ∨ a=z) (hb : D b ∨ b=z)
    (hc : D c ∨ c=z) (hab : a<b) (he : a+c=2*b),
    a=z ∨ b=z ∨ c=z) :=
  ⟨@P41SingerExtension.zero_absent, @P41SingerExtension.restricted_sum_outside, @P41SingerExtension.adjoin_zero_weak, @P41SingerExtension.AP_contains_added_point⟩

end Submissions.J4P41SingerExtension.Proof
