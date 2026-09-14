import Init

namespace Submissions.J4P16PathClosure.Proof

def DistinctFive {X : Type} (a b c d e : X) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e

def DisjointEdges {X : Type} (a b c d : X) : Prop :=
  a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

def DegreeTwo {X : Type} (E : X → X → Prop) : Prop :=
  ∀ x a b c, E x a → E x b → E x c → a ≠ b → a ≠ c → b ≠ c → False

def MatchingTwo {X : Type} (E : X → X → Prop) : Prop :=
  ∀ a b c d e f, E a b → E c d → E e f →
    DisjointEdges a b c d → DisjointEdges a b e f → DisjointEdges c d e f → False

theorem neighbor_pair {X : Type} {E : X → X → Prop} (degree : DegreeTwo E)
    {x a b c : X} (ha : E x a) (hb : E x b) (hab : a ≠ b) (hc : E x c) :
    c = a ∨ c = b := by
  classical
  by_cases hca : c = a
  · exact Or.inl hca
  by_cases hcb : c = b
  · exact Or.inr hcb
  exact False.elim (degree x a b c ha hb hc hab (Ne.symm hca) (Ne.symm hcb))

theorem endpoint_neighbors {X : Type} {E : X → X → Prop}
    (sym : ∀ {x y}, E x y → E y x) (loop : ∀ x, ¬ E x x)
    (degree : DegreeTwo E) (matching : MatchingTwo E)
    (a b c d e : X) (distinct : DistinctFive a b c d e)
    (_hab : E a b) (hbc : E b c) (hcd : E c d) (hde : E d e)
    {v : X} (hav : E a v) : v = b ∨ v = e := by
  classical
  rcases distinct with ⟨ab, ac, ad, ae, bc, bd, be, cd, ce, de⟩
  by_cases vb : v = b
  · exact Or.inl vb
  by_cases ve : v = e
  · exact Or.inr ve
  have va : v ≠ a := by
    intro h
    subst v
    exact loop a hav
  have vc : v ≠ c := by
    intro h
    subst v
    have h := neighbor_pair degree (sym hbc) hcd bd (sym hav)
    exact h.elim ab ad
  have vd : v ≠ d := by
    intro h
    subst v
    have h := neighbor_pair degree (sym hcd) hde ce (sym hav)
    exact h.elim ac ae
  exact False.elim (matching a v b c d e hav hbc hde
    ⟨ab, ac, vb, vc⟩ ⟨ad, ae, vd, ve⟩ ⟨bd, be, cd, ce⟩)

-- A four-edge path in a simple graph of maximum degree two and matching
-- number at most two exhausts its component and every other nonempty component.
-- Its only possible extra edge closes the five-cycle.
theorem path_five_exhausts {X : Type} {E : X → X → Prop}
    (sym : ∀ {x y}, E x y → E y x) (loop : ∀ x, ¬ E x x)
    (degree : DegreeTwo E) (matching : MatchingTwo E)
    (a b c d e : X) (distinct : DistinctFive a b c d e)
    (hab : E a b) (hbc : E b c) (hcd : E c d) (hde : E d e)
    {u v : X} (huv : E u v) :
    (u = a ∧ (v = b ∨ v = e)) ∨
    (u = b ∧ (v = a ∨ v = c)) ∨
    (u = c ∧ (v = b ∨ v = d)) ∨
    (u = d ∧ (v = c ∨ v = e)) ∨
    (u = e ∧ (v = d ∨ v = a)) := by
  classical
  have original := distinct
  rcases distinct with ⟨ab, ac, ad, ae, bc, bd, be, cd, ce, de⟩
  have reversed : DistinctFive e d c b a := by
    simp_all [DistinctFive, ne_comm]
  have na {t : X} (h : E a t) : t = b ∨ t = e :=
    endpoint_neighbors (E := E) sym loop degree matching a b c d e original hab hbc hcd hde h
  have nb {t : X} (h : E b t) : t = a ∨ t = c :=
    neighbor_pair degree (sym hab) hbc ac h
  have nc {t : X} (h : E c t) : t = b ∨ t = d :=
    neighbor_pair degree (sym hbc) hcd bd h
  have nd {t : X} (h : E d t) : t = c ∨ t = e :=
    neighbor_pair degree (sym hcd) hde ce h
  have ne {t : X} (h : E e t) : t = d ∨ t = a :=
    endpoint_neighbors (E := E) sym loop degree matching e d c b a reversed
      (sym hde) (sym hcd) (sym hbc) (sym hab) h
  by_cases ua : u = a
  · subst u; exact Or.inl ⟨rfl, na huv⟩
  by_cases ub : u = b
  · subst u; exact Or.inr (Or.inl ⟨rfl, nb huv⟩)
  by_cases uc : u = c
  · subst u; exact Or.inr (Or.inr (Or.inl ⟨rfl, nc huv⟩))
  by_cases ud : u = d
  · subst u; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, nd huv⟩)))
  by_cases ue : u = e
  · subst u; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ne huv⟩)))
  have va : v ≠ a := by
    intro h; subst v
    exact (na (sym huv)).elim ub ue
  have vb : v ≠ b := by
    intro h; subst v
    exact (nb (sym huv)).elim ua uc
  have vc : v ≠ c := by
    intro h; subst v
    exact (nc (sym huv)).elim ub ud
  have vd : v ≠ d := by
    intro h; subst v
    exact (nd (sym huv)).elim uc ue
  exact False.elim (matching u v a b c d huv hab hcd
    ⟨ua, ub, va, vb⟩ ⟨uc, ud, vc, vd⟩ ⟨ac, ad, bc, bd⟩)


theorem solves :
(∀ {X : Type} {E : X → X → Prop}
    (sym : ∀ {x y}, E x y → E y x) (loop : ∀ x, ¬ E x x)
    (degree : DegreeTwo E) (matching : MatchingTwo E)
    (a b c d e : X) (distinct : DistinctFive a b c d e)
    (hab : E a b) (hbc : E b c) (hcd : E c d) (hde : E d e)
    {u v : X} (huv : E u v),
(u = a ∧ (v = b ∨ v = e)) ∨
    (u = b ∧ (v = a ∨ v = c)) ∨
    (u = c ∧ (v = b ∨ v = d)) ∨
    (u = d ∧ (v = c ∨ v = e)) ∨
    (u = e ∧ (v = d ∨ v = a))) := by
  exact @path_five_exhausts

end Submissions.J4P16PathClosure.Proof
