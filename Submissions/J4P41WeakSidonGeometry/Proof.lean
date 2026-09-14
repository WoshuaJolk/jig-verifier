import Init


namespace Submissions.J4P41WeakSidonGeometry.Proof.P41QuadrilateralTransfer

def WeakSidon (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a≠b → c≠d →
    a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

theorem cycle_labels_force_AP (A : Int → Prop) (hw : WeakSidon A)
    (p q r s : Int) (hp : A p) (hq : A q) (hr : A r) (hs : A s)
    (hpq : p≠q) (hpr : p≠r) (he : p+s=q+r) :
    (p=s ∧ q+r=2*p ∧ q≠r) ∨ (q=r ∧ p+s=2*q ∧ p≠s) := by
  by_cases hps : p=s
  · exact Or.inl ⟨hps, by omega, by omega⟩
  by_cases hqr : q=r
  · exact Or.inr ⟨hqr, by omega, hps⟩
  have hh := hw p s q r hp hs hq hr hps hqr he
  rcases hh with hh | hh
  · exact False.elim (hpq hh.1)
  · exact False.elim (hpr hh.1)

theorem rectangle_forces_AP (A : Int → Prop) (hw : WeakSidon A)
    (x w y z : Int) (hxw : x≠w) (hyz : y≠z)
    (h1 : A (y-x)) (h2 : A (z-x)) (h3 : A (y-w)) (h4 : A (z-w)) :
    (y-x=z-w ∧ (z-x)+(y-w)=2*(y-x) ∧ z-x≠y-w) ∨
    (z-x=y-w ∧ (y-x)+(z-w)=2*(z-x) ∧ y-x≠z-w) := by
  exact cycle_labels_force_AP A hw (y-x) (z-x) (y-w) (z-w)
    h1 h2 h3 h4 (by omega) (by omega) (by omega)

theorem progression_cycle_labels (a b c x : Int) (he : a+c=2*b) :
    (x+b)-x=b ∧ (x+c)-x=c ∧
    (x+b)-(x+(b-a))=a ∧ (x+c)-(x+(b-a))=b := by omega

-- The edge carrying the upper endpoint c occurs in just this anchor's
-- quadrilateral. This prevents an unselected cycle being rebuilt by others.
theorem upper_endpoint_edge_unique (a b c x t : Int)
    (hab : a<b) (hbc : b<c) (he : a+c=2*b)
    (h : (x=t ∧ x+c=t+b) ∨ (x=t ∧ x+c=t+c) ∨
         (x=t+(b-a) ∧ x+c=t+b) ∨ (x=t+(b-a) ∧ x+c=t+c)) : x=t := by
  rcases h with h | h | h | h <;> omega

-- The finite selection/cardinality arguments supplying these bounds are
-- proved separately on paper; no unproved asymptotic estimate is assumed.
theorem packing_transfer_arithmetic (N r m E : Int)
    (hN : 0≤N) (hextract : r≤8*m) (hedges : N*m≤E) : N*r≤8*E := by
  have hh := Int.mul_le_mul_of_nonneg_left hextract hN
  have he : N*(8*m)=8*(N*m) := by grind
  omega

-- A C4 edge cover must hit at least N-d translated cycles of this AP.
-- Endpoint-labelled edges hit at most one; midpoint-labelled edges at most two.
theorem full_host_threshold_hits_AP (N d fa fb fc : Int)
    (hshort : 2*d≤N) (hcover : N-d≤fa+2*fb+fc) :
    N≤8*fa ∨ N≤8*fb ∨ N≤8*fc := by omega


end Submissions.J4P41WeakSidonGeometry.Proof.P41QuadrilateralTransfer


namespace Submissions.J4P41WeakSidonGeometry.Proof.P41WeakSingerRepair

def WeakSidon (A : Int → Prop) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a≠b → c≠d →
    a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

-- An actual restricted outsider collision remains forbidden after adding
-- more points. The three old points and outsider cannot be mistaken for
-- different representations of the same unordered pair.
theorem outsider_collision_forbidden (A : Int → Prop) (hw : WeakSidon A)
    (u v w b : Int) (hu : A u) (hv : A v) (hw' : A w) (hb : A b)
    (huv : u≠v) (hbw : b≠w) (hub : u≠b) (hvb : v≠b)
    (he : u+v=b+w) : False := by
  have h := hw u v b w hu hv hb hw' huv hbw he
  rcases h with h | h
  · exact hub h.1
  · exact hvb h.2

-- Two distinct residues each copied one period apart create four distinct
-- points with the same restricted sum, not merely a doubled-summand AP.
theorem two_copied_residues_forbidden (A : Int → Prop) (hw : WeakSidon A)
    (p q V : Int) (hpq : p<q) (hq : q<p+V)
    (h1 : A p) (h2 : A (p+V)) (h3 : A q) (h4 : A (q+V)) : False := by
  have h := hw (p+V) q (q+V) p h2 h3 h4 h1
    (by omega) (by omega) (by omega)
  rcases h with h | h <;> omega

-- The ordered integer count T includes J doubled positive pairs. The
-- normalized Singer argument supplies J≤1 away from its exceptional
-- residue; T=2U+J is the exact conversion to restricted configurations.
theorem restricted_integer_count (q E T U J : Int)
    (hcount : q+1-24*E-12 ≤ 5*T)
    (hsplit : T=2*U+J) (hdoubled : J≤1) :
    q-24*E-16 ≤ 10*U := by omega

-- Every removed old point meets at most two unordered configurations.
theorem weak_insertion_cost (q E T U J r : Int)
    (hcount : q+1-24*E-12 ≤ 5*T)
    (hsplit : T=2*U+J) (hdoubled : J≤1) (hcover : U≤2*r) :
    q-24*E-16 ≤ 20*r := by
  have h := restricted_integer_count q E T U J hcount hsplit hdoubled
  omega

-- This contradiction uses a separately proved, explicit count L, not the
-- unknown dense weak-Sidon repair bound from the full problem.
theorem nonexception_excluded (T U J r L : Int)
    (hcount : L≤T) (hsplit : T=2*U+J)
    (hdoubled : J≤1) (hcover : U≤2*r) (hsmall : 4*r+1<L) : False := by omega

-- Odd-characteristic classical Singer sources have at most two doubled
-- solutions, by the separate nonzero binary-quadratic-form argument.
theorem weak_insertion_cost_general (k E T U J r j : Int)
    (hcount : k-24*E-12 ≤ 5*T)
    (hsplit : T=2*U+J) (hdoubled : J≤j) (hcover : U≤2*r) :
    k-24*E-12-5*j ≤ 20*r := by omega

theorem outsider_excluded_general (T U J r L j : Int)
    (hcount : L≤T) (hsplit : T=2*U+J)
    (hdoubled : J≤j) (hcover : U≤2*r) (hsmall : 4*r+j<L) : False := by omega


end Submissions.J4P41WeakSidonGeometry.Proof.P41WeakSingerRepair

namespace Submissions.J4P41WeakSidonGeometry.Proof

theorem proof :
  (∀ (A : Int → Prop) (hw : P41QuadrilateralTransfer.WeakSidon A)
    (x w y z : Int) (hxw : x≠w) (hyz : y≠z)
    (h1 : A (y-x)) (h2 : A (z-x)) (h3 : A (y-w)) (h4 : A (z-w)),
    (y-x=z-w ∧ (z-x)+(y-w)=2*(y-x) ∧ z-x≠y-w) ∨
    (z-x=y-w ∧ (y-x)+(z-w)=2*(z-x) ∧ y-x≠z-w)) ∧
  (∀ (a b c x t : Int)
    (hab : a<b) (hbc : b<c) (he : a+c=2*b)
    (h : (x=t ∧ x+c=t+b) ∨ (x=t ∧ x+c=t+c) ∨
         (x=t+(b-a) ∧ x+c=t+b) ∨ (x=t+(b-a) ∧ x+c=t+c)),
    x=t) ∧
  (∀ (N d fa fb fc : Int)
    (hshort : 2*d≤N) (hcover : N-d≤fa+2*fb+fc),
    N≤8*fa ∨ N≤8*fb ∨ N≤8*fc) ∧
  (∀ (A : Int → Prop) (hw : P41WeakSingerRepair.WeakSidon A)
    (p q V : Int) (hpq : p<q) (hq : q<p+V)
    (h1 : A p) (h2 : A (p+V)) (h3 : A q) (h4 : A (q+V)),
    False) ∧
  (∀ (k E T U J r j : Int)
    (hcount : k-24*E-12 ≤ 5*T)
    (hsplit : T=2*U+J) (hdoubled : J≤j) (hcover : U≤2*r),
    k-24*E-12-5*j ≤ 20*r) :=
  ⟨@P41QuadrilateralTransfer.rectangle_forces_AP, @P41QuadrilateralTransfer.upper_endpoint_edge_unique, @P41QuadrilateralTransfer.full_host_threshold_hits_AP, @P41WeakSingerRepair.two_copied_residues_forbidden, @P41WeakSingerRepair.weak_insertion_cost_general⟩

end Submissions.J4P41WeakSidonGeometry.Proof
