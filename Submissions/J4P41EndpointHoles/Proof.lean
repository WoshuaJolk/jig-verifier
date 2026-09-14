import Init

namespace Submissions.J4P41EndpointHoles.Proof.P41Endpoint

def PosDiff (A : Int → Prop) (h : Int) : Prop :=
  0 < h ∧ ∃ a b, A a ∧ A b ∧ b-a=h

def label (V d : Int) : Int := if 0 < d then d else V+d

theorem label_eq_emod (V d : Int) (hd : -V < d ∧ d < V) (hne : d ≠ 0) :
    label V d = d % V := by
  by_cases hp : 0 < d
  · simp only [label, if_pos hp]
    exact (Int.emod_eq_of_lt (by omega) hd.2).symm
  · have hs : (V+d) % V = V+d := Int.emod_eq_of_lt (by omega) (by omega)
    rw [Int.add_emod_left] at hs
    simp only [label, if_neg hp]
    exact hs.symm

def CyclicUnique (A : Int → Prop) (V : Int) : Prop :=
  ∀ a b c d, A a → A b → A c → A d → a ≠ b → c ≠ d →
    label V (b-a) = label V (d-c) → a=c ∧ b=d

def CyclicComplete (A : Int → Prop) (V : Int) : Prop :=
  ∀ h, 0 < h → h < V → ∃ a b, A a ∧ A b ∧ a ≠ b ∧ label V (b-a)=h

theorem complement_exclusion (A : Int → Prop) (V h : Int)
    (hu : CyclicUnique A V) (hh : 0 < h) (hv : h < V) :
    ¬ (PosDiff A h ∧ PosDiff A (V-h)) := by
  rintro ⟨⟨_,a,b,ha,hb,hab⟩,⟨_,c,d,hc,hd,hcd⟩⟩
  have hl : label V (b-a) = label V (c-d) := by
    simp only [label, if_pos (by omega : 0 < b-a), if_neg (by omega : ¬ 0 < c-d)]
    omega
  have he := hu a b d c ha hb hd hc (by omega) (by omega) hl
  omega

theorem complement_coverage (A : Int → Prop) (V h : Int)
    (hc : CyclicComplete A V) (hh : 0 < h) (hv : h < V) :
    PosDiff A h ∨ PosDiff A (V-h) := by
  obtain ⟨a,b,ha,hb,hab,hl⟩ := hc h hh hv
  by_cases hp : 0 < b-a
  · simp only [label, if_pos hp] at hl
    exact Or.inl ⟨hh,a,b,ha,hb,hl⟩
  · simp only [label, if_neg hp] at hl
    exact Or.inr ⟨by omega,b,a,hb,ha,by omega⟩

theorem perfect_hole_iff (A : Int → Prop) (V h : Int)
    (hu : CyclicUnique A V) (hc : CyclicComplete A V)
    (hh : 0 < h) (hv : h < V) :
    (¬ PosDiff A h) ↔ PosDiff A (V-h) := by
  constructor
  · intro hn
    exact (complement_coverage A V h hc hh hv).resolve_left hn
  · intro he hs
    exact complement_exclusion A V h hu hh hv ⟨hs,he⟩

theorem endpoint_reflection (A : Int → Prop) (V L G h : Int)
    (hV : V=L+G) (hh : h < V) :
    PosDiff A (V-h) ↔ ∃ a b, A a ∧ A b ∧ a+(L-b)=h-G := by
  constructor
  · rintro ⟨_,a,b,ha,hb,he⟩
    exact ⟨a,b,ha,hb,by omega⟩
  · rintro ⟨a,b,ha,hb,he⟩
    exact ⟨by omega,a,b,ha,hb,by omega⟩

theorem first_hole (A : Int → Prop) (V L G : Int)
    (hu : CyclicUnique A V) (hc : CyclicComplete A V)
    (hV : V=L+G) (hL : 0 < L) (hG : 0 < G)
    (h0 : A 0) (hmax : A L) (hbound : ∀ a, A a → 0 ≤ a ∧ a ≤ L) :
    (¬ PosDiff A G) ∧ (∀ h, 0 < h → h < G → PosDiff A h) := by
  have hlong : PosDiff A (V-G) := ⟨by omega,0,L,h0,hmax,by omega⟩
  constructor
  · intro hp
    exact complement_exclusion A V G hu hG (by omega) ⟨hp,hlong⟩
  · intro h hh hg
    rcases complement_coverage A V h hc hh (by omega) with hp | hp
    · exact hp
    · obtain ⟨_,a,b,ha,hb,he⟩ := hp
      have ha' := hbound a ha
      have hb' := hbound b hb
      omega

theorem modular_hole_partition (short long missing : Bool)
    (hcount : (if short then 1 else 0) + (if long then 1 else 0) +
      (if missing then 1 else 0) = (1 : Int)) :
    (if short then 0 else 1) =
      (if long then 1 else 0) + (if missing then 1 else 0) := by
  cases short <;> cases long <;> cases missing <;> simp_all

theorem endpoint_weight (V L G H a b : Int) (hV : V=L+G) :
    H-(V-(b-a)) = H-G-a-(L-b) := by omega

theorem endpoint_weight_positive (G T a c : Int)
    (ha : a ≤ T) (hc : c ≤ T) :
    T ≤ G+3*T-G-a-c := by omega

theorem perfect_excess_identity (k V G N : Int)
    (hV : V=k*(k-1)+1) (hN : N=V-G+1) :
    k^2-N=k+G-2 := by grind

theorem zero_hole_test_scale (k G H : Int) (hk : 2 ≤ k) (hg : k ≤ G)
    (hh : 4*H ≤ k+G-2) : H < G := by omega

end Submissions.J4P41EndpointHoles.Proof.P41Endpoint

namespace Submissions.J4P41EndpointHoles.Proof

theorem proof :
  (∀ (V d : Int) (hd : -V < d ∧ d < V) (hne : d ≠ 0),
    P41Endpoint.label V d = d % V) ∧
  (∀ (A : Int → Prop) (V h : Int)
    (hu : P41Endpoint.CyclicUnique A V) (hc : P41Endpoint.CyclicComplete A V)
    (hh : 0 < h) (hv : h < V),
    (¬ P41Endpoint.PosDiff A h) ↔ P41Endpoint.PosDiff A (V-h)) ∧
  (∀ (A : Int → Prop) (V L G h : Int)
    (hV : V=L+G) (hh : h < V),
    P41Endpoint.PosDiff A (V-h) ↔ ∃ a b, A a ∧ A b ∧ a+(L-b)=h-G) ∧
  (∀ (A : Int → Prop) (V L G : Int)
    (hu : P41Endpoint.CyclicUnique A V) (hc : P41Endpoint.CyclicComplete A V)
    (hV : V=L+G) (hL : 0 < L) (hG : 0 < G)
    (h0 : A 0) (hmax : A L) (hbound : ∀ a, A a → 0 ≤ a ∧ a ≤ L),
    (¬ P41Endpoint.PosDiff A G) ∧ (∀ h, 0 < h → h < G → P41Endpoint.PosDiff A h)) :=
  ⟨@P41Endpoint.label_eq_emod, @P41Endpoint.perfect_hole_iff, @P41Endpoint.endpoint_reflection, @P41Endpoint.first_hole⟩

end Submissions.J4P41EndpointHoles.Proof
