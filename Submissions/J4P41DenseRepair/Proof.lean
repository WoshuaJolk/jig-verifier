import Init


namespace Submissions.J4P41DenseRepair.Proof.P41DenseDefects

theorem strict_coordinates (T : Nat → Prop) (x : Nat → Int)
    (rho : Nat → Nat → Int)
    (pos : ∀ i j, T i → T j → i<j → 0<rho i j)
    (correct : ∀ i j, T i → T j → i<j → x j-x i=rho i j)
    (i j : Nat) (hi : T i) (hj : T j) (hij : i<j) : x i<x j := by
  have hp := pos i j hi hj hij
  have hc := correct i j hi hj hij
  omega

theorem coordinate_injective (T : Nat → Prop) (x : Nat → Int)
    (strict : ∀ i j, T i → T j → i<j → x i<x j)
    (i j : Nat) (hi : T i) (hj : T j) (he : x i=x j) : i=j := by
  by_cases h : i<j
  · have hh := strict i j hi hj h
    omega
  · by_cases h' : j<i
    · have hh := strict j i hj hi h'
      omega
    · omega

theorem index_order_of_coordinates (T : Nat → Prop) (x : Nat → Int)
    (strict : ∀ i j, T i → T j → i<j → x i<x j)
    (i j : Nat) (hi : T i) (hj : T j) (he : x i<x j) : i<j := by
  by_cases h : j<i
  · have hh := strict j i hj hi h
    omega
  · by_cases heq : i=j
    · subst j
      omega
    · omega

-- The complete retained graph gives genuine ordinary Sidonicity. No
-- distinctness of a,b,c,d is assumed, so doubled summands are covered.
theorem correct_clique_sidon (T : Nat → Prop) (x : Nat → Int)
    (rho : Nat → Nat → Int)
    (pos : ∀ i j, T i → T j → i<j → 0<rho i j)
    (correct : ∀ i j, T i → T j → i<j → x j-x i=rho i j)
    (unique : ∀ i j l m, T i → T j → T l → T m → i<j → l<m →
      rho i j=rho l m → i=l ∧ j=m)
    (a b c d : Nat) (ha : T a) (hb : T b) (hc : T c) (hd : T d)
    (hsum : x a+x b=x c+x d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have strict := strict_coordinates T x rho pos correct
  by_cases hac : a=c
  · subst c
    have hbd : b=d := coordinate_injective T x strict b d hb hd (by omega)
    exact Or.inl ⟨rfl,hbd⟩
  · by_cases hlt : a<c
    · have hxa := strict a c ha hc hlt
      have hdb := index_order_of_coordinates T x strict d b hd hb (by omega)
      have h1 := correct a c ha hc hlt
      have h2 := correct d b hd hb hdb
      have hu := unique a c d b ha hc hd hb hlt hdb (by omega)
      exact Or.inr ⟨hu.1,hu.2.symm⟩
    · have hca : c<a := by omega
      have hxc := strict c a hc ha hca
      have hbd := index_order_of_coordinates T x strict b d hb hd (by omega)
      have h1 := correct c a hc ha hca
      have h2 := correct b d hb hd hbd
      have hu := unique c a b d hc ha hb hd hca hbd (by omega)
      exact Or.inr ⟨hu.2,hu.1.symm⟩

-- The retained indices also recover a subset of the original source when
-- their anchor edges have not been edited. Selection is a separate paper step.
theorem original_clique_sidon (T : Nat → Prop) (x : Nat → Int)
    (rho : Nat → Nat → Int) (anchor : Nat)
    (pos : ∀ i j, T i → T j → i<j → 0<rho i j)
    (unique : ∀ i j l m, T i → T j → T l → T m → i<j → l<m →
      rho i j=rho l m → i=l ∧ j=m)
    (ha : ∀ i, T i → rho anchor i=x i-x anchor)
    (hc : ∀ i j, T i → T j → i<j →
      rho anchor j-rho anchor i=rho i j)
    (a b c d : Nat) (hta : T a) (htb : T b) (htc : T c) (htd : T d)
    (hsum : x a+x b=x c+x d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  apply correct_clique_sidon T x rho pos _ unique a b c d hta htb htc htd hsum
  intro i j hi hj hij
  have h1 := ha i hi
  have h2 := ha j hj
  have h3 := hc i j hi hj hij
  omega

def WeakSidon (S : Int → Prop) : Prop :=
  ∀ a b c d, S a → S b → S c → S d → a<b → c<d →
    a+b=c+d → a=c ∧ b=d

def NoAP (S : Int → Prop) : Prop :=
  ∀ a b c, S a → S b → S c → a<b → b<c → a+c≠2*b

-- A formal port of the elementary weak-Sidon/AP-free characterization,
-- credited to the cited literature, not a new mathematical discovery.
theorem ordered_sidon (S : Int → Prop) (hw : WeakSidon S) (hn : NoAP S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hab : a≤b) (hcd : c≤d) (hs : a+b=c+d) : a=c ∧ b=d := by
  by_cases he : a=b
  · by_cases hf : c=d
    · omega
    · have h1 : c<a := by omega
      have h2 : a<d := by omega
      have h3 := hn c a d hc ha hd h1 h2
      omega
  · by_cases hf : c=d
    · have h1 : a<c := by omega
      have h2 : c<b := by omega
      have h3 := hn a c b ha hc hb h1 h2
      omega
    · exact hw a b c d ha hb hc hd (by omega) (by omega) hs

theorem weak_noAP_sidon (S : Int → Prop) (hw : WeakSidon S) (hn : NoAP S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hs : a+b=c+d) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  by_cases hab : a≤b
  · by_cases hcd : c≤d
    · exact Or.inl (ordered_sidon S hw hn a b c d ha hb hc hd hab hcd hs)
    · exact Or.inr (ordered_sidon S hw hn a b d c ha hb hd hc hab (by omega) (by omega))
  · by_cases hcd : c≤d
    · have h := ordered_sidon S hw hn b a c d hb ha hc hd (by omega) hcd (by omega)
      exact Or.inr ⟨h.2,h.1⟩
    · have h := ordered_sidon S hw hn b a d c hb ha hd hc (by omega) (by omega) (by omega)
      exact Or.inl ⟨h.2,h.1⟩

theorem repeated_difference_is_AP (S : Int → Prop) (hw : WeakSidon S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hab : a<b) (hcd : c<d) (hac : a<c) (he : b-a=d-c) : b=c := by
  by_cases hbc : b<c
  · have h := hw a d b c ha hd hb hc (by omega) hbc (by omega)
    omega
  · by_cases hcb : c<b
    · have h := hw a d c b ha hd hc hb (by omega) hcb (by omega)
      omega
    · omega

theorem anchor_original_budget (k tau changes errors degree removed : Int)
    (hk : 0≤k) (ha : k*(errors+degree)≤3*tau+2*changes)
    (hr : removed≤errors+degree) : k*removed≤3*tau+2*changes := by
  have hh := Int.mul_le_mul_of_nonneg_left hr hk
  omega

theorem general_metric_lower (k r sq agree changes edits : Int)
    (hclass : sq≤k*(k-r)) (hagree : 2*agree=sq-k)
    (hcompare : k*(k-1)≤2*(agree+changes+edits)) :
    k*r≤2*(changes+edits) := by grind


end Submissions.J4P41DenseRepair.Proof.P41DenseDefects

namespace Submissions.J4P41DenseRepair.Proof

theorem proof :
  (∀ (T : Nat → Prop) (x : Nat → Int)
    (rho : Nat → Nat → Int) (anchor : Nat)
    (pos : ∀ i j, T i → T j → i<j → 0<rho i j)
    (unique : ∀ i j l m, T i → T j → T l → T m → i<j → l<m →
      rho i j=rho l m → i=l ∧ j=m)
    (ha : ∀ i, T i → rho anchor i=x i-x anchor)
    (hc : ∀ i j, T i → T j → i<j →
      rho anchor j-rho anchor i=rho i j)
    (a b c d : Nat) (hta : T a) (htb : T b) (htc : T c) (htd : T d)
    (hsum : x a+x b=x c+x d),
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)) ∧
  (∀ (S : Int → Prop) (hw : P41DenseDefects.WeakSidon S) (hn : P41DenseDefects.NoAP S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hs : a+b=c+d),
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)) ∧
  (∀ (S : Int → Prop) (hw : P41DenseDefects.WeakSidon S)
    (a b c d : Int) (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (hab : a<b) (hcd : c<d) (hac : a<c) (he : b-a=d-c),
    b=c) ∧
  (∀ (k r sq agree changes edits : Int)
    (hclass : sq≤k*(k-r)) (hagree : 2*agree=sq-k)
    (hcompare : k*(k-1)≤2*(agree+changes+edits)),
    k*r≤2*(changes+edits)) :=
  ⟨@P41DenseDefects.original_clique_sidon, @P41DenseDefects.weak_noAP_sidon, @P41DenseDefects.repeated_difference_is_AP, @P41DenseDefects.general_metric_lower⟩

end Submissions.J4P41DenseRepair.Proof
