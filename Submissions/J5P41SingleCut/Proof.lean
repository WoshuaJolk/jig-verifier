import Init

namespace Submissions.J5P41SingleCut.Proof


namespace SingleCut

def Edge (k i j : Nat) : Prop := i < j ∧ j < k
def Cross (c i j : Nat) : Prop := i ≤ c ∧ c < j
instance (c i j : Nat) : Decidable (Cross c i j) :=
  inferInstanceAs (Decidable (i ≤ c ∧ c < j))
def Shift (a : Nat → Int) (c : Nat) (h : Int) (i : Nat) : Int :=
  a i - if c < i then h else 0
def Unique (a : Nat → Int) (k : Nat) : Prop :=
  ∀ i j l m, Edge k i j → Edge k l m → a j-a i=a m-a l → i=l ∧ j=m
def NoCollision (a : Nat → Int) (k c : Nat) (h : Int) : Prop :=
  ∀ i j l m, Edge k i j → Edge k l m → Cross c i j → ¬Cross c l m →
    a j-a i-h ≠ a m-a l

theorem difference_formula (a : Nat → Int) (c i j : Nat) (h : Int) (hij : i<j) :
    Shift a c h j - Shift a c h i = a j-a i-(if Cross c i j then h else 0) := by
  by_cases hi : c<i
  · have hj : c<j := by omega
    have hn : ¬Cross c i j := by simp only [Cross]; omega
    simp only [Shift,if_pos hi,if_pos hj,if_neg hn,Int.sub_zero] <;> omega
  · by_cases hj : c<j
    · have hc : Cross c i j := by exact ⟨by omega,hj⟩
      simp only [Shift,if_neg hi,if_pos hj,if_pos hc,Int.sub_zero] <;> omega
    · have hn : ¬Cross c i j := by simp only [Cross]; omega
      simp only [Shift,if_neg hi,if_neg hj,if_neg hn,Int.sub_zero] <;> omega

theorem unique_shift_iff (a : Nat → Int) (k c : Nat) (h : Int)
    (original : Unique a k) : Unique (Shift a c h) k ↔ NoCollision a k c h := by
  constructor
  · intro shifted i j l m he hf hc hn same
    have f := difference_formula a c i j h he.1
    have g := difference_formula a c l m h hf.1
    simp only [if_pos hc] at f
    simp only [if_neg hn, Int.sub_zero] at g
    have pairs := shifted i j l m he hf (by omega)
    rcases pairs with ⟨rfl,rfl⟩
    exact hn hc
  · intro separate i j l m he hf same
    have f := difference_formula a c i j h he.1
    have g := difference_formula a c l m h hf.1
    by_cases hc : Cross c i j <;> by_cases hd : Cross c l m
    · simp only [if_pos hc] at f
      simp only [if_pos hd] at g
      exact original i j l m he hf (by omega)
    · simp only [if_pos hc] at f
      simp only [if_neg hd, Int.sub_zero] at g
      exact False.elim (separate i j l m he hf hc hd (by omega))
    · simp only [if_neg hc, Int.sub_zero] at f
      simp only [if_pos hd] at g
      exact False.elim (separate l m i j hf he hd hc (by omega))
    · simp only [if_neg hc, Int.sub_zero] at f
      simp only [if_neg hd, Int.sub_zero] at g
      exact original i j l m he hf (by omega)

theorem shifted_positive (a : Nat → Int) (k c : Nat) (h : Int)
    (positive : ∀ i j, Edge k i j → 0<a j-a i)
    (cross_room : ∀ i j, Edge k i j → Cross c i j → h<a j-a i) :
    ∀ i j, Edge k i j → 0<Shift a c h j-Shift a c h i := by
  intro i j he
  have f := difference_formula a c i j h he.1
  by_cases hc : Cross c i j
  · simp only [if_pos hc] at f
    have hp := cross_room i j he hc
    omega
  · simp only [if_neg hc, Int.sub_zero] at f
    have hp := positive i j he
    omega

def Sidon (D : Int → Prop) : Prop :=
  ∀ a b c d, D a → D b → D c → D d → a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

theorem two_shifted_force_outsider (D : Int → Prop) (hs : Sidon D)
    (x y h : Int) (hx : D x) (hy : D y) (different : x≠y) (nonzero : h≠0) :
    ¬D (x+h) ∨ ¬D (y+h) := by
  by_cases hu : D (x+h)
  · right
    intro hv
    have pairs := hs x (y+h) y (x+h) hx hv hy hu (by omega)
    rcases pairs with pair | pair <;> omega
  · exact Or.inl hu

theorem carry_to_small_side (k E triples lost removed moved : Int)
    (carry : k-24*E-12≤5*triples)
    (cover : triples≤4*lost) (overlap : lost≤removed+moved) :
    k-24*E-12≤20*(removed+moved) := by omega

theorem no_outsider_under_threshold (k E triples lost removed moved : Int)
    (carry : k-24*E-12≤5*triples)
    (cover : triples≤4*lost) (overlap : lost≤removed+moved)
    (small : 20*(removed+moved)<k-24*E-12) : False := by omega

end SingleCut

/-- Existing cut-shift equivalence and its separate positivity implication. -/
theorem proof :
  ∀ (a : Nat → Int) (k c : Nat) (h : Int),
    (SingleCut.Unique a k →
      (SingleCut.Unique (SingleCut.Shift a c h) k ↔ SingleCut.NoCollision a k c h)) ∧
    ((∀ i j, SingleCut.Edge k i j → 0 < a j - a i) →
      (∀ i j, SingleCut.Edge k i j → SingleCut.Cross c i j → h < a j - a i) →
      ∀ i j, SingleCut.Edge k i j → 0 < SingleCut.Shift a c h j - SingleCut.Shift a c h i)
 := by
  intro a k c h
  exact ⟨SingleCut.unique_shift_iff a k c h, SingleCut.shifted_positive a k c h⟩

end Submissions.J5P41SingleCut.Proof
