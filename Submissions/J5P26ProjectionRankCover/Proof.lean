import Init

namespace Submissions.J5P26ProjectionRankCover.Proof

universe u

def drop {V : Type u} [Zero V] (i row col : Fin 4) (x : V) : V :=
  if row=i ∨ col=i then x else 0

theorem three_mask_residual {V : Type u} [Zero V] (row col : Fin 4) (x : V) :
    drop 1 row col (drop 2 row col (drop 3 row col x))=0 := by
  have h : (row ≠ 1 ∧ col ≠ 1) ∨ (row ≠ 2 ∧ col ≠ 2) ∨ (row ≠ 3 ∧ col ≠ 3) := by
    omega
  cases h with
  | inl h => simp_all [drop]
  | inr h =>
    cases h with
    | inl h => simp_all [drop]
    | inr h => simp_all [drop]

theorem cover_identity {V : Type u} [Lean.Grind.IntModule V]
    (e1 e2 e3 : V -> V) (q : V)
    (s1 : forall x y, e1 (x-y)=e1 x-e1 y)
    (s2 : forall x y, e2 (x-y)=e2 x-e2 y)
    (hz : (q-e3 q)-e2 (q-e3 q)-e1 ((q-e3 q)-e2 (q-e3 q))=0) :
    q=(e1 q+(e2 q-e1 (e2 q)))+
      ((e3 q-e2 (e3 q))-e1 (e3 q-e2 (e3 q))) := by
  simp only [s1,s2] at hz ⊢
  grind

theorem three_projection_rank_cover {V : Type u} [Lean.Grind.IntModule V]
    (rho : V -> Nat) (e1 e2 e3 : V -> V) (q : V)
    (s1 : forall x y, e1 (x-y)=e1 x-e1 y)
    (s2 : forall x y, e2 (x-y)=e2 x-e2 y)
    (radd : forall x y, rho (x+y)<=rho x+rho y)
    (rsub : forall x y, rho (x-y)<=rho x+rho y)
    (r1 : forall x, rho (e1 x)<=rho x)
    (r2 : forall x, rho (e2 x)<=rho x)
    (hz : (q-e3 q)-e2 (q-e3 q)-e1 ((q-e3 q)-e2 (q-e3 q))=0)
    (a b c : Nat) (ha : rho (e1 q)<=a) (hb : rho (e2 q)<=b)
    (hc : rho (e3 q)<=c) : rho q<=a+2*b+4*c := by
  have hcover := cover_identity e1 e2 e3 q s1 s2 hz
  have hb1 := rsub (e2 q) (e1 (e2 q))
  have hb2 := r1 (e2 q)
  have hcb := rsub (e3 q) (e2 (e3 q))
  have hc2 := r2 (e3 q)
  have hc3 := rsub (e3 q-e2 (e3 q)) (e1 (e3 q-e2 (e3 q)))
  have hc4 := r1 (e3 q-e2 (e3 q))
  have hs1 := radd (e1 q) (e2 q-e1 (e2 q))
  have hs2 := radd (e1 q+(e2 q-e1 (e2 q)))
      ((e3 q-e2 (e3 q))-e1 (e3 q-e2 (e3 q)))
  rw [← hcover] at hs2
  omega

theorem direct_error_identity {V : Type u} [Lean.Grind.IntModule V]
    (f shifted x b : V) :
    f-b=(f-(shifted-x))+(shifted-x-b) := by
  grind

theorem solves :
  (∀ {V : Type u} [Lean.Grind.IntModule V]
    (rho : V -> Nat) (e1 e2 e3 : V -> V) (q : V)
    (s1 : forall x y, e1 (x-y)=e1 x-e1 y)
    (s2 : forall x y, e2 (x-y)=e2 x-e2 y)
    (radd : forall x y, rho (x+y)<=rho x+rho y)
    (rsub : forall x y, rho (x-y)<=rho x+rho y)
    (r1 : forall x, rho (e1 x)<=rho x)
    (r2 : forall x, rho (e2 x)<=rho x)
    (hz : (q-e3 q)-e2 (q-e3 q)-e1 ((q-e3 q)-e2 (q-e3 q))=0)
    (a b c : Nat) (ha : rho (e1 q)<=a) (hb : rho (e2 q)<=b)
    (hc : rho (e3 q)<=c), rho q<=a+2*b+4*c) ∧
  (∀ {V : Type u} [Zero V] (row col : Fin 4) (x : V), drop 1 row col (drop 2 row col (drop 3 row col x))=0) := by
  exact ⟨@three_projection_rank_cover, @three_mask_residual⟩

end Submissions.J5P26ProjectionRankCover.Proof
