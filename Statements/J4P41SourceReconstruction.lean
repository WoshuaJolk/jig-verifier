import Init

namespace Statements.J4P41SourceReconstruction


namespace P41Reconstruction

def OrdinarySidon (S : Int → Prop) : Prop :=
  ∀ a b c d, S a → S b → S c → S d → a+b=c+d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

def tri (h d : Int) : Int := if d<h then h-d else 0

def windowSquare (k : Int) (ds : List Int) (h : Int) : Int :=
  k*h+2*(ds.map (tri h)).sum

end P41Reconstruction

abbrev statement : Prop :=
  (∀ (S : Int → Prop) (hs : P41Reconstruction.OrdinarySidon S)
    (x y a0 b0 a1 b1 a b : Int) (hxy : x ≠ y)
    (ha0 : S a0) (hb0 : S b0) (ha1 : S a1) (hb1 : S b1)
    (ha : S a) (hb : S b)
    (h0 : x-a0=y-b0) (h1 : x-a1=b1-y)
    (hm : x-a=y-b ∨ x-a=b-y),
    (a=a0 ∧ b=b0) ∨ (a=a1 ∧ b=b1) ∨ (a=b1 ∧ b=a1)) ∧
  (∀ (k r delta : Int) (hr : 0 ≤ r)
    (hbasin : 9*r ≤ k) (hdelta : 2*k*r-9*r*r+r ≤ delta),
    k*r ≤ delta) ∧
  (∀ (k h : Int) (ds : List Int),
    P41Reconstruction.windowSquare k ds (h+1)-2*P41Reconstruction.windowSquare k ds h+P41Reconstruction.windowSquare k ds (h-1) =
      2*(ds.map (fun d => if d=h then 1 else 0)).sum)

theorem target : statement := sorry

end Statements.J4P41SourceReconstruction
