import Init

namespace Statements.J4P41QuadraticCollision


namespace P41CompressedQuadratic

def mark (p t : Int) : Int := p*t+(t*t)%p

def lift (p b t : Int) : Int := b*t+(t*t)%p

end P41CompressedQuadratic

abbrev statement : Prop :=
  (∀ (p m n : Int) (hn : 16 ≤ n)
    (odd : p=2*m+1) (lower : n*n < p) (upper : p < (n+1)*(n+1)),
    ∃ s t : Int, 0 ≤ t ∧ t+2 < s ∧ s+1 < p ∧
      P41CompressedQuadratic.mark p (s+1)-P41CompressedQuadratic.mark p s=P41CompressedQuadratic.mark p (t+2)-P41CompressedQuadratic.mark p t) ∧
  (∀ (p m n c : Int) (hn : 16 ≤ n)
    (odd : p=2*m+1) (lower : n*n < p) (upper : p < (n+1)*(n+1))
    (hc : 0 ≤ c) (room : 3*c+12*n+6 ≤ p),
    ∃ s t : Int, 0 ≤ t ∧ t+2 < s ∧ s+1 < p ∧
      P41CompressedQuadratic.lift p (p+c) (s+1)-P41CompressedQuadratic.lift p (p+c) s=
        P41CompressedQuadratic.lift p (p+c) (t+2)-P41CompressedQuadratic.lift p (p+c) t) ∧
  (∀ (p b x y : Int) (hp : 0 < p) (hb : p ≤ b) (hxy : x < y),
    P41CompressedQuadratic.lift p b x < P41CompressedQuadratic.lift p b y)

theorem target : statement := sorry

end Statements.J4P41QuadraticCollision
