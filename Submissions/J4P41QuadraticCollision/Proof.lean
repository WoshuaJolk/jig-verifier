import Init


namespace Submissions.J4P41QuadraticCollision.Proof.P41CompressedQuadratic

def mark (p t : Int) : Int := p*t+(t*t)%p

private theorem mod_once (a p : Int) (lo : p ≤ a) (hi : a < 2*p) :
    a%p=a-p := by
  calc
    a%p=(a-p)%p := (Int.sub_emod_right a p).symm
    _=a-p := Int.emod_eq_of_lt (by omega) (by omega)

/- Two residue increases cannot both wrap when their combined width is small. -/
theorem two_candidates (p d x : Int) (hd : 0 ≤ d) (hp : 3*d+6 ≤ p)
    (hx : 0 ≤ x) (hxp : x < p) :
    (x+d)%p-x=d ∨
      (((x+2*d+2)%p+d+4)%p)-(x+2*d+2)%p=d+4 := by
  by_cases h : x+d < p
  · left
    rw [Int.emod_eq_of_lt (by omega) h]
    omega
  · right
    have hz : (x+2*d+2)%p=x+2*d+2-p := mod_once _ _ (by omega) (by omega)
    rw [hz, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/- Explicit rank-one versus rank-two collision. The square-root bracket,
   parity and n>=16 are numerical hypotheses, not Sidon/energy assumptions. -/
theorem compressed_collision (p m n : Int) (hn : 16 ≤ n)
    (odd : p=2*m+1) (lower : n*n < p) (upper : p < (n+1)*(n+1)) :
    ∃ s t : Int, 0 ≤ t ∧ t+2 < s ∧ s+1 < p ∧
      mark p (s+1)-mark p s=mark p (t+2)-mark p t := by
  have positive_product : 0 ≤ (n-16)*n := Int.mul_nonneg (by omega) (by omega)
  have scale : 16*n < p := by grind
  have hp : 0 < p := by omega
  have hnm : 0 ≤ (n-1)*(n-1) := by
    have h := Int.mul_nonneg (show 0 ≤ n-1 by omega) (show 0 ≤ n-1 by omega)
    exact h
  have hns : 0 ≤ n*n := Int.mul_nonneg (by omega) (by omega)
  have small1 : (n-1)*(n-1)<p := by grind
  have big1 : p ≤ (n+1)*(n+1) := by omega
  have big2 : p ≤ (n+2)*(n+2) := by grind
  have top1 : (n+1)*(n+1)<2*p := by grind
  have top2 : (n+2)*(n+2)<2*p := by grind
  have q0 : ((n-1)*(n-1))%p=(n-1)*(n-1) := Int.emod_eq_of_lt hnm small1
  have q1 : (n*n)%p=n*n := Int.emod_eq_of_lt hns lower
  have q2 : ((n+1)*(n+1))%p=(n+1)*(n+1)-p := mod_once _ _ big1 top1
  have q3 : ((n+2)*(n+2))%p=(n+2)*(n+2)-p := mod_once _ _ big2 top2
  have left_edge : mark p (n+1)-mark p (n-1)=p+4*n := by
    simp only [mark, q0, q2]
    grind
  have right_edge : mark p (n+2)-mark p n=p+4*n+4 := by
    simp only [mark, q1, q3]
    grind
  let i := m+2*n
  have hstep : (i+1)*(i+1)=i*i+4*n+p := by dsimp [i]; grind
  have hskip : (i+2)*(i+2)=i*i+8*n+2+p*2 := by dsimp [i]; grind
  have hnext : (i+3)*(i+3)=(i+2)*(i+2)+(4*n+4)+p := by dsimp [i]; grind
  have qstep : ((i+1)*(i+1))%p=((i*i)%p+4*n)%p := by
    rw [Int.emod_add_emod, hstep, Int.add_emod_right]
  have qskip : ((i+2)*(i+2))%p=((i*i)%p+(8*n+2))%p := by
    rw [Int.emod_add_emod, hskip]
    simpa only [Int.add_assoc] using (Int.add_mul_emod_self_left (i*i+8*n+2) p 2)
  have qnext : ((i+3)*(i+3))%p=(((i+2)*(i+2))%p+(4*n+4))%p := by
    rw [Int.emod_add_emod, hnext, Int.add_emod_right]
  have hcarry := two_candidates p (4*n) ((i*i)%p) (by omega) (by omega)
    (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hp)
  rcases hcarry with h | h
  · refine ⟨i,n-1,by omega,?_,?_,?_⟩
    · dsimp [i]; omega
    · dsimp [i]; omega
    · have r : ((i+1)*(i+1))%p-(i*i)%p=4*n := by rw [qstep]; exact h
      have e : mark p (i+1)-mark p i=p+4*n := by simp only [mark]; grind
      have e2 : mark p (n-1+2)-mark p (n-1)=p+4*n := by
        have : n-1+2=n+1 := by omega
        rw [this]; exact left_edge
      omega
  · refine ⟨i+2,n,by omega,?_,?_,?_⟩
    · dsimp [i]; omega
    · dsimp [i]; omega
    · have r : ((i+3)*(i+3))%p-((i+2)*(i+2))%p=4*n+4 := by
        rw [qnext,qskip]
        have he : (i*i)%p+2*(4*n)+2=(i*i)%p+(8*n+2) := by omega
        rw [he] at h
        simpa only [Int.add_assoc] using h
      have e : mark p (i+3)-mark p (i+2)=p+4*n+4 := by simp only [mark]; grind
      have e2 : mark p (i+2+1)-mark p (i+2)=p+4*n+4 := by
        have : i+2+1=i+3 := by omega
        rw [this]; exact e
      omega

theorem mark_strict_mono (p x y : Int) (hp : 0 < p) (hxy : x < y) :
    mark p x < mark p y := by
  have hprod : 0 ≤ p*(y-x-1) := Int.mul_nonneg (by omega) (by omega)
  have hx := Int.emod_lt_of_pos (x*x) hp
  have hy := Int.emod_nonneg (y*y) (show p≠0 by omega)
  simp only [mark]
  grind

def lift (p b t : Int) : Int := b*t+(t*t)%p

private theorem range_collision_core (p n c i e : Int) (hn : 16 ≤ n)
    (hc : 0 ≤ c) (room : 3*c+12*n+6 ≤ p)
    (lower : n*n < p) (upper : p < (n+1)*(n+1))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (index : 2*i+1=c+4*n+e*p) :
    ∃ s t : Int, 0 ≤ t ∧ t+2 < s ∧ s+1 < p ∧
      lift p (p+c) (s+1)-lift p (p+c) s=
        lift p (p+c) (t+2)-lift p (p+c) t := by
  have hp : 0 < p := by omega
  have hnm : 0 ≤ (n-1)*(n-1) := Int.mul_nonneg (by omega) (by omega)
  have hns : 0 ≤ n*n := Int.mul_nonneg (by omega) (by omega)
  have small1 : (n-1)*(n-1)<p := by grind
  have big1 : p ≤ (n+1)*(n+1) := by omega
  have big2 : p ≤ (n+2)*(n+2) := by grind
  have top1 : (n+1)*(n+1)<2*p := by grind
  have top2 : (n+2)*(n+2)<2*p := by grind
  have q0 : ((n-1)*(n-1))%p=(n-1)*(n-1) := Int.emod_eq_of_lt hnm small1
  have q1 : (n*n)%p=n*n := Int.emod_eq_of_lt hns lower
  have q2 : ((n+1)*(n+1))%p=(n+1)*(n+1)-p := mod_once _ _ big1 top1
  have q3 : ((n+2)*(n+2))%p=(n+2)*(n+2)-p := mod_once _ _ big2 top2
  have left_edge : lift p (p+c) (n+1)-lift p (p+c) (n-1)=p+2*c+4*n := by
    simp only [lift,q0,q2]; grind
  have right_edge : lift p (p+c) (n+2)-lift p (p+c) n=p+2*c+4*n+4 := by
    simp only [lift,q1,q3]; grind
  have hstep : (i+1)*(i+1)=i*i+(c+4*n)+p*e := by grind
  have hskip : (i+2)*(i+2)=i*i+(2*(c+4*n)+2)+p*(2*e) := by grind
  have hnext : (i+3)*(i+3)=(i+2)*(i+2)+(c+4*n+4)+p*e := by grind
  have qstep : ((i+1)*(i+1))%p=((i*i)%p+(c+4*n))%p := by
    rw [Int.emod_add_emod,hstep]
    exact Int.add_mul_emod_self_left _ _ _
  have qskip : ((i+2)*(i+2))%p=((i*i)%p+(2*(c+4*n)+2))%p := by
    rw [Int.emod_add_emod,hskip]
    exact Int.add_mul_emod_self_left _ _ _
  have qnext : ((i+3)*(i+3))%p=(((i+2)*(i+2))%p+(c+4*n+4))%p := by
    rw [Int.emod_add_emod,hnext]
    exact Int.add_mul_emod_self_left _ _ _
  have lower_i : n+2 < i := by
    have := Int.mul_nonneg he0 (show 0 ≤ p by omega)
    omega
  have upper_i : i+3 < p := by
    have := Int.mul_nonneg (show 0 ≤ 1-e by omega) (show 0 ≤ p by omega)
    grind
  have hcarry := two_candidates p (c+4*n) ((i*i)%p) (by omega) (by omega)
    (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hp)
  rcases hcarry with h | h
  · refine ⟨i,n-1,by omega,by omega,by omega,?_⟩
    have r : ((i+1)*(i+1))%p-(i*i)%p=c+4*n := by rw [qstep]; exact h
    have ev : lift p (p+c) (i+1)-lift p (p+c) i=p+2*c+4*n := by
      simp only [lift]; grind
    have : n-1+2=n+1 := by omega
    rw [this]; omega
  · refine ⟨i+2,n,by omega,by omega,by omega,?_⟩
    have r : ((i+3)*(i+3))%p-((i+2)*(i+2))%p=c+4*n+4 := by
      rw [qnext,qskip]
      simpa only [Int.add_assoc] using h
    have ev : lift p (p+c) (i+3)-lift p (p+c) (i+2)=p+2*c+4*n+4 := by
      simp only [lift]; grind
    have : i+2+1=i+3 := by omega
    rw [this]; omega

/- All integer bases p+c in the stated interval, with no parity omission. -/
theorem compressed_range_collision (p m n c : Int) (hn : 16 ≤ n)
    (odd : p=2*m+1) (lower : n*n < p) (upper : p < (n+1)*(n+1))
    (hc : 0 ≤ c) (room : 3*c+12*n+6 ≤ p) :
    ∃ s t : Int, 0 ≤ t ∧ t+2 < s ∧ s+1 < p ∧
      lift p (p+c) (s+1)-lift p (p+c) s=
        lift p (p+c) (t+2)-lift p (p+c) t := by
  have hdiv := Int.ediv_mul_add_emod c 2
  have hmod0 := Int.emod_nonneg c (show (2:Int)≠0 by decide)
  have hmod1 := Int.emod_lt_of_pos c (show (0:Int)<2 by decide)
  by_cases h : c%2=0
  · exact range_collision_core p n c (m+c/2+2*n) 1 hn hc room lower upper
      (by decide) (by decide) (by omega)
  · exact range_collision_core p n c (c/2+2*n) 0 hn hc room lower upper
      (by decide) (by decide) (by omega)

theorem lift_strict_mono (p b x y : Int) (hp : 0 < p) (hb : p ≤ b) (hxy : x < y) :
    lift p b x < lift p b y := by
  have hprod : 0 ≤ b*(y-x-1) := Int.mul_nonneg (by omega) (by omega)
  have hx := Int.emod_lt_of_pos (x*x) hp
  have hy := Int.emod_nonneg (y*y) (show p≠0 by omega)
  simp only [lift]
  grind



end Submissions.J4P41QuadraticCollision.Proof.P41CompressedQuadratic

namespace Submissions.J4P41QuadraticCollision.Proof

theorem proof :
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
    P41CompressedQuadratic.lift p b x < P41CompressedQuadratic.lift p b y) :=
  ⟨@P41CompressedQuadratic.compressed_collision, @P41CompressedQuadratic.compressed_range_collision, @P41CompressedQuadratic.lift_strict_mono⟩

end Submissions.J4P41QuadraticCollision.Proof
