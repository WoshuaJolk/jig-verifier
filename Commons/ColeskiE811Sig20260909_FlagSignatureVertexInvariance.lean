import Commons.ColeskiE811Sig20260909_FlagSignature

/- BEGIN bundled local module FlagSignatureVertexInvariance -/


namespace ColeskiFlagSignature

open ColeskiPatternAction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern) : FivePattern :=
  fun u v => x (q⁻¹ u) (q⁻¹ v)

theorem sum_relabel (q : Equiv.Perm (Fin 5)) (f : Fin 5 → Nat) :
    (∑ v : Fin 5, f (q⁻¹ v)) = ∑ v : Fin 5, f v := by
  exact Equiv.sum_comp q⁻¹ f

theorem bagSum_relabel (q : Equiv.Perm (Fin 5)) (f : Fin 5 → Nat) :
    bagSum (fun v => f (q⁻¹ v)) = bagSum f := by
  simp only [bagSum, sum_relabel]

theorem bagSquareSum_relabel (q : Equiv.Perm (Fin 5)) (f : Fin 5 → Nat) :
    bagSquareSum (fun v => f (q⁻¹ v)) = bagSquareSum f := by
  unfold bagSquareSum
  congr 1
  simpa only using Equiv.sum_comp q⁻¹ (fun v => (f v * f v) % modulus)

theorem bagSum_comp (q : Equiv.Perm (Fin 5)) (f : Fin 5 → Nat) :
    bagSum (fun v => f (q v)) = bagSum f := by
  unfold bagSum
  congr 1
  exact Equiv.sum_comp q f

theorem bagSquareSum_comp (q : Equiv.Perm (Fin 5)) (f : Fin 5 → Nat) :
    bagSquareSum (fun v => f (q v)) = bagSquareSum f := by
  unfold bagSquareSum
  congr 1
  simpa only using Equiv.sum_comp q (fun v => (f v * f v) % modulus)

theorem degreeCount_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (p : Fin 60) (v : Fin 5) (c : Fin 6) :
    degreeCount (relabel q x) p (q v) c = degreeCount x p v c := by
  unfold degreeCount relabel
  rw [← Equiv.sum_comp q]
  simp

theorem degreeCode_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (p : Fin 60) (v : Fin 5) :
    degreeCode (relabel q x) p (q v) = degreeCode x p v := by
  unfold degreeCode
  simp only [degreeCount_relabel]

theorem initialLabel_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (mark v : Fin 5) (p : Fin 60) :
    initialLabel (relabel q x) (q mark) p (q v) = initialLabel x mark p v := by
  unfold initialLabel
  rw [degreeCode_relabel]
  simp [relabel]

theorem neighborValue_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (mark v w : Fin 5) (p : Fin 60) :
    neighborValue (relabel q x) (q mark) p (q v) (q w) =
      neighborValue x mark p v w := by
  unfold neighborValue
  simp only [q.injective.eq_iff]
  split
  · rfl
  · rw [initialLabel_relabel]
    simp [relabel]

theorem refinedLabel_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (mark v : Fin 5) (p : Fin 60) :
    refinedLabel (relabel q x) (q mark) p (q v) = refinedLabel x mark p v := by
  have hsum : bagSum (neighborValue (relabel q x) (q mark) p (q v)) =
      bagSum (neighborValue x mark p v) := by
    calc
      bagSum (neighborValue (relabel q x) (q mark) p (q v)) =
          bagSum (fun w => neighborValue (relabel q x) (q mark) p (q v) (q w)) :=
        (bagSum_comp q _).symm
      _ = bagSum (neighborValue x mark p v) := by
        congr 1
        funext w
        exact neighborValue_relabel q x mark v w p
  have hsquare : bagSquareSum (neighborValue (relabel q x) (q mark) p (q v)) =
      bagSquareSum (neighborValue x mark p v) := by
    calc
      bagSquareSum (neighborValue (relabel q x) (q mark) p (q v)) =
          bagSquareSum (fun w => neighborValue (relabel q x) (q mark) p (q v) (q w)) :=
        (bagSquareSum_comp q _).symm
      _ = bagSquareSum (neighborValue x mark p v) := by
        congr 1
        funext w
        exact neighborValue_relabel q x mark v w p
  unfold refinedLabel
  rw [initialLabel_relabel, hsum, hsquare]

theorem otherRefinedValue_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (mark v : Fin 5) (p : Fin 60) :
    otherRefinedValue (relabel q x) (q mark) p (q v) =
      otherRefinedValue x mark p v := by
  unfold otherRefinedValue
  rw [refinedLabel_relabel]
  simp

theorem candidate_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (flag : FiveFlag) (p : Fin 60) :
    candidate (relabel q x) (q flag.1, flag.2) p = candidate x flag p := by
  have hsum : bagSum (otherRefinedValue (relabel q x) (q flag.1) p) =
      bagSum (otherRefinedValue x flag.1 p) := by
    calc
      bagSum (otherRefinedValue (relabel q x) (q flag.1) p) =
          bagSum (fun v => otherRefinedValue (relabel q x) (q flag.1) p (q v)) :=
        (bagSum_comp q _).symm
      _ = bagSum (otherRefinedValue x flag.1 p) := by
        congr 1
        funext v
        exact otherRefinedValue_relabel q x flag.1 v p
  have hsquare : bagSquareSum (otherRefinedValue (relabel q x) (q flag.1) p) =
      bagSquareSum (otherRefinedValue x flag.1 p) := by
    calc
      bagSquareSum (otherRefinedValue (relabel q x) (q flag.1) p) =
          bagSquareSum (fun v => otherRefinedValue (relabel q x) (q flag.1) p (q v)) :=
        (bagSquareSum_comp q _).symm
      _ = bagSquareSum (otherRefinedValue x flag.1 p) := by
        congr 1
        funext v
        exact otherRefinedValue_relabel q x flag.1 v p
  unfold candidate
  rw [refinedLabel_relabel, hsum, hsquare]

theorem signature_relabel (q : Equiv.Perm (Fin 5)) (x : FivePattern)
    (flag : FiveFlag) :
    signature (relabel q x) (q flag.1, flag.2) = signature x flag := by
  unfold signature bagSum bagSquareSum
  simp only [candidate_relabel]

end ColeskiFlagSignature

#print axioms ColeskiFlagSignature.signature_relabel

/- END bundled local module FlagSignatureVertexInvariance -/
