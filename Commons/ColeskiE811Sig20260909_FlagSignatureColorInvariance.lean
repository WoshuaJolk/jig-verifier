import Commons.ColeskiE811Sig20260909_FlagSignatureColorTable

/- BEGIN bundled local module FlagSignatureColorInvariance -/


namespace ColeskiFlagSignature

open ColeskiPaletteAction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def recolor (q : colorGroup) (x : FivePattern) : FivePattern :=
  fun u v => (x u v).map q.val

theorem optionCode_recolor (q : colorGroup) (p : Fin 60) (o : Option (Fin 6)) :
    optionCode p (o.map q.val) = optionCode (composeEquiv q p) o := by
  cases o with
  | none => rfl
  | some c =>
      simp only [Option.map_some, optionCode]
      rw [paletteColor_composeEquiv]

theorem degreeCount_recolor (q : colorGroup) (x : FivePattern)
    (p : Fin 60) (v : Fin 5) (c : Fin 6) :
    degreeCount (recolor q x) p v c =
      degreeCount x (composeEquiv q p) v c := by
  unfold degreeCount recolor
  apply Finset.sum_congr rfl
  intro w hw
  rw [optionCode_recolor]

theorem degreeCode_recolor (q : colorGroup) (x : FivePattern)
    (p : Fin 60) (v : Fin 5) :
    degreeCode (recolor q x) p v = degreeCode x (composeEquiv q p) v := by
  unfold degreeCode
  simp only [degreeCount_recolor]

theorem initialLabel_recolor (q : colorGroup) (x : FivePattern)
    (mark v : Fin 5) (p : Fin 60) :
    initialLabel (recolor q x) mark p v =
      initialLabel x mark (composeEquiv q p) v := by
  unfold initialLabel
  rw [degreeCode_recolor]
  split
  · rfl
  · simp only [recolor, optionCode_recolor]

theorem neighborValue_recolor (q : colorGroup) (x : FivePattern)
    (mark v w : Fin 5) (p : Fin 60) :
    neighborValue (recolor q x) mark p v w =
      neighborValue x mark (composeEquiv q p) v w := by
  unfold neighborValue
  split
  · rfl
  · rw [initialLabel_recolor]
    simp only [recolor, optionCode_recolor]

theorem refinedLabel_recolor (q : colorGroup) (x : FivePattern)
    (mark v : Fin 5) (p : Fin 60) :
    refinedLabel (recolor q x) mark p v =
      refinedLabel x mark (composeEquiv q p) v := by
  unfold refinedLabel bagSum bagSquareSum
  simp only [initialLabel_recolor, neighborValue_recolor]

theorem otherRefinedValue_recolor (q : colorGroup) (x : FivePattern)
    (mark v : Fin 5) (p : Fin 60) :
    otherRefinedValue (recolor q x) mark p v =
      otherRefinedValue x mark (composeEquiv q p) v := by
  unfold otherRefinedValue
  split
  · rfl
  · rw [refinedLabel_recolor]

theorem candidate_recolor (q : colorGroup) (x : FivePattern)
    (flag : FiveFlag) (p : Fin 60) :
    candidate (recolor q x) (flag.1, q.val flag.2) p =
      candidate x flag (composeEquiv q p) := by
  unfold candidate bagSum bagSquareSum
  rw [paletteColor_composeEquiv, refinedLabel_recolor]
  simp only [otherRefinedValue_recolor]

theorem bagSum_perm {V : Type*} [Fintype V] (e : Equiv.Perm V) (f : V → Nat) :
    bagSum (fun v => f (e v)) = bagSum f := by
  unfold bagSum
  exact congrArg (fun n => n % modulus) (Equiv.sum_comp e f)

theorem bagSquareSum_perm {V : Type*} [Fintype V]
    (e : Equiv.Perm V) (f : V → Nat) :
    bagSquareSum (fun v => f (e v)) = bagSquareSum f := by
  unfold bagSquareSum
  exact congrArg (fun n => n % modulus)
    (Equiv.sum_comp e (fun v => (f v * f v) % modulus))

theorem signature_recolor (q : colorGroup) (x : FivePattern) (flag : FiveFlag) :
    signature (recolor q x) (flag.1, q.val flag.2) = signature x flag := by
  have hcandidates :
      candidate (recolor q x) (flag.1, q.val flag.2) =
        fun p => candidate x flag (composeEquiv q p) := by
    funext p
    exact candidate_recolor q x flag p
  have hsum : bagSum (candidate (recolor q x) (flag.1, q.val flag.2)) =
      bagSum (candidate x flag) := by
    rw [hcandidates]
    exact bagSum_perm (composeEquiv q) (candidate x flag)
  have hsquare : bagSquareSum (candidate (recolor q x) (flag.1, q.val flag.2)) =
      bagSquareSum (candidate x flag) := by
    rw [hcandidates]
    exact bagSquareSum_perm (composeEquiv q) (candidate x flag)
  unfold signature
  rw [hsum, hsquare]

end ColeskiFlagSignature

#print axioms ColeskiFlagSignature.signature_recolor

/- END bundled local module FlagSignatureColorInvariance -/
