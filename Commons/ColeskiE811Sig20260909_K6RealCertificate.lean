import Commons.ColeskiE811Sig20260909_WitnessCoefficient

/- BEGIN bundled local module K6RealCertificate -/

namespace ColeskiK6RealCertificate
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiOrbitChecks
open ColeskiK6Check ColeskiWitnessCoefficient ColeskiOrbitCoefficient
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem edgeColor_lt (r a i j : Nat) : edgeColor r a i j < 6 := by
  unfold edgeColor
  split
  · decide
  · dsimp only
    split <;> exact Nat.mod_lt _ (by decide)

def colorFin (r a i j : Nat) : Fin 6 := ⟨edgeColor r a i j,edgeColor_lt r a i j⟩

theorem cast_list_sum (l : List Int) :
    ((l.sum : Int) : ℝ) = (l.map (fun x : Int => (x : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem sumList6 (f : Nat → ℝ) : ((List.range 6).map f).sum = ∑ i : Fin 6, f i.val := by
  simp [Fin.sum_univ_succ,List.range_succ,add_assoc]

theorem sumList5 (f : Nat → ℝ) : ((List.range 5).map f).sum = ∑ i : Fin 5, f i.val := by
  simp [Fin.sum_univ_succ,List.range_succ,add_assoc]

theorem cast_sum6 (f : Nat → Int) : ((((List.range 6).map f).sum : Int) : ℝ) = ∑ i : Fin 6, (f i.val : ℝ) := by
  rw [cast_list_sum]
  simpa only [List.map_map,Function.comp_def] using sumList6 (fun i => (f i : ℝ))

theorem cast_sum5 (f : Nat → Int) : ((((List.range 5).map f).sum : Int) : ℝ) = ∑ i : Fin 5, (f i.val : ℝ) := by
  rw [cast_list_sum]
  simpa only [List.map_map,Function.comp_def] using sumList5 (fun i => (f i : ℝ))

noncomputable def realTotal (r a : Nat) : ℝ :=
  ∑ z : Fin 6, ∑ m : Fin 5,
    (6 * coefficientFor (fromCode (deletionCode r a z.val))
      (m,colorFin r a (skip z.val m.val) z.val) -
    ∑ c : Fin 6, coefficientFor (fromCode (deletionCode r a z.val)) (m,c))

theorem coefficient_at_deletion
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true)
    (z : Fin 6) (f : Fin 5 × Fin 6) :
    coefficientFor (fromCode (deletionCode r a z.val)) f =
      (flagWeight ws[z.val]! f.1.val f.2.val : ℝ) := by
  have hd := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 z.val (List.mem_range.mpr z.isLt)
  have ht : 0 < ws[z.val]! ∧ ws[z.val]! ≤ 3967200 ∧
      transformed5 ws[z.val]! = deletionCode r a z.val := by
    simpa [deletionCheck,and_assoc] using hd
  let w : Fin 3967200 := ⟨ws[z.val]!-1,by omega⟩
  have he : w.val+1 = ws[z.val]! := by dsimp [w]; omega
  have hw : transformed5 (w.val+1) = deletionCode r a z.val := by rw [he]; exact ht.2.2
  simpa only [he] using coefficient_witness checks w (deletionCode r a z.val) hw f

theorem realTotal_eq
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) :
    realTotal r a = (total r a ws : ℝ) := by
  unfold realTotal total
  rw [cast_sum6]
  apply Finset.sum_congr rfl
  intro z hz
  rw [cast_sum5]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [coefficient_at_deletion checks r a ws h z]
  simp only [contribution,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,cast_sum6,colorFin]

theorem checked_positive
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (r a : Nat) (ws : Array Nat) (h : checkPositive r a ws = true) : 0 < realTotal r a := by
  have hp : 0 < total r a ws := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  rw [realTotal_eq checks r a ws h]
  exact_mod_cast hp
end ColeskiK6RealCertificate
#print axioms ColeskiK6RealCertificate.checked_positive

/- END bundled local module K6RealCertificate -/
