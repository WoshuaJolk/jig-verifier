import Commons.ColeskiE811Sig20260909_K5SemanticsOnly
import Commons.ColeskiE811Sig20260909_PatternAction

/- BEGIN bundled local module PatternCode -/

namespace ColeskiPatternCode
open ColeskiK4Coverage ColeskiPatternAction

def encode10 (e : Fin 10 → Fin 6) : Nat :=
  (e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val

theorem encode10_lt (e : Fin 10 → Fin 6) : encode10 e < 60466176 := by
  have h0 := (e 0).isLt
  have h1 := (e 1).isLt
  have h2 := (e 2).isLt
  have h3 := (e 3).isLt
  have h4 := (e 4).isLt
  have h5 := (e 5).isLt
  have h6 := (e 6).isLt
  have h7 := (e 7).isLt
  have h8 := (e 8).isLt
  have h9 := (e 9).isLt
  unfold encode10
  omega

theorem digit_encode10 (e : Fin 10 → Fin 6) (i : Fin 10) : digit (encode10 e) i = (e i).val := by
  have h0 := (e 0).isLt
  have h1 := (e 1).isLt
  have h2 := (e 2).isLt
  have h3 := (e 3).isLt
  have h4 := (e 4).isLt
  have h5 := (e 5).isLt
  have h6 := (e 6).isLt
  have h7 := (e 7).isLt
  have h8 := (e 8).isLt
  have h9 := (e 9).isLt
  fin_cases i
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/1%6 = (e 0).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/6%6 = (e 1).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/36%6 = (e 2).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/216%6 = (e 3).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/1296%6 = (e 4).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/7776%6 = (e 5).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/46656%6 = (e 6).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/279936%6 = (e 7).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/1679616%6 = (e 8).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val + 46656*(e 6).val + 279936*(e 7).val + 1679616*(e 8).val + 10077696*(e 9).val)/10077696%6 = (e 9).val
    omega

theorem digit_encode10_nat (e : Fin 10 → Fin 6) (i : Nat) (hi : i < 10) :
    digit (encode10 e) i = (e ⟨i,hi⟩).val := digit_encode10 e ⟨i,hi⟩

def edgeVertices : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def patternCode (x : Pattern (Fin 5) (Fin 6)) : Nat :=
  encode10 (fun e => (x (edgeVertices e).1 (edgeVertices e).2).getD 0)

def edgeIndex (u v : Nat) : Nat :=
  if u = 0 then v-1 else if u = 1 then v+2 else if u = 2 then v+4 else 9

def fromCode (n : Nat) : Pattern (Fin 5) (Fin 6) :=
  fun u v => if u = v then none else
    some ⟨digit n (edgeIndex (min u.val v.val) (max u.val v.val)), Nat.mod_lt _ (by decide)⟩

theorem fromCode_symmetric (n : Nat) : ∀ u v, fromCode n u v = fromCode n v u := by
  intro u v
  simp [fromCode, eq_comm, Nat.min_comm, Nat.max_comm]

theorem fromCode_no_loops (n : Nat) : ∀ u, fromCode n u u = none := by
  intro u
  simp [fromCode]

theorem fromCode_full (n : Nat) : ∀ u v, u ≠ v → fromCode n u v ≠ none := by
  intro u v h
  simp [fromCode, h]

private theorem some_getD {o : Option (Fin 6)} (h : o ≠ none) : some (o.getD 0) = o := by
  cases o <;> simp_all

theorem reconstruct (x : Pattern (Fin 5) (Fin 6))
    (hs : ∀ u v, x u v = x v u) (hd : ∀ u, x u u = none)
    (hf : ∀ u v, u ≠ v → x u v ≠ none) : fromCode (patternCode x) = x := by
  funext u v
  fin_cases u <;> fin_cases v <;>
    simp [fromCode, patternCode, edgeIndex, digit_encode10_nat, edgeVertices, hd, hs]
  all_goals try rw [← hs]
  all_goals apply some_getD; apply hf; decide
end ColeskiPatternCode
#print axioms ColeskiPatternCode.reconstruct

/- END bundled local module PatternCode -/
