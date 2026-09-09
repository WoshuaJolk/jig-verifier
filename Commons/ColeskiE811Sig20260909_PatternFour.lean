import Commons.ColeskiE811Sig20260909_K4SemanticsOnly
import Commons.ColeskiE811Sig20260909_PatternAction

/- BEGIN bundled local module PatternFour -/

namespace ColeskiPatternFour
open ColeskiK4Coverage ColeskiPatternAction

def edgeVertices : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def patternCode (x : Pattern (Fin 4) (Fin 6)) : Nat :=
  encode (fun e => (x (edgeVertices e).1 (edgeVertices e).2).getD 0)
def edgeIndex (u v : Nat) : Nat := if u = 0 then v-1 else if u = 1 then v+1 else 5

def fromCode (n : Nat) : Pattern (Fin 4) (Fin 6) :=
  fun u v => if u = v then none else
    some ⟨digit n (edgeIndex (min u.val v.val) (max u.val v.val)),Nat.mod_lt _ (by decide)⟩

theorem digit_encode_nat (e : Fin 6 → Fin 6) (i : Nat) (hi : i < 6) :
    digit (encode e) i = (e ⟨i,hi⟩).val := digit_encode e ⟨i,hi⟩

theorem fromCode_symmetric (n : Nat) : ∀ u v, fromCode n u v = fromCode n v u := by
  intro u v
  simp [fromCode,eq_comm,Nat.min_comm,Nat.max_comm]

theorem fromCode_no_loops (n : Nat) : ∀ u, fromCode n u u = none := by
  intro u
  simp [fromCode]

theorem fromCode_full (n : Nat) : ∀ u v, u ≠ v → fromCode n u v ≠ none := by
  intro u v h
  simp [fromCode,h]

private theorem some_getD {o : Option (Fin 6)} (h : o ≠ none) : some (o.getD 0) = o := by
  cases o <;> simp_all

theorem reconstruct (x : Pattern (Fin 4) (Fin 6))
    (hs : ∀ u v, x u v = x v u) (hd : ∀ u, x u u = none)
    (hf : ∀ u v, u ≠ v → x u v ≠ none) : fromCode (patternCode x) = x := by
  have hforward (u v : Fin 4) (h : u ≠ v) : some ((x u v).getD 0) = x u v := some_getD (hf u v h)
  have hreverse (u v : Fin 4) (h : u ≠ v) : some ((x u v).getD 0) = x v u :=
    (hforward u v h).trans (hs u v)
  funext u v
  fin_cases u <;> fin_cases v <;>
    simp [fromCode,patternCode,edgeIndex,digit_encode_nat,edgeVertices,hd,hs]
  all_goals first | exact hforward _ _ (by decide) | exact hreverse _ _ (by decide)

theorem code_allowed (x : Pattern (Fin 4) (Fin 6))
    (h : ∀ u v w, u ≠ v → u ≠ w → v ≠ w →
      good ((x u v).getD 0) ((x u w).getD 0) ((x v w).getD 0) = true) :
    allowed (patternCode x) = true := by
  have h012 := h 0 1 2 (by decide) (by decide) (by decide)
  have h013 := h 0 1 3 (by decide) (by decide) (by decide)
  have h023 := h 0 2 3 (by decide) (by decide) (by decide)
  have h123 := h 1 2 3 (by decide) (by decide) (by decide)
  simp [allowed,patternCode,digit_encode_nat,edgeVertices,h012,h013,h023,h123]
end ColeskiPatternFour
#print axioms ColeskiPatternFour.reconstruct
#print axioms ColeskiPatternFour.code_allowed

/- END bundled local module PatternFour -/
