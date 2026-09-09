import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K4SemanticsOnly -/

namespace ColeskiK4Coverage

def palettes : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,5}, {0,4,5},
   {1,2,5}, {1,3,4}, {1,4,5}, {2,3,4}, {2,3,5}}

theorem good_iff : ∀ a b c : Fin 6,
    good a b c = true ↔ a = b ∨ b = c ∨ a = c ∨
      ({a,b,c} : Finset (Fin 6)) ∈ palettes := by decide

def vertexPermutations : Array Nat := #[726,546,696,336,486,306,721,541,661,121,451,91,686,326,656,116,236,56,471,291,441,81,231,51]

theorem color_permutations_valid : ∀ p : Fin 60,
    ((List.range 6).map (digit colorPermutations[p.val]!)).Perm (List.range 6) := by decide

theorem color_permutations_good : ∀ p : Fin 60, ∀ a b c : Fin 6,
    good (digit colorPermutations[p.val]! a)
      (digit colorPermutations[p.val]! b) (digit colorPermutations[p.val]! c) = good a b c := by
  intro p
  fin_cases p <;> decide

theorem vertex_permutations_valid : ∀ p : Fin 24,
    ((List.range 4).map (digit vertexPermutations[p.val]!)).Perm (List.range 4) := by decide

def edgeLeft : Nat → Nat
  | 0 | 1 | 2 => 0
  | 3 | 4 => 1
  | _ => 2

def edgeRight : Nat → Nat
  | 0 => 1
  | 1 | 3 => 2
  | _ => 3

theorem edge_permutations_induced : ∀ p : Fin 24, ∀ e : Fin 6,
    let i := digit vertexPermutations[p.val]! (edgeLeft e)
    let j := digit vertexPermutations[p.val]! (edgeRight e)
    let k := digit edgePermutations[p.val]! e
    edgeLeft k = min i j ∧ edgeRight k = max i j := by decide

def encode (e : Fin 6 → Fin 6) : Nat :=
  (e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val +
    1296*(e 4).val + 7776*(e 5).val

theorem encode_lt (e : Fin 6 → Fin 6) : encode e < 46656 := by
  have h0 := (e 0).isLt
  have h1 := (e 1).isLt
  have h2 := (e 2).isLt
  have h3 := (e 3).isLt
  have h4 := (e 4).isLt
  have h5 := (e 5).isLt
  unfold encode
  omega

theorem digit_encode (e : Fin 6 → Fin 6) (i : Fin 6) : digit (encode e) i = (e i).val := by
  have h0 := (e 0).isLt
  have h1 := (e 1).isLt
  have h2 := (e 2).isLt
  have h3 := (e 3).isLt
  have h4 := (e 4).isLt
  have h5 := (e 5).isLt
  fin_cases i
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val) / 1 % 6 = (e 0).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val) / 6 % 6 = (e 1).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val) / 36 % 6 = (e 2).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val) / 216 % 6 = (e 3).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val) / 1296 % 6 = (e 4).val
    omega
  · change ((e 0).val + 6*(e 1).val + 36*(e 2).val + 216*(e 3).val + 1296*(e 4).val + 7776*(e 5).val) / 7776 % 6 = (e 5).val
    omega

theorem encode_injective : Function.Injective encode := by
  intro a b h
  funext i
  apply Fin.ext
  rw [← digit_encode a i, ← digit_encode b i, h]
end ColeskiK4Coverage

/- END bundled local module K4SemanticsOnly -/
