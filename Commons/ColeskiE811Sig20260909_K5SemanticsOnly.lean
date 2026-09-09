import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5SemanticsOnly -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ColeskiK4Coverage
def vertexPermutations5 : Array Nat := #[5910,4830,5730,3570,4470,3390,5880,4800,5520,2280,4260,2100,5670,3510,5490,2250,2970,1890,4380,3300,4200,2040,2940,1860,5905,4825,5725,3565,4465,3385,5845,4765,5305,985,4045,805,5635,3475,5275,955,2755,595,4345,3265,3985,745,2725,565,5870,4790,5510,2270,4250,2090,5840,4760,5300,980,4040,800,5420,2180,5240,920,1460,380,4130,1970,3950,710,1430,350,5655,3495,5475,2235,2955,1875,5625,3465,5265,945,2745,585,5415,2175,5235,915,1455,375,2835,1755,2655,495,1395,315,4360,3280,4180,2020,2920,1840,4330,3250,3970,730,2710,550,4120,1960,3940,700,1420,340,2830,1750,2650,490,1390,310]

theorem vertex_permutations5_valid : ∀ p : Fin 120,
    ((List.range 5).map (digit vertexPermutations5[p.val]!)).Perm (List.range 5) := by decide

def edgeLeft5 : Nat → Nat
  | 0 | 1 | 2 | 3 => 0
  | 4 | 5 | 6 => 1
  | 7 | 8 => 2
  | _ => 3

def edgeRight5 : Nat → Nat
  | 0 => 1
  | 1 | 4 => 2
  | 2 | 5 | 7 => 3
  | _ => 4

theorem edge_maps5_induced : ∀ p : Fin 120, ∀ e : Fin 10,
    let i := digit vertexPermutations5[p.val]! (edgeLeft5 e)
    let j := digit vertexPermutations5[p.val]! (edgeRight5 e)
    let k := edgeMaps5[p.val]!/10^e.val%10
    edgeLeft5 k = min i j ∧ edgeRight5 k = max i j := by
  intro p
  fin_cases p <;> decide

def extensionDigit (r a : Nat) : Nat → Nat
  | 0 => digit r 0
  | 1 => digit r 1
  | 2 => digit r 2
  | 3 => digit a 0
  | 4 => digit r 3
  | 5 => digit r 4
  | 6 => digit a 1
  | 7 => digit r 5
  | 8 => digit a 2
  | _ => digit a 3

theorem extension_digits (r a : Nat) (e : Fin 10) :
    digit (extendCode r a) e = extensionDigit r a e := by
  have hr0 : digit r 0 < 6 := Nat.mod_lt _ (by decide)
  have hr1 : digit r 1 < 6 := Nat.mod_lt _ (by decide)
  have hr2 : digit r 2 < 6 := Nat.mod_lt _ (by decide)
  have hr3 : digit r 3 < 6 := Nat.mod_lt _ (by decide)
  have hr4 : digit r 4 < 6 := Nat.mod_lt _ (by decide)
  have hr5 : digit r 5 < 6 := Nat.mod_lt _ (by decide)
  have ha0 : digit a 0 < 6 := Nat.mod_lt _ (by decide)
  have ha1 : digit a 1 < 6 := Nat.mod_lt _ (by decide)
  have ha2 : digit a 2 < 6 := Nat.mod_lt _ (by decide)
  have ha3 : digit a 3 < 6 := Nat.mod_lt _ (by decide)
  fin_cases e
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/1%6 = digit r 0
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/6%6 = digit r 1
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/36%6 = digit r 2
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/216%6 = digit a 0
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/1296%6 = digit r 3
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/7776%6 = digit r 4
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/46656%6 = digit a 1
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/279936%6 = digit r 5
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/1679616%6 = digit a 2
    omega
  · change (digit r 0 + 6*(digit r 1) + 36*(digit r 2) + 216*(digit a 0) + 1296*(digit r 3) + 7776*(digit r 4) + 46656*(digit a 1) + 279936*(digit r 5) + 1679616*(digit a 2) + 10077696*(digit a 3))/10077696%6 = digit a 3
    omega
end ColeskiK5Coverage
#print axioms ColeskiK5Coverage.edge_maps5_induced
#print axioms ColeskiK5Coverage.extension_digits

/- END bundled local module K5SemanticsOnly -/
