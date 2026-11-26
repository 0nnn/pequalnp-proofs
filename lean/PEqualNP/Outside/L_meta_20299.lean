import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20299_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 8]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [29, 30]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [20, 32]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [20, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [37, 25]⟩, ⟨.and, [33, 28]⟩, ⟨.and, [23, 38]⟩, ⟨.and, [31, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [44, 42]⟩, ⟨.or, [45, 43]⟩], 46⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8465338603409387505 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20299_aux

theorem PEqualNP.Outside.L_meta_20299 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8465338603409387505 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20299_aux.main
