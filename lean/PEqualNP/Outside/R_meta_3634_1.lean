import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3634_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x2.card = (2 : ℕ) →
      x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} →
      Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} →
      x1.size = (13 : ℕ) →
      (∀ (x8 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) =
        [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) →
      ∃ i : Fin x1.gates.length,
        (x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (4 : ℕ) ∈ (x1.gates.get i).inputs ∧
        ∀ j : Fin x1.gates.length, j ≠ i →
          (x1.gates.get j).inputs[(0 : ℕ)]? ≠ Option.some (4 : ℕ) ∧
          ((x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ (4 : ℕ) ∉ (x1.gates.get j).inputs))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x2.card = (2 : ℕ) →
      x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} →
      Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} →
      x1.size = (13 : ℕ) →
      (∀ (x8 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) =
        [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) →
      (∃ i : Fin x1.gates.length,
        (x1.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (4 : ℕ) ∈ (x1.gates.get i).inputs ∧
        ∀ j : Fin x1.gates.length, j ≠ i →
          (x1.gates.get j).inputs[(0 : ℕ)]? ≠ Option.some (4 : ℕ) ∧
          ((x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ (4 : ℕ) ∉ (x1.gates.get j).inputs)) →
      False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro x1 x2 hfit hcard hne hdisj hsize heval
  exact h2 x1 x2 hfit hcard hne hdisj hsize heval (h1 x1 x2 hfit hcard hne hdisj hsize heval)
