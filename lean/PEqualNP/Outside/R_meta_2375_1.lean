import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2375_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      x1.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      x1.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true)
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      x1.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (17 : ℕ) → have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)); have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false; (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro x1 x2 x3 x4 hf1 hf2 hs x8 x9 h10 h11 h12
  have hop := (hf1 x1 (by simp)).1
  cases h : x1.op
  · exact h1 x1 x2 x3 x4 hf1 h hf2 hs h10 h11 h12
  · exact h2 x1 x2 x3 x4 hf1 h hf2 hs h10 h11 h12
  · exact h3 x1 x2 x3 x4 hf1 h hf2 hs h10 h11 h12
  · simp [h] at hop
  · simp [h] at hop
