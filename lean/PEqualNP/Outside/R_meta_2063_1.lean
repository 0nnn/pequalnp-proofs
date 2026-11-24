import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2063_1
    (h1 : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ)));
      have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ);
      have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false;
      have a : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have g : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
        have c : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5;
        PEqualNP.MetaComplexity.Monotone2 x5 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →
        x4 x5 →
        x5.size < (64 : ℕ) →
        (∀ (x10 x11 : ℕ), (g x10).op = a → (g x11).op = a → c x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) →
        (∃ (x11 x12 : ℕ), (g x11).op = a ∧ (g x12).op = a ∧ c x11 x12 ∧ (26 : ℕ) + x11 ∈ (g x12).inputs) →
        ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size)
    (h2 : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ)));
      have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ);
      have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false;
      have a : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have g : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
        have c : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5;
        PEqualNP.MetaComplexity.Monotone2 x5 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →
        x4 x5 →
        x5.size < (64 : ℕ) →
        (∀ (x10 x11 : ℕ), (g x10).op = a → (g x11).op = a → c x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) →
        (∃ (x11 x12 : ℕ), (g x11).op = a ∧ (g x12).op = a ∧ c x11 x12) →
        (∀ (x11 x12 : ℕ), (g x11).op = a → (g x12).op = a → c x11 x12 → (26 : ℕ) + x11 ∉ (g x12).inputs) →
        ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size) :
    have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  classical
  intro x1 x2 x3 x4 x5 hmon hrb hok hsz hdirty hnest
  by_cases hdir : ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12 ∧ (26 : ℕ) + x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).inputs
  · exact h1 x5 hmon hrb hok hsz hdirty hdir
  · push Not at hdir
    exact h2 x5 hmon hrb hok hsz hdirty hnest hdir
