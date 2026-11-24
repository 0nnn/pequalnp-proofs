import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2382_1
    (h1 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) →
        (∃ a ∈ PEqualNP.TopForm.junk x1 x2, ∃ b ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b) →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) →
        x8 < (2 : ℕ) * x7.card →
        x7.card ≤ x8)
    (h2 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) →
        (∀ a ∈ PEqualNP.TopForm.junk x1 x2, ∀ b ∈ PEqualNP.TopForm.junk x1 x2, ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b) →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) →
        x8 < (2 : ℕ) * x7.card →
        x7.card ≤ x8)
    (h3 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) →
        x8 < (2 : ℕ) * x7.card →
        x7.card ≤ x8) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2; have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card; (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8 := by
  classical
  intro x1 x2 hsize hleast htop hjunk x7 x8 hcov hlt
  by_cases h3c : (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card
  · exact h3 x2 hsize hleast htop h3c hcov hlt
  · have h2c : (PEqualNP.TopForm.junk x1 x2).card = 2 := by omega
    by_cases hnest : ∃ a ∈ PEqualNP.TopForm.junk x1 x2, ∃ b ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.InCone 11 x2 a b
    · exact h1 x2 hsize hleast htop h2c hnest hcov hlt
    · push Not at hnest
      exact h2 x2 hsize hleast htop h2c hnest hcov hlt
