import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_5373_1
    (dirty :
      ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),
        (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) →
        ¬x6.IsAcyclic →
        (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) →
        IsAO2 (x1 + x2) x5 →
        (∀ (x11 : Fin (x1 + x2) → Bool), circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) →
        x4 ⊆ x3 →
        (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) →
        (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) →
        (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) →
        (∃ j < x5.gates.length, (gateAt x5 j).op = GateOp.and ∧ ∃ v : Fin (x1 + x2) → Bool, gateVal (x1 + x2) x5 j v = true ∧ circuitFun (x1 + x2) x5 v = false) →
        ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : Circuit), x17.size < x5.size ∧ IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true))
    (nested :
      ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),
        (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) →
        ¬x6.IsAcyclic →
        (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) →
        IsAO2 (x1 + x2) x5 →
        (∀ (x11 : Fin (x1 + x2) → Bool), circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) →
        x4 ⊆ x3 →
        (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) →
        (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) →
        (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) →
        (∀ j < x5.gates.length, (gateAt x5 j).op = GateOp.and → ∀ v : Fin (x1 + x2) → Bool, gateVal (x1 + x2) x5 j v = true → circuitFun (x1 + x2) x5 v = true) →
        (∃ i < x5.gates.length, ∃ j < x5.gates.length, (gateAt x5 i).op = GateOp.and ∧ (gateAt x5 j).op = GateOp.and ∧ InCone (x1 + x2) x5 i j) →
        ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : Circuit), x17.size < x5.size ∧ IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true)) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by
  classical
  intro n m E M C G adj cyc hSquare hAO hEval hSub hMatchP hMatchL hLeaf
  by_cases hDirty : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∃ v : Fin (n + m) → Bool, gateVal (n + m) C j v = true ∧ circuitFun (n + m) C v = false
  · exact dirty n m E M C G adj cyc hSquare hAO hEval hSub hMatchP hMatchL hLeaf hDirty
  have hClean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ v : Fin (n + m) → Bool, gateVal (n + m) C j v = true → circuitFun (n + m) C v = true := by
    intro j hj hop v hv
    cases hf : circuitFun (n + m) C v with
    | true => rfl
    | false => exact (hDirty ⟨j, hj, hop, v, hv, hf⟩).elim
  by_cases hNested : ∃ i < C.gates.length, ∃ j < C.gates.length,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone (n + m) C i j
  · exact nested n m E M C G adj cyc hSquare hAO hEval hSub hMatchP hMatchL hLeaf hClean hNested
  have hTop : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone (n + m) C i j := by
    intro i hi j hj hopi hopj hc
    exact hNested ⟨i, hi, j, hj, hopi, hopj, hc⟩
  let N := n + m
  let left : Fin n → Fin N := Fin.castAdd m
  let right : Fin m → Fin N := Fin.natAdd n
  have leftInj : Function.Injective left := fun a b h => Fin.ext (by simpa [left] using congrArg Fin.val h)
  have rightInj : Function.Injective right := by
    intro a b h
    have hv := congrArg Fin.val h
    change n + a.val = n + b.val at hv
    exact Fin.ext (by omega)
  have sides (p : Fin n) (l : Fin m) : left p ≠ right l := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = n + l.val at hv
    omega
  -- Step 1: Existence of e0 ∈ E \ M and E.card ≥ 2 (from ¬ G.IsAcyclic)
  have hExistFree : ∃ e0 ∈ E, e0 ∉ M ∧ (E.erase e0).Nonempty := by
    have hHasCycle : ∃ u : Fin N, ∃ p : G.Walk u u, p.IsCycle := by
      unfold SimpleGraph.IsAcyclic at cyc
      push_neg at cyc
      exact cyc
    obtain ⟨u, c, hc⟩ := hHasCycle
    have hlen : 3 ≤ c.length := hc.three_le_length
    cases c with
    | nil => simp at hlen
    | @cons _ v _ huv p1 =>
      cases p1 with
      | nil => simp at hlen
      | @cons _ w _ hvw p2 =>
        have hne_uw : u ≠ w := by
          intro eq
          subst eq
          have hnd := hc.edges_nodup
          simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnd
          have hmem : s(u, v) ∈ s(v, u) :: p2.edges := by
            rw [Sym2.eq_swap]; exact List.mem_cons_self
          exact hnd.1 hmem
        obtain ⟨e1, he1, h1⟩ := (adj u v).mp huv
        obtain ⟨e2, he2, h2⟩ := (adj v w).mp hvw
        have he12 : e1 ≠ e2 := by
          intro eq
          subst eq
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
          · exact (sides _ _ h2a.symm).elim
          · exact hne_uw h2a.symm
          · exact hne_uw h2b.symm
          · exact (sides _ _ h2b).elim
        have hnotboth : ¬ (e1 ∈ M ∧ e2 ∈ M) := by
          rintro ⟨hm1, hm2⟩
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
          · exact (sides _ _ h2a.symm).elim
          · exact he12 (hMatchL e1 hm1 e2 hm2 (rightInj h2b))
          · exact he12 (hMatchP e1 hm1 e2 hm2 (leftInj h2a))
          · exact (sides _ _ h2b).elim
        by_cases hm1 : e1 ∈ M
        · exact ⟨e2, he2, fun hm2 => hnotboth ⟨hm1, hm2⟩, ⟨e1, Finset.mem_erase.mpr ⟨he12, he1⟩⟩⟩
        · exact ⟨e1, he1, hm1, ⟨e2, Finset.mem_erase.mpr ⟨he12.symm, he2⟩⟩⟩
  obtain ⟨e0, he0E, he0M, hErNonempty⟩ := hExistFree
  -- Basic circuit evaluation helpers
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len (gs : List Gate) (w : List Bool) :
      (gs.foldl stepW w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega
  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepW w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepW w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (stepW w g) w.length (by simp [stepW])]
        simp only [List.getElem_cons_zero]
        have h2 : (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepW, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepW w g) i (by simp [stepW]; omega)]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          have hge : w.length ≤ i := Nat.le_of_not_lt hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
          rfl
      | succ j =>
        have key := ih (stepW w g) j (by simpa using hj)
        have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]; exact key
  let wval (w : ℕ) (x : Fin N → Bool) : Bool := (C.wires (List.ofFn x)).getD w false
  have wval_input (i : Fin N) (x : Fin N → Bool) : wval i.val x = x i := by
    change (C.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
    rw [foldl_getD_lt C.gates (List.ofFn x) i.val (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have wval_ge (w : ℕ) (hw : N + C.gates.length ≤ w) (x : Fin N → Bool) : wval w x = false := by
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [foldl_len, List.length_ofFn]; omega)]
    rfl
  have gateAt_eq {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]
  have gateAt_mem {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj
  have gate_inputs_two {j : ℕ} (hj : j < C.gates.length) :
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    have hl := hAO.2.2 (gateAt C j) (gateAt_mem hj)
    rcases heq : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [heq] at hl
    · simp [heq] at hl
    · unfold opnd
      rw [heq]; rfl
    · simp [heq] at hl
  have opnd_lt {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) : opnd C j b < N + j := by
    apply hAO.2.1 j hj
    rw [gate_inputs_two hj]
    fin_cases b <;> simp
  have wval_gate {j : ℕ} (hj : j < C.gates.length) (x : Fin N → Bool) :
      wval (N + j) x =
        if (gateAt C j).op = GateOp.and then wval (opnd C j 0) x && wval (opnd C j 1) x
        else wval (opnd C j 0) x || wval (opnd C j 1) x := by
    have hfg := foldl_getD_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hfg
    change (C.gates.foldl stepW (List.ofFn x)).getD (N + j) false = _
    rw [hfg, ← gateAt_eq hj, gate_inputs_two hj]
    have h0 : opnd C j 0 < N + j := opnd_lt hj 0
    have h1 : opnd C j 1 < N + j := opnd_lt hj 1
    simp only [List.map_cons, List.map_nil, if_pos h0, if_pos h1]
    rcases hAO.1 (gateAt C j) (gateAt_mem hj) with hop | hop
    · rw [hop, ite_eq_left rfl]
      change ([wval (opnd C j 0) x, wval (opnd C j 1) x].all id) = _
      simp
    · rw [hop, ite_eq_right (by intro h; cases h)]
      change ([wval (opnd C j 0) x, wval (opnd C j 1) x].any id) = _
      simp
  have wval_mono (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ i, x i = true → y i = true) :
      wval w x = true → wval w y = true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hw : w < N
      · rw [wval_input ⟨w, hw⟩ x, wval_input ⟨w, hw⟩ y]; exact hxy ⟨w, hw⟩
      · by_cases hw2 : w < N + C.gates.length
        · have hj : w - N < C.gates.length := by omega
          have heq : N + (w - N) = w := by omega
          rw [← heq, wval_gate hj x, wval_gate hj y]
          split_ifs
          · simp only [Bool.and_eq_true]
            rintro ⟨h0, h1⟩
            exact ⟨ih _ (by have := opnd_lt hj 0; omega) h0, ih _ (by have := opnd_lt hj 1; omega) h1⟩
          · simp only [Bool.or_eq_true]
            rintro (h0 | h1)
            · exact Or.inl (ih _ (by have := opnd_lt hj 0; omega) h0)
            · exact Or.inr (ih _ (by have := opnd_lt hj 1; omega) h1)
        · rw [wval_ge w (by omega) x]; intro h; cases h
  -- Cone characterization
  have cones_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep N) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      rw [List.length_append, List.length_singleton]; omega
  have cones_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep N) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, N ≤ w ∧ w < N + j ∧
          (i = w - N ∨ i ∈ (gs.foldl (coneStep N) []).getD (w - N) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep N) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k < gs.length, (coneStep N (gs.foldl (coneStep N) []) g).getD k [] =
          (gs.foldl (coneStep N) []).getD k [] := by
        intro k hk
        change ((gs.foldl (coneStep N) []) ++ [_]).getD k [] = _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - N) (by omega)]; exact Or.inr h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - N) (by omega)] at h3; exact Or.inr h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep N (gs.foldl (coneStep N) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + gs.length))).flatMap
              (fun w => (w - N) :: (gs.foldl (coneStep N) []).getD (w - N) []) := by
          change ((gs.foldl (coneStep N) []) ++ [(g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + (gs.foldl (coneStep N) []).length))).flatMap
            (fun w => (w - N) :: (gs.foldl (coneStep N) []).getD (w - N) [])]).getD gs.length [] = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [e1, e2]
        simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - N) (by omega)]; exact Or.inr h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
          rcases h3 with rfl | h3
          · exact Or.inl rfl
          · rw [key (w - N) (by omega)] at h3; exact Or.inr h3
      · have e0 : (coneStep N (gs.foldl (coneStep N) []) g).getD j [] = [] := by
          change ((gs.foldl (coneStep N) []) ++ [_]).getD j [] = []
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, List.length_singleton, hlen]; omega)]
          rfl
        rw [e0]; simp; omega
  have inCone_step {i j : ℕ} (hj : j < C.gates.length) (b : Fin 2)
      (hw : N ≤ opnd C j b) (h : i = opnd C j b - N ∨ InCone N C i (opnd C j b - N)) :
      InCone N C i j := by
    unfold InCone cones
    rw [cones_char C.gates i j]
    refine ⟨hj, opnd C j b, ?_, hw, opnd_lt hj b, h⟩
    change opnd C j b ∈ (gateAt C j).inputs
    rw [gate_inputs_two hj]; fin_cases b <;> simp
  have inCone_trans {i k j : ℕ} (h1 : InCone N C i k) (h2 : InCone N C k j) : InCone N C i j := by
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      unfold InCone cones at h2
      rw [cones_char C.gates k j] at h2
      obtain ⟨hj, w, hw, hge, hlt, rfl | hk⟩ := h2
      · unfold InCone cones
        rw [cones_char C.gates i j]
        exact ⟨hj, w, hw, hge, hlt, Or.inr h1⟩
      · have hlt2 : w - N < j := by omega
        have hit := ih (w - N) hlt2 hk
        unfold InCone cones
        rw [cones_char C.gates i j]
        exact ⟨hj, w, hw, hge, hlt, Or.inr hit⟩
  -- Single-vertex evaluation and BelowF
  let single (u : Fin N) : Fin N → Bool := fun i => decide (i = u)
  let sSet (w : ℕ) : Finset (Fin N) := Finset.univ.filter fun u => wval w (single u) = true
  have f_single_false (u : Fin N) : circuitFun N C (single u) = false := by
    rw [hEval, decide_eq_false_iff_not]
    rintro ⟨p, l, _, hp, hl⟩
    simp only [single, decide_eq_true_eq] at hp hl
    exact sides p l (hp.trans hl.symm)
  have sSet_input (u : Fin N) : sSet u.val = {u} := by
    ext v
    simp only [sSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [wval_input u (single v)]
    simp [single, eq_comm]
  have sSet_and {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
      sSet (N + j) = ∅ := by
    ext u
    simp only [sSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    have hf := hClean j hj hop (single u) h
    rw [f_single_false u] at hf
    cases hf
  have sSet_or {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
      sSet (N + j) = sSet (opnd C j 0) ∪ sSet (opnd C j 1) := by
    ext u
    simp only [sSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [wval_gate hj (single u), if_neg (by intro h; rw [hop] at h; cases h), Bool.or_eq_true]
  -- Reachability through OR gates (simple reflexive-transitive closure via induction on wire)
  -- We define orReach w : Finset ℕ as the set of gates k < C.gates.length reachable from w via OR gates.
  have hOutBounds : N ≤ C.output ∧ C.output < N + C.gates.length := by
    constructor
    · by_contra hlt
      push_neg at hlt
      have h1 : circuitFun N C (single ⟨C.output, hlt⟩) = true := by
        change wval C.output (single ⟨C.output, hlt⟩) = true
        rw [wval_input ⟨C.output, hlt⟩ (single ⟨C.output, hlt⟩)]
        simp [single]
      rw [f_single_false] at h1; cases h1
    · by_contra hge
      push_neg at hge
      have h1 : circuitFun N C (fun _ => true) = false := wval_ge C.output hge (fun _ => true)
      rw [hEval] at h1
      have h2 : decide (∃ p l, (p, l) ∈ E ∧ true = true ∧ true = true) = true :=
        decide_eq_true_eq.mpr ⟨e0.1, e0.2, he0E, rfl, rfl⟩
      rw [h2] at h1; cases h1
  -- Use OrReaches from PEqualNP.CleanedNonEdge! Wait: let's prove its simple char in 20 lines
  have orSets_len (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      change (cs ++ [_]).length + gs.length = cs.length + (gs.length + 1)
      rw [List.length_append, List.length_singleton]; omega
  have orSets_char (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, N ≤ w ∧ w < N + j ∧
            i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []).getD (w - N) [])) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []).length = gs.length := by
        rw [orSets_len]; simp
      have key : ∀ k < gs.length, (PEqualNP.CleanedNonEdge.orStep N (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []).getD k [] := by
        intro k hk
        change ((gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []) ++ [_]).getD k [] = _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact ⟨by simp; omega, Or.inl rfl⟩
          · refine ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - N) (by omega)]; exact h3
        · rintro ⟨_, rfl | ⟨hop, w, hw, h1, h2, h3⟩⟩
          · exact ⟨h, Or.inl rfl⟩
          · rw [key (w - N) (by omega)] at h3
            exact ⟨h, Or.inr ⟨hop, w, hw, h1, h2, h3⟩⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (PEqualNP.CleanedNonEdge.orStep N (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + gs.length))).flatMap
                (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []).getD (w - N) []) := by
            generalize gs.foldl (PEqualNP.CleanedNonEdge.orStep N) [] = cs at hlen ⊢
            unfold PEqualNP.CleanedNonEdge.orStep
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            simp [hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (rfl | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl rfl⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - N) (by omega)]; exact h3
          · rintro ⟨_, rfl | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl rfl
            · rw [key (w - N) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (PEqualNP.CleanedNonEdge.orStep N (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []) g).getD gs.length [] = [gs.length] := by
            generalize gs.foldl (PEqualNP.CleanedNonEdge.orStep N) [] = cs at hlen ⊢
            unfold PEqualNP.CleanedNonEdge.orStep
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            simp [hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact (hop hop2).elim
      · have e0 : (PEqualNP.CleanedNonEdge.orStep N (gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []) g).getD j [] = [] := by
          change ((gs.foldl (PEqualNP.CleanedNonEdge.orStep N) []) ++ [_]).getD j [] = []
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_append, List.length_singleton, hlen]; omega)]
          rfl
        rw [e0]; simp; omega
  have orReaches_iff (w i : ℕ) :
      PEqualNP.CleanedNonEdge.OrReaches N C w i ↔
        N ≤ w ∧ w < N + C.gates.length ∧
          (i = w - N ∨ ((gateAt C (w - N)).op = GateOp.or ∧
            ∃ b : Fin 2, PEqualNP.CleanedNonEdge.OrReaches N C (opnd C (w - N) b) i)) := by
    unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets
    constructor
    · rintro ⟨hge, hm⟩
      rw [orSets_char C.gates i (w - N)] at hm
      obtain ⟨hlt, h3⟩ := hm
      refine ⟨hge, by omega, ?_⟩
      rcases h3 with rfl | ⟨hop, u, hu, h1, h2, h3⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hop, ?_⟩
        change u ∈ (gateAt C (w - N)).inputs at hu
        rw [gate_inputs_two hlt] at hu
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ⟨0, h1, h3⟩
        · exact ⟨1, h1, h3⟩
    · rintro ⟨hge, hlt, h3⟩
      refine ⟨hge, ?_⟩
      rw [orSets_char C.gates i (w - N)]
      refine ⟨by omega, ?_⟩
      rcases h3 with rfl | ⟨hop, b, hb1, hb2⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hop, opnd C (w - N) b, ?_, hb1, opnd_lt (by omega) b, hb2⟩
        change opnd C (w - N) b ∈ (gateAt C (w - N)).inputs
        rw [gate_inputs_two (by omega)]; fin_cases b <;> simp
  have orReaches_lt {w i : ℕ} (h : PEqualNP.CleanedNonEdge.OrReaches N C w i) : i < C.gates.length ∧ N + i ≤ w := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      rw [orReaches_iff] at h
      obtain ⟨hge, hlt, rfl | ⟨_, b, hb⟩⟩ := h
      · exact ⟨by omega, by omega⟩
      · have hblt := opnd_lt (j := w - N) (by omega) b
        have hres := ih (opnd C (w - N) b) (by omega) hb
        exact ⟨hres.1, by omega⟩
  have orReaches_inCone {j b i} (hj : j < C.gates.length) (h : PEqualNP.CleanedNonEdge.OrReaches N C (opnd C j b) i) :
      InCone N C i j := by
    have hrec : ∀ w, PEqualNP.CleanedNonEdge.OrReaches N C w i → ∀ k < C.gates.length, w = N + k →
        i = k ∨ InCone N C i k := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hr k hk heq
        rw [orReaches_iff] at hr
        obtain ⟨hge, hlt, rfl | ⟨_, c, hc⟩⟩ := hr
        · exact Or.inl (by omega)
        · have heq2 : w - N = k := by omega
          rw [heq2] at hc
          have hltc := opnd_lt hk c
          have hgec : N ≤ opnd C k c := (orReaches_iff _ _).mp hc |>.1
          have hltc2 : opnd C k c - N < C.gates.length := by omega
          have hsub := ih (opnd C k c) (by omega) hc (opnd C k c - N) hltc2 (by omega)
          exact Or.inr (inCone_step hk c hgec hsub)
    have hge : N ≤ opnd C j b := (orReaches_iff _ _).mp h |>.1
    have hlt := opnd_lt hj b
    have hsub := hrec (opnd C j b) h (opnd C j b - N) (by omega) (by omega)
    exact inCone_step hj b hge hsub
  have orReaches_val {w i : ℕ} (h : PEqualNP.CleanedNonEdge.OrReaches N C w i) (x : Fin N → Bool) :
      wval (N + i) x = true → wval w x = true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      rw [orReaches_iff] at h
      obtain ⟨hge, hlt, rfl | ⟨hop, b, hb⟩⟩ := h
      · have heq : N + (w - N) = w := by omega
        rw [heq]; exact id
      · intro hi
        have hblt := opnd_lt (j := w - N) (by omega) b
        have hbv := ih (opnd C (w - N) b) (by omega) hb hi
        have heq : N + (w - N) = w := by omega
        rw [← heq, wval_gate (by omega) x, if_neg (by intro h; rw [hop] at h; cases h), Bool.or_eq_true]
        fin_cases b
        · exact Or.inl hbv
        · exact Or.inr hbv
  have orReaches_sSet_sub {w i : ℕ} (h : PEqualNP.CleanedNonEdge.OrReaches N C w i) :
      sSet (N + i) ⊆ sSet w := by
    intro u hu
    simp only [sSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact orReaches_val h (single u) hu
  -- Step 2: Every edge (p, l) ∈ E is covered by an AND gate a in F
  let F0 : Finset ℕ := (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches N C C.output j
  have find_and_from_top (w : ℕ) (x : Fin N → Bool)
      (hBelow : ∀ u : Fin N, wval w (single u) = false) (ht : wval w x = true) :
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
        PEqualNP.CleanedNonEdge.OrReaches N C w a ∧ wval (N + a) x = true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hw : w < N
      · have h1 := hBelow ⟨w, hw⟩
        rw [wval_input ⟨w, hw⟩ (single ⟨w, hw⟩)] at h1
        simp [single] at h1
      · by_cases hw2 : w < N + C.gates.length
        · have hj : w - N < C.gates.length := by omega
          have heq : N + (w - N) = w := by omega
          rcases hAO.1 (gateAt C (w - N)) (gateAt_mem hj) with hop | hop
          · refine ⟨w - N, hj, hop, ?_, by rwa [heq]⟩
            rw [orReaches_iff]; exact ⟨by omega, hw2, Or.inl rfl⟩
          · rw [← heq, wval_gate hj x, if_neg (by intro h; rw [hop] at h; cases h), Bool.or_eq_true] at ht
            have hSubBelow (b : Fin 2) : ∀ u : Fin N, wval (opnd C (w - N) b) (single u) = false := by
              intro u
              have h0 := hBelow u
              rw [← heq, wval_gate hj (single u), if_neg (by intro h; rw [hop] at h; cases h), Bool.or_eq_false_iff] at h0
              fin_cases b
              · exact h0.1
              · exact h0.2
            rcases ht with h0 | h1
            · obtain ⟨a, ha, hopa, hra, hva⟩ := ih (opnd C (w - N) 0) (by have := opnd_lt hj 0; omega) (hSubBelow 0) h0
              exact ⟨a, ha, hopa, (orReaches_iff w a).mpr ⟨by omega, hw2, Or.inr ⟨hop, 0, hra⟩⟩, hva⟩
            · obtain ⟨a, ha, hopa, hra, hva⟩ := ih (opnd C (w - N) 1) (by have := opnd_lt hj 1; omega) (hSubBelow 1) h1
              exact ⟨a, ha, hopa, (orReaches_iff w a).mpr ⟨by omega, hw2, Or.inr ⟨hop, 1, hra⟩⟩, hva⟩
        · rw [wval_ge w (by omega) x] at ht; cases ht
  -- From an operand of an AND gate in F0, no AND gate can be true (by hTop!), so wval w x = true → ∃ u ∈ sSet w, x u = true
  have operand_sSet_hit {a : ℕ} (ha : a < C.gates.length) (hopa : (gateAt C a).op = GateOp.and)
      (b : Fin 2) (x : Fin N → Bool) :
      wval (opnd C a b) x = true → ∃ u ∈ sSet (opnd C a b), x u = true := by
    have rec_hit : ∀ w, (∀ i < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches N C w i → (gateAt C i).op ≠ GateOp.and) →
        wval w x = true → ∃ u ∈ sSet w, x u = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hno ht
        by_cases hw : w < N
        · rw [wval_input ⟨w, hw⟩ x] at ht
          have hsu : sSet w = {⟨w, hw⟩} := sSet_input ⟨w, hw⟩
          exact ⟨⟨w, hw⟩, by rw [hsu]; exact Finset.mem_singleton_self _, ht⟩
        · by_cases hw2 : w < N + C.gates.length
          · have hj : w - N < C.gates.length := by omega
            have heq : N + (w - N) = w := by omega
            have hnotand : (gateAt C (w - N)).op ≠ GateOp.and :=
              hno (w - N) hj ((orReaches_iff w (w - N)).mpr ⟨by omega, hw2, Or.inl rfl⟩)
            have hop : (gateAt C (w - N)).op = GateOp.or :=
              (hAO.1 (gateAt C (w - N)) (gateAt_mem hj)).resolve_left hnotand
            rw [← heq, wval_gate hj x, if_neg hnotand, Bool.or_eq_true] at ht
            rcases ht with h0 | h1
            · have hno0 : ∀ i < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches N C (opnd C (w - N) 0) i → (gateAt C i).op ≠ GateOp.and :=
                fun i hi hr => hno i hi ((orReaches_iff w i).mpr ⟨by omega, hw2, Or.inr ⟨hop, 0, hr⟩⟩)
              obtain ⟨u, hu, hxu⟩ := ih (opnd C (w - N) 0) (by have := opnd_lt hj 0; omega) hno0 h0
              exact ⟨u, by rw [← heq, sSet_or hj hop]; exact Finset.mem_union_left _ hu, hxu⟩
            · have hno1 : ∀ i < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches N C (opnd C (w - N) 1) i → (gateAt C i).op ≠ GateOp.and :=
                fun i hi hr => hno i hi ((orReaches_iff w i).mpr ⟨by omega, hw2, Or.inr ⟨hop, 1, hr⟩⟩)
              obtain ⟨u, hu, hxu⟩ := ih (opnd C (w - N) 1) (by have := opnd_lt hj 1; omega) hno1 h1
              exact ⟨u, by rw [← heq, sSet_or hj hop]; exact Finset.mem_union_right _ hu, hxu⟩
          · rw [wval_ge w (by omega) x] at ht; cases ht
    apply rec_hit (opnd C a b)
    intro i hi hr hopi
    exact hTop i hi a ha hopi hopa (orReaches_inCone ha hr)
  -- Step 3: Star property for every a ∈ F0
  have noFourCycle : ∀ u v : Fin N, u ≠ v →
      (Finset.univ.filter fun w : Fin N => G.Adj u w ∧ G.Adj v w).card ≤ 1 := by
    intro u v huv
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    by_contra hne
    obtain ⟨e1, he1, h1⟩ := (adj u w1).mp hw1.1
    obtain ⟨e2, he2, h2⟩ := (adj v w1).mp hw1.2
    obtain ⟨e3, he3, h3⟩ := (adj u w2).mp hw2.1
    obtain ⟨e4, he4, h4⟩ := (adj v w2).mp hw2.2
    rcases h1 with ⟨hu1, hw1r⟩ | ⟨hw1l, hu1⟩
    · rcases h2 with ⟨hv1, hw1r2⟩ | ⟨hw1l2, _⟩
      · rcases h3 with ⟨hu2, hw2r⟩ | ⟨_, hu2⟩
        · rcases h4 with ⟨hv2, hw2r2⟩ | ⟨_, hv2⟩
          · have hp : e1.1 ≠ e2.1 := fun eq => huv (hu1.trans ((congrArg left eq).trans hv1.symm))
            have hl : e1.2 ≠ e3.2 := fun eq => hne (hw1r.trans ((congrArg right eq).trans hw2r.symm))
            have he2_2 : e2.2 = e1.2 := rightInj (hw1r2.symm.trans hw1r)
            have he3_1 : e3.1 = e1.1 := leftInj (hu2.symm.trans hu1)
            have he4_1 : e4.1 = e2.1 := leftInj (hv2.symm.trans hv1)
            have he4_2 : e4.2 = e3.2 := rightInj (hw2r2.symm.trans hw2r)
            exact hSquare e1.1 e2.1 e1.2 e3.2 hp hl
              ⟨he1, by rwa [← he3_1], by rwa [← he2_2], by rw [← he4_1, ← he4_2]; exact he4⟩
          · exact (sides _ _ (hv1.symm.trans hv2)).elim
        · exact (sides _ _ (hu1.symm.trans hu2)).elim
      · exact (sides _ _ (hw1l2.symm.trans hw1r)).elim
    · rcases h2 with ⟨_, hw1r2⟩ | ⟨hw1l2, hv1⟩
      · exact (sides _ _ (hw1l.symm.trans hw1r2)).elim
      · rcases h3 with ⟨hu2, _⟩ | ⟨hw2l, hu2⟩
        · exact (sides _ _ (hu2.symm.trans hu1)).elim
        · rcases h4 with ⟨hv2, _⟩ | ⟨hw2l2, hv2⟩
          · exact (sides _ _ (hv2.symm.trans hv1)).elim
          · have hp : e1.1 ≠ e3.1 := fun eq => hne (hw1l.trans ((congrArg left eq).trans hw2l.symm))
            have hl : e1.2 ≠ e2.2 := fun eq => huv (hu1.trans ((congrArg right eq).trans hv1.symm))
            have he2_1 : e2.1 = e1.1 := leftInj (hw1l2.symm.trans hw1l)
            have he3_2 : e3.2 = e1.2 := rightInj (hu2.symm.trans hu1)
            have he4_1 : e4.1 = e3.1 := leftInj (hw2l2.symm.trans hw2l)
            have he4_2 : e4.2 = e2.2 := rightInj (hv2.symm.trans hv1)
            exact hSquare e1.1 e3.1 e1.2 e2.2 hp hl
              ⟨he1, by rwa [← he2_1], by rwa [← he3_2], by rw [← he4_1, ← he4_2]; exact he4⟩
  have side_adj {a : ℕ} (ha : a ∈ F0) {u v : Fin N}
      (hu : u ∈ sSet (opnd C a 0)) (hv : v ∈ sSet (opnd C a 1)) : G.Adj u v := by
    simp only [F0, Finset.mem_filter, Finset.mem_range] at ha
    simp only [sSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have h0 : wval (opnd C a 0) (pairInput u v) = true :=
      wval_mono _ _ _ (fun k hk => by simp only [single, decide_eq_true_eq] at hk; rw [hk]; change decide (u = u ∨ u = v) = true; simp) hu
    have h1 : wval (opnd C a 1) (pairInput u v) = true :=
      wval_mono _ _ _ (fun k hk => by simp only [single, decide_eq_true_eq] at hk; rw [hk]; change decide (v = u ∨ v = v) = true; simp) hv
    have hga : gateVal N C a (pairInput u v) = true := by
      change wval (N + a) (pairInput u v) = true
      rw [wval_gate ha.1, ite_eq_left ha.2.1, h0, h1]; rfl
    have hf := hClean a ha.1 ha.2.1 (pairInput u v) hga
    rw [hEval, decide_eq_true_eq] at hf
    obtain ⟨p, l, hpl, hp, hl⟩ := hf
    change decide (left p = u ∨ left p = v) = true at hp
    change decide (right l = u ∨ right l = v) = true at hl
    rw [decide_eq_true_eq] at hp hl
    rcases hp with hpu | hpv <;> rcases hl with hlu | hlv
    · exact (sides p l (hpu.trans hlu.symm)).elim
    · exact (adj u v).mpr ⟨(p, l), hpl, Or.inl ⟨hpu.symm, hlv.symm⟩⟩
    · exact (adj u v).mpr ⟨(p, l), hpl, Or.inr ⟨hpv.symm, hlu.symm⟩⟩
    · exact (sides p l (hpv.trans hlv.symm)).elim
  have side_star {a : ℕ} (ha : a ∈ F0) :
      (sSet (opnd C a 0)).card ≤ 1 ∨ (sSet (opnd C a 1)).card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp h.1
    obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp h.2
    have hle := noFourCycle u1 u2 hu12
    have hmem1 : v1 ∈ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, side_adj ha hu1 hv1, side_adj ha hu2 hv1⟩
    have hmem2 : v2 ∈ Finset.univ.filter (fun w => G.Adj u1 w ∧ G.Adj u2 w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, side_adj ha hu1 hv2, side_adj ha hu2 hv2⟩
    exact hv12 (Finset.card_le_one.mp hle v1 hmem1 v2 hmem2)
  let F : Finset ℕ := F0.filter fun a => (sSet (opnd C a 0)).Nonempty ∧ (sSet (opnd C a 1)).Nonempty
  have edge_covered (e : Fin n × Fin m) (he : e ∈ E) :
      ∃ a ∈ F, (left e.1 ∈ sSet (opnd C a 0) ∧ right e.2 ∈ sSet (opnd C a 1)) ∨
               (right e.2 ∈ sSet (opnd C a 0) ∧ left e.1 ∈ sSet (opnd C a 1)) := by
    have hft : wval C.output (pairInput (left e.1) (right e.2)) = true := by
      change circuitFun N C (pairInput (left e.1) (right e.2)) = true
      rw [hEval, decide_eq_true_eq]
      exact ⟨e.1, e.2, he, by change decide (left e.1 = left e.1 ∨ left e.1 = right e.2) = true; simp,
        by change decide (right e.2 = left e.1 ∨ right e.2 = right e.2) = true; simp⟩
    obtain ⟨a, ha, hopa, hra, hva⟩ := find_and_from_top C.output (pairInput (left e.1) (right e.2)) f_single_false hft
    have haF0 : a ∈ F0 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hopa, hra⟩
    rw [wval_gate ha, ite_eq_left hopa, Bool.and_eq_true] at hva
    obtain ⟨u, hu, hxu⟩ := operand_sSet_hit ha hopa 0 _ hva.1
    obtain ⟨v, hv, hxv⟩ := operand_sSet_hit ha hopa 1 _ hva.2
    have haF : a ∈ F := Finset.mem_filter.mpr ⟨haF0, ⟨u, hu⟩, ⟨v, hv⟩⟩
    have huv : u ≠ v := (side_adj haF0 hu hv).ne
    change decide (u = left e.1 ∨ u = right e.2) = true at hxu
    change decide (v = left e.1 ∨ v = right e.2) = true at hxv
    rw [decide_eq_true_eq] at hxu hxv
    rcases hxu with rfl | rfl <;> rcases hxv with rfl | rfl
    · exact (huv rfl).elim
    · exact ⟨a, haF, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨a, haF, Or.inr ⟨hu, hv⟩⟩
    · exact (huv rfl).elim
  -- Center and leaf operand for each a ∈ F
  have hCtrEx (a : ℕ) (ha : a ∈ F) :
      ∃ c : Fin N, ∃ lf : ℕ, (lf = opnd C a 0 ∨ lf = opnd C a 1) ∧
        (∀ u ∈ sSet lf, G.Adj c u) ∧
        (∀ u v : Fin N, (u ∈ sSet (opnd C a 0) ∧ v ∈ sSet (opnd C a 1)) ∨
          (v ∈ sSet (opnd C a 0) ∧ u ∈ sSet (opnd C a 1)) →
          (u = c ∧ v ∈ sSet lf) ∨ (v = c ∧ u ∈ sSet lf)) := by
    have ha0 : a ∈ F0 := (Finset.mem_filter.mp ha).1
    have hne := (Finset.mem_filter.mp ha).2
    rcases side_star ha0 with h0 | h1
    · obtain ⟨c, hc⟩ := hne.1
      have hsub0 : ∀ x ∈ sSet (opnd C a 0), x = c := fun x hx => Finset.card_le_one.mp h0 x hx c hc
      refine ⟨c, opnd C a 1, Or.inr rfl, fun u hu => side_adj ha0 hc hu, ?_⟩
      rintro u v (⟨hu, hv⟩ | ⟨hv, hu⟩)
      · exact Or.inl ⟨hsub0 u hu, hv⟩
      · exact Or.inr ⟨hsub0 v hv, hu⟩
    · obtain ⟨c, hc⟩ := hne.2
      have hsub1 : ∀ x ∈ sSet (opnd C a 1), x = c := fun x hx => Finset.card_le_one.mp h1 x hx c hc
      refine ⟨c, opnd C a 0, Or.inl rfl, fun u hu => (side_adj ha0 hu hc).symm, ?_⟩
      rintro u v (⟨hu, hv⟩ | ⟨hv, hu⟩)
      · exact Or.inr ⟨hsub1 v hv, hu⟩
      · exact Or.inl ⟨hsub1 u hu, hv⟩
  let ctr (a : ℕ) : Fin N := if ha : a ∈ F then Classical.choose (hCtrEx a ha) else ⟨0, by
    have := e0.1.isLt; omega⟩
  let lf (a : ℕ) : ℕ := if ha : a ∈ F then Classical.choose (Classical.choose_spec (hCtrEx a ha)) else 0
  have hCtrSpec {a : ℕ} (ha : a ∈ F) :
      (lf a = opnd C a 0 ∨ lf a = opnd C a 1) ∧
      (∀ u ∈ sSet (lf a), G.Adj (ctr a) u) ∧
      (∀ u v : Fin N, (u ∈ sSet (opnd C a 0) ∧ v ∈ sSet (opnd C a 1)) ∨
        (v ∈ sSet (opnd C a 0) ∧ u ∈ sSet (opnd C a 1)) →
        (u = ctr a ∧ v ∈ sSet (lf a)) ∨ (v = ctr a ∧ u ∈ sSet (lf a))) := by
    simp only [ctr, lf, dif_pos ha]
    exact Classical.choose_spec (Classical.choose_spec (hCtrEx a ha))
  -- Step 4A: Top OR gates count: F.card ≤ OrTop.card + 1
  let OrTop : Finset ℕ := (Finset.range C.gates.length).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches N C C.output i
  have hTopCount : F.card ≤ OrTop.card + 1 := by
    have hF_sub : F ⊆ F0 := Finset.filter_subset _ _
    let V := F ∪ OrTop
    have hDisj : Disjoint F OrTop := by
      rw [Finset.disjoint_left]
      intro j hjF hjO
      have h1 := (Finset.mem_filter.mp (hF_sub hjF)).2.1
      have h2 := (Finset.mem_filter.mp hjO).2.1
      rw [h1] at h2; cases h2
    have hRootMem : C.output - N ∈ F0 ∪ OrTop := by
      have hlt : C.output - N < C.gates.length := by omega
      have hr : PEqualNP.CleanedNonEdge.OrReaches N C C.output (C.output - N) :=
        (orReaches_iff C.output (C.output - N)).mpr ⟨hOutBounds.1, hOutBounds.2, Or.inl rfl⟩
      rcases hAO.1 (gateAt C (C.output - N)) (gateAt_mem hlt) with hop | hop
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hop, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hop, hr⟩)
    -- Every gate in F0 ∪ OrTop other than root is an operand of some gate in OrTop
    have hCover : (F0 ∪ OrTop).erase (C.output - N) ⊆
        OrTop.biUnion fun k => ({opnd C k 0 - N, opnd C k 1 - N} : Finset ℕ) := by
      intro i hi
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
      have hri : PEqualNP.CleanedNonEdge.OrReaches N C C.output i := by
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact (Finset.mem_filter.mp h1).2.2
        · exact (Finset.mem_filter.mp h2).2.2
      -- Walk down from C.output to find immediate predecessor k ∈ OrTop
      have hPred : ∀ w, PEqualNP.CleanedNonEdge.OrReaches N C w i → w ≠ N + i →
          ∃ k < C.gates.length, (gateAt C k).op = GateOp.or ∧
            PEqualNP.CleanedNonEdge.OrReaches N C w k ∧
            (opnd C k 0 = N + i ∨ opnd C k 1 = N + i) := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hr hwne
          rw [orReaches_iff] at hr
          obtain ⟨hge, hlt, rfl | ⟨hop, b, hb⟩⟩ := hr
          · exact (hwne (by omega)).elim
          · by_cases heq : opnd C (w - N) b = N + i
            · refine ⟨w - N, by omega, hop, (orReaches_iff w (w - N)).mpr ⟨hge, hlt, Or.inl rfl⟩, ?_⟩
              fin_cases b
              · exact Or.inl heq
              · exact Or.inr heq
            · have hblt := opnd_lt (j := w - N) (by omega) b
              obtain ⟨k, hk, hopk, hrk, heqk⟩ := ih (opnd C (w - N) b) (by omega) hb heq
              exact ⟨k, hk, hopk, (orReaches_iff w k).mpr ⟨hge, hlt, Or.inr ⟨hop, b, hrk⟩⟩, heqk⟩
      obtain ⟨k, hk, hopk, hrk, heqk⟩ := hPred C.output hri (by omega)
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hopk, hrk⟩, ?_⟩
      rcases heqk with h0 | h1
      · simp [h0]
      · simp [h1]
    have hCard1 : ((F0 ∪ OrTop).erase (C.output - N)).card ≤ 2 * OrTop.card := by
      calc ((F0 ∪ OrTop).erase (C.output - N)).card
          ≤ (OrTop.biUnion fun k => ({opnd C k 0 - N, opnd C k 1 - N} : Finset ℕ)).card :=
            Finset.card_le_card hCover
        _ ≤ ∑ k ∈ OrTop, ({opnd C k 0 - N, opnd C k 1 - N} : Finset ℕ).card := Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ OrTop, 2 := Finset.sum_le_sum fun k _ => Finset.card_le_two
        _ = 2 * OrTop.card := by simp [Nat.mul_comm]
    have hDisj0 : Disjoint F0 OrTop := by
      rw [Finset.disjoint_left]
      intro j hjF hjO
      have h1 := (Finset.mem_filter.mp hjF).2.1
      have h2 := (Finset.mem_filter.mp hjO).2.1
      rw [h1] at h2; cases h2
    have hCard2 : F0.card + OrTop.card = (F0 ∪ OrTop).card := (Finset.card_union_of_disjoint hDisj0).symm
    have hCard3 : ((F0 ∪ OrTop).erase (C.output - N)).card + 1 = (F0 ∪ OrTop).card :=
      Finset.card_erase_add_one hRootMem
    have hF_le : F.card ≤ F0.card := Finset.card_le_card hF_sub
    omega
  -- Step 4B: Leaf OR gates count: E.card ≤ OrLeaf.card + F.card
  let OrLeaf : Finset ℕ := (Finset.range C.gates.length).filter fun i =>
    (gateAt C i).op = GateOp.or ∧ 2 ≤ (sSet (N + i)).card ∧
      ∃ a ∈ F, PEqualNP.CleanedNonEdge.OrReaches N C (lf a) i
  have hTopLeafDisj : Disjoint OrTop OrLeaf := by
    rw [Finset.disjoint_left]
    intro i hiT hiL
    have hr := (Finset.mem_filter.mp hiT).2.2
    have h2 := (Finset.mem_filter.mp hiL).2.2.1
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (sSet (N + i)).card)
    simp only [sSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hf : circuitFun N C (single u) = true := orReaches_val hr (single u) hu
    rw [f_single_false u] at hf; cases hf
  have hFLeafDisj : Disjoint F OrLeaf := by
    rw [Finset.disjoint_left]
    intro i hiF hiL
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hiF).1).2.1
    have h2 := (Finset.mem_filter.mp hiL).2.1
    rw [h1] at h2; cases h2
  have hFTopDisj : Disjoint F OrTop := by
    rw [Finset.disjoint_left]
    intro i hiF hiT
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hiF).1).2.1
    have h2 := (Finset.mem_filter.mp hiT).2.1
    rw [h1] at h2; cases h2
  let T : Finset (Fin N) := F.image ctr
  have hT_le_F : T.card ≤ F.card := Finset.card_image_le
  let Sc (c : Fin N) : Finset (Fin N) := Finset.univ.filter fun b =>
    ∃ a ∈ F, ctr a = c ∧ b ∈ sSet (lf a)
  let Fc (c : Fin N) : Finset ℕ := F.filter fun a => ctr a = c
  let Oc (c : Fin N) : Finset ℕ := OrLeaf.filter fun i =>
    ∃ a ∈ Fc c, PEqualNP.CleanedNonEdge.OrReaches N C (lf a) i
  have hOc_disj : ∀ c1 ∈ T, ∀ c2 ∈ T, c1 ≠ c2 → Disjoint (Oc c1) (Oc c2) := by
    intro c1 _ c2 _ hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi1).1).2.2.1
    obtain ⟨a1, ha1, hr1⟩ := (Finset.mem_filter.mp hi1).2
    obtain ⟨a2, ha2, hr2⟩ := (Finset.mem_filter.mp hi2).2
    obtain ⟨ha1F, hc1⟩ := Finset.mem_filter.mp ha1
    obtain ⟨ha2F, hc2⟩ := Finset.mem_filter.mp ha2
    have hsub1 := orReaches_sSet_sub hr1
    have hsub2 := orReaches_sSet_sub hr2
    obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < (sSet (N + i)).card)
    have hle := noFourCycle c1 c2 hne
    have hm1 : u1 ∈ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hc1 ▸ (hCtrSpec ha1F).2.1 u1 (hsub1 hu1), hc2 ▸ (hCtrSpec ha2F).2.1 u1 (hsub2 hu1)⟩
    have hm2 : u2 ∈ Finset.univ.filter (fun w => G.Adj c1 w ∧ G.Adj c2 w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hc1 ▸ (hCtrSpec ha1F).2.1 u2 (hsub1 hu2), hc2 ▸ (hCtrSpec ha2F).2.1 u2 (hsub2 hu2)⟩
    exact hu12 (Finset.card_le_one.mp hle u1 hm1 u2 hm2)
  have hSc_le (c : Fin N) : (Sc c).card ≤ (Oc c).card + (Fc c).card := by
    -- Representative map: wire w → none if sSet w = ∅, inl b if sSet w = {b}, inr (w - N) if |sSet w| ≥ 2
    let rep (w : ℕ) : Option (Fin N ⊕ ℕ) :=
      if h2 : 2 ≤ (sSet w).card then some (Sum.inr (w - N))
      else if h1 : (sSet w).Nonempty then some (Sum.inl (Classical.choose h1))
      else none
    have rep_eq_inl {w : ℕ} {b : Fin N} (h : sSet w = {b}) : rep w = some (Sum.inl b) := by
      have hcard : (sSet w).card = 1 := by rw [h]; simp
      have hne : (sSet w).Nonempty := ⟨b, by rw [h]; simp⟩
      simp only [rep, show ¬ (2 ≤ (sSet w).card) by omega, ↓reduceDIte, dif_pos hne]
      have hmem : Classical.choose hne ∈ ({b} : Finset (Fin N)) := h ▸ Classical.choose_spec hne
      rw [Finset.mem_singleton.mp hmem]
    have rep_eq_inr {w : ℕ} (h2 : 2 ≤ (sSet w).card) : rep w = some (Sum.inr (w - N)) := by
      simp only [rep, dif_pos h2]
    let LHS : Finset (Option (Fin N ⊕ ℕ)) :=
      (Sc c).image (fun b => some (Sum.inl b)) ∪ (Oc c).image (fun k => some (Sum.inr k))
    let RHS : Finset (Option (Fin N ⊕ ℕ)) :=
      (Fc c).image (fun a => rep (lf a)) ∪
      (Oc c).biUnion (fun k => {rep (opnd C k 0), rep (opnd C k 1)})
    have hSubLR : LHS ⊆ RHS := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz1 | hz2
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨a, haF, hca, hba⟩ := (Finset.mem_filter.mp hb).2
        have haFc : a ∈ Fc c := Finset.mem_filter.mpr ⟨haF, hca⟩
        have hWalk2 : ∀ w, (∀ k < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches N C w k →
            PEqualNP.CleanedNonEdge.OrReaches N C (lf a) k) →
            b ∈ sSet w →
            sSet w = {b} ∨ ∃ k ∈ Oc c, sSet (opnd C k 0) = {b} ∨ sSet (opnd C k 1) = {b} := by
          intro w
          induction w using Nat.strong_induction_on with
          | _ w ih =>
            intro hreach hbw
            by_cases h2 : 2 ≤ (sSet w).card
            · have hwge : N ≤ w := by
                by_contra hlt; push_neg at hlt; rw [sSet_input ⟨w, hlt⟩] at h2; simp at h2
              have hwlt : w < N + C.gates.length := by
                by_contra hge2; push_neg at hge2
                have : sSet w = ∅ := by ext u; simp [sSet, wval_ge w hge2 (single u)]
                rw [this] at h2; simp at h2
              have hk : w - N < C.gates.length := by omega
              have heq : N + (w - N) = w := by omega
              have hop : (gateAt C (w - N)).op = GateOp.or := by
                rcases hAO.1 (gateAt C (w - N)) (gateAt_mem hk) with h | h
                · rw [← heq, sSet_and hk h] at h2; simp at h2
                · exact h
              have hrk : PEqualNP.CleanedNonEdge.OrReaches N C (lf a) (w - N) :=
                hreach (w - N) hk ((orReaches_iff w (w - N)).mpr ⟨hwge, hwlt, Or.inl rfl⟩)
              have hkOc : w - N ∈ Oc c := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, ?_, ⟨a, haF, hrk⟩⟩, ⟨a, haFc, hrk⟩⟩
                rwa [heq]
              rw [← heq, sSet_or hk hop, Finset.mem_union] at hbw
              rcases hbw with hb0 | hb1
              · rcases ih (opnd C (w - N) 0) (by have := opnd_lt hk 0; omega)
                    (fun k' hk' hr' => hreach k' hk' ((orReaches_iff w k').mpr ⟨hwge, hwlt, Or.inr ⟨hop, 0, hr'⟩⟩)) hb0 with h1 | hres
                · exact Or.inr ⟨w - N, hkOc, Or.inl h1⟩
                · exact Or.inr hres
              · rcases ih (opnd C (w - N) 1) (by have := opnd_lt hk 1; omega)
                    (fun k' hk' hr' => hreach k' hk' ((orReaches_iff w k').mpr ⟨hwge, hwlt, Or.inr ⟨hop, 1, hr'⟩⟩)) hb1 with h1 | hres
                · exact Or.inr ⟨w - N, hkOc, Or.inr h1⟩
                · exact Or.inr hres
            · left
              have hle1 : (sSet w).card ≤ 1 := by omega
              ext u; simp only [Finset.mem_singleton]
              exact ⟨fun hu => Finset.card_le_one.mp hle1 u hu b hbw, fun hu => hu ▸ hbw⟩
        rcases hWalk2 (lf a) (fun _ _ h => h) hba with h1 | ⟨k, hkOc, h0 | h1⟩
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haFc, rep_eq_inl h1⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hkOc, by simp [rep_eq_inl h0]⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hkOc, by simp [rep_eq_inl h1]⟩)
      · obtain ⟨k, hkOc, rfl⟩ := Finset.mem_image.mp hz2
        have hkLeaf := (Finset.mem_filter.mp hkOc).1
        have hk2 := (Finset.mem_filter.mp hkLeaf).2.2.1
        obtain ⟨a, haFc, hrk⟩ := (Finset.mem_filter.mp hkOc).2
        have haF := (Finset.mem_filter.mp haFc).1
        by_cases heq : lf a = N + k
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haFc, ?_⟩)
          rw [heq, rep_eq_inr hk2]
          simp
        · -- Walk from lf a to immediate predecessor k' ∈ Oc c of k
          have hPred : ∀ w, (∀ j < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches N C w j →
              PEqualNP.CleanedNonEdge.OrReaches N C (lf a) j) →
              PEqualNP.CleanedNonEdge.OrReaches N C w k → w ≠ N + k →
              ∃ k' ∈ Oc c, opnd C k' 0 = N + k ∨ opnd C k' 1 = N + k := by
            intro w
            induction w using Nat.strong_induction_on with
            | _ w ih =>
              intro hreach hr hwne
              rw [orReaches_iff] at hr
              obtain ⟨hge, hlt, rfl | ⟨hop, b, hb⟩⟩ := hr
              · exact (hwne (by omega)).elim
              · have hk' : w - N < C.gates.length := by omega
                have hrk' : PEqualNP.CleanedNonEdge.OrReaches N C (lf a) (w - N) :=
                  hreach (w - N) hk' ((orReaches_iff w (w - N)).mpr ⟨hge, hlt, Or.inl rfl⟩)
                have h2k' : 2 ≤ (sSet (N + (w - N))).card := by
                  have hsub := orReaches_sSet_sub ((orReaches_iff w k).mpr ⟨hge, hlt, Or.inr ⟨hop, b, hb⟩⟩)
                  have heqw : N + (w - N) = w := by omega
                  rw [heqw]
                  exact hk2.trans (Finset.card_le_card hsub)
                have hk'Oc : w - N ∈ Oc c :=
                  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk', hop, h2k', ⟨a, haF, hrk'⟩⟩, ⟨a, haFc, hrk'⟩⟩
                by_cases hbe : opnd C (w - N) b = N + k
                · refine ⟨w - N, hk'Oc, ?_⟩
                  fin_cases b
                  · exact Or.inl hbe
                  · exact Or.inr hbe
                · exact ih (opnd C (w - N) b) (by have := opnd_lt hk' b; omega)
                    (fun j hj hrj => hreach j hj ((orReaches_iff w j).mpr ⟨hge, hlt, Or.inr ⟨hop, b, hrj⟩⟩)) hb hbe
          obtain ⟨k', hk'Oc, h0 | h1⟩ := hPred (lf a) (fun _ _ h => h) hrk heq
          · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k', hk'Oc, ?_⟩)
            simp [h0, rep_eq_inr hk2]
          · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k', hk'Oc, ?_⟩)
            simp [h1, rep_eq_inr hk2]
    have hDisjL : Disjoint ((Sc c).image (fun b => some (Sum.inl b))) ((Oc c).image (fun k => some (Sum.inr k))) := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨k, _, h⟩ := Finset.mem_image.mp h2
      cases h
    have hLHS : LHS.card = (Sc c).card + (Oc c).card := by
      rw [Finset.card_union_of_disjoint hDisjL,
          Finset.card_image_of_injective _ (fun _ _ h => Sum.inl_injective (Option.some_injective _ h)),
          Finset.card_image_of_injective _ (fun _ _ h => Sum.inr_injective (Option.some_injective _ h))]
    have hRHS : RHS.card ≤ (Fc c).card + 2 * (Oc c).card := by
      calc RHS.card
          ≤ ((Fc c).image (fun a => rep (lf a))).card +
              ((Oc c).biUnion (fun k => {rep (opnd C k 0), rep (opnd C k 1)})).card := Finset.card_union_le _ _
        _ ≤ (Fc c).card + ∑ k ∈ Oc c, ({rep (opnd C k 0), rep (opnd C k 1)} : Finset _).card :=
            Nat.add_le_add Finset.card_image_le Finset.card_biUnion_le
        _ ≤ (Fc c).card + ∑ _k ∈ Oc c, 2 := Nat.add_le_add_left (Finset.sum_le_sum fun _ _ => Finset.card_le_two) _
        _ = (Fc c).card + 2 * (Oc c).card := by simp [Nat.mul_comm]
    have hle := (Finset.card_le_card hSubLR).trans hRHS
    omega
  have hSumSc : ∑ c ∈ T, (Sc c).card ≤ OrLeaf.card + F.card := by
    have h1 : ∑ c ∈ T, (Sc c).card ≤ (∑ c ∈ T, (Oc c).card) + ∑ c ∈ T, (Fc c).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun c _ => hSc_le c
    have h2 : ∑ c ∈ T, (Oc c).card ≤ OrLeaf.card := by
      rw [← Finset.card_biUnion (fun c1 hc1 c2 hc2 hne => hOc_disj c1 hc1 c2 hc2 hne)]
      exact Finset.card_le_card (Finset.biUnion_subset.mpr fun c _ => Finset.filter_subset _ _)
    have h3 : ∑ c ∈ T, (Fc c).card = F.card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext a
        simp only [Finset.mem_biUnion, Fc, Finset.mem_filter, T, Finset.mem_image]
        exact ⟨by rintro ⟨_, _, ha, _⟩; exact ha, fun ha => ⟨ctr a, ⟨a, ha, rfl⟩, ha, rfl⟩⟩
      · intro c1 _ c2 _ hne
        change Disjoint (Fc c1) (Fc c2)
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
    omega
  have hE_le_SumSc : E.card ≤ ∑ c ∈ T, (Sc c).card := by
    let fE (e : Fin n × Fin m) : Σ _ : Fin N, Fin N :=
      if h : e ∈ E then
        let a := Classical.choose (edge_covered e h)
        if left e.1 = ctr a ∧ right e.2 ∈ sSet (lf a) then ⟨left e.1, right e.2⟩
        else ⟨right e.2, left e.1⟩
      else ⟨left e0.1, right e0.2⟩
    have hfE_mem (e : Fin n × Fin m) (he : e ∈ E) :
        fE e ∈ T.sigma Sc := by
      simp only [fE, dite_eq_left, Finset.mem_sigma]
      have haF : Classical.choose (edge_covered e he) ∈ F := (Classical.choose_spec (edge_covered e he)).1
      have hcov := (Classical.choose_spec (edge_covered e he)).2
      have hsp := (hCtrSpec haF).2.2 (left e.1) (right e.2) hcov
      split_ifs with h1
      · refine ⟨Finset.mem_image.mpr ⟨_, haF, h1.1.symm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, haF, h1.1.symm, h1.2⟩⟩
      · have h2 : right e.2 = ctr (Classical.choose (edge_covered e he)) ∧ left e.1 ∈ sSet (lf (Classical.choose (edge_covered e he))) :=
          hsp.resolve_left h1
        refine ⟨Finset.mem_image.mpr ⟨_, haF, h2.1.symm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, haF, h2.1.symm, h2.2⟩⟩
    have hfE_inj : Set.InjOn fE ↑E := by
      intro e1 he1 e2 he2 heq
      simp only [Finset.mem_coe] at he1 he2
      simp only [fE, dif_pos he1, dif_pos he2] at heq
      split_ifs at heq
      · have hfst : left e1.1 = left e2.1 := congrArg Sigma.fst heq
        have hsnd : right e1.2 = right e2.2 := congrArg Sigma.snd heq
        exact Prod.ext (leftInj hfst) (rightInj hsnd)
      · exact (sides e1.1 e2.2 (congrArg Sigma.fst heq)).elim
      · exact (sides e2.1 e1.2 (congrArg Sigma.fst heq).symm).elim
      · have hfst : right e1.2 = right e2.2 := congrArg Sigma.fst heq
        have hsnd : left e1.1 = left e2.1 := congrArg Sigma.snd heq
        exact Prod.ext (leftInj hsnd) (rightInj hfst)
    calc E.card = (E.image fE).card := (Finset.card_image_of_injOn hfE_inj).symm
      _ ≤ (T.sigma Sc).card := Finset.card_le_card (Finset.image_subset_iff.mpr hfE_mem)
      _ = ∑ c ∈ T, (Sc c).card := Finset.card_sigma T Sc
  -- Combine all 3 disjoint sets inside Finset.range C.gates.length
  have hSizeLB : E.card + T.card ≤ C.size + 1 := by
    have hSubAll : F ∪ OrTop ∪ OrLeaf ⊆ Finset.range C.gates.length := by
      refine Finset.union_subset (Finset.union_subset ?_ (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
      exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hDisj2 : Disjoint (F ∪ OrTop) OrLeaf := Finset.disjoint_union_left.mpr ⟨hFLeafDisj, hTopLeafDisj⟩
    have hAllCard : F.card + OrTop.card + OrLeaf.card ≤ C.gates.length := by
      calc F.card + OrTop.card + OrLeaf.card
          = (F ∪ OrTop).card + OrLeaf.card := by rw [Finset.card_union_of_disjoint hFTopDisj]
        _ = (F ∪ OrTop ∪ OrLeaf).card := (Finset.card_union_of_disjoint hDisj2).symm
        _ ≤ (Finset.range C.gates.length).card := Finset.card_le_card hSubAll
        _ = C.gates.length := Finset.card_range _
    change E.card + T.card ≤ C.gates.length + 1
    omega
  -- Step 5: Construct explicit two-level IsAO2 circuit D for E' = E.erase e0 of size ≤ E'.card + T.card - 1 < C.size
  let E' := E.erase e0
  have hT_cover : ∀ e ∈ E', left e.1 ∈ T ∨ right e.2 ∈ T := by
    intro e he
    have heE := Finset.mem_of_mem_erase he
    obtain ⟨a, haF, hcov⟩ := edge_covered e heE
    rcases (hCtrSpec haF).2.2 (left e.1) (right e.2) hcov with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨a, haF, h1.symm⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨a, haF, h2.symm⟩)
  -- Partition E' into stars rooted at vertices of T
  let assign (e : Fin n × Fin m) : Fin N := if left e.1 ∈ T then left e.1 else right e.2
  let other (e : Fin n × Fin m) : Fin N := if left e.1 ∈ T then right e.2 else left e.1
  let star (c : Fin N) : Finset (Fin N) := (E'.filter fun e => assign e = c).image other
  let T' : Finset (Fin N) := T.filter fun c => (star c).Nonempty
  have hAssign_mem {e : Fin n × Fin m} (he : e ∈ E') : assign e ∈ T := by
    simp only [assign]
    split_ifs with h
    · exact h
    · exact (hT_cover e he).resolve_left h
  have hStar_card (c : Fin N) : (star c).card = (E'.filter fun e => assign e = c).card := by
    apply Finset.card_image_of_injOn
    intro e1 he1 e2 he2 heq
    simp only [Finset.mem_coe, Finset.mem_filter] at he1 he2
    have h1 := he1.2; have h2 := he2.2
    simp only [assign] at h1 h2
    simp only [other] at heq
    split_ifs at h1 h2 heq
    · exact Prod.ext (leftInj (h1.trans h2.symm)) (rightInj heq)
    · exact (sides e1.1 e2.2 (h1.trans h2.symm)).elim
    · exact (sides e2.1 e1.2 (h2.trans h1.symm)).elim
    · exact Prod.ext (leftInj heq) (rightInj (h1.trans h2.symm))
  have hSum_star : ∑ c ∈ T', (star c).card = E'.card := by
    have h1 : ∑ c ∈ T', (star c).card = ∑ c ∈ T, (star c).card := by
      apply Finset.sum_subset (Finset.filter_subset _ T)
      intro c hcT hc
      simp only [T', Finset.mem_filter, not_and, Finset.not_nonempty_iff_eq_empty] at hc
      have : star c = ∅ := hc hcT
      simp [this]
    rw [h1]
    simp_rw [hStar_card]
    rw [← Finset.card_biUnion]
    · congr 1; ext e; simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨by rintro ⟨_, _, he, _⟩; exact he, fun he => ⟨assign e, hAssign_mem he, he, rfl⟩⟩
    · intro c1 _ c2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hT'_nonempty : T'.Nonempty := by
    obtain ⟨e, he⟩ := hErNonempty
    exact ⟨assign e, Finset.mem_filter.mpr ⟨hAssign_mem he, ⟨other e, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩⟩⟩
  have hT'_le : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
  -- Helper: build a binary OR chain over a nonempty list of wire indices < base
  have buildOr (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) (hlt : ∀ w ∈ ws, w < base) :
      ∃ (gs : List Gate) (out : ℕ), gs.length + 1 = ws.length ∧
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < base + j) ∧
        out < base + gs.length ∧
        ∀ (w0 : List Bool), w0.length = base →
          (gs.foldl stepW w0).getD out false = ws.any (fun u => w0.getD u false) := by
    induction ws generalizing base with
    | nil => exact (hne rfl).elim
    | cons a rest ih =>
      cases rest with
      | nil =>
        refine ⟨[], a, rfl, (by intro _ h; cases h), (by intro _ h; cases h), hlt a List.mem_cons_self, ?_⟩
        intro w0 _
        simp
      | cons b rest' =>
        obtain ⟨gs, out, hlen, hao, hrb, hout, hev⟩ :=
          ih base (List.cons_ne_nil _ _) (fun u hu => hlt u (List.mem_cons_of_mem _ hu))
        let gNew : Gate := ⟨GateOp.or, [a, out]⟩
        refine ⟨gs ++ [gNew], base + gs.length, (by rw [List.length_append, List.length_singleton, List.length_cons]; omega), ?_, ?_, (by simp), ?_⟩
        · intro g hg
          rcases List.mem_append.mp hg with hg1 | hg2
          · exact hao g hg1
          · rw [List.mem_singleton.mp hg2]; exact ⟨Or.inr rfl, rfl⟩
        · intro j hj i hi
          rw [List.length_append, List.length_singleton] at hj
          by_cases hj1 : j < gs.length
          · have e1 : (gs ++ [gNew]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
            rw [e1] at hi
            exact hrb j hj1 i hi
          · have hjeq : j = gs.length := by omega
            subst hjeq
            have e1 : (gs ++ [gNew]).getD gs.length ⟨GateOp.or, []⟩ = gNew := by
              simp [List.getD_eq_getElem?_getD]
            rw [e1] at hi
            simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · have := hlt i List.mem_cons_self; omega
            · exact hout
        · intro w0 hw0
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hfl : (gs.foldl stepW w0).length = base + gs.length := by rw [foldl_len, hw0]
          have hget : (stepW (gs.foldl stepW w0) gNew).getD (base + gs.length) false =
              ((gs.foldl stepW w0).getD a false || (gs.foldl stepW w0).getD out false) := by
            change ((gs.foldl stepW w0) ++ [gNew.op.eval (gNew.inputs.map fun i => (gs.foldl stepW w0).getD i false)]).getD (base + gs.length) false = _
            rw [← hfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            change ([ (gs.foldl stepW w0).getD a false, (gs.foldl stepW w0).getD out false ].any id) = _
            simp
          rw [hget, foldl_getD_lt gs w0 a (by rw [hw0]; exact hlt a List.mem_cons_self), hev w0 hw0]
          simp
  -- Build star circuit for each c ∈ T' sequentially, then OR them together
  have buildStars (cs : List (Fin N)) (hcs : ∀ c ∈ cs, c ∈ T') (base : ℕ) (hN : N ≤ base) :
      ∃ (gs : List Gate) (outs : List ℕ),
        gs.length = (cs.map fun c => (star c).card).sum ∧
        outs.length = cs.length ∧
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < base + j) ∧
        (∀ u ∈ outs, u < base + gs.length) ∧
        ∀ (w0 : List Bool), w0.length = base →
          ∀ idx : Fin cs.length,
            (gs.foldl stepW w0).getD (outs.getD idx.val 0) false =
              (w0.getD (cs[idx.val]).val false && (star cs[idx.val]).toList.any (fun v => w0.getD v.val false)) := by
    induction cs generalizing base with
    | nil =>
      exact ⟨[], [], rfl, rfl, (by intro _ h; cases h), (by intro _ h; cases h), (by intro _ h; cases h),
        fun _ _ idx => Fin.elim0 idx⟩
    | cons c cs ih =>
      have hcT' : c ∈ T' := hcs c List.mem_cons_self
      have hne : (star c).Nonempty := (Finset.mem_filter.mp hcT').2
      let ws := (star c).toList.map Fin.val
      have hws_ne : ws ≠ [] := by
        intro h
        have hlen : ws.length = 0 := by simp [h]
        simp only [ws, List.length_map, Finset.length_toList] at hlen
        exact Finset.nonempty_iff_ne_empty.mp hne (Finset.card_eq_zero.mp hlen)
      obtain ⟨gs1, out1, hlen1, hao1, hrb1, hout1, hev1⟩ :=
        buildOr base ws hws_ne (fun w hw => by
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
          exact lt_of_lt_of_le v.isLt hN)
      let gs_c := gs1 ++ [⟨GateOp.and, [c.val, out1]⟩]
      let out_c := base + gs1.length
      have hlen_c : gs_c.length = (star c).card := by
        have : ws.length = (star c).card := by simp [ws]
        simp [gs_c]; omega
      obtain ⟨gs2, outs2, hlen2, hol2, hao2, hrb2, hout2, hev2⟩ :=
        ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (base + gs_c.length) (by omega)
      refine ⟨gs_c ++ gs2, out_c :: outs2, by simp [hlen_c, hlen2], by simp [hol2], ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg1 | hg2
        · rcases List.mem_append.mp hg1 with hg1a | hg1b
          · exact hao1 g hg1a
          · rw [List.mem_singleton.mp hg1b]; exact ⟨Or.inl rfl, rfl⟩
        · exact hao2 g hg2
      · intro j hj i hi
        by_cases hj1 : j < gs_c.length
        · have e1 : (gs_c ++ gs2).getD j ⟨GateOp.or, []⟩ = gs_c.getD j ⟨GateOp.or, []⟩ := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
          rw [e1] at hi
          by_cases hj1a : j < gs1.length
          · have e2 : gs_c.getD j ⟨GateOp.or, []⟩ = gs1.getD j ⟨GateOp.or, []⟩ := by
              simp [gs_c, List.getD_eq_getElem?_getD, List.getElem?_append_left hj1a]
            rw [e2] at hi
            exact hrb1 j hj1a i hi
          · have hjeq : j = gs1.length := by simp [gs_c] at hj1; omega
            subst hjeq
            have e2 : gs_c.getD gs1.length ⟨GateOp.or, []⟩ = ⟨GateOp.and, [c.val, out1]⟩ := by
              simp [gs_c, List.getD_eq_getElem?_getD]
            rw [e2] at hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · have := c.isLt; omega
            · exact hout1
        · have hj2 : j - gs_c.length < gs2.length := by rw [List.length_append] at hj; omega
          have e1 : (gs_c ++ gs2).getD j ⟨GateOp.or, []⟩ = gs2.getD (j - gs_c.length) ⟨GateOp.or, []⟩ := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : gs_c.length ≤ j)]
          rw [e1] at hi
          have hlt2 := hrb2 (j - gs_c.length) hj2 i hi
          omega
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu2
        · simp [out_c, gs_c]
        · have := hout2 u hu2; rw [List.length_append]; omega
      · intro w0 hw0 idx
        rw [List.foldl_append]
        have hw1 : (gs_c.foldl stepW w0).length = base + gs_c.length := by rw [foldl_len, hw0]
        rcases idx with ⟨idxv, hidx_lt⟩
        cases idxv with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          rw [foldl_getD_lt gs2 (gs_c.foldl stepW w0) out_c (by rw [hw1]; simp [out_c, gs_c])]
          simp only [gs_c, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hfl1 : (gs1.foldl stepW w0).length = base + gs1.length := by rw [foldl_len, hw0]
          have hget : (stepW (gs1.foldl stepW w0) ⟨GateOp.and, [c.val, out1]⟩).getD out_c false =
              ((gs1.foldl stepW w0).getD c.val false && (gs1.foldl stepW w0).getD out1 false) := by
            change ((gs1.foldl stepW w0) ++ [(GateOp.and).eval ([c.val, out1].map fun i => (gs1.foldl stepW w0).getD i false)]).getD out_c false = _
            rw [show out_c = (gs1.foldl stepW w0).length by omega, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
            change ([ (gs1.foldl stepW w0).getD c.val false, (gs1.foldl stepW w0).getD out1 false ].all id) = _
            simp
          rw [hget, foldl_getD_lt gs1 w0 c.val (by rw [hw0]; exact lt_of_lt_of_le c.isLt hN), hev1 w0 hw0]
          simp [ws, List.any_map]
          rfl
        | succ k =>
          have hk : k < cs.length := by simp at hidx_lt; omega
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          rw [hev2 (gs_c.foldl stepW w0) hw1 ⟨k, hk⟩]
          congr 1
          · exact foldl_getD_lt gs_c w0 (cs[k]).val (by rw [hw0]; exact lt_of_lt_of_le (cs[k]).isLt hN)
          · congr 1
            funext v
            exact foldl_getD_lt gs_c w0 v.val (by rw [hw0]; exact lt_of_lt_of_le v.isLt hN)
  -- Assemble D from buildStars + buildOr
  let cs := T'.toList
  have hcs_ne : cs ≠ [] := by
    intro h
    have hlen : cs.length = 0 := by simp [h]
    simp only [cs, Finset.length_toList] at hlen
    exact Finset.nonempty_iff_ne_empty.mp hT'_nonempty (Finset.card_eq_zero.mp hlen)
  obtain ⟨gsS, outsS, hlenS, holS, haoS, hrbS, houtS, hevS⟩ :=
    buildStars cs (fun c hc => Finset.mem_toList.mp hc) N (le_refl N)
  have houts_ne : outsS ≠ [] := by
    intro h; rw [h] at holS; simp only [List.length_nil] at holS
    exact hcs_ne (List.eq_nil_of_length_eq_zero holS.symm)
  obtain ⟨gsO, outO, hlenO, haoO, hrbO, houtO, hevO⟩ :=
    buildOr (N + gsS.length) outsS houts_ne houtS
  let D : Circuit := ⟨gsS ++ gsO, outO⟩
  have hD_size : D.size < C.size := by
    have hsum1 : (cs.map fun c => (star c).card).sum = E'.card := by
      have : (cs.map fun c => (star c).card).sum = ∑ c ∈ T', (star c).card := by
        simp [cs, Finset.sum_toList]
      rw [this, hSum_star]
    have hcs_len : cs.length = T'.card := Finset.length_toList T'
    have hDlen : D.size + 1 = E'.card + T'.card := by
      change (gsS ++ gsO).length + 1 = E'.card + T'.card
      rw [List.length_append]
      omega
    have hE'card : E'.card + 1 = E.card := Finset.card_erase_add_one he0E
    omega
  have hD_ao : IsAO2 N D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact (haoS g h1).1
      · exact (haoO g h2).1
    · intro j hj i hi
      change i ∈ ((gsS ++ gsO).getD j ⟨GateOp.or, []⟩).inputs at hi
      by_cases hj1 : j < gsS.length
      · have e1 : (gsS ++ gsO).getD j ⟨GateOp.or, []⟩ = gsS.getD j ⟨GateOp.or, []⟩ := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj1]
        rw [e1] at hi
        exact hrbS j hj1 i hi
      · have hj2 : j - gsS.length < gsO.length := by change j < (gsS ++ gsO).length at hj; rw [List.length_append] at hj; omega
        have e1 : (gsS ++ gsO).getD j ⟨GateOp.or, []⟩ = gsO.getD (j - gsS.length) ⟨GateOp.or, []⟩ := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : gsS.length ≤ j)]
        rw [e1] at hi
        have hlt := hrbO (j - gsS.length) hj2 i hi
        omega
    · intro g hg
      rcases List.mem_append.mp hg with h1 | h2
      · exact (haoS g h1).2
      · exact (haoO g h2).2
  have hD_eval : ∀ x : Fin N → Bool,
      circuitFun N D x = decide (∃ p l, (p, l) ∈ E' ∧ x (left p) = true ∧ x (right l) = true) := by
    intro x
    change ((gsS ++ gsO).foldl stepW (List.ofFn x)).getD outO false = _
    rw [List.foldl_append]
    have hlen1 : (gsS.foldl stepW (List.ofFn x)).length = N + gsS.length := by
      rw [foldl_len, List.length_ofFn]
    rw [hevO (gsS.foldl stepW (List.ofFn x)) hlen1]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, hvu⟩
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hu
      have hidx_cs : idx < cs.length := by omega
      have hget : outsS.getD idx 0 = outsS[idx] := by simp [List.getD_eq_getElem?_getD, hidx_lt]
      rw [← hget, hevS (List.ofFn x) List.length_ofFn ⟨idx, hidx_cs⟩, Bool.and_eq_true, List.any_eq_true] at hvu
      obtain ⟨hcval, v, hv_mem, hv_val⟩ := hvu
      have hxc : x cs[idx] = true := by
        simpa [List.getD_eq_getElem?_getD] using hcval
      have hxv : x v = true := by
        simpa [List.getD_eq_getElem?_getD] using hv_val
      have hv_star : v ∈ star cs[idx] := Finset.mem_toList.mp hv_mem
      obtain ⟨e, he_filt, hother⟩ := Finset.mem_image.mp hv_star
      obtain ⟨heE', hassign⟩ := Finset.mem_filter.mp he_filt
      refine ⟨e.1, e.2, heE', ?_, ?_⟩
      · simp only [assign] at hassign
        simp only [other] at hother
        split_ifs at hassign hother
        · rwa [hassign]
        · rwa [hother]
      · simp only [assign] at hassign
        simp only [other] at hother
        split_ifs at hassign hother
        · rwa [hother]
        · rwa [hassign]
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hcm : assign (p, l) ∈ T' := Finset.mem_filter.mpr
        ⟨hAssign_mem hpl, ⟨other (p, l), Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨hpl, rfl⟩, rfl⟩⟩⟩
      have hcm_cs : assign (p, l) ∈ cs := Finset.mem_toList.mpr hcm
      obtain ⟨idx, hidx_cs, hcs_eq⟩ := List.getElem_of_mem hcm_cs
      have hidx_o : idx < outsS.length := by omega
      refine ⟨outsS[idx], List.getElem_mem hidx_o, ?_⟩
      have hget : outsS.getD idx 0 = outsS[idx] := by simp [List.getD_eq_getElem?_getD, hidx_o]
      rw [← hget, hevS (List.ofFn x) List.length_ofFn ⟨idx, hidx_cs⟩, Bool.and_eq_true, List.any_eq_true]
      refine ⟨?_, other (p, l), Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨hpl, hcs_eq.symm⟩, rfl⟩), ?_⟩
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Option.getD_some, hcs_eq, assign]
        split_ifs <;> assumption
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Option.getD_some, other]
        split_ifs <;> assumption
  exact ⟨e0, he0E, he0M, D, hD_size, hD_ao, hD_eval⟩
