module

public import UniversalGroup.Simulator.Recognition.ACoefficients
public import UniversalGroup.Simulator.DModel

@[expose] public section

/-!
# Reduced T forms of the two simulator factors

Replacing the last displayed generator of A by T only changes it by a
coefficient in A's base subgroup. The attaching subgroups are disjoint from
both coefficient groups, so restriction of the rebased HNN extension gives
reduced forms and exact intersections with the preceding f stage.
-/

namespace UniversalGroup.SimulatorFactorNormalForms

noncomputable section
open HNNLemmas SimulatorIntersectionB
set_option maxHeartbeats 800000

variable (G : PreparedInput) (D : ValievDatum G)

abbrev fromF := SimulatorModel.fromF D.toCodeWords D.F_support D.E_support
abbrev attaching := SimulatorModel.qSubgroup D.toCodeWords D.F_support D.E_support
abbrev marker := SimulatorDModel.marker D.toCodeWords D.F_support D.E_support
abbrev left := TwistedCentralizer.left (attaching G D) (marker G D)
abbrev right := TwistedCentralizer.right (attaching G D) (marker G D) (f G D)
abbrev phi := UniversalGroup.rangeEquiv (left G D) (right G D)
  (TwistedCentralizer.left_injective _ _) (TwistedCentralizer.right_injective _ _ _)
abbrev Rebased := SimulatorDModel.Rebased D.toCodeWords D.F_support D.E_support
abbrev toLiteral := SimulatorDModel.toLiteral D.toCodeWords D.F_support D.E_support
abbrev ReducedWord := HNNExtension.NormalWord.ReducedWord (FStage G D)
  (left G D).range (right G D).range

private theorem preserves_of_disjoint (H : Subgroup (FStage G D))
    (hl : ∀ v : Core G D, v ∈ CE G D →
      ofCore G D (pCore G D * v * (pCore G D)⁻¹) ∈ H → v = 1)
    (hr : ∀ v : Core G D, v ∈ CE G D →
      (f G D)⁻¹ * ofCore G D (pCore G D * v * (pCore G D)⁻¹) * f G D ∈ H → v = 1)
    (a : (left G D).range) :
    (a : FStage G D) ∈ H ↔ ((phi G D a : (right G D).range) : FStage G D) ∈ H := by
  rcases a with ⟨_, c, rfl⟩
  rw [UniversalGroup.rangeEquiv_apply_range]
  rcases c with ⟨_, v, hv, rfl⟩
  change marker G D * ofCore G D v * (marker G D)⁻¹ ∈ H ↔
    (f G D)⁻¹ * (marker G D * ofCore G D v * (marker G D)⁻¹) * f G D ∈ H
  have hm : marker G D * ofCore G D v * (marker G D)⁻¹ =
      ofCore G D (pCore G D * v * (pCore G D)⁻¹) := by simp [marker, SimulatorDModel.marker]
  rw [hm]
  constructor
  · intro h
    have hvone := hl v hv h
    simp [hvone]
  · intro h
    have hvone := hr v hv h
    simp [hvone]

theorem preserves_A (a : (left G D).range) :
    (a : FStage G D) ∈ SimulatorIntersectionA.Base G D ↔
      ((phi G D a : (right G D).range) : FStage G D) ∈ SimulatorIntersectionA.Base G D :=
  preserves_of_disjoint G D _ (SimulatorIntersectionA.attaching_left_disjoint G D)
    (SimulatorIntersectionA.attaching_right_disjoint G D) a

theorem preserves_B (a : (left G D).range) :
    (a : FStage G D) ∈ SimulatorIntersectionB.Base G D ↔
      ((phi G D a : (right G D).range) : FStage G D) ∈ SimulatorIntersectionB.Base G D :=
  preserves_of_disjoint G D _ (SimulatorIntersectionB.attaching_left_disjoint G D)
    (SimulatorIntersectionB.attaching_right_disjoint G D) a

private theorem range_le_iff {ι K : Type*} [Group K] (j : FreeGroup ι →* K) (H : Subgroup K) :
    j.range ≤ H ↔ ∀ i, j (FreeGroup.of i) ∈ H := by
  have he : j = FreeGroup.lift (fun i => j (FreeGroup.of i)) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  conv_lhs => rw [he, FreeGroup.range_lift_eq_closure, Subgroup.closure_le]
  exact Set.range_subset_iff

@[simp] theorem fromF_code (i : Fin 2) :
    fromF G D (ofCore G D (codeCore G D (FreeGroup.of i))) =
      SimulatorRelations.positive D.toCodeWords (D.code i) := by
  rw [SimulatorModel.fromF_ofF]
  change SimulatorModel.fromCore D.toCodeWords D.F_support D.E_support
    (SimulatorFreeLetters.coreLetters D.toCodeWords D.F_support D.E_support
      (CodeSubgroups.codeLift D.r (FreeGroup.of i))) = _
  rw [← MonoidHom.comp_apply, SimulatorFreeLetters.fromCore_comp_coreLetters]
  simp only [CodeSubgroups.codeLift, FreeGroup.lift_apply_of, CodeSubgroups.positiveFree,
    CodeSubgroups.map_positive, SimulatorFreeLetters.freeS]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [D.code_shape]
  rfl

@[simp] theorem fromF_letter (i : Fin 2) :
    fromF G D (ofCore G D
      (SimulatorFreeLetters.coreLetters D.toCodeWords D.F_support D.E_support (FreeGroup.of i))) =
      SimulatorRelations.s D.toCodeWords i := by
  rw [SimulatorModel.fromF_ofF, ← MonoidHom.comp_apply,
    SimulatorFreeLetters.fromCore_comp_coreLetters]
  fin_cases i <;> simp [SimulatorFreeLetters.freeS]

@[simp] theorem fromF_conjugated_letter (i : Fin 2) :
    fromF G D (ConjugatedAmalgam.conjugatedOf (CD G D)
      (SimulatorFreeLetters.coreLetters D.toCodeWords D.F_support D.E_support (FreeGroup.of i))) =
    (SimulatorRelations.f D.toCodeWords)⁻¹ * SimulatorRelations.s D.toCodeWords i *
      SimulatorRelations.f D.toCodeWords := by
  change fromF G D ((f G D)⁻¹ * ofCore G D _ * f G D) = _
  simp only [map_mul, map_inv, fromF_letter, SimulatorModel.fromF_stable]

/-- A literal coefficient group with the new stable letter T adjoined. -/
def factor (H : Subgroup (FStage G D)) : Subgroup (simulatorL D.toCodeWords).Group :=
  generatedWith (H.map (fromF G D)) (SimulatorRecognitionForward.target D.toCodeWords)

private theorem base_le_factor (H : Subgroup (FStage G D)) : H.map (fromF G D) ≤ factor G D H := by
  intro x hx
  exact Subgroup.subset_closure (Or.inl hx)

private theorem target_mem_factor (H : Subgroup (FStage G D)) :
    SimulatorRecognitionForward.target D.toCodeWords ∈ factor G D H :=
  Subgroup.subset_closure (Or.inr rfl)

private theorem factor_le (H : Subgroup (FStage G D)) (K : Subgroup (simulatorL D.toCodeWords).Group)
    (hb : H.map (fromF G D) ≤ K) (hT : SimulatorRecognitionForward.target D.toCodeWords ∈ K) :
    factor G D H ≤ K := by
  rw [factor, generatedWith, Subgroup.closure_le]
  rintro x (hx|hx)
  · exact hb hx
  · rcases hx with rfl
    exact hT

theorem baseA_map_le_iff (K : Subgroup (simulatorL D.toCodeWords).Group) :
    (SimulatorIntersectionA.Base G D).map (fromF G D) ≤ K ↔
      (∀ i, SimulatorRelations.positive D.toCodeWords (D.code i) ∈ K) ∧
      ∀ i, (SimulatorRelations.f D.toCodeWords)⁻¹ * SimulatorRelations.s D.toCodeWords i *
        SimulatorRelations.f D.toCodeWords ∈ K := by
  change (((codeCore G D).range.map (ofCore G D)) ⊔
    (SimulatorIntersectionA.Letters G D).map (ConjugatedAmalgam.conjugatedOf (CD G D))).map
      (fromF G D) ≤ K ↔ _
  rw [Subgroup.map_sup, sup_le_iff, Subgroup.map_map, ← MonoidHom.range_comp,
    range_le_iff, SimulatorIntersectionA.Letters, Subgroup.map_map,
    ← MonoidHom.range_comp, range_le_iff]
  simp only [MonoidHom.comp_apply, fromF_code, fromF_conjugated_letter]

theorem baseB_map_le_iff (K : Subgroup (simulatorL D.toCodeWords).Group) :
    (SimulatorIntersectionB.Base G D).map (fromF G D) ≤ K ↔
      (∀ i, SimulatorRelations.positive D.toCodeWords (D.code i) ∈ K) ∧
      SimulatorRelations.f D.toCodeWords ∈ K := by
  rw [SimulatorIntersectionB.Base, ← MonoidHom.range_comp, range_le_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      simpa only [MonoidHom.comp_apply, baseLift_old, fromF_code] using h i.castSucc
    · simpa only [MonoidHom.comp_apply, baseLift_f, SimulatorModel.fromF_stable] using h (Fin.last 2)
  · rintro ⟨hc, hf⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [MonoidHom.comp_apply, baseLift_f, SimulatorModel.fromF_stable] using hf
    · simpa only [MonoidHom.comp_apply, baseLift_old, fromF_code] using hc j

private theorem aValue_mem (i : Fin 5) : CodeSubgroups.aValues D.toCodeWords i ∈ simulatorA D.toCodeWords :=
  Subgroup.subset_closure (Set.mem_range_self i)

private theorem bValues_eq : CodeSubgroups.bValues D.toCodeWords =
    ![SimulatorRelations.positive D.toCodeWords (D.code 0),
      SimulatorRelations.positive D.toCodeWords (D.code 1),
      SimulatorRelations.f D.toCodeWords, SimulatorRecognitionForward.target D.toCodeWords] := by
  funext i
  fin_cases i
  · exact SimulatorRelations.eval_positive D.toCodeWords (D.code 0)
  · exact SimulatorRelations.eval_positive D.toCodeWords (D.code 1)
  · simp [CodeSubgroups.bValues, FP.evalWord, simulatorLWords, SimulatorRelations.f, generators]
  · rfl

private theorem bValue_mem (i : Fin 4) : CodeSubgroups.bValues D.toCodeWords i ∈ simulatorB D.toCodeWords :=
  Subgroup.subset_closure (Set.mem_range_self i)

private theorem baseA_map_le_A :
    (SimulatorIntersectionA.Base G D).map (fromF G D) ≤ simulatorA D.toCodeWords := by
  rw [baseA_map_le_iff]
  constructor <;> intro i <;> fin_cases i
  · simpa [EllAlgebra.aValues_eq] using aValue_mem G D 0
  · simpa [EllAlgebra.aValues_eq] using aValue_mem G D 1
  · simpa [EllAlgebra.aValues_eq] using aValue_mem G D 2
  · simpa [EllAlgebra.aValues_eq] using aValue_mem G D 3

private theorem baseB_map_le_B :
    (SimulatorIntersectionB.Base G D).map (fromF G D) ≤ simulatorB D.toCodeWords := by
  rw [baseB_map_le_iff]
  constructor
  · intro i
    fin_cases i
    · simpa [bValues_eq] using bValue_mem G D 0
    · simpa [bValues_eq] using bValue_mem G D 1
  · simpa [bValues_eq] using bValue_mem G D 2

/-- The correction coefficient relating R = Pt and T belongs to A's base. -/
theorem marker_conjugate_mem_baseA :
    (f G D)⁻¹ * marker G D * f G D ∈ SimulatorIntersectionA.Base G D :=
  SimulatorIntersectionA.conjugated_letters_mem_base G D (pCore_mem_letters G D)

@[simp] theorem fromF_marker_conjugate :
    fromF G D ((f G D)⁻¹ * marker G D * f G D) =
      (SimulatorRelations.f D.toCodeWords)⁻¹ * SimulatorRelations.positive D.toCodeWords D.P *
        SimulatorRelations.f D.toCodeWords := by
  simp only [map_mul, map_inv, SimulatorModel.fromF_stable, SimulatorDModel.fromF_marker]

theorem target_mul_marker_conjugate :
    SimulatorRecognitionForward.target D.toCodeWords *
        fromF G D ((f G D)⁻¹ * marker G D * f G D) =
      SimulatorRelations.positive D.toCodeWords D.P * SimulatorRelations.t D.toCodeWords := by
  rw [fromF_marker_conjugate, SimulatorRecognitionForward.target_eq]
  simp only [SimulatorRelations.q, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    inv_mul_cancel, mul_one]

/-- The rebased coefficient subgroup with T is exactly the displayed A. -/
theorem factorA_eq : factor G D (SimulatorIntersectionA.Base G D) = simulatorA D.toCodeWords := by
  have hc : fromF G D ((f G D)⁻¹ * marker G D * f G D) ∈
      (SimulatorIntersectionA.Base G D).map (fromF G D) :=
    ⟨_, marker_conjugate_mem_baseA G D, rfl⟩
  apply le_antisymm
  · apply factor_le G D _ _ (baseA_map_le_A G D)
    have hR : SimulatorRelations.positive D.toCodeWords D.P * SimulatorRelations.t D.toCodeWords ∈
        simulatorA D.toCodeWords := by simpa [EllAlgebra.aValues_eq] using aValue_mem G D 4
    have h := (simulatorA D.toCodeWords).mul_mem hR
      ((simulatorA D.toCodeWords).inv_mem (baseA_map_le_A G D hc))
    rw [← target_mul_marker_conjugate G D, mul_inv_cancel_right] at h
    exact h
  · change Subgroup.closure (Set.range (CodeSubgroups.aValues D.toCodeWords)) ≤ _
    rw [Subgroup.closure_le, Set.range_subset_iff]
    have hb := (baseA_map_le_iff G D _).mp (base_le_factor G D (SimulatorIntersectionA.Base G D))
    intro i
    rw [EllAlgebra.aValues_eq]
    fin_cases i
    · exact hb.1 0
    · exact hb.1 1
    · exact hb.2 0
    · exact hb.2 1
    · change SimulatorRelations.positive D.toCodeWords D.P * SimulatorRelations.t D.toCodeWords ∈ _
      rw [← target_mul_marker_conjugate G D]
      exact (factor G D _).mul_mem (target_mem_factor G D _) (base_le_factor G D _ hc)

/-- The rebased coefficient subgroup with T is exactly the displayed B. -/
theorem factorB_eq : factor G D (SimulatorIntersectionB.Base G D) = simulatorB D.toCodeWords := by
  apply le_antisymm
  · apply factor_le G D _ _ (baseB_map_le_B G D)
    simpa [bValues_eq] using bValue_mem G D 3
  · change Subgroup.closure (Set.range (CodeSubgroups.bValues D.toCodeWords)) ≤ _
    rw [Subgroup.closure_le, Set.range_subset_iff]
    have hb := (baseB_map_le_iff G D _).mp (base_le_factor G D (SimulatorIntersectionB.Base G D))
    intro i
    rw [bValues_eq]
    fin_cases i
    · exact hb.1 0
    · exact hb.1 1
    · exact hb.2
    · exact target_mem_factor G D _

/-- The coefficient subgroup with the stable letter in the T presentation. -/
def rebasedFactor (H : Subgroup (FStage G D)) : Subgroup (Rebased G D) :=
  TwistedCentralizer.rebasedSubgroup (attaching G D) (marker G D) (f G D) H

private theorem ambientFactor_map (H : Subgroup (FStage G D)) :
    (TwistedCentralizer.subgroup (attaching G D) (marker G D) (f G D) H).map
      (SimulatorModel.fromModel D.toCodeWords D.F_support D.E_support) = factor G D H := by
  unfold TwistedCentralizer.subgroup factor generatedWith
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq,
    Subgroup.closure_eq, Subgroup.map_sup, Subgroup.map_map,
    MonoidHom.map_closure, Set.image_singleton, SimulatorDModel.fromModel_target]
  have hc : (SimulatorModel.fromModel D.toCodeWords D.F_support D.E_support).comp
      (centralizerOf (attaching G D)) = fromF G D := by
    apply MonoidHom.ext
    intro x
    exact SimulatorModel.fromModel_ofQ D.toCodeWords D.F_support D.E_support x
  rw [hc]

/-- Transport of the restricted T subgroup to the literal simulator. -/
theorem rebasedFactor_map (H : Subgroup (FStage G D)) :
    (rebasedFactor G D H).map (toLiteral G D) = factor G D H := by
  change (TwistedCentralizer.rebasedSubgroup (attaching G D) (marker G D) (f G D) H).map
    ((SimulatorModel.fromModel D.toCodeWords D.F_support D.E_support).comp
      (TwistedCentralizer.toAmbient (attaching G D) (marker G D) (f G D))) = _
  rw [← Subgroup.map_map, TwistedCentralizer.map_rebasedSubgroup, ambientFactor_map]

private theorem exists_reducedWord_factor (H : Subgroup (FStage G D))
    (hp : ∀ a : (left G D).range, (a : FStage G D) ∈ H ↔
      ((phi G D a : (right G D).range) : FStage G D) ∈ H)
    {x : (simulatorL D.toCodeWords).Group} (hx : x ∈ factor G D H) :
    ∃ w : ReducedWord G D, toLiteral G D (w.prod (phi G D)) = x ∧
      w.head ∈ H ∧ ∀ p ∈ w.toList, p.2 ∈ H := by
  rw [← rebasedFactor_map G D H] at hx
  rcases hx with ⟨y,hy,rfl⟩
  obtain ⟨w,hw,hh,ht⟩ := exists_reducedWord_of_mem_generatedWithStable H hp hy
  exact ⟨w,congrArg (toLiteral G D) hw,hh,ht⟩

/-- Every element of A has an ambient reduced T word with coefficients in Base A. -/
theorem exists_reducedWord_A {x : (simulatorL D.toCodeWords).Group}
    (hx : x ∈ simulatorA D.toCodeWords) :
    ∃ w : ReducedWord G D, toLiteral G D (w.prod (phi G D)) = x ∧
      w.head ∈ SimulatorIntersectionA.Base G D ∧
        ∀ p ∈ w.toList, p.2 ∈ SimulatorIntersectionA.Base G D := by
  rw [← factorA_eq G D] at hx
  exact exists_reducedWord_factor G D _ (preserves_A G D) hx

/-- Every element of B has an ambient reduced T word with coefficients in Base B. -/
theorem exists_reducedWord_B {x : (simulatorL D.toCodeWords).Group}
    (hx : x ∈ simulatorB D.toCodeWords) :
    ∃ w : ReducedWord G D, toLiteral G D (w.prod (phi G D)) = x ∧
      w.head ∈ SimulatorIntersectionB.Base G D ∧
        ∀ p ∈ w.toList, p.2 ∈ SimulatorIntersectionB.Base G D := by
  rw [← factorB_eq G D] at hx
  exact exists_reducedWord_factor G D _ (preserves_B G D) hx

end
end UniversalGroup.SimulatorFactorNormalForms
