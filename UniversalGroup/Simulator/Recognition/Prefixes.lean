module

public import UniversalGroup.Simulator.Recognition.CoefficientTransport
public import UniversalGroup.Simulator.Codes.Cancellation
public import UniversalGroup.Foundations.HNN.ReducedWordPeel

@[expose] public section

/-! Recognized codewords and the two removable T prefixes. -/

namespace UniversalGroup.SimulatorRecognizedPrefixes

open SimulatorIntersectionB SimulatorCoefficientTransport

noncomputable section
set_option maxHeartbeats 800000
variable (G : PreparedInput) (D : ValievDatum G)

/-- Decode a signed codeword once core recognition has made its marker
product positive. The resulting input word is trivial in the input monoid. -/
theorem decode (g : FreeGroup (Fin 2)) (Q : PositiveWord)
    (hQ : CodeSubgroups.codeLift D.r g * BorisovCStage.positiveFree D.P =
      BorisovCStage.positiveFree Q)
    (hrec : PositiveEq D.toCodeWords.rules Q D.P) :
    ∃ w : PositiveWord, PositiveEq G.monoidRules w [] ∧
      g = CodeSubgroups.positiveFree w ∧ Q = w.flatMap D.code ++ D.P := by
  have hQ' : CodeSubgroups.codeLift D.r g * CodeSubgroups.positiveFree (valievMarker D.r D.t) =
      CodeSubgroups.positiveFree Q := by
    simpa only [D.marker_shape, BorisovCStage.positiveFree_eq_eval, CodeSubgroups.positiveFree] using hQ
  rcases CodeCancellation.code_mul_marker_positive D.r D.t D.r_ge_two g Q hQ' with ⟨w, hg, hw⟩
  have hw' : Q = w.flatMap D.code ++ D.P := by simpa only [D.code_shape, D.marker_shape] using hw
  refine ⟨w, (D.recognizes w).2 ?_, hg, hw'⟩
  rwa [← hw']

def codeValue (w : PositiveWord) : FStage G D :=
  ofCore G D (codeCore G D (CodeSubgroups.positiveFree w))

theorem fromF_codeValue (w : PositiveWord) :
    SimulatorModel.fromF D.toCodeWords D.F_support D.E_support (codeValue G D w) =
      SimulatorRelations.positive D.toCodeWords (w.flatMap D.code) := by
  unfold codeValue codeCore
  rw [MonoidHom.comp_apply, CodeCancellation.codeLift_positive]
  rw [coreLetters_eq_sLift2]
  change SimulatorModel.fromF D.toCodeWords D.F_support D.E_support
    (ofCore G D (SimulatorModel.coreOf D.toCodeWords D.F_support D.E_support
      (BorisovCStage.sLift3 (CodeSubgroups.positiveFree (w.flatMap (valievCode D.r)))))) = _
  rw [show CodeSubgroups.positiveFree (w.flatMap (valievCode D.r)) =
      BorisovCStage.positiveFree (w.flatMap (valievCode D.r)) by
        rw [BorisovCStage.positiveFree_eq_eval]; rfl,
    sLift3_positiveFree, SimulatorModel.fromF_ofF]
  simp only [BorisovCStage.positive3, CodeSubgroups.map_positive]
  simp [SimulatorModel.fromCore_s1, SimulatorModel.fromCore_s2,
    SimulatorRelations.positive, D.code_shape]

/-- The proposed intersection, regarded inside the rebased HNN model. -/
def recognized : Subgroup (Rebased G D) :=
  (recognitionSubgroup G D.toCodeWords).comap (toLiteral G D)

/-- Mathlib's stable letter is the inverse of the displayed T. -/
theorem toLiteral_t :
    toLiteral G D (HNNExtension.t : Rebased G D) =
      (SimulatorRecognitionForward.target D.toCodeWords)⁻¹ := by
  have h := congrArg Inv.inv (SimulatorDModel.toLiteral_stable D.toCodeWords D.F_support D.E_support)
  simpa only [TwistedCentralizer.stable, IdentifyingHNN.stable, map_inv, inv_inv] using h

theorem toLiteral_prefix (b z : FStage G D) (u : ℤˣ) :
    toLiteral G D (ReducedWordPeel.prefixElement (phi G D) b u z) =
      SimulatorModel.fromF D.toCodeWords D.F_support D.E_support b *
        ((SimulatorRecognitionForward.target D.toCodeWords)⁻¹) ^ (u : ℤ) *
          (SimulatorModel.fromF D.toCodeWords D.F_support D.E_support z)⁻¹ := by
  simp only [ReducedWordPeel.prefixElement, map_mul, map_zpow, map_inv, toLiteral_t]
  rw [show (HNNExtension.of : FStage G D →* Rebased G D) =
    TwistedCentralizer.of (attaching G D) (marker G D) (f G D) from rfl]
  rw [SimulatorDModel.toLiteral_of, SimulatorDModel.toLiteral_of]

/-- The positive displayed-T prefix is precisely a recognized delta. -/
theorem positive_prefix (w : PositiveWord) (hw : PositiveEq G.monoidRules w []) :
    ReducedWordPeel.prefixElement (phi G D) (codeValue G D w) (-1)
      ((f G D)⁻¹ * codeValue G D w * f G D) ∈ recognized G D := by
  change toLiteral G D _ ∈ recognitionSubgroup G D.toCodeWords
  rw [toLiteral_prefix]
  simp only [Units.val_neg, Units.val_one, zpow_neg, zpow_one, inv_inv,
    map_mul, map_inv, fromF_codeValue, SimulatorModel.fromF_stable]
  have heq : SimulatorRelations.positive D.toCodeWords (w.flatMap D.code) *
      SimulatorRecognitionForward.target D.toCodeWords *
        (SimulatorRelations.f D.toCodeWords)⁻¹ *
          (SimulatorRelations.positive D.toCodeWords (w.flatMap D.code))⁻¹ *
            SimulatorRelations.f D.toCodeWords = simulatorDelta D.toCodeWords w :=
    by
      rw [SimulatorRecognitionForward.delta_eq, SimulatorRecognitionForward.target_eq]
      simp [SimulatorRelations.positive, evalPositive, mul_assoc]
  have hm : simulatorDelta D.toCodeWords w ∈ recognitionSubgroup G D.toCodeWords :=
    Subgroup.subset_closure ⟨w, hw, rfl⟩
  convert heq ▸ hm using 1
  group

/-- The negative displayed-T prefix is the inverse of a recognized delta. -/
theorem negative_prefix (w : PositiveWord) (hw : PositiveEq G.monoidRules w []) :
    ReducedWordPeel.prefixElement (phi G D) ((f G D)⁻¹ * codeValue G D w * f G D) 1
      (codeValue G D w) ∈ recognized G D := by
  change toLiteral G D _ ∈ recognitionSubgroup G D.toCodeWords
  rw [toLiteral_prefix]
  simp only [Units.val_one, zpow_one, map_mul, map_inv, fromF_codeValue,
    SimulatorModel.fromF_stable]
  have hm : (simulatorDelta D.toCodeWords w)⁻¹ ∈ recognitionSubgroup G D.toCodeWords :=
    (recognitionSubgroup G D.toCodeWords).inv_mem (Subgroup.subset_closure ⟨w, hw, rfl⟩)
  rw [SimulatorRecognitionForward.delta_eq] at hm
  rw [SimulatorRecognitionForward.target_eq]
  simp only [SimulatorRelations.positive, evalPositive, List.map_append, List.prod_append] at hm ⊢
  convert hm using 1
  group

end
end UniversalGroup.SimulatorRecognizedPrefixes
