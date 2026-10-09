module

public import UniversalGroup.Simulator.Recognition.BCoefficients
public import UniversalGroup.Simulator.Recognition.FiniteRank.NormalForms

@[expose] public section

/-! Coefficient factorizations in the rebased simulator, specialized to Valiev codes. -/

namespace UniversalGroup.SimulatorCoefficientTransport

open SimulatorIntersectionB BorisovCStage

noncomputable section
set_option maxHeartbeats 800000

variable (G : PreparedInput) (D : ValievDatum G)

abbrev attaching := SimulatorModel.qSubgroup D.toCodeWords D.F_support D.E_support
abbrev marker := SimulatorDModel.marker D.toCodeWords D.F_support D.E_support
abbrev left := TwistedCentralizer.left (attaching G D) (marker G D)
abbrev right := TwistedCentralizer.right (attaching G D) (marker G D) (f G D)
abbrev phi := UniversalGroup.rangeEquiv (left G D) (right G D)
  (TwistedCentralizer.left_injective _ _) (TwistedCentralizer.right_injective _ _ _)
abbrev Rebased := SimulatorDModel.Rebased D.toCodeWords D.F_support D.E_support
abbrev toLiteral : Rebased G D →* (simulatorL D.toCodeWords).Group :=
  SimulatorDModel.toLiteral D.toCodeWords D.F_support D.E_support
abbrev coefficients := SimulatorDModel.coefficients D.toCodeWords D.F_support D.E_support

theorem left_coefficient_factorization (b a : FStage G D)
    (ha : a ∈ coefficients G D) (h : b⁻¹ * a ∈ (left G D).range) :
    ∃ u v : Core G D, u ∈ CD G D ∧ v ∈ CE G D ∧
      b = ofCore G D (u * pCore G D * v * (pCore G D)⁻¹) :=
  HigmanSimulatorB.left_coefficient_factorization (finiteRankData G D) b a ha h

theorem right_coefficient_factorization (b a : FStage G D)
    (ha : a ∈ coefficients G D) (h : b⁻¹ * a ∈ (right G D).range) :
    ∃ u v : Core G D, u ∈ CD G D ∧ v ∈ CE G D ∧
      b = (f G D)⁻¹ * ofCore G D (u * pCore G D * v * (pCore G D)⁻¹) * f G D :=
  HigmanSimulatorB.right_coefficient_factorization (finiteRankData G D) b a ha h

end

end UniversalGroup.SimulatorCoefficientTransport
