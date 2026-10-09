module

public import UniversalGroup.Simulator.Recognition.FiniteRank.Coefficients

@[expose] public section

/-!
# Recognition at the base coefficients of the subgroup `B`

The arbitrary finite-rank coefficient theorems specialize to the two
literal Valiev codewords. The base subgroup, attaching-group intersections,
and signed recognition equations retain the displayed rank-two interface.
-/

namespace UniversalGroup.SimulatorIntersectionB

open SimulatorModel SimulatorFreeLetters BorisovCStage HNNLemmas

noncomputable section

variable (G : PreparedInput) (D : ValievDatum G)

/-- The literal Valiev code as an instance of the finite-rank simulator interface. -/
def finiteRankData : HigmanSimulatorB.Data 2 where
  words := D.toCodeWords
  F_support := D.F_support
  E_support := D.E_support
  code := CodeSubgroups.codeLift D.r
  code_injective := CodeSubgroups.codeLift_injective D.r

abbrev Core := SimulatorModel.Core D.toCodeWords D.F_support D.E_support
abbrev FStage := SimulatorModel.FStage D.toCodeWords D.F_support D.E_support
abbrev ofCore : Core G D →* FStage G D := ofF D.toCodeWords D.F_support D.E_support
abbrev pCore : Core G D :=
  coreOf D.toCodeWords D.F_support D.E_support (positive3 D.P)
abbrev f : FStage G D := fStable D.toCodeWords D.F_support D.E_support
abbrev CD : Subgroup (Core G D) := SimulatorModel.CD D.toCodeWords D.F_support D.E_support
abbrev CE : Subgroup (Core G D) := SimulatorModel.CE D.toCodeWords D.F_support D.E_support

def codeCore : FreeGroup (Fin 2) →* Core G D :=
  (coreLetters D.toCodeWords D.F_support D.E_support).comp (CodeSubgroups.codeLift D.r)

def baseLift : FreeGroup (Fin 3) →* FStage G D :=
  AdjoinFree.hom (CD G D) (codeCore G D)

def Base : Subgroup (FStage G D) := (baseLift G D).range

@[simp] theorem baseLift_old (i : Fin 2) :
    baseLift G D (FreeGroup.of i.castSucc) = ofCore G D (codeCore G D (FreeGroup.of i)) :=
  HigmanSimulatorB.baseLift_old (finiteRankData G D) i

@[simp] theorem baseLift_f : baseLift G D (FreeGroup.of (Fin.last 2)) = f G D :=
  HigmanSimulatorB.baseLift_f (finiteRankData G D)

theorem f_mem_base : f G D ∈ Base G D :=
  HigmanSimulatorB.f_mem_base (finiteRankData G D)

theorem codeCore_mem_letters (w : FreeGroup (Fin 2)) :
    codeCore G D w ∈ (coreLetters D.toCodeWords D.F_support D.E_support).range :=
  HigmanSimulatorB.codeCore_mem_letters (finiteRankData G D) w

theorem ofCore_mem_base_iff (x : Core G D) :
    ofCore G D x ∈ Base G D ↔ x ∈ (codeCore G D).range :=
  HigmanSimulatorB.ofCore_mem_base_iff (finiteRankData G D) x

theorem base_inf_CD : Base G D ⊓ (CD G D).map (ofCore G D) = ⊥ :=
  HigmanSimulatorB.base_inf_CD (finiteRankData G D)

theorem sLift3_positiveFree (w : PositiveWord) :
    sLift3 (BorisovCStage.positiveFree w) = positive3 w :=
  HigmanSimulatorB.sLift3_positiveFree w

theorem coreLetters_eq_sLift2 :
    coreLetters D.toCodeWords D.F_support D.E_support =
      sLift2 (rules D.toCodeWords D.F_support D.E_support)
        (free D.toCodeWords D.F_support D.E_support) :=
  HigmanSimulatorB.coreLetters_eq_sLift2 (finiteRankData G D)

theorem pCore_mem_letters :
    pCore G D ∈ (coreLetters D.toCodeWords D.F_support D.E_support).range :=
  HigmanSimulatorB.pCore_mem_letters (finiteRankData G D)

/-- The left attaching subgroup for the rebased letter `T` is disjoint
from the base of `B`. -/
theorem attaching_left_disjoint (v : Core G D) (hv : v ∈ CE G D)
    (hb : ofCore G D (pCore G D * v * (pCore G D)⁻¹) ∈ Base G D) : v = 1 :=
  HigmanSimulatorB.attaching_left_disjoint (finiteRankData G D) v hv hb

/-- The right attaching subgroup is its conjugate by `f`, which belongs
to the base of `B`, so it is disjoint as well. -/
theorem attaching_right_disjoint (v : Core G D) (hv : v ∈ CE G D)
    (hb : (f G D)⁻¹ * ofCore G D (pCore G D * v * (pCore G D)⁻¹) * f G D ∈
      Base G D) : v = 1 :=
  HigmanSimulatorB.attaching_right_disjoint (finiteRankData G D) v hv hb

/-- A positive-sign first coefficient gives a signed code word whose
product with the marker is positive and semigroup-equivalent to the marker. -/
theorem positive_coefficient
    (b : FStage G D) (hb : b ∈ Base G D)
    (u v : Core G D) (hu : u ∈ CD G D) (hv : v ∈ CE G D)
    (heq : b = ofCore G D (u * pCore G D * v * (pCore G D)⁻¹)) :
    ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord),
      b = ofCore G D (codeCore G D g) ∧
      CodeSubgroups.codeLift D.r g * BorisovCStage.positiveFree D.P =
        BorisovCStage.positiveFree Q ∧ PositiveEq D.toCodeWords.rules Q D.P :=
  HigmanSimulatorB.positive_coefficient (finiteRankData G D) b hb u v hu hv heq

/-- The corresponding negative-sign coefficient is an `f`-conjugate of
the same kind of recognized signed code word. -/
theorem negative_coefficient
    (b : FStage G D) (hb : b ∈ Base G D)
    (u v : Core G D) (hu : u ∈ CD G D) (hv : v ∈ CE G D)
    (heq : b = (f G D)⁻¹ * ofCore G D (u * pCore G D * v * (pCore G D)⁻¹) * f G D) :
    ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord),
      b = (f G D)⁻¹ * ofCore G D (codeCore G D g) * f G D ∧
      CodeSubgroups.codeLift D.r g * BorisovCStage.positiveFree D.P =
        BorisovCStage.positiveFree Q ∧ PositiveEq D.toCodeWords.rules Q D.P :=
  HigmanSimulatorB.negative_coefficient (finiteRankData G D) b hb u v hu hv heq

end

end UniversalGroup.SimulatorIntersectionB
