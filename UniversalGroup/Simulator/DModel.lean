module

public import UniversalGroup.Simulator.Recognition.Forward
public import UniversalGroup.Foundations.HNN.TwistedCentralizer

@[expose] public section

/-!
# The exact HNN model of the centralizer subgroup D

Rebase the final simulator extension at its displayed generator T. The
subgroup D then consists of reduced words with coefficients in the embedded
copy of `⟨c,d⟩`. Its intersection with the preceding f stage is exactly that
copy of `⟨c,d⟩`.
-/

namespace UniversalGroup.SimulatorDModel
noncomputable section
open HNNLemmas
set_option maxHeartbeats 800000

variable (D : CodeWords) (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

/-- The coefficient subgroup in the preceding f stage. -/
def coefficients : Subgroup (SimulatorModel.FStage D hF hE) :=
  (SimulatorModel.CD D hF hE).map (SimulatorModel.ofF D hF hE)

/-- The positive marker, evaluated before adjoining q. -/
def marker : SimulatorModel.FStage D hF hE :=
  SimulatorModel.ofF D hF hE (SimulatorModel.coreOf D hF hE (BorisovCStage.positive3 D.P))

abbrev Rebased := TwistedCentralizer.Model (SimulatorModel.qSubgroup D hF hE)
  (marker D hF hE) (SimulatorModel.fStable D hF hE)

def toLiteral : Rebased D hF hE →* (simulatorL D).Group :=
  (SimulatorModel.fromModel D hF hE).comp
    (TwistedCentralizer.toAmbient (SimulatorModel.qSubgroup D hF hE)
      (marker D hF hE) (SimulatorModel.fStable D hF hE))

/-- The T presentation is equivalent to the literal simulator. -/
def equiv : Rebased D hF hE ≃* (simulatorL D).Group :=
  (TwistedCentralizer.equiv (SimulatorModel.qSubgroup D hF hE)
    (marker D hF hE) (SimulatorModel.fStable D hF hE)).trans (SimulatorModel.equiv D hF hE).symm

theorem toLiteral_injective : Function.Injective (toLiteral D hF hE) := (equiv D hF hE).injective

@[simp] theorem toLiteral_of (x : SimulatorModel.FStage D hF hE) :
    toLiteral D hF hE (TwistedCentralizer.of (SimulatorModel.qSubgroup D hF hE)
      (marker D hF hE) (SimulatorModel.fStable D hF hE) x) = SimulatorModel.fromF D hF hE x := by
  rw [toLiteral, MonoidHom.comp_apply, TwistedCentralizer.toAmbient_of]
  exact SimulatorModel.fromModel_ofQ D hF hE x

private theorem fromCore_positive (w : PositiveWord) :
    SimulatorModel.fromCore D hF hE
      (SimulatorModel.coreOf D hF hE (BorisovCStage.positive3 w)) = SimulatorRelations.positive D w := by
  simp only [BorisovCStage.positive3, CodeSubgroups.map_positive]
  simp [SimulatorRelations.positive, SimulatorModel.fromCore_s1, SimulatorModel.fromCore_s2]

@[simp] theorem fromF_marker :
    SimulatorModel.fromF D hF hE (marker D hF hE) = SimulatorRelations.positive D D.P := by
  rw [marker, SimulatorModel.fromF_ofF, fromCore_positive]

@[simp] theorem fromModel_target :
    SimulatorModel.fromModel D hF hE (TwistedCentralizer.target
      (SimulatorModel.qSubgroup D hF hE) (marker D hF hE) (SimulatorModel.fStable D hF hE)) =
      SimulatorRecognitionForward.target D := by
  change SimulatorModel.fromModel D hF hE
    (SimulatorModel.ofQ D hF hE (marker D hF hE) * SimulatorModel.q D hF hE *
      SimulatorModel.ofQ D hF hE ((marker D hF hE)⁻¹ * SimulatorModel.fStable D hF hE)) = _
  simp only [map_mul, map_inv, SimulatorModel.fromModel_ofQ, SimulatorModel.fromModel_q,
    fromF_marker, SimulatorModel.fromF_stable, SimulatorRecognitionForward.target_eq, mul_assoc]

@[simp] theorem toLiteral_stable :
    toLiteral D hF hE (TwistedCentralizer.stable (SimulatorModel.qSubgroup D hF hE)
      (marker D hF hE) (SimulatorModel.fStable D hF hE)) = SimulatorRecognitionForward.target D := by
  simp [toLiteral]

/-- The f stable letter centralizes every coefficient. -/
theorem f_commutes (x : SimulatorModel.FStage D hF hE) (hx : x ∈ coefficients D hF hE) :
    Commute (SimulatorModel.fStable D hF hE) x := by
  rcases hx with ⟨a,ha,rfl⟩
  exact ((centralizerOf_commute_stable_iff (SimulatorModel.CD D hF hE) a).mpr ha).symm

def subgroup : Subgroup (SimulatorModel.Model D hF hE) :=
  TwistedCentralizer.subgroup (SimulatorModel.qSubgroup D hF hE)
    (marker D hF hE) (SimulatorModel.fStable D hF hE) (coefficients D hF hE)

theorem coefficients_map : (coefficients D hF hE).map (SimulatorModel.fromF D hF hE) =
    SimulatorRecognitionForward.CD D := by
  rw [coefficients, Subgroup.map_map]
  change (Subgroup.closure ({SimulatorModel.coreC D hF hE,
    SimulatorModel.coreOf D hF hE BorisovHNNModel.d3} : Set _)).map
      ((SimulatorModel.fromF D hF hE).comp (SimulatorModel.ofF D hF hE)) = _
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  simp only [MonoidHom.comp_apply, SimulatorModel.fromF_ofF,
    SimulatorModel.fromCore_c, SimulatorModel.fromCore_d]
  rfl

/-- The twisted-stable subgroup is precisely the displayed subgroup D. -/
theorem subgroup_map : (subgroup D hF hE).map (SimulatorModel.fromModel D hF hE) = simulatorD D := by
  unfold subgroup TwistedCentralizer.subgroup generatedWith
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.map_sup,
    Subgroup.map_map, MonoidHom.map_closure, Set.image_singleton, fromModel_target]
  have hcomp : (SimulatorModel.fromModel D hF hE).comp
      (centralizerOf (SimulatorModel.qSubgroup D hF hE)) = SimulatorModel.fromF D hF hE := by
    apply MonoidHom.ext
    intro x
    exact SimulatorModel.fromModel_ofQ D hF hE x
  rw [hcomp, coefficients_map]
  rw [SimulatorRecognitionForward.CD, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro ((rfl|rfl)|rfl)
    · exact ⟨0,by simp [FP.evalWord,simulatorLWords,SimulatorRelations.c,generators]⟩
    · exact ⟨1,by simp [FP.evalWord,simulatorLWords,SimulatorRelations.d,generators]⟩
    · exact ⟨2,rfl⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [FP.evalWord,simulatorLWords,SimulatorRelations.c,
      SimulatorRelations.d,SimulatorRecognitionForward.target,generators]

/-- No additional element of the f stage belongs to D. -/
theorem fromF_mem_D_iff (x : SimulatorModel.FStage D hF hE) :
    SimulatorModel.fromF D hF hE x ∈ simulatorD D ↔ x ∈ coefficients D hF hE := by
  rw [← subgroup_map]
  constructor
  · rintro ⟨z,hz,hzx⟩
    have he : z = SimulatorModel.ofQ D hF hE x :=
      SimulatorModel.fromModel_injective D hF hE (hzx.trans (SimulatorModel.fromModel_ofQ D hF hE x).symm)
    rw [he] at hz
    exact (TwistedCentralizer.of_mem_subgroup_iff _ _ _ _ (f_commutes D hF hE) x).mp hz
  · intro hx
    refine ⟨SimulatorModel.ofQ D hF hE x,?_,SimulatorModel.fromModel_ofQ D hF hE x⟩
    exact (TwistedCentralizer.of_mem_subgroup_iff _ _ _ _ (f_commutes D hF hE) x).mpr hx

/-- Every literal D element has a reduced T-word whose coefficients lie
in the embedded subgroup ⟨c,d⟩ of the f stage. -/
theorem exists_reducedWord {x : (simulatorL D).Group} (hx : x ∈ simulatorD D) :
    ∃ w : HNNExtension.NormalWord.ReducedWord (SimulatorModel.FStage D hF hE)
      (TwistedCentralizer.left (SimulatorModel.qSubgroup D hF hE) (marker D hF hE)).range
      (TwistedCentralizer.right (SimulatorModel.qSubgroup D hF hE) (marker D hF hE)
        (SimulatorModel.fStable D hF hE)).range,
      toLiteral D hF hE (w.prod (UniversalGroup.rangeEquiv
        (TwistedCentralizer.left (SimulatorModel.qSubgroup D hF hE) (marker D hF hE))
        (TwistedCentralizer.right (SimulatorModel.qSubgroup D hF hE) (marker D hF hE)
          (SimulatorModel.fStable D hF hE))
        (TwistedCentralizer.left_injective _ _) (TwistedCentralizer.right_injective _ _ _))) = x ∧
        w.head ∈ coefficients D hF hE ∧ ∀ p ∈ w.toList, p.2 ∈ coefficients D hF hE := by
  rw [← subgroup_map D hF hE] at hx
  rcases hx with ⟨z,hz,rfl⟩
  obtain ⟨w,hw,hhead,hcoeff⟩ := TwistedCentralizer.exists_reducedWord _ _ _ _
    (f_commutes D hF hE) hz
  exact ⟨w,congrArg (SimulatorModel.fromModel D hF hE) hw,hhead,hcoeff⟩

end
end UniversalGroup.SimulatorDModel
