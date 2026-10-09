module

public import UniversalGroup.Simulator.FreeLetters
public import UniversalGroup.Simulator.Core.Symmetry
public import UniversalGroup.Foundations.HNN.CentralizerMap

@[expose] public section

/-! The single-letter symmetry in the faithful simulator. -/

namespace UniversalGroup.SimulatorSymmetry

open HNNLemmas

noncomputable section

variable (D : CodeWords) (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

abbrev rules := SimulatorModel.rules D hF hE
abbrev Base (i : Fin 2) := BorisovCoreSymmetry.CSubgroup (rules D hF hE) i

abbrev baseC (i : Fin 2) : Base D hF hE i := BorisovCoreSymmetry.coreC (rules D hF hE) i
abbrev baseD (i : Fin 2) : Base D hF hE i := BorisovCoreSymmetry.coreD (rules D hF hE) i
abbrev baseE (i : Fin 2) : Base D hF hE i := BorisovCoreSymmetry.coreE (rules D hF hE) i
abbrev baseS (i : Fin 2) : Base D hF hE i := BorisovCoreSymmetry.coreStable (rules D hF hE) i

def associatedMinus : Subgroup (Base D hF hE 0) :=
  Subgroup.closure ({baseC D hF hE 0, baseD D hF hE 0} : Set _)

def associatedPlus : Subgroup (Base D hF hE 1) :=
  Subgroup.closure ({baseC D hF hE 1, baseE D hF hE 1} : Set _)

theorem associatedMinus_map : (associatedMinus D hF hE).map (Base D hF hE 0).subtype =
    SimulatorModel.CD D hF hE := by
  simp [associatedMinus, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, SimulatorModel.CD, baseC, baseD,
    BorisovCoreSymmetry.coreC, BorisovCoreSymmetry.coreD, SimulatorModel.coreC, SimulatorModel.coreOf]

theorem associatedPlus_map : (associatedPlus D hF hE).map (Base D hF hE 1).subtype =
    SimulatorModel.CE D hF hE := by
  simp [associatedPlus, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, SimulatorModel.CE, baseC, baseE,
    BorisovCoreSymmetry.coreC, BorisovCoreSymmetry.coreE, SimulatorModel.coreC, SimulatorModel.coreOf]

private theorem closure_pair_inv {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a, b⁻¹} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · exact Subgroup.subset_closure (by simp)
    · simpa using Subgroup.inv_mem (Subgroup.closure ({a, b⁻¹} : Set G))
        (Subgroup.subset_closure (by simp : b⁻¹ ∈ ({a, b⁻¹} : Set G)))

def baseEquiv : Base D hF hE 0 ≃* Base D hF hE 1 :=
  BorisovCoreSymmetry.cSubgroupEquiv (rules D hF hE)

theorem associated_equiv_map : (associatedMinus D hF hE).map (baseEquiv D hF hE).toMonoidHom =
    associatedPlus D hF hE := by
  simp only [associatedMinus, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    baseEquiv, baseC, baseD, MulEquiv.coe_toMonoidHom,
    BorisovCoreSymmetry.cSubgroupEquiv_coreC, BorisovCoreSymmetry.cSubgroupEquiv_coreD]
  change Subgroup.closure ({baseC D hF hE 1, (baseE D hF hE 1)⁻¹} : Set _) = _
  exact closure_pair_inv _ _

def associatedEquiv : associatedMinus D hF hE ≃* associatedPlus D hF hE :=
  ((baseEquiv D hF hE).subgroupMap (associatedMinus D hF hE)).trans
    (MulEquiv.subgroupCongr (associated_equiv_map D hF hE))

abbrev Minus := CentralizerHNN (Base D hF hE 0) (associatedMinus D hF hE)
abbrev Plus := CentralizerHNN (Base D hF hE 1) (associatedPlus D hF hE)

/-- The abstract single-letter symmetry, including the outer stable letter. -/
def parameterEquiv : Minus D hF hE ≃* Plus D hF hE :=
  HNNLemmas.congr (baseEquiv D hF hE) (associatedEquiv D hF hE) (associatedEquiv D hF hE)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

@[simp] theorem parameterEquiv_of (x : Base D hF hE 0) :
    parameterEquiv D hF hE (centralizerOf (associatedMinus D hF hE) x) =
      centralizerOf (associatedPlus D hF hE) (baseEquiv D hF hE x) := by
  rfl

@[simp] theorem parameterEquiv_stable :
    parameterEquiv D hF hE (centralizerStable (associatedMinus D hF hE)) =
      centralizerStable (associatedPlus D hF hE) := by
  rfl

theorem minus_mem (x : Base D hF hE 0) :
    x ∈ associatedMinus D hF hE ↔ (x : SimulatorModel.Core D hF hE) ∈ SimulatorModel.CD D hF hE := by
  rw [← associatedMinus_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    exact h ▸ hy

def plusBase : Base D hF hE 1 →* SimulatorModel.FStage D hF hE :=
  (SimulatorModel.ofF D hF hE).comp (Base D hF hE 1).subtype

theorem plus_mem (x : Base D hF hE 1) :
    x ∈ associatedPlus D hF hE ↔ plusBase D hF hE x ∈ SimulatorModel.qSubgroup D hF hE := by
  constructor
  · intro hx
    refine ⟨x, ?_, rfl⟩
    rw [← associatedPlus_map]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = (x : SimulatorModel.Core D hF hE) := (HNNExtension.of_injective _) hyx
    rw [← associatedPlus_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    have hz' : z = x := Subtype.ext (hzy.trans hy')
    exact hz' ▸ hz

def minusToF : Minus D hF hE →* SimulatorModel.FStage D hF hE :=
  CentralizerMap.hom (associatedMinus D hF hE) (SimulatorModel.CD D hF hE)
    (Base D hF hE 0).subtype (minus_mem D hF hE)

def minusToModel : Minus D hF hE →* SimulatorModel.Model D hF hE :=
  (SimulatorModel.ofQ D hF hE).comp (minusToF D hF hE)

def plusToModel : Plus D hF hE →* SimulatorModel.Model D hF hE :=
  CentralizerMap.hom (associatedPlus D hF hE) (SimulatorModel.qSubgroup D hF hE)
    (plusBase D hF hE) (plus_mem D hF hE)

theorem minusToModel_injective : Function.Injective (minusToModel D hF hE) :=
  (HNNExtension.of_injective _).comp
    (CentralizerMap.hom_injective _ _ _ _ Subtype.coe_injective)

theorem plusToModel_injective : Function.Injective (plusToModel D hF hE) :=
  CentralizerMap.hom_injective _ _ _ _
    ((HNNExtension.of_injective _).comp Subtype.coe_injective)

@[simp] theorem minusToModel_of (x : Base D hF hE 0) :
    minusToModel D hF hE (centralizerOf (associatedMinus D hF hE) x) =
      SimulatorModel.coreToModel D hF hE x := by
  exact congrArg (SimulatorModel.ofQ D hF hE)
    (CentralizerMap.hom_of _ _ _ _ x)

@[simp] theorem plusToModel_of (x : Base D hF hE 1) :
    plusToModel D hF hE (centralizerOf (associatedPlus D hF hE) x) =
      SimulatorModel.coreToModel D hF hE x := by
  simp [plusToModel, plusBase, SimulatorModel.coreToModel, SimulatorModel.ofQ]

@[simp] theorem minusToModel_stable :
    minusToModel D hF hE (centralizerStable (associatedMinus D hF hE)) = SimulatorModel.f D hF hE := by
  exact congrArg (SimulatorModel.ofQ D hF hE)
    (CentralizerMap.hom_stable _ _ _ _)

@[simp] theorem plusToModel_stable :
    plusToModel D hF hE (centralizerStable (associatedPlus D hF hE)) = SimulatorModel.q D hF hE := by
  simp [plusToModel, SimulatorModel.q]

/-- Conjugation by `f⁻¹`, followed by the faithful literal interpretation. -/
def coordinates : SimulatorModel.Model D hF hE →* (simulatorL D).Group :=
  (SimulatorModel.fromModel D hF hE).comp
    (MulAut.conj (SimulatorModel.f D hF hE)⁻¹).toMonoidHom

theorem coordinates_injective : Function.Injective (coordinates D hF hE) :=
  (SimulatorModel.fromModel_injective D hF hE).comp (MulAut.conj _).injective

@[simp] theorem coordinates_apply (x : SimulatorModel.Model D hF hE) :
    coordinates D hF hE x = (SimulatorRelations.f D)⁻¹ * SimulatorModel.fromModel D hF hE x * SimulatorRelations.f D := by
  simp [coordinates, SimulatorModel.f]

def minusHom : Minus D hF hE →* (simulatorL D).Group :=
  (coordinates D hF hE).comp (minusToModel D hF hE)

def plusHom : Plus D hF hE →* (simulatorL D).Group :=
  (coordinates D hF hE).comp (plusToModel D hF hE)

theorem minusHom_injective : Function.Injective (minusHom D hF hE) :=
  (coordinates_injective D hF hE).comp (minusToModel_injective D hF hE)

theorem plusHom_injective : Function.Injective (plusHom D hF hE) :=
  (coordinates_injective D hF hE).comp (plusToModel_injective D hF hE)

/-- The symmetry between the two actual embedded single-letter subgroups. -/
def subgroupEquiv : (minusHom D hF hE).range ≃* (plusHom D hF hE).range :=
  (MonoidHom.ofInjective (minusHom_injective D hF hE)).symm.trans
    ((parameterEquiv D hF hE).trans (MonoidHom.ofInjective (plusHom_injective D hF hE)))

theorem subgroupEquiv_apply (x : Minus D hF hE) :
    ((subgroupEquiv D hF hE ⟨minusHom D hF hE x, ⟨x, rfl⟩⟩ : (plusHom D hF hE).range) :
        (simulatorL D).Group) = plusHom D hF hE (parameterEquiv D hF hE x) := by
  change plusHom D hF hE (parameterEquiv D hF hE
    ((MonoidHom.ofInjective (minusHom_injective D hF hE)).symm
      ⟨minusHom D hF hE x, ⟨x, rfl⟩⟩)) = _
  have h : ((MonoidHom.ofInjective (minusHom_injective D hF hE)).symm
      ⟨minusHom D hF hE x, ⟨x, rfl⟩⟩) = x := by
    exact (MonoidHom.ofInjective (minusHom_injective D hF hE)).symm_apply_apply x
  rw [h]

private theorem generated_closure {G : Type*} [Group G] (A B : Subgroup G) (φ : A ≃* B) (S : Set G) :
    generatedWithStable (A := A) (B := B) (phi := φ) (Subgroup.closure S) =
      Subgroup.closure ((HNNExtension.of (φ := φ) '' S) ∪ {HNNExtension.t}) := by
  simp only [generatedWithStable, MonoidHom.map_closure, Subgroup.closure_union, Subgroup.closure_eq]

def baseSet (i : Fin 2) : Set (SimulatorModel.Core D hF hE) :=
  SimulatorModel.coreOf D hF hE ''
    ({BorisovHNNModel.d3, BorisovHNNModel.e3, BorisovCStage.stable3 i} : Set _) ∪
      {SimulatorModel.coreC D hF hE}

theorem base_eq_closure (i : Fin 2) : Base D hF hE i = Subgroup.closure (baseSet D hF hE i) := by
  change generatedWithStable (A := BorisovCStage.U (rules D hF hE))
    (B := BorisovCStage.V (rules D hF hE))
    (phi := BorisovCStage.cEquiv (rules D hF hE) (SimulatorModel.free D hF hE))
    (BorisovInputsBridge.J3 i) = _
  rw [BorisovInputsBridge.J3, generated_closure]
  simp only [baseSet, Subgroup.closure_union, SimulatorModel.coreC, BorisovCStage.c,
    Subgroup.closure_singleton_inv]
  rfl

def e0 : (simulatorL D).Group := (SimulatorRelations.f D)⁻¹ * SimulatorRelations.e D * SimulatorRelations.f D
def x (i : Fin 2) : (simulatorL D).Group := (SimulatorRelations.f D)⁻¹ * SimulatorRelations.s D i * SimulatorRelations.f D
def q0 : (simulatorL D).Group := (SimulatorRelations.f D)⁻¹ * SimulatorRelations.q D * SimulatorRelations.f D

@[simp] theorem coordinates_coreC : coordinates D hF hE (SimulatorModel.c D hF hE) = SimulatorRelations.c D := by
  rw [coordinates_apply]
  simp only [SimulatorModel.c, SimulatorModel.fromModel_core, SimulatorModel.fromCore_c]
  exact (SimulatorRelations.c_f D).symm.inv_mul_cancel

@[simp] theorem coordinates_d : coordinates D hF hE (SimulatorModel.d D hF hE) = SimulatorRelations.d D := by
  rw [coordinates_apply]
  simp only [SimulatorModel.d, SimulatorModel.lowToModel, MonoidHom.comp_apply,
    SimulatorModel.fromModel_core, SimulatorModel.fromCore_d]
  exact (SimulatorRelations.d_f D).symm.inv_mul_cancel

@[simp] theorem coordinates_e : coordinates D hF hE (SimulatorModel.e D hF hE) = e0 D := by
  simp [coordinates_apply, SimulatorModel.e, SimulatorModel.lowToModel, e0]

@[simp] theorem coordinates_s (i : Fin 2) : coordinates D hF hE (SimulatorModel.s D hF hE i) = x D i := by
  fin_cases i <;> simp [coordinates_apply, SimulatorModel.s, SimulatorModel.lowToModel, x]

@[simp] theorem coordinates_f : coordinates D hF hE (SimulatorModel.f D hF hE) = SimulatorRelations.f D := by
  simp [coordinates_apply, SimulatorModel.f]

@[simp] theorem coordinates_q : coordinates D hF hE (SimulatorModel.q D hF hE) = q0 D := by
  simp [coordinates_apply, q0]

def minusValues : Fin 5 → (simulatorL D).Group :=
  ![SimulatorRelations.d D, e0 D, SimulatorRelations.c D, SimulatorRelations.f D, x D 0]

def plusValues : Fin 5 → (simulatorL D).Group :=
  ![SimulatorRelations.d D, e0 D, SimulatorRelations.c D, q0 D, x D 1]

def minusParameters : Fin 5 → Minus D hF hE :=
  ![centralizerOf _ (baseD D hF hE 0), centralizerOf _ (baseE D hF hE 0),
    centralizerOf _ (baseC D hF hE 0), centralizerStable _, centralizerOf _ (baseS D hF hE 0)]

def plusParameters : Fin 5 → Plus D hF hE :=
  ![centralizerOf _ (baseD D hF hE 1), centralizerOf _ (baseE D hF hE 1),
    centralizerOf _ (baseC D hF hE 1), centralizerStable _, centralizerOf _ (baseS D hF hE 1)]

@[simp] theorem minusHom_parameters (i : Fin 5) : minusHom D hF hE (minusParameters D hF hE i) = minusValues D i := by
  fin_cases i <;>
    simp only [minusParameters, minusValues, Matrix.cons_val_zero', Matrix.cons_val_succ',
      minusHom, MonoidHom.comp_apply, minusToModel_of, minusToModel_stable]
  · exact coordinates_d D hF hE
  · exact coordinates_e D hF hE
  · exact coordinates_coreC D hF hE
  · exact coordinates_f D hF hE
  · exact coordinates_s D hF hE 0

@[simp] theorem plusHom_parameters (i : Fin 5) : plusHom D hF hE (plusParameters D hF hE i) = plusValues D i := by
  fin_cases i <;>
    simp only [plusParameters, plusValues, Matrix.cons_val_zero', Matrix.cons_val_succ',
      plusHom, MonoidHom.comp_apply, plusToModel_of, plusToModel_stable]
  · exact coordinates_d D hF hE
  · exact coordinates_e D hF hE
  · exact coordinates_coreC D hF hE
  · exact coordinates_q D hF hE
  · exact coordinates_s D hF hE 1

def HMinus : Subgroup (simulatorL D).Group := Subgroup.closure (Set.range (minusValues D))
def HPlus : Subgroup (simulatorL D).Group := Subgroup.closure (Set.range (plusValues D))

private theorem base_le_comap {G : Type*} [Group G] (i : Fin 2)
    (φ : SimulatorModel.Core D hF hE →* G) (H : Subgroup G)
    (hd : φ (SimulatorModel.coreOf D hF hE BorisovHNNModel.d3) ∈ H)
    (he : φ (SimulatorModel.coreOf D hF hE BorisovHNNModel.e3) ∈ H)
    (hc : φ (SimulatorModel.coreC D hF hE) ∈ H)
    (hs : φ (SimulatorModel.coreOf D hF hE (BorisovCStage.stable3 i)) ∈ H) :
    Base D hF hE i ≤ H.comap φ := by
  rw [base_eq_closure, Subgroup.closure_le]
  rintro x (⟨y, hy, rfl⟩ | rfl)
  · rcases hy with rfl | rfl | rfl
    · exact hd
    · exact he
    · exact hs
  · exact hc

private theorem minus_base_le : Base D hF hE 0 ≤
    (HMinus D).comap ((coordinates D hF hE).comp (SimulatorModel.coreToModel D hF hE)) := by
  apply base_le_comap
  · change coordinates D hF hE (SimulatorModel.d D hF hE) ∈ HMinus D
    rw [coordinates_d]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  · change coordinates D hF hE (SimulatorModel.e D hF hE) ∈ HMinus D
    rw [coordinates_e]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  · change coordinates D hF hE (SimulatorModel.c D hF hE) ∈ HMinus D
    rw [coordinates_coreC]
    exact Subgroup.subset_closure ⟨2, rfl⟩
  · change coordinates D hF hE (SimulatorModel.s D hF hE 0) ∈ HMinus D
    rw [coordinates_s]
    exact Subgroup.subset_closure ⟨4, rfl⟩

private theorem plus_base_le : Base D hF hE 1 ≤
    (HPlus D).comap ((coordinates D hF hE).comp (SimulatorModel.coreToModel D hF hE)) := by
  apply base_le_comap
  · change coordinates D hF hE (SimulatorModel.d D hF hE) ∈ HPlus D
    rw [coordinates_d]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  · change coordinates D hF hE (SimulatorModel.e D hF hE) ∈ HPlus D
    rw [coordinates_e]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  · change coordinates D hF hE (SimulatorModel.c D hF hE) ∈ HPlus D
    rw [coordinates_coreC]
    exact Subgroup.subset_closure ⟨2, rfl⟩
  · change coordinates D hF hE (SimulatorModel.s D hF hE 1) ∈ HPlus D
    rw [coordinates_s]
    exact Subgroup.subset_closure ⟨4, rfl⟩

/-- The negative parameter model is precisely the subgroup on
`d,f⁻¹ef,c,f,f⁻¹s₁f`. -/
theorem range_minusHom : (minusHom D hF hE).range = HMinus D := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using HNNExtension.induction_on with
    | of x =>
        change coordinates D hF hE (minusToModel D hF hE (centralizerOf _ x)) ∈ HMinus D
        rw [minusToModel_of]
        exact minus_base_le D hF hE x.property
    | t =>
        change minusHom D hF hE (minusParameters D hF hE 3) ∈ HMinus D
        rw [minusHom_parameters]
        exact Subgroup.subset_closure ⟨3, rfl⟩
    | mul x y hx hy => simpa using (HMinus D).mul_mem hx hy
    | inv x hx => simpa using (HMinus D).inv_mem hx
  · rw [HMinus, Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨minusParameters D hF hE i, minusHom_parameters D hF hE i⟩

/-- The positive parameter model is precisely the subgroup on
`d,f⁻¹ef,c,f⁻¹qf,f⁻¹s₂f`. -/
theorem range_plusHom : (plusHom D hF hE).range = HPlus D := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using HNNExtension.induction_on with
    | of x =>
        change coordinates D hF hE (plusToModel D hF hE (centralizerOf _ x)) ∈ HPlus D
        rw [plusToModel_of]
        exact plus_base_le D hF hE x.property
    | t =>
        change plusHom D hF hE (plusParameters D hF hE 3) ∈ HPlus D
        rw [plusHom_parameters]
        exact Subgroup.subset_closure ⟨3, rfl⟩
    | mul x y hx hy => simpa using (HPlus D).mul_mem hx hy
    | inv x hx => simpa using (HPlus D).inv_mem hx
  · rw [HPlus, Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨plusParameters D hF hE i, plusHom_parameters D hF hE i⟩

/-- The desired isomorphism of the actual five-generator subgroups of `L`. -/
def equiv : HMinus D ≃* HPlus D :=
  (MulEquiv.subgroupCongr (range_minusHom D hF hE).symm).trans
    ((subgroupEquiv D hF hE).trans (MulEquiv.subgroupCongr (range_plusHom D hF hE)))

def minusElement (i : Fin 5) : HMinus D := ⟨minusValues D i, Subgroup.subset_closure ⟨i, rfl⟩⟩
def plusElement (i : Fin 5) : HPlus D := ⟨plusValues D i, Subgroup.subset_closure ⟨i, rfl⟩⟩

theorem equiv_parameter (i : Fin 5) :
    ((equiv D hF hE (minusElement D i) : HPlus D) : (simulatorL D).Group) =
      plusHom D hF hE (parameterEquiv D hF hE (minusParameters D hF hE i)) := by
  have ha : (MulEquiv.subgroupCongr (range_minusHom D hF hE).symm) (minusElement D i) =
      (⟨minusHom D hF hE (minusParameters D hF hE i), ⟨minusParameters D hF hE i, rfl⟩⟩ :
        (minusHom D hF hE).range) := by
    apply Subtype.ext
    exact (minusHom_parameters D hF hE i).symm
  change ((subgroupEquiv D hF hE
    ((MulEquiv.subgroupCongr (range_minusHom D hF hE).symm) (minusElement D i)) :
      (plusHom D hF hE).range) : (simulatorL D).Group) = _
  rw [ha]
  exact subgroupEquiv_apply D hF hE _

@[simp] theorem equiv_x1 : equiv D hF hE (minusElement D 4) = (plusElement D 4)⁻¹ := by
  apply Subtype.ext
  rw [equiv_parameter]
  change plusHom D hF hE (parameterEquiv D hF hE (centralizerOf _ (baseS D hF hE 0))) = _
  rw [parameterEquiv_of]
  simp only [baseEquiv, baseS, BorisovCoreSymmetry.cSubgroupEquiv_coreS1, map_inv]
  exact congrArg Inv.inv (plusHom_parameters D hF hE 4)

end

end UniversalGroup.SimulatorSymmetry
