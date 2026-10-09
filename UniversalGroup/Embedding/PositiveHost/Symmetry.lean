module

public import UniversalGroup.Embedding.PositiveHost.CoreSymmetry
public import UniversalGroup.Simulator.Symmetry.CodeIntersections

@[expose] public section

/-! The positive symmetry between the faithful single-letter simulator subgroups. -/

namespace UniversalGroup.Embedding.PositiveHost

open HNNLemmas SimulatorSymmetry
noncomputable section
variable (D : CodeWords) (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

def baseEquiv : Base D hF hE 0 ≃* Base D hF hE 1 :=
  CoreSymmetry.cSubgroupEquiv (rules D hF hE)

theorem associated_equiv_map : (associatedMinus D hF hE).map (baseEquiv D hF hE).toMonoidHom =
    associatedPlus D hF hE := by
  rw [associatedMinus, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  change Subgroup.closure
      ({CoreSymmetry.cSubgroupEquiv (rules D hF hE) (CoreSymmetry.coreC (rules D hF hE) 0),
        CoreSymmetry.cSubgroupEquiv (rules D hF hE) (CoreSymmetry.coreD (rules D hF hE) 0)} : Set _) =
    Subgroup.closure ({CoreSymmetry.coreC (rules D hF hE) 1,
      CoreSymmetry.coreE (rules D hF hE) 1} : Set _)
  simp

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

/-- The desired isomorphism of the actual five-generator subgroups of `L`. -/
def equiv : HMinus D ≃* HPlus D :=
  (MulEquiv.subgroupCongr (range_minusHom D hF hE).symm).trans
    ((subgroupEquiv D hF hE).trans (MulEquiv.subgroupCongr (range_plusHom D hF hE)))

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

@[simp] theorem equiv_d : equiv D hF hE (minusElement D 0) = plusElement D 1 := by
  apply Subtype.ext
  rw [equiv_parameter]
  change plusHom D hF hE (parameterEquiv D hF hE (centralizerOf _ (baseD D hF hE 0))) = _
  rw [parameterEquiv_of]
  change plusHom D hF hE (centralizerOf _ ((baseEquiv D hF hE) (baseD D hF hE 0))) = _
  change plusHom D hF hE (centralizerOf _
    (CoreSymmetry.cSubgroupEquiv (rules D hF hE)
      (CoreSymmetry.coreD (rules D hF hE) 0))) = _
  rw [CoreSymmetry.cSubgroupEquiv_coreD]
  exact plusHom_parameters D hF hE 1

@[simp] theorem equiv_e0 : equiv D hF hE (minusElement D 1) = plusElement D 0 := by
  apply Subtype.ext
  rw [equiv_parameter]
  change plusHom D hF hE (parameterEquiv D hF hE (centralizerOf _ (baseE D hF hE 0))) = _
  rw [parameterEquiv_of]
  change plusHom D hF hE (centralizerOf _
    (CoreSymmetry.cSubgroupEquiv (rules D hF hE)
      (CoreSymmetry.coreE (rules D hF hE) 0))) = _
  rw [CoreSymmetry.cSubgroupEquiv_coreE]
  exact plusHom_parameters D hF hE 0

@[simp] theorem equiv_c : equiv D hF hE (minusElement D 2) = plusElement D 2 := by
  apply Subtype.ext
  rw [equiv_parameter]
  change plusHom D hF hE (parameterEquiv D hF hE (centralizerOf _ (baseC D hF hE 0))) = _
  rw [parameterEquiv_of]
  change plusHom D hF hE (centralizerOf _
    (CoreSymmetry.cSubgroupEquiv (rules D hF hE)
      (CoreSymmetry.coreC (rules D hF hE) 0))) = _
  rw [CoreSymmetry.cSubgroupEquiv_coreC]
  exact plusHom_parameters D hF hE 2

@[simp] theorem equiv_f : equiv D hF hE (minusElement D 3) = plusElement D 3 := by
  apply Subtype.ext
  rw [equiv_parameter]
  change plusHom D hF hE (parameterEquiv D hF hE (centralizerStable _)) = _
  rw [parameterEquiv_stable]
  exact plusHom_parameters D hF hE 3

@[simp] theorem equiv_x1 : equiv D hF hE (minusElement D 4) = (plusElement D 4)⁻¹ := by
  apply Subtype.ext
  rw [equiv_parameter]
  change plusHom D hF hE (parameterEquiv D hF hE (centralizerOf _ (baseS D hF hE 0))) = _
  rw [parameterEquiv_of]
  change plusHom D hF hE (centralizerOf _
    (CoreSymmetry.cSubgroupEquiv (rules D hF hE)
      (CoreSymmetry.coreStable (rules D hF hE) 0))) = _
  rw [CoreSymmetry.cSubgroupEquiv_coreS1]
  change plusHom D hF hE (centralizerOf _ (baseS D hF hE 1)⁻¹) = _
  rw [map_inv, map_inv]
  exact congrArg Inv.inv (plusHom_parameters D hF hE 4)


/-- The single-letter symmetry regarded inside the literal `K` presentation. -/
def equivK : HMinusK D ≃* HPlusK D :=
  (minusMapK D).symm.trans ((equiv D hF hE).trans (plusMapK D))

@[simp] theorem equivK_minusMap (a : HMinus D) :
    equivK D hF hE (minusMapK D a) = plusMapK D (equiv D hF hE a) := by
  simp [equivK]

@[simp] theorem equivK_d : equivK D hF hE (minusElementK D 0) = plusElementK D 1 := by
  simp [minusElementK, plusElementK]
@[simp] theorem equivK_e0 : equivK D hF hE (minusElementK D 1) = plusElementK D 0 := by
  simp [minusElementK, plusElementK]
@[simp] theorem equivK_c : equivK D hF hE (minusElementK D 2) = plusElementK D 2 := by
  simp [minusElementK, plusElementK]
@[simp] theorem equivK_f : equivK D hF hE (minusElementK D 3) = plusElementK D 3 := by
  simp [minusElementK, plusElementK]
@[simp] theorem equivK_x1 : equivK D hF hE (minusElementK D 4) = (plusElementK D 4)⁻¹ := by
  simp [minusElementK, plusElementK]

end
end UniversalGroup.Embedding.PositiveHost
