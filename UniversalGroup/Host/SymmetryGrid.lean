module

public import UniversalGroup.Host.SymmetrySubgroups
public import UniversalGroup.Host.EllGrid

@[expose] public section

/-! Exact restrictions of the two `h` subgroups to the product grid. -/

namespace UniversalGroup.SymmetryGrid

noncomputable section
set_option maxHeartbeats 1600000
open SymmetrySubgroups HNNLemmas SimulatorSymmetry

variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

section Restricted
variable (H : Subgroup (simulatorK D.toCodeWords).Group)
  (hC : (EllStage.toK G D hi).range ⊓ H = simulatorGrid D.toCodeWords ⊓ H)

theorem simulator_mem_intoEll_iff (k : (simulatorK D.toCodeWords).Group) :
    (EllStage.simulatorEmbedding G D hi).hom k ∈ (intoEll G D hi H hC).range ↔ k ∈ H := by
  constructor
  · rintro ⟨w, hw⟩
    have hwbase : intoEll G D hi H hC w ∈ (EllStage.ofM G D hi).range :=
      ⟨EllStage.ofK G D k, hw.symm⟩
    obtain ⟨m, rfl⟩ := CentralizerIntoHNN.preimage_base _ _ _ _ _
      (mem_left G D hi H hC) (mem_right G D hi H hC)
      (fixes_associated G D hi H hC) w hwbase
    rw [intoEll_of] at hw
    have hm : intoM G D H m = EllStage.ofK G D k := EllStage.ofM_injective G D hi hw
    have hmbase : intoM G D H m ∈ (EllStage.ofK G D).range := ⟨k, hm.symm⟩
    obtain ⟨b, hb⟩ := AmalgamRestriction.preimage_base (simulatorGrid D.toCodeWords)
      H G.presentation.Group m hmbase
    rw [← hb, intoM_base] at hm
    have heq := CentralizingAmalgam.ofBase_injective (simulatorGrid D.toCodeWords) G.presentation.Group hm
    exact heq ▸ b.property
  · intro hk
    refine ⟨centralizerOf (associated G D H)
      (CentralizingAmalgam.ofBase (Common G D H) G.presentation.Group ⟨k, hk⟩), ?_⟩
    rw [intoEll_of, intoM_base]
    rfl


include hC in
theorem inputFree_le_intoEll (hc : generators (simulatorK D.toCodeWords) 0 ∈ H) :
    InputFreeSubgroup.subgroup G D hi ≤ (intoEll G D hi H hC).range := by
  rw [InputFreeSubgroup.subgroup, InputFreeSubgroup.hom_range]
  apply sup_le
  · apply sup_le
    · rintro _ ⟨z, rfl⟩
      apply (simulator_mem_intoEll_iff G D hi H hC _).mpr
      exact H.zpow_mem hc _
    · rintro _ ⟨g, rfl⟩
      refine ⟨centralizerOf (associated G D H)
        (CentralizingAmalgam.ofInput (Common G D H) G.presentation.Group g), ?_⟩
      rw [intoEll_of, intoM_input]
      rfl
  · rw [Subgroup.zpowers_le]
    refine ⟨(centralizerStable (associated G D H))⁻¹, ?_⟩
    simp

end Restricted

theorem simulator_mem_left_iff (k : (simulatorK D.toCodeWords).Group) :
    (EllStage.simulatorEmbedding G D hi).hom k ∈ (left G D hi).range ↔ k ∈ minusH G D :=
  simulator_mem_intoEll_iff G D hi _ (minus_exact G D hi) k

theorem range_right : (right G D hi).range =
    (intoEll G D hi (plusH G D) (plus_exact G D hi)).range := by
  have he : (extensionEquiv G D hi).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (extensionEquiv G D hi).surjective
  rw [right, MonoidHom.range_comp, he]
  ext x
  simp

theorem simulator_mem_right_iff (k : (simulatorK D.toCodeWords).Group) :
    (EllStage.simulatorEmbedding G D hi).hom k ∈ (right G D hi).range ↔ k ∈ plusH G D := by
  rw [range_right]
  exact simulator_mem_intoEll_iff G D hi _ (plus_exact G D hi) k

private theorem c_mem_minus : generators (simulatorK D.toCodeWords) 0 ∈ minusH G D := by
  have h := (minusElementK D.toCodeWords 2).property
  simpa [minusElementK_val, minusValues, simulatorInclusion, SimulatorRelations.c, generators] using h

private theorem c_mem_plus : generators (simulatorK D.toCodeWords) 0 ∈ plusH G D := by
  have h := (plusElementK D.toCodeWords 2).property
  simpa [plusElementK_val, plusValues, simulatorInclusion, SimulatorRelations.c, generators] using h

theorem inputFree_le_left : InputFreeSubgroup.subgroup G D hi ≤ (left G D hi).range :=
  inputFree_le_intoEll G D hi _ (minus_exact G D hi) (c_mem_minus G D)

theorem inputFree_le_right : InputFreeSubgroup.subgroup G D hi ≤ (right G D hi).range := by
  rw [range_right]
  exact inputFree_le_intoEll G D hi _ (plus_exact G D hi) (c_mem_plus G D)

private theorem lift_cyclic_iff (j : Fin 4) (v : FreeGroup (Fin 4)) :
    SimulatorGrid.lift D.toCodeWords v ∈
      Subgroup.closure ({SimulatorGrid.lift D.toCodeWords (FreeGroup.of j)} : Set _) ↔
      v ∈ Subgroup.closure ({FreeGroup.of j} : Set _) := by
  rw [← Set.image_singleton, ← MonoidHom.map_closure]
  exact Subgroup.mem_map_iff_mem (SimulatorGrid.lift_injective D.toCodeWords D.F_support D.E_support)

theorem grid_mem_left_iff (v : FreeGroup (Fin 4)) :
    EllGrid.right G D hi v ∈ (left G D hi).range ↔
      v ∈ Subgroup.closure ({FreeGroup.of 1} : Set _) := by
  rw [EllGrid.right, MonoidHom.comp_apply, simulator_mem_left_iff]
  have hv : SimulatorGrid.lift D.toCodeWords v ∈ simulatorGrid D.toCodeWords :=
    (SimulatorGrid.lift_range D.toCodeWords) ▸ ⟨v, rfl⟩
  rw [show SimulatorGrid.lift D.toCodeWords v ∈ minusH G D ↔
      SimulatorGrid.lift D.toCodeWords v ∈ simulatorGrid D.toCodeWords ⊓ minusH G D from
        ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩,
    grid_inf_HMinusK G D hi]
  have hx : xK D.toCodeWords 0 = SimulatorGrid.lift D.toCodeWords (FreeGroup.of 1) := by
    rw [SimulatorGrid.lift_of, xK_eq_gridValue]
    congr 1
  rw [hx]
  exact lift_cyclic_iff G D 1 v

theorem grid_mem_right_iff (v : FreeGroup (Fin 4)) :
    EllGrid.right G D hi v ∈ (right G D hi).range ↔
      v ∈ Subgroup.closure ({FreeGroup.of 2} : Set _) := by
  rw [EllGrid.right, MonoidHom.comp_apply, simulator_mem_right_iff]
  have hv : SimulatorGrid.lift D.toCodeWords v ∈ simulatorGrid D.toCodeWords :=
    (SimulatorGrid.lift_range D.toCodeWords) ▸ ⟨v, rfl⟩
  rw [show SimulatorGrid.lift D.toCodeWords v ∈ plusH G D ↔
      SimulatorGrid.lift D.toCodeWords v ∈ simulatorGrid D.toCodeWords ⊓ plusH G D from
        ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩,
    grid_inf_HPlusK G D hi]
  have hx : xK D.toCodeWords 1 = SimulatorGrid.lift D.toCodeWords (FreeGroup.of 2) := by
    rw [SimulatorGrid.lift_of, xK_eq_gridValue]
    congr 1
  rw [hx]
  exact lift_cyclic_iff G D 2 v

theorem product_mem_left_iff (a : InputFreeSubgroup.Domain G × FreeGroup (Fin 4)) :
    EllGrid.product G D hi a ∈ (left G D hi).range ↔
      a.2 ∈ Subgroup.closure ({FreeGroup.of 1} : Set _) := by
  change InputFreeSubgroup.hom G D hi a.1 * EllGrid.right G D hi a.2 ∈ _ ↔ _
  have hu : InputFreeSubgroup.hom G D hi a.1 ∈ (left G D hi).range :=
    inputFree_le_left G D hi ⟨a.1, rfl⟩
  exact (Subgroup.mul_mem_cancel_left _ hu).trans (grid_mem_left_iff G D hi a.2)

theorem product_mem_right_iff (a : InputFreeSubgroup.Domain G × FreeGroup (Fin 4)) :
    EllGrid.product G D hi a ∈ (right G D hi).range ↔
      a.2 ∈ Subgroup.closure ({FreeGroup.of 2} : Set _) := by
  change InputFreeSubgroup.hom G D hi a.1 * EllGrid.right G D hi a.2 ∈ _ ↔ _
  have hu : InputFreeSubgroup.hom G D hi a.1 ∈ (right G D hi).range :=
    inputFree_le_right G D hi ⟨a.1, rfl⟩
  exact (Subgroup.mul_mem_cancel_left _ hu).trans (grid_mem_right_iff G D hi a.2)

end
end UniversalGroup.SymmetryGrid
