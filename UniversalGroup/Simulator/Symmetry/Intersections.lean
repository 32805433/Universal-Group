module

public import UniversalGroup.Simulator.Symmetry.Equivalence

@[expose] public section

/-! Exact intersections of the single-letter subgroups with the free
four-letter simulator subgroup. -/

namespace UniversalGroup.SimulatorSymmetry

open HNNLemmas BorisovCStage BorisovHNNModel BorisovInputsBridge SimulatorFreeLetters

noncomputable section

variable (D : CodeWords) (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

private theorem projection_J3 (i : Fin 2) :
    J3 i ≤ (Subgroup.closure ({FreeGroup.of i} : Set (FreeGroup (Fin 2)))).comap stableProjection3 := by
  rw [J3, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · simp
  · simp
  · fin_cases i <;> simp [stable3]

private theorem lowLetters_of (i : Fin 2) : lowLetters (FreeGroup.of i) = stable3 i := by
  fin_cases i <;> simp [lowLetters, stable3]

def coreCyclic (i : Fin 2) : Subgroup (SimulatorModel.Core D hF hE) :=
  Subgroup.closure ({SimulatorModel.coreOf D hF hE (stable3 i)} : Set _)

theorem base_inf_coreLetters (i : Fin 2) :
    (coreLetters D hF hE).range ⊓ Base D hF hE i = coreCyclic D hF hE i := by
  apply le_antisymm
  · rintro x ⟨⟨w, rfl⟩, hw⟩
    have hm : coreLetters D hF hE w ∈ Base D hF hE i ⊓ (SimulatorModel.coreOf D hF hE).range :=
      ⟨hw, ⟨lowLetters w, rfl⟩⟩
    have hbase : Base D hF hE i ⊓ (SimulatorModel.coreOf D hF hE).range =
        (J3 i).map (SimulatorModel.coreOf D hF hE) :=
      generatedWithStable_inf_base (J3 i) (cEquiv_mem_J3_iff (rules D hF hE) (SimulatorModel.free D hF hE) i)
    rw [hbase] at hm
    rcases hm with ⟨y, hy, hyw⟩
    have h : y = lowLetters w := (BorisovCStage.of3_injective _ _) hyw
    have hp := projection_J3 i (h ▸ hy)
    change stableProjection3 (lowLetters w) ∈ Subgroup.closure {FreeGroup.of i} at hp
    rw [projection_lowLetters] at hp
    rcases Subgroup.mem_closure_singleton.mp hp with ⟨z, hz⟩
    rw [← hz, map_zpow]
    change (SimulatorModel.coreOf D hF hE (lowLetters (FreeGroup.of i))) ^ z ∈ _
    rw [lowLetters_of]
    exact (coreCyclic D hF hE i).zpow_mem (Subgroup.subset_closure rfl) z
  · rw [coreCyclic, Subgroup.closure_le, Set.singleton_subset_iff]
    constructor
    · exact ⟨FreeGroup.of i, by simp [coreLetters, lowLetters_of]⟩
    · exact (baseS D hF hE i).property

theorem CD_le_base : SimulatorModel.CD D hF hE ≤ Base D hF hE 0 := by
  rw [SimulatorModel.CD, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact (baseC D hF hE 0).property
  · exact (baseD D hF hE 0).property

theorem CE_le_base : SimulatorModel.CE D hF hE ≤ Base D hF hE 1 := by
  rw [SimulatorModel.CE, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact (baseC D hF hE 1).property
  · exact (baseE D hF hE 1).property

theorem range_minusToF : (minusToF D hF hE).range =
    generatedWithStable (A := SimulatorModel.CD D hF hE) (B := SimulatorModel.CD D hF hE)
      (phi := MulEquiv.refl _) (Base D hF hE 0) := by
  unfold minusToF
  refine (CentralizerMap.range_eq_generated _ _ _ _).trans ?_
  simp

theorem range_fLetters : (fLetters D hF hE).range =
    generatedWithStable (A := SimulatorModel.CD D hF hE) (B := SimulatorModel.CD D hF hE)
      (phi := MulEquiv.refl _) (coreLetters D hF hE).range :=
  AdjoinFree.range_hom _ _

theorem minusToF_inf_fLetters : (fLetters D hF hE).range ⊓ (minusToF D hF hE).range =
    generatedWithStable (A := SimulatorModel.CD D hF hE) (B := SimulatorModel.CD D hF hE)
      (phi := MulEquiv.refl _) (coreCyclic D hF hE 0) := by
  rw [range_fLetters, range_minusToF,
    centralizer_intersection_of_le _ _ _ (CD_le_base D hF hE), base_inf_coreLetters]

private theorem inf_map_restrict {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (U V W : Subgroup G) (X : Subgroup H)
    (hφ : Function.Injective φ) (hX : X ⊓ φ.range = U.map φ) (hUV : U ⊓ V = W) :
    X ⊓ V.map φ = W.map φ := by
  apply le_antisymm
  · rintro x ⟨hx, y, hy, rfl⟩
    have hm : φ y ∈ X ⊓ φ.range := ⟨hx, ⟨y, rfl⟩⟩
    rw [hX] at hm
    rcases hm with ⟨z, hz, hzy⟩
    have h : z = y := hφ hzy
    refine ⟨y, ?_, rfl⟩
    rw [← hUV]
    exact ⟨h ▸ hz, hy⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [← hUV] at hy
    have hm : φ y ∈ U.map φ := ⟨y, hy.1, rfl⟩
    rw [← hX] at hm
    exact ⟨hm.1, y, hy.2, rfl⟩

theorem minusToModel_inf_modelLetters :
    (modelLetters D hF hE).range ⊓ (minusToModel D hF hE).range =
      (generatedWithStable (A := SimulatorModel.CD D hF hE) (B := SimulatorModel.CD D hF hE)
        (phi := MulEquiv.refl _) (coreCyclic D hF hE 0)).map (SimulatorModel.ofQ D hF hE) := by
  rw [minusToModel, MonoidHom.range_comp]
  exact inf_map_restrict _ _ _ _ _ (HNNExtension.of_injective _)
    (modelLetters_inf_fStage D hF hE) (minusToF_inf_fLetters D hF hE)

theorem fLetters_inf_plusBase : (fLetters D hF hE).range ⊓ (plusBase D hF hE).range =
    (coreCyclic D hF hE 1).map (SimulatorModel.ofF D hF hE) := by
  rw [plusBase, MonoidHom.range_comp]
  simp only [Subgroup.range_subtype]
  exact inf_map_restrict _ _ _ _ _ (HNNExtension.of_injective _)
    (fLetters_inf_core D hF hE) (base_inf_coreLetters D hF hE 1)

theorem qSubgroup_le_plusBase : SimulatorModel.qSubgroup D hF hE ≤ (plusBase D hF hE).range := by
  rw [plusBase, MonoidHom.range_comp]
  simp only [Subgroup.range_subtype]
  exact Subgroup.map_mono (CE_le_base D hF hE)

theorem plusToModel_inf_modelLetters :
    (modelLetters D hF hE).range ⊓ (plusToModel D hF hE).range =
      generatedWithStable (A := SimulatorModel.qSubgroup D hF hE) (B := SimulatorModel.qSubgroup D hF hE)
        (phi := MulEquiv.refl _) ((coreCyclic D hF hE 1).map (SimulatorModel.ofF D hF hE)) := by
  rw [modelLetters, AdjoinFree.range_hom, plusToModel, CentralizerMap.range_eq_generated,
    centralizer_intersection_of_le _ _ _ (qSubgroup_le_plusBase D hF hE), fLetters_inf_plusBase]

private theorem generated_closure_set {G : Type*} [Group G] (A B : Subgroup G) (φ : A ≃* B) (S : Set G) :
    generatedWithStable (A := A) (B := B) (phi := φ) (Subgroup.closure S) =
      Subgroup.closure ((HNNExtension.of (φ := φ) '' S) ∪ {HNNExtension.t}) := by
  simp only [generatedWithStable, MonoidHom.map_closure, Subgroup.closure_union, Subgroup.closure_eq]

theorem minus_model_intersection : (modelLetters D hF hE).range ⊓ (minusToModel D hF hE).range =
    Subgroup.closure ({SimulatorModel.s D hF hE 0, SimulatorModel.f D hF hE} : Set _) := by
  rw [minusToModel_inf_modelLetters, coreCyclic, generated_closure_set, MonoidHom.map_closure]
  simp only [Set.image_union, Set.image_singleton, SimulatorModel.s,
    SimulatorModel.f, SimulatorModel.fStable, SimulatorModel.lowToModel,
    SimulatorModel.coreToModel, SimulatorModel.ofF, SimulatorModel.ofQ, centralizerOf,
    centralizerStable, stable3]
  simp only [Set.singleton_union, MonoidHom.comp_apply]
  congr 1

theorem plus_model_intersection : (modelLetters D hF hE).range ⊓ (plusToModel D hF hE).range =
    Subgroup.closure ({SimulatorModel.s D hF hE 1, SimulatorModel.q D hF hE} : Set _) := by
  rw [plusToModel_inf_modelLetters, coreCyclic, MonoidHom.map_closure, generated_closure_set]
  simp only [Set.image_singleton, SimulatorModel.s,
    SimulatorModel.q, SimulatorModel.lowToModel, SimulatorModel.coreToModel,
    SimulatorModel.ofF, SimulatorModel.ofQ, centralizerOf, centralizerStable, stable3]
  simp only [Set.singleton_union, MonoidHom.comp_apply]
  congr 1

theorem modelLetters_map_coordinates : (modelLetters D hF hE).range.map (coordinates D hF hE) =
    (freeF4 D).range := by
  have hf : (SimulatorModel.f D hF hE)⁻¹ ∈ (modelLetters D hF hE).range :=
    (modelLetters D hF hE).range.inv_mem ⟨FreeGroup.of 2, modelLetters_f D hF hE⟩
  have hn := Subgroup.mem_normalizer_iff_map_conj_eq.mp ((modelLetters D hF hE).range.le_normalizer hf)
  change (modelLetters D hF hE).range.map (MulAut.conj (SimulatorModel.f D hF hE)⁻¹).toMonoidHom = _ at hn
  rw [coordinates, ← Subgroup.map_map, hn, ← MonoidHom.range_comp, fromModel_comp_modelLetters]

private theorem conjugate_pair_closure {G : Type*} [Group G] (s f : G) :
    Subgroup.closure ({f⁻¹ * s * f, f} : Set G) = Subgroup.closure ({s, f} : Set G) := by
  let S : Subgroup G := Subgroup.closure ({s, f} : Set G)
  let T : Subgroup G := Subgroup.closure ({f⁻¹ * s * f, f} : Set G)
  have hs : s ∈ S := Subgroup.subset_closure (by simp)
  have hf : f ∈ S := Subgroup.subset_closure (by simp)
  have hx : f⁻¹ * s * f ∈ T := Subgroup.subset_closure (by simp)
  have hf' : f ∈ T := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨S.mul_mem (S.mul_mem (S.inv_mem hf) hs) hf, hf⟩
  · rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, hf'⟩
    change s ∈ T
    have h := T.mul_mem (T.mul_mem hf' hx) (T.inv_mem hf')
    simpa [mul_assoc] using h

include hF hE

/-- The negative single-letter subgroup meets the free four-letter subgroup
exactly in the free subgroup on `s₁,f`. -/
theorem HMinus_inf_freeF4 : HMinus D ⊓ (freeF4 D).range =
    Subgroup.closure ({SimulatorRelations.s D 0, SimulatorRelations.f D} : Set _) := by
  rw [inf_comm, ← range_minusHom D hF hE, minusHom, MonoidHom.range_comp,
    ← modelLetters_map_coordinates D hF hE,
    ← Subgroup.map_inf _ _ _ (coordinates_injective D hF hE), minus_model_intersection,
    MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [coordinates_s, coordinates_f]
  exact conjugate_pair_closure _ _

/-- The positive single-letter subgroup meets the free four-letter subgroup
in `f⁻¹⟨s₂,q⟩f = ⟨x₂,q₀⟩`. -/
theorem HPlus_inf_freeF4 : HPlus D ⊓ (freeF4 D).range =
    Subgroup.closure ({x D 1, q0 D} : Set _) := by
  rw [inf_comm, ← range_plusHom D hF hE, plusHom, MonoidHom.range_comp,
    ← modelLetters_map_coordinates D hF hE,
    ← Subgroup.map_inf _ _ _ (coordinates_injective D hF hE), plus_model_intersection,
    MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [coordinates_s, coordinates_q]

end

end UniversalGroup.SimulatorSymmetry
