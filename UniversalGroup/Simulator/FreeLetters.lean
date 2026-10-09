module

public import UniversalGroup.Simulator.Model
public import UniversalGroup.Simulator.Core.FreeSubgroups
public import UniversalGroup.Foundations.HNN.AdjoinFree

@[expose] public section

/-!
# The four free simulator letters

The letters `s₁,s₂,f,q` freely generate a rank-four subgroup in the literal
simulator. The comparison with the model transports the free-letter maps
used by the code-subgroup and recognition proofs.
-/

namespace UniversalGroup.SimulatorFreeLetters

open HNNLemmas BorisovCStage BorisovHNNModel

noncomputable section

variable (D : CodeWords) (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

def lowLetters : FreeGroup (Fin 2) →* Gamma3 :=
  FreeGroup.lift ![s1_3, s2_3]

theorem projection_lowLetters (w : FreeGroup (Fin 2)) :
    stableProjection3 (lowLetters w) = w := by
  have h : stableProjection3.comp lowLetters = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [lowLetters]
  exact DFunLike.congr_fun h w

theorem lowLetters_injective : Function.Injective lowLetters :=
  Function.LeftInverse.injective projection_lowLetters

def coreLetters : FreeGroup (Fin 2) →* SimulatorModel.Core D hF hE :=
  (SimulatorModel.coreOf D hF hE).comp lowLetters

theorem coreLetters_injective : Function.Injective (coreLetters D hF hE) :=
  (BorisovCStage.of3_injective _ _).comp lowLetters_injective

private def coreGrid : Subgroup (SimulatorModel.Core D hF hE) :=
  generatedWithStable (A := U (SimulatorModel.rules D hF hE))
    (B := V (SimulatorModel.rules D hF hE))
    (phi := cEquiv (SimulatorModel.rules D hF hE) (SimulatorModel.free D hF hE)) DE3

private theorem coreGrid_inf_low : coreGrid D hF hE ⊓ (SimulatorModel.coreOf D hF hE).range =
    DE3.map (SimulatorModel.coreOf D hF hE) :=
  generatedWithStable_inf_base DE3
    (CoreFreeSubgroups.cEquiv_mem_DE3_iff (SimulatorModel.rules D hF hE))

private theorem coreLetters_inf_coreGrid : (coreLetters D hF hE).range ⊓ coreGrid D hF hE = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨w, rfl⟩, hx⟩
  have hm : coreLetters D hF hE w ∈ coreGrid D hF hE ⊓
      (SimulatorModel.coreOf D hF hE).range := ⟨hx, ⟨lowLetters w, rfl⟩⟩
  rw [coreGrid_inf_low] at hm
  rcases hm with ⟨y, hy, heq⟩
  have hyw : y = lowLetters w := (BorisovCStage.of3_injective _ _) heq
  have hp : stableProjection3 (lowLetters w) = 1 := DE3_le_projection_ker (hyw ▸ hy)
  rw [projection_lowLetters] at hp
  simp [hp]

private theorem c_mem_coreGrid : SimulatorModel.coreC D hF hE ∈ coreGrid D hF hE := by
  apply (coreGrid D hF hE).inv_mem
  exact Subgroup.subset_closure (Or.inr rfl)

private theorem d_mem_coreGrid : SimulatorModel.coreOf D hF hE d3 ∈ coreGrid D hF hE := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨d3, Subgroup.subset_closure (by simp), rfl⟩

private theorem e_mem_coreGrid : SimulatorModel.coreOf D hF hE e3 ∈ coreGrid D hF hE := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨e3, Subgroup.subset_closure (by simp), rfl⟩

private theorem CD_le_coreGrid : SimulatorModel.CD D hF hE ≤ coreGrid D hF hE := by
  rw [SimulatorModel.CD, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact c_mem_coreGrid D hF hE
  · exact d_mem_coreGrid D hF hE

private theorem CE_le_coreGrid : SimulatorModel.CE D hF hE ≤ coreGrid D hF hE := by
  rw [SimulatorModel.CE, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact c_mem_coreGrid D hF hE
  · exact e_mem_coreGrid D hF hE

theorem coreLetters_inf_CD : (coreLetters D hF hE).range ⊓ SimulatorModel.CD D hF hE = ⊥ := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf_left _ (CD_le_coreGrid D hF hE)).trans (le_of_eq (coreLetters_inf_coreGrid D hF hE))

theorem coreLetters_inf_CE : (coreLetters D hF hE).range ⊓ SimulatorModel.CE D hF hE = ⊥ := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf_left _ (CE_le_coreGrid D hF hE)).trans (le_of_eq (coreLetters_inf_coreGrid D hF hE))

def fLetters : FreeGroup (Fin 3) →* SimulatorModel.FStage D hF hE :=
  AdjoinFree.hom (SimulatorModel.CD D hF hE) (coreLetters D hF hE)

theorem fLetters_injective : Function.Injective (fLetters D hF hE) :=
  AdjoinFree.hom_injective _ _ (coreLetters_injective D hF hE) (coreLetters_inf_CD D hF hE)

theorem fLetters_inf_core : (fLetters D hF hE).range ⊓ (SimulatorModel.ofF D hF hE).range =
    (coreLetters D hF hE).range.map (SimulatorModel.ofF D hF hE) :=
  AdjoinFree.range_hom_inf_base _ _

theorem fLetters_inf_qSubgroup :
    (fLetters D hF hE).range ⊓ SimulatorModel.qSubgroup D hF hE = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨hx, y, hy, rfl⟩
  have hm : SimulatorModel.ofF D hF hE y ∈ (fLetters D hF hE).range ⊓
      (SimulatorModel.ofF D hF hE).range := ⟨hx, ⟨y, rfl⟩⟩
  rw [fLetters_inf_core] at hm
  rcases hm with ⟨z, hz, hzy⟩
  have h : z = y := (HNNExtension.of_injective _) hzy
  have hy1 : y ∈ (⊥ : Subgroup (SimulatorModel.Core D hF hE)) := by
    rw [← coreLetters_inf_CE D hF hE]
    exact ⟨h ▸ hz, hy⟩
  have hy' : y = 1 := hy1
  simp [hy']

def modelLetters : FreeGroup (Fin 4) →* SimulatorModel.Model D hF hE :=
  AdjoinFree.hom (SimulatorModel.qSubgroup D hF hE) (fLetters D hF hE)

@[simp] theorem modelLetters_s1 : modelLetters D hF hE (FreeGroup.of 0) = SimulatorModel.s D hF hE 0 := by
  change AdjoinFree.hom _ _ (FreeGroup.of (0 : Fin 3).castSucc) = _
  rw [AdjoinFree.hom_old]
  change SimulatorModel.ofQ D hF hE (AdjoinFree.hom _ _ (FreeGroup.of (0 : Fin 2).castSucc)) = _
  rw [AdjoinFree.hom_old]
  simp [coreLetters, lowLetters, SimulatorModel.s, SimulatorModel.lowToModel,
    SimulatorModel.coreToModel, SimulatorModel.ofF, SimulatorModel.ofQ]

@[simp] theorem modelLetters_s2 : modelLetters D hF hE (FreeGroup.of 1) = SimulatorModel.s D hF hE 1 := by
  change AdjoinFree.hom _ _ (FreeGroup.of (1 : Fin 3).castSucc) = _
  rw [AdjoinFree.hom_old]
  change SimulatorModel.ofQ D hF hE (AdjoinFree.hom _ _ (FreeGroup.of (1 : Fin 2).castSucc)) = _
  rw [AdjoinFree.hom_old]
  simp [coreLetters, lowLetters, SimulatorModel.s, SimulatorModel.lowToModel,
    SimulatorModel.coreToModel, SimulatorModel.ofF, SimulatorModel.ofQ]

@[simp] theorem modelLetters_f : modelLetters D hF hE (FreeGroup.of 2) = SimulatorModel.f D hF hE := by
  change AdjoinFree.hom _ _ (FreeGroup.of (2 : Fin 3).castSucc) = _
  rw [AdjoinFree.hom_old]
  change SimulatorModel.ofQ D hF hE (AdjoinFree.hom _ _ (FreeGroup.of (Fin.last 2))) = _
  rw [AdjoinFree.hom_last]
  rfl

@[simp] theorem modelLetters_q : modelLetters D hF hE (FreeGroup.of 3) = SimulatorModel.q D hF hE := by
  change AdjoinFree.hom _ _ (FreeGroup.of (Fin.last 3)) = _
  rw [AdjoinFree.hom_last]
  rfl

theorem modelLetters_injective : Function.Injective (modelLetters D hF hE) :=
  AdjoinFree.hom_injective _ _ (fLetters_injective D hF hE) (fLetters_inf_qSubgroup D hF hE)

theorem modelLetters_inf_fStage : (modelLetters D hF hE).range ⊓ (SimulatorModel.ofQ D hF hE).range =
    (fLetters D hF hE).range.map (SimulatorModel.ofQ D hF hE) :=
  AdjoinFree.range_hom_inf_base _ _

/-- The four literal simulator letters, in order `s₁,s₂,f,q=t*f⁻¹`. -/
def freeF4 : FreeGroup (Fin 4) →* (simulatorL D).Group :=
  FreeGroup.lift ![SimulatorRelations.s D 0, SimulatorRelations.s D 1,
    SimulatorRelations.f D, SimulatorRelations.q D]

/-- The free subgroup on the original two simulator letters. -/
def freeS : FreeGroup (Fin 2) →* (simulatorL D).Group :=
  FreeGroup.lift ![SimulatorRelations.s D 0, SimulatorRelations.s D 1]

@[simp] theorem freeF4_s1 : freeF4 D (FreeGroup.of 0) = SimulatorRelations.s D 0 := by
  simp [freeF4]

@[simp] theorem freeF4_s2 : freeF4 D (FreeGroup.of 1) = SimulatorRelations.s D 1 := by
  simp [freeF4]

@[simp] theorem freeF4_f : freeF4 D (FreeGroup.of 2) = SimulatorRelations.f D := by
  simp [freeF4]

@[simp] theorem freeF4_q : freeF4 D (FreeGroup.of 3) = SimulatorRelations.q D := by
  simp [freeF4]

theorem fromModel_comp_modelLetters : (SimulatorModel.fromModel D hF hE).comp
    (modelLetters D hF hE) = freeF4 D := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp [freeF4, SimulatorModel.s, SimulatorModel.lowToModel, SimulatorModel.f]

theorem fromCore_comp_coreLetters : (SimulatorModel.fromCore D hF hE).comp
    (coreLetters D hF hE) = freeS D := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [coreLetters, lowLetters, freeS]

include hF hE in
/-- The four named letters freely generate a rank-four subgroup of `L`. -/
theorem freeF4_injective : Function.Injective (freeF4 D) := by
  rw [← fromModel_comp_modelLetters D hF hE]
  exact (SimulatorModel.fromModel_injective D hF hE).comp (modelLetters_injective D hF hE)

end

end UniversalGroup.SimulatorFreeLetters
