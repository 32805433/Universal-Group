module

public import UniversalGroup.Simulator.Symmetry.Intersections
public import UniversalGroup.Simulator.Codes.RightIntersection
public import UniversalGroup.Host.EllStage

@[expose] public section

/-!
The coded subgroup, the conjugated amalgam defining the `ell` domain, and
its free grid each meet the two single-letter subgroups in exactly the
specified cyclic subgroup.
-/

namespace UniversalGroup.SimulatorSymmetry

noncomputable section
open SimulatorFreeLetters CodeSubgroups HNNLemmas

variable (D : CodeWords)

private theorem a_map_freeF4 : (aFreeLift D).range.map (freeF4 D) = simulatorA D := by
  rw [← MonoidHom.range_comp, freeF4_comp_aFreeLift, aLift_range]

private theorem left_map_freeF4 : leftAmbient.map (freeF4 D) =
    Subgroup.closure ({SimulatorRelations.s D 0, SimulatorRelations.f D} : Set _) := by
  simp [leftAmbient, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]

private theorem right_map_freeF4 : rightAmbient.map (freeF4 D) =
    Subgroup.closure ({x D 1, q0 D} : Set _) := by
  simp [rightAmbient, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, x, q0]

theorem A_le_freeF4 : simulatorA D ≤ (freeF4 D).range := by
  rw [← a_map_freeF4]
  exact Subgroup.map_le_range _ _

private theorem inf_restrict {α : Type*} [Group α] (A B C : Subgroup α) (hAC : A ≤ C) :
    A ⊓ B = A ⊓ (B ⊓ C) := by
  ext x
  exact ⟨fun h => ⟨h.1, h.2, hAC h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩

theorem A_inf_HMinus (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))
    (r : ℕ) (hcode : D.code = valievCode r) :
    simulatorA D ⊓ HMinus D = Subgroup.closure ({x D 0} : Set _) := by
  rw [inf_restrict _ _ _ (A_le_freeF4 D), HMinus_inf_freeF4 D hF hE,
    ← a_map_freeF4 D, ← left_map_freeF4 D,
    ← Subgroup.map_inf _ _ _ (freeF4_injective D hF hE),
    aFree_inter_left D r hcode, MonoidHom.map_closure]
  simp [aFreeValues, x]

theorem A_inf_HPlus (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))
    (r : ℕ) (hcode : D.code = valievCode r) :
    simulatorA D ⊓ HPlus D = Subgroup.closure ({x D 1} : Set _) := by
  rw [inf_restrict _ _ _ (A_le_freeF4 D), HPlus_inf_freeF4 D hF hE,
    ← a_map_freeF4 D, ← right_map_freeF4 D,
    ← Subgroup.map_inf _ _ _ (freeF4_injective D hF hE),
    aFree_inter_right D r hcode, MonoidHom.map_closure]
  simp [aFreeValues, x]

/-- The two single-letter subgroups regarded as subgroups of the literal `K`. -/
def HMinusK : Subgroup (simulatorK D).Group := (HMinus D).map (simulatorInclusion D)
def HPlusK : Subgroup (simulatorK D).Group := (HPlus D).map (simulatorInclusion D)
def xK (i : Fin 2) : (simulatorK D).Group := simulatorInclusion D (x D i)

variable (G : PreparedInput) (V : ValievDatum G)
  (hintersections : ValievIntersections G V)

/-- The conjugated amalgam that forms the `ell` domain meets `L` exactly in `A`. -/
theorem domain_inf_L : (EllStage.toK G V hintersections).range ⊓
    (simulatorInclusion V.toCodeWords).range =
      (simulatorA V.toCodeWords).map (simulatorInclusion V.toCodeWords) := by
  apply le_antisymm
  · rintro y ⟨⟨w, rfl⟩, z, hz⟩
    have hw : ConjugatedAmalgam.toHNN _ _ _ _ _ _ (EllStage.common_le_D G V hintersections) w ∈
        (centralizerOf (simulatorD V.toCodeWords)).range := by
      refine ⟨z, ?_⟩
      have h := congrArg (SimulatorCentralizer.equiv V.toCodeWords) hz
      simpa [EllStage.toK] using h
    obtain ⟨a, rfl⟩ := ConjugatedAmalgam.toHNN_preimage_base _ _ _ _ _ _ _
      hintersections.1 hintersections.2 w hw
    exact ⟨a, a.property, (EllStage.toK_inA G V hintersections a).symm⟩
  · rintro y ⟨a, ha, rfl⟩
    exact ⟨⟨EllStage.inA G V hintersections ⟨a, ha⟩,
      EllStage.toK_inA G V hintersections _⟩, ⟨a, rfl⟩⟩

private theorem inf_restrict_left {α : Type*} [Group α] (A B C : Subgroup α) (hBC : B ≤ C) :
    A ⊓ B = (A ⊓ C) ⊓ B := by
  ext x
  exact ⟨fun h => ⟨⟨h.1, hBC h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem domain_inf_mapped (H : Subgroup (simulatorL V.toCodeWords).Group) :
    (EllStage.toK G V hintersections).range ⊓ H.map (simulatorInclusion V.toCodeWords) =
      (simulatorA V.toCodeWords ⊓ H).map (simulatorInclusion V.toCodeWords) := by
  rw [inf_restrict_left _ _ _ (Subgroup.map_le_range _ _), domain_inf_L,
    Subgroup.map_inf _ _ _ (simulatorInclusion_injective V.toCodeWords)]

theorem domain_inf_HMinusK :
    (EllStage.toK G V hintersections).range ⊓ HMinusK V.toCodeWords =
      Subgroup.closure ({xK V.toCodeWords 0} : Set _) := by
  rw [HMinusK, domain_inf_mapped,
    A_inf_HMinus V.toCodeWords V.F_support V.E_support V.r V.code_shape,
    MonoidHom.map_closure, Set.image_singleton]
  rfl

theorem domain_inf_HPlusK :
    (EllStage.toK G V hintersections).range ⊓ HPlusK V.toCodeWords =
      Subgroup.closure ({xK V.toCodeWords 1} : Set _) := by
  rw [HPlusK, domain_inf_mapped,
    A_inf_HPlus V.toCodeWords V.F_support V.E_support V.r V.code_shape,
    MonoidHom.map_closure, Set.image_singleton]
  rfl

theorem xK_eq_gridValue (i : Fin 2) : xK D i = simulatorGridValues D i.castSucc.succ := by
  fin_cases i
  · change xK D 0 = simulatorGridValues D 1
    simp [xK, x, simulatorGridValues, SimulatorWords.x, FP.evalWord, simulatorLWords,
      SimulatorRelations.f, SimulatorRelations.s, generators, mul_assoc]
  · change xK D 1 = simulatorGridValues D 2
    rw [simulatorGridValues, show (2 : Fin 4) = (1 : Fin 3).succ from rfl, Fin.cons_succ]
    simp [xK, x, SimulatorWords.x, FP.evalWord, simulatorLWords,
      SimulatorRelations.f, SimulatorRelations.s, generators, mul_assoc]

theorem xK_mem_grid (i : Fin 2) : xK D i ∈ simulatorGrid D := by
  rw [xK_eq_gridValue]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem x_mem_HMinus : x D 0 ∈ HMinus D := by
  exact Subgroup.subset_closure ⟨4, rfl⟩

theorem x_mem_HPlus : x D 1 ∈ HPlus D := by
  exact Subgroup.subset_closure ⟨4, rfl⟩

include hintersections in
/-- Exact negative single-letter intersection with the four-generator grid. -/
theorem grid_inf_HMinusK : simulatorGrid V.toCodeWords ⊓ HMinusK V.toCodeWords =
    Subgroup.closure ({xK V.toCodeWords 0} : Set _) := by
  apply le_antisymm
  · rw [← domain_inf_HMinusK G V hintersections]
    exact inf_le_inf (EllStage.grid_le_domain_range G V hintersections) le_rfl
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact ⟨xK_mem_grid V.toCodeWords 0,
      ⟨x V.toCodeWords 0, x_mem_HMinus V.toCodeWords, rfl⟩⟩

include hintersections in
/-- Exact positive single-letter intersection with the four-generator grid. -/
theorem grid_inf_HPlusK : simulatorGrid V.toCodeWords ⊓ HPlusK V.toCodeWords =
    Subgroup.closure ({xK V.toCodeWords 1} : Set _) := by
  apply le_antisymm
  · rw [← domain_inf_HPlusK G V hintersections]
    exact inf_le_inf (EllStage.grid_le_domain_range G V hintersections) le_rfl
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact ⟨xK_mem_grid V.toCodeWords 1,
      ⟨x V.toCodeWords 1, x_mem_HPlus V.toCodeWords, rfl⟩⟩

def minusMapK : HMinus D ≃* HMinusK D :=
  Subgroup.equivMapOfInjective _ _ (simulatorInclusion_injective D)
def plusMapK : HPlus D ≃* HPlusK D :=
  Subgroup.equivMapOfInjective _ _ (simulatorInclusion_injective D)

@[simp] theorem minusMapK_val (a : HMinus D) :
    (minusMapK D a : (simulatorK D).Group) = simulatorInclusion D a := rfl
@[simp] theorem plusMapK_val (a : HPlus D) :
    (plusMapK D a : (simulatorK D).Group) = simulatorInclusion D a := rfl

def minusElementK (i : Fin 5) : HMinusK D := minusMapK D (minusElement D i)
def plusElementK (i : Fin 5) : HPlusK D := plusMapK D (plusElement D i)

@[simp] theorem minusElementK_val (i : Fin 5) :
    (minusElementK D i : (simulatorK D).Group) = simulatorInclusion D (minusValues D i) := rfl
@[simp] theorem plusElementK_val (i : Fin 5) :
    (plusElementK D i : (simulatorK D).Group) = simulatorInclusion D (plusValues D i) := rfl

variable (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

/-- The single-letter symmetry regarded inside the literal `K` presentation. -/
def equivK : HMinusK D ≃* HPlusK D :=
  (minusMapK D).symm.trans ((equiv D hF hE).trans (plusMapK D))

@[simp] theorem equivK_minusMap (a : HMinus D) :
    equivK D hF hE (minusMapK D a) = plusMapK D (equiv D hF hE a) := by
  simp [equivK]

@[simp] theorem equivK_x1 : equivK D hF hE (minusElementK D 4) = (plusElementK D 4)⁻¹ := by
  simp [minusElementK, plusElementK]

end
end UniversalGroup.SimulatorSymmetry
