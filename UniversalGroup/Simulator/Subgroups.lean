module

public import UniversalGroup.Simulator.Model
public import UniversalGroup.Simulator.Centralizer
public import UniversalGroup.Simulator.Core.FreeSubgroups

@[expose] public section

/-!
# The simulator's free `c,d` pair and source commutations

The faithful simulator model carries the core's free pair `(c,d)` into the
literal presentations `L` and `K`. Its image commutes with the subgroup
parametrized by `(f,k)`. These are the simulator inputs to the later
`F(c,d) × F(f,k,h²)` embedding. Only both-letter support of the three rule
words is needed for the pair's injectivity.
-/

namespace UniversalGroup.SimulatorSubgroups

noncomputable section

variable (D : CodeWords)

/-- The canonical pair `c,d` in the seven-generator presentation. -/
def pairD : FreeGroup (Fin 2) →* (simulatorL D).Group :=
  FreeGroup.lift ![generators (simulatorL D) 0, generators (simulatorL D) 1]

@[simp] theorem pairD_c : pairD D (FreeGroup.of 0) = generators (simulatorL D) 0 := by
  simp [pairD]

@[simp] theorem pairD_d : pairD D (FreeGroup.of 1) = generators (simulatorL D) 1 := by
  simp [pairD]

variable (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

theorem fromCore_comp_pairD :
    (SimulatorModel.fromCore D hF hE).comp
      (CoreFreeSubgroups.pairD (D.supportedRules hF hE)) = pairD D := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · simp only [MonoidHom.comp_apply]
    exact SimulatorModel.fromCore_c D hF hE
  · simp only [MonoidHom.comp_apply]
    exact SimulatorModel.fromCore_d D hF hE

include hF hE in
theorem pairD_injective : Function.Injective (pairD D) := by
  rw [← fromCore_comp_pairD D hF hE]
  exact (SimulatorModel.fromCore_injective D hF hE).comp
    (CoreFreeSubgroups.pairD_injective (D.supportedRules hF hE))

/-- The canonical `c,d` pair in the eight-generator simulator. -/
def kPairD : FreeGroup (Fin 2) →* (simulatorK D).Group :=
  FreeGroup.lift ![generators (simulatorK D) 0, generators (simulatorK D) 1]

@[simp] theorem kPairD_c : kPairD D (FreeGroup.of 0) = generators (simulatorK D) 0 := by
  simp [kPairD]

@[simp] theorem kPairD_d : kPairD D (FreeGroup.of 1) = generators (simulatorK D) 1 := by
  simp [kPairD]

theorem inclusion_comp_pairD :
    (simulatorInclusion D).comp (pairD D) = kPairD D := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [pairD, kPairD, simulatorInclusion, generators]

include hF hE in
theorem kPairD_injective : Function.Injective (kPairD D) := by
  rw [← inclusion_comp_pairD D]
  exact (simulatorInclusion_injective D).comp (pairD_injective D hF hE)

private theorem commute_free_lifts {G : Type*} [Group G]
    {α β : Type*} (x : α → G) (y : β → G)
    (h : ∀ i j, Commute (x i) (y j)) (u : FreeGroup α) (v : FreeGroup β) :
    Commute (FreeGroup.lift x u) (FreeGroup.lift y v) := by
  have hgen (i : α) (w : FreeGroup β) : Commute (x i) (FreeGroup.lift y w) := by
    induction w using FreeGroup.induction_on with
    | one => simp
    | of j => simpa using h i j
    | inv_of j hj => simpa only [map_inv] using hj.inv_right
    | mul w z hw hz => simpa only [map_mul] using hw.mul_right hz
  induction u using FreeGroup.induction_on with
  | one => simp
  | of i => simpa using hgen i v
  | inv_of i hi => simpa only [map_inv] using hi.inv_left
  | mul w z hw hz => simpa only [map_mul] using hw.mul_left hz

/-- Words in `c,d` commute with words in `f,k`. -/
theorem source_commute (u v : FreeGroup (Fin 2)) :
    Commute (kPairD D u) (SimulatorCentralizer.fk D v) := by
  apply commute_free_lifts
  intro i j
  have hcf : Commute (generators (simulatorK D) 0) (generators (simulatorK D) 5) := by
    simpa [simulatorInclusion, SimulatorRelations.c, SimulatorRelations.f, generators] using
      (SimulatorRelations.c_f D).map (simulatorInclusion D)
  have hdf : Commute (generators (simulatorK D) 1) (generators (simulatorK D) 5) := by
    simpa [simulatorInclusion, SimulatorRelations.d, SimulatorRelations.f, generators] using
      (SimulatorRelations.d_f D).map (simulatorInclusion D)
  have hck : Commute (generators (simulatorK D) 0) (generators (simulatorK D) 7) := by
    simpa [FP.evalWord, simulatorLWords, simulatorInclusion, generators] using
      SimulatorCentralizer.inclusion_basis_commutes_k D 0
  have hdk : Commute (generators (simulatorK D) 1) (generators (simulatorK D) 7) := by
    simpa [FP.evalWord, simulatorLWords, simulatorInclusion, generators] using
      SimulatorCentralizer.inclusion_basis_commutes_k D 1
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact hcf
  · exact hck
  · exact hdf
  · exact hdk

end
end UniversalGroup.SimulatorSubgroups
