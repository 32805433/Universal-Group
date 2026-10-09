module

public import UniversalGroup.Host.EllAlgebra
public import UniversalGroup.Simulator.Centralizer
public import UniversalGroup.Host.InputAmalgam

@[expose] public section

/-!
The four grid generators are free. Killing `k` sends them to a free basis
of `F(s₁,s₂,f,q)`, so the proof does not require a recognition hypothesis.
-/

namespace UniversalGroup.SimulatorGrid

open PositiveEvaluation
variable (D : CodeWords)

def freeValues : Fin 4 → FreeGroup (Fin 4) :=
  ![FreeGroup.of 2,
    (FreeGroup.of 2)⁻¹ * FreeGroup.of 0 * FreeGroup.of 2,
    (FreeGroup.of 2)⁻¹ * FreeGroup.of 1 * FreeGroup.of 2,
    CodeSubgroups.positiveFour D.P * FreeGroup.of 3 * FreeGroup.of 2]

def changeBasis : FreeGroup (Fin 4) →* FreeGroup (Fin 4) := FreeGroup.lift (freeValues D)

def undoValues : Fin 4 → FreeGroup (Fin 4) :=
  let s : Fin 2 → FreeGroup (Fin 4) :=
    ![FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹,
      FreeGroup.of 0 * FreeGroup.of 2 * (FreeGroup.of 0)⁻¹]
  ![s 0, s 1, FreeGroup.of 0,
    (value s D.P)⁻¹ * FreeGroup.of 3 * (FreeGroup.of 0)⁻¹]

def undo : FreeGroup (Fin 4) →* FreeGroup (Fin 4) := FreeGroup.lift (undoValues D)

theorem undo_comp_changeBasis : (undo D).comp (changeBasis D) = MonoidHom.id _ := by
  have hp : undo D (CodeSubgroups.positiveFour D.P) =
      value ![FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹,
        FreeGroup.of 0 * FreeGroup.of 2 * (FreeGroup.of 0)⁻¹] D.P := by
    rw [CodeSubgroups.positiveFour, CodeSubgroups.map_positive]
    simp only [undo, FreeGroup.lift_apply_of, undoValues, Matrix.cons_val]
    unfold evalPositive value
    congr 2
    funext i
    fin_cases i <;> rfl
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · simp [changeBasis, freeValues, undo, undoValues, mul_assoc]
  · simp [changeBasis, freeValues, undo, undoValues, mul_assoc]
  · simp [changeBasis, freeValues, undo, undoValues, mul_assoc]
  · simp only [MonoidHom.comp_apply, changeBasis, FreeGroup.lift_apply_of]
    change undo D (CodeSubgroups.positiveFour D.P * FreeGroup.of 3 * FreeGroup.of 2) = _
    rw [map_mul, map_mul, hp]
    simp [undo, undoValues, mul_assoc]

theorem changeBasis_injective : Function.Injective (changeBasis D) := by
  intro x y h
  have h' := congrArg (undo D) h
  simpa only [← MonoidHom.comp_apply, undo_comp_changeBasis, MonoidHom.id_apply] using h'

def lift : FreeGroup (Fin 4) →* (simulatorK D).Group :=
  FreeGroup.lift (simulatorGridValues D)

@[simp] theorem lift_of (i : Fin 4) : lift D (FreeGroup.of i) = simulatorGridValues D i := by
  simp [lift]

theorem lift_range : (lift D).range = simulatorGrid D := by
  rw [lift, FreeGroup.range_lift_eq_closure]
  rfl

theorem retraction_grid (i : Fin 4) :
    simulatorRetraction D (simulatorGridValues D i) =
      SimulatorFreeLetters.freeF4 D (freeValues D i) := by
  have hi (x : (simulatorL D).Group) :
      simulatorRetraction D (simulatorInclusion D x) = x :=
    DFunLike.congr_fun (simulatorRetraction_comp_inclusion D) x
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [simulatorGridValues, simulatorRetraction, generators, freeValues,
      SimulatorRelations.f, Fin.append, Fin.addCases]
    rfl
  · change simulatorRetraction D (simulatorInclusion D
      ((simulatorL D).evalWord (simulatorLWords.x D j))) = _
    rw [hi]
    fin_cases j <;>
      simp [freeValues, CodeSubgroups.freeF4_positive,
        FP.evalWord, SimulatorWords.x, simulatorLWords, SimulatorRelations.f,
        SimulatorRelations.s, SimulatorRelations.q, SimulatorRelations.t, generators, mul_assoc]

theorem retraction_comp_lift :
    (simulatorRetraction D).comp (lift D) =
      (SimulatorFreeLetters.freeF4 D).comp (changeBasis D) := by
  apply FreeGroup.ext_hom
  intro i
  simp [changeBasis, retraction_grid]

theorem lift_injective (hF : ∀ i, ContainsBoth (D.F i))
    (hE : ∀ i, ContainsBoth (D.E i)) : Function.Injective (lift D) := by
  have h : Function.Injective ((SimulatorFreeLetters.freeF4 D).comp (changeBasis D)) :=
    (SimulatorFreeLetters.freeF4_injective D hF hE).comp (changeBasis_injective D)
  rw [← retraction_comp_lift] at h
  intro x y hxy
  exact h (congrArg (simulatorRetraction D) hxy)

theorem c_commute_x (i : Fin 3) :
    Commute (SimulatorRelations.c D)
      ((simulatorL D).evalWord (simulatorLWords.x D i)) := by
  have hp : Commute (SimulatorRelations.c D) (SimulatorRelations.positive D D.P) := by
    rw [EllAlgebra.positive_eq_value]
    exact value_commute _ _ (SimulatorRelations.c_s D) D.P
  fin_cases i
  · simpa [FP.evalWord, SimulatorWords.x, simulatorLWords, SimulatorRelations.c,
      SimulatorRelations.f, SimulatorRelations.s, generators, mul_assoc] using
      ((SimulatorRelations.c_f D).inv_right.mul_right (SimulatorRelations.c_s D 0)).mul_right
        (SimulatorRelations.c_f D)
  · simpa [FP.evalWord, SimulatorWords.x, simulatorLWords, SimulatorRelations.c,
      SimulatorRelations.f, SimulatorRelations.s, generators, mul_assoc] using
      ((SimulatorRelations.c_f D).inv_right.mul_right (SimulatorRelations.c_s D 1)).mul_right
        (SimulatorRelations.c_f D)
  · simpa [FP.evalWord, SimulatorWords.x, simulatorLWords, SimulatorRelations.c,
      SimulatorWords.positive, SimulatorRelations.positive, evalPositive,
      SimulatorRelations.s, SimulatorRelations.t, generators] using
      hp.mul_right (SimulatorRelations.c_t D)

theorem c_commute_values (i : Fin 4) :
    Commute (simulatorInclusion D (SimulatorRelations.c D)) (simulatorGridValues D i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hk := SimulatorCentralizer.inclusion_basis_commutes_k D 0
    change Commute (simulatorInclusion D (SimulatorRelations.c D))
      (generators (simulatorK D) 7) at hk
    have hf := (SimulatorRelations.c_f D).map (simulatorInclusion D)
    have hfeq : simulatorInclusion D (SimulatorRelations.f D) =
        generators (simulatorK D) 5 := by
      simp [SimulatorRelations.f, simulatorInclusion, generators]
    rw [hfeq] at hf
    exact (hk.inv_right.mul_right hf).mul_right hk
  · exact (c_commute_x D j).map (simulatorInclusion D)

theorem c_commute_grid (x : simulatorGrid D) :
    Commute (simulatorInclusion D (SimulatorRelations.c D)) (x : (simulatorK D).Group) := by
  have h := PositiveEvaluation.commute_closure (MonoidHom.id (simulatorK D).Group)
    (simulatorInclusion D (SimulatorRelations.c D)) (Set.range (simulatorGridValues D))
    (by rintro _ ⟨i, rfl⟩; exact c_commute_values D i) x.property
  exact h

end UniversalGroup.SimulatorGrid
