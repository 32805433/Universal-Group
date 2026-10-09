module

public import UniversalGroup.Simulator.Codes.Free
public import UniversalGroup.Simulator.FreeLetters

@[expose] public section

/-!
# The free basis of `A` and the displayed generators of `B`

The coded free-group calculations transport through the proved embedding
of `F(s₁,s₂,f,q)` into the literal simulator. The displayed maps use exactly
the basis order in `simulatorA` and `simulatorB`.
-/

namespace UniversalGroup.CodeSubgroups

noncomputable section

variable (D : CodeWords)

/-- The five displayed generators `ḡ₁,ḡ₂,x₁,x₂,x₃` of `A`. -/
def aValues : Fin 5 → (simulatorL D).Group := fun i =>
  (simulatorL D).evalWord
    (![simulatorLWords.positive (D.code 0), simulatorLWords.positive (D.code 1),
      simulatorLWords.x D 0, simulatorLWords.x D 1, simulatorLWords.x D 2] i)

/-- The four displayed generators `ḡ₁,ḡ₂,f,T` of `B`. -/
def bValues : Fin 4 → (simulatorL D).Group := fun i =>
  (simulatorL D).evalWord
    (![simulatorLWords.positive (D.code 0), simulatorLWords.positive (D.code 1),
      simulatorLWords.f, simulatorLWords.T D] i)

def aLift : FreeGroup (Fin 5) →* (simulatorL D).Group := FreeGroup.lift (aValues D)
def bLift : FreeGroup (Fin 4) →* (simulatorL D).Group := FreeGroup.lift (bValues D)

@[simp] theorem aLift_of (i : Fin 5) : aLift D (FreeGroup.of i) = aValues D i := by
  simp [aLift]

@[simp] theorem bLift_of (i : Fin 4) : bLift D (FreeGroup.of i) = bValues D i := by
  simp [bLift]

theorem aLift_range : (aLift D).range = simulatorA D := by
  rw [aLift, FreeGroup.range_lift_eq_closure]
  rfl

theorem bLift_range : (bLift D).range = simulatorB D := by
  rw [bLift, FreeGroup.range_lift_eq_closure]
  rfl

theorem freeF4_positive (w : PositiveWord) :
    SimulatorFreeLetters.freeF4 D (positiveFour w) =
      (simulatorL D).evalWord (simulatorLWords.positive w) := by
  rw [positiveFour, map_positive, SimulatorFreeLetters.freeF4_s1,
    SimulatorFreeLetters.freeF4_s2, SimulatorRelations.eval_positive]
  rfl

theorem freeF4_aFreeValues (i : Fin 5) :
    SimulatorFreeLetters.freeF4 D (aFreeValues D i) = aValues D i := by
  fin_cases i <;>
    simp [aFreeValues, aValues, freeF4_positive, SimulatorWords.x,
      FP.evalWord, simulatorLWords, SimulatorRelations.f, SimulatorRelations.s,
      SimulatorRelations.q, SimulatorRelations.t, generators, mul_assoc]

theorem freeF4_comp_aFreeLift :
    (SimulatorFreeLetters.freeF4 D).comp (aFreeLift D) = aLift D := by
  apply FreeGroup.ext_hom
  intro i
  simp [aFreeLift, freeF4_aFreeValues]

theorem aLift_injective_of_code_shape
    (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))
    (r : ℕ) (hcode : D.code = valievCode r) : Function.Injective (aLift D) := by
  rw [← freeF4_comp_aFreeLift]
  exact (SimulatorFreeLetters.freeF4_injective D hF hE).comp
    (aFreeLift_injective D r hcode)

/-- The displayed `A` basis is free for every actual recognition datum. -/
theorem aLift_injective (G : PreparedInput) (D : ValievDatum G) :
    Function.Injective (aLift D.toCodeWords) :=
  aLift_injective_of_code_shape D.toCodeWords D.F_support D.E_support D.r D.code_shape

end
end UniversalGroup.CodeSubgroups
