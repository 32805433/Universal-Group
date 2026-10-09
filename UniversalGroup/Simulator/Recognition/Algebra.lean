module

public import UniversalGroup.Host.EllAlgebra

@[expose] public section

/-!
# The algebraic inclusions of the recognition subgroup

Every displayed `Δ(w)` belongs to both `A` and `B`, for arbitrary codewords
and arbitrary positive words. These inclusions require neither recognition
nor the Valiev intersection theorem. They follow from explicit words in the
displayed generators of the two subgroups.
-/

namespace UniversalGroup.RecognitionAlgebra
noncomputable section

open PositiveEvaluation

variable (D : CodeWords)

/-- The expression for `Δ(w)` in the four displayed generators of `B`. -/
def bDeltaWord (w : PositiveWord) : FreeGroup (Fin 4) :=
  value ![FreeGroup.of 0, FreeGroup.of 1] w * FreeGroup.of 3 *
    (FreeGroup.of 2)⁻¹ * (value ![FreeGroup.of 0, FreeGroup.of 1] w)⁻¹ * FreeGroup.of 2

/-- Concatenation of codewords is multiplication of the two code generators. -/
theorem bLift_bar (w : PositiveWord) :
    CodeSubgroups.bLift D (value ![FreeGroup.of 0, FreeGroup.of 1] w) =
      SimulatorRelations.positive D (w.flatMap D.code) := by
  have hv : (fun i : Fin 2 => CodeSubgroups.bLift D (![FreeGroup.of 0, FreeGroup.of 1] i)) =
      (fun i => SimulatorRelations.positive D (D.code i)) := by
    funext i
    fin_cases i <;> simp [CodeSubgroups.bValues]
  rw [map_value, hv]
  simp only [EllAlgebra.positive_eq_value, value_flatMap]

/-- The explicit `B` word evaluates to the literal simulator element. -/
theorem bLift_bDeltaWord (w : PositiveWord) :
    CodeSubgroups.bLift D (bDeltaWord w) = simulatorDelta D w := by
  simp only [bDeltaWord, map_mul, map_inv, bLift_bar, CodeSubgroups.bLift_of]
  simp [CodeSubgroups.bValues, simulatorDelta, SimulatorWords.delta,
    SimulatorWords.bar, FP.evalWord,
    SimulatorRelations.positive, SimulatorWords.positive, simulatorLWords,
    SimulatorRelations.s, evalPositive, generators, mul_assoc]

/-- All recognition elements lie in `A`, independently of whether the
corresponding positive word is recognized. -/
theorem delta_mem_A (w : PositiveWord) : simulatorDelta D w ∈ simulatorA D := by
  rw [← CodeSubgroups.aLift_range]
  exact ⟨EllAlgebra.deltaWord D w, EllAlgebra.aLift_deltaWord D w⟩

/-- All recognition elements lie in `B`, with no recognition hypotheses. -/
theorem delta_mem_B (w : PositiveWord) : simulatorDelta D w ∈ simulatorB D := by
  rw [← CodeSubgroups.bLift_range]
  exact ⟨bDeltaWord w, bLift_bDeltaWord D w⟩

/-- The generated recognition subgroup is contained in `A`. -/
theorem recognition_le_A (G : PreparedInput) : recognitionSubgroup G D ≤ simulatorA D := by
  rw [recognitionSubgroup, Subgroup.closure_le]
  rintro x ⟨w, _, rfl⟩
  exact delta_mem_A D w

/-- The generated recognition subgroup is contained in `B`. -/
theorem recognition_le_B (G : PreparedInput) : recognitionSubgroup G D ≤ simulatorB D := by
  rw [recognitionSubgroup, Subgroup.closure_le]
  rintro x ⟨w, _, rfl⟩
  exact delta_mem_B D w

end
end UniversalGroup.RecognitionAlgebra
