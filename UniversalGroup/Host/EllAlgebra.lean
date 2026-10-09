module

public import UniversalGroup.Host.PositiveEvaluation
public import UniversalGroup.Simulator.Codes.Bases

@[expose] public section

/-!
The algebra of the diagonal attaching map for `ell`.  In particular, monoid
recognition is used only in the forward direction, to evaluate a recognized
word in the input group.  No embedding theorem for the final host is used.
-/

namespace UniversalGroup

namespace PositiveEvaluation

@[simp] theorem value_append {H : Type*} [Group H] (v : Fin 2 → H)
    (w w' : PositiveWord) : value v (w ++ w') = value v w * value v w' := by
  simp [value, List.prod_append]

@[simp] theorem map_value {H K : Type*} [Group H] [Group K] (f : H →* K)
    (v : Fin 2 → H) (w : PositiveWord) :
    f (value v w) = value (fun i => f (v i)) w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih]

theorem value_flatMap {H : Type*} [Group H] (v : Fin 2 → H)
    (code : Fin 2 → PositiveWord) (w : PositiveWord) :
    value v (w.flatMap code) = value (fun i => value v (code i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih]

theorem eval_signedPositive {H : Type*} [Group H] (v : Fin 2 → H)
    (w : PositiveWord) : Word.eval v (signedPositive w) = value v w := by
  induction w with
  | nil => simp [Word.eval, signedPositive, value]
  | cons i w ih =>
    change Word.eval v (Word.generator i ++ signedPositive w) = _
    simp [ih]

theorem value_eq_of_positiveEq {H : Type*} [Group H] (v : Fin 2 → H)
    (rules : Set (PositiveWord × PositiveWord))
    (hrules : ∀ p ∈ rules, value v p.1 = value v p.2)
    {w w' : PositiveWord} (h : PositiveEq rules w w') : value v w = value v w' := by
  induction h with
  | refl => rfl
  | @tail w' w'' h hstep ih =>
    apply ih.trans
    rcases hstep with ⟨l, r, x, y, hxy, hstep⟩
    have heq := hrules (x, y) hxy
    rcases hstep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [heq]

end PositiveEvaluation

theorem PreparedInput.recognized_value_eq_one (G : PreparedInput)
    (w : PositiveWord) (hw : PositiveEq G.monoidRules w []) :
    PositiveEvaluation.value (generators G.presentation) w = 1 := by
  apply (PositiveEvaluation.value_eq_of_positiveEq _ G.monoidRules ?_ hw).trans
  · rfl
  · rintro _ ⟨i, rfl⟩
    rw [PositiveEvaluation.value_nil, ← PositiveEvaluation.eval_signedPositive]
    exact G.presentation.relator_eq_one i

namespace EllAlgebra

open PositiveEvaluation

theorem positive_eq_value (D : CodeWords) (w : PositiveWord) :
    SimulatorRelations.positive D w = value (SimulatorRelations.s D) w := by
  unfold SimulatorRelations.positive evalPositive value
  congr 2
  funext i
  fin_cases i <;> rfl

theorem aValues_eq (D : CodeWords) : CodeSubgroups.aValues D =
    ![SimulatorRelations.positive D (D.code 0),
      SimulatorRelations.positive D (D.code 1),
      (SimulatorRelations.f D)⁻¹ * SimulatorRelations.s D 0 * SimulatorRelations.f D,
      (SimulatorRelations.f D)⁻¹ * SimulatorRelations.s D 1 * SimulatorRelations.f D,
      SimulatorRelations.positive D D.P * SimulatorRelations.t D] := by
  funext i
  fin_cases i <;>
    simp [CodeSubgroups.aValues, SimulatorWords.positive,
      SimulatorWords.x, FP.evalWord, simulatorLWords,
      SimulatorRelations.positive, evalPositive, SimulatorRelations.s,
      SimulatorRelations.f, SimulatorRelations.t, generators, mul_assoc]

/-- The free word in the five displayed generators of `A` representing
the recognized element `delta(w)`. -/
def deltaWord (D : CodeWords) (w : PositiveWord) : FreeGroup (Fin 5) :=
  value ![FreeGroup.of 0, FreeGroup.of 1] w * FreeGroup.of 4 *
    (value ![FreeGroup.of 2, FreeGroup.of 3] (w.flatMap D.code ++ D.P))⁻¹

theorem aLift_deltaWord (D : CodeWords) (w : PositiveWord) :
    CodeSubgroups.aLift D (deltaWord D w) = simulatorDelta D w := by
  have hx (v : PositiveWord) :
      value ![CodeSubgroups.aValues D 2, CodeSubgroups.aValues D 3] v =
        (SimulatorRelations.f D)⁻¹ * SimulatorRelations.positive D v *
          SimulatorRelations.f D := by
    simp only [aValues_eq, Matrix.cons_val]
    rw [positive_eq_value]
    have heq : ![(SimulatorRelations.f D)⁻¹ * SimulatorRelations.s D 0 * SimulatorRelations.f D,
        (SimulatorRelations.f D)⁻¹ * SimulatorRelations.s D 1 * SimulatorRelations.f D] =
        (fun i => (SimulatorRelations.f D)⁻¹ * SimulatorRelations.s D i *
          ((SimulatorRelations.f D)⁻¹)⁻¹) := by
      funext i
      fin_cases i <;> simp
    rw [heq, value_conj]
    simp
  have hc : (fun i : Fin 2 => CodeSubgroups.aLift D
      (![FreeGroup.of 0, FreeGroup.of 1] i)) =
      (fun i => SimulatorRelations.positive D (D.code i)) := by
    funext i
    fin_cases i <;> simp [aValues_eq]
  have hxx : (fun i : Fin 2 => CodeSubgroups.aLift D
      (![FreeGroup.of 2, FreeGroup.of 3] i)) =
      ![CodeSubgroups.aValues D 2, CodeSubgroups.aValues D 3] := by
    funext i
    fin_cases i <;> simp
  unfold deltaWord
  simp only [map_mul, map_inv, map_value, hc, hxx, CodeSubgroups.aLift_of]
  rw [hx]
  have hc' : value (fun i => SimulatorRelations.positive D (D.code i)) w =
      SimulatorRelations.positive D (w.flatMap D.code) := by
    simp only [positive_eq_value, value_flatMap]
  rw [hc', aValues_eq]
  simp [simulatorDelta, SimulatorWords.delta, SimulatorWords.T,
    SimulatorWords.bar, FP.evalWord, simulatorLWords, SimulatorWords.positive,
    SimulatorRelations.positive, evalPositive, SimulatorRelations.s,
    SimulatorRelations.f, SimulatorRelations.t, generators, List.prod_append, mul_assoc]

/-- Generic diagonal map.  The last three generators are retained, while
the first two acquire commuting input letters conjugated by `f`. -/
def diagonal {H : Type*} [Group H] (a : Fin 5 → H) (u : Fin 2 → H) (f : H) :
    FreeGroup (Fin 5) →* H :=
  FreeGroup.lift ![a 0 * f * u 0 * f⁻¹, a 1 * f * u 1 * f⁻¹, a 2, a 3, a 4]

theorem diagonal_code {H : Type*} [Group H] (a : Fin 5 → H)
    (u : Fin 2 → H) (f : H)
    (hc : ∀ i j, Commute (f * u i * f⁻¹) (![a 0, a 1] j)) (w : PositiveWord) :
    diagonal a u f (value ![FreeGroup.of 0, FreeGroup.of 1] w) =
      value ![a 0, a 1] w * f * value u w * f⁻¹ := by
  rw [map_value]
  have heq : (fun i : Fin 2 => diagonal a u f (![FreeGroup.of 0, FreeGroup.of 1] i)) =
      (fun i => ![a 0, a 1] i * (f * u i * f⁻¹)) := by
    funext i
    fin_cases i <;> simp [diagonal, mul_assoc]
  rw [heq, value_mul _ _ hc, value_conj]
  group

/-- A recognized word is fixed by the diagonal map.  This is the agreement
condition needed to extend the map across the amalgamated subgroup. -/
theorem diagonal_deltaWord {H : Type*} [Group H] (D : CodeWords)
    (a : Fin 5 → H) (u : Fin 2 → H) (f : H)
    (hc : ∀ i j, Commute (f * u i * f⁻¹) (![a 0, a 1] j))
    (w : PositiveWord) (hw : value u w = 1) :
    diagonal a u f (deltaWord D w) = FreeGroup.lift a (deltaWord D w) := by
  have hx : ∀ v : PositiveWord,
      diagonal a u f (value ![FreeGroup.of 2, FreeGroup.of 3] v) =
        FreeGroup.lift a (value ![FreeGroup.of 2, FreeGroup.of 3] v) := by
    intro v
    simp only [map_value]
    congr 1
    funext i
    fin_cases i <;> simp [diagonal]
  unfold deltaWord
  simp only [map_mul, map_inv]
  rw [diagonal_code a u f hc, hw, hx]
  simp only [diagonal, FreeGroup.lift_apply_of, Matrix.cons_val,
    map_value, mul_one, mul_inv_cancel_right]
  congr 2
  congr 1
  funext i
  fin_cases i <;> simp

end EllAlgebra
end UniversalGroup
