module

public import UniversalGroup.Simulator.Core.CStage

@[expose] public section

/-!
# Literal positivity of the canonical free-group word

The signed recognition theorem returns equality with a positive free word.
These lemmas recover the literal reduced spelling needed for marker parsing.
-/

namespace UniversalGroup.BorisovCStage

private theorem positiveLetters_isReduced (w : List (Fin 2)) :
    FreeGroup.IsReduced (w.map fun i => (i, true)) := by
  induction w with
  | nil => simp [FreeGroup.IsReduced]
  | cons i w ih =>
      cases w with
      | nil => simp [FreeGroup.IsReduced]
      | cons j w =>
          change List.IsChain (fun a b : Fin 2 × Bool =>
            a.1 = b.1 → a.2 = b.2)
              ((i, true) :: (j, true) :: w.map fun k => (k, true))
          rw [List.isChain_cons]
          exact ⟨by simp, ih⟩

@[simp] theorem positiveFree_toWord (w : List (Fin 2)) :
    (positiveFree w).toWord = w.map (fun i => (i, true)) := by
  rw [positiveFree, FreeGroup.toWord_mk]
  exact (positiveLetters_isReduced w).reduce_eq

end UniversalGroup.BorisovCStage

namespace UniversalGroup

theorem PositiveStep.symm {rules : Set (PositiveWord × PositiveWord)}
    {u v : PositiveWord} (h : PositiveStep rules u v) : PositiveStep rules v u := by
  rcases h with ⟨l, r, x, y, hxy, hwords⟩
  rcases hwords with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact ⟨l, r, x, y, hxy, Or.inr ⟨hv, hu⟩⟩
  · exact ⟨l, r, x, y, hxy, Or.inl ⟨hv, hu⟩⟩

theorem PositiveEq.symm {rules : Set (PositiveWord × PositiveWord)}
    {u v : PositiveWord} (h : PositiveEq rules u v) : PositiveEq rules v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact (Relation.ReflTransGen.single (PositiveStep.symm hstep)).trans ih

end UniversalGroup
