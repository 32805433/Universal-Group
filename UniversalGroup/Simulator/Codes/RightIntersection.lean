module

public import UniversalGroup.Simulator.Codes.RightAction

@[expose] public section

/-!
# The second exact single-letter intersection

Conjugating by `f` and changing two basis elements puts the coded subgroup
in the form tested by the rotated decoder. The resulting intersection is
then transported back to the original basis.
-/

namespace UniversalGroup.CodeSubgroups

noncomputable section

private def rebase : FreeGroup (Fin 5) →* FreeGroup (Fin 5) :=
  FreeGroup.lift ![(FreeGroup.of 4)⁻¹ * FreeGroup.of 0 * FreeGroup.of 4,
    (FreeGroup.of 4)⁻¹ * FreeGroup.of 1 * FreeGroup.of 4,
    FreeGroup.of 2, FreeGroup.of 3, FreeGroup.of 4]

private theorem rebase_surjective : Function.Surjective rebase := by
  let undo : FreeGroup (Fin 5) →* FreeGroup (Fin 5) :=
    FreeGroup.lift ![FreeGroup.of 4 * FreeGroup.of 0 * (FreeGroup.of 4)⁻¹,
      FreeGroup.of 4 * FreeGroup.of 1 * (FreeGroup.of 4)⁻¹,
      FreeGroup.of 2, FreeGroup.of 3, FreeGroup.of 4]
  have h : rebase.comp undo = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [rebase, undo, mul_assoc]
  intro w
  exact ⟨undo w, DFunLike.congr_fun h w⟩

private def conjF : FreeGroup (Fin 4) ≃* FreeGroup (Fin 4) :=
  MulAut.conj (FreeGroup.of 2)

private theorem newLift_eq (D : CodeWords) :
    RightAction.newLift D =
      (conjF.toMonoidHom.comp (aFreeLift D)).comp rebase := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp [RightAction.newLift, RightAction.newValues, aFreeLift, aFreeValues,
      rebase, conjF, MulAut.conj_apply, mul_assoc]

private theorem newLift_range (D : CodeWords) :
    (RightAction.newLift D).range = (aFreeLift D).range.map conjF.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨aFreeLift D (rebase w), ⟨rebase w, rfl⟩, ?_⟩
    rw [newLift_eq]
    rfl
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    obtain ⟨v, rfl⟩ := rebase_surjective w
    exact ⟨v, by rw [newLift_eq]; rfl⟩

/-- The conjugate of the ambient free subgroup on `s₂,q` by `f⁻¹`. -/
def rightAmbient : Subgroup (FreeGroup (Fin 4)) :=
  Subgroup.closure
    ({(FreeGroup.of 2)⁻¹ * FreeGroup.of 1 * FreeGroup.of 2,
      (FreeGroup.of 2)⁻¹ * FreeGroup.of 3 * FreeGroup.of 2} : Set (FreeGroup (Fin 4)))

private theorem rightAmbient_map : rightAmbient.map conjF.toMonoidHom = RightAction.ambient := by
  simp [rightAmbient, RightAction.ambient, MonoidHom.map_closure, conjF,
    Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply, mul_assoc]

/-- The exact second single-letter intersection in the free four-letter group. -/
theorem aFree_inter_right (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r) :
    (aFreeLift D).range ⊓ rightAmbient =
      Subgroup.closure ({aFreeValues D 3} : Set (FreeGroup (Fin 4))) := by
  apply Subgroup.map_injective (f := conjF.toMonoidHom) conjF.injective
  rw [Subgroup.map_inf _ _ _ conjF.injective, ← newLift_range, rightAmbient_map,
    RightAction.new_intersection D r hcode]
  simp [MonoidHom.map_closure, aFreeValues, conjF, MulAut.conj_apply, mul_assoc]

end
end UniversalGroup.CodeSubgroups
