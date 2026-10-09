module

public import UniversalGroup.Preparation.Conjugations
public import UniversalGroup.Foundations.FinitePresentation.Products

@[expose] public section

/-! The finite cyclic-conjugation input for the last two-generator compression. -/
namespace UniversalGroup.PreparationReflectionStage
noncomputable section
open PreparationCyclic

variable (Q : FP n m)
abbrev Base := ReflectionProduct Q
def uBase : Base Q := (1,generator)
def values : Fin (n+n+1) → Base Q := reflectionValues Q
abbrev Model := PreparationConjugations.Stage (uBase Q) (values Q)
def of : Base Q →* Model Q := PreparationConjugations.of (uBase Q) (values Q)
def u : Model Q := of Q (uBase Q)
def j : FreeGroup (Fin (n+n+1)) →* Model Q :=
  PreparationConjugations.stableFree (uBase Q) (values Q)
def rho : Model Q →* C4 :=
  PreparationConjugations.projection (uBase Q) (values Q) (MonoidHom.snd _ _)
    rfl (reflectionValues_projection Q)

theorem uBase_fourthPower : uBase Q ^4=1 := by simp [uBase]
theorem of_injective : Function.Injective (of Q) :=
  PreparationConjugations.of_injective _ _ (uBase_fourthPower Q)
    (reflectionValues_fourthPower Q) (MonoidHom.snd _ _) rfl
    (reflectionValues_projection Q)

theorem fourthPower : u Q ^4=1 := by
  rw [u,←map_pow,uBase_fourthPower,map_one]
theorem j_injective : Function.Injective (j Q) :=
  PreparationConjugations.stableFree_injective _ _
@[simp] theorem rho_u : rho Q (u Q)=generator := by
  exact PreparationConjugations.projection_of _ _ _ _ _ _
theorem rho_j : (rho Q).comp (j Q)=1 :=
  PreparationConjugations.projection_comp_stableFree _ _ _ _ _
theorem generates :
    Subgroup.closure ({u Q} ∪ Set.range (fun i=>j Q (FreeGroup.of i)))=⊤ :=
  PreparationConjugations.generate _ _ (reflectionValues_generate Q)

def embedding : Q.Group →* Model Q :=
  (of Q).comp ((MonoidHom.inl _ C4).comp (PreparationReflections.ofOld Q))
theorem embedding_injective : Function.Injective (embedding Q) := by
  intro x y hxy
  apply PreparationReflections.ofOld_injective Q
  exact congrArg Prod.fst (of_injective Q hxy)

instance basePresented : Group.IsFinitelyPresented (Base Q) := by
  let P := PreparationReflections.presentation Q
  have : Finite P.relSet := (Set.finite_range _).to_subtype
  have : Group.IsFinitelyPresented P.Group := inferInstance
  change Group.IsFinitelyPresented (P.Group × C4)
  exact PreparationFinite.prod _ _

instance modelPresented : Group.IsFinitelyPresented (Model Q) :=
  PreparationConjugations.finitelyPresented _ _

end
end UniversalGroup.PreparationReflectionStage
