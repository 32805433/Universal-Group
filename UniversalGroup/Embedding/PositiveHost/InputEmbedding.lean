module

public import UniversalGroup.Embedding.PositiveHost.InputRelators
public import UniversalGroup.Embedding.PositiveHost.ModelComparison

@[expose] public section

/-! The specified input map, independent of its later injectivity proof. -/

namespace UniversalGroup.Embedding.PositiveHost

/-- The concrete map from the prepared input, sending its generators to
`u₁ = b²cb⁻²` and `u₂ = b⁻¹cb`. -/
def baseInputHom (G : PreparedInput) (D : ValievDatum G)
    (hintersections : ValievIntersections G D) :
    G.presentation.Group →* (positiveBasePresentation D.toCodeWords).Group :=
  G.presentation.homOfRelators (baseInputValues D.toCodeWords)
    (base_input_relators G D hintersections)

@[simp]
theorem baseInputHom_generator (G : PreparedInput) (D : ValievDatum G)
    (hintersections : ValievIntersections G D) (i : Fin 2) :
    baseInputHom G D hintersections (generators G.presentation i) =
      baseInputValues D.toCodeWords i :=
  FP.homOfRelators_of _ _ _ _


namespace InputEmbedding
noncomputable section
variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

theorem comp_model : (BaseModel.hom G D hi).comp (baseInputHom G D hi) =
    BaseModel.input G D hi := by
  apply PresentedGroup.ext
  intro i
  change BaseModel.hom G D hi (baseInputHom G D hi (generators G.presentation i)) = _
  rw [baseInputHom_generator]
  exact BaseModel.hom_input_word G D hi i

theorem injective : Function.Injective (baseInputHom G D hi) := by
  intro x y h
  apply BaseModel.input_injective G D hi
  have hh := congrArg (BaseModel.hom G D hi) h
  simpa only [← MonoidHom.comp_apply, comp_model] using hh

def embedding : GroupEmbedding G.presentation.Group
    (positiveBasePresentation D.toCodeWords).Group :=
  ⟨baseInputHom G D hi, injective G D hi⟩
end
end InputEmbedding

end UniversalGroup.Embedding.PositiveHost
