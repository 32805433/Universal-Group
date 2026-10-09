module

public import UniversalGroup.Embedding.ProtectedInput
public import UniversalGroup.Host.InputTriples
public import UniversalGroup.Foundations.Conjugation

@[expose] public section

/-!
# Comparing the row presentation with its proper HNN model

The HNN base is `ℤ * G * ℤ`, marked by `c,G,ℓ`.  The free-triple
theorem makes its two associated maps injective.  The compact two-generator
row presentation maps faithfully to this model, with the precise markings
needed to transport the protected triple into later extension towers.
-/

namespace UniversalGroup.Embedding.RowModel

noncomputable section
set_option maxHeartbeats 1000000
variable (G : PreparedInput)

abbrev Model := IdentifyingHNN (A := FreeGroup (Fin 3)) (G := InputFreeSubgroup.Domain G)
  (InputTriples.left G) (InputTriples.right G)
  (InputTriples.left_injective G) (InputTriples.right_injective G)

def of : InputFreeSubgroup.Domain G →* Model G := IdentifyingHNN.of _ _ _ _
def b : Model G := IdentifyingHNN.stable _ _ _ _
def c : Model G := of G (InputTriples.c G)
def ell : Model G := of G (InputTriples.ell G)

def input : G.presentation.Group →* Model G :=
  (of G).comp (Monoid.Coprod.inl.comp Monoid.Coprod.inr)

@[simp] theorem input_generator (i : Fin 2) :
    input G (generators G.presentation i) = of G (InputTriples.input G i) := rfl

theorem shifts (i : Fin 3) :
    (b G)⁻¹ * of G (![InputTriples.input G 0, InputTriples.ell G, InputTriples.c G] i) *
        b G = of G (![InputTriples.ell G, InputTriples.c G, InputTriples.input G 1] i) := by
  have hh := IdentifyingHNN.conjugates (A := FreeGroup (Fin 3))
    (G := InputFreeSubgroup.Domain G) (InputTriples.left G) (InputTriples.right G)
    (InputTriples.left_injective G) (InputTriples.right_injective G) (FreeGroup.of i)
  rw [InputTriples.left_of, InputTriples.right_of] at hh
  exact hh

theorem substitutions :
    ell G = b G * c G * (b G)⁻¹ ∧
    input G (generators G.presentation 0) = b G ^ 2 * c G * (b G ^ 2)⁻¹ ∧
    input G (generators G.presentation 1) = (b G)⁻¹ * c G * b G := by
  have h0 := shifts G 0
  have h1 := shifts G 1
  have h2 := shifts G 2
  change (b G)⁻¹ * of G (InputTriples.input G 0) * b G = ell G at h0
  change (b G)⁻¹ * ell G * b G = c G at h1
  change (b G)⁻¹ * c G * b G = of G (InputTriples.input G 1) at h2
  have hl : ell G = b G * c G * (b G)⁻¹ := eq_conjugate_of_inv_conjugate_eq h1
  refine ⟨hl, ?_, h2.symm⟩
  rw [input_generator, eq_conjugate_of_inv_conjugate_eq h0]
  rw [hl, pow_two]
  group

def values : Fin 2 → Model G := ![b G, c G]

theorem eval_input_words (i : Fin 2) :
    Word.eval (values G) (RowWords.input i) = input G (generators G.presentation i) := by
  rw [RowWords.eval_input]
  fin_cases i
  · exact (substitutions G).2.1.symm
  · exact (substitutions G).2.2.symm

theorem relators (i : Fin G.relatorCount) :
    Word.eval (values G) ((rowPresentation G).relator i) = 1 := by
  change Word.eval (values G)
    (Word.substitute RowWords.input (G.presentation.relator i)) = 1
  rw [Word.eval_substitute]
  simp only [eval_input_words]
  have h := congrArg (input G) (G.presentation.relator_eq_one i)
  simpa only [FP.evalWord, Word.map_eval, map_one, generators, Function.comp_def] using h

def toModel : RowGroup G →* Model G :=
  (rowPresentation G).homOfRelators (values G) (relators G)

@[simp] theorem toModel_b : toModel G (rowGeneratorB G) = b G := by
  simp [toModel, rowGeneratorB, generators, values]

@[simp] theorem toModel_c : toModel G (rowGeneratorC G) = c G := by
  simp [toModel, rowGeneratorC, generators, values]

/-- Send the three marked factors of the HNN base to their eliminated words. -/
def fromBase : InputFreeSubgroup.Domain G →* RowGroup G :=
  Monoid.Coprod.lift
    (Monoid.Coprod.lift (zpowersHom _ (rowGeneratorC G)) (rowInput G))
    (zpowersHom _ (rowGeneratorB G * rowGeneratorC G * (rowGeneratorB G)⁻¹))

@[simp] theorem fromBase_c : fromBase G (InputTriples.c G) = rowGeneratorC G := by
  simp [fromBase, InputTriples.c]

@[simp] theorem fromBase_ell :
    fromBase G (InputTriples.ell G) = rowGeneratorB G * rowGeneratorC G * (rowGeneratorB G)⁻¹ := by
  simp [fromBase, InputTriples.ell]

@[simp] theorem fromBase_input (i : Fin 2) :
    fromBase G (InputTriples.input G i) = rowInputValues G i := by
  simp [fromBase, InputTriples.input]

theorem fromBase_conjugates (w : FreeGroup (Fin 3)) :
    (rowGeneratorB G)⁻¹ * fromBase G (InputTriples.left G w) * rowGeneratorB G =
      fromBase G (InputTriples.right G w) := by
  have h : (MulAut.conj (rowGeneratorB G)⁻¹).toMonoidHom.comp
      ((fromBase G).comp (InputTriples.left G)) =
      (fromBase G).comp (InputTriples.right G) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;>
      simp [rowInputValues, pow_two, mul_assoc]
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv] using DFunLike.congr_fun h w

def fromModel : Model G →* RowGroup G :=
  IdentifyingHNN.lift _ _ _ _ (fromBase G) (rowGeneratorB G) (fromBase_conjugates G)

@[simp] theorem fromModel_of (x : InputFreeSubgroup.Domain G) :
    fromModel G (of G x) = fromBase G x := by
  simp [fromModel, of]

@[simp] theorem fromModel_b : fromModel G (b G) = rowGeneratorB G := by
  simp [fromModel, b]

@[simp] theorem fromModel_c : fromModel G (c G) = rowGeneratorC G := by
  simp [c]

theorem fromModel_comp_toModel : (fromModel G).comp (toModel G) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · change fromModel G (toModel G (rowGeneratorB G)) = rowGeneratorB G
    simp
  · change fromModel G (toModel G (rowGeneratorC G)) = rowGeneratorC G
    simp

theorem toModel_injective : Function.Injective (toModel G) := by
  intro x y h
  have hh := congrArg (fromModel G) h
  simpa only [← MonoidHom.comp_apply, fromModel_comp_toModel, MonoidHom.id_apply] using hh

end

end UniversalGroup.Embedding.RowModel
