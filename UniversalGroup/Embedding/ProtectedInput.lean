module

public import UniversalGroup.Coding.Data
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The protected input required for thirteen-relator compression

The row presentation eliminates `u,v,ℓ` from
`⟨G,c,ℓ,b | uᵇ = ℓ, ℓᵇ = c, cᵇ = v⟩`.  Its two generator slots are
ordered `b,c`.  The additional input hypothesis records the precise free triple
needed by the factor swap, recorded separately from `PreparedInput`.

`ProtectedInput.Theorem` supplies this input using a marked quotient of the
positive preparation and an explicit action preserving the free triple.
-/

namespace UniversalGroup.Embedding

noncomputable section

namespace RowWords

def b : Word 2 := Word.generator 0
def c : Word 2 := Word.generator 1

/-- The two input generators after eliminating the three row equations. -/
def input : Fin 2 → Word 2 :=
  ![Word.product [Word.pow b 2, c, Word.inverse (Word.pow b 2)],
    Word.product [Word.inverse b, c, b]]

@[simp] theorem eval_input {H : Type*} [Group H] (x : Fin 2 → H) (i : Fin 2) :
    Word.eval x (input i) =
      ![x 0 ^ 2 * x 1 * (x 0 ^ 2)⁻¹, (x 0)⁻¹ * x 1 * x 0] i := by
  fin_cases i <;> simp [input, b, c, mul_assoc]

end RowWords

/-- The exact two-generator presentation of the row group, ordered `b,c`. -/
def rowPresentation (G : PreparedInput) : FP 2 G.relatorCount where
  relator i := Word.substitute RowWords.input (G.presentation.relator i)

abbrev RowGroup (G : PreparedInput) := (rowPresentation G).Group

def rowGeneratorB (G : PreparedInput) : RowGroup G := generators (rowPresentation G) 0
def rowGeneratorC (G : PreparedInput) : RowGroup G := generators (rowPresentation G) 1

def rowInputValues (G : PreparedInput) : Fin 2 → RowGroup G :=
  ![rowGeneratorB G ^ 2 * rowGeneratorC G * (rowGeneratorB G ^ 2)⁻¹,
    (rowGeneratorB G)⁻¹ * rowGeneratorC G * rowGeneratorB G]

/-- The input relators hold after the row substitution. -/
theorem row_input_relators (G : PreparedInput) (i : Fin G.relatorCount) :
    Word.eval (rowInputValues G) (G.presentation.relator i) = 1 := by
  have h := (rowPresentation G).relator_eq_one i
  change Word.eval (fun j => generators (rowPresentation G) j)
    (Word.substitute RowWords.input (G.presentation.relator i)) = 1 at h
  rw [Word.eval_substitute] at h
  simpa only [RowWords.eval_input, rowInputValues, rowGeneratorB, rowGeneratorC] using h

/-- The canonical map from the prepared input to its row presentation. -/
def rowInput (G : PreparedInput) : G.presentation.Group →* RowGroup G :=
  G.presentation.homOfRelators (rowInputValues G) (row_input_relators G)

@[simp] theorem rowInput_generator (G : PreparedInput) (i : Fin 2) :
    rowInput G (generators G.presentation i) = rowInputValues G i := by
  simp [rowInput, generators]

/-- The protected triple, in the order `b, cbc⁻¹, c³`. -/
def rowTriple (G : PreparedInput) : FreeGroup (Fin 3) →* RowGroup G :=
  FreeGroup.lift ![rowGeneratorB G, rowGeneratorC G * rowGeneratorB G * (rowGeneratorC G)⁻¹, rowGeneratorC G ^ 3]

/-- Freeness is required in the actual row group, not just in `F(b,c)`. -/
def ProtectedRowTriple (G : PreparedInput) : Prop := Function.Injective (rowTriple G)

namespace RowTriple

def generator (i : Fin 3) : FreeGroup (Fin 3) := FreeGroup.of i

/-- Change `(C,B,D)` to `(BDB⁻¹,B,C)`. -/
def changeBasis : FreeGroup (Fin 3) →* FreeGroup (Fin 3) :=
  FreeGroup.lift ![generator 1 * generator 2 * (generator 1)⁻¹,
    generator 1, generator 0]

def undoBasis : FreeGroup (Fin 3) →* FreeGroup (Fin 3) :=
  FreeGroup.lift ![generator 2, generator 1,
    (generator 1)⁻¹ * generator 0 * generator 1]

theorem undo_comp_change : undoBasis.comp changeBasis = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [changeBasis, undoBasis, generator, mul_assoc]

theorem changeBasis_injective : Function.Injective changeBasis := by
  intro x y h
  have hh := congrArg undoBasis h
  simpa only [← MonoidHom.comp_apply, undo_comp_change, MonoidHom.id_apply] using hh

end RowTriple

/-- The ordered attaching triple `(A,B,C)` used in the five-equation factor swap. -/
def compressionTriple (G : PreparedInput) : FreeGroup (Fin 3) →* RowGroup G :=
  (rowTriple G).comp RowTriple.changeBasis

theorem compressionTriple_injective (G : PreparedInput) (h : ProtectedRowTriple G) :
    Function.Injective (compressionTriple G) :=
  h.comp RowTriple.changeBasis_injective

@[simp] theorem compressionTriple_zero (G : PreparedInput) :
    compressionTriple G (FreeGroup.of 0) =
      (rowGeneratorC G * rowGeneratorB G * (rowGeneratorC G)⁻¹) * rowGeneratorC G ^ 3 *
        (rowGeneratorC G * rowGeneratorB G * (rowGeneratorC G)⁻¹)⁻¹ := by
  simp [compressionTriple, RowTriple.changeBasis, RowTriple.generator, rowTriple]

@[simp] theorem compressionTriple_one (G : PreparedInput) :
    compressionTriple G (FreeGroup.of 1) = rowGeneratorC G * rowGeneratorB G * (rowGeneratorC G)⁻¹ := by
  simp [compressionTriple, RowTriple.changeBasis, RowTriple.generator, rowTriple]

@[simp] theorem compressionTriple_two (G : PreparedInput) :
    compressionTriple G (FreeGroup.of 2) = rowGeneratorB G := by
  simp [compressionTriple, RowTriple.changeBasis, RowTriple.generator, rowTriple]

end

end UniversalGroup.Embedding
