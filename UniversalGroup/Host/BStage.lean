module

public import UniversalGroup.Host.InputTriples
public import UniversalGroup.Foundations.Conjugation

@[expose] public section

/-! The proper `b` extension, its embedded product grid, and the row substitutions. -/

namespace UniversalGroup.BCompression
noncomputable section

variable (G : PreparedInput)
variable {J : Type*} [Group J]
variable (grid : InputFreeSubgroup.Domain G × FreeGroup (Fin 2) →* J)
  (hgrid : Function.Injective grid)

def left : FreeGroup (Fin 3) × FreeGroup (Fin 2) →* J :=
  grid.comp ((InputTriples.left G).prodMap (MonoidHom.id _))

def right : FreeGroup (Fin 3) × FreeGroup (Fin 2) →* J :=
  grid.comp ((InputTriples.right G).prodMap (MonoidHom.id _))

include hgrid in
theorem left_injective : Function.Injective (left G grid) := by
  intro u v h
  have hh := hgrid h
  exact Prod.ext (InputTriples.left_injective G (by simpa using congrArg Prod.fst hh))
    (by simpa using congrArg Prod.snd hh)

include hgrid in
theorem right_injective : Function.Injective (right G grid) := by
  intro u v h
  have hh := hgrid h
  exact Prod.ext (InputTriples.right_injective G (by simpa using congrArg Prod.fst hh))
    (by simpa using congrArg Prod.snd hh)

abbrev Model := IdentifyingHNN (left G grid) (right G grid)
  (left_injective G grid hgrid) (right_injective G grid hgrid)

def of : J →* Model G grid hgrid := IdentifyingHNN.of _ _ _ _
def b : Model G grid hgrid := IdentifyingHNN.stable _ _ _ _

theorem of_injective : Function.Injective (of G grid hgrid) :=
  IdentifyingHNN.of_injective _ _ _ _

def embeddedGrid : InputFreeSubgroup.Domain G × FreeGroup (Fin 2) →* Model G grid hgrid :=
  (of G grid hgrid).comp grid

theorem embeddedGrid_injective : Function.Injective (embeddedGrid G grid hgrid) :=
  (of_injective G grid hgrid).comp hgrid

theorem shifts (i : Fin 3) :
    (b G grid hgrid)⁻¹ * embeddedGrid G grid hgrid
        (![InputTriples.input G 0, InputTriples.ell G, InputTriples.c G] i, 1) *
      b G grid hgrid = embeddedGrid G grid hgrid
        (![InputTriples.ell G, InputTriples.c G, InputTriples.input G 1] i, 1) := by
  have h := IdentifyingHNN.conjugates (left G grid) (right G grid)
    (left_injective G grid hgrid) (right_injective G grid hgrid) (FreeGroup.of i, 1)
  change (b G grid hgrid)⁻¹ * of G grid hgrid (left G grid (FreeGroup.of i, 1)) *
    b G grid hgrid = of G grid hgrid (right G grid (FreeGroup.of i, 1)) at h
  simpa only [left, right, MonoidHom.comp_apply, MonoidHom.coe_prodMap, Prod.map_apply,
    MonoidHom.id_apply, InputTriples.left_of, InputTriples.right_of, embeddedGrid] using h

theorem commutes_columns (v : FreeGroup (Fin 2)) :
    Commute (b G grid hgrid) (embeddedGrid G grid hgrid (1, v)) := by
  have h := IdentifyingHNN.conjugates (left G grid) (right G grid)
    (left_injective G grid hgrid) (right_injective G grid hgrid) (1, v)
  change (b G grid hgrid)⁻¹ * of G grid hgrid (grid (InputTriples.left G 1, v)) *
    b G grid hgrid = of G grid hgrid (grid (InputTriples.right G 1, v)) at h
  simp only [map_one] at h
  have hh := congrArg (fun z => b G grid hgrid * z) h
  simpa [embeddedGrid, commute_iff_eq, mul_assoc] using hh.symm

theorem substitutions :
    embeddedGrid G grid hgrid (InputTriples.ell G, 1) =
        b G grid hgrid * embeddedGrid G grid hgrid (InputTriples.c G, 1) * (b G grid hgrid)⁻¹ ∧
      embeddedGrid G grid hgrid (InputTriples.input G 0, 1) =
        b G grid hgrid ^ 2 * embeddedGrid G grid hgrid (InputTriples.c G, 1) *
          (b G grid hgrid ^ 2)⁻¹ ∧
      embeddedGrid G grid hgrid (InputTriples.input G 1, 1) =
        (b G grid hgrid)⁻¹ * embeddedGrid G grid hgrid (InputTriples.c G, 1) * b G grid hgrid := by
  have h0 := shifts G grid hgrid 0
  have h1 := shifts G grid hgrid 1
  have h2 := shifts G grid hgrid 2
  simp only [Matrix.cons_val] at h0 h1 h2
  have hl := eq_conjugate_of_inv_conjugate_eq h1
  refine ⟨hl, ?_, h2.symm⟩
  rw [eq_conjugate_of_inv_conjugate_eq h0, hl]
  rw [pow_two]
  group

end
end UniversalGroup.BCompression
