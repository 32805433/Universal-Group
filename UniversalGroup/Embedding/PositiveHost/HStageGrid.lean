module

public import UniversalGroup.Embedding.PositiveHost.HStage
public import UniversalGroup.Host.SymmetryGrid

@[expose] public section

/-! The positive symmetry has the same associated subgroup ranges, so the
shared exact grid intersections apply. -/
namespace UniversalGroup.Embedding.PositiveHost.HStageGrid
noncomputable section
variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

theorem right_range : (HStage.right G D hi).range =
    (UniversalGroup.SymmetrySubgroups.right G D hi).range := by
  have hp : (HStage.extensionEquiv G D hi).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (HStage.extensionEquiv G D hi).surjective
  rw [HStage.right, MonoidHom.range_comp, hp]
  rw [UniversalGroup.SymmetryGrid.range_right]
  ext x
  simp

theorem product_mem_left_iff (a : InputFreeSubgroup.Domain G × FreeGroup (Fin 4)) :
    EllGrid.product G D hi a ∈ (HStage.left G D hi).range ↔
      a.2 ∈ Subgroup.closure ({FreeGroup.of 1} : Set _) :=
  UniversalGroup.SymmetryGrid.product_mem_left_iff G D hi a

theorem product_mem_right_iff (a : InputFreeSubgroup.Domain G × FreeGroup (Fin 4)) :
    EllGrid.product G D hi a ∈ (HStage.right G D hi).range ↔
      a.2 ∈ Subgroup.closure ({FreeGroup.of 2} : Set _) := by
  rw [right_range]
  exact UniversalGroup.SymmetryGrid.product_mem_right_iff G D hi a

end
end UniversalGroup.Embedding.PositiveHost.HStageGrid
