module

public import UniversalGroup.Embedding.ProtectedInput.RowModel
public import UniversalGroup.Host.BStage
public import UniversalGroup.Foundations.HNN.Map

@[expose] public section

/-!
# The full row product in the final b-extension

The row HNN extension embeds by reflecting both associated subgroups. A
normal-form argument then shows that its image meets the column factor only
at one. The stable letter commutes with every column, so their product embeds.
-/

namespace UniversalGroup.Embedding.RowProduct

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

/-- Reflecting the associated subgroups also reflects the HNN base. -/
theorem identifying_preimage_base
    {A P C M : Type*} [Group A] [Group P] [Group C] [Group M]
    (l r : A →* P) (hl : Function.Injective l) (hr : Function.Injective r)
    (l' r' : C →* M) (hl' : Function.Injective l') (hr' : Function.Injective r')
    (f : P →* M) (F : IdentifyingHNN l r hl hr →* IdentifyingHNN l' r' hl' hr')
    (hA : ∀ x, x ∈ l.range ↔ f x ∈ l'.range)
    (hB : ∀ x, x ∈ r.range ↔ f x ∈ r'.range)
    (hof : ∀ x, F (IdentifyingHNN.of l r hl hr x) = IdentifyingHNN.of l' r' hl' hr' (f x))
    (ht : F (IdentifyingHNN.stable l r hl hr) = IdentifyingHNN.stable l' r' hl' hr')
    (y : IdentifyingHNN l r hl hr)
    (hy : F y ∈ (IdentifyingHNN.of l' r' hl' hr').range) :
    ∃ x : P, y = IdentifyingHNN.of l r hl hr x := by
  apply HNNMap.preimage_base l.range r.range (rangeEquiv l r hl hr)
    l'.range r'.range (rangeEquiv l' r' hl' hr') f F hA hB hof ?_ y hy
  simpa only [IdentifyingHNN.stable, map_inv, inv_inv] using congrArg Inv.inv ht

variable (G : PreparedInput) {J : Type*} [Group J]
  (grid : InputFreeSubgroup.Domain G × FreeGroup (Fin 2) →* J)
  (hgrid : Function.Injective grid)

abbrev Model := BCompression.Model G grid hgrid

def base : InputFreeSubgroup.Domain G →* J := grid.comp (MonoidHom.inl _ _)

def columns : FreeGroup (Fin 2) →* Model G grid hgrid :=
  (BCompression.embeddedGrid G grid hgrid).comp (MonoidHom.inr _ _)

theorem conjugates_row (w : FreeGroup (Fin 3)) :
    (BCompression.b G grid hgrid)⁻¹ *
        BCompression.of G grid hgrid (base G grid (InputTriples.left G w)) *
        BCompression.b G grid hgrid =
      BCompression.of G grid hgrid (base G grid (InputTriples.right G w)) := by
  exact IdentifyingHNN.conjugates (BCompression.left G grid) (BCompression.right G grid)
    (BCompression.left_injective G grid hgrid) (BCompression.right_injective G grid hgrid) (w,1)

set_option maxHeartbeats 1600000 in
/-- Extend the row base and its stable letter into the actual ambient HNN. -/
def row : RowModel.Model G →* Model G grid hgrid :=
  IdentifyingHNN.lift (A := FreeGroup (Fin 3)) (G := InputFreeSubgroup.Domain G)
    (H := Model G grid hgrid) (InputTriples.left G) (InputTriples.right G)
    (InputTriples.left_injective G) (InputTriples.right_injective G)
    ((BCompression.of G grid hgrid).comp (base G grid))
    (BCompression.b G grid hgrid) (by
      intro w
      change (BCompression.b G grid hgrid)⁻¹ *
        BCompression.of G grid hgrid (base G grid (InputTriples.left G w)) *
        BCompression.b G grid hgrid =
        BCompression.of G grid hgrid (base G grid (InputTriples.right G w))
      exact conjugates_row G grid hgrid w)

@[simp] theorem row_of (u : InputFreeSubgroup.Domain G) :
    row G grid hgrid (RowModel.of G u) = BCompression.embeddedGrid G grid hgrid (u,1) := by
  simp [row, RowModel.of, base, BCompression.embeddedGrid]

@[simp] theorem row_b :
    row G grid hgrid (RowModel.b G) = BCompression.b G grid hgrid := by
  simp [row, RowModel.b]

theorem row_t : row G grid hgrid HNNExtension.t = (BCompression.b G grid hgrid)⁻¹ := by
  have hh := congrArg Inv.inv (row_b G grid hgrid)
  simpa only [RowModel.b, IdentifyingHNN.stable, map_inv, inv_inv] using hh

include hgrid in
theorem reflects_left (u : InputFreeSubgroup.Domain G) :
    u ∈ (InputTriples.left G).range ↔ base G grid u ∈ (BCompression.left G grid).range := by
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨(w,1),rfl⟩
  · rintro ⟨⟨w,v⟩,hw⟩
    refine ⟨w,?_⟩
    change grid (InputTriples.left G w,v) = grid (u,1) at hw
    exact congrArg Prod.fst (hgrid hw)

include hgrid in
theorem reflects_right (u : InputFreeSubgroup.Domain G) :
    u ∈ (InputTriples.right G).range ↔ base G grid u ∈ (BCompression.right G grid).range := by
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨(w,1),rfl⟩
  · rintro ⟨⟨w,v⟩,hw⟩
    refine ⟨w,?_⟩
    change grid (InputTriples.right G w,v) = grid (u,1) at hw
    exact congrArg Prod.fst (hgrid hw)

/-- A row word whose image lies in the ambient base already has no stable letter. -/
theorem row_preimage_base (y : RowModel.Model G)
    (hy : row G grid hgrid y ∈ (BCompression.of G grid hgrid).range) :
    ∃ u : InputFreeSubgroup.Domain G, y = RowModel.of G u := by
  have hpre := identifying_preimage_base
    (A := FreeGroup (Fin 3)) (P := InputFreeSubgroup.Domain G)
    (C := FreeGroup (Fin 3) × FreeGroup (Fin 2)) (M := J)
    (InputTriples.left G) (InputTriples.right G)
    (InputTriples.left_injective G) (InputTriples.right_injective G)
    (BCompression.left G grid) (BCompression.right G grid)
    (BCompression.left_injective G grid hgrid) (BCompression.right_injective G grid hgrid)
    (base G grid) (by
      change RowModel.Model G →* Model G grid hgrid
      exact row G grid hgrid)
    (reflects_left G grid hgrid) (reflects_right G grid hgrid)
    (by
      intro u
      change row G grid hgrid (RowModel.of G u) =
        BCompression.embeddedGrid G grid hgrid (u,1)
      exact row_of G grid hgrid u)
    (by
      change row G grid hgrid (RowModel.b G) = BCompression.b G grid hgrid
      exact row_b G grid hgrid)
  exact hpre y hy

theorem row_commutes_columns (y : RowModel.Model G) (v : FreeGroup (Fin 2)) :
    Commute (row G grid hgrid y) (columns G grid hgrid v) := by
  induction y using HNNExtension.induction_on with
  | of u =>
      have hh := (MonoidHom.commute_inl_inr (M := InputFreeSubgroup.Domain G)
        (N := FreeGroup (Fin 2)) u v).map (BCompression.embeddedGrid G grid hgrid)
      change Commute (row G grid hgrid (RowModel.of G u)) (columns G grid hgrid v)
      rw [row_of]
      simpa only [columns, MonoidHom.comp_apply,
        MonoidHom.inl_apply, MonoidHom.inr_apply] using hh
  | t =>
      rw [row_t]
      exact (BCompression.commutes_columns G grid hgrid v).inv_left
  | mul y z hy hz => simpa only [map_mul] using hy.mul_left hz
  | inv y hy => simpa only [map_inv] using hy.inv_left

/-- The entire row group and column free group form a direct product. -/
def product : RowModel.Model G × FreeGroup (Fin 2) →* Model G grid hgrid :=
  (row G grid hgrid).noncommCoprod (columns G grid hgrid) (row_commutes_columns G grid hgrid)

@[simp] theorem product_of (u : InputFreeSubgroup.Domain G) (v : FreeGroup (Fin 2)) :
    product G grid hgrid (RowModel.of G u,v) = BCompression.embeddedGrid G grid hgrid (u,v) := by
  change row G grid hgrid (RowModel.of G u) * columns G grid hgrid v = _
  rw [row_of]
  change BCompression.embeddedGrid G grid hgrid (u,1) *
    BCompression.embeddedGrid G grid hgrid (1,v) = _
  rw [← map_mul]
  simp

theorem product_injective : Function.Injective (product G grid hgrid) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨y,v⟩ h
  have hrow : row G grid hgrid y = (columns G grid hgrid v)⁻¹ := by
    have hh := congrArg (fun z => z * (columns G grid hgrid v)⁻¹) h
    simpa [product, mul_assoc] using hh
  have hy : row G grid hgrid y ∈ (BCompression.of G grid hgrid).range := by
    refine ⟨(grid (1,v))⁻¹,?_⟩
    rw [hrow]
    simp [columns, BCompression.embeddedGrid]
  obtain ⟨u,rfl⟩ := row_preimage_base G grid hgrid y hy
  rw [product_of] at h
  have hz : BCompression.embeddedGrid G grid hgrid (u,v) =
      BCompression.embeddedGrid G grid hgrid 1 := h.trans (map_one _).symm
  have huv : (u,v) = (1,1) := (BCompression.embeddedGrid_injective G grid hgrid) hz
  have hu := congrArg Prod.fst huv
  have hv := congrArg Prod.snd huv
  change u = 1 at hu
  change v = 1 at hv
  simp [hu,hv]

end
end UniversalGroup.Embedding.RowProduct
