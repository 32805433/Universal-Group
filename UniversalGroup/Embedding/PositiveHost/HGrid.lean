module

public import UniversalGroup.Embedding.PositiveHost.HStageGrid
public import UniversalGroup.Foundations.HNN.ProductGridHNN
public import UniversalGroup.Foundations.HNN.Map

@[expose] public section

/-! The faithful product grid after the `h` extension. -/

namespace UniversalGroup.Embedding.PositiveHost.HGrid
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable (G : PreparedInput) (D : ValievDatum G) (hintersections : ValievIntersections G D)
abbrev U := InputFreeSubgroup.Domain G
abbrev F := FreeGroup (Fin 4)
abbrev Z := FreeGroup (Fin 1)

/-- The old product grid in the base of the `h` extension. -/
def baseMap : U G × F →* HStage.Model G D hintersections :=
  (HStage.ofEll G D hintersections).comp (EllGrid.product G D hintersections)

theorem commutes_U (u : U G) :
    Commute (HStage.stable G D hintersections)
      (HStage.ofEll G D hintersections (InputFreeSubgroup.hom G D hintersections u)) := by
  induction u using Monoid.Coprod.induction_on with
  | inl p =>
    induction p using Monoid.Coprod.induction_on with
    | inl z =>
      rw [InputFreeSubgroup.hom_c]
      simpa only [InputFreeSubgroup.cPowers, zpowersHom_apply, map_zpow,
        HStage.simulatorEmbedding, MonoidHom.comp_apply] using
        (HStage.commutes_c G D hintersections).zpow_right (Multiplicative.toAdd z)
    | inr g =>
      rw [InputFreeSubgroup.hom_input]
      exact HStage.commutes_input G D hintersections g
    | mul p q hp hq => simpa only [map_mul] using hp.mul_right hq
  | inr z =>
    rw [InputFreeSubgroup.hom_ell, map_zpow]
    exact (HStage.commutes_ell G D hintersections).zpow_right (Multiplicative.toAdd z)
  | mul p q hp hq => simpa only [map_mul] using hp.mul_right hq

def old : F →* HStage.Model G D hintersections :=
  (HStage.ofEll G D hintersections).comp (EllGrid.right G D hintersections)

@[simp] theorem old_of (i : Fin 4) :
    old G D hintersections (FreeGroup.of i) =
      (HStage.simulatorEmbedding G D hintersections).hom (simulatorGridValues D.toCodeWords i) := by
  simp [old, EllGrid.right, SimulatorGrid.lift, HStage.simulatorEmbedding]

private theorem conjugates_cyclic (w : Z) :
    (HStage.stable G D hintersections)⁻¹ * old G D hintersections (ProductGridHNN.positive 1 w) *
      HStage.stable G D hintersections = old G D hintersections (ProductGridHNN.negative 2 w) := by
  have h : (MulAut.conj (HStage.stable G D hintersections)⁻¹).toMonoidHom.comp
      ((old G D hintersections).comp (ProductGridHNN.positive 1)) =
      (old G D hintersections).comp (ProductGridHNN.negative 2) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i
    simp only [MonoidHom.comp_apply, ProductGridHNN.positive, ProductGridHNN.negative,
      FreeGroup.lift_apply_of, map_inv, old_of]
    change (HStage.stable G D hintersections)⁻¹ *
      (HStage.simulatorEmbedding G D hintersections).hom (simulatorGridValues D.toCodeWords 1) *
      HStage.stable G D hintersections =
      ((HStage.simulatorEmbedding G D hintersections).hom (simulatorGridValues D.toCodeWords 2))⁻¹
    rw [show simulatorGridValues D.toCodeWords 1 = SimulatorSymmetry.xK D.toCodeWords 0 from
        (SimulatorSymmetry.xK_eq_gridValue D.toCodeWords 0).symm,
      show simulatorGridValues D.toCodeWords 2 = SimulatorSymmetry.xK D.toCodeWords 1 from
        (SimulatorSymmetry.xK_eq_gridValue D.toCodeWords 1).symm]
    exact HStage.conjugates_x1 G D hintersections
  exact DFunLike.congr_fun h w

theorem relation (a : U G × Z) :
    (HStage.stable G D hintersections)⁻¹ * baseMap G D hintersections (ProductGridHNN.left (U G) a) *
      HStage.stable G D hintersections =
      baseMap G D hintersections (ProductGridHNN.right (U G) a) := by
  rcases a with ⟨u, w⟩
  change (HStage.stable G D hintersections)⁻¹ *
      (HStage.ofEll G D hintersections
        (InputFreeSubgroup.hom G D hintersections u *
          EllGrid.right G D hintersections (ProductGridHNN.positive 1 w))) *
      HStage.stable G D hintersections =
      HStage.ofEll G D hintersections
        (InputFreeSubgroup.hom G D hintersections u *
          EllGrid.right G D hintersections (ProductGridHNN.negative 2 w))
  rw [map_mul, map_mul]
  have hU := (commutes_U G D hintersections u).inv_left.eq
  calc
    _ = (HStage.stable G D hintersections)⁻¹ *
        HStage.ofEll G D hintersections (InputFreeSubgroup.hom G D hintersections u) *
        (old G D hintersections (ProductGridHNN.positive 1 w) * HStage.stable G D hintersections) := by
          simp only [old, MonoidHom.comp_apply]; group
    _ = _ := by
      rw [hU, mul_assoc]
      congr 1
      change (HStage.stable G D hintersections)⁻¹ *
        (old G D hintersections (ProductGridHNN.positive 1 w) * HStage.stable G D hintersections) =
        old G D hintersections (ProductGridHNN.negative 2 w)
      rw [← mul_assoc, conjugates_cyclic]

/-- The parameter HNN maps into the actual `h` extension. -/
def toModel : ProductGridHNN.Model (U G) →* HStage.Model G D hintersections :=
  IdentifyingHNN.lift _ _ _ _ (baseMap G D hintersections) (HStage.stable G D hintersections)
    (relation G D hintersections)

@[simp] theorem toModel_of (a : U G × F) :
    toModel G D hintersections (ProductGridHNN.of (U G) a) = baseMap G D hintersections a :=
  IdentifyingHNN.lift_of _ _ _ _ _ _ _ a

@[simp] theorem toModel_stable :
    toModel G D hintersections (ProductGridHNN.stable (U G)) = HStage.stable G D hintersections :=
  IdentifyingHNN.lift_stable _ _ _ _ _ _ _

/-- The normal form in the parameter HNN remains reduced in the positive extension. -/
theorem toModel_injective : Function.Injective (toModel G D hintersections) := by
  apply HNNMap.identifying_injective (A₀ := U G × Z) (P₀ := U G × F)
    (C₀ := HStage.Domain G D) (M₀ := EllStage.Model G D hintersections)
    (ProductGridHNN.left (U G)) (ProductGridHNN.right (U G))
    (ProductGridHNN.left_injective (U G)) (ProductGridHNN.right_injective (U G))
    (HStage.left G D hintersections) (HStage.right G D hintersections)
    (HStage.left_injective G D hintersections) (HStage.right_injective G D hintersections)
    (EllGrid.product G D hintersections) (toModel G D hintersections)
  · intro a
    exact (ProductGridHNN.mem_left_range (U G) a).trans
      (HStageGrid.product_mem_left_iff G D hintersections a).symm
  · intro a
    exact (ProductGridHNN.mem_right_range (U G) a).trans
      (HStageGrid.product_mem_right_iff G D hintersections a).symm
  · intro a
    exact toModel_of G D hintersections a
  · exact toModel_stable G D hintersections
  · exact EllGrid.product_injective G D hintersections

/-- The free grid columns have order `x₀,x₁,h,x₃`. -/
def product : U G × F →* HStage.Model G D hintersections :=
  (toModel G D hintersections).comp (ProductGridHNN.product (U G))

/-- The new four-column product grid is faithful. -/
theorem product_injective : Function.Injective (product G D hintersections) :=
  (toModel_injective G D hintersections).comp (ProductGridHNN.product_injective (U G))

@[simp] theorem product_left (u : U G) :
    product G D hintersections (u, 1) =
      HStage.ofEll G D hintersections (InputFreeSubgroup.hom G D hintersections u) := by
  simp [product, ProductGridHNN.input, baseMap]

@[simp] theorem product_x0 :
    product G D hintersections (1, FreeGroup.of 0) =
      (HStage.simulatorEmbedding G D hintersections).hom (simulatorGridValues D.toCodeWords 0) := by
  simp [product, ProductGridHNN.old, baseMap, EllGrid.right, HStage.simulatorEmbedding]

@[simp] theorem product_x1 :
    product G D hintersections (1, FreeGroup.of 1) =
      (HStage.simulatorEmbedding G D hintersections).hom (simulatorGridValues D.toCodeWords 1) := by
  simp [product, ProductGridHNN.old, baseMap, EllGrid.right, HStage.simulatorEmbedding]

@[simp] theorem product_h :
    product G D hintersections (1, FreeGroup.of 2) = HStage.stable G D hintersections := by
  simp [product]

@[simp] theorem product_x3 :
    product G D hintersections (1, FreeGroup.of 3) =
      (HStage.simulatorEmbedding G D hintersections).hom (simulatorGridValues D.toCodeWords 3) := by
  simp [product, ProductGridHNN.old, baseMap, EllGrid.right, HStage.simulatorEmbedding]

end
end UniversalGroup.Embedding.PositiveHost.HGrid
