module

public import UniversalGroup.Host.InputFreeSubgroup
public import UniversalGroup.Simulator.Grid

@[expose] public section

/-! The exact product grid `U × F(x₀,x₁,x₂,x₃)` after adjoining `ell`. -/

namespace UniversalGroup.EllGrid

noncomputable section
variable (G : PreparedInput) (D : ValievDatum G) (hintersections : ValievIntersections G D)

def right : FreeGroup (Fin 4) →* EllStage.Model G D hintersections :=
  (EllStage.simulatorEmbedding G D hintersections).hom.comp (SimulatorGrid.lift D.toCodeWords)

theorem right_injective : Function.Injective (right G D hintersections) :=
  (EllStage.simulatorEmbedding G D hintersections).injective.comp
    (SimulatorGrid.lift_injective D.toCodeWords D.F_support D.E_support)

theorem commute (u : InputFreeSubgroup.Domain G) (v : FreeGroup (Fin 4)) :
    Commute (InputFreeSubgroup.hom G D hintersections u) (right G D hintersections v) := by
  let x : simulatorGrid D.toCodeWords := ⟨SimulatorGrid.lift D.toCodeWords v,
    (SimulatorGrid.lift_range D.toCodeWords) ▸ ⟨v, rfl⟩⟩
  induction u using Monoid.Coprod.induction_on with
  | inl p =>
    induction p using Monoid.Coprod.induction_on with
    | inl z =>
      rw [InputFreeSubgroup.hom_c]
      have h := (SimulatorGrid.c_commute_grid D.toCodeWords x).map
        (EllStage.simulatorEmbedding G D hintersections).hom
      have hc : simulatorInclusion D.toCodeWords (SimulatorRelations.c D.toCodeWords) =
          generators (simulatorK D.toCodeWords) 0 := by
        simp [simulatorInclusion, SimulatorRelations.c, generators]
      rw [hc] at h
      simpa [InputFreeSubgroup.cPowers, zpowersHom_apply, right] using
        h.zpow_left (Multiplicative.toAdd z)
    | inr g =>
      rw [InputFreeSubgroup.hom_input]
      have h := (CentralizingAmalgam.commute (simulatorGrid D.toCodeWords)
        G.presentation.Group x g).symm.map (EllStage.ofM G D hintersections)
      exact h
    | mul p q hp hq =>
      simpa only [map_mul] using hp.mul_left hq
  | inr z =>
    rw [InputFreeSubgroup.hom_ell]
    exact (EllStage.commutes_grid G D hintersections x).zpow_left (Multiplicative.toAdd z)
  | mul p q hp hq =>
    simpa only [map_mul] using hp.mul_left hq

theorem disjoint : Disjoint (MonoidHom.range (G := InputFreeSubgroup.Domain G) (InputFreeSubgroup.hom G D hintersections))
    (right G D hintersections).range := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hu, v, rfl⟩
  have hx : right G D hintersections v ∈
      (MonoidHom.range (G := InputFreeSubgroup.Domain G) (InputFreeSubgroup.hom G D hintersections)) ⊓
        (EllStage.simulatorEmbedding G D hintersections).hom.range :=
    ⟨hu, SimulatorGrid.lift D.toCodeWords v, rfl⟩
  rw [InputFreeSubgroup.hom_inf_simulator] at hx
  obtain ⟨z, hz⟩ := hx
  have h := (EllStage.simulatorEmbedding G D hintersections).injective hz
  have he := congrArg (InputFreeSubgroup.cExponent D.toCodeWords) h
  have hzero : InputFreeSubgroup.cExponent D.toCodeWords (SimulatorGrid.lift D.toCodeWords v) = 1 :=
    InputFreeSubgroup.cExponent_grid D.toCodeWords
      ⟨_, (SimulatorGrid.lift_range D.toCodeWords) ▸ ⟨v, rfl⟩⟩
  have hz1 : z = 1 := by
    rw [hzero] at he
    change ((InputFreeSubgroup.cExponent D.toCodeWords).comp
      (InputFreeSubgroup.cPowers D.toCodeWords)) z = 1 at he
    simpa only [InputFreeSubgroup.cExponent_comp_cPowers, MonoidHom.id_apply] using he
  change right G D hintersections v = 1
  rw [← hz, hz1, map_one]

def product : InputFreeSubgroup.Domain G × FreeGroup (Fin 4) →*
    EllStage.Model G D hintersections :=
  (InputFreeSubgroup.hom G D hintersections).noncommCoprod
    (right G D hintersections) (commute G D hintersections)

/-- Both factors embed and their images have trivial intersection. -/
theorem product_injective : Function.Injective (product G D hintersections) := by
  have hinv (u : InputFreeSubgroup.Domain G) :
      InputFreeSubgroup.hom G D hintersections u⁻¹ =
        (InputFreeSubgroup.hom G D hintersections u)⁻¹ := by
    apply mul_eq_one_iff_eq_inv.mp
    rw [← map_mul, inv_mul_cancel u, map_one]
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  change InputFreeSubgroup.hom G D hintersections u * right G D hintersections v =
    InputFreeSubgroup.hom G D hintersections u' * right G D hintersections v' at h
  have huv : InputFreeSubgroup.hom G D hintersections (u⁻¹ * u') =
      right G D hintersections (v * v'⁻¹) := by
    simp only [map_mul, map_inv, hinv]
    have hh := congrArg (fun z => (InputFreeSubgroup.hom G D hintersections u)⁻¹ * z *
      (right G D hintersections v')⁻¹) h
    simpa [mul_assoc] using hh.symm
  have hm : InputFreeSubgroup.hom G D hintersections (u⁻¹ * u') ∈
      (MonoidHom.range (G := InputFreeSubgroup.Domain G) (InputFreeSubgroup.hom G D hintersections)) ⊓
        (right G D hintersections).range :=
    ⟨⟨u⁻¹ * u', rfl⟩, v * v'⁻¹, huv.symm⟩
  have hu : InputFreeSubgroup.hom G D hintersections (u⁻¹ * u') = 1 :=
    (disjoint G D hintersections).le_bot hm
  have huu : InputFreeSubgroup.hom G D hintersections u =
      InputFreeSubgroup.hom G D hintersections u' := by
    have hh : (InputFreeSubgroup.hom G D hintersections u)⁻¹ *
        InputFreeSubgroup.hom G D hintersections u' = 1 := by
      simpa only [map_mul, hinv] using hu
    exact inv_mul_eq_one.mp hh
  have hvv : right G D hintersections v = right G D hintersections v' := by
    rw [huu] at h
    exact mul_left_cancel h
  exact Prod.ext (InputFreeSubgroup.hom_injective G D hintersections huu)
    (right_injective G D hintersections hvv)

@[simp] theorem product_left (u : InputFreeSubgroup.Domain G) :
    product G D hintersections (u, 1) = InputFreeSubgroup.hom G D hintersections u := by
  simp [product]

@[simp] theorem product_right (v : FreeGroup (Fin 4)) :
    product G D hintersections (1, v) = right G D hintersections v := by
  simp [product]

end
end UniversalGroup.EllGrid
