module

public import UniversalGroup.Simulator.Symmetry.CodeIntersections
public import UniversalGroup.Foundations.Amalgam.Restriction
public import UniversalGroup.Foundations.HNN.CentralizerIntoHNN

@[expose] public section

/-!
# Associated subgroups after adjoining the input and `ell`

The exact subgroup restrictions and their equivalence supply the common
infrastructure for the positive symmetry and its product-grid intersection.
-/

namespace UniversalGroup.SymmetrySubgroups
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open HNNLemmas

variable (G : PreparedInput) (D : ValievDatum G) (hintersections : ValievIntersections G D)

/-- The diagonal identification fixes every element of the four-letter grid. -/
theorem right_eq_left (a : EllStage.Domain G D hintersections)
    (ha : EllStage.toK G D hintersections a ∈ simulatorGrid D.toCodeWords) :
    EllStage.right G D hintersections a = EllStage.left G D hintersections a := by
  apply EllStage.ofM_injective G D hintersections
  have h := EllStage.conjugates G D hintersections a
  have hc := EllStage.commutes_grid G D hintersections
    ⟨EllStage.toK G D hintersections a, ha⟩
  change Commute (EllStage.ell G D hintersections)
    (EllStage.ofM G D hintersections (EllStage.left G D hintersections a)) at hc
  rw [← h]
  calc
    _ = (EllStage.ell G D hintersections)⁻¹ *
        (EllStage.ofM G D hintersections (EllStage.left G D hintersections a) *
          EllStage.ell G D hintersections) := by group
    _ = _ := by rw [← hc.eq]; group

section Restricted
variable (H : Subgroup (simulatorK D.toCodeWords).Group)
  (hC : (EllStage.toK G D hintersections).range ⊓ H = simulatorGrid D.toCodeWords ⊓ H)

abbrev Common := AmalgamRestriction.Common (simulatorGrid D.toCodeWords) H
abbrev M := AmalgamRestriction.Source (simulatorGrid D.toCodeWords) H G.presentation.Group

def intoM : M G D H →* InputAmalgam G D.toCodeWords :=
  AmalgamRestriction.hom (simulatorGrid D.toCodeWords) H G.presentation.Group

theorem intoM_injective : Function.Injective (intoM G D H) :=
  AmalgamRestriction.hom_injective _ _ _

@[simp] theorem intoM_base (x : H) :
    intoM G D H (CentralizingAmalgam.ofBase (Common G D H) G.presentation.Group x) =
      EllStage.ofK G D x := AmalgamRestriction.hom_ofBase _ _ _ x

@[simp] theorem intoM_input (x : G.presentation.Group) :
    intoM G D H (CentralizingAmalgam.ofInput (Common G D H) G.presentation.Group x) =
      (inputAmalgamEmbedding G D.toCodeWords).hom x := AmalgamRestriction.hom_ofInput _ _ _ x

@[simp] theorem rho_intoM (x : M G D H) :
    EllStage.rho G D (intoM G D H x) =
      (CentralizingAmalgam.toBase (Common G D H) G.presentation.Group x : (simulatorK D.toCodeWords).Group) :=
  AmalgamRestriction.toBase_hom _ _ _ x

/-- The common cyclic subgroup, viewed inside the restricted input amalgam. -/
def associated : Subgroup (M G D H) :=
  (Common G D H).map (CentralizingAmalgam.ofBase (Common G D H) G.presentation.Group)

include hC in
theorem mem_left (x : M G D H) :
    x ∈ associated G D H ↔ intoM G D H x ∈ (EllStage.left G D hintersections).range := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨w, hw⟩ := EllStage.grid_le_domain_range G D hintersections ha
    refine ⟨w, ?_⟩
    change EllStage.ofK G D (EllStage.toK G D hintersections w) = _
    rw [hw, intoM_base]
    rfl
  · rintro ⟨a, ha⟩
    have hxbase : intoM G D H x ∈ (EllStage.ofK G D).range :=
      ⟨EllStage.toK G D hintersections a, ha⟩
    obtain ⟨b, hb⟩ := AmalgamRestriction.preimage_base
      (simulatorGrid D.toCodeWords) H G.presentation.Group x hxbase
    have heq : EllStage.toK G D hintersections a = (b : (simulatorK D.toCodeWords).Group) := by
      apply CentralizingAmalgam.ofBase_injective (simulatorGrid D.toCodeWords) G.presentation.Group
      exact ha.trans ((congrArg (intoM G D H) hb).symm.trans (intoM_base G D H b))
    have hbgrid : (b : (simulatorK D.toCodeWords).Group) ∈ simulatorGrid D.toCodeWords := by
      have hh : (b : (simulatorK D.toCodeWords).Group) ∈ (EllStage.toK G D hintersections).range ⊓ H :=
        ⟨⟨a, heq⟩, b.property⟩
      rw [hC] at hh
      exact hh.1
    exact ⟨b, hbgrid, hb⟩

include hC in
theorem mem_right (x : M G D H) :
    x ∈ associated G D H ↔ intoM G D H x ∈ (EllStage.right G D hintersections).range := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (mem_left G D hintersections H hC x).mp hx
    have hagrid : EllStage.toK G D hintersections a ∈ simulatorGrid D.toCodeWords := by
      rcases hx with ⟨b, hb, rfl⟩
      have hh := congrArg (EllStage.rho G D) ha
      change ((EllStage.rho G D).comp (EllStage.left G D hintersections)) a = _ at hh
      rw [EllStage.rho_comp_left, rho_intoM, CentralizingAmalgam.toBase_ofBase] at hh
      exact hh ▸ hb
    exact ⟨a, (right_eq_left G D hintersections a hagrid).trans ha⟩
  · rintro ⟨a, ha⟩
    have hH : EllStage.toK G D hintersections a ∈ H := by
      have hh := congrArg (EllStage.rho G D) ha
      change ((EllStage.rho G D).comp (EllStage.right G D hintersections)) a = _ at hh
      rw [EllStage.rho_comp_right, rho_intoM] at hh
      exact hh ▸ (CentralizingAmalgam.toBase (Common G D H) G.presentation.Group x).property
    have hagrid : EllStage.toK G D hintersections a ∈ simulatorGrid D.toCodeWords := by
      have hh : EllStage.toK G D hintersections a ∈
          (EllStage.toK G D hintersections).range ⊓ H := ⟨⟨a, rfl⟩, hH⟩
      rw [hC] at hh
      exact hh.1
    apply (mem_left G D hintersections H hC x).mpr
    exact ⟨a, (right_eq_left G D hintersections a hagrid).symm.trans ha⟩

include hC in
theorem fixes_associated (x : associated G D H) :
    ((UniversalGroup.rangeEquiv (EllStage.left G D hintersections) (EllStage.right G D hintersections)
      (EllStage.left_injective G D hintersections) (EllStage.right_injective G D hintersections)
        ⟨intoM G D H x, (mem_left G D hintersections H hC x).mp x.property⟩) : InputAmalgam G D.toCodeWords) =
      intoM G D H x := by
  obtain ⟨a, ha⟩ := (mem_left G D hintersections H hC x).mp x.property
  have hagrid : EllStage.toK G D hintersections a ∈ simulatorGrid D.toCodeWords := by
    rcases x.property with ⟨b, hb, hbx⟩
    have hh := congrArg (EllStage.rho G D) (ha.trans (congrArg (intoM G D H) hbx).symm)
    change ((EllStage.rho G D).comp (EllStage.left G D hintersections)) a = _ at hh
    rw [EllStage.rho_comp_left, rho_intoM, CentralizingAmalgam.toBase_ofBase] at hh
    exact hh ▸ hb
  have he : (⟨intoM G D H x, (mem_left G D hintersections H hC x).mp x.property⟩ :
      (EllStage.left G D hintersections).range) = ⟨EllStage.left G D hintersections a, ⟨a, rfl⟩⟩ :=
    Subtype.ext ha.symm
  rw [he, UniversalGroup.rangeEquiv_apply_range, right_eq_left G D hintersections a hagrid, ha]

abbrev Extension := CentralizerHNN (M G D H) (associated G D H)

def intoEll : Extension G D H →* EllStage.Model G D hintersections :=
  CentralizerIntoHNN.hom _ _ _ _ (intoM G D H)
    (mem_left G D hintersections H hC) (fixes_associated G D hintersections H hC)

theorem intoEll_injective : Function.Injective (intoEll G D hintersections H hC) :=
  CentralizerIntoHNN.hom_injective _ _ _ _ _ (mem_left G D hintersections H hC)
    (mem_right G D hintersections H hC) (fixes_associated G D hintersections H hC)
    (intoM_injective G D H)

@[simp] theorem intoEll_of (x : M G D H) :
    intoEll G D hintersections H hC (centralizerOf (associated G D H) x) =
      EllStage.ofM G D hintersections (intoM G D H x) := by
  exact CentralizerIntoHNN.hom_of _ _ _ _ _ _ _ x

@[simp] theorem intoEll_stable :
    intoEll G D hintersections H hC (centralizerStable (associated G D H)) =
      (EllStage.ell G D hintersections)⁻¹ := by
  simp [intoEll, EllStage.ell, IdentifyingHNN.stable]

end Restricted

open SimulatorSymmetry
abbrev minusH := HMinusK D.toCodeWords
abbrev plusH := HPlusK D.toCodeWords

abbrev symmetryK := equivK D.toCodeWords D.F_support D.E_support

theorem minus_exact : (EllStage.toK G D hintersections).range ⊓ minusH G D =
    simulatorGrid D.toCodeWords ⊓ minusH G D := by
  rw [minusH, domain_inf_HMinusK G D hintersections, grid_inf_HMinusK G D hintersections]

theorem plus_exact : (EllStage.toK G D hintersections).range ⊓ plusH G D =
    simulatorGrid D.toCodeWords ⊓ plusH G D := by
  rw [plusH, domain_inf_HPlusK G D hintersections, grid_inf_HPlusK G D hintersections]

include hintersections in
theorem minus_common : Common G D (minusH G D) =
    Subgroup.closure ({minusElementK D.toCodeWords 4} : Set _) := by
  apply Subgroup.map_injective (f := (minusH G D).subtype) Subtype.val_injective
  rw [show (Common G D (minusH G D)).map (minusH G D).subtype =
      simulatorGrid D.toCodeWords ⊓ minusH G D from Subgroup.subgroupOf_map_subtype _ _]
  rw [grid_inf_HMinusK G D hintersections, MonoidHom.map_closure, Set.image_singleton]
  rfl

include hintersections in
theorem plus_common : Common G D (plusH G D) =
    Subgroup.closure ({plusElementK D.toCodeWords 4} : Set _) := by
  apply Subgroup.map_injective (f := (plusH G D).subtype) Subtype.val_injective
  rw [show (Common G D (plusH G D)).map (plusH G D).subtype =
      simulatorGrid D.toCodeWords ⊓ plusH G D from Subgroup.subgroupOf_map_subtype _ _]
  rw [grid_inf_HPlusK G D hintersections, MonoidHom.map_closure, Set.image_singleton]
  rfl

include hintersections in
theorem common_map : (Common G D (minusH G D)).map (symmetryK G D).toMonoidHom =
    Common G D (plusH G D) := by
  rw [minus_common G D hintersections, plus_common G D hintersections,
    MonoidHom.map_closure, Set.image_singleton]
  simp only [symmetryK, MulEquiv.coe_toMonoidHom, equivK_x1, Subgroup.closure_singleton_inv]

include hintersections in
theorem common_mem (x : minusH G D) :
    x ∈ Common G D (minusH G D) ↔ symmetryK G D x ∈ Common G D (plusH G D) := by
  rw [← common_map G D hintersections]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    exact (symmetryK G D).injective heq ▸ hy

/-- Extend the five-letter symmetry across the input amalgam. -/
def amalgamEquiv : M G D (minusH G D) ≃* M G D (plusH G D) :=
  AmalgamRestriction.congrEquiv (Common G D (minusH G D)) G.presentation.Group
    (Common G D (plusH G D)) (symmetryK G D) (common_mem G D hintersections)

@[simp] theorem amalgamEquiv_base (x : minusH G D) :
    amalgamEquiv G D hintersections
      (CentralizingAmalgam.ofBase (Common G D (minusH G D)) G.presentation.Group x) =
    CentralizingAmalgam.ofBase (Common G D (plusH G D)) G.presentation.Group (symmetryK G D x) :=
  AmalgamRestriction.congrEquiv_ofBase _ _ _ _ _ x

theorem associated_map : (associated G D (minusH G D)).map
    (amalgamEquiv G D hintersections).toMonoidHom = associated G D (plusH G D) := by
  rw [associated, Subgroup.map_map]
  have h : (amalgamEquiv G D hintersections).toMonoidHom.comp
      (CentralizingAmalgam.ofBase (Common G D (minusH G D)) G.presentation.Group) =
      (CentralizingAmalgam.ofBase (Common G D (plusH G D)) G.presentation.Group).comp
        (symmetryK G D).toMonoidHom := by
    ext x
    exact amalgamEquiv_base G D hintersections x
  rw [h, ← Subgroup.map_map, common_map G D hintersections]
  rfl

def associatedEquiv : associated G D (minusH G D) ≃* associated G D (plusH G D) :=
  ((amalgamEquiv G D hintersections).subgroupMap (associated G D (minusH G D))).trans
    (MulEquiv.subgroupCongr (associated_map G D hintersections))

/-- The single-letter symmetry extends further while fixing `ell`. -/
def extensionEquiv : Extension G D (minusH G D) ≃* Extension G D (plusH G D) :=
  HNNLemmas.congr (amalgamEquiv G D hintersections)
    (associatedEquiv G D hintersections) (associatedEquiv G D hintersections)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

abbrev Domain := Extension G D (minusH G D)

def left : Domain G D →* EllStage.Model G D hintersections :=
  intoEll G D hintersections (minusH G D) (minus_exact G D hintersections)

def right : Domain G D →* EllStage.Model G D hintersections :=
  (intoEll G D hintersections (plusH G D) (plus_exact G D hintersections)).comp
    (extensionEquiv G D hintersections).toMonoidHom

end
end UniversalGroup.SymmetrySubgroups
