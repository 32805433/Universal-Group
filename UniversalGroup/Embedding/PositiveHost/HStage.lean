module

public import UniversalGroup.Embedding.PositiveHost.Symmetry
public import UniversalGroup.Host.SymmetrySubgroups

@[expose] public section

/-! The proper positive h-extension. The associated subgroups use
the exact restrictions in `Host.SymmetrySubgroups`. -/

namespace UniversalGroup.Embedding.PositiveHost.HStage
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open HNNLemmas SimulatorSymmetry
open UniversalGroup.SymmetrySubgroups

variable (G : PreparedInput) (D : ValievDatum G) (hintersections : ValievIntersections G D)

abbrev symmetryK := PositiveHost.equivK D.toCodeWords D.F_support D.E_support

include hintersections in
theorem common_map : (Common G D (minusH G D)).map (symmetryK G D).toMonoidHom =
    Common G D (plusH G D) := by
  rw [minus_common G D hintersections, plus_common G D hintersections,
    MonoidHom.map_closure, Set.image_singleton]
  simp only [symmetryK, MulEquiv.coe_toMonoidHom, PositiveHost.equivK_x1, Subgroup.closure_singleton_inv]

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

@[simp] theorem amalgamEquiv_input (x : G.presentation.Group) :
    amalgamEquiv G D hintersections
      (CentralizingAmalgam.ofInput (Common G D (minusH G D)) G.presentation.Group x) =
    CentralizingAmalgam.ofInput (Common G D (plusH G D)) G.presentation.Group x :=
  AmalgamRestriction.congrEquiv_ofInput _ _ _ _ _ x

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

@[simp] theorem extensionEquiv_of (x : M G D (minusH G D)) :
    extensionEquiv G D hintersections (centralizerOf (associated G D (minusH G D)) x) =
      centralizerOf (associated G D (plusH G D)) (amalgamEquiv G D hintersections x) := rfl

@[simp] theorem extensionEquiv_stable :
    extensionEquiv G D hintersections (centralizerStable (associated G D (minusH G D))) =
      centralizerStable (associated G D (plusH G D)) := rfl

abbrev Domain := Extension G D (minusH G D)

def left : Domain G D →* EllStage.Model G D hintersections :=
  intoEll G D hintersections (minusH G D) (minus_exact G D hintersections)

def right : Domain G D →* EllStage.Model G D hintersections :=
  (intoEll G D hintersections (plusH G D) (plus_exact G D hintersections)).comp
    (extensionEquiv G D hintersections).toMonoidHom

theorem left_injective : Function.Injective (left G D hintersections) :=
  intoEll_injective G D hintersections _ _

theorem right_injective : Function.Injective (right G D hintersections) :=
  (intoEll_injective G D hintersections (plusH G D) (plus_exact G D hintersections)).comp (extensionEquiv G D hintersections).injective

/-- Parameter elements coming from the five-letter simulator subgroup. -/
def base (x : minusH G D) : Domain G D :=
  centralizerOf (associated G D (minusH G D))
    (CentralizingAmalgam.ofBase (Common G D (minusH G D)) G.presentation.Group x)

def input (x : G.presentation.Group) : Domain G D :=
  centralizerOf (associated G D (minusH G D))
    (CentralizingAmalgam.ofInput (Common G D (minusH G D)) G.presentation.Group x)

def ellParameter : Domain G D := (centralizerStable (associated G D (minusH G D)))⁻¹

@[simp] theorem left_base (x : minusH G D) :
    left G D hintersections (base G D x) =
      (EllStage.simulatorEmbedding G D hintersections).hom x := by
  simp only [left, base, intoEll_of, intoM_base, EllStage.simulatorEmbedding, MonoidHom.comp_apply]

@[simp] theorem right_base (x : minusH G D) :
    right G D hintersections (base G D x) =
      (EllStage.simulatorEmbedding G D hintersections).hom (symmetryK G D x) := by
  simp only [right, base, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    extensionEquiv_of, amalgamEquiv_base, intoEll_of, intoM_base, EllStage.simulatorEmbedding]

@[simp] theorem left_input (x : G.presentation.Group) :
    left G D hintersections (input G D x) = (EllStage.inputEmbedding G D hintersections).hom x := by
  simp only [left, input, intoEll_of, intoM_input, EllStage.inputEmbedding, MonoidHom.comp_apply]

@[simp] theorem right_input (x : G.presentation.Group) :
    right G D hintersections (input G D x) = (EllStage.inputEmbedding G D hintersections).hom x := by
  simp only [right, input, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    extensionEquiv_of, amalgamEquiv_input, intoEll_of, intoM_input, EllStage.inputEmbedding]

@[simp] theorem left_ellParameter :
    left G D hintersections (ellParameter G D) = EllStage.ell G D hintersections := by
  simp [left, ellParameter]

@[simp] theorem right_ellParameter :
    right G D hintersections (ellParameter G D) = EllStage.ell G D hintersections := by
  simp [right, ellParameter]

/-- The actual HNN extension adjoining the stable letter `h`. -/
abbrev Model := IdentifyingHNN (left G D hintersections) (right G D hintersections)
  (left_injective G D hintersections) (right_injective G D hintersections)

def ofEll : EllStage.Model G D hintersections →* Model G D hintersections :=
  IdentifyingHNN.of _ _ _ _

def stable : Model G D hintersections := IdentifyingHNN.stable _ _ _ _

theorem ofEll_injective : Function.Injective (ofEll G D hintersections) := IdentifyingHNN.of_injective _ _ _ _

def inputEmbedding : GroupEmbedding G.presentation.Group (Model G D hintersections) :=
  ⟨(ofEll G D hintersections).comp (EllStage.inputEmbedding G D hintersections).hom,
    (ofEll_injective G D hintersections).comp (EllStage.inputEmbedding G D hintersections).injective⟩

def simulatorEmbedding : GroupEmbedding (simulatorK D.toCodeWords).Group (Model G D hintersections) :=
  ⟨(ofEll G D hintersections).comp (EllStage.simulatorEmbedding G D hintersections).hom,
    (ofEll_injective G D hintersections).comp (EllStage.simulatorEmbedding G D hintersections).injective⟩

theorem conjugates (x : Domain G D) :
    (stable G D hintersections)⁻¹ * ofEll G D hintersections (left G D hintersections x) *
      stable G D hintersections = ofEll G D hintersections (right G D hintersections x) :=
  IdentifyingHNN.conjugates _ _ _ _ x

theorem conjugates_base (x : minusH G D) :
    (stable G D hintersections)⁻¹ * (simulatorEmbedding G D hintersections).hom x *
      stable G D hintersections =
      (simulatorEmbedding G D hintersections).hom (symmetryK G D x) := by
  simpa [simulatorEmbedding] using conjugates G D hintersections (base G D x)

theorem commutes_input (x : G.presentation.Group) :
    Commute (stable G D hintersections) ((inputEmbedding G D hintersections).hom x) := by
  have h := conjugates G D hintersections (input G D x)
  rw [left_input, right_input] at h
  have hh := congrArg (fun z => stable G D hintersections * z) h
  simpa [commute_iff_eq, inputEmbedding, mul_assoc] using hh.symm

theorem commutes_ell :
    Commute (stable G D hintersections) (ofEll G D hintersections (EllStage.ell G D hintersections)) := by
  have h := conjugates G D hintersections (ellParameter G D)
  rw [left_ellParameter, right_ellParameter] at h
  have hh := congrArg (fun z => stable G D hintersections * z) h
  simpa [commute_iff_eq, mul_assoc] using hh.symm

/-- The old seven-letter simulator interpreted after the `h` extension. -/
def ofL : (simulatorL D.toCodeWords).Group →* Model G D hintersections :=
  (simulatorEmbedding G D hintersections).hom.comp (simulatorInclusion D.toCodeWords)

theorem conjugates_d :
    (stable G D hintersections)⁻¹ * ofL G D hintersections (SimulatorRelations.d D.toCodeWords) *
      stable G D hintersections = ofL G D hintersections (e0 D.toCodeWords) := by
  simpa [symmetryK, ofL, minusValues, plusValues] using
    conjugates_base G D hintersections (minusElementK D.toCodeWords 0)

theorem conjugates_e0 :
    (stable G D hintersections)⁻¹ * ofL G D hintersections (e0 D.toCodeWords) *
      stable G D hintersections = ofL G D hintersections (SimulatorRelations.d D.toCodeWords) := by
  simpa [symmetryK, ofL, minusValues, plusValues] using
    conjugates_base G D hintersections (minusElementK D.toCodeWords 1)

theorem conjugates_f :
    (stable G D hintersections)⁻¹ * ofL G D hintersections (SimulatorRelations.f D.toCodeWords) *
      stable G D hintersections = ofL G D hintersections (q0 D.toCodeWords) := by
  simpa [symmetryK, ofL, minusValues, plusValues] using
    conjugates_base G D hintersections (minusElementK D.toCodeWords 3)

theorem conjugates_x1 :
    (stable G D hintersections)⁻¹ * ofL G D hintersections (x D.toCodeWords 0) *
      stable G D hintersections = (ofL G D hintersections (x D.toCodeWords 1))⁻¹ := by
  simpa [symmetryK, ofL, minusValues, plusValues] using
    conjugates_base G D hintersections (minusElementK D.toCodeWords 4)

theorem commutes_c :
    Commute (stable G D hintersections)
      ((simulatorEmbedding G D hintersections).hom (generators (simulatorK D.toCodeWords) 0)) := by
  have h := conjugates_base G D hintersections (minusElementK D.toCodeWords 2)
  have hc : (stable G D hintersections)⁻¹ *
      (simulatorEmbedding G D hintersections).hom (generators (simulatorK D.toCodeWords) 0) *
      stable G D hintersections =
      (simulatorEmbedding G D hintersections).hom (generators (simulatorK D.toCodeWords) 0) := by
    simpa [symmetryK, minusValues, plusValues, simulatorInclusion, SimulatorRelations.c, generators] using h
  have hh := congrArg (fun z => stable G D hintersections * z) hc
  simpa [commute_iff_eq, mul_assoc] using hh.symm

/-- The two positive conjugacy equations make h² centralize d. -/
theorem commutes_d_square :
    Commute (ofL G D hintersections (SimulatorRelations.d D.toCodeWords))
      (stable G D hintersections ^ 2) := by
  have hd := conjugates_d G D hintersections
  have he := conjugates_e0 G D hintersections
  rw [← hd] at he
  rw [commute_iff_eq]
  have hh := congrArg (fun z => stable G D hintersections ^ 2 * z) he
  simpa [pow_two, mul_assoc] using hh

end
end UniversalGroup.Embedding.PositiveHost.HStage
