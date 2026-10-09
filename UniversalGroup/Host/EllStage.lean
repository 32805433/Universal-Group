module

public import UniversalGroup.Host.EllAlgebra
public import UniversalGroup.Simulator.Centralizer
public import UniversalGroup.Foundations.Amalgam.Conjugated
public import UniversalGroup.Foundations.HNN.Identifying
public import UniversalGroup.Host.InputAmalgam

@[expose] public section

/-!
The genuine `ell` extension of the changed input amalgam.  The attaching
maps are built from the free basis of `A`, the recognized subgroup, and the
normal form for the two conjugated factors.  Both attaching maps are proved
injective before constructing the HNN extension.
-/

namespace UniversalGroup.EllStage

noncomputable section
set_option maxHeartbeats 1600000
open PositiveEvaluation

variable (G : PreparedInput) (D : ValievDatum G)

def ofK : (simulatorK D.toCodeWords).Group →* InputAmalgam G D.toCodeWords :=
  CentralizingAmalgam.ofBase (simulatorGrid D.toCodeWords) G.presentation.Group

def ofL : (simulatorL D.toCodeWords).Group →* InputAmalgam G D.toCodeWords :=
  (ofK G D).comp (simulatorInclusion D.toCodeWords)

def rho : InputAmalgam G D.toCodeWords →* (simulatorK D.toCodeWords).Group :=
  CentralizingAmalgam.toBase (simulatorGrid D.toCodeWords) G.presentation.Group

def u (i : Fin 2) : InputAmalgam G D.toCodeWords :=
  (inputAmalgamEmbedding G D.toCodeWords).hom (generators G.presentation i)

@[simp] theorem rho_ofK (x : (simulatorK D.toCodeWords).Group) : rho G D (ofK G D x) = x :=
  CentralizingAmalgam.toBase_ofBase _ _ x

@[simp] theorem rho_ofL (x : (simulatorL D.toCodeWords).Group) :
    rho G D (ofL G D x) = simulatorInclusion D.toCodeWords x := by
  change rho G D (ofK G D _) = _
  simp

@[simp] theorem rho_u (i : Fin 2) : rho G D (u G D i) = 1 :=
  CentralizingAmalgam.toBase_ofInput _ _ _

def aEquiv : FreeGroup (Fin 5) ≃* simulatorA D.toCodeWords :=
  (MonoidHom.ofInjective (CodeSubgroups.aLift_injective G D)).trans
    (MulEquiv.subgroupCongr (CodeSubgroups.aLift_range D.toCodeWords))

@[simp] theorem aEquiv_val (w : FreeGroup (Fin 5)) :
    (aEquiv G D w : (simulatorL D.toCodeWords).Group) = CodeSubgroups.aLift D.toCodeWords w := rfl

@[simp] theorem aEquiv_symm_val (a : simulatorA D.toCodeWords) :
    CodeSubgroups.aLift D.toCodeWords ((aEquiv G D).symm a) = a :=
  congrArg Subtype.val ((aEquiv G D).apply_symm_apply a)

def a (i : Fin 5) : InputAmalgam G D.toCodeWords := ofL G D (CodeSubgroups.aValues D.toCodeWords i)
def f : InputAmalgam G D.toCodeWords := ofL G D (SimulatorRelations.f D.toCodeWords)

theorem u_commute_x (i : Fin 2) (j : Fin 3) :
    Commute (u G D i)
      (ofL G D ((simulatorL D.toCodeWords).evalWord (simulatorLWords.x D.toCodeWords j))) := by
  exact inputAmalgam_commute G D.toCodeWords i j.succ

theorem conjugated_u_commute_s (i j : Fin 2) :
    Commute (f G D * u G D i * (f G D)⁻¹)
      (ofL G D (SimulatorRelations.s D.toCodeWords j)) := by
  have h := (u_commute_x G D i j.castSucc).map (MulAut.conj (f G D)).toMonoidHom
  have hx : ofL G D ((simulatorL D.toCodeWords).evalWord (simulatorLWords.x D.toCodeWords j.castSucc)) =
      (f G D)⁻¹ * ofL G D (SimulatorRelations.s D.toCodeWords j) * f G D := by
    fin_cases j <;>
      simp [FP.evalWord, SimulatorWords.x, simulatorLWords,
        SimulatorRelations.s, SimulatorRelations.f, f, generators, mul_assoc]
  rw [hx] at h
  simpa [MulAut.conj_apply, mul_assoc] using h

theorem conjugated_u_commute_code (i j : Fin 2) :
    Commute (f G D * u G D i * (f G D)⁻¹) (![a G D 0, a G D 1] j) := by
  have h := value_commute (f G D * u G D i * (f G D)⁻¹)
    (fun j => ofL G D (SimulatorRelations.s D.toCodeWords j))
    (conjugated_u_commute_s G D i) (D.code j)
  rw [← map_value, ← EllAlgebra.positive_eq_value] at h
  fin_cases j <;> simpa [a, EllAlgebra.aValues_eq] using h

def rawRightA : FreeGroup (Fin 5) →* InputAmalgam G D.toCodeWords :=
  EllAlgebra.diagonal (a G D) (u G D) (f G D)

theorem rho_comp_rawRightA :
    (rho G D).comp (rawRightA G D) =
      (simulatorInclusion D.toCodeWords).comp (CodeSubgroups.aLift D.toCodeWords) := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [rawRightA, EllAlgebra.diagonal, a]

theorem rawRightA_deltaWord (w : PositiveWord) (hw : PositiveEq G.monoidRules w []) :
    rawRightA G D (EllAlgebra.deltaWord D.toCodeWords w) = ofL G D (simulatorDelta D.toCodeWords w) := by
  have hu : value (u G D) w = 1 := by
    change value (fun i => (inputAmalgamEmbedding G D.toCodeWords).hom
      (generators G.presentation i)) w = 1
    rw [← map_value, G.recognized_value_eq_one w hw, map_one]
  rw [rawRightA, EllAlgebra.diagonal_deltaWord _ _ _ _
    (conjugated_u_commute_code G D) w hu]
  have heq : FreeGroup.lift (a G D) = (ofL G D).comp (CodeSubgroups.aLift D.toCodeWords) := by
    apply FreeGroup.ext_hom
    intro i
    simp [a]
  rw [heq, MonoidHom.comp_apply, EllAlgebra.aLift_deltaWord]

def rightA : simulatorA D.toCodeWords →* InputAmalgam G D.toCodeWords :=
  (rawRightA G D).comp (aEquiv G D).symm.toMonoidHom

@[simp] theorem rightA_aEquiv (w : FreeGroup (Fin 5)) :
    rightA G D (aEquiv G D w) = rawRightA G D w := by
  simp [rightA]

theorem rho_rightA (x : simulatorA D.toCodeWords) :
    rho G D (rightA G D x) = simulatorInclusion D.toCodeWords x := by
  change ((rho G D).comp (rawRightA G D)) ((aEquiv G D).symm x) = _
  rw [rho_comp_rawRightA, MonoidHom.comp_apply, aEquiv_symm_val]

theorem rightA_recognized {x : (simulatorL D.toCodeWords).Group}
    (hx : x ∈ recognitionSubgroup G D.toCodeWords) (ha : x ∈ simulatorA D.toCodeWords) :
    rightA G D ⟨x, ha⟩ = ofL G D x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have heq : (⟨simulatorDelta D.toCodeWords w, ha⟩ : simulatorA D.toCodeWords) =
        aEquiv G D (EllAlgebra.deltaWord D.toCodeWords w) := by
      apply Subtype.ext
      exact (EllAlgebra.aLift_deltaWord D.toCodeWords w).symm
    rw [heq, rightA_aEquiv, rawRightA_deltaWord G D w hw]
  | one => change rightA G D 1 = ofL G D 1; simp
  | mul x y hx hy ihx ihy =>
    have hxA : x ∈ simulatorA D.toCodeWords := by
      exact (Subgroup.closure_le (simulatorA D.toCodeWords)).mpr (by
        rintro _ ⟨w, hw, rfl⟩
        rw [← CodeSubgroups.aLift_range]
        exact ⟨EllAlgebra.deltaWord D.toCodeWords w, EllAlgebra.aLift_deltaWord D.toCodeWords w⟩) hx
    have hyA : y ∈ simulatorA D.toCodeWords := by
      exact (Subgroup.closure_le (simulatorA D.toCodeWords)).mpr (by
        rintro _ ⟨w, hw, rfl⟩
        rw [← CodeSubgroups.aLift_range]
        exact ⟨EllAlgebra.deltaWord D.toCodeWords w, EllAlgebra.aLift_deltaWord D.toCodeWords w⟩) hy
    change rightA G D (⟨x, hxA⟩ * ⟨y, hyA⟩) = _
    rw [map_mul, ihx hxA, ihy hyA, map_mul]
  | inv x hx ih =>
    have hxA : x ∈ simulatorA D.toCodeWords := (simulatorA D.toCodeWords).inv_mem_iff.mp ha
    change rightA G D (⟨x, hxA⟩)⁻¹ = _
    rw [map_inv, ih hxA, map_inv]

variable (hintersections : ValievIntersections G D)
section Common
include hintersections

theorem common_le_A : recognitionSubgroup G D.toCodeWords ≤ simulatorA D.toCodeWords := by
  rw [← hintersections.1]
  exact inf_le_right

theorem common_le_B : recognitionSubgroup G D.toCodeWords ≤ simulatorB D.toCodeWords := by
  rw [← hintersections.2]
  exact inf_le_right

theorem common_le_D : recognitionSubgroup G D.toCodeWords ≤ simulatorD D.toCodeWords := by
  rw [← hintersections.1]
  exact inf_le_left

end Common

/-- Abstract parameter group of the two subgroups identified by `ell`. -/
abbrev Domain := ConjugatedAmalgam.Amalgam
  (simulatorA D.toCodeWords) (simulatorB D.toCodeWords)
  (recognitionSubgroup G D.toCodeWords)
  (common_le_A G D hintersections) (common_le_B G D hintersections)

abbrev inA : simulatorA D.toCodeWords →* Domain G D hintersections :=
  ConjugatedAmalgam.inA _ _ _ _ _
abbrev inB : simulatorB D.toCodeWords →* Domain G D hintersections :=
  ConjugatedAmalgam.inB _ _ _ _ _

/-- The proper conjugated amalgam inside the literal `K` presentation. -/
def toK : Domain G D hintersections →* (simulatorK D.toCodeWords).Group :=
  (SimulatorCentralizer.equiv D.toCodeWords).symm.toMonoidHom.comp
    (ConjugatedAmalgam.toHNN _ _ _ _ _ (simulatorD D.toCodeWords)
      (common_le_D G D hintersections))

theorem toK_injective : Function.Injective (toK G D hintersections) :=
  (SimulatorCentralizer.equiv D.toCodeWords).symm.injective.comp
    (ConjugatedAmalgam.toHNN_injective _ _ _ _ _ _ _ hintersections.1 hintersections.2)

@[simp] theorem toK_inA (x : simulatorA D.toCodeWords) :
    toK G D hintersections (inA G D hintersections x) = simulatorInclusion D.toCodeWords x := by
  change (SimulatorCentralizer.equiv D.toCodeWords).symm
    (ConjugatedAmalgam.toHNN _ _ _ _ _ _ _ (ConjugatedAmalgam.inA _ _ _ _ _ x)) = _
  rw [ConjugatedAmalgam.toHNN_inA]
  apply (SimulatorCentralizer.equiv D.toCodeWords).injective
  simp

@[simp] theorem toK_inB (x : simulatorB D.toCodeWords) :
    toK G D hintersections (inB G D hintersections x) =
      (generators (simulatorK D.toCodeWords) 7)⁻¹ * simulatorInclusion D.toCodeWords x *
        generators (simulatorK D.toCodeWords) 7 := by
  change (SimulatorCentralizer.equiv D.toCodeWords).symm
    (ConjugatedAmalgam.toHNN _ _ _ _ _ _ _ (ConjugatedAmalgam.inB _ _ _ _ _ x)) = _
  rw [ConjugatedAmalgam.toHNN_inB]
  apply (SimulatorCentralizer.equiv D.toCodeWords).injective
  simp

def left : Domain G D hintersections →* InputAmalgam G D.toCodeWords :=
  (ofK G D).comp (toK G D hintersections)

def rightB : simulatorB D.toCodeWords →* InputAmalgam G D.toCodeWords :=
  (ofK G D).comp
    ((MulAut.conj (generators (simulatorK D.toCodeWords) 7)⁻¹).toMonoidHom.comp
      ((simulatorInclusion D.toCodeWords).comp (simulatorB D.toCodeWords).subtype))

theorem agrees (x : recognitionSubgroup G D.toCodeWords) :
    rightA G D ⟨x, common_le_A G D hintersections x.property⟩ =
      rightB G D ⟨x, common_le_B G D hintersections x.property⟩ := by
  rw [rightA_recognized G D x.property]
  have h := (SimulatorCentralizer.inclusion_commute_k_iff D.toCodeWords (x : _)).mpr
    (common_le_D G D hintersections x.property)
  change ofK G D (simulatorInclusion D.toCodeWords x) =
    ofK G D ((generators (simulatorK D.toCodeWords) 7)⁻¹ *
      simulatorInclusion D.toCodeWords x * generators (simulatorK D.toCodeWords) 7)
  exact congrArg (ofK G D) h.symm.inv_mul_cancel.symm

/-- The diagonal map extends over the common recognized subgroup. -/
def right : Domain G D hintersections →* InputAmalgam G D.toCodeWords :=
  ConjugatedAmalgam.lift _ _ _ _ _ (rightA G D) (rightB G D) (agrees G D hintersections)

@[simp] theorem right_inA (x : simulatorA D.toCodeWords) :
    right G D hintersections (inA G D hintersections x) = rightA G D x := by
  exact ConjugatedAmalgam.lift_inA _ _ _ _ _ _ _ _ x

@[simp] theorem right_inB (x : simulatorB D.toCodeWords) :
    right G D hintersections (inB G D hintersections x) = rightB G D x := by
  exact ConjugatedAmalgam.lift_inB _ _ _ _ _ _ _ _ x

theorem rho_comp_left : (rho G D).comp (left G D hintersections) = toK G D hintersections := by
  apply MonoidHom.ext
  intro x
  exact rho_ofK G D _

theorem rho_comp_right : (rho G D).comp (right G D hintersections) = toK G D hintersections := by
  apply ConjugatedAmalgam.hom_ext
  · intro x
    change rho G D (right G D hintersections (inA G D hintersections x)) = _
    rw [right_inA, rho_rightA, toK_inA]
  · intro x
    change rho G D (right G D hintersections (inB G D hintersections x)) = _
    rw [right_inB, toK_inB]
    exact rho_ofK G D _

theorem left_injective : Function.Injective (left G D hintersections) :=
  (CentralizingAmalgam.ofBase_injective _ _).comp (toK_injective G D hintersections)

theorem right_injective : Function.Injective (right G D hintersections) := by
  intro x y h
  apply toK_injective G D hintersections
  have hh := congrArg (rho G D) h
  simpa only [← MonoidHom.comp_apply, rho_comp_right] using hh

/-- The actual HNN extension adjoining `ell`; both associated maps are injective. -/
abbrev Model := IdentifyingHNN (left G D hintersections) (right G D hintersections)
  (left_injective G D hintersections) (right_injective G D hintersections)

def ofM : InputAmalgam G D.toCodeWords →* Model G D hintersections :=
  IdentifyingHNN.of _ _ _ _

def ell : Model G D hintersections := IdentifyingHNN.stable _ _ _ _

theorem ofM_injective : Function.Injective (ofM G D hintersections) :=
  IdentifyingHNN.of_injective _ _ _ _

/-- The original input group survives the diagonal `ell` attachment. -/
def inputEmbedding : GroupEmbedding G.presentation.Group (Model G D hintersections) :=
  ⟨(ofM G D hintersections).comp (inputAmalgamEmbedding G D.toCodeWords).hom,
    (ofM_injective G D hintersections).comp (inputAmalgamEmbedding G D.toCodeWords).injective⟩

def simulatorEmbedding : GroupEmbedding (simulatorK D.toCodeWords).Group
    (Model G D hintersections) :=
  ⟨(ofM G D hintersections).comp (ofK G D),
    (ofM_injective G D hintersections).comp (CentralizingAmalgam.ofBase_injective _ _)⟩

theorem conjugates (x : Domain G D hintersections) :
    (ell G D hintersections)⁻¹ * ofM G D hintersections (left G D hintersections x) *
      ell G D hintersections = ofM G D hintersections (right G D hintersections x) :=
  IdentifyingHNN.conjugates _ _ _ _ x

theorem conjugates_A (w : FreeGroup (Fin 5)) :
    (ell G D hintersections)⁻¹ * ofM G D hintersections
        (ofL G D (CodeSubgroups.aLift D.toCodeWords w)) * ell G D hintersections =
      ofM G D hintersections (rawRightA G D w) := by
  have h := conjugates G D hintersections (inA G D hintersections (aEquiv G D w))
  simpa [left, rightA_aEquiv, ofL] using h

theorem commutes_conjugated_B (x : simulatorB D.toCodeWords) :
    Commute (ell G D hintersections)
      (ofM G D hintersections (rightB G D x)) := by
  have h := conjugates G D hintersections (inB G D hintersections x)
  have hl : left G D hintersections (inB G D hintersections x) = rightB G D x := by
    simp [left, rightB]
  rw [hl, right_inB] at h
  have hh := congrArg (fun z => ell G D hintersections * z) h
  simpa [commute_iff_eq, mul_assoc] using hh.symm

/-- The two literal attachment equations. -/
theorem attachment (i : Fin 2) :
    ofM G D hintersections (a G D i.castSucc.castSucc.castSucc) * ell G D hintersections =
      ell G D hintersections *
        (ofM G D hintersections (a G D i.castSucc.castSucc.castSucc) *
          ofM G D hintersections (f G D) * ofM G D hintersections (u G D i) *
          (ofM G D hintersections (f G D))⁻¹) := by
  have h := conjugates_A G D hintersections (FreeGroup.of i.castSucc.castSucc.castSucc)
  have hh := congrArg (fun z => ell G D hintersections * z) h
  fin_cases i <;> simpa [rawRightA, EllAlgebra.diagonal, a, mul_assoc] using hh

theorem commutes_x (j : Fin 3) :
    Commute (ell G D hintersections)
      (ofM G D hintersections
        (ofL G D ((simulatorL D.toCodeWords).evalWord (simulatorLWords.x D.toCodeWords j)))) := by
  have h := conjugates_A G D hintersections (FreeGroup.of (j.addNat 2))
  have hh := congrArg (fun z => ell G D hintersections * z) h
  fin_cases j <;>
    simpa [rawRightA, EllAlgebra.diagonal, a, CodeSubgroups.aValues,
      commute_iff_eq, mul_assoc] using hh.symm

/-- All four grid letters are fixed by `ell`. -/
theorem commutes_grid_value (j : Fin 4) :
    Commute (ell G D hintersections)
      (ofM G D hintersections (ofK G D (simulatorGridValues D.toCodeWords j))) := by
  refine Fin.cases ?_ (fun i => commutes_x G D hintersections i) j
  · let b : simulatorB D.toCodeWords :=
      ⟨CodeSubgroups.bValues D.toCodeWords 2,
        (CodeSubgroups.bLift_range D.toCodeWords) ▸
          ⟨FreeGroup.of 2, CodeSubgroups.bLift_of D.toCodeWords 2⟩⟩
    have h := commutes_conjugated_B G D hintersections b
    simpa [b, rightB, CodeSubgroups.bValues, FP.evalWord, simulatorLWords,
      simulatorInclusion, generators, simulatorGridValues, map_mul, map_inv,
      mul_assoc] using h

theorem commutes_grid (x : simulatorGrid D.toCodeWords) :
    Commute (ell G D hintersections)
      ((simulatorEmbedding G D hintersections).hom (x : (simulatorK D.toCodeWords).Group)) := by
  apply PositiveEvaluation.commute_closure _ _ _ ?_ x.property
  rintro _ ⟨i, rfl⟩
  exact commutes_grid_value G D hintersections i

def gridDomainValue (j : Fin 4) : Domain G D hintersections :=
  Fin.cases
    (inB G D hintersections
      ⟨CodeSubgroups.bValues D.toCodeWords 2,
        (CodeSubgroups.bLift_range D.toCodeWords) ▸
          ⟨FreeGroup.of 2, CodeSubgroups.bLift_of D.toCodeWords 2⟩⟩)
    (fun i => inA G D hintersections (aEquiv G D (FreeGroup.of (i.addNat 2)))) j

@[simp] theorem toK_gridDomainValue (j : Fin 4) :
    toK G D hintersections (gridDomainValue G D hintersections j) =
      simulatorGridValues D.toCodeWords j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [gridDomainValue, CodeSubgroups.bValues, FP.evalWord, simulatorLWords,
      simulatorInclusion, generators, simulatorGridValues]
  · change toK G D hintersections
      (inA G D hintersections (aEquiv G D (FreeGroup.of (i.addNat 2)))) = _
    rw [toK_inA]
    simp only [simulatorGridValues, Fin.cons_succ]
    fin_cases i <;>
      simp [aEquiv_val, CodeSubgroups.aValues]

theorem grid_le_domain_range : simulatorGrid D.toCodeWords ≤ (toK G D hintersections).range := by
  rw [simulatorGrid, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨gridDomainValue G D hintersections i, toK_gridDomainValue G D hintersections i⟩

end
end UniversalGroup.EllStage
