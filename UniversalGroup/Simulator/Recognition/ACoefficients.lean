module

public import UniversalGroup.Simulator.Recognition.BCoefficients
public import UniversalGroup.Simulator.Core.RecognitionGeometry

@[expose] public section

/-! Coefficient geometry for the reverse intersection with `A`. -/

namespace UniversalGroup.SimulatorIntersectionA

open SimulatorIntersectionB SimulatorFreeLetters SimulatorModel BorisovCStage HNNLemmas
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (G : PreparedInput) (D : ValievDatum G)

abbrev Letters : Subgroup (Core G D) :=
  (coreLetters D.toCodeWords D.F_support D.E_support).range

def Base : Subgroup (FStage G D) :=
  RecognitionGeometry.aBase (CD G D) (Letters G D) (codeCore G D).range

abbrev Wide : Subgroup (FStage G D) :=
  RecognitionGeometry.wide (CD G D) (Letters G D)

theorem codes_le_letters : (codeCore G D).range ≤ Letters G D := by
  rintro x ⟨w, rfl⟩
  exact codeCore_mem_letters G D w

theorem ofCore_mem_base_iff (x : Core G D) :
    ofCore G D x ∈ Base G D ↔ x ∈ (codeCore G D).range :=
  RecognitionGeometry.ofCore_mem_aBase_iff _ _ _ (codes_le_letters G D)
    (coreLetters_inf_CD D.toCodeWords D.F_support D.E_support) x

theorem base_le_wide : Base G D ≤ Wide G D :=
  RecognitionGeometry.aBase_le_wide _ _ _ (codes_le_letters G D)

theorem conjugated_letters_mem_base {x : Core G D} (hx : x ∈ Letters G D) :
    (f G D)⁻¹ * ofCore G D x * f G D ∈ Base G D :=
  RecognitionGeometry.conjugated_mem_aBase _ _ _ hx

theorem f_mem_wide : f G D ∈ Wide G D := RecognitionGeometry.f_mem_wide _ _

theorem conjugated_core_mem_wide_iff (x : Core G D) :
    (f G D)⁻¹ * ofCore G D x * f G D ∈ Wide G D ↔ x ∈ Letters G D := by
  constructor
  · intro hx
    have hm := (Wide G D).mul_mem ((Wide G D).mul_mem (f_mem_wide G D) hx)
      ((Wide G D).inv_mem (f_mem_wide G D))
    apply (RecognitionGeometry.ofCore_mem_wide_iff _ _ x).1
    change ofCore G D x ∈ Wide G D
    simpa [mul_assoc] using hm
  · intro hx
    exact base_le_wide G D (conjugated_letters_mem_base G D hx)

theorem attaching_left_disjoint (v : Core G D) (hv : v ∈ CE G D)
    (hb : ofCore G D (pCore G D * v * (pCore G D)⁻¹) ∈ Base G D) : v = 1 := by
  apply SimulatorIntersectionB.attaching_left_disjoint G D v hv
  exact (SimulatorIntersectionB.ofCore_mem_base_iff G D _).2
    ((ofCore_mem_base_iff G D _).1 hb)

theorem attaching_right_disjoint (v : Core G D) (hv : v ∈ CE G D)
    (hb : (f G D)⁻¹ * ofCore G D (pCore G D * v * (pCore G D)⁻¹) * f G D ∈
      Base G D) : v = 1 := by
  have hm := (conjugated_core_mem_wide_iff G D _).1 (base_le_wide G D hb)
  have hp : pCore G D ∈ Letters G D := pCore_mem_letters G D
  have hvletters : v ∈ Letters G D := by
    have hh := (Letters G D).mul_mem
      ((Letters G D).mul_mem ((Letters G D).inv_mem hp) hm) hp
    simpa [mul_assoc] using hh
  have hz : v ∈ (⊥ : Subgroup (Core G D)) := by
    rw [← coreLetters_inf_CE D.toCodeWords D.F_support D.E_support]
    exact ⟨hvletters, hv⟩
  exact hz

theorem positive_coefficient (b : FStage G D) (hb : b ∈ Base G D)
    (u v : Core G D) (hu : u ∈ CD G D) (hv : v ∈ CE G D)
    (heq : b = ofCore G D (u * pCore G D * v * (pCore G D)⁻¹)) :
    ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord),
      b = ofCore G D (codeCore G D g) ∧
      CodeSubgroups.codeLift D.r g * BorisovCStage.positiveFree D.P =
        BorisovCStage.positiveFree Q ∧ PositiveEq D.toCodeWords.rules Q D.P := by
  apply SimulatorIntersectionB.positive_coefficient G D b _ u v hu hv heq
  rw [heq] at hb ⊢
  exact (SimulatorIntersectionB.ofCore_mem_base_iff G D _).2
    ((ofCore_mem_base_iff G D _).1 hb)

/-- A negative first coefficient yields an arbitrary signed stable word;
the next coefficient or terminal comparison will force it into the code subgroup. -/
theorem negative_coefficient (b : FStage G D) (hb : b ∈ Base G D)
    (u v : Core G D) (hu : u ∈ CD G D) (hv : v ∈ CE G D)
    (heq : b = (f G D)⁻¹ * ofCore G D
      (u * pCore G D * v * (pCore G D)⁻¹) * f G D) :
    ∃ (W : FreeGroup (Fin 2)) (Q : PositiveWord),
      b = (f G D)⁻¹ * ofCore G D
        (coreLetters D.toCodeWords D.F_support D.E_support W) * f G D ∧
      W * BorisovCStage.positiveFree D.P = BorisovCStage.positiveFree Q ∧
      PositiveEq D.toCodeWords.rules Q D.P := by
  have hm : u * pCore G D * v * (pCore G D)⁻¹ ∈ Letters G D :=
    (conjugated_core_mem_wide_iff G D _).1 (base_le_wide G D (heq ▸ hb))
  obtain ⟨W, hW⟩ := hm
  let R := rules D.toCodeWords D.F_support D.E_support
  let hf := free D.toCodeWords D.F_support D.E_support
  have hcontext : sLift2 R hf (W * BorisovCStage.positiveFree D.P) =
      u * positive2 R hf D.P * v := by
    rw [map_mul]
    have hW' : sLift2 R hf W = u * pCore G D * v * (pCore G D)⁻¹ := by
      rw [← coreLetters_eq_sLift2 G D]
      exact hW
    rw [hW']
    change (u * pCore G D * v * (pCore G D)⁻¹) *
      coreOf D.toCodeWords D.F_support D.E_support
        (sLift3 (BorisovCStage.positiveFree D.P)) = _
    rw [sLift3_positiveFree]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rfl
  obtain ⟨Q, hQ, hQP⟩ := SimulatorRecognitionCore.of_context_factorization R hf
    _ D.P u v hu hv hcontext
  refine ⟨W, Q, ?_, hQ, hQP⟩
  rw [heq, hW]

theorem negative_next_negative {v x : Core G D} {j : FStage G D}
    (hv : v ∈ Letters G D) (hj : j ∈ Base G D)
    (heq : ofCore G D v * j = (f G D)⁻¹ * ofCore G D x * f G D) :
    v ∈ (codeCore G D).range :=
  RecognitionGeometry.negative_next_negative _ _ _ (codes_le_letters G D)
    (coreLetters_inf_CD D.toCodeWords D.F_support D.E_support) hv hj heq

/-- At a negative-positive boundary the intervening coefficient is a
code word, and a second application of recognition supplies the two
positive words needed for marker cancellation. -/
theorem negative_next_positive (W : FreeGroup (Fin 2)) (j : FStage G D)
    (hj : j ∈ Base G D) (u v : Core G D)
    (hu : u ∈ CD G D) (hv : v ∈ CE G D)
    (heq : ofCore G D (coreLetters D.toCodeWords D.F_support D.E_support W) * j =
      ofCore G D (u * pCore G D * v * (pCore G D)⁻¹)) :
    ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord),
      j = ofCore G D (codeCore G D g) ∧
      (W * CodeSubgroups.codeLift D.r g) * BorisovCStage.positiveFree D.P =
        BorisovCStage.positiveFree Q ∧ PositiveEq D.toCodeWords.rules Q D.P := by
  let x := coreLetters D.toCodeWords D.F_support D.E_support W
  let a := u * pCore G D * v * (pCore G D)⁻¹
  have hjEq : j = ofCore G D (x⁻¹ * a) := by
    rw [map_mul, map_inv]
    exact (eq_inv_mul_iff_mul_eq).2 heq
  have hjcore : x⁻¹ * a ∈ (codeCore G D).range :=
    (ofCore_mem_base_iff G D _).1 (hjEq ▸ hj)
  obtain ⟨g, hg⟩ := hjcore
  have hjg : j = ofCore G D (codeCore G D g) := by rw [hg]; exact hjEq
  have hcore : x * codeCore G D g = a := by
    rw [hg]
    group
  let R := rules D.toCodeWords D.F_support D.E_support
  let hf := free D.toCodeWords D.F_support D.E_support
  have hcontext : sLift2 R hf
      ((W * CodeSubgroups.codeLift D.r g) * BorisovCStage.positiveFree D.P) =
      u * positive2 R hf D.P * v := by
    rw [map_mul, map_mul]
    have hwords : sLift2 R hf W * sLift2 R hf (CodeSubgroups.codeLift D.r g) = a := by
      rw [← coreLetters_eq_sLift2 G D]
      exact hcore
    rw [hwords]
    change (u * pCore G D * v * (pCore G D)⁻¹) *
      coreOf D.toCodeWords D.F_support D.E_support
        (sLift3 (BorisovCStage.positiveFree D.P)) = _
    rw [sLift3_positiveFree]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rfl
  obtain ⟨Q, hQ, hQP⟩ := SimulatorRecognitionCore.of_context_factorization R hf
    _ D.P u v hu hv hcontext
  exact ⟨g, Q, hjg, hQ, hQP⟩

theorem negative_terminal {v x : Core G D} {j : FStage G D}
    (hv : v ∈ Letters G D) (hj : j ∈ Base G D) (hx : x ∈ CD G D)
    (heq : ofCore G D v * j = ofCore G D x) : v ∈ (codeCore G D).range :=
  RecognitionGeometry.negative_terminal _ _ _ (codes_le_letters G D)
    (coreLetters_inf_CD D.toCodeWords D.F_support D.E_support) hv hj hx heq

end
end UniversalGroup.SimulatorIntersectionA
