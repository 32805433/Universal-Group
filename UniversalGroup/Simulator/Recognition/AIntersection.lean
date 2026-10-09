module

public import UniversalGroup.Simulator.Recognition.AComparison
public import UniversalGroup.Simulator.Recognition.Prefixes
public import UniversalGroup.Simulator.Recognition.FactorNormalForms

@[expose] public section

/-! The reverse A intersection: recognize and remove the first stable syllable. -/
namespace UniversalGroup.SimulatorIntersectionAUpper

open SimulatorIntersectionB SimulatorCoefficientTransport BorisovCStage
open SimulatorIntersectionA

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (G : PreparedInput) (D : ValievDatum G)

private theorem code_of_positive_suffix (W : FreeGroup (Fin 2)) (Q v : PositiveWord)
    (hQ : W * positiveFree D.P = positiveFree Q)
    (hv : Q = v.flatMap D.code ++ D.P) :
    W = CodeSubgroups.codeLift D.r (CodeSubgroups.positiveFree v) := by
  apply mul_right_cancel (b := positiveFree D.P)
  rw [hQ, hv, CodeCancellation.codeLift_positive]
  simp only [positiveFree_eq_eval, evalPositive, List.map_append, List.prod_append,
    D.code_shape, CodeSubgroups.positiveFree]

/-- Compare with a D normal form. A negative-positive boundary needs the
literal marker-cancellation theorem; all other boundaries give a codeword directly. -/
theorem first_coefficient
    (w : ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range)
    (hhead : w.head ∈ SimulatorIntersectionA.Base G D)
    (hcoeff : ∀ p ∈ w.toList, p.2 ∈ SimulatorIntersectionA.Base G D)
    (hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords)
    (u : ℤˣ) (a : FStage G D) (rest : List (ℤˣ × FStage G D))
    (hw : w.toList = (u, a) :: rest) :
    ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord),
      CodeSubgroups.codeLift D.r g * positiveFree D.P = positiveFree Q ∧
      PositiveEq D.toCodeWords.rules Q D.P ∧
      ((u = -1 ∧ w.head = ofCore G D (codeCore G D g)) ∨
       (u = 1 ∧ w.head = (f G D)⁻¹ * ofCore G D (codeCore G D g) * f G D)) := by
  obtain ⟨z, hz, hzhead, hzcoeff⟩ :=
    SimulatorDModel.exists_reducedWord D.toCodeWords D.F_support D.E_support hD
  have heq : w.prod (phi G D) = z.prod (phi G D) :=
    SimulatorDModel.toLiteral_injective D.toCodeWords D.F_support D.E_support hz.symm
  obtain ⟨_, _, _, hcoset, _⟩ :=
    ReducedWordPeel.first_comparison (phi G D) w z heq u a rest hw
  rcases Int.units_eq_one_or u with rfl | rfl
  · have hm : w.head⁻¹ * z.head ∈ (right G D).range := by simpa using hcoset
    obtain ⟨x, y, hx, hy, hxy⟩ := right_coefficient_factorization G D _ _ hzhead hm
    obtain ⟨W, Q, hWhead, hQ, hrec⟩ :=
      SimulatorIntersectionA.negative_coefficient G D _ hhead x y hx hy hxy
    have halt := SimulatorIntersectionACompare.negative_head_alternative G D w z W
      hWhead hcoeff hzhead hzcoeff heq a rest hw
    have hcode : ∃ g, W = CodeSubgroups.codeLift D.r g := by
      rcases halt with ⟨g, hg⟩ | ⟨g, V, hg, hV, hVrec⟩
      · refine ⟨g, ?_⟩
        apply SimulatorFreeLetters.coreLetters_injective D.toCodeWords D.F_support D.E_support
        exact hg.symm
      · have hseparator : CodeSubgroups.positiveFree Q *
            (CodeSubgroups.positiveFree D.P)⁻¹ * CodeSubgroups.codeLift D.r g *
              CodeSubgroups.positiveFree D.P = CodeSubgroups.positiveFree V := by
          have hQ' : W * CodeSubgroups.positiveFree D.P = CodeSubgroups.positiveFree Q := by
            simpa only [positiveFree_eq_eval, CodeSubgroups.positiveFree] using hQ
          have hV' : (W * CodeSubgroups.codeLift D.r g) * CodeSubgroups.positiveFree D.P =
              CodeSubgroups.positiveFree V := by
            simpa only [positiveFree_eq_eval, CodeSubgroups.positiveFree] using hV
          rw [← hQ']
          simpa only [mul_assoc, mul_inv_cancel, mul_one] using hV'
        obtain ⟨v, hv, _⟩ := CodeCancellation.coded_marker_of_separator D g hg Q V
          hrec hVrec hseparator
        exact ⟨CodeSubgroups.positiveFree v, code_of_positive_suffix G D W Q v hQ hv⟩
    obtain ⟨g, hg⟩ := hcode
    refine ⟨g, Q, hg ▸ hQ, hrec, Or.inr ⟨rfl, ?_⟩⟩
    rw [hWhead, hg]
    rfl
  · have hm : w.head⁻¹ * z.head ∈ (left G D).range := by simpa using hcoset
    obtain ⟨x, y, hx, hy, hxy⟩ := left_coefficient_factorization G D _ _ hzhead hm
    obtain ⟨g, Q, hg, hQ, hrec⟩ :=
      SimulatorIntersectionA.positive_coefficient G D _ hhead x y hx hy hxy
    exact ⟨g, Q, hQ, hrec, Or.inl ⟨rfl, hg⟩⟩

/-- Each leading syllable is a recognized delta or its inverse, up to the
base coefficient used by the shorter tail. -/
theorem recognized_prefix
    (w : ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range)
    (u : ℤˣ) (a : FStage G D) (rest : List (ℤˣ × FStage G D))
    (hw : w.toList = (u, a) :: rest) (hhead : w.head ∈ SimulatorIntersectionA.Base G D)
    (hcoeff : ∀ p ∈ w.toList, p.2 ∈ SimulatorIntersectionA.Base G D)
    (hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords) :
    ∃ z ∈ SimulatorIntersectionA.Base G D,
      ReducedWordPeel.prefixElement (phi G D) w.head u z ∈
        SimulatorRecognizedPrefixes.recognized G D := by
  obtain ⟨g, Q, hQ, hrec, hshape⟩ := first_coefficient G D w hhead hcoeff hD u a rest hw
  obtain ⟨v, hv, hg, _⟩ := SimulatorRecognizedPrefixes.decode G D g Q hQ hrec
  subst g
  have hbase : SimulatorRecognizedPrefixes.codeValue G D v ∈ SimulatorIntersectionA.Base G D :=
    (SimulatorIntersectionA.ofCore_mem_base_iff G D _).2 ⟨CodeSubgroups.positiveFree v, rfl⟩
  rcases hshape with ⟨rfl, hhead'⟩ | ⟨rfl, hhead'⟩
  · refine ⟨(f G D)⁻¹ * SimulatorRecognizedPrefixes.codeValue G D v * f G D, ?_, ?_⟩
    · exact conjugated_letters_mem_base G D (codeCore_mem_letters G D _)
    · rw [hhead']
      exact SimulatorRecognizedPrefixes.positive_prefix G D v hv
  · refine ⟨SimulatorRecognizedPrefixes.codeValue G D v, hbase, ?_⟩
    rw [hhead']
    exact SimulatorRecognizedPrefixes.negative_prefix G D v hv

theorem reducedWord_mem_recognition
    (w : ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range)
    (hhead : w.head ∈ SimulatorIntersectionA.Base G D)
    (hcoeff : ∀ p ∈ w.toList, p.2 ∈ SimulatorIntersectionA.Base G D)
    (hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords) :
    w.prod (phi G D) ∈ SimulatorRecognizedPrefixes.recognized G D := by
  let K : Subgroup (Rebased G D) := (simulatorD D.toCodeWords).comap (toLiteral G D)
  apply ReducedWordPeel.mem_of_recognized_prefix (phi G D) (SimulatorIntersectionA.Base G D) K
    (SimulatorRecognizedPrefixes.recognized G D) ?_ ?_ ?_ w hhead hcoeff hD
  · intro x hx
    exact SimulatorRecognitionForward.recognition_le_D G D hx
  · intro g hg hgK
    change toLiteral G D (TwistedCentralizer.of (attaching G D) (marker G D) (f G D) g) ∈
      simulatorD D.toCodeWords at hgK
    rw [SimulatorDModel.toLiteral_of] at hgK
    have hgD := (SimulatorDModel.fromF_mem_D_iff D.toCodeWords D.F_support D.E_support g).1 hgK
    obtain ⟨x, hx, hxeq⟩ := hgD
    have hcode := (SimulatorIntersectionA.ofCore_mem_base_iff G D x).1 (hxeq ▸ hg)
    have hxletters := codes_le_letters G D hcode
    have hx1 : x = 1 := by
      have hm : x ∈ Letters G D ⊓ CD G D := ⟨hxletters, hx⟩
      rw [SimulatorFreeLetters.coreLetters_inf_CD] at hm
      exact hm
    have hg1 : g = 1 := by rw [← hxeq, hx1, map_one]
    rw [hg1, map_one]
    exact (SimulatorRecognizedPrefixes.recognized G D).one_mem
  · intro v u a rest hv hvhead hvcoeff hvK
    exact recognized_prefix G D v u a rest hv hvhead hvcoeff hvK

/-- The reverse half of Valiev's intersection theorem for A. -/
theorem intersection_le :
    simulatorD D.toCodeWords ⊓ simulatorA D.toCodeWords ≤
      recognitionSubgroup G D.toCodeWords := by
  rintro x ⟨hxD, hxA⟩
  obtain ⟨w, hw, hhead, hcoeff⟩ := SimulatorFactorNormalForms.exists_reducedWord_A G D hxA
  have hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords := hw ▸ hxD
  have hm := reducedWord_mem_recognition G D w hhead hcoeff hD
  change toLiteral G D (w.prod (phi G D)) ∈ recognitionSubgroup G D.toCodeWords at hm
  rwa [hw] at hm

/-- The exact recognition identity `D ∩ A = R`. -/
theorem intersection_eq :
    simulatorD D.toCodeWords ⊓ simulatorA D.toCodeWords =
      recognitionSubgroup G D.toCodeWords := by
  apply le_antisymm (intersection_le G D)
  exact le_inf (SimulatorRecognitionForward.recognition_le_D G D)
    (RecognitionAlgebra.recognition_le_A D.toCodeWords G)

end
end UniversalGroup.SimulatorIntersectionAUpper
