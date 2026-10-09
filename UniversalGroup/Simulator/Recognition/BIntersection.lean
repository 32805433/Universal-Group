module

public import UniversalGroup.Simulator.Recognition.Prefixes
public import UniversalGroup.Simulator.Recognition.FactorNormalForms

@[expose] public section

/-!
# Exact intersection with the right code subgroup

First-syllable recognition and induction on reduced words give the upper
inclusion; forward recognition supplies the reverse inclusion.
-/

namespace UniversalGroup.SimulatorIntersectionBUpper

open SimulatorIntersectionB SimulatorCoefficientTransport BorisovCStage

noncomputable section
set_option maxHeartbeats 800000

variable (G : PreparedInput) (D : ValievDatum G)

/-- Compare a reduced B word with a reduced D word and recognize its first
base coefficient; signs refer to Mathlib's stable letter, the inverse of T. -/
theorem first_coefficient
    (w : ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range)
    (hhead : w.head ∈ Base G D)
    (hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords)
    (u : ℤˣ) (a : FStage G D) (rest : List (ℤˣ × FStage G D))
    (hw : w.toList = (u, a) :: rest) :
    ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord),
      CodeSubgroups.codeLift D.r g * positiveFree D.P = positiveFree Q ∧
      PositiveEq D.toCodeWords.rules Q D.P ∧
      ((u = -1 ∧ w.head = ofCore G D (codeCore G D g)) ∨
       (u = 1 ∧ w.head = (f G D)⁻¹ * ofCore G D (codeCore G D g) * f G D)) := by
  rcases SimulatorDModel.exists_reducedWord D.toCodeWords D.F_support D.E_support hD with
    ⟨v, hv, hvhead, hvcoeff⟩
  have heq : w.prod (phi G D) = v.prod (phi G D) :=
    SimulatorDModel.toLiteral_injective D.toCodeWords D.F_support D.E_support hv.symm
  rcases ReducedWordPeel.first_comparison (phi G D) w v heq u a rest hw with
    ⟨a', rest', hvlist, hcoset, hsigns⟩
  rcases Int.units_eq_one_or u with rfl | rfl
  · have hm : w.head⁻¹ * v.head ∈ (right G D).range := by simpa using hcoset
    rcases right_coefficient_factorization G D w.head v.head hvhead hm with ⟨x, y, hx, hy, hxy⟩
    rcases negative_coefficient G D w.head hhead x y hx hy hxy with ⟨g, Q, hg, hQ, hrec⟩
    exact ⟨g, Q, hQ, hrec, Or.inr ⟨rfl, hg⟩⟩
  · have hm : w.head⁻¹ * v.head ∈ (left G D).range := by simpa using hcoset
    rcases left_coefficient_factorization G D w.head v.head hvhead hm with ⟨x, y, hx, hy, hxy⟩
    rcases positive_coefficient G D w.head hhead x y hx hy hxy with ⟨g, Q, hg, hQ, hrec⟩
    exact ⟨g, Q, hQ, hrec, Or.inl ⟨rfl, hg⟩⟩

/-- The first coefficient supplies exactly the recognized prefix required
by the length-decreasing induction. -/
theorem recognized_prefix
    (w : ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range)
    (u : ℤˣ) (a : FStage G D) (rest : List (ℤˣ × FStage G D))
    (hw : w.toList = (u, a) :: rest) (hhead : w.head ∈ Base G D)
    (hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords) :
    ∃ z ∈ Base G D,
      ReducedWordPeel.prefixElement (phi G D) w.head u z ∈
        SimulatorRecognizedPrefixes.recognized G D := by
  rcases first_coefficient G D w hhead hD u a rest hw with ⟨g, Q, hQ, hrec, hshape⟩
  rcases SimulatorRecognizedPrefixes.decode G D g Q hQ hrec with ⟨v, hv, hg, hword⟩
  subst g
  have hbase : SimulatorRecognizedPrefixes.codeValue G D v ∈ Base G D :=
    (ofCore_mem_base_iff G D _).2 ⟨CodeSubgroups.positiveFree v, rfl⟩
  rcases hshape with ⟨rfl, hhead'⟩ | ⟨rfl, hhead'⟩
  · refine ⟨(f G D)⁻¹ * SimulatorRecognizedPrefixes.codeValue G D v * f G D, ?_, ?_⟩
    · exact (Base G D).mul_mem
        ((Base G D).mul_mem ((Base G D).inv_mem (f_mem_base G D)) hbase) (f_mem_base G D)
    · rw [hhead']
      exact SimulatorRecognizedPrefixes.positive_prefix G D v hv
  · refine ⟨SimulatorRecognizedPrefixes.codeValue G D v, hbase, ?_⟩
    rw [hhead']
    exact SimulatorRecognizedPrefixes.negative_prefix G D v hv

/-- Every reduced word with B coefficients whose value lies in D is a
product of recognized delta generators and their inverses. -/
theorem reducedWord_mem_recognition
    (w : ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range)
    (hhead : w.head ∈ Base G D) (hcoeff : ∀ p ∈ w.toList, p.2 ∈ Base G D)
    (hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords) :
    w.prod (phi G D) ∈ SimulatorRecognizedPrefixes.recognized G D := by
  let K : Subgroup (Rebased G D) := (simulatorD D.toCodeWords).comap (toLiteral G D)
  apply ReducedWordPeel.mem_of_recognized_prefix (phi G D) (Base G D) K
    (SimulatorRecognizedPrefixes.recognized G D) ?_ ?_ ?_ w hhead hcoeff hD
  · intro x hx
    exact SimulatorRecognitionForward.recognition_le_D G D hx
  · intro g hg hgK
    change toLiteral G D (TwistedCentralizer.of (attaching G D) (marker G D) (f G D) g) ∈
      simulatorD D.toCodeWords at hgK
    rw [SimulatorDModel.toLiteral_of] at hgK
    have hgD := (SimulatorDModel.fromF_mem_D_iff D.toCodeWords D.F_support D.E_support g).1 hgK
    have hg1 : g = 1 := by
      have hm : g ∈ Base G D ⊓ (CD G D).map (ofCore G D) := ⟨hg, hgD⟩
      rw [base_inf_CD] at hm
      exact hm
    subst g
    simp
  · intro v u a rest hv hvhead hvcoeff hvK
    exact recognized_prefix G D v u a rest hv hvhead hvK

/-- The reverse half of Valiev's intersection theorem for B. -/
theorem intersection_le :
    simulatorD D.toCodeWords ⊓ simulatorB D.toCodeWords ≤
      recognitionSubgroup G D.toCodeWords := by
  rintro x ⟨hxD, hxB⟩
  rcases SimulatorFactorNormalForms.exists_reducedWord_B G D hxB with ⟨w, hw, hhead, hcoeff⟩
  have hD : toLiteral G D (w.prod (phi G D)) ∈ simulatorD D.toCodeWords := hw ▸ hxD
  have hm := reducedWord_mem_recognition G D w hhead hcoeff hD
  change toLiteral G D (w.prod (phi G D)) ∈ recognitionSubgroup G D.toCodeWords at hm
  rwa [hw] at hm

/-- The exact recognition identity `D ∩ B = R`. -/
theorem intersection_eq :
    simulatorD D.toCodeWords ⊓ simulatorB D.toCodeWords =
      recognitionSubgroup G D.toCodeWords := by
  apply le_antisymm (intersection_le G D)
  exact le_inf (SimulatorRecognitionForward.recognition_le_D G D)
    (RecognitionAlgebra.recognition_le_B D.toCodeWords G)

end

end UniversalGroup.SimulatorIntersectionBUpper
