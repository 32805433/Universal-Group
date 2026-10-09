module

public import UniversalGroup.Simulator.Recognition.FiniteRank.NormalForms
public import UniversalGroup.Foundations.HNN.ReducedWordPeel

@[expose] public section

/-! Exact recognition intersection for an arbitrary injected signed code. -/
namespace UniversalGroup.HigmanSimulatorB
noncomputable section
open BorisovCStage
set_option maxHeartbeats 800000
variable {k : ℕ} (D : Data k)

def Accepted (g : FreeGroup (Fin k)) : Prop :=
  ∃ Q : PositiveWord, D.code g * positiveFree D.words.P = positiveFree Q ∧
    PositiveEq D.words.rules Q D.words.P

def codeValue (g : FreeGroup (Fin k)) : FStage D := ofCore D (codeCore D g)

def literalCode : FreeGroup (Fin k) →* (simulatorL D.words).Group :=
  (fromF D).comp ((ofCore D).comp (codeCore D))

def delta (g : FreeGroup (Fin k)) : (simulatorL D.words).Group :=
  literalCode D g * SimulatorRecognitionForward.target D.words *
    (SimulatorRelations.f D.words)⁻¹ * (literalCode D g)⁻¹ * SimulatorRelations.f D.words

def recognition : Subgroup (simulatorL D.words).Group :=
  Subgroup.closure (delta D '' {g | Accepted D g})

def recognized : Subgroup (Rebased D) := (recognition D).comap (toLiteral D)

theorem literalCode_marker (g : FreeGroup (Fin k)) (Q : PositiveWord)
    (hQ : D.code g * positiveFree D.words.P = positiveFree Q) :
    literalCode D g * SimulatorRelations.positive D.words D.words.P =
      SimulatorRelations.positive D.words Q := by
  let j := (fromF D).comp ((ofCore D).comp
    (SimulatorFreeLetters.coreLetters D.words D.F_support D.E_support))
  have hj (w : PositiveWord) : j (positiveFree w) = SimulatorRelations.positive D.words w := by
    dsimp [j]
    rw [SimulatorModel.fromF_ofF, ← MonoidHom.comp_apply,
      SimulatorFreeLetters.fromCore_comp_coreLetters, positiveFree_eq_eval,
      CodeSubgroups.map_positive]
    simp [SimulatorFreeLetters.freeS, SimulatorRelations.positive]
  have h := congrArg j hQ
  rw [map_mul, hj, hj] at h
  exact h

theorem delta_mem_D (g : FreeGroup (Fin k)) (hg : Accepted D g) :
    delta D g ∈ simulatorD D.words := by
  obtain ⟨Q,hQ,hrec⟩ := hg
  obtain ⟨a,ha,b,hb,heq⟩ := SimulatorRecognitionForward.simulation D.words hrec
  have hq : b * SimulatorRelations.q D.words * b⁻¹ = SimulatorRelations.q D.words :=
    (SimulatorRecognitionForward.q_commute_CE D.words hb).symm.mul_inv_cancel
  have hf : a⁻¹ * SimulatorRelations.f D.words = SimulatorRelations.f D.words * a⁻¹ :=
    (SimulatorRecognitionForward.f_commute_CD D.words ha).inv_right.symm.eq
  have hval := literalCode_marker D g Q hQ
  have hd : delta D g = a * SimulatorRecognitionForward.target D.words * a⁻¹ := by
    unfold delta
    rw [SimulatorRecognitionForward.target_eq]
    calc
      _ = (literalCode D g * SimulatorRelations.positive D.words D.words.P) *
          SimulatorRelations.q D.words *
          (literalCode D g * SimulatorRelations.positive D.words D.words.P)⁻¹ *
          SimulatorRelations.f D.words := by group
      _ = a * (SimulatorRelations.positive D.words D.words.P *
          (b * SimulatorRelations.q D.words * b⁻¹) *
          (SimulatorRelations.positive D.words D.words.P)⁻¹) * a⁻¹ *
          SimulatorRelations.f D.words := by rw [hval, heq]; group
      _ = _ := by rw [hq]; simp only [mul_assoc]; rw [hf]
  rw [hd]
  exact (simulatorD D.words).mul_mem
    ((simulatorD D.words).mul_mem (SimulatorRecognitionForward.CD_le_D D.words ha)
      (SimulatorRecognitionForward.target_mem_D D.words))
    ((simulatorD D.words).inv_mem (SimulatorRecognitionForward.CD_le_D D.words ha))

theorem recognition_le_D : recognition D ≤ simulatorD D.words := by
  rw [recognition, Subgroup.closure_le]
  rintro x ⟨g,hg,rfl⟩
  exact delta_mem_D D g hg

/-- Mathlib's stable letter is the inverse of the displayed T. -/
theorem toLiteral_t :
    toLiteral D (HNNExtension.t : Rebased D) =
      (SimulatorRecognitionForward.target D.words)⁻¹ := by
  have h := congrArg Inv.inv (SimulatorDModel.toLiteral_stable D.words D.F_support D.E_support)
  simpa only [TwistedCentralizer.stable, IdentifyingHNN.stable, map_inv, inv_inv] using h

theorem toLiteral_prefix (b z : FStage D) (u : ℤˣ) :
    toLiteral D (ReducedWordPeel.prefixElement (phi D) b u z) =
      SimulatorModel.fromF D.words D.F_support D.E_support b *
        ((SimulatorRecognitionForward.target D.words)⁻¹) ^ (u : ℤ) *
          (SimulatorModel.fromF D.words D.F_support D.E_support z)⁻¹ := by
  simp only [ReducedWordPeel.prefixElement, map_mul, map_zpow, map_inv, toLiteral_t]
  rw [show (HNNExtension.of : FStage D →* Rebased D) =
    TwistedCentralizer.of (attaching D) (marker D) (f D) from rfl]
  rw [SimulatorDModel.toLiteral_of, SimulatorDModel.toLiteral_of]


theorem positive_prefix (g : FreeGroup (Fin k)) (hg : Accepted D g) :
    ReducedWordPeel.prefixElement (phi D) (codeValue D g) (-1)
      ((f D)⁻¹ * codeValue D g * f D) ∈ recognized D := by
  change toLiteral D _ ∈ recognition D
  rw [toLiteral_prefix]
  simp only [Units.val_neg, Units.val_one, zpow_neg, zpow_one, inv_inv,
    map_mul, map_inv, SimulatorModel.fromF_stable]
  have hm : delta D g ∈ recognition D := Subgroup.subset_closure ⟨g,hg,rfl⟩
  unfold delta at hm
  change literalCode D g * SimulatorRecognitionForward.target D.words *
    (SimulatorRelations.f D.words)⁻¹ * (literalCode D g)⁻¹ *
      SimulatorRelations.f D.words ∈ recognition D at hm
  convert hm using 1
  dsimp [literalCode, codeValue]
  group

theorem negative_prefix (g : FreeGroup (Fin k)) (hg : Accepted D g) :
    ReducedWordPeel.prefixElement (phi D) ((f D)⁻¹ * codeValue D g * f D) 1
      (codeValue D g) ∈ recognized D := by
  change toLiteral D _ ∈ recognition D
  rw [toLiteral_prefix]
  simp only [Units.val_one, zpow_one, map_mul, map_inv, SimulatorModel.fromF_stable]
  have hm : (delta D g)⁻¹ ∈ recognition D :=
    (recognition D).inv_mem (Subgroup.subset_closure ⟨g,hg,rfl⟩)
  convert hm using 1
  dsimp [delta, literalCode, codeValue]
  group

theorem first_coefficient
    (w : ReducedWordPeel.Word (FStage D) (left D).range (right D).range)
    (hhead : w.head ∈ Base D)
    (hD : toLiteral D (w.prod (phi D)) ∈ simulatorD D.words)
    (u : ℤˣ) (a : FStage D) (rest : List (ℤˣ × FStage D))
    (hw : w.toList = (u, a) :: rest) :
    ∃ (g : FreeGroup (Fin k)) (Q : PositiveWord),
      D.code g * positiveFree D.words.P = positiveFree Q ∧
      PositiveEq D.words.rules Q D.words.P ∧
      ((u = -1 ∧ w.head = ofCore D (codeCore D g)) ∨
       (u = 1 ∧ w.head = (f D)⁻¹ * ofCore D (codeCore D g) * f D)) := by
  rcases SimulatorDModel.exists_reducedWord D.words D.F_support D.E_support hD with
    ⟨v, hv, hvhead, hvcoeff⟩
  have heq : w.prod (phi D) = v.prod (phi D) :=
    SimulatorDModel.toLiteral_injective D.words D.F_support D.E_support hv.symm
  rcases ReducedWordPeel.first_comparison (phi D) w v heq u a rest hw with
    ⟨a', rest', hvlist, hcoset, hsigns⟩
  rcases Int.units_eq_one_or u with rfl | rfl
  · have hm : w.head⁻¹ * v.head ∈ (right D).range := by simpa using hcoset
    rcases right_coefficient_factorization D w.head v.head hvhead hm with ⟨x, y, hx, hy, hxy⟩
    rcases negative_coefficient D w.head hhead x y hx hy hxy with ⟨g, Q, hg, hQ, hrec⟩
    exact ⟨g, Q, hQ, hrec, Or.inr ⟨rfl, hg⟩⟩
  · have hm : w.head⁻¹ * v.head ∈ (left D).range := by simpa using hcoset
    rcases left_coefficient_factorization D w.head v.head hvhead hm with ⟨x, y, hx, hy, hxy⟩
    rcases positive_coefficient D w.head hhead x y hx hy hxy with ⟨g, Q, hg, hQ, hrec⟩
    exact ⟨g, Q, hQ, hrec, Or.inl ⟨rfl, hg⟩⟩


theorem recognized_prefix
    (w : ReducedWordPeel.Word (FStage D) (left D).range (right D).range)
    (u : ℤˣ) (a : FStage D) (rest : List (ℤˣ × FStage D))
    (hw : w.toList = (u, a) :: rest) (hhead : w.head ∈ Base D)
    (hD : toLiteral D (w.prod (phi D)) ∈ simulatorD D.words) :
    ∃ z ∈ Base D,
      ReducedWordPeel.prefixElement (phi D) w.head u z ∈ recognized D := by
  rcases first_coefficient D w hhead hD u a rest hw with ⟨g,Q,hQ,hrec,hshape⟩
  have hg : Accepted D g := ⟨Q,hQ,hrec⟩
  have hbase : codeValue D g ∈ Base D := (ofCore_mem_base_iff D _).2 ⟨g,rfl⟩
  rcases hshape with ⟨rfl,hhead'⟩ | ⟨rfl,hhead'⟩
  · refine ⟨(f D)⁻¹ * codeValue D g * f D, ?_, ?_⟩
    · exact (Base D).mul_mem
        ((Base D).mul_mem ((Base D).inv_mem (f_mem_base D)) hbase) (f_mem_base D)
    · rw [hhead']; exact positive_prefix D g hg
  · refine ⟨codeValue D g,hbase,?_⟩
    rw [hhead']; exact negative_prefix D g hg

/-- Every reduced word with B coefficients whose value lies in D is a
product of recognized delta generators and their inverses. -/
theorem reducedWord_mem_recognition
    (w : ReducedWordPeel.Word (FStage D) (left D).range (right D).range)
    (hhead : w.head ∈ Base D) (hcoeff : ∀ p ∈ w.toList, p.2 ∈ Base D)
    (hD : toLiteral D (w.prod (phi D)) ∈ simulatorD D.words) :
    w.prod (phi D) ∈ recognized D := by
  let K : Subgroup (Rebased D) := (simulatorD D.words).comap (toLiteral D)
  apply ReducedWordPeel.mem_of_recognized_prefix (phi D) (Base D) K
    (recognized D) ?_ ?_ ?_ w hhead hcoeff hD
  · intro x hx
    exact recognition_le_D D hx
  · intro g hg hgK
    change toLiteral D (TwistedCentralizer.of (attaching D) (marker D) (f D) g) ∈
      simulatorD D.words at hgK
    rw [SimulatorDModel.toLiteral_of] at hgK
    have hgD := (SimulatorDModel.fromF_mem_D_iff D.words D.F_support D.E_support g).1 hgK
    have hg1 : g = 1 := by
      have hm : g ∈ Base D ⊓ (CD D).map (ofCore D) := ⟨hg, hgD⟩
      rw [base_inf_CD] at hm
      exact hm
    subst g
    simp
  · intro v u a rest hv hvhead hvcoeff hvK
    exact recognized_prefix D v u a rest hv hvhead hvK


theorem intersection_le : simulatorD D.words ⊓ B D ≤ recognition D := by
  rintro x ⟨hxD,hxB⟩
  rcases exists_reducedWord_B D hxB with ⟨w,hw,hhead,hcoeff⟩
  have hD : toLiteral D (w.prod (phi D)) ∈ simulatorD D.words := hw ▸ hxD
  have hm := reducedWord_mem_recognition D w hhead hcoeff hD
  change toLiteral D (w.prod (phi D)) ∈ recognition D at hm
  rwa [hw] at hm

end
end UniversalGroup.HigmanSimulatorB
