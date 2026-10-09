module

public import UniversalGroup.Simulator.Relations
public import UniversalGroup.Simulator.Core.IntersectionsTransport
public import UniversalGroup.Simulator.Core.CoreLift
public import Mathlib.Algebra.Group.Commute.Hom

@[expose] public section

/-!
# A faithful HNN model of the seven-generator simulator

Starting with Borisov's proved `c` stage, adjoin `f` centralizing `<c,d>`
and then `q` centralizing `<c,e>`. The displayed simulator letter is
`t = q*f`. Only the support of the three rule words is used.
-/

namespace UniversalGroup.SimulatorModel

open HNNLemmas

noncomputable section

variable (D : CodeWords) (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i))

abbrev rules := D.supportedRules hF hE
abbrev free := BorisovInputsBridge.rankFiveFree (rules D hF hE)
abbrev Core := BorisovCStage.Gamma2 (rules D hF hE) (free D hF hE)

def coreOf : BorisovHNNModel.Gamma3 →* Core D hF hE :=
  BorisovCStage.of3 (rules D hF hE) (free D hF hE)

def coreC : Core D hF hE := BorisovCStage.c (rules D hF hE) (free D hF hE)

def CD : Subgroup (Core D hF hE) :=
  Subgroup.closure ({coreC D hF hE, coreOf D hF hE BorisovHNNModel.d3} : Set _)

def CE : Subgroup (Core D hF hE) :=
  Subgroup.closure ({coreC D hF hE, coreOf D hF hE BorisovHNNModel.e3} : Set _)

abbrev FStage := CentralizerHNN (Core D hF hE) (CD D hF hE)

def ofF : Core D hF hE →* FStage D hF hE := centralizerOf (CD D hF hE)
def fStable : FStage D hF hE := centralizerStable (CD D hF hE)

def qSubgroup : Subgroup (FStage D hF hE) := (CE D hF hE).map (ofF D hF hE)

abbrev Model := CentralizerHNN (FStage D hF hE) (qSubgroup D hF hE)

def ofQ : FStage D hF hE →* Model D hF hE := centralizerOf (qSubgroup D hF hE)
def coreToModel : Core D hF hE →* Model D hF hE := (ofQ D hF hE).comp (ofF D hF hE)
def lowToModel : BorisovHNNModel.Gamma3 →* Model D hF hE :=
  (coreToModel D hF hE).comp (coreOf D hF hE)

theorem coreToModel_injective : Function.Injective (coreToModel D hF hE) :=
  (HNNExtension.of_injective _).comp (HNNExtension.of_injective _)


def c : Model D hF hE := coreToModel D hF hE (coreC D hF hE)
def d : Model D hF hE := lowToModel D hF hE BorisovHNNModel.d3
def e : Model D hF hE := lowToModel D hF hE BorisovHNNModel.e3
def s : Fin 2 → Model D hF hE :=
  ![lowToModel D hF hE BorisovHNNModel.s1_3, lowToModel D hF hE BorisovHNNModel.s2_3]
def f : Model D hF hE := ofQ D hF hE (fStable D hF hE)
def q : Model D hF hE := centralizerStable (qSubgroup D hF hE)
def t : Model D hF hE := q D hF hE * f D hF hE

def values : Fin 7 → Model D hF hE :=
  ![c D hF hE, d D hF hE, e D hF hE, s D hF hE 0, s D hF hE 1,
    f D hF hE, t D hF hE]

theorem eval_positive (w : PositiveWord) :
    Word.eval (values D hF hE) (simulatorLWords.positive w) =
      lowToModel D hF hE (BorisovCStage.positive3 w) := by
  simp only [SimulatorWords.positive, Word.eval_substitutePositive]
  simp only [BorisovCStage.positive3, evalPositive, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  fin_cases i <;> simp [simulatorLWords, values, s]

theorem d_power (i : Fin 2) : d D hF hE ^ 4 * s D hF hE i = s D hF hE i * d D hF hE := by
  fin_cases i
  · simpa [d, s] using congrArg (lowToModel D hF hE)
      BorisovHNNModel.gamma3_d_four_mul_s1
  · simpa [d, s] using congrArg (lowToModel D hF hE)
      BorisovHNNModel.gamma3_d_four_mul_s2

theorem e_power (i : Fin 2) : e D hF hE * s D hF hE i = s D hF hE i * e D hF hE ^ 4 := by
  fin_cases i
  · simpa [e, s] using congrArg (lowToModel D hF hE) BorisovHNNModel.gamma3_e_mul_s1
  · simpa [e, s] using congrArg (lowToModel D hF hE) BorisovHNNModel.gamma3_e_mul_s2

theorem c_s (i : Fin 2) : Commute (c D hF hE) (s D hF hE i) := by
  have h := (BorisovCStage.c_commutes_stable (rules D hF hE) (free D hF hE) i).symm.map
    (coreToModel D hF hE)
  fin_cases i <;> simpa [c, s, coreC, coreOf, lowToModel, BorisovCStage.stable3] using h

theorem c_f : Commute (c D hF hE) (f D hF hE) := by
  apply Commute.map _ (ofQ D hF hE)
  exact (centralizerOf_commute_stable_iff _ _).2 (Subgroup.subset_closure (by simp))

theorem d_f : Commute (d D hF hE) (f D hF hE) := by
  apply Commute.map _ (ofQ D hF hE)
  exact (centralizerOf_commute_stable_iff _ _).2 (Subgroup.subset_closure (by simp))

theorem c_q : Commute (c D hF hE) (q D hF hE) := by
  apply (centralizerOf_commute_stable_iff _ _).2
  exact ⟨coreC D hF hE, Subgroup.subset_closure (by simp), rfl⟩

theorem e_q : Commute (e D hF hE) (q D hF hE) := by
  apply (centralizerOf_commute_stable_iff _ _).2
  exact ⟨coreOf D hF hE BorisovHNNModel.e3,
    Subgroup.subset_closure (by simp), rfl⟩

theorem c_t : Commute (c D hF hE) (t D hF hE) := (c_q D hF hE).mul_right (c_f D hF hE)

theorem e_t : e D hF hE * t D hF hE =
    t D hF hE * (f D hF hE)⁻¹ * e D hF hE * f D hF hE := by
  simp only [t, mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc, (e_q D hF hE).eq]
  exact mul_assoc _ _ _

theorem rewriting (i : Fin 3) :
    (d D hF hE ^ (i.val + 1))⁻¹ * c D hF hE * d D hF hE ^ (i.val + 1) *
        Word.eval (values D hF hE) (simulatorLWords.positive (D.E i)) =
      Word.eval (values D hF hE) (simulatorLWords.positive (D.F i)) *
        e D hF hE ^ (i.val + 1) * c D hF hE * (e D hF hE ^ (i.val + 1))⁻¹ := by
  rw [eval_positive, eval_positive]
  have h : (c D hF hE)⁻¹ *
      (d D hF hE ^ (i.val + 1) * lowToModel D hF hE (BorisovCStage.positive3 (D.F i)) *
        e D hF hE ^ (i.val + 1)) * c D hF hE =
      d D hF hE ^ (i.val + 1) * lowToModel D hF hE (BorisovCStage.positive3 (D.E i)) *
        e D hF hE ^ (i.val + 1) := by
    have hs := BorisovCStage.c_simulation (rules D hF hE) (free D hF hE) i
    change (coreC D hF hE)⁻¹ * coreOf D hF hE
        (BorisovHNNModel.d3 ^ (i.val + 1) * BorisovCStage.positive3 (D.F i) *
          BorisovHNNModel.e3 ^ (i.val + 1)) * coreC D hF hE =
      coreOf D hF hE (BorisovHNNModel.d3 ^ (i.val + 1) * BorisovCStage.positive3 (D.E i) *
        BorisovHNNModel.e3 ^ (i.val + 1)) at hs
    have hm := congrArg (coreToModel D hF hE) hs
    simp only [map_mul, map_inv, map_pow] at hm
    exact hm
  have hh := congrArg (fun z => (d D hF hE ^ (i.val + 1))⁻¹ * c D hF hE * z *
    (e D hF hE ^ (i.val + 1))⁻¹) h
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel_right,
    inv_mul_cancel_right, mul_inv_cancel, mul_one] using hh.symm

private theorem commutator_eq_one {H : Type*} [Group H] {a b : H} (h : Commute a b) :
    a⁻¹ * b⁻¹ * a * b = 1 := by
  rw [mul_assoc, mul_assoc, h.eq]
  simp

theorem relators (i : Fin 13) :
    Word.eval (values D hF hE) ((simulatorL D).relator i) = 1 := by
  fin_cases i
  all_goals simp only [simulatorL, simulatorLRelators, Matrix.cons_val_zero',
    Matrix.cons_val_succ']
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using d_power D hF hE 0
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using d_power D hF hE 1
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using e_power D hF hE 0
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using e_power D hF hE 1
  · simpa [simulatorLWords, values] using commutator_eq_one (c_s D hF hE 0)
  · simpa [simulatorLWords, values] using commutator_eq_one (c_s D hF hE 1)
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using rewriting D hF hE 0
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using rewriting D hF hE 1
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using rewriting D hF hE 2
  · simpa [simulatorLWords, values] using commutator_eq_one (c_f D hF hE)
  · simpa [simulatorLWords, values] using commutator_eq_one (d_f D hF hE)
  · simpa [simulatorLWords, values] using commutator_eq_one (c_t D hF hE)
  · apply (Word.eval_relation_eq_one_iff _ _ _).2
    simpa [simulatorLWords, values, mul_assoc] using e_t D hF hE

def toModel : (simulatorL D).Group →* Model D hF hE :=
  (simulatorL D).homOfRelators (values D hF hE) (relators D hF hE)

@[simp] theorem toModel_generator (i : Fin 7) :
    toModel D hF hE (generators (simulatorL D) i) = values D hF hE i :=
  FP.homOfRelators_of _ _ _ _

def fromCore : Core D hF hE →* (simulatorL D).Group :=
  CoreLift.lift (rules D hF hE) (free D hF hE)
    (SimulatorRelations.d D) (SimulatorRelations.e D) (SimulatorRelations.s D)
    (SimulatorRelations.c D)
    { d_power := SimulatorRelations.d_power D
      e_power := SimulatorRelations.e_power D
      c_commutes := SimulatorRelations.c_s D
      simulation := SimulatorRelations.rewriting_normalized D }

@[simp] theorem fromCore_c : fromCore D hF hE (coreC D hF hE) = SimulatorRelations.c D := by
  simp [fromCore, coreC]

@[simp] theorem fromCore_d :
    fromCore D hF hE (coreOf D hF hE BorisovHNNModel.d3) = SimulatorRelations.d D := by
  simp [fromCore, coreOf]

@[simp] theorem fromCore_e :
    fromCore D hF hE (coreOf D hF hE BorisovHNNModel.e3) = SimulatorRelations.e D := by
  simp [fromCore, coreOf]

@[simp] theorem fromCore_s1 :
    fromCore D hF hE (coreOf D hF hE BorisovHNNModel.s1_3) = SimulatorRelations.s D 0 := by
  simp [fromCore, coreOf]

@[simp] theorem fromCore_s2 :
    fromCore D hF hE (coreOf D hF hE BorisovHNNModel.s2_3) = SimulatorRelations.s D 1 := by
  simp [fromCore, coreOf]

private theorem commute_closure {A B : Type*} [Group A] [Group B]
    (φ : A →* B) (z : B) (S : Set A) (h : ∀ x ∈ S, Commute z (φ x))
    {x : A} (hx : x ∈ Subgroup.closure S) : Commute z (φ x) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy => simpa using hx.mul_right hy
  | inv x _ hx => simpa using hx.inv_right

theorem fromF_condition (x : CD D hF hE) :
    SimulatorRelations.f D * fromCore D hF hE x =
      fromCore D hF hE x * SimulatorRelations.f D := by
  apply Commute.eq
  apply commute_closure _ _ _ _ x.property
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · simpa using (SimulatorRelations.c_f D).symm
  · simpa using (SimulatorRelations.d_f D).symm

def fromF : FStage D hF hE →* (simulatorL D).Group :=
  HNNExtension.lift (fromCore D hF hE) (SimulatorRelations.f D) (fromF_condition D hF hE)

@[simp] theorem fromF_ofF (x : Core D hF hE) :
    fromF D hF hE (ofF D hF hE x) = fromCore D hF hE x := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem fromF_stable : fromF D hF hE (fStable D hF hE) = SimulatorRelations.f D := by
  exact HNNExtension.lift_t _ _ _

theorem fromModel_condition (x : qSubgroup D hF hE) :
    SimulatorRelations.q D * fromF D hF hE x =
      fromF D hF hE x * SimulatorRelations.q D := by
  rcases x.property with ⟨a, ha, hx⟩
  have h : Commute (SimulatorRelations.q D) (fromCore D hF hE a) := by
    apply commute_closure _ _ _ _ ha
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · simpa using (SimulatorRelations.c_q D).symm
    · simpa using (SimulatorRelations.e_q D).symm
  rw [← hx, fromF_ofF]
  exact h.eq

def fromModel : Model D hF hE →* (simulatorL D).Group :=
  HNNExtension.lift (fromF D hF hE) (SimulatorRelations.q D) (fromModel_condition D hF hE)

@[simp] theorem fromModel_ofQ (x : FStage D hF hE) :
    fromModel D hF hE (ofQ D hF hE x) = fromF D hF hE x := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem fromModel_q : fromModel D hF hE (q D hF hE) = SimulatorRelations.q D := by
  exact HNNExtension.lift_t _ _ _

@[simp] theorem fromModel_core (x : Core D hF hE) :
    fromModel D hF hE (coreToModel D hF hE x) = fromCore D hF hE x := by
  simp [coreToModel]

@[simp] theorem fromModel_values (i : Fin 7) :
    fromModel D hF hE (values D hF hE i) = generators (simulatorL D) i := by
  fin_cases i <;> simp [values, c, d, e, s, f, t, lowToModel,
    SimulatorRelations.c, SimulatorRelations.d, SimulatorRelations.e,
    SimulatorRelations.s, SimulatorRelations.f, SimulatorRelations.q,
    SimulatorRelations.t, mul_assoc]

theorem fromModel_comp_toModel :
    (fromModel D hF hE).comp (toModel D hF hE) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  change fromModel D hF hE (toModel D hF hE (generators (simulatorL D) i)) = _
  rw [toModel_generator, fromModel_values]
  rfl

theorem toModel_fromCore (x : Core D hF hE) :
    toModel D hF hE (fromCore D hF hE x) = coreToModel D hF hE x := by
  have h : (toModel D hF hE).comp (fromCore D hF hE) = coreToModel D hF hE := by
    apply CoreLift.hom_ext
    · change toModel D hF hE (fromCore D hF hE (coreC D hF hE)) = c D hF hE
      simp [SimulatorRelations.c, values]
    · change toModel D hF hE (fromCore D hF hE (coreOf D hF hE BorisovHNNModel.d3)) = d D hF hE
      simp [SimulatorRelations.d, values]
    · change toModel D hF hE (fromCore D hF hE (coreOf D hF hE BorisovHNNModel.e3)) = e D hF hE
      simp [SimulatorRelations.e, values]
    · change toModel D hF hE (fromCore D hF hE (coreOf D hF hE BorisovHNNModel.s1_3)) = s D hF hE 0
      simp [SimulatorRelations.s, values]
    · change toModel D hF hE (fromCore D hF hE (coreOf D hF hE BorisovHNNModel.s2_3)) = s D hF hE 1
      simp [SimulatorRelations.s, values]
  exact DFunLike.congr_fun h x

theorem toModel_fromF (x : FStage D hF hE) :
    toModel D hF hE (fromF D hF hE x) = ofQ D hF hE x := by
  have h : (toModel D hF hE).comp (fromF D hF hE) = ofQ D hF hE := by
    apply HNNExtension.hom_ext
    · apply MonoidHom.ext
      intro x
      exact toModel_fromCore D hF hE x
    · change toModel D hF hE (fromF D hF hE (fStable D hF hE)) = f D hF hE
      simp [SimulatorRelations.f, values]
  exact DFunLike.congr_fun h x

theorem toModel_comp_fromModel :
    (toModel D hF hE).comp (fromModel D hF hE) = MonoidHom.id _ := by
  apply HNNExtension.hom_ext
  · apply MonoidHom.ext
    intro x
    exact toModel_fromF D hF hE x
  · change toModel D hF hE (fromModel D hF hE (q D hF hE)) = q D hF hE
    simp [SimulatorRelations.q, SimulatorRelations.t, SimulatorRelations.f, values, t]

/-- The literal thirteen-relator simulator is exactly the faithful HNN tower. -/
def equiv : (simulatorL D).Group ≃* Model D hF hE where
  toFun := toModel D hF hE
  invFun := fromModel D hF hE
  left_inv := DFunLike.congr_fun (fromModel_comp_toModel D hF hE)
  right_inv := DFunLike.congr_fun (toModel_comp_fromModel D hF hE)
  map_mul' := map_mul (toModel D hF hE)

theorem fromModel_injective : Function.Injective (fromModel D hF hE) :=
  (equiv D hF hE).symm.injective

/-- The whole five-generator core embeds in the literal simulator. -/
theorem fromCore_injective : Function.Injective (fromCore D hF hE) := by
  intro x y h
  apply coreToModel_injective D hF hE
  simpa only [toModel_fromCore] using congrArg (toModel D hF hE) h

end
end UniversalGroup.SimulatorModel
