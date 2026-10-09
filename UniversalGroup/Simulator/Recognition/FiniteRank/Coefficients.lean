module

public import UniversalGroup.Simulator.Recognition.Core
public import UniversalGroup.Simulator.Recognition.Forward

@[expose] public section

/-!
# Recognition for arbitrary finite-rank code subgroups

The subgroup on the codewords and `f` meets the simulator core exactly in
the code subgroup. This reduces the first coefficient of a `T`-normal-form
comparison to the signed c-stage recognition theorem.
-/

namespace UniversalGroup.HigmanSimulatorB

open SimulatorModel SimulatorFreeLetters BorisovCStage HNNLemmas

noncomputable section

/-- Arbitrary finitely many injected signed input codes in a supported simulator. -/
structure Data (k : ℕ) where
  words : CodeWords
  F_support : ∀ i, ContainsBoth (words.F i)
  E_support : ∀ i, ContainsBoth (words.E i)
  code : FreeGroup (Fin k) →* FreeGroup (Fin 2)
  code_injective : Function.Injective code

variable {k : ℕ} (D : Data k)

abbrev Core := SimulatorModel.Core D.words D.F_support D.E_support
abbrev FStage := SimulatorModel.FStage D.words D.F_support D.E_support
abbrev ofCore : Core D →* FStage D := ofF D.words D.F_support D.E_support
abbrev pCore : Core D :=
  coreOf D.words D.F_support D.E_support (positive3 D.words.P)
abbrev f : FStage D := fStable D.words D.F_support D.E_support
abbrev CD : Subgroup (Core D) := SimulatorModel.CD D.words D.F_support D.E_support
abbrev CE : Subgroup (Core D) := SimulatorModel.CE D.words D.F_support D.E_support

def codeCore : FreeGroup (Fin k) →* Core D :=
  (coreLetters D.words D.F_support D.E_support).comp (D.code)

def baseLift : FreeGroup (Fin (k+1)) →* FStage D :=
  AdjoinFree.hom (CD D) (codeCore D)

def Base : Subgroup (FStage D) := (baseLift D).range

@[simp] theorem baseLift_old (i : Fin k) :
    baseLift D (FreeGroup.of i.castSucc) = ofCore D (codeCore D (FreeGroup.of i)) :=
  AdjoinFree.hom_old _ _ i

@[simp] theorem baseLift_f : baseLift D (FreeGroup.of (Fin.last k)) = f D :=
  AdjoinFree.hom_last _ _

theorem f_mem_base : f D ∈ Base D := ⟨FreeGroup.of (Fin.last k), baseLift_f D⟩

theorem codeCore_mem_letters (w : FreeGroup (Fin k)) :
    codeCore D w ∈ (coreLetters D.words D.F_support D.E_support).range :=
  ⟨D.code w, rfl⟩

theorem base_inf_core : Base D ⊓ (ofCore D).range =
    (codeCore D).range.map (ofCore D) :=
  AdjoinFree.range_hom_inf_base _ _

theorem ofCore_mem_base_iff (x : Core D) :
    ofCore D x ∈ Base D ↔ x ∈ (codeCore D).range := by
  constructor
  · intro hx
    have hm : ofCore D x ∈ Base D ⊓ (ofCore D).range := ⟨hx, ⟨x, rfl⟩⟩
    rw [base_inf_core] at hm
    rcases hm with ⟨y, hy, hyx⟩
    exact (HNNExtension.of_injective _ hyx) ▸ hy
  · intro hx
    have hm : ofCore D x ∈ (codeCore D).range.map (ofCore D) := ⟨x, hx, rfl⟩
    rw [← base_inf_core] at hm
    exact hm.1

theorem base_inf_CD : Base D ⊓ (CD D).map (ofCore D) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨hx, y, hy, rfl⟩
  rcases (ofCore_mem_base_iff D y).1 hx with ⟨w, rfl⟩
  have hm : codeCore D w ∈ (⊥ : Subgroup (Core D)) := by
    rw [← coreLetters_inf_CD D.words D.F_support D.E_support]
    exact ⟨codeCore_mem_letters D w, hy⟩
  have heq : codeCore D w = 1 := hm
  simp [heq]

theorem sLift3_positiveFree (w : PositiveWord) :
    sLift3 (BorisovCStage.positiveFree w) = positive3 w := by
  rw [positiveFree_eq_eval, CodeSubgroups.map_positive]
  simp only [sLift3, FreeGroup.lift_apply_of]
  rfl

theorem coreLetters_eq_sLift2 :
    coreLetters D.words D.F_support D.E_support =
      sLift2 (rules D.words D.F_support D.E_support)
        (free D.words D.F_support D.E_support) := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [coreLetters, lowLetters, sLift2, sLift3, stable3, coreOf]

theorem pCore_mem_letters :
    pCore D ∈ (coreLetters D.words D.F_support D.E_support).range := by
  refine ⟨BorisovCStage.positiveFree D.words.P, ?_⟩
  rw [coreLetters_eq_sLift2]
  change coreOf D.words D.F_support D.E_support
    (sLift3 (BorisovCStage.positiveFree D.words.P)) = _
  rw [sLift3_positiveFree]

/-- The left attaching subgroup for the rebased letter `T` is disjoint
from the base of `B`. -/
theorem attaching_left_disjoint (v : Core D) (hv : v ∈ CE D)
    (hb : ofCore D (pCore D * v * (pCore D)⁻¹) ∈ Base D) : v = 1 := by
  rcases (ofCore_mem_base_iff D _).1 hb with ⟨w, hw⟩
  have hletters : pCore D * v * (pCore D)⁻¹ ∈
      (coreLetters D.words D.F_support D.E_support).range :=
    hw ▸ codeCore_mem_letters D w
  have hvletters : v ∈ (coreLetters D.words D.F_support D.E_support).range := by
    have hm := ((coreLetters D.words D.F_support D.E_support).range.mul_mem
      (((coreLetters D.words D.F_support D.E_support).range.inv_mem
        (pCore_mem_letters D))) hletters)
    have hn := (coreLetters D.words D.F_support D.E_support).range.mul_mem hm
      (pCore_mem_letters D)
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hn
  have hm : v ∈ (⊥ : Subgroup (Core D)) := by
    rw [← coreLetters_inf_CE D.words D.F_support D.E_support]
    exact ⟨hvletters, hv⟩
  exact hm

/-- The right attaching subgroup is its conjugate by `f`, which belongs
to the base of `B`, so it is disjoint as well. -/
theorem attaching_right_disjoint (v : Core D) (hv : v ∈ CE D)
    (hb : (f D)⁻¹ * ofCore D (pCore D * v * (pCore D)⁻¹) * f D ∈
      Base D) : v = 1 := by
  apply attaching_left_disjoint D v hv
  have hm := (Base D).mul_mem ((Base D).mul_mem (f_mem_base D) hb)
    ((Base D).inv_mem (f_mem_base D))
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hm

/-- A positive-sign first coefficient gives a signed code word whose
product with the marker is positive and semigroup-equivalent to the marker. -/
theorem positive_coefficient
    (b : FStage D) (hb : b ∈ Base D)
    (u v : Core D) (hu : u ∈ CD D) (hv : v ∈ CE D)
    (heq : b = ofCore D (u * pCore D * v * (pCore D)⁻¹)) :
    ∃ (g : FreeGroup (Fin k)) (Q : PositiveWord),
      b = ofCore D (codeCore D g) ∧
      D.code g * BorisovCStage.positiveFree D.words.P =
        BorisovCStage.positiveFree Q ∧ PositiveEq D.words.rules Q D.words.P := by
  have hm : u * pCore D * v * (pCore D)⁻¹ ∈ (codeCore D).range :=
    (ofCore_mem_base_iff D _).1 (heq ▸ hb)
  rcases hm with ⟨g, hg⟩
  let R := rules D.words D.F_support D.E_support
  let hf := free D.words D.F_support D.E_support
  have hcontext : sLift2 R hf
      (D.code g * BorisovCStage.positiveFree D.words.P) =
        u * positive2 R hf D.words.P * v := by
    rw [map_mul]
    have hg' : sLift2 R hf (D.code g) =
        u * pCore D * v * (pCore D)⁻¹ := by
      rw [← coreLetters_eq_sLift2 D]
      exact hg
    rw [hg']
    change (u * pCore D * v * (pCore D)⁻¹) *
      coreOf D.words D.F_support D.E_support (sLift3 (BorisovCStage.positiveFree D.words.P)) = _
    rw [sLift3_positiveFree]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rfl
  rcases SimulatorRecognitionCore.of_context_factorization R hf _ D.words.P u v hu hv hcontext with
    ⟨Q, hQ, hrec⟩
  exact ⟨g, Q, heq.trans (congrArg (ofCore D) hg.symm), hQ, hrec⟩

/-- The corresponding negative-sign coefficient is an `f`-conjugate of
the same kind of recognized signed code word. -/
theorem negative_coefficient
    (b : FStage D) (hb : b ∈ Base D)
    (u v : Core D) (hu : u ∈ CD D) (hv : v ∈ CE D)
    (heq : b = (f D)⁻¹ * ofCore D (u * pCore D * v * (pCore D)⁻¹) * f D) :
    ∃ (g : FreeGroup (Fin k)) (Q : PositiveWord),
      b = (f D)⁻¹ * ofCore D (codeCore D g) * f D ∧
      D.code g * BorisovCStage.positiveFree D.words.P =
        BorisovCStage.positiveFree Q ∧ PositiveEq D.words.rules Q D.words.P := by
  have hm : f D * b * (f D)⁻¹ ∈ Base D :=
    (Base D).mul_mem ((Base D).mul_mem (f_mem_base D) hb)
      ((Base D).inv_mem (f_mem_base D))
  have heq' : f D * b * (f D)⁻¹ =
      ofCore D (u * pCore D * v * (pCore D)⁻¹) := by
    rw [heq]
    group
  rcases positive_coefficient D _ hm u v hu hv heq' with ⟨g, Q, hg, hQ, hrec⟩
  refine ⟨g, Q, ?_, hQ, hrec⟩
  have hh := congrArg (fun x => (f D)⁻¹ * x * f D) hg
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

end

end UniversalGroup.HigmanSimulatorB
