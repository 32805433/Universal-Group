module

public import UniversalGroup.Simulator.Data
public import UniversalGroup.Foundations.HNN.NormalForms
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# The simulator's centralizer HNN extension

The literal sixteen-relator presentation is isomorphic to the actual HNN
extension centralizing `simulatorD`. The comparison preserves all old
simulator generators and identifies `k` with the stable letter. No support
or recognition hypotheses are needed. The canonical map on `(f,k)` records
the two coordinates used in the source-subgroup construction.
-/

namespace UniversalGroup
namespace SimulatorCentralizer

open HNNLemmas

noncomputable section

abbrev Model (D : CodeWords) :=
  CentralizerHNN (simulatorL D).Group (simulatorD D)

private theorem commutator_eq_one_iff {H : Type*} [Group H] (x y : H) :
    x⁻¹ * y⁻¹ * x * y = 1 ↔ Commute x y := by
  constructor
  · intro h
    change x * y = y * x
    calc
      x * y = (y * x) * (x⁻¹ * y⁻¹ * x * y) := by group
      _ = y * x := by rw [h, mul_one]
  · intro h
    calc
      x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
      _ = 1 := by rw [h.eq]; group

/-- Images of the eight displayed generators in the genuine HNN extension. -/
def modelValues (D : CodeWords) : Fin 8 → Model D :=
  Fin.append
    (fun i => centralizerOf (simulatorD D) (generators (simulatorL D) i))
    ![centralizerStable (simulatorD D)]

theorem modelValues_old_word (D : CodeWords) (w : Word 7) :
    Word.eval (modelValues D) (Word.mapGenerators (Fin.castAdd 1) w) =
      centralizerOf (simulatorD D) ((simulatorL D).evalWord w) := by
  rw [Word.eval_mapGenerators, FP.evalWord, Word.map_eval]
  congr 1
  funext i
  simp [modelValues, generators]

theorem centralizes_basis (D : CodeWords) (i : Fin 3) :
    Commute
      (centralizerOf (simulatorD D) ((simulatorL D).evalWord
        (![simulatorLWords.c, simulatorLWords.d, simulatorLWords.T D] i)))
      (centralizerStable (simulatorD D)) := by
  apply (centralizerOf_commute_stable_iff _ _).mpr
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem model_relators (D : CodeWords) (i : Fin 16) :
    Word.eval (modelValues D) ((simulatorK D).relator i) = 1 := by
  refine Fin.addCases (m := 13) (n := 3) (fun j => ?_) (fun j => ?_) i
  · simp only [simulatorK, Fin.append_left, modelValues_old_word,
      FP.relator_eq_one, map_one]
  · simp only [simulatorK, Fin.append_right]
    fin_cases j
    · change Word.eval (modelValues D)
        (Word.commutator (Word.mapGenerators (Fin.castAdd 1) (simulatorLWords.T D))
          (Word.generator 7)) = 1
      simp only [Word.eval_commutator,
        modelValues_old_word, Word.eval_generator]
      exact (commutator_eq_one_iff _ _).mpr (centralizes_basis D 2)
    · have h := (commutator_eq_one_iff _ _).mpr (centralizes_basis D 0)
      simpa [modelValues, FP.evalWord, simulatorLWords, generators,
        Fin.append, Fin.addCases] using h
    · have h := (commutator_eq_one_iff _ _).mpr (centralizes_basis D 1)
      simpa [modelValues, FP.evalWord, simulatorLWords, generators,
        Fin.append, Fin.addCases] using h

def toModel (D : CodeWords) : (simulatorK D).Group →* Model D :=
  (simulatorK D).homOfRelators (modelValues D) (model_relators D)

@[simp] theorem toModel_generator (D : CodeWords) (i : Fin 8) :
    toModel D (generators (simulatorK D) i) = modelValues D i :=
  FP.homOfRelators_of _ _ _ _

@[simp] theorem toModel_old (D : CodeWords) (i : Fin 7) :
    toModel D (generators (simulatorK D) (Fin.castAdd 1 i)) =
      centralizerOf (simulatorD D) (generators (simulatorL D) i) := by
  simp [modelValues]

@[simp] theorem toModel_k (D : CodeWords) :
    toModel D (generators (simulatorK D) 7) =
      centralizerStable (simulatorD D) := by
  simp [modelValues, Fin.append, Fin.addCases]

theorem toModel_inclusion (D : CodeWords) :
    (toModel D).comp (simulatorInclusion D) = centralizerOf (simulatorD D) := by
  apply PresentedGroup.ext
  intro i
  simp [toModel, simulatorInclusion, modelValues, generators]

theorem inclusion_old_word (D : CodeWords) (w : Word 7) :
    simulatorInclusion D ((simulatorL D).evalWord w) =
      (simulatorK D).evalWord (Word.mapGenerators (Fin.castAdd 1) w) := by
  simp [simulatorInclusion, FP.evalWord, Word.map_eval, generators,
    Function.comp_def]

theorem inclusion_basis_commutes_k (D : CodeWords) (i : Fin 3) :
    Commute
      (simulatorInclusion D ((simulatorL D).evalWord
        (![simulatorLWords.c, simulatorLWords.d, simulatorLWords.T D] i)))
      (generators (simulatorK D) 7) := by
  apply (commutator_eq_one_iff _ _).mp
  rw [inclusion_old_word]
  fin_cases i
  · have h := (simulatorK D).relator_eq_one 14
    change Word.eval (generators (simulatorK D))
      (Word.commutator (Word.generator 0) (Word.generator 7)) = 1 at h
    simpa [FP.evalWord, simulatorLWords, generators, Function.comp_def] using h
  · have h := (simulatorK D).relator_eq_one 15
    change Word.eval (generators (simulatorK D))
      (Word.commutator (Word.generator 1) (Word.generator 7)) = 1 at h
    simpa [FP.evalWord, simulatorLWords, generators, Function.comp_def] using h
  · have h := (simulatorK D).relator_eq_one 13
    change Word.eval (generators (simulatorK D))
      (Word.commutator (Word.mapGenerators (Fin.castAdd 1) (simulatorLWords.T D))
        (Word.generator 7)) = 1 at h
    simpa [FP.evalWord, generators, Function.comp_def] using h

theorem inclusion_commutes_k (D : CodeWords) {x : (simulatorL D).Group}
    (hx : x ∈ simulatorD D) :
    Commute (simulatorInclusion D x) (generators (simulatorK D) 7) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact inclusion_basis_commutes_k D i
  | one => simp
  | mul x y _ _ hx hy => simpa using hx.mul_left hy
  | inv x _ hx => simpa using hx.inv_left

def fromModel (D : CodeWords) : Model D →* (simulatorK D).Group :=
  HNNExtension.lift (simulatorInclusion D) (generators (simulatorK D) 7) (by
    intro a
    exact (inclusion_commutes_k D a.property).symm.eq)

@[simp] theorem fromModel_of (D : CodeWords) (x : (simulatorL D).Group) :
    fromModel D (centralizerOf (simulatorD D) x) = simulatorInclusion D x := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem fromModel_stable (D : CodeWords) :
    fromModel D (centralizerStable (simulatorD D)) =
      generators (simulatorK D) 7 := by
  exact HNNExtension.lift_t _ _ _

theorem fromModel_comp_toModel (D : CodeWords) :
    (fromModel D).comp (toModel D) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  refine Fin.addCases (m := 7) (n := 1) (fun j => ?_) (fun j => ?_) i
  · simp [generators, toModel, modelValues, simulatorInclusion]
  · fin_cases j
    simp [generators, toModel, modelValues, Fin.append, Fin.addCases]

theorem toModel_comp_fromModel (D : CodeWords) :
    (toModel D).comp (fromModel D) = MonoidHom.id _ := by
  apply HNNExtension.hom_ext
  · apply MonoidHom.ext
    intro x
    change toModel D (simulatorInclusion D x) = centralizerOf (simulatorD D) x
    exact DFunLike.congr_fun (toModel_inclusion D) x
  · exact (congrArg (toModel D) (fromModel_stable D)).trans (toModel_k D)

/-- The literal presentation has exactly the intended centralizer-HNN
structure, with all named generator images fixed. -/
def equiv (D : CodeWords) : (simulatorK D).Group ≃* Model D where
  toFun := toModel D
  invFun := fromModel D
  left_inv x := DFunLike.congr_fun (fromModel_comp_toModel D) x
  right_inv x := DFunLike.congr_fun (toModel_comp_fromModel D) x
  map_mul' := map_mul (toModel D)

@[simp] theorem equiv_inclusion (D : CodeWords) (x : (simulatorL D).Group) :
    equiv D (simulatorInclusion D x) = centralizerOf (simulatorD D) x :=
  DFunLike.congr_fun (toModel_inclusion D) x

@[simp] theorem equiv_k (D : CodeWords) :
    equiv D (generators (simulatorK D) 7) = centralizerStable (simulatorD D) :=
  toModel_k D

/-- Britton's centralizer test for the literal simulator presentation. -/
theorem inclusion_commute_k_iff (D : CodeWords) (x : (simulatorL D).Group) :
    Commute (simulatorInclusion D x) (generators (simulatorK D) 7) ↔
      x ∈ simulatorD D := by
  constructor
  · intro h
    apply (centralizerOf_commute_stable_iff (simulatorD D) x).mp
    rw [commute_iff_eq]
    have hh := congrArg (equiv D) h
    simpa only [map_mul, equiv_inclusion, equiv_k] using hh
  · exact inclusion_commutes_k D

/-- The canonical free-group map on the two simulator letters `f,k`. -/
def fk (D : CodeWords) : FreeGroup (Fin 2) →* (simulatorK D).Group :=
  FreeGroup.lift ![generators (simulatorK D) 5, generators (simulatorK D) 7]

@[simp] theorem fk_of_zero (D : CodeWords) :
    fk D (FreeGroup.of 0) = generators (simulatorK D) 5 := by simp [fk]

@[simp] theorem fk_of_one (D : CodeWords) :
    fk D (FreeGroup.of 1) = generators (simulatorK D) 7 := by simp [fk]

end
end SimulatorCentralizer
end UniversalGroup
