module

public import UniversalGroup.Embedding.PositiveHost.HGrid
public import UniversalGroup.Host.AStage
public import UniversalGroup.Host.BStage

@[expose] public section

/-!
# A faithful model of the six-generator presentation

The positive `h` extension, column shift by `a`, and row extension by `b`
preserve the input and the row/column grid. This module records their
coordinates; comparison with the positive nineteen-relator presentation is separate.
-/

namespace UniversalGroup.Embedding.PositiveHost.BaseModel
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

variable (G : PreparedInput) (D : ValievDatum G) (hi : ValievIntersections G D)

abbrev U := InputFreeSubgroup.Domain G
abbrev AStage := ShiftCompression.Stage (U G) (HGrid.product G D hi) (HGrid.product_injective G D hi)
abbrev aGrid : U G × FreeGroup (Fin 2) →* AStage G D hi :=
  ShiftCompression.productEmbedding (U G) (HGrid.product G D hi) (HGrid.product_injective G D hi)
theorem aGrid_injective : Function.Injective (aGrid G D hi) :=
  ShiftCompression.productEmbedding_injective _ _ _

abbrev Model := BCompression.Model G (aGrid G D hi) (aGrid_injective G D hi)
def ofA : AStage G D hi →* Model G D hi := BCompression.of _ _ _
def ofH : HStage.Model G D hi →* Model G D hi :=
  (ofA G D hi).comp (ShiftCompression.inclusion _ _ _)
def ofEll : EllStage.Model G D hi →* Model G D hi :=
  (ofH G D hi).comp (HStage.ofEll G D hi)
def sim : (simulatorK D.toCodeWords).Group →* Model G D hi :=
  (ofH G D hi).comp (HStage.simulatorEmbedding G D hi).hom

theorem ofH_injective : Function.Injective (ofH G D hi) :=
  (BCompression.of_injective _ _ _).comp (ShiftCompression.inclusion_injective _ _ _)
def input : G.presentation.Group →* Model G D hi :=
  (ofH G D hi).comp (HStage.inputEmbedding G D hi).hom

theorem input_injective : Function.Injective (input G D hi) :=
  (ofH_injective G D hi).comp (HStage.inputEmbedding G D hi).injective

def c : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 0)
def d : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 1)
def e : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 2)
def s1 : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 3)
def s2 : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 4)
def f : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 5)
def t : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 6)
def k : Model G D hi := sim G D hi (generators (simulatorK D.toCodeWords) 7)
def h : Model G D hi := ofH G D hi (HStage.stable G D hi)
def ell : Model G D hi := ofEll G D hi (EllStage.ell G D hi)
def a : Model G D hi := ofA G D hi (ShiftCompression.a _ _ _)
def b : Model G D hi := BCompression.b _ _ _
def u (i : Fin 2) : Model G D hi := input G D hi (generators G.presentation i)
def positive (w : PositiveWord) : Model G D hi := evalPositive (s1 G D hi) (s2 G D hi) w

def embeddedGrid : U G × FreeGroup (Fin 2) →* Model G D hi :=
  BCompression.embeddedGrid _ _ _

theorem embeddedGrid_left (v : U G) :
    embeddedGrid G D hi (v,1) = ofEll G D hi (InputFreeSubgroup.hom G D hi v) := by
  change ofA G D hi (aGrid G D hi (v,1)) = _
  rw [ShiftCompression.productEmbedding_u, HGrid.product_left]
  rfl

theorem embeddedGrid_c : embeddedGrid G D hi (InputTriples.c G,1) = c G D hi := by
  rw [embeddedGrid_left]
  simp [InputTriples.c, InputFreeSubgroup.hom_c, InputFreeSubgroup.cPowers,
    zpowersHom_apply, c, sim, ofEll, HStage.simulatorEmbedding]

theorem embeddedGrid_input (i : Fin 2) :
    embeddedGrid G D hi (InputTriples.input G i,1) = u G D hi i := by
  rw [embeddedGrid_left]
  simp only [InputTriples.input, InputFreeSubgroup.hom_input]
  rfl

theorem embeddedGrid_ell : embeddedGrid G D hi (InputTriples.ell G,1) = ell G D hi := by
  rw [embeddedGrid_left]
  simp [InputTriples.ell, InputFreeSubgroup.hom_ell, ell]

theorem embeddedGrid_a : embeddedGrid G D hi (1,FreeGroup.of 0) = a G D hi := by
  exact congrArg (ofA G D hi) (ShiftCompression.productEmbedding_a _ _ _)

theorem embeddedGrid_x : embeddedGrid G D hi (1,FreeGroup.of 1) =
    (k G D hi)⁻¹ * f G D hi * k G D hi := by
  change ofA G D hi (aGrid G D hi (1,FreeGroup.of 1)) = _
  rw [ShiftCompression.productEmbedding_x, HGrid.product_x0]
  simp [ofH, sim, k, f, simulatorGridValues, mul_assoc]

def pair : FreeGroup (Fin 2) →* Model G D hi :=
  (embeddedGrid G D hi).comp (MonoidHom.inr _ _)

theorem pair_a : pair G D hi (FreeGroup.of 0) = a G D hi := embeddedGrid_a G D hi
theorem pair_x : pair G D hi (FreeGroup.of 1) =
    (k G D hi)⁻¹ * f G D hi * k G D hi := embeddedGrid_x G D hi

theorem embeddedGrid_columns (v : U G) (w : FreeGroup (Fin 4)) :
    embeddedGrid G D hi (v,ShiftCompression.columns w) =
      ofH G D hi (HGrid.product G D hi (v,w)) := by
  exact congrArg (ofA G D hi) (ShiftCompression.productEmbedding_columns _ _ _ v w)

theorem old_column (i : Fin 4) :
    ofH G D hi (HGrid.product G D hi (1,FreeGroup.of i)) =
      (a G D hi ^ i.val)⁻¹ * ((k G D hi)⁻¹ * f G D hi * k G D hi) * a G D hi ^ i.val := by
  have hh := embeddedGrid_columns G D hi 1 (FreeGroup.of i)
  change pair G D hi (ShiftCompression.columns (FreeGroup.of i)) = _ at hh
  simpa only [ShiftCompression.columns, FreeGroup.lift_apply_of, map_mul, map_pow,
    map_inv, pair_a, pair_x, inv_pow] using hh.symm

theorem column_one :
    (a G D hi)⁻¹ * ((k G D hi)⁻¹ * f G D hi * k G D hi) * a G D hi =
      (f G D hi)⁻¹ * s1 G D hi * f G D hi := by
  have hh := old_column G D hi 1
  rw [HGrid.product_x1] at hh
  simpa [sim, ofH, simulatorGridValues, FP.evalWord, SimulatorWords.x,
    simulatorLWords, simulatorInclusion, generators, f, s1, mul_assoc] using hh.symm

theorem column_two :
    (a G D hi ^ 2)⁻¹ * ((k G D hi)⁻¹ * f G D hi * k G D hi) * a G D hi ^ 2 = h G D hi := by
  have hh := old_column G D hi 2
  rw [HGrid.product_h] at hh
  exact hh.symm

theorem sim_positive (w : PositiveWord) :
    sim G D hi (simulatorInclusion D.toCodeWords
      ((simulatorL D.toCodeWords).evalWord (simulatorLWords.positive w))) = positive G D hi w := by
  rw [SimulatorRelations.eval_positive]
  simp only [SimulatorRelations.positive, CodeSubgroups.map_positive]
  simp [SimulatorRelations.s, simulatorInclusion, generators, positive, s1, s2]

theorem column_three :
    positive G D hi D.P * t G D hi =
      (a G D hi ^ 3)⁻¹ * ((k G D hi)⁻¹ * f G D hi * k G D hi) * a G D hi ^ 3 := by
  have hh := old_column G D hi 3
  rw [HGrid.product_x3] at hh
  change sim G D hi (simulatorInclusion D.toCodeWords
    ((simulatorL D.toCodeWords).evalWord
      (Word.product [simulatorLWords.positive D.P, simulatorLWords.t]))) = _ at hh
  have heval : (simulatorL D.toCodeWords).evalWord
      (Word.product [simulatorLWords.positive D.P, simulatorLWords.t]) =
      (simulatorL D.toCodeWords).evalWord (simulatorLWords.positive D.P) *
        generators (simulatorL D.toCodeWords) 6 := by
    simp [FP.evalWord, simulatorLWords, generators]
  rw [heval, map_mul, map_mul, sim_positive] at hh
  simpa [simulatorInclusion, generators, t] using hh

theorem h_d :
    (h G D hi)⁻¹ * d G D hi * h G D hi = (f G D hi)⁻¹ * e G D hi * f G D hi := by
  have hh := congrArg (ofH G D hi) (HStage.conjugates_d G D hi)
  simpa [h, d, e, f, sim, HStage.ofL, SimulatorSymmetry.e0,
    SimulatorRelations.d, SimulatorRelations.e, SimulatorRelations.f,
    simulatorInclusion, generators, mul_assoc] using hh

theorem h_f :
    (h G D hi)⁻¹ * f G D hi * h G D hi = (f G D hi)⁻¹ * t G D hi := by
  have hh := congrArg (ofH G D hi) (HStage.conjugates_f G D hi)
  simpa [h, f, t, sim, HStage.ofL, SimulatorSymmetry.q0,
    SimulatorRelations.q, SimulatorRelations.t, SimulatorRelations.f,
    simulatorInclusion, generators, mul_assoc] using hh

theorem h_x1 :
    (h G D hi)⁻¹ * ((f G D hi)⁻¹ * s1 G D hi * f G D hi) * h G D hi =
      ((f G D hi)⁻¹ * s2 G D hi * f G D hi)⁻¹ := by
  have hh := congrArg (ofH G D hi) (HStage.conjugates_x1 G D hi)
  simpa [h, f, s1, s2, sim, HStage.ofL, SimulatorSymmetry.x,
    SimulatorWords.x, FP.evalWord, simulatorLWords,
    SimulatorRelations.s, SimulatorRelations.f,
    simulatorInclusion, generators, mul_assoc] using hh

theorem attachment (i : Fin 2) :
    positive G D hi (D.code i) * ell G D hi =
      ell G D hi * positive G D hi (D.code i) * f G D hi * u G D hi i * (f G D hi)⁻¹ := by
  have hh := congrArg (ofEll G D hi) (EllStage.attachment G D hi i)
  have hp : ofEll G D hi (EllStage.ofM G D hi
      (EllStage.a G D i.castSucc.castSucc.castSucc)) = positive G D hi (D.code i) := by
    change sim G D hi (simulatorInclusion D.toCodeWords
      (CodeSubgroups.aValues D.toCodeWords i.castSucc.castSucc.castSucc)) = _
    have hv : CodeSubgroups.aValues D.toCodeWords i.castSucc.castSucc.castSucc =
        (simulatorL D.toCodeWords).evalWord (simulatorLWords.positive (D.code i)) := by
      fin_cases i <;> rfl
    rw [hv, sim_positive]
  have hf : ofEll G D hi (EllStage.ofM G D hi (EllStage.f G D)) = f G D hi := by
    change sim G D hi (simulatorInclusion D.toCodeWords
      (SimulatorRelations.f D.toCodeWords)) = _
    simp [SimulatorRelations.f, simulatorInclusion, generators, f]
  have hu : ofEll G D hi (EllStage.ofM G D hi (EllStage.u G D i)) = u G D hi i := rfl
  simpa only [map_mul, map_inv, hp, hf, hu, ell, mul_assoc] using hh

theorem ell_code (i : Fin 2) :
    Commute (ell G D hi) ((k G D hi)⁻¹ * positive G D hi (D.code i) * k G D hi) := by
  let x : simulatorB D.toCodeWords :=
    ⟨CodeSubgroups.bValues D.toCodeWords i.castSucc.castSucc,
      (CodeSubgroups.bLift_range D.toCodeWords) ▸
        ⟨FreeGroup.of i.castSucc.castSucc, CodeSubgroups.bLift_of D.toCodeWords _⟩⟩
  have hh := (EllStage.commutes_conjugated_B G D hi x).map (ofEll G D hi)
  have hp : sim G D hi (simulatorInclusion D.toCodeWords x) = positive G D hi (D.code i) := by
    change sim G D hi (simulatorInclusion D.toCodeWords
      (CodeSubgroups.bValues D.toCodeWords i.castSucc.castSucc)) = _
    have hv : CodeSubgroups.bValues D.toCodeWords i.castSucc.castSucc =
        (simulatorL D.toCodeWords).evalWord (simulatorLWords.positive (D.code i)) := by
      fin_cases i <;> rfl
    rw [hv, sim_positive]
  change Commute (ell G D hi)
    (sim G D hi ((generators (simulatorK D.toCodeWords) 7)⁻¹ *
      simulatorInclusion D.toCodeWords x * generators (simulatorK D.toCodeWords) 7)) at hh
  simpa only [map_mul, map_inv, hp, k] using hh

theorem substitutions :
    ell G D hi = b G D hi * c G D hi * (b G D hi)⁻¹ ∧
    u G D hi 0 = b G D hi ^ 2 * c G D hi * (b G D hi ^ 2)⁻¹ ∧
    u G D hi 1 = (b G D hi)⁻¹ * c G D hi * b G D hi := by
  simpa only [show BCompression.embeddedGrid G (aGrid G D hi) (aGrid_injective G D hi) = embeddedGrid G D hi from rfl, b, embeddedGrid_ell, embeddedGrid_c, embeddedGrid_input]
    using BCompression.substitutions G (aGrid G D hi) (aGrid_injective G D hi)

theorem c_a : Commute (c G D hi) (a G D hi) := by
  have hh := (MonoidHom.commute_inl_inr (M := U G) (N := FreeGroup (Fin 2))
    (InputTriples.c G) (FreeGroup.of 0)).map (embeddedGrid G D hi)
  simpa only [MonoidHom.inl_apply, MonoidHom.inr_apply, embeddedGrid_c, embeddedGrid_a] using hh

theorem a_b : Commute (a G D hi) (b G D hi) := by
  simpa only [show BCompression.embeddedGrid G (aGrid G D hi) (aGrid_injective G D hi) = embeddedGrid G D hi from rfl, b, embeddedGrid_a] using
    (BCompression.commutes_columns G (aGrid G D hi) (aGrid_injective G D hi) (FreeGroup.of 0)).symm

theorem b_x : Commute (b G D hi) ((k G D hi)⁻¹ * f G D hi * k G D hi) := by
  simpa only [show BCompression.embeddedGrid G (aGrid G D hi) (aGrid_injective G D hi) = embeddedGrid G D hi from rfl, b, embeddedGrid_x] using
    BCompression.commutes_columns G (aGrid G D hi) (aGrid_injective G D hi) (FreeGroup.of 1)

theorem d_h_square : Commute (d G D hi) (h G D hi ^ 2) := by
  have hp := (HStage.commutes_d_square G D hi).map (ofH G D hi)
  simpa [d, h, sim, HStage.ofL, SimulatorRelations.d, simulatorInclusion,
    generators] using hp

end
end UniversalGroup.Embedding.PositiveHost.BaseModel
