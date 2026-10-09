module

public import UniversalGroup.Embedding.PositiveHost.Recovery
public import UniversalGroup.Host.PositiveEvaluation

@[expose] public section

/-!
# Removing the input relators

The argument uses the given simulator intersections, the recovered simulator
map, and the attaching relations. No injectivity theorem for the host is used.
-/

namespace UniversalGroup.Embedding.PositiveHost

/-- Values of the prepared input generators at the six-generator stage. -/
def baseInputValues (D : CodeWords) (i : Fin 2) : (positiveBasePresentation D).Group :=
  (positiveBasePresentation D).evalWord (baseWords.u i)

namespace InputRelators

attribute [local irreducible] positiveBasePresentation
set_option maxHeartbeats 1200000

open BaseRecovery UniversalGroup.PositiveEvaluation

variable (D : CodeWords)

theorem conjugate_positive (w : PositiveWord) :
    (f D)⁻¹ * positive D w * f D = value ![x1 D, x2 D] w := by
  change (f D)⁻¹ * value ![s1 D, s2 D] w * f D = _
  have hh := value_conj ((f D)⁻¹) ![s1 D, s2 D] w
  simp only [inv_inv] at hh
  rw [← hh]
  congr 1
  funext i
  fin_cases i <;> simp [s1, x2, mul_assoc]

theorem positive_code (w : PositiveWord) :
    positive D (w.flatMap D.code) = value (fun i => positive D (D.code i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa [positive, List.prod_append] using congrArg (positive D (D.code i) * ·) ih

theorem ell_T : Commute (ell D) (T D) := by
  obtain ⟨_, h1, h2, h3⟩ := ell_grid D
  have hh : Commute (ell D) (value ![x1 D, x2 D] D.P) := by
    apply value_commute
    intro i
    fin_cases i <;> assumption
  have ht : T D = (positive D D.P * t D) * (value ![x1 D, x2 D] D.P)⁻¹ := by
    rw [← conjugate_positive]
    simp [T, mul_assoc]
  rw [ht]
  exact h3.mul_right hh.inv_right

theorem simulator_T : simulatorMap D ((simulatorL D).evalWord (simulatorLWords.T D)) = T D := by
  rw [simulatorMap_eval]
  simp only [SimulatorWords.T, Word.eval_product, Word.eval_inverse, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hp := BaseRecovery.sim_positive D D.P
  rw [hp]
  simp [simulatorLWords, simulatorValues, T, mul_assoc]

theorem simulator_delta (w : PositiveWord) :
    simulatorMap D (simulatorDelta D w) =
      positive D (w.flatMap D.code) * T D * (f D)⁻¹ *
        (positive D (w.flatMap D.code))⁻¹ * f D := by
  unfold simulatorDelta
  rw [simulatorMap_eval]
  simp only [SimulatorWords.delta, Word.eval_product, Word.eval_inverse, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, SimulatorWords.bar,
    BaseRecovery.sim_positive]
  have ht := simulator_T D
  rw [simulatorMap_eval] at ht
  rw [ht]
  simp [simulatorLWords, simulatorValues, mul_assoc]

theorem recognized_commutes (G : PreparedInput) (datum : ValievDatum G)
    (hintersections : ValievIntersections G datum) (w : PositiveWord)
    (hw : PositiveEq G.monoidRules w []) :
    Commute (ell datum.toCodeWords)
      (simulatorMap datum.toCodeWords (simulatorDelta datum.toCodeWords w)) := by
  let D := datum.toCodeWords
  have hh := (simulatorDelta_mem_intersections G datum hintersections w hw).2
  change simulatorDelta D w ∈ simulatorD D ⊓ simulatorB D at hh
  have hk : Commute (k D) (simulatorMap D (simulatorDelta D w)) := by
    apply commute_closure _ _ _ ?_ hh.1
    rintro y ⟨i, rfl⟩
    fin_cases i
    · simpa [simulatorMap, simulatorLWords, simulatorValues, generators] using
        (basic_commutations D).2.2.1.symm
    · simpa [simulatorMap, simulatorLWords, simulatorValues, generators] using
        (basic_commutations D).2.2.2.1.symm
    · simpa only [Matrix.cons_val_zero', Matrix.cons_val_succ', simulator_T] using k_T D
  let φ := (MulAut.conj ((k D)⁻¹)).toMonoidHom.comp (simulatorMap D)
  have hl : Commute (ell D) (φ (simulatorDelta D w)) := by
    apply commute_closure _ _ _ ?_ hh.2
    rintro y ⟨i, rfl⟩
    fin_cases i
    · simpa [φ, D, simulatorMap_eval, BaseRecovery.sim_positive] using ell_code D 0
    · simpa [φ, D, simulatorMap_eval, BaseRecovery.sim_positive] using ell_code D 1
    · simpa [φ, simulatorMap, simulatorLWords, simulatorValues, generators, x] using (ell_grid D).1
    · change Commute (ell D) ((k D)⁻¹ *
        simulatorMap D ((simulatorL D).evalWord (simulatorLWords.T D)) * k D)
      rw [simulator_T, (k_T D).inv_mul_cancel]
      exact ell_T D
  simpa only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv, hk.inv_mul_cancel] using hl

theorem attach_word (w : PositiveWord) :
    (ell D)⁻¹ * positive D (w.flatMap D.code) * ell D =
      positive D (w.flatMap D.code) * f D * value (u D) w * (f D)⁻¹ := by
  let v : Fin 2 → Host D := fun i => positive D (D.code i)
  let v' : Fin 2 → Host D := fun i => f D * u D i * (f D)⁻¹
  have hc : ∀ i j, Commute (v' i) (v j) := by
    intro i j
    have hh := u_grid D i
    have hs : ∀ l : Fin 2, Commute (v' i) (![s1 D, s2 D] l) := by
      intro l
      fin_cases l
      · simpa [v', s1] using hh.1.conj (f D)
      · simpa [v', x2, mul_assoc] using hh.2.conj (f D)
    exact value_commute (v' i) _ hs (D.code j)
  have ha (i : Fin 2) : (ell D)⁻¹ * v i * ell D = v i * v' i := by
    have hi := attachment D i
    calc
      (ell D)⁻¹ * v i * ell D = (ell D)⁻¹ * (positive D (D.code i) * ell D) := by
        simp [v, mul_assoc]
      _ = v i * v' i := by rw [hi]; simp [v, v', mul_assoc]
  calc
    (ell D)⁻¹ * positive D (w.flatMap D.code) * ell D =
        value (fun i => (ell D)⁻¹ * v i * ell D) w := by
      rw [positive_code]
      simpa only [inv_inv] using (value_conj ((ell D)⁻¹) v w).symm
    _ = value (fun i => v i * v' i) w := by simp only [ha]
    _ = value v w * value v' w := value_mul v v' hc w
    _ = positive D (w.flatMap D.code) * f D * value (u D) w * (f D)⁻¹ := by
      change value v w * value (fun i => f D * u D i * (f D)⁻¹) w = _
      rw [value_conj, ← positive_code]
      group

theorem recognized_trivial (G : PreparedInput) (datum : ValievDatum G)
    (hintersections : ValievIntersections G datum) (w : PositiveWord)
    (hw : PositiveEq G.monoidRules w []) : value (u datum.toCodeWords) w = 1 := by
  let D := datum.toCodeWords
  let W := positive D (w.flatMap D.code)
  let Z := value ![x1 D, x2 D] (w.flatMap D.code ++ D.P)
  let X := positive D D.P * t D
  let δ := simulatorMap D (simulatorDelta D w)
  have hδ : δ = W * X * Z⁻¹ := by
    dsimp [δ, W, X, Z]
    rw [simulator_delta, ← conjugate_positive]
    simp [positive, List.prod_append, T, mul_assoc]
  obtain ⟨_, h1, h2, hX⟩ := ell_grid D
  have hZ : Commute (ell D) Z := by
    apply value_commute
    intro i
    fin_cases i <;> assumption
  have hcomm : Commute (ell D) δ := recognized_commutes G datum hintersections w hw
  have hW : Commute (ell D) W := by
    have heq : W = δ * Z * X⁻¹ := by rw [hδ]; group
    rw [heq]
    exact (hcomm.mul_right hZ).mul_right hX.inv_right
  have hatt := attach_word D w
  change (ell D)⁻¹ * W * ell D = W * f D * value (u D) w * (f D)⁻¹ at hatt
  rw [hW.inv_mul_cancel] at hatt
  have heq : f D * value (u D) w * (f D)⁻¹ = 1 := by
    apply mul_left_cancel (a := W)
    simpa only [mul_assoc, mul_one] using hatt.symm
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one, inv_mul_cancel]
    using congrArg (fun z => (f D)⁻¹ * z * f D) heq

end InputRelators

/-- The input relators follow from the host relations and the given simulator
intersection theorem; they are not additional defining relations of the host. -/
theorem base_input_relators (G : PreparedInput) (D : ValievDatum G)
    (hintersections : ValievIntersections G D) (i : Fin G.relatorCount) :
    Word.eval (baseInputValues D.toCodeWords) (G.presentation.relator i) = 1 := by
  have hh := InputRelators.recognized_trivial G D hintersections (G.relators i)
    (G.relator_monoidEq i)
  simpa [Word.eval, PreparedInput.presentation, positivePresentation, signedPositive,
    FreeGroup.lift_mk, List.map_map, Function.comp_def, baseInputValues,
    UniversalGroup.PositiveEvaluation.value] using hh

end UniversalGroup.Embedding.PositiveHost
