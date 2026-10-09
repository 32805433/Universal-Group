module

public import UniversalGroup.Embedding.Presentations
public import UniversalGroup.Simulator.Centralizer
public import UniversalGroup.Simulator.Relations
public import Mathlib.Algebra.Group.Commute.Hom

@[expose] public section

/-! Verification of the nineteen displayed relators in a group with the
named simulator, symmetry and compression equations. -/

namespace UniversalGroup.Embedding.PositiveHost.BaseModelLaws

variable (D : CodeWords) {H : Type*} [Group H]
variable (sim : (simulatorK D).Group →* H) (a b : H)

def values : Fin 6 → H := ![sim (generators (simulatorK D) 0),
  sim (generators (simulatorK D) 1), sim (generators (simulatorK D) 5),
  sim (generators (simulatorK D) 7), a, b]

def value (w : Word 6) : H := Word.eval (values D sim a b) w

structure Laws : Prop where
  s1 : value D sim a b baseWords.s1 = sim (generators (simulatorK D) 3)
  s2 : value D sim a b baseWords.s2 = sim (generators (simulatorK D) 4)
  e : value D sim a b (positiveE baseWords) = sim (generators (simulatorK D) 2)
  t : value D sim a b baseWords.t = sim (generators (simulatorK D) 6)
  attachment : ∀ i : Fin 2,
    value D sim a b (baseWords.positive (D.code i)) * value D sim a b baseWords.ell =
      value D sim a b baseWords.ell * value D sim a b (baseWords.positive (D.code i)) *
        sim (generators (simulatorK D) 5) * value D sim a b (baseWords.u i) *
          (sim (generators (simulatorK D) 5))⁻¹
  ell_code : ∀ i : Fin 2, Commute (value D sim a b baseWords.ell)
    ((sim (generators (simulatorK D) 7))⁻¹ *
      value D sim a b (baseWords.positive (D.code i)) * sim (generators (simulatorK D) 7))
  h_square : Commute (sim (generators (simulatorK D) 1))
    (value D sim a b baseWords.h ^ 2)
  column_three : value D sim a b (baseWords.positive D.P) * sim (generators (simulatorK D) 6) =
    (a ^ 3)⁻¹ * ((sim (generators (simulatorK D) 7))⁻¹ *
      sim (generators (simulatorK D) 5) * sim (generators (simulatorK D) 7)) * a ^ 3
  c_a : Commute (sim (generators (simulatorK D) 0)) a
  a_b : Commute a b
  b_x : Commute b ((sim (generators (simulatorK D) 7))⁻¹ *
    sim (generators (simulatorK D) 5) * sim (generators (simulatorK D) 7))

variable (laws : Laws D sim a b)

@[simp] theorem value_product (ws : List (Word 6)) :
    value D sim a b (Word.product ws) = (ws.map (value D sim a b)).prod :=
  Word.eval_product _ ws
@[simp] theorem value_inverse (w : Word 6) :
    value D sim a b (Word.inverse w) = (value D sim a b w)⁻¹ := Word.eval_inverse _ w
@[simp] theorem value_pow (w : Word 6) (n : ℕ) :
    value D sim a b (Word.pow w n) = value D sim a b w ^ n := Word.eval_pow _ w n
@[simp] theorem value_c : value D sim a b baseWords.c = sim (generators (simulatorK D) 0) := by
  simp [value, baseWords, values]
@[simp] theorem value_d : value D sim a b baseWords.d = sim (generators (simulatorK D) 1) := by
  simp [value, baseWords, values]
@[simp] theorem value_f : value D sim a b baseWords.f = sim (generators (simulatorK D) 5) := by
  simp [value, baseWords, values]
@[simp] theorem value_k : value D sim a b baseWords.k = sim (generators (simulatorK D) 7) := by
  simp [value, baseWords, values]
@[simp] theorem value_a : value D sim a b baseWords.a = a := by simp [value, baseWords, values]
@[simp] theorem value_b : value D sim a b baseWords.b = b := by simp [value, baseWords, values]
@[simp] theorem value_x : value D sim a b baseWords.x =
    (sim (generators (simulatorK D) 7))⁻¹ * sim (generators (simulatorK D) 5) *
      sim (generators (simulatorK D) 7) := by simp [BaseWords.x, mul_assoc]

/-- Recover the second simulator letter from the conjugation of the first column. -/
theorem eval_s2_of_conjugates (z : Fin 6 → H) (f h s1 s2 : H)
    (hf : Word.eval z baseWords.f = f)
    (hh : Word.eval z baseWords.h = h)
    (hx : Word.eval z baseWords.x1 = f⁻¹ * s1 * f)
    (hconj : h⁻¹ * (f⁻¹ * s1 * f) * h = (f⁻¹ * s2 * f)⁻¹) :
    Word.eval z baseWords.s2 = s2 := by
  have hinv := congrArg Inv.inv hconj
  have he : h⁻¹ * (f⁻¹ * s1 * f)⁻¹ * h = f⁻¹ * s2 * f := by
    simpa [mul_assoc] using hinv
  simp only [BaseWords.s2, Word.eval_product, Word.eval_inverse,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hf, hh, hx]
  simpa [mul_assoc] using congrArg (fun x => f * x * f⁻¹) he

/-- Recover the positive `e` word from its conjugation equation in any group. -/
theorem eval_e_of_conjugates (z : Fin 6 → H) (f h d e : H)
    (hf : Word.eval z baseWords.f = f)
    (hh : Word.eval z baseWords.h = h)
    (hd : Word.eval z baseWords.d = d)
    (hconj : h⁻¹ * d * h = f⁻¹ * e * f) :
    Word.eval z (positiveE baseWords) = e := by
  simp only [positiveE, Word.eval_product, Word.eval_inverse,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hf, hh, hd]
  simpa [mul_assoc] using congrArg (fun x => f * x * f⁻¹) hconj

/-- Recover the `t` word from the conjugation of `f` in any group. -/
theorem eval_t_of_conjugates (z : Fin 6 → H) (f h t : H)
    (hf : Word.eval z baseWords.f = f)
    (hh : Word.eval z baseWords.h = h)
    (hconj : h⁻¹ * f * h = f⁻¹ * t) :
    Word.eval z baseWords.t = t := by
  simp only [BaseWords.t, Word.eval_product, Word.eval_inverse,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hf, hh]
  simpa [mul_assoc] using congrArg (fun x => f * x) hconj

def oldValues : Fin 7 → H := fun i => sim (generators (simulatorK D) (Fin.castAdd 1 i))

theorem eval_old (w : Word 7) : Word.eval (oldValues D sim) w =
    sim (simulatorInclusion D ((simulatorL D).evalWord w)) := by
  rw [SimulatorCentralizer.inclusion_old_word, FP.evalWord, Word.map_eval,
    Word.eval_mapGenerators]
  rfl

theorem old_relator (i : Fin 13) : Word.eval (oldValues D sim) ((simulatorL D).relator i) = 1 := by
  rw [eval_old, FP.relator_eq_one, map_one, map_one]

include laws in
theorem value_positive (w : List (Fin 2)) :
    value D sim a b (baseWords.positive w) = Word.eval (oldValues D sim) (simulatorLWords.positive w) := by
  change Word.eval (values D sim a b) (baseWords.positive w) = _
  simp only [BaseWords.positive, Word.eval_substitutePositive]
  change (w.map (fun i => if i = 0 then value D sim a b baseWords.s1 else value D sim a b baseWords.s2)).prod = _
  rw [laws.s1, laws.s2]
  simp [SimulatorWords.positive, simulatorLWords, oldValues]

private theorem equation (w z : Word 6) (h : value D sim a b w = value D sim a b z) :
    value D sim a b (Word.relation w z) = 1 :=
  (Word.eval_relation_eq_one_iff _ _ _).mpr h

private theorem commutation (w z : Word 6) (h : Commute (value D sim a b w) (value D sim a b z)) :
    value D sim a b (Word.commutator w z) = 1 := by
  change Word.eval _ _ = 1
  rw [Word.eval_commutator]
  have hh := h.eq
  change (value D sim a b w)⁻¹ * (value D sim a b z)⁻¹ * value D sim a b w * value D sim a b z = 1
  rw [mul_assoc, mul_assoc, hh, ← mul_assoc (value D sim a b z)⁻¹,
    inv_mul_cancel, one_mul, inv_mul_cancel]

include laws in
theorem rewriting (i : Fin 3) : value D sim a b (positiveRewritingRelator D baseWords i) = 1 := by
  have h := old_relator D sim ⟨i.val + 6, by omega⟩
  have hh : (simulatorL D).relator ⟨i.val + 6, by omega⟩ =
      Word.relation
        (Word.product [Word.inverse (Word.pow simulatorLWords.d (i.val + 1)),
          simulatorLWords.c, Word.pow simulatorLWords.d (i.val + 1), simulatorLWords.positive (D.E i)])
        (Word.product [simulatorLWords.positive (D.F i), Word.pow simulatorLWords.e (i.val + 1),
          simulatorLWords.c, Word.inverse (Word.pow simulatorLWords.e (i.val + 1))]) := by
    fin_cases i <;> rfl
  rw [hh, Word.eval_relation_eq_one_iff] at h
  apply equation
  simpa [value_product, laws.e, value_positive D sim a b laws, simulatorLWords, oldValues,
    mul_assoc] using h

include laws in
theorem core_relator (i : Fin 12) : value D sim a b (positiveCoreRelators D baseWords i) = 1 := by
  fin_cases i
  · apply equation
    have h := (Word.eval_relation_eq_one_iff _ _ _).mp (old_relator D sim 0)
    simpa [laws.s1, simulatorLWords, oldValues, mul_assoc] using h
  · apply equation
    have h := (Word.eval_relation_eq_one_iff _ _ _).mp (old_relator D sim 2)
    simpa [laws.s1, laws.e, simulatorLWords, oldValues, mul_assoc] using h
  · exact rewriting D sim a b laws 0
  · exact rewriting D sim a b laws 1
  · exact rewriting D sim a b laws 2
  · apply commutation
    have h := (SimulatorCentralizer.inclusion_basis_commutes_k D 2).map sim
    have ht : value D sim a b (baseWords.T D) =
        sim (simulatorInclusion D ((simulatorL D).evalWord (simulatorLWords.T D))) := by
      rw [← eval_old]
      simp [BaseWords.T, SimulatorWords.T, value_positive D sim a b laws, laws.t,
        simulatorLWords, oldValues]
    simpa only [ht, value_k, Matrix.cons_val] using h
  · apply equation
    simpa [mul_assoc] using laws.attachment 0
  · apply equation
    simpa [mul_assoc] using laws.attachment 1
  · apply commutation
    simpa [mul_assoc] using laws.ell_code 0
  · apply commutation
    simpa [mul_assoc] using laws.ell_code 1
  · apply commutation
    simpa using laws.h_square
  · apply equation
    simpa [laws.t, mul_assoc] using laws.column_three

include laws in
theorem relators (i : Fin 19) : Word.eval (values D sim a b) ((positiveBasePresentation D).relator i) = 1 := by
  refine Fin.addCases (m := 12) (n := 7) (fun j => ?_) (fun j => ?_) i
  · simpa only [positiveBasePresentation, Fin.append_left, value] using core_relator D sim a b laws j
  · fin_cases j
    · apply commutation
      have h := (SimulatorRelations.c_f D).map ((sim).comp (simulatorInclusion D))
      simpa [SimulatorRelations.c, SimulatorRelations.f, simulatorInclusion, generators,
        value_c, value_f] using h
    · apply commutation
      have h := (SimulatorRelations.d_f D).map ((sim).comp (simulatorInclusion D))
      simpa [SimulatorRelations.d, SimulatorRelations.f, simulatorInclusion, generators,
        value_d, value_f] using h
    · apply commutation
      have h := (SimulatorCentralizer.inclusion_basis_commutes_k D 0).map sim
      simpa [FP.evalWord, simulatorLWords, simulatorInclusion, generators] using h
    · apply commutation
      have h := (SimulatorCentralizer.inclusion_basis_commutes_k D 1).map sim
      simpa [FP.evalWord, simulatorLWords, simulatorInclusion, generators] using h
    · apply commutation
      simpa using laws.c_a
    · apply commutation
      simpa using laws.a_b
    · apply commutation
      simpa using laws.b_x

def hom : (positiveBasePresentation D).Group →* H :=
  (positiveBasePresentation D).homOfRelators (values D sim a b) (relators D sim a b laws)

@[simp] theorem hom_generator (i : Fin 6) :
    hom D sim a b laws (generators (positiveBasePresentation D) i) = values D sim a b i :=
  FP.homOfRelators_of _ _ _ _

@[simp] theorem hom_evalWord (w : Word 6) :
    hom D sim a b laws ((positiveBasePresentation D).evalWord w) = value D sim a b w :=
  FP.homOfRelators_evalWord _ _ _ _

end UniversalGroup.Embedding.PositiveHost.BaseModelLaws
