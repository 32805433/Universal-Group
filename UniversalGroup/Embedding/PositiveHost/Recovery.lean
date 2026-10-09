module

public import UniversalGroup.Simulator.Data
public import UniversalGroup.Embedding.Presentations

@[expose] public section

/-! Recover the simulator and grid relations from the nineteen displayed rows. -/

namespace UniversalGroup.Embedding.PositiveHost.BaseRecovery

attribute [local irreducible] positiveBasePresentation
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

variable (D : CodeWords)

abbrev Host := (positiveBasePresentation D).Group

def c : Host D := generators (positiveBasePresentation D) 0
def d : Host D := generators (positiveBasePresentation D) 1
def f : Host D := generators (positiveBasePresentation D) 2
def k : Host D := generators (positiveBasePresentation D) 3
def a : Host D := generators (positiveBasePresentation D) 4
def b : Host D := generators (positiveBasePresentation D) 5
def x : Host D := (k D)⁻¹ * f D * k D
def x1 : Host D := (a D)⁻¹ * x D * a D
def h : Host D := (a D ^ 2)⁻¹ * x D * a D ^ 2
def s1 : Host D := f D * x1 D * (f D)⁻¹
def s2 : Host D := f D * (h D)⁻¹ * (x1 D)⁻¹ * h D * (f D)⁻¹
def e : Host D := f D * (h D)⁻¹ * d D * h D * (f D)⁻¹
def t : Host D := f D * (h D)⁻¹ * f D * h D
def ell : Host D := b D * c D * (b D)⁻¹
def u : Fin 2 → Host D := ![b D ^ 2 * c D * (b D ^ 2)⁻¹, (b D)⁻¹ * c D * b D]
def E0 : Host D := (f D)⁻¹ * e D * f D
def x2 : Host D := (f D)⁻¹ * s2 D * f D
def positive (w : PositiveWord) : Host D := (w.map ![s1 D, s2 D]).prod
def T : Host D := positive D D.P * t D * (f D)⁻¹ * (positive D D.P)⁻¹ * f D

@[simp] theorem eval_positive (w : PositiveWord) :
    (positiveBasePresentation D).evalWord (baseWords.positive w) = positive D w := by
  simp only [FP.evalWord, BaseWords.positive, Word.eval_substitutePositive]
  unfold positive
  congr 2
  funext i
  fin_cases i <;>
    simp [BaseWords.s1, BaseWords.s2, BaseWords.h, BaseWords.x1, BaseWords.x,
      baseWords, s1, s2, h, x1, x, a, k, f, generators, mul_assoc]

@[simp] theorem eval_u (i : Fin 2) :
    (positiveBasePresentation D).evalWord (baseWords.u i) = u D i := by
  fin_cases i <;> simp [FP.evalWord, BaseWords.u, baseWords, u, b, c, generators, mul_assoc]

private theorem commutator_iff (v : Fin n → Host D) (w z : Word n) :
    Word.eval v (Word.commutator w z) = 1 ↔ Commute (Word.eval v w) (Word.eval v z) := by
  rw [Word.eval_commutator, mul_assoc, mul_assoc, inv_mul_eq_one,
    eq_inv_mul_iff_mul_eq, commute_iff_eq]
  exact eq_comm

private theorem displayed_equation (i : Fin 19) (lhs rhs : Word 6)
    (hi : (positiveBasePresentation D).relator i = Word.relation lhs rhs) :
    (positiveBasePresentation D).evalWord lhs = (positiveBasePresentation D).evalWord rhs := by
  apply (Word.eval_relation_eq_one_iff _ _ _).mp
  rw [← hi]
  exact (positiveBasePresentation D).relator_eq_one i

private theorem displayed_commutation (i : Fin 19) (lhs rhs : Word 6)
    (hi : (positiveBasePresentation D).relator i = Word.commutator lhs rhs) :
    Commute ((positiveBasePresentation D).evalWord lhs) ((positiveBasePresentation D).evalWord rhs) := by
  apply (commutator_iff D _ _ _).mp
  rw [← hi]
  exact (positiveBasePresentation D).relator_eq_one i

theorem basic_commutations :
    Commute (c D) (f D) ∧ Commute (d D) (f D) ∧
    Commute (c D) (k D) ∧ Commute (d D) (k D) ∧
    Commute (c D) (a D) ∧ Commute (a D) (b D) ∧ Commute (b D) (x D) := by
  have hh := And.intro (displayed_commutation D 12 _ _ (by unfold positiveBasePresentation; rfl))
      (And.intro (displayed_commutation D 13 _ _ (by unfold positiveBasePresentation; rfl))
      (And.intro (displayed_commutation D 14 _ _ (by unfold positiveBasePresentation; rfl))
      (And.intro (displayed_commutation D 15 _ _ (by unfold positiveBasePresentation; rfl))
      (And.intro (displayed_commutation D 16 _ _ (by unfold positiveBasePresentation; rfl))
      (And.intro (displayed_commutation D 17 _ _ (by unfold positiveBasePresentation; rfl))
        (displayed_commutation D 18 _ _ (by unfold positiveBasePresentation; rfl)))))))
  simpa [FP.evalWord, baseWords, generators, c, d, f, k, a, b, x, BaseWords.x, mul_assoc] using hh

theorem exponent_s1 : d D ^ 4 * s1 D = s1 D * d D ∧
    e D * s1 D = s1 D * e D ^ 4 := by
  have hd := displayed_equation D 0 _ _ (by unfold positiveBasePresentation; rfl)
  have he := displayed_equation D 1 _ _ (by unfold positiveBasePresentation; rfl)
  constructor
  · simpa [FP.evalWord, BaseWords.s1, BaseWords.x1, BaseWords.x, baseWords,
      generators, d, s1, x1, x, f, k, a, mul_assoc] using hd
  · simpa [FP.evalWord, BaseWords.s1, positiveE, BaseWords.h, BaseWords.x1,
      BaseWords.x, baseWords, generators, d, e, s1, h, x1, x, f, k, a, mul_assoc] using he

theorem symmetry : (h D)⁻¹ * E0 D * h D = d D := by
  have hh := displayed_commutation D 10 _ _ (by unfold positiveBasePresentation; rfl)
  have hd : Commute (d D) (h D ^ 2) := by
    simpa [FP.evalWord, BaseWords.h, BaseWords.x, baseWords,
      generators, d, h, k, f, a, x, mul_assoc] using hh
  simpa [E0, e, pow_two, mul_assoc] using hd.symm.inv_mul_cancel

theorem c_x : Commute (c D) (x D) := by
  obtain ⟨hcf, _, hck, _⟩ := basic_commutations D
  exact (hck.inv_right.mul_right hcf).mul_right hck

theorem grid (z : Host D) (ha : Commute z (a D)) (hx : Commute z (x D)) :
    Commute z (x1 D) ∧ Commute z (h D) ∧ Commute z (x2 D) := by
  have hh : Commute z (h D) :=
    ((ha.pow_right 2).inv_right.mul_right hx).mul_right (ha.pow_right 2)
  have h1 : Commute z (x1 D) := (ha.inv_right.mul_right hx).mul_right ha
  refine ⟨h1, hh, ?_⟩
  simpa [x2, s2, mul_assoc] using
    (hh.inv_right.mul_right h1.inv_right).mul_right hh

theorem c_simulator : Commute (c D) (s1 D) ∧ Commute (c D) (s2 D) ∧
    Commute (c D) (t D) := by
  obtain ⟨hcf, _, _, _, hca, _⟩ := basic_commutations D
  obtain ⟨h1, hh, _⟩ := grid D (c D) hca (c_x D)
  exact ⟨(hcf.mul_right h1).mul_right hcf.inv_right,
    (((hcf.mul_right hh.inv_right).mul_right h1.inv_right).mul_right hh).mul_right hcf.inv_right,
    ((hcf.mul_right hh.inv_right).mul_right hcf).mul_right hh⟩

theorem exponent_s2 : d D ^ 4 * s2 D = s2 D * d D ∧
    e D * s2 D = s2 D * e D ^ 4 := by
  obtain ⟨hd, he⟩ := exponent_s1 D
  have hdf := (basic_commutations D).2.1
  let C := MulAut.conj ((f D)⁻¹)
  have Cd : C (d D) = d D := by simpa [C] using hdf.symm.inv_mul_cancel
  have Cs : C (s1 D) = x1 D := by simp [C, s1, mul_assoc]
  have Ce : C (e D) = E0 D := by simp [C, E0]
  have hd' := congrArg C hd
  have he' := congrArg C he
  simp only [map_mul, map_pow, Cd, Cs, Ce] at hd' he'
  let J := MulAut.conj ((h D)⁻¹)
  have Jd : J (d D) = E0 D := by simp [J, E0, e, mul_assoc]
  have JE : J (E0 D) = d D := by simpa [J] using symmetry D
  have Jx : J (x1 D) = (x2 D)⁻¹ := by simp [J, x2, s2, mul_assoc]
  have hx := congrArg J hd'
  have hy := congrArg J he'
  simp only [map_mul, map_pow, Jd, JE, Jx] at hx hy
  have hd2 : d D ^ 4 * x2 D = x2 D * d D := by
    calc
      d D ^ 4 * x2 D = x2 D * (d D * (x2 D)⁻¹) * x2 D := by rw [hy]; group
      _ = x2 D * d D := by group
  have he2 : E0 D * x2 D = x2 D * E0 D ^ 4 := by
    have hh := congrArg (fun z => x2 D * z * x2 D) hx
    simpa [mul_assoc] using hh.symm
  have C2 : C (s2 D) = x2 D := by simp [C, x2]
  constructor
  · apply C.injective
    simpa only [map_mul, map_pow, Cd, C2] using hd2
  · apply C.injective
    simpa only [map_mul, map_pow, Ce, C2] using he2

theorem t_e : e D * t D = t D * (f D)⁻¹ * e D * f D := by
  have hdf := (basic_commutations D).2.1
  simpa [e, t, mul_assoc] using
    congrArg (fun z => f D * (h D)⁻¹ * z * h D) hdf.eq

theorem rewriting (i : Fin 3) :
    (d D ^ (i.val + 1))⁻¹ * c D * d D ^ (i.val + 1) * positive D (D.E i) =
      positive D (D.F i) * e D ^ (i.val + 1) * c D * (e D ^ (i.val + 1))⁻¹ := by
  have hh := displayed_equation D ⟨i.val + 2, by omega⟩ _ _
    (show (positiveBasePresentation D).relator ⟨i.val + 2, by omega⟩ =
      positiveRewritingRelator D baseWords i by fin_cases i <;> unfold positiveBasePresentation <;> rfl)
  simp only [FP.evalWord, Word.eval_product, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Word.eval_pow, Word.eval_inverse] at hh
  have hp (w : PositiveWord) :
      Word.eval (fun i => PresentedGroup.of i) (baseWords.positive w) = positive D w :=
    eval_positive D w
  simp only [hp] at hh
  simpa [positiveE, BaseWords.h, BaseWords.x, baseWords, e, h, x,
    c, d, k, f, a, generators, mul_assoc] using hh

def simulatorValues : Fin 7 → Host D := ![c D, d D, e D, s1 D, s2 D, f D, t D]

theorem sim_positive (w : PositiveWord) :
    Word.eval (simulatorValues D) (simulatorLWords.positive w) = positive D w := by
  simp only [SimulatorWords.positive, Word.eval_substitutePositive]
  unfold positive
  congr 2
  funext i
  fin_cases i <;> simp [simulatorLWords, simulatorValues]

theorem simulator_relators (i : Fin 13) :
    Word.eval (simulatorValues D) ((simulatorL D).relator i) = 1 := by
  have hp := sim_positive D
  obtain ⟨hd1, he1⟩ := exponent_s1 D
  obtain ⟨hd2, he2⟩ := exponent_s2 D
  obtain ⟨hc1, hc2, hct⟩ := c_simulator D
  obtain ⟨hcf, hdf, _⟩ := basic_commutations D
  have ht := t_e D
  have hr := rewriting D
  fin_cases i
  all_goals simp only [simulatorL, simulatorLRelators, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals simp only [Word.eval_relation_eq_one_iff, commutator_iff]
  all_goals try simp only [Word.eval_product, Word.eval_pow, Word.eval_inverse, hp,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  all_goals simp [simulatorLWords, simulatorValues, hd1, hd2, he1, he2,
    hc1, hc2, hct, hcf, hdf, ht, mul_assoc]
  · simpa [mul_assoc] using hr 0
  · simpa [mul_assoc] using hr 1
  · simpa [mul_assoc] using hr 2

def simulatorMap : (simulatorL D).Group →* Host D :=
  (simulatorL D).homOfRelators (simulatorValues D) (simulator_relators D)

@[simp] theorem simulatorMap_eval (w : Word 7) :
    simulatorMap D ((simulatorL D).evalWord w) = Word.eval (simulatorValues D) w :=
  FP.homOfRelators_evalWord _ _ _ _

private theorem eval_product (ws : List (Word 6)) :
    (positiveBasePresentation D).evalWord (Word.product ws) =
      (ws.map (positiveBasePresentation D).evalWord).prod := Word.eval_product _ _

private theorem eval_inverse (w : Word 6) :
    (positiveBasePresentation D).evalWord (Word.inverse w) =
      ((positiveBasePresentation D).evalWord w)⁻¹ := Word.eval_inverse _ _

private theorem eval_pow (w : Word 6) (n : ℕ) :
    (positiveBasePresentation D).evalWord (Word.pow w n) =
      ((positiveBasePresentation D).evalWord w)^n := Word.eval_pow _ _ _

@[simp] theorem eval_c : (positiveBasePresentation D).evalWord baseWords.c = c D := by
  simp [baseWords, c, generators]

@[simp] theorem eval_f : (positiveBasePresentation D).evalWord baseWords.f = f D := by
  simp [baseWords, f, generators]

@[simp] theorem eval_k : (positiveBasePresentation D).evalWord baseWords.k = k D := by
  simp [baseWords, k, generators]

@[simp] theorem eval_a : (positiveBasePresentation D).evalWord baseWords.a = a D := by
  simp [baseWords, a, generators]

@[simp] theorem eval_b : (positiveBasePresentation D).evalWord baseWords.b = b D := by
  simp [baseWords, b, generators]

@[simp] theorem eval_x : (positiveBasePresentation D).evalWord baseWords.x = x D := by
  simp [BaseWords.x, eval_product, eval_inverse, x, mul_assoc]

@[simp] theorem eval_h : (positiveBasePresentation D).evalWord baseWords.h = h D := by
  simp [BaseWords.h, eval_product, eval_inverse, eval_pow, h, mul_assoc]

@[simp] theorem eval_t : (positiveBasePresentation D).evalWord baseWords.t = t D := by
  simp [BaseWords.t, eval_product, eval_inverse, t, mul_assoc]

@[simp] theorem eval_ell : (positiveBasePresentation D).evalWord baseWords.ell = ell D := by
  simp [BaseWords.ell, eval_product, eval_inverse, ell, mul_assoc]

@[simp] theorem eval_T : (positiveBasePresentation D).evalWord (baseWords.T D) = T D := by
  simp only [BaseWords.T, eval_product, eval_inverse, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, eval_positive, eval_t, eval_f]
  simp only [T, mul_assoc]

theorem k_T : Commute (k D) (T D) := by
  have hh := displayed_commutation D 5 _ _ (by unfold positiveBasePresentation; rfl)
  simpa only [eval_T, eval_k] using hh.symm

theorem column_three : positive D D.P * t D = (a D ^ 3)⁻¹ * x D * a D ^ 3 := by
  have hh := displayed_equation D 11 _ _ (by unfold positiveBasePresentation; rfl)
  simpa only [eval_product, eval_inverse, eval_pow, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, eval_positive, eval_t, eval_a, eval_x, mul_assoc] using hh

theorem attachment (i : Fin 2) :
    positive D (D.code i) * ell D =
      ell D * positive D (D.code i) * f D * u D i * (f D)⁻¹ := by
  have hh := displayed_equation D ⟨i.val + 6, by omega⟩ _ _
    (show (positiveBasePresentation D).relator ⟨i.val + 6, by omega⟩ =
      inputRelator D baseWords i by fin_cases i <;> unfold positiveBasePresentation <;> rfl)
  simpa only [eval_product, eval_inverse, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, eval_positive, eval_ell, eval_f, eval_u, mul_assoc] using hh

theorem ell_code (i : Fin 2) :
    Commute (ell D) ((k D)⁻¹ * positive D (D.code i) * k D) := by
  have hh := displayed_commutation D ⟨i.val + 8, by omega⟩ _ _
    (show (positiveBasePresentation D).relator ⟨i.val + 8, by omega⟩ =
      inputCommutator D baseWords i by fin_cases i <;> unfold positiveBasePresentation <;> rfl)
  simpa only [eval_product, eval_inverse, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, eval_positive, eval_ell, eval_k, mul_assoc] using hh

theorem grid_three (z : Host D) (ha : Commute z (a D)) (hx : Commute z (x D)) :
    Commute z (positive D D.P * t D) := by
  rw [column_three]
  exact ((ha.pow_right 3).inv_right.mul_right hx).mul_right (ha.pow_right 3)

theorem ell_grid : Commute (ell D) (x D) ∧ Commute (ell D) (x1 D) ∧
    Commute (ell D) (x2 D) ∧ Commute (ell D) (positive D D.P * t D) := by
  obtain ⟨_, _, _, _, hca, hab, hbx⟩ := basic_commutations D
  have hl_a : Commute (ell D) (a D) :=
    ((hab.mul_right hca.symm).mul_right hab.inv_right).symm
  have hl_x : Commute (ell D) (x D) :=
    ((hbx.symm.mul_right (c_x D).symm).mul_right hbx.symm.inv_right).symm
  have hh := grid D (ell D) hl_a hl_x
  exact ⟨hl_x, hh.1, hh.2.2, grid_three D _ hl_a hl_x⟩

theorem u_grid (i : Fin 2) : Commute (u D i) (x1 D) ∧ Commute (u D i) (x2 D) := by
  obtain ⟨_, _, _, _, hca, hab, hbx⟩ := basic_commutations D
  have hua : Commute (u D i) (a D) := by
    fin_cases i
    · exact (((hab.pow_right 2).mul_right hca.symm).mul_right (hab.pow_right 2).inv_right).symm
    · exact ((hab.inv_right.mul_right hca.symm).mul_right hab).symm
  have hux : Commute (u D i) (x D) := by
    fin_cases i
    · exact (((hbx.symm.pow_right 2).mul_right (c_x D).symm).mul_right
        (hbx.symm.pow_right 2).inv_right).symm
    · exact ((hbx.symm.inv_right.mul_right (c_x D).symm).mul_right hbx.symm).symm
  have hh := grid D (u D i) hua hux
  exact ⟨hh.1, hh.2.2⟩

end UniversalGroup.Embedding.PositiveHost.BaseRecovery
