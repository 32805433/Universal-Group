module

public import UniversalGroup.Simulator.Data
public import UniversalGroup.Simulator.Core.SupportedRules
public import Mathlib.Algebra.Group.Commute.Basic

@[expose] public section

/-! The displayed simulator relations in element form. -/

namespace UniversalGroup.SimulatorRelations

variable (D : CodeWords)

abbrev Presented := (simulatorL D).Group

def c : Presented D := generators (simulatorL D) 0
def d : Presented D := generators (simulatorL D) 1
def e : Presented D := generators (simulatorL D) 2
def s : Fin 2 → Presented D := ![generators (simulatorL D) 3, generators (simulatorL D) 4]
def f : Presented D := generators (simulatorL D) 5
def t : Presented D := generators (simulatorL D) 6
def q : Presented D := t D * (f D)⁻¹
def positive (w : PositiveWord) : Presented D := evalPositive (s D 0) (s D 1) w

@[simp] theorem eval_positive (w : PositiveWord) :
    (simulatorL D).evalWord (simulatorLWords.positive w) = positive D w := by
  simp [FP.evalWord, SimulatorWords.positive, simulatorLWords, positive,
    evalPositive, s, generators]

private theorem equation (i : Fin 13) (a b : Word 7)
    (hi : (simulatorL D).relator i = Word.relation a b) :
    (simulatorL D).evalWord a = (simulatorL D).evalWord b := by
  apply (Word.eval_relation_eq_one_iff _ _ _).mp
  rw [← hi]
  exact (simulatorL D).relator_eq_one i

private theorem commutation (i : Fin 13) (a b : Word 7)
    (hi : (simulatorL D).relator i = Word.commutator a b) :
    Commute ((simulatorL D).evalWord a) ((simulatorL D).evalWord b) := by
  have h := (simulatorL D).relator_eq_one i
  rw [hi, FP.evalWord, Word.eval_commutator] at h
  rw [mul_assoc, mul_assoc, inv_mul_eq_one, eq_inv_mul_iff_mul_eq] at h
  exact h.symm

theorem d_power (i : Fin 2) : d D ^ 4 * s D i = s D i * d D := by
  have h := equation D ⟨i.val, by omega⟩ _ _
    (show (simulatorL D).relator ⟨i.val, by omega⟩ =
      Word.relation
        (Word.product [Word.pow simulatorLWords.d 4, simulatorLWords.s i])
        (Word.product [simulatorLWords.s i, simulatorLWords.d]) by fin_cases i <;> rfl)
  fin_cases i <;>
    simpa [FP.evalWord, simulatorLWords, d, s, generators, mul_assoc] using h

theorem e_power (i : Fin 2) : e D * s D i = s D i * e D ^ 4 := by
  have h := equation D ⟨i.val + 2, by omega⟩ _ _
    (show (simulatorL D).relator ⟨i.val + 2, by omega⟩ =
      Word.relation
        (Word.product [simulatorLWords.e, simulatorLWords.s i])
        (Word.product [simulatorLWords.s i, Word.pow simulatorLWords.e 4]) by fin_cases i <;> rfl)
  fin_cases i <;>
    simpa [FP.evalWord, simulatorLWords, e, s, generators, mul_assoc] using h

theorem c_s (i : Fin 2) : Commute (c D) (s D i) := by
  have h := commutation D ⟨i.val + 4, by omega⟩ _ _
    (show (simulatorL D).relator ⟨i.val + 4, by omega⟩ =
      Word.commutator simulatorLWords.c (simulatorLWords.s i) by fin_cases i <;> rfl)
  fin_cases i <;>
    simpa [FP.evalWord, simulatorLWords, c, s, generators] using h

theorem rewriting (i : Fin 3) :
    (d D ^ (i.val + 1))⁻¹ * c D * d D ^ (i.val + 1) * positive D (D.E i) =
      positive D (D.F i) * e D ^ (i.val + 1) * c D * (e D ^ (i.val + 1))⁻¹ := by
  have h := equation D ⟨i.val + 6, by omega⟩ _ _
    (show (simulatorL D).relator ⟨i.val + 6, by omega⟩ = Word.relation
      (Word.product [Word.inverse (Word.pow simulatorLWords.d (i.val + 1)),
        simulatorLWords.c, Word.pow simulatorLWords.d (i.val + 1),
        simulatorLWords.positive (D.E i)])
      (Word.product [simulatorLWords.positive (D.F i),
        Word.pow simulatorLWords.e (i.val + 1), simulatorLWords.c,
        Word.inverse (Word.pow simulatorLWords.e (i.val + 1))]) by fin_cases i <;> rfl)
  simpa [FP.evalWord, SimulatorWords.positive, simulatorLWords, positive,
    evalPositive, d, e, c, s, generators, mul_assoc] using h

theorem rewriting_normalized (i : Fin 3) :
    (c D)⁻¹ * (d D ^ (i.val + 1) * positive D (D.F i) * e D ^ (i.val + 1)) * c D =
      d D ^ (i.val + 1) * positive D (D.E i) * e D ^ (i.val + 1) := by
  have h := congrArg
    (fun z => (c D)⁻¹ * d D ^ (i.val + 1) * z * e D ^ (i.val + 1)) (rewriting D i)
  simpa [mul_assoc] using h.symm

theorem c_f : Commute (c D) (f D) := by
  have h := commutation D 9 _ _ rfl
  simpa [FP.evalWord, simulatorLWords, c, f, generators] using h

theorem d_f : Commute (d D) (f D) := by
  have h := commutation D 10 _ _ rfl
  simpa [FP.evalWord, simulatorLWords, d, f, generators] using h

theorem c_t : Commute (c D) (t D) := by
  have h := commutation D 11 _ _ rfl
  simpa [FP.evalWord, simulatorLWords, c, t, generators] using h

theorem e_t : e D * t D = t D * (f D)⁻¹ * e D * f D := by
  have h := equation D 12 _ _ rfl
  simpa [FP.evalWord, simulatorLWords, e, t, f, generators, mul_assoc] using h

theorem c_q : Commute (c D) (q D) := (c_t D).mul_right (c_f D).inv_right

theorem e_q : Commute (e D) (q D) := by
  change e D * q D = q D * e D
  have h := congrArg (fun z => z * (f D)⁻¹) (e_t D)
  simpa [q, mul_assoc] using h

end UniversalGroup.SimulatorRelations
