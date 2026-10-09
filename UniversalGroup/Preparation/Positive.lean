module

public import UniversalGroup.Coding.Data
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Positive presentations from a torsion generator and a stable letter

If a two-generator presentation has generators x,t with x⁴ = 1, change to
 a = t and b = t⁻¹x. The relation (ab)⁴ = 1 permits every inverse to be
replaced by a positive word. A character x ↦ 0, t ↦ 1 then proves that both
new generators have infinite order.
-/

namespace UniversalGroup.PreparationPositive

noncomputable section

/-- The additional positive relation (ab)⁴. -/
def fourthPower : PositiveWord := [0,1,0,1,0,1,0,1]

/-- Positive spellings of x, x⁻¹, t, t⁻¹ under x = ab and t = a. -/
def letter : Fin 2 × Bool → PositiveWord
  | (i, true) => if i = 0 then [0,1] else [0]
  | (i, false) => if i = 0 then [0,1,0,1,0,1] else [1,0,1,0,1,0,1]

def encode (w : Word 2) : PositiveWord := w.flatMap letter

def value {H : Type*} [Group H] (a b : H) (w : PositiveWord) : H :=
  Word.eval ![a,b] (signedPositive w)

@[simp] theorem value_append {H : Type*} [Group H] (a b : H) (u v : PositiveWord) :
    value a b (u ++ v) = value a b u * value a b v := by
  simp [value, signedPositive]

@[simp] theorem value_fourthPower {H : Type*} [Group H] (a b : H) :
    value a b fourthPower = (a*b)^4 := by
  simp [value, fourthPower, signedPositive, Word.eval, FreeGroup.lift_mk, pow_succ, mul_assoc]

private theorem value_letter {H : Type*} [Group H] (a b : H) (hp : (a*b)^4=1)
    (j : Fin 2 × Bool) : value a b (letter j) =
      Word.eval ![a*b,a] [j] := by
  have hc : (a*b)^3 = (a*b)⁻¹ := eq_inv_of_mul_eq_one_left (by
    simpa only [pow_succ] using hp)
  rcases j with ⟨i,sgn⟩
  fin_cases i <;> cases sgn
  · simpa [value, letter, signedPositive, Word.eval, FreeGroup.lift_mk, pow_succ, mul_assoc] using hc
  · simp [value, letter, signedPositive, Word.eval, FreeGroup.lift_mk]
  · have h : b*(a*b)^3 = a⁻¹ := by rw [hc]; group
    simpa [value, letter, signedPositive, Word.eval, FreeGroup.lift_mk, pow_succ, mul_assoc] using h
  · simp [value, letter, signedPositive, Word.eval, FreeGroup.lift_mk]

/-- Evaluation of a converted word agrees with the original signed word. -/
theorem value_encode {H : Type*} [Group H] (a b : H) (hp : (a*b)^4=1) (w : Word 2) :
    value a b (encode w) = Word.eval ![a*b,a] w := by
  induction w with
  | nil => simp [value, encode, signedPositive, Word.eval]
  | cons j w ih =>
    change value a b (letter j ++ encode w) = _
    rw [value_append, value_letter a b hp, ih]
    change Word.eval ![a*b,a] [j] * Word.eval ![a*b,a] w = Word.eval ![a*b,a] ([j]++w)
    rw [Word.eval_append]

variable (P : FP 2 m)

def relators : Fin (m+1) → PositiveWord :=
  Fin.lastCases fourthPower (fun i => encode (P.relator i))

def presentation : FP 2 (m+1) := positivePresentation (relators P)

@[simp] theorem relator_last : (presentation P).relator (Fin.last m) = signedPositive fourthPower := by
  simp [presentation, positivePresentation, relators]

@[simp] theorem relator_cast (i : Fin m) :
    (presentation P).relator i.castSucc = signedPositive (encode (P.relator i)) := by
  simp [presentation, positivePresentation, relators]

abbrev a := generators (presentation P) 0
abbrev b := generators (presentation P) 1

private theorem value_generators (w : PositiveWord) :
    value (a P) (b P) w = (presentation P).evalWord (signedPositive w) := by
  unfold value FP.evalWord
  congr 1
  funext i
  fin_cases i <;> rfl

theorem product_fourthPower : (a P*b P)^4=1 := by
  have h := (presentation P).relator_eq_one (Fin.last m)
  rw [relator_last, ← value_generators] at h
  simpa only [value_fourthPower] using h

def ofOld : P.Group →* (presentation P).Group :=
  P.homOfRelators ![a P*b P,a P] (by
    intro i
    rw [← value_encode (a P) (b P) (product_fourthPower P)]
    rw [value_generators]
    simpa only [relator_cast] using (presentation P).relator_eq_one i.castSucc)

variable (hx : (generators P 0)^4=1)
include hx

omit hx in
private theorem pair_generators : ![generators P 0, generators P 1] =
    (fun i => (PresentedGroup.of i : P.Group)) := by
  funext i
  fin_cases i <;> rfl

def toOld : (presentation P).Group →* P.Group :=
  (presentation P).homOfRelators ![generators P 1, (generators P 1)⁻¹ * generators P 0] (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [relator_last]
      change value (generators P 1) ((generators P 1)⁻¹ * generators P 0) fourthPower = 1
      rw [value_fourthPower, mul_inv_cancel_left]
      exact hx
    · rw [relator_cast]
      change value (generators P 1) ((generators P 1)⁻¹ * generators P 0) (encode (P.relator j)) = 1
      rw [value_encode _ _ (by simpa only [mul_inv_cancel_left] using hx)]
      simpa only [mul_inv_cancel_left, pair_generators, FP.evalWord] using P.relator_eq_one j)

@[simp] theorem toOld_a : toOld P hx (a P) = generators P 1 := by
  simp [toOld, a, generators]
@[simp] theorem toOld_b : toOld P hx (b P) = (generators P 1)⁻¹ * generators P 0 := by
  simp [toOld, b, generators]

theorem toOld_comp_ofOld : (toOld P hx).comp (ofOld P) = MonoidHom.id P.Group := by
  apply PresentedGroup.ext
  intro i
  change toOld P hx (ofOld P (generators P i)) = generators P i
  fin_cases i <;> simp [ofOld, toOld, generators, a, b]

/-- The original presentation embeds in the positive presentation. -/
theorem ofOld_injective : Function.Injective (ofOld P) := by
  intro x y hxy
  have h := congrArg (toOld P hx) hxy
  simpa only [← MonoidHom.comp_apply, toOld_comp_ofOld, MonoidHom.id_apply] using h

variable (chi : P.Group →* Multiplicative ℤ)
  (hchi_x : chi (generators P 0) = 1)
  (hchi_t : chi (generators P 1) = Multiplicative.ofAdd 1)

/-- The inherited character has values +1 and -1 on the positive generators. -/
def degree : (presentation P).Group →* Multiplicative ℤ := chi.comp (toOld P hx)

include hchi_t in
@[simp] theorem degree_a : degree P hx chi (a P) = Multiplicative.ofAdd 1 := by
  simp only [degree, MonoidHom.comp_apply, toOld_a, hchi_t]
include hchi_x hchi_t in
@[simp] theorem degree_b : degree P hx chi (b P) = Multiplicative.ofAdd (-1) := by
  simp only [degree, MonoidHom.comp_apply, toOld_b, map_mul, map_inv, hchi_x, hchi_t, mul_one]
  rfl

include hchi_x hchi_t in
/-- Both displayed generators of the positive presentation have infinite order. -/
theorem infiniteOrder (i : Fin 2) (z : ℤ)
    (h : (generators (presentation P) i)^z=1) : z=0 := by
  have hh := congrArg (degree P hx chi) h
  rw [map_zpow, map_one] at hh
  fin_cases i
  · change (degree P hx chi (a P))^z=1 at hh
    rw [degree_a P hx chi hchi_t] at hh
    simpa using congrArg Multiplicative.toAdd hh
  · change (degree P hx chi (b P))^z=1 at hh
    rw [degree_b P hx chi hchi_x hchi_t] at hh
    simpa using congrArg Multiplicative.toAdd hh

def prepared : PreparedInput where
  relatorCount := m+1
  relators := relators P
  infiniteOrder := infiniteOrder P hx chi hchi_x hchi_t

end
end UniversalGroup.PreparationPositive
