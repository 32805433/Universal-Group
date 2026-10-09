module

public import UniversalGroup.Simulator.Data
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Evaluation of positive words

Positive-word evaluation preserves conjugation and splits products of
commuting letters. Commutation also extends to a generated subgroup.
-/

namespace UniversalGroup

namespace PositiveEvaluation

def value {H : Type*} [Group H] (v : Fin 2 → H) (w : PositiveWord) : H := (w.map v).prod

@[simp] theorem value_nil {H : Type*} [Group H] (v : Fin 2 → H) : value v [] = 1 := rfl
@[simp] theorem value_cons {H : Type*} [Group H] (v : Fin 2 → H) (i : Fin 2) (w) :
    value v (i :: w) = v i * value v w := rfl

theorem value_commute {H : Type*} [Group H] (z : H) (v : Fin 2 → H)
    (hv : ∀ i, Commute z (v i)) (w : PositiveWord) : Commute z (value v w) := by
  induction w with
  | nil => exact Commute.one_right z
  | cons i w ih => exact (hv i).mul_right ih

theorem value_conj {H : Type*} [Group H] (z : H) (v : Fin 2 → H) (w : PositiveWord) :
    value (fun i => z * v i * z⁻¹) w = z * value v w * z⁻¹ := by
  induction w with
  | nil => simp
  | cons i w ih => rw [value_cons, value_cons, ih]; group

theorem value_mul {H : Type*} [Group H] (v v' : Fin 2 → H)
    (hc : ∀ i j, Commute (v' i) (v j)) (w : PositiveWord) :
    value (fun i => v i * v' i) w = value v w * value v' w := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [value_cons, ih]
    have hh := value_commute (v' i) v (hc i) w
    calc
      (v i * v' i) * (value v w * value v' w) =
        v i * (v' i * value v w) * value v' w := by group
      _ = (v i * value v w) * (v' i * value v' w) := by rw [hh.eq]; group

theorem commute_closure {A H : Type*} [Group A] [Group H] (φ : A →* H)
    (z : H) (S : Set A) (hs : ∀ x ∈ S, Commute z (φ x))
    {x : A} (hx : x ∈ Subgroup.closure S) : Commute z (φ x) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y _ _ hx hy => simpa using hx.mul_right hy
  | inv x _ hx => simpa using hx.inv_right

end PositiveEvaluation

end UniversalGroup
