module

public import UniversalGroup.Simulator.Core.SupportedRules
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Free coded subgroups, detected by finite-state permutation actions

The first three states decode the two code words independently. A fourth
state later detects the two conjugated simulator letters. The state labels
lie in a free group, so equality of the induced permutations detects every
word in the proposed free basis.
-/

namespace UniversalGroup.CodeSubgroups

noncomputable section

abbrev State (H : Type*) := Fin 4 × H

variable {H : Type*} [Group H]

/-- Translate the group coordinate by a label depending on the state. -/
def fiber (v : Fin 4 → H) : Equiv.Perm (State H) where
  toFun z := (z.1, v z.1 * z.2)
  invFun z := (z.1, (v z.1)⁻¹ * z.2)
  left_inv := by intro ⟨i, z⟩; simp
  right_inv := by intro ⟨i, z⟩; simp

@[simp] theorem fiber_apply (v : Fin 4 → H) (i : Fin 4) (z : H) :
    fiber v (i, z) = (i, v i * z) := rfl

@[simp] theorem fiber_pow_apply (v : Fin 4 → H) (n : ℕ) (i : Fin 4) (z : H) :
    (fiber v ^ n) (i, z) = (i, v i ^ n * z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih => simp [pow_succ, Equiv.Perm.mul_apply, ih, mul_assoc]

/-- Cycle states `0,1,2`, and translate at the fixed fourth state. -/
def cycle (z : H) : Equiv.Perm (State H) where
  toFun p := (![1, 2, 0, 3] p.1, if p.1 = 3 then z * p.2 else p.2)
  invFun p := (![2, 0, 1, 3] p.1, if p.1 = 3 then z⁻¹ * p.2 else p.2)
  left_inv := by intro ⟨i, w⟩; fin_cases i <;> simp
  right_inv := by intro ⟨i, w⟩; fin_cases i <;> simp

@[simp] theorem cycle_zero (z w : H) : cycle z (0, w) = (1, w) := rfl
@[simp] theorem cycle_one (z w : H) : cycle z (1, w) = (2, w) := rfl
@[simp] theorem cycle_two (z w : H) : cycle z (2, w) = (0, w) := rfl
@[simp] theorem cycle_three (z w : H) : cycle z (3, w) = (3, z * w) := rfl

/-- The code-decoding labels; the fourth label remains independently available. -/
def letterA (x y z : H) : Equiv.Perm (State H) :=
  fiber ![1, x⁻¹ * y, x * ((x⁻¹ * y) ^ 2)⁻¹, z]

def letterB (z : H) : Equiv.Perm (State H) := cycle z

/-- The two code words act by arbitrary prescribed translations at state zero. -/
theorem code_action (x y z t : H) (r : ℕ) (i : Fin 2) (w : H) :
    evalPositive (letterA x y z) (letterB t) (valievCode r i) (0, w) =
      (0, ![x, y] i * w) := by
  fin_cases i <;>
    simp [valievCode, evalPositive, letterA, letterB,
      Equiv.Perm.mul_apply, mul_assoc, pow_succ]

/-- An action preserves the distinguished fiber and translates it by `x`. -/
def ActsAs (p : Equiv.Perm (State H)) (x : H) : Prop :=
  ∀ w, p (0, w) = (0, x * w)

theorem actsAs_one : ActsAs (1 : Equiv.Perm (State H)) (1 : H) := by
  intro w
  simp

theorem ActsAs.mul {p q : Equiv.Perm (State H)} {x y : H}
    (hp : ActsAs p x) (hq : ActsAs q y) : ActsAs (p * q) (x * y) := by
  intro w
  rw [Equiv.Perm.mul_apply, hq w, hp (y * w), mul_assoc]

theorem ActsAs.inv {p : Equiv.Perm (State H)} {x : H}
    (hp : ActsAs p x) : ActsAs p⁻¹ x⁻¹ := by
  intro w
  apply p.injective
  rw [hp (x⁻¹ * w)]
  simp

/-- A homomorphism acting by the free generators on one fiber is injective. -/
theorem injective_of_generator_actions {ι : Type*}
    (φ : FreeGroup ι →* Equiv.Perm (State (FreeGroup ι)))
    (hφ : ∀ i, ActsAs (φ (FreeGroup.of i)) (FreeGroup.of i)) :
    Function.Injective φ := by
  have hacts (w : FreeGroup ι) : ActsAs (φ w) w := by
    induction w using FreeGroup.induction_on with
    | one => simpa only [map_one] using (actsAs_one (H := FreeGroup ι))
    | of i => exact hφ i
    | inv_of i hi => simpa only [map_inv] using hi.inv
    | mul u v hu hv => simpa only [map_mul] using hu.mul hv
  intro u v huv
  have h := congrArg (fun p : Equiv.Perm (State (FreeGroup ι)) => p (0, 1)) huv
  rw [hacts u 1, hacts v 1] at h
  simpa only [mul_one, Prod.mk.injEq, true_and] using h

/-- Positive binary words evaluated in the free group on the first two letters. -/
def positiveFree (w : PositiveWord) : FreeGroup (Fin 2) :=
  evalPositive (FreeGroup.of 0) (FreeGroup.of 1) w

theorem map_positive {K : Type*} [Group K] (f : H →* K) (a b : H) (w : PositiveWord) :
    f (evalPositive a b w) = evalPositive (f a) (f b) w := by
  simp only [evalPositive, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  fin_cases i <;> simp

/-- The canonical map from two free generators to the two literal code words. -/
def codeLift (r : ℕ) : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
  FreeGroup.lift (fun i => positiveFree (valievCode r i))

/-- The code words are a free pair, even without a lower bound on `r`. -/
theorem codeLift_injective (r : ℕ) : Function.Injective (codeLift r) := by
  let ρ : FreeGroup (Fin 2) →* Equiv.Perm (State (FreeGroup (Fin 2))) :=
    FreeGroup.lift ![letterA (FreeGroup.of 0) (FreeGroup.of 1) 1, letterB 1]
  have hρ : Function.Injective (ρ.comp (codeLift r)) := by
    apply injective_of_generator_actions
    intro i w
    simp only [MonoidHom.comp_apply, codeLift, FreeGroup.lift_apply_of,
      positiveFree, map_positive]
    have h := code_action (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1) 1 1 r i w
    fin_cases i <;> simpa [ρ] using h
  intro u v huv
  exact hρ (congrArg ρ huv)

/-- Exchange the distinguished fiber with the independent fourth fiber. -/
def swapOuter : Equiv.Perm (State H) where
  toFun p := (![3, 1, 2, 0] p.1, p.2)
  invFun p := (![3, 1, 2, 0] p.1, p.2)
  left_inv := by intro ⟨i, w⟩; fin_cases i <;> rfl
  right_inv := by intro ⟨i, w⟩; fin_cases i <;> rfl

omit [Group H] in
@[simp] theorem swapOuter_apply (i : Fin 4) (w : H) :
    swapOuter (i, w) = (![3, 1, 2, 0] i, w) := rfl

omit [Group H] in
@[simp] theorem swapOuter_inv_apply (i : Fin 4) (w : H) :
    swapOuter⁻¹ (i, w) = (![3, 1, 2, 0] i, w) := rfl

/-- Positive words in the first two generators of the free group `F(s₁,s₂,f,q)`. -/
def positiveFour (w : PositiveWord) : FreeGroup (Fin 4) :=
  evalPositive (FreeGroup.of 0) (FreeGroup.of 1) w

def aFreeValues (D : CodeWords) : Fin 5 → FreeGroup (Fin 4) :=
  ![positiveFour (D.code 0), positiveFour (D.code 1),
    (FreeGroup.of 2)⁻¹ * FreeGroup.of 0 * FreeGroup.of 2,
    (FreeGroup.of 2)⁻¹ * FreeGroup.of 1 * FreeGroup.of 2,
    positiveFour D.P * FreeGroup.of 3 * FreeGroup.of 2]

def aFreeLift (D : CodeWords) : FreeGroup (Fin 5) →* FreeGroup (Fin 4) :=
  FreeGroup.lift (aFreeValues D)

def aRepValues (D : CodeWords) : Fin 4 → Equiv.Perm (State (FreeGroup (Fin 5))) :=
  let a := letterA (FreeGroup.of 0) (FreeGroup.of 1) (FreeGroup.of 2)
  let b := letterB (FreeGroup.of 3)
  let f : Equiv.Perm (State (FreeGroup (Fin 5))) := swapOuter
  let q := (evalPositive a b D.P)⁻¹ * fiber ![FreeGroup.of 4, 1, 1, 1] * f⁻¹
  ![a, b, f, q]

def aRep (D : CodeWords) :
    FreeGroup (Fin 4) →* Equiv.Perm (State (FreeGroup (Fin 5))) :=
  FreeGroup.lift (aRepValues D)

theorem aRep_actions (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r)
    (i : Fin 5) : ActsAs (aRep D (aFreeValues D i)) (FreeGroup.of i) := by
  intro w
  fin_cases i
  · have h := code_action (FreeGroup.of (0 : Fin 5)) (FreeGroup.of 1)
      (FreeGroup.of 2) (FreeGroup.of 3) r 0 w
    simpa [aFreeValues, positiveFour, map_positive, aRep, aRepValues, hcode] using h
  · have h := code_action (FreeGroup.of (0 : Fin 5)) (FreeGroup.of 1)
      (FreeGroup.of 2) (FreeGroup.of 3) r 1 w
    simpa [aFreeValues, positiveFour, map_positive, aRep, aRepValues, hcode] using h
  · simp [aFreeValues, aRep, aRepValues, letterA, Equiv.Perm.mul_apply]
  · simp [aFreeValues, aRep, aRepValues, letterB, Equiv.Perm.mul_apply]
  · simp [aFreeValues, positiveFour, map_positive, aRep, aRepValues, mul_assoc]

/-- The five generators defining `A` are a free basis in the free four-letter group. -/
theorem aFreeLift_injective (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r) :
    Function.Injective (aFreeLift D) := by
  have hρ : Function.Injective ((aRep D).comp (aFreeLift D)) := by
    apply injective_of_generator_actions
    intro i
    simpa [aFreeLift] using aRep_actions D r hcode i
  intro u v huv
  exact hρ (congrArg (aRep D) huv)

end
end UniversalGroup.CodeSubgroups
