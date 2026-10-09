module

public import UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# A protected row triple detected by a four-state action

A proper HNN extension supplies `S³ U S⁻³ = V` inside a group retaining a
free triple `Q,P,R`.  Explicit weighted permutations on four states then
satisfy `(c b⁻³ c b³)² = 1`, while `b, cbc⁻¹, c³` act at state one as
translations by `Q,P,R`.  Thus that triple is free even after imposing the
square relation.  This gives a small-cancellation-free target for preparation.
-/

namespace UniversalGroup.Embedding.ProtectedAction

noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Base := FreeGroup (Fin 5)
abbrev Parameters := FreeGroup (Fin 3)

def p₀ : Base := FreeGroup.of 1
def q₀ : Base := FreeGroup.of 0
def r₀ : Base := FreeGroup.of 2
def x₀ : Base := FreeGroup.of 3
def y₀ : Base := FreeGroup.of 4

def u₀ : Base := r₀⁻¹ * (p₀ ^ 3)⁻¹ * q₀ ^ 3
def v₀ : Base := r₀⁻¹ * p₀ ^ 3 * (q₀ ^ 3)⁻¹

def left : Parameters →* Base := FreeGroup.lift ![u₀,x₀,y₀]
def right : Parameters →* Base := FreeGroup.lift ![x₀,y₀,v₀]

private def retractLeft : Base →* Parameters :=
  FreeGroup.lift ![1,1,(FreeGroup.of 0)⁻¹,FreeGroup.of 1,FreeGroup.of 2]

private def retractRight : Base →* Parameters :=
  FreeGroup.lift ![1,1,(FreeGroup.of 2)⁻¹,FreeGroup.of 0,FreeGroup.of 1]

private theorem retractLeft_comp : retractLeft.comp left = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [retractLeft, left, u₀, p₀, q₀, r₀, x₀, y₀]

private theorem retractRight_comp : retractRight.comp right = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [retractRight, right, v₀, p₀, q₀, r₀, x₀, y₀]

theorem left_injective : Function.Injective left := by
  intro a b h
  have hh := congrArg retractLeft h
  simpa only [← MonoidHom.comp_apply, retractLeft_comp, MonoidHom.id_apply] using hh

theorem right_injective : Function.Injective right := by
  intro a b h
  have hh := congrArg retractRight h
  simpa only [← MonoidHom.comp_apply, retractRight_comp, MonoidHom.id_apply] using hh

abbrev Auxiliary := IdentifyingHNN left right left_injective right_injective

def of : Base →* Auxiliary := IdentifyingHNN.of _ _ _ _
def stable : Auxiliary := IdentifyingHNN.stable _ _ _ _

def P : Auxiliary := of p₀
def Q : Auxiliary := of q₀
def R : Auxiliary := of r₀
def S : Auxiliary := stable⁻¹

def U : Auxiliary := R⁻¹ * (P ^ 3)⁻¹ * Q ^ 3
def V : Auxiliary := R⁻¹ * P ^ 3 * (Q ^ 3)⁻¹
def Z : Auxiliary := S * U * S⁻¹

private theorem conjugates (i : Fin 3) :
    stable⁻¹ * of (![u₀,x₀,y₀] i) * stable = of (![x₀,y₀,v₀] i) := by
  have h := IdentifyingHNN.conjugates left right left_injective right_injective
    (FreeGroup.of i)
  change stable⁻¹ * of (left (FreeGroup.of i)) * stable = of (right (FreeGroup.of i)) at h
  have hl : left (FreeGroup.of i) = ![u₀,x₀,y₀] i := FreeGroup.lift_apply_of
  have hr : right (FreeGroup.of i) = ![x₀,y₀,v₀] i := FreeGroup.lift_apply_of
  rw [hl, hr] at h
  exact h

/-- Three successive HNN identifications give the sole auxiliary relation. -/
theorem auxiliary_relation : S ^ 3 * U * (S ^ 3)⁻¹ = V := by
  have h₀ := conjugates 0
  have h₁ := conjugates 1
  have h₂ := conjugates 2
  simp only [Matrix.cons_val] at h₀ h₁ h₂
  have hu : of u₀ = U := by simp [u₀, U, P, Q, R]
  have hv : of v₀ = V := by simp [v₀, V, P, Q, R]
  rw [hu] at h₀
  rw [hv] at h₂
  calc
    S ^ 3 * U * (S ^ 3)⁻¹ =
        stable⁻¹ * (stable⁻¹ * (stable⁻¹ * U * stable) * stable) * stable := by
      simp [S, pow_succ, mul_assoc]
    _ = V := by rw [h₀, h₁, h₂]

/-- The original three generators still freely generate in the proper extension. -/
def freeTriple : Parameters →* Auxiliary :=
  of.comp (FreeGroup.map (![0,1,2] : Fin 3 → Fin 5))

theorem freeTriple_injective : Function.Injective freeTriple := by
  apply (IdentifyingHNN.of_injective left right left_injective right_injective).comp
  apply FreeGroup.map_injective
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem freeTriple_of (i : Fin 3) :
    freeTriple (FreeGroup.of i) = ![Q,P,R] i := by
  fin_cases i <;> simp [freeTriple, P, Q, R, p₀, q₀, r₀]

abbrev State := Fin 4 × Auxiliary

def b : Equiv.Perm State where
  toFun z := (![0,1,3,2] z.1, (![P,Q,1,S] z.1) * z.2)
  invFun z := (![0,1,3,2] z.1, (![P⁻¹,Q⁻¹,S⁻¹,1] z.1) * z.2)
  left_inv := by intro ⟨i,w⟩; fin_cases i <;> simp
  right_inv := by intro ⟨i,w⟩; fin_cases i <;> simp

def c : Equiv.Perm State where
  toFun z := (![1,2,0,3] z.1, (![1,1,R,Z] z.1) * z.2)
  invFun z := (![2,0,1,3] z.1, (![R⁻¹,1,1,Z⁻¹] z.1) * z.2)
  left_inv := by intro ⟨i,w⟩; fin_cases i <;> simp
  right_inv := by intro ⟨i,w⟩; fin_cases i <;> simp

private def W : Equiv.Perm State := c * (b ^ 3)⁻¹ * c * b ^ 3

private theorem W_zero (w : Auxiliary) : W (0,w) = (2,(Q ^ 3)⁻¹ * P ^ 3 * w) := by
  simp [W, b, c, pow_succ, Equiv.Perm.mul_apply, mul_assoc]

private theorem W_one (w : Auxiliary) : W (1,w) = (3,Z * (S ^ 2)⁻¹ * Q ^ 3 * w) := by
  simp [W, b, c, pow_succ, Equiv.Perm.mul_apply, mul_assoc]

private theorem W_two (w : Auxiliary) : W (2,w) = (0,R * S⁻¹ * Z * S * w) := by
  simp [W, b, c, pow_succ, Equiv.Perm.mul_apply, mul_assoc]

private theorem W_three (w : Auxiliary) : W (3,w) = (1,(P ^ 3)⁻¹ * R * S ^ 2 * w) := by
  simp [W, b, c, pow_succ, Equiv.Perm.mul_apply, mul_assoc]

private theorem cancel_zero : R * S⁻¹ * Z * S * (Q ^ 3)⁻¹ * P ^ 3 = 1 := by
  simp only [Z, U]
  group

private theorem cancel_one : (P ^ 3)⁻¹ * R * S ^ 2 * Z * (S ^ 2)⁻¹ * Q ^ 3 = 1 := by
  calc
    (P ^ 3)⁻¹ * R * S ^ 2 * Z * (S ^ 2)⁻¹ * Q ^ 3 =
        (P ^ 3)⁻¹ * R * (S ^ 3 * U * (S ^ 3)⁻¹) * Q ^ 3 := by
      simp only [Z]
      group
    _ = 1 := by rw [auxiliary_relation]; simp only [V]; group

/-- The marked row relation holds in the weighted permutation action on `Fin 4 × Auxiliary`. -/
theorem relation : (c * (b ^ 3)⁻¹ * c * b ^ 3) ^ 2 = 1 := by
  change W ^ 2 = 1
  apply Equiv.ext
  intro ⟨i,w⟩
  rw [pow_two, Equiv.Perm.mul_apply]
  fin_cases i
  · change W (W (0,w)) = (0,w)
    rw [W_zero, W_two]
    change (0, R * S⁻¹ * Z * S * ((Q ^ 3)⁻¹ * P ^ 3 * w)) = (0,w)
    have h := congrArg (fun z => z * w) cancel_zero
    simpa only [one_mul, mul_assoc] using congrArg (Prod.mk (0 : Fin 4)) h
  · change W (W (1,w)) = (1,w)
    rw [W_one, W_three]
    have h := congrArg (fun z => z * w) cancel_one
    simpa only [one_mul, mul_assoc] using congrArg (Prod.mk (1 : Fin 4)) h
  · change W (W (2,w)) = (2,w)
    rw [W_two, W_zero]
    have h : (Q ^ 3)⁻¹ * P ^ 3 * (R * S⁻¹ * Z * S) = 1 := by
      exact mul_eq_one_comm.mp (by simpa only [mul_assoc] using cancel_zero)
    simpa only [one_mul, mul_assoc] using congrArg (Prod.mk (2 : Fin 4))
      (congrArg (fun z => z * w) h)
  · change W (W (3,w)) = (3,w)
    rw [W_three, W_one]
    have h : Z * (S ^ 2)⁻¹ * Q ^ 3 * ((P ^ 3)⁻¹ * R * S ^ 2) = 1 := by
      exact mul_eq_one_comm.mp (by simpa only [mul_assoc] using cancel_one)
    simpa only [one_mul, mul_assoc] using congrArg (Prod.mk (3 : Fin 4))
      (congrArg (fun z => z * w) h)

def triple : Parameters →* Equiv.Perm State := FreeGroup.lift ![b,c*b*c⁻¹,c^3]

private theorem triple_of_action (i : Fin 3) (w : Auxiliary) :
    triple (FreeGroup.of i) (1,w) = (1,freeTriple (FreeGroup.of i)*w) := by
  fin_cases i <;>
    simp [triple, b, c, pow_succ, Equiv.Perm.mul_apply, mul_assoc]

private def ActsAs (p : Equiv.Perm State) (x : Auxiliary) : Prop :=
  ∀ w, p (1,w) = (1,x*w)

private theorem actsAs_one : ActsAs 1 1 := by intro w; simp

private theorem ActsAs.mul {p q : Equiv.Perm State} {x y : Auxiliary}
    (hp : ActsAs p x) (hq : ActsAs q y) : ActsAs (p*q) (x*y) := by
  intro w
  rw [Equiv.Perm.mul_apply, hq, hp, mul_assoc]

private theorem ActsAs.inv {p : Equiv.Perm State} {x : Auxiliary}
    (hp : ActsAs p x) : ActsAs p⁻¹ x⁻¹ := by
  intro w
  apply p.injective
  rw [hp]
  simp

/-- The three row words freely generate despite the imposed square relation. -/
theorem triple_injective : Function.Injective triple := by
  have ha (g : Parameters) : ActsAs (triple g) (freeTriple g) := by
    induction g using FreeGroup.induction_on with
    | one => simpa only [map_one] using actsAs_one
    | of i => exact triple_of_action i
    | inv_of i hi => simpa only [map_inv] using hi.inv
    | mul g h hg hh => simpa only [map_mul] using hg.mul hh
  intro x y h
  apply freeTriple_injective
  have hh := congrArg (fun p => p (1,1)) h
  rw [ha, ha] at hh
  simpa using hh

end
end UniversalGroup.Embedding.ProtectedAction
