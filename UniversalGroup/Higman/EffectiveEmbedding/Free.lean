module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-! The countable free family of conjugates in the free group on two letters. -/
namespace UniversalGroup.EffectiveEmbeddingFree
noncomputable section

abbrev State := ℤ × FreeGroup ℕ
def shift : Equiv.Perm State where
  toFun z := (z.1 + 1,z.2)
  invFun z := (z.1 - 1,z.2)
  left_inv := by intro ⟨i,w⟩; simp
  right_inv := by intro ⟨i,w⟩; simp
def label (k : ℤ) : FreeGroup ℕ := if 0 ≤ k then FreeGroup.of k.toNat else 1
def write : Equiv.Perm State where
  toFun z := (z.1,label z.1*z.2)
  invFun z := (z.1,(label z.1)⁻¹*z.2)
  left_inv := by intro ⟨i,w⟩; simp
  right_inv := by intro ⟨i,w⟩; simp

theorem shift_pow (j : ℕ) (k : ℤ) (w : FreeGroup ℕ) :
    (shift ^ j) (k,w) = (k+(j:ℤ),w) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ,Equiv.Perm.mul_apply]
    change (shift ^ j) (k+1,w) = _
    rw [ih]
    congr 1
    omega
theorem shift_inv_pow (j : ℕ) (k : ℤ) (w : FreeGroup ℕ) :
    (shift⁻¹ ^ j) (k,w) = (k-(j:ℤ),w) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ,Equiv.Perm.mul_apply]
    change (shift⁻¹ ^ j) (k-1,w) = _
    rw [ih]
    congr 1
    omega

@[simp] theorem label_nat (i : ℕ) : label (i:ℤ) = FreeGroup.of i := by simp [label]

def conjugates : FreeGroup ℕ →* FreeGroup (Fin 2) :=
  FreeGroup.lift fun i => ((FreeGroup.of (0:Fin 2))^i)⁻¹ * FreeGroup.of 1 *
    (FreeGroup.of 0)^i
def representation : FreeGroup (Fin 2) →* Equiv.Perm State :=
  FreeGroup.lift ![shift,write]

theorem generator_action (i : ℕ) (w : FreeGroup ℕ) :
    representation (conjugates (FreeGroup.of i)) (0,w) = (0,FreeGroup.of i*w) := by
  simp only [conjugates,FreeGroup.lift_apply_of,map_mul,map_inv,map_pow,
    representation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Equiv.Perm.mul_apply,shift_pow,zero_add,← inv_pow]
  change (shift⁻¹ ^ i) ((i:ℤ),label (i:ℤ)*w) = _
  rw [label_nat,shift_inv_pow]
  simp

def ActsAs (p : Equiv.Perm State) (x : FreeGroup ℕ) : Prop := ∀ w,p (0,w)=(0,x*w)
theorem actsAs_one : ActsAs 1 1 := by intro w;simp
theorem ActsAs.mul {p q : Equiv.Perm State} {x y : FreeGroup ℕ}
    (hp : ActsAs p x) (hq : ActsAs q y) : ActsAs (p*q) (x*y) := by
  intro w
  rw [Equiv.Perm.mul_apply,hq,hp,mul_assoc]
theorem ActsAs.inv {p : Equiv.Perm State} {x : FreeGroup ℕ}
    (hp : ActsAs p x) : ActsAs p⁻¹ x⁻¹ := by
  intro w
  apply p.injective
  rw [hp]
  simp

theorem conjugates_injective : Function.Injective conjugates := by
  have ha (g : FreeGroup ℕ) : ActsAs (representation (conjugates g)) g := by
    induction g using FreeGroup.induction_on with
    | one => simpa only [map_one] using actsAs_one
    | of i => exact generator_action i
    | inv_of i hi => simpa only [map_inv] using hi.inv
    | mul g h hg hh => simpa only [map_mul] using hg.mul hh
  intro g h he
  have hs := congrArg (fun p => representation p (0,1)) he
  rw [ha,ha] at hs
  simpa using hs

end
end UniversalGroup.EffectiveEmbeddingFree
