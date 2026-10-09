module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

/-! Free subgroups in the kernel of `C₄ * C₄ → C₄`, detected by explicit permutation actions. -/
namespace UniversalGroup.PreparationFreeProduct
noncomputable section
set_option maxHeartbeats 1000000
abbrev Cyclic := Multiplicative (ZMod 4)
def generator : Cyclic := Multiplicative.ofAdd 1
abbrev Pair := Monoid.Coprod Cyclic Cyclic
def b : Pair := Monoid.Coprod.inl generator
def v : Pair := Monoid.Coprod.inr generator
def projection : Pair →* Cyclic := Monoid.Coprod.lift (MonoidHom.id _) 1

/-- A fourth-root relation gives a homomorphism from the cyclic group of order four. -/
def cyclicHom {H : Type*} [Group H] (p : H) (hp : p^4=1) : Cyclic →* H where
  toFun x := p ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    change p ^ (x.toAdd+y.toAdd).val = p ^ x.toAdd.val * p ^ y.toAdd.val
    rw [ZMod.val_add,← pow_add]
    have hm (n : ℕ) : p^(n%4) = p^n := by
      conv_rhs => rw [← Nat.mod_add_div n 4]
      rw [pow_add,pow_mul,hp,one_pow,mul_one]
    exact hm _

@[simp] theorem cyclicHom_generator {H : Type*} [Group H] (p : H) (hp : p^4=1) :
    cyclicHom p hp generator = p := by
  change p ^ (1 : ZMod 4).val = p
  rw [show (1 : ZMod 4).val = 1 by decide,pow_one]

abbrev State (H : Type*) := Fin 4 × Bool × Bool × H
variable {H : Type*}

/-- A cyclic permutation of four coordinates. -/
def cycle : Equiv.Perm (State H) where
  toFun z := (![1,2,3,0] z.1,z.2)
  invFun z := (![3,0,1,2] z.1,z.2)
  left_inv := by intro ⟨i,z⟩;fin_cases i <;> rfl
  right_inv := by intro ⟨i,z⟩;fin_cases i <;> rfl

theorem cycle_four : (cycle : Equiv.Perm (State H))^4=1 := by
  apply Equiv.ext
  intro ⟨i,z⟩
  fin_cases i <;> rfl

variable [Group H]

/-- Lift four arbitrary translations to a permutation whose fourth power is one.
Its square is an involution reversing the sign on each coordinate. -/
def rotor (values : Fin 4 → H) : Equiv.Perm (State H) where
  toFun z := (z.1, if z.2.1 then
    (false, !z.2.2.1, (if z.2.2.1 then (values z.1)⁻¹ else values z.1)*z.2.2.2)
    else (true,z.2.2))
  invFun z := (z.1, if z.2.1 then (false,z.2.2) else
    (true,!z.2.2.1,(if z.2.2.1 then (values z.1)⁻¹ else values z.1)*z.2.2.2))
  left_inv := by intro ⟨i,q,e,w⟩;cases q <;> cases e <;> simp
  right_inv := by intro ⟨i,q,e,w⟩;cases q <;> cases e <;> simp

theorem rotor_four (values : Fin 4 → H) : rotor values ^ 4 = 1 := by
  apply Equiv.ext
  intro ⟨i,q,e,w⟩
  cases q <;> cases e <;>
    simp [rotor,pow_succ,Equiv.Perm.mul_apply]

def representation (x y : H) : Pair →* Equiv.Perm (State H) :=
  Monoid.Coprod.lift (cyclicHom cycle cycle_four)
    (cyclicHom (rotor ![1,x,y,1]) (rotor_four _))

@[simp] theorem representation_b (x y : H) : representation x y b = cycle := by
  simp [representation,b]
@[simp] theorem representation_v (x y : H) :
    representation x y v = rotor ![1,x,y,1] := by simp [representation,v]

def freePair : FreeGroup (Fin 2) →* Pair :=
  FreeGroup.lift ![v^2*b⁻¹*v^2*b, v^2*(b^2)⁻¹*v^2*b^2]

theorem pair_action (x y : H) (i : Fin 2) (w : H) :
    representation x y (freePair (FreeGroup.of i)) (0,false,false,w) =
      (0,false,false,![x,y] i*w) := by
  fin_cases i <;>
    simp [freePair,map_mul,map_inv,cycle,rotor,Equiv.Perm.mul_apply,pow_succ]

def ActsAs (p : Equiv.Perm (State H)) (x : H) : Prop :=
  ∀ w, p (0,false,false,w) = (0,false,false,x*w)
theorem actsAs_one : ActsAs (1 : Equiv.Perm (State H)) (1:H) := by intro w;simp

theorem ActsAs.mul {p q : Equiv.Perm (State H)} {x y : H}
    (hp : ActsAs p x) (hq : ActsAs q y) : ActsAs (p*q) (x*y) := by
  intro w
  rw [Equiv.Perm.mul_apply,hq,hp,mul_assoc]
theorem ActsAs.inv {p : Equiv.Perm (State H)} {x : H}
    (hp : ActsAs p x) : ActsAs p⁻¹ x⁻¹ := by
  intro w
  apply p.injective
  rw [hp]
  simp

theorem freePair_injective : Function.Injective freePair := by
  let ρ := representation (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1)
  have ha (g : FreeGroup (Fin 2)) : ActsAs (ρ (freePair g)) g := by
    induction g using FreeGroup.induction_on with
    | one => simpa only [map_one] using (actsAs_one (H := FreeGroup (Fin 2)))
    | of i =>
        intro w
        have h := pair_action (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1) i w
        fin_cases i <;> exact h
    | inv_of i hi => simpa only [map_inv] using hi.inv
    | mul g h hg hh => simpa only [map_mul] using hg.mul hh
  intro g h he
  have hs := congrArg (fun p => ρ p (0,false,false,1)) he
  rw [ha,ha] at hs
  simpa using hs

@[simp] theorem projection_b : projection b = generator := by simp [projection,b]
@[simp] theorem projection_v : projection v = 1 := by simp [projection,v]

theorem projection_freePair (g : FreeGroup (Fin 2)) : projection (freePair g) = 1 := by
  have he : projection.comp freePair = 1 := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [freePair]
  exact DFunLike.congr_fun he g

namespace FiniteFree
abbrev State (n : ℕ) := ℤ × FreeGroup (Fin n)
def shift (n : ℕ) : Equiv.Perm (State n) where
  toFun z := (z.1+1,z.2)
  invFun z := (z.1-1,z.2)
  left_inv := by intro ⟨i,w⟩;simp
  right_inv := by intro ⟨i,w⟩;simp

def label (n : ℕ) (k : ℤ) : FreeGroup (Fin n) :=
  if h : 0 ≤ k ∧ k < (n : ℤ) then FreeGroup.of ⟨k.toNat,by omega⟩ else 1

def write (n : ℕ) : Equiv.Perm (State n) where
  toFun z := (z.1,label n z.1*z.2)
  invFun z := (z.1,(label n z.1)⁻¹*z.2)
  left_inv := by intro ⟨i,w⟩;simp
  right_inv := by intro ⟨i,w⟩;simp

theorem shift_pow (n j : ℕ) (k : ℤ) (w : FreeGroup (Fin n)) :
    (shift n ^ j) (k,w) = (k+(j:ℤ),w) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
      rw [pow_succ,Equiv.Perm.mul_apply]
      change (shift n ^ j) (k+1,w) = _
      rw [ih]
      congr 1
      omega

theorem shift_inv_pow (n j : ℕ) (k : ℤ) (w : FreeGroup (Fin n)) :
    ((shift n)⁻¹ ^ j) (k,w) = (k-(j:ℤ),w) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
      rw [pow_succ,Equiv.Perm.mul_apply]
      change ((shift n)⁻¹ ^ j) (k-1,w) = _
      rw [ih]
      congr 1
      omega

@[simp] theorem label_nat (n : ℕ) (i : Fin n) : label n (i.val:ℤ) = FreeGroup.of i := by
  simp [label,i.isLt]

def hom (n : ℕ) : FreeGroup (Fin n) →* FreeGroup (Fin 2) :=
  FreeGroup.lift fun i => ((FreeGroup.of (0:Fin 2))^i.val)⁻¹ * FreeGroup.of 1 *
    (FreeGroup.of 0)^i.val

def representation (n : ℕ) : FreeGroup (Fin 2) →* Equiv.Perm (State n) :=
  FreeGroup.lift ![shift n,write n]

theorem generator_action (n : ℕ) (i : Fin n) (w : FreeGroup (Fin n)) :
    representation n (hom n (FreeGroup.of i)) (0,w) = (0,FreeGroup.of i*w) := by
  simp only [hom,FreeGroup.lift_apply_of,map_mul,map_inv,map_pow,
    representation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Equiv.Perm.mul_apply,shift_pow,zero_add,← inv_pow]
  change ((shift n)⁻¹ ^ i.val) ((i.val:ℤ),label n (i.val:ℤ)*w) = _
  rw [label_nat,shift_inv_pow]
  simp

def ActsAs (n : ℕ) (p : Equiv.Perm (State n)) (x : FreeGroup (Fin n)) : Prop :=
  ∀ w,p (0,w) = (0,x*w)
theorem actsAs_one (n : ℕ) : ActsAs n 1 1 := by intro w;simp
theorem ActsAs.mul {n : ℕ} {p q : Equiv.Perm (State n)} {x y : FreeGroup (Fin n)}
    (hp : ActsAs n p x) (hq : ActsAs n q y) : ActsAs n (p*q) (x*y) := by
  intro w
  rw [Equiv.Perm.mul_apply,hq,hp,mul_assoc]
theorem ActsAs.inv {n : ℕ} {p : Equiv.Perm (State n)} {x : FreeGroup (Fin n)}
    (hp : ActsAs n p x) : ActsAs n p⁻¹ x⁻¹ := by
  intro w
  apply p.injective
  rw [hp]
  simp

theorem hom_injective (n : ℕ) : Function.Injective (hom n) := by
  have ha (g : FreeGroup (Fin n)) : ActsAs n (representation n (hom n g)) g := by
    induction g using FreeGroup.induction_on with
    | one => simpa only [map_one] using actsAs_one n
    | of i => exact generator_action n i
    | inv_of i hi => simpa only [map_inv] using hi.inv
    | mul g h hg hh => simpa only [map_mul] using hg.mul hh
  intro g h he
  have hs := congrArg (fun p => representation n p (0,1)) he
  rw [ha,ha] at hs
  simpa using hs
end FiniteFree

/-- A free family of any prescribed finite size inside the projection kernel. -/
def freeFamily (n : ℕ) : FreeGroup (Fin n) →* Pair := freePair.comp (FiniteFree.hom n)
theorem freeFamily_injective (n : ℕ) : Function.Injective (freeFamily n) :=
  freePair_injective.comp (FiniteFree.hom_injective n)
@[simp] theorem projection_freeFamily (n : ℕ) (g : FreeGroup (Fin n)) :
    projection (freeFamily n g) = 1 := projection_freePair _

theorem freeFamilyProjection (n : ℕ) : projection.comp (freeFamily n) = 1 := by
  apply DFunLike.ext
  intro g
  exact projection_freeFamily n g

end
end UniversalGroup.PreparationFreeProduct
