module

public import UniversalGroup.Higman.EffectiveEmbedding.Free
public import UniversalGroup.Higman.Enumeration
public import UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

@[expose] public section

/-! The algebraic part of the effective countable-to-two-generator HNN embedding. -/
namespace UniversalGroup.EffectiveEmbeddingHNN
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Monoid

variable (R : RecursivePresentation ℕ)
abbrev Base := Coprod R.Group (FreeGroup (Fin 2))
def a : Base R := Coprod.inr (FreeGroup.of 1)
def b : Base R := Coprod.inr (FreeGroup.of 0)
def g (i : ℕ) : Base R := Coprod.inl (PresentedGroup.of i)

def left : FreeGroup ℕ →* Base R := Coprod.inr.comp EffectiveEmbeddingFree.conjugates
def right : FreeGroup ℕ →* Base R := FreeGroup.lift fun i =>
  match i with
  | 0 => b R
  | j+1 => g R j * (a R ^ (j+1))⁻¹ * b R * a R ^ (j+1)

theorem left_injective : Function.Injective (left R) :=
  Coprod.inr_injective.comp EffectiveEmbeddingFree.conjugates_injective

def projection : Base R →* FreeGroup (Fin 2) := Coprod.lift 1 (MonoidHom.id _)
def swap : FreeGroup (Fin 2) →* FreeGroup (Fin 2) := FreeGroup.map (Equiv.swap 0 1)

theorem projection_right : (projection R).comp (right R) = swap.comp EffectiveEmbeddingFree.conjugates := by
  apply FreeGroup.ext_hom
  intro i
  cases i <;> simp [right,g,a,b,projection,swap,EffectiveEmbeddingFree.conjugates]

theorem right_injective : Function.Injective (right R) := by
  intro x y h
  apply EffectiveEmbeddingFree.conjugates_injective
  apply FreeGroup.map_injective (Equiv.swap 0 1).injective
  have he := congrArg (projection R) h
  change ((projection R).comp (right R)) x = ((projection R).comp (right R)) y at he
  rw [projection_right] at he
  exact he

abbrev Host := IdentifyingHNN (left R) (right R) (left_injective R) (right_injective R)
def ofBase : Base R →* Host R := IdentifyingHNN.of _ _ _ _
def embedding : R.Group →* Host R := (ofBase R).comp Coprod.inl
theorem embedding_injective : Function.Injective (embedding R) :=
  (IdentifyingHNN.of_injective _ _ _ _).comp Coprod.inl_injective
def x : Host R := ofBase R (a R)
def y : Host R := ofBase R (b R)
def t : Host R := IdentifyingHNN.stable _ _ _ _

theorem conjugates_zero : (t R)⁻¹ * x R * t R = y R := by
  have h := IdentifyingHNN.conjugates (left R) (right R) (left_injective R) (right_injective R)
      (FreeGroup.of 0)
  change (t R)⁻¹ * ofBase R (left R (FreeGroup.of 0)) * t R =
    ofBase R (right R (FreeGroup.of 0)) at h
  have hl : left R (FreeGroup.of 0)=a R := by simp [left,EffectiveEmbeddingFree.conjugates,a]
  have hr : right R (FreeGroup.of 0)=b R := by simp [right]
  rw [hl,hr] at h
  exact h

theorem conjugates_succ (i : ℕ) :
    (t R)⁻¹ * ((y R ^ (i+1))⁻¹ * x R * y R ^ (i+1)) * t R =
      embedding R (PresentedGroup.of i) * (x R ^ (i+1))⁻¹ * y R * x R ^ (i+1) := by
  have h := IdentifyingHNN.conjugates (left R) (right R) (left_injective R) (right_injective R)
      (FreeGroup.of (i+1))
  change (t R)⁻¹ * ofBase R (left R (FreeGroup.of (i+1))) * t R =
    ofBase R (right R (FreeGroup.of (i+1))) at h
  have hl : left R (FreeGroup.of (i+1))=(b R ^ (i+1))⁻¹*a R*b R ^ (i+1) := by
    simp [left,EffectiveEmbeddingFree.conjugates,a,b]
  have hr : right R (FreeGroup.of (i+1))=g R i*(a R ^ (i+1))⁻¹*b R*a R ^ (i+1) := by
    simp [right]
  rw [hl,hr] at h
  simpa only [map_mul,map_inv,map_pow,x,y,embedding,MonoidHom.comp_apply,g] using h

def generators : FreeGroup (Fin 2) →* Host R := FreeGroup.lift ![x R,t R]
@[simp] theorem generators_zero : generators R (FreeGroup.of 0)=x R := by simp [generators]
@[simp] theorem generators_one : generators R (FreeGroup.of 1)=t R := by simp [generators]

theorem generators_surjective : Function.Surjective (generators R) := by
  let S := (generators R).range
  have hx : x R∈S := ⟨FreeGroup.of 0,generators_zero R⟩
  have ht : t R∈S := ⟨FreeGroup.of 1,generators_one R⟩
  have hy : y R∈S := by
    rw [←conjugates_zero]
    exact S.mul_mem (S.mul_mem (S.inv_mem ht) hx) ht
  have hg (i : ℕ) : embedding R (PresentedGroup.of i)∈S := by
    have he : embedding R (PresentedGroup.of i) =
        (t R)⁻¹ * ((y R ^ (i+1))⁻¹ * x R * y R ^ (i+1)) * t R *
          (x R ^ (i+1))⁻¹ * (y R)⁻¹ * x R ^ (i+1) := by
      rw [conjugates_succ]
      group
    rw [he]
    exact S.mul_mem (S.mul_mem (S.mul_mem
      (S.mul_mem (S.mul_mem (S.inv_mem ht)
        (S.mul_mem (S.mul_mem (S.inv_mem (S.pow_mem hy _)) hx) (S.pow_mem hy _))) ht)
      (S.inv_mem (S.pow_mem hx _))) (S.inv_mem hy)) (S.pow_mem hx _)
  have hR (z : R.Group) : embedding R z∈S := by
    exact PresentedGroup.generated_by R.relSet (S.comap (embedding R)) hg z
  have hfree (z : FreeGroup (Fin 2)) : ofBase R (Coprod.inr z)∈S := by
    induction z using FreeGroup.induction_on with
    | one => simp
    | of i => fin_cases i <;> assumption
    | inv_of i hi => simpa only [map_inv] using S.inv_mem hi
    | mul z w hz hw => simpa only [map_mul] using S.mul_mem hz hw
  have hbase (z : Base R) : ofBase R z∈S := by
    induction z using Coprod.induction_on with
    | inl z => exact hR z
    | inr z => exact hfree z
    | mul z w hz hw => simpa only [map_mul] using S.mul_mem hz hw
  intro z
  change z∈S
  induction z using HNNExtension.induction_on with
  | of z => exact hbase z
  | t => simpa only [t,IdentifyingHNN.stable,inv_inv] using S.inv_mem ht
  | mul z w hz hw => exact S.mul_mem hz hw
  | inv z hz => exact S.inv_mem hz

end
end UniversalGroup.EffectiveEmbeddingHNN
