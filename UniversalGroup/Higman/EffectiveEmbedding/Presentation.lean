module

public import UniversalGroup.Higman.EffectiveEmbedding.Words

@[expose] public section

/-! A presentation of the explicit countable HNN extension. -/
namespace UniversalGroup.EffectiveEmbeddingPresentation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Monoid EffectiveEmbeddingWords EffectiveEmbeddingHNN

def relations (R : RecursivePresentation ℕ) : Set RawWord :=
  {w | (∃ v ∈ R.relators,shiftWord v=w) ∨ ∃ i,hnnWord i=w}
def relSet (R : RecursivePresentation ℕ) : Set (FreeGroup ℕ) := FreeGroup.mk '' relations R
abbrev Presented (R : RecursivePresentation ℕ) := PresentedGroup (relSet R)

variable (R : RecursivePresentation ℕ)

def values : ℕ → Host R
  | 0 => x R
  | 1 => y R
  | 2 => t R
  | i+3 => embedding R (PresentedGroup.of i)

theorem eval_map {H K : Type*} [Group H] [Group K] (f : H →* K) (q : ℕ → H) (w : RawWord) :
    eval (fun i=>f (q i)) w=f (eval q w) := by
  induction w with
  | nil => simp
  | cons l w ih => cases l with | mk k s => cases s <;> simp [ih]

theorem eval_of {T : Set (FreeGroup ℕ)} (w : RawWord) :
    eval (PresentedGroup.of (rels:=T)) w=PresentedGroup.mk T (FreeGroup.mk w) := by
  have h : FreeGroup.lift (PresentedGroup.of (rels:=T))=PresentedGroup.mk T := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  exact DFunLike.congr_fun h _

theorem eval_relation (w : RawWord) (hw : w∈relations R) : eval (values R) w=1 := by
  rcases hw with ⟨v,hv,rfl⟩|⟨i,rfl⟩
  · rw [eval_shiftWord]
    change eval (fun i=>embedding R (PresentedGroup.of i)) v=1
    rw [eval_map,eval_of]
    have h : PresentedGroup.mk R.relSet (FreeGroup.mk v)=1 :=
      PresentedGroup.one_of_mem ⟨v,hv,rfl⟩
    rw [h,map_one]
  · cases i with
    | zero =>
      rw [eval_hnnWord_zero]
      change (t R)⁻¹*x R*t R*(y R)⁻¹=1
      rw [conjugates_zero,mul_inv_cancel]
    | succ i =>
      rw [eval_hnnWord_succ]
      change (t R)⁻¹*((y R^(i+1))⁻¹*x R*y R^(i+1))*t R*
        (embedding R (PresentedGroup.of i)*(x R^(i+1))⁻¹*y R*x R^(i+1))⁻¹=1
      rw [conjugates_succ,mul_inv_cancel]

def toHost : Presented R →* Host R := PresentedGroup.toGroup (f := values R) (fun r hr=>by
  obtain ⟨w,hw,rfl⟩:=hr
  exact eval_relation R w hw)

@[simp] theorem toHost_of (i : ℕ) : toHost R (PresentedGroup.of i)=values R i := by
  simp [toHost]

theorem of_relation (w : RawWord) (hw : w∈relations R) :
    eval (PresentedGroup.of (rels:=relSet R)) w=1 := by
  rw [eval_of]
  exact PresentedGroup.one_of_mem ⟨w,hw,rfl⟩

def fromInput : R.Group →* Presented R := PresentedGroup.toGroup (f:=fun i=>PresentedGroup.of (i+3))
  (fun r hr=>by
    obtain ⟨w,hw,rfl⟩:=hr
    change eval (fun i=>PresentedGroup.of (rels:=relSet R) (i+3)) w=1
    rw [←eval_shiftWord]
    exact of_relation R (shiftWord w) (Or.inl ⟨w,hw,rfl⟩))

@[simp] theorem fromInput_of (i : ℕ) : fromInput R (PresentedGroup.of i)=PresentedGroup.of (i+3) := by
  simp [fromInput]

def fromBase : Base R →* Presented R := Coprod.lift (fromInput R)
  (FreeGroup.lift ![PresentedGroup.of 1,PresentedGroup.of 0])

@[simp] theorem fromBase_a : fromBase R (a R)=PresentedGroup.of 0 := by simp [fromBase,a]
@[simp] theorem fromBase_b : fromBase R (b R)=PresentedGroup.of 1 := by simp [fromBase,b]
@[simp] theorem fromBase_g (i : ℕ) : fromBase R (g R i)=PresentedGroup.of (i+3) := by simp [fromBase,g]

theorem conjugation_generator (i : ℕ) :
    (PresentedGroup.of (rels:=relSet R) 2)⁻¹*fromBase R (left R (FreeGroup.of i))*
      PresentedGroup.of 2=fromBase R (right R (FreeGroup.of i)) := by
  have h := of_relation R (hnnWord i) (Or.inr ⟨i,rfl⟩)
  cases i with
  | zero =>
    rw [eval_hnnWord_zero] at h
    have he := eq_of_mul_inv_eq_one h
    simpa [left,right,EffectiveEmbeddingFree.conjugates,fromBase,a,b] using he
  | succ i =>
    rw [eval_hnnWord_succ] at h
    have he := eq_of_mul_inv_eq_one h
    simpa [left,right,EffectiveEmbeddingFree.conjugates,fromBase,a,b,g] using he

theorem conjugation (z : FreeGroup ℕ) :
    (PresentedGroup.of (rels:=relSet R) 2)⁻¹*fromBase R (left R z)*
      PresentedGroup.of 2=fromBase R (right R z) := by
  induction z using FreeGroup.induction_on with
  | one => simp
  | of i => exact conjugation_generator R i
  | inv_of i hi =>
    simp only [map_inv]
    rw [←hi]
    group
  | mul z w hz hw =>
    simp only [map_mul]
    rw [←hz,←hw]
    group

def fromHost : Host R →* Presented R := IdentifyingHNN.lift _ _ _ _ (fromBase R)
  (PresentedGroup.of 2) (conjugation R)

@[simp] theorem fromHost_ofBase (z : Base R) : fromHost R (ofBase R z)=fromBase R z :=
  IdentifyingHNN.lift_of _ _ _ _ _ _ _ z
@[simp] theorem fromHost_t : fromHost R (t R)=PresentedGroup.of 2 :=
  IdentifyingHNN.lift_stable _ _ _ _ _ _ _

theorem toHost_fromInput : (toHost R).comp (fromInput R)=embedding R := by
  apply PresentedGroup.ext
  intro i
  simp [values]

theorem toHost_fromBase : (toHost R).comp (fromBase R)=ofBase R := by
  apply Coprod.hom_ext
  · exact toHost_fromInput R
  · apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [fromBase,values,x,y,a,b]

theorem toHost_fromHost : (toHost R).comp (fromHost R)=MonoidHom.id (Host R) := by
  apply IdentifyingHNN.hom_ext
  · intro z
    change toHost R (fromHost R (ofBase R z))=ofBase R z
    rw [fromHost_ofBase]
    exact DFunLike.congr_fun (toHost_fromBase R) z
  · change toHost R (fromHost R (t R))=t R
    rw [fromHost_t,toHost_of]
    rfl

theorem fromHost_toHost : (fromHost R).comp (toHost R)=MonoidHom.id (Presented R) := by
  apply PresentedGroup.ext
  intro i
  change fromHost R (toHost R (PresentedGroup.of i))=PresentedGroup.of i
  rw [toHost_of]
  match i with
  | 0 => exact fromHost_ofBase R (a R) |>.trans (fromBase_a R)
  | 1 => exact fromHost_ofBase R (b R) |>.trans (fromBase_b R)
  | 2 => exact fromHost_t R
  | i+3 =>
    change fromHost R (ofBase R (g R i))=PresentedGroup.of (i+3)
    rw [fromHost_ofBase,fromBase_g]

def equiv : Presented R ≃* Host R :=
  { toHost R with
    invFun := fromHost R
    left_inv := fun z=>DFunLike.congr_fun (fromHost_toHost R) z
    right_inv := fun z=>DFunLike.congr_fun (toHost_fromHost R) z }

end
end UniversalGroup.EffectiveEmbeddingPresentation
