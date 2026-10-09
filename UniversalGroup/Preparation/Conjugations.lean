module

public import UniversalGroup.Preparation.Cyclic
public import UniversalGroup.Foundations.FinitePresentation.Extensions

@[expose] public section

/-! Finite simultaneous conjugations between cyclic subgroups of order four. -/
namespace UniversalGroup.PreparationConjugations
noncomputable section
open Monoid PreparationCyclic
set_option maxHeartbeats 1200000

variable {G : Type*} [Group G] {n : ℕ}
abbrev Raw (G : Type*) [Group G] (n : ℕ) := Coprod G (FreeGroup (Fin n))
def relation (u : G) (v : Fin n → G) (i : Fin n) : Raw G n :=
  (Coprod.inr (FreeGroup.of i))⁻¹ * Coprod.inl u * Coprod.inr (FreeGroup.of i) *
    (Coprod.inl (v i))⁻¹
abbrev relations (u : G) (v : Fin n → G) : Subgroup (Raw G n) :=
  Subgroup.normalClosure (Set.range (relation u v))
abbrev Stage (u : G) (v : Fin n → G) := Raw G n ⧸ relations u v
def quotient (u : G) (v : Fin n → G) : Raw G n →* Stage u v :=
  QuotientGroup.mk' (relations u v)
def of (u : G) (v : Fin n → G) : G →* Stage u v :=
  (quotient u v).comp Coprod.inl
def stableFree (u : G) (v : Fin n → G) : FreeGroup (Fin n) →* Stage u v :=
  (quotient u v).comp Coprod.inr
def stable (u : G) (v : Fin n → G) (i : Fin n) : Stage u v :=
  stableFree u v (FreeGroup.of i)

theorem conjugates (u : G) (v : Fin n → G) (i : Fin n) :
    (stable u v i)⁻¹ * of u v u * stable u v i = of u v (v i) := by
  have h : quotient u v (relation u v i)=1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i,rfl⟩)
  change (stable u v i)⁻¹ * of u v u * stable u v i * (of u v (v i))⁻¹=1 at h
  exact mul_inv_eq_one.mp h

variable {H : Type*} [Group H]
def lift (u : G) (v : Fin n → G) (f : G →* H) (t : Fin n → H)
    (ht : ∀ i, (t i)⁻¹*f u*t i=f (v i)) : Stage u v →* H :=
  QuotientGroup.lift (relations u v) (Coprod.lift f (FreeGroup.lift t)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,rfl⟩
    change (Coprod.lift f (FreeGroup.lift t)) (relation u v i)=1
    simp [relation,ht])

@[simp] theorem lift_of (u : G) (v : Fin n → G) (f : G →* H) (t : Fin n → H)
    (ht : ∀ i, (t i)⁻¹*f u*t i=f (v i)) (g : G) :
    lift u v f t ht (of u v g)=f g := by simp [lift,of,quotient]
@[simp] theorem lift_stable (u : G) (v : Fin n → G) (f : G →* H) (t : Fin n → H)
    (ht : ∀ i, (t i)⁻¹*f u*t i=f (v i)) (i : Fin n) :
    lift u v f t ht (stable u v i)=t i := by simp [lift,stable,stableFree,quotient]

def retractFree (u : G) (v : Fin n → G) : Stage u v →* FreeGroup (Fin n) :=
  lift u v 1 FreeGroup.of (by intro i;simp)
@[simp] theorem retractFree_stable (u : G) (v : Fin n → G) (i : Fin n) :
    retractFree u v (stable u v i)=FreeGroup.of i := by simp [retractFree]
theorem stableFree_injective (u : G) (v : Fin n → G) :
    Function.Injective (stableFree u v) := by
  have h : (retractFree u v).comp (stableFree u v)=MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    exact retractFree_stable u v i
  intro x y hxy
  have hh:=congrArg (retractFree u v) hxy
  simpa only [←MonoidHom.comp_apply,h,MonoidHom.id_apply] using hh

def projection (u : G) (v : Fin n → G) (rho : G →* C4)
    (hu : rho u=generator) (hv : ∀ i, rho (v i)=generator) : Stage u v →* C4 :=
  lift u v rho (fun _=>1) (by intro i;simp [hu,hv])
@[simp] theorem projection_of (u : G) (v : Fin n → G) (rho : G →* C4)
    (hu : rho u=generator) (hv : ∀ i, rho (v i)=generator) (g : G) :
    projection u v rho hu hv (of u v g)=rho g := by simp [projection]
@[simp] theorem projection_stable (u : G) (v : Fin n → G) (rho : G →* C4)
    (hu : rho u=generator) (hv : ∀ i, rho (v i)=generator) (i : Fin n) :
    projection u v rho hu hv (stable u v i)=1 := by simp [projection]

theorem finitelyPresented [Group.IsFinitelyPresented G] (u : G) (v : Fin n → G) :
    Group.IsFinitelyPresented (Stage u v) :=
  Group.IsFinitelyPresented.quotient (relations u v)
    ⟨Set.range (relation u v),Set.finite_range _,rfl⟩

/-- Successively applying the HNN embedding theorem preserves the original
base group in the finite simultaneous presentation. -/
theorem of_injective (u : G) (v : Fin n → G) (hu : u^4=1)
    (hv : ∀ i, v i ^4=1) (rho : G →* C4)
    (hru : rho u=generator) (hrv : ∀ i, rho (v i)=generator) :
    Function.Injective (of u v) := by
  induction n with
  | zero =>
      let F := lift u v (MonoidHom.id G) Fin.elim0 (by intro i;exact Fin.elim0 i)
      intro x y hxy
      have h:=congrArg F hxy
      simpa only [F,lift_of,MonoidHom.id_apply] using h
  | succ n ih =>
      let w : Fin n → G := fun i=>v i.castSucc
      let o := of u w
      let pr := projection u w rho hru (fun i=>hrv i.castSucc)
      have ho : Function.Injective o := ih w (fun i=>hv i.castSucc)
        (fun i=>hrv i.castSucc)
      have hu' : o u ^4=1 := by rw [←map_pow,hu,map_one]
      have hv' : o (v (Fin.last n)) ^4=1 := by rw [←map_pow,hv,map_one]
      let l : C4 →* Stage u w := PreparationCyclic.hom (o u) hu'
      let r : C4 →* Stage u w := PreparationCyclic.hom (o (v (Fin.last n))) hv'
      have hl : Function.Injective l := PreparationCyclic.hom_injective _ _ pr
        (by simpa [pr,o] using hru)
      have hr : Function.Injective r := PreparationCyclic.hom_injective _ _ pr
        (by simpa [pr,o] using hrv (Fin.last n))
      let J := IdentifyingHNN l r hl hr
      let j : Stage u w →* J := IdentifyingHNN.of l r hl hr
      let a : J := IdentifyingHNN.stable l r hl hr
      let ts : Fin (n+1) → J := Fin.lastCases a (fun i=>j (stable u w i))
      have ht (i : Fin (n+1)) : (ts i)⁻¹*(j.comp o) u*ts i=(j.comp o) (v i) := by
        refine Fin.lastCases ?_ (fun k=>?_) i
        · have h:=IdentifyingHNN.conjugates l r hl hr generator
          simpa [ts,a,j,l,r,MonoidHom.comp_apply] using h
        · have h:=congrArg j (conjugates u w k)
          simpa [ts,MonoidHom.comp_apply,w,o] using h
      let F : Stage u v →* J := lift u v (j.comp o) ts ht
      intro x y hxy
      apply ho
      apply IdentifyingHNN.of_injective l r hl hr
      have h:=congrArg F hxy
      simpa only [F,lift_of,MonoidHom.comp_apply] using h

/-- The common cyclic generator and the stable letters generate the extension
when the conjugate cyclic generators generate the base. -/
theorem generate (u : G) (v : Fin n → G)
    (hv : Subgroup.closure (Set.range v)=⊤) :
    Subgroup.closure ({of u v u} ∪ Set.range (stable u v))=⊤ := by
  let S := Subgroup.closure ({of u v u} ∪ Set.range (stable u v))
  have hu : of u v u∈S := Subgroup.subset_closure (Or.inl (Set.mem_singleton _))
  have ht (i : Fin n) : stable u v i∈S := Subgroup.subset_closure (Or.inr ⟨i,rfl⟩)
  have hbase (g : G) : of u v g∈S := by
    have hle : Subgroup.closure (Set.range v) ≤ S.comap (of u v) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      change of u v (v i)∈S
      rw [←conjugates]
      exact S.mul_mem (S.mul_mem (S.inv_mem (ht i)) hu) (ht i)
    rw [hv] at hle
    exact hle (Subgroup.mem_top _)
  have hfree (w : FreeGroup (Fin n)) : stableFree u v w∈S := by
    induction w using FreeGroup.induction_on with
    | one => simpa only [map_one] using S.one_mem
    | of i => exact ht i
    | inv_of i hi =>
        rw [map_inv]
        exact S.inv_mem hi
    | mul x y hx hy =>
        rw [map_mul]
        exact S.mul_mem hx hy
  apply top_unique
  intro x hx
  change x∈S
  clear hx
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (relations u v) x
  induction w using Coprod.induction_on with
  | inl g => exact hbase g
  | inr w => exact hfree w
  | mul x y hx hy =>
      change quotient u v (x*y)∈S
      rw [map_mul]
      exact S.mul_mem hx hy

@[simp] theorem projection_comp_stableFree (u : G) (v : Fin n → G) (rho : G →* C4)
    (hu : rho u=generator) (hv : ∀ i, rho (v i)=generator) :
    (projection u v rho hu hv).comp (stableFree u v)=1 := by
  apply FreeGroup.ext_hom
  intro i
  exact projection_stable u v rho hu hv i

end
end UniversalGroup.PreparationConjugations
