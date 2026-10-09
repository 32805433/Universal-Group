module

public import UniversalGroup.Preparation.FreeProduct
public import UniversalGroup.Preparation.Cyclic
public import UniversalGroup.Foundations.FinitePresentation.Extensions

@[expose] public section

/-! The last Higman–Neumann–Neumann compression, with cyclic factors of order four. -/
namespace UniversalGroup.PreparationTwoGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Monoid PreparationFreeProduct

structure Input (P : Type) [Group P] (n : ℕ) where
  u : P
  fourthPower : u^4=1
  j : FreeGroup (Fin n) →* P
  injective : Function.Injective j
  rho : P →* Cyclic
  rho_u : rho u=generator
  rho_j : rho.comp j=1
  generates : Subgroup.closure ({u} ∪ Set.range (fun i => j (FreeGroup.of i)))=⊤

namespace Input

variable {P : Type} [Group P] {n : ℕ} (D : Input P n)

def Factor : Bool → Type | false => P | true => Pair
instance factorGroup (i : Bool) : Group (Factor (P:=P) i) := by
  cases i <;> dsimp [Factor] <;> infer_instance

def diagram : (i : Bool) → FreeGroup (Fin n) →* Factor (P:=P) i
  | false => D.j
  | true => freeFamily n

theorem diagram_injective (i : Bool) : Function.Injective (D.diagram i) := by
  cases i
  · exact D.injective
  · exact freeFamily_injective n

abbrev Amalgam := PushoutI D.diagram
def inP : P →* D.Amalgam := PushoutI.of (φ:=D.diagram) false
def inPair : Pair →* D.Amalgam := PushoutI.of (φ:=D.diagram) true

theorem inP_injective : Function.Injective D.inP := PushoutI.of_injective D.diagram_injective false
theorem inPair_injective : Function.Injective D.inPair := PushoutI.of_injective D.diagram_injective true

theorem identifies (g : FreeGroup (Fin n)) : D.inP (D.j g)=D.inPair (freeFamily n g) :=
  (PushoutI.of_apply_eq_base D.diagram false g).trans
    (PushoutI.of_apply_eq_base D.diagram true g).symm

def pairMaps : (i : Bool) → Factor (P:=P) i →* Pair
  | false => Coprod.inl.comp D.rho
  | true => Coprod.inr.comp projection

def toPair : D.Amalgam →* Pair := PushoutI.lift D.pairMaps 1 (by
  intro i
  cases i
  · change (Coprod.inl.comp D.rho).comp D.j=1
    rw [MonoidHom.comp_assoc,D.rho_j,MonoidHom.comp_one]
  · change (Coprod.inr.comp projection).comp (freeFamily n)=1
    rw [MonoidHom.comp_assoc,freeFamilyProjection,MonoidHom.comp_one])

@[simp] theorem toPair_inP (g : P) : D.toPair (D.inP g)=Coprod.inl (D.rho g) :=
  PushoutI.lift_of (φ:=D.diagram) _ _ _ (i:=false) g
@[simp] theorem toPair_inPair (g : Pair) : D.toPair (D.inPair g)=Coprod.inr (projection g) :=
  PushoutI.lift_of (φ:=D.diagram) _ _ _ (i:=true) g

def targetPair : Pair →* D.Amalgam := Coprod.lift
  (D.inP.comp (PreparationCyclic.hom D.u D.fourthPower))
  (D.inPair.comp Coprod.inl)

@[simp] theorem targetPair_b : D.targetPair b=D.inP D.u := by
  simp [targetPair,b,show generator=PreparationCyclic.generator from rfl]
@[simp] theorem targetPair_v : D.targetPair v=D.inPair b := by
  simp [targetPair,v,b]

theorem targetPair_injective : Function.Injective D.targetPair := by
  have h : D.toPair.comp D.targetPair=MonoidHom.id Pair := by
    apply Coprod.hom_ext
    · apply PreparationCyclic.hom_ext
      change D.toPair (D.targetPair b)=b
      rw [D.targetPair_b,D.toPair_inP,D.rho_u]
      rfl
    · apply PreparationCyclic.hom_ext
      change D.toPair (D.targetPair v)=v
      rw [D.targetPair_v,D.toPair_inPair]
      simp [projection,b,v]
  intro x y hxy
  have hh := congrArg D.toPair hxy
  simpa only [←MonoidHom.comp_apply,h,MonoidHom.id_apply] using hh

abbrev Host := IdentifyingHNN D.inPair D.targetPair D.inPair_injective D.targetPair_injective

def ofBase : D.Amalgam →* D.Host := IdentifyingHNN.of _ _ _ _
def embedding : P →* D.Host := D.ofBase.comp D.inP
def x : D.Host := D.ofBase (D.inPair b)
def t : D.Host := IdentifyingHNN.stable _ _ _ _

theorem embedding_injective : Function.Injective D.embedding :=
  (IdentifyingHNN.of_injective _ _ _ _).comp D.inP_injective

theorem x_fourthPower : D.x^4=1 := by
  change (D.ofBase (D.inPair b))^4=1
  rw [←map_pow,←map_pow]
  have hb : b^4=1 := by
    change (Coprod.inl generator : Pair)^4=1
    rw [←map_pow,show generator^4=1 by decide,map_one]
  rw [hb,map_one,map_one]

theorem conjugates_b : D.t⁻¹*D.x*D.t=D.embedding D.u := by
  simpa only [targetPair_b,t,x,embedding,ofBase,MonoidHom.comp_apply] using
    (IdentifyingHNN.conjugates D.inPair D.targetPair D.inPair_injective D.targetPair_injective b)

theorem conjugates_v : D.t⁻¹*D.ofBase (D.inPair v)*D.t=D.x := by
  simpa only [targetPair_v,t,x,ofBase] using
    (IdentifyingHNN.conjugates D.inPair D.targetPair D.inPair_injective D.targetPair_injective v)

def character : D.Host →* Multiplicative ℤ :=
  IdentifyingHNN.lift _ _ _ _ 1 (Multiplicative.ofAdd 1) (by intro a; simp)

@[simp] theorem character_x : D.character D.x=1 := by
  change IdentifyingHNN.lift _ _ _ _ _ _ _ (IdentifyingHNN.of _ _ _ _ _) = 1
  rw [IdentifyingHNN.lift_of]; rfl
@[simp] theorem character_t : D.character D.t=Multiplicative.ofAdd 1 :=
  IdentifyingHNN.lift_stable _ _ _ _ _ _ _

def generators : FreeGroup (Fin 2) →* D.Host := FreeGroup.lift ![D.x,D.t]

@[simp] theorem generators_zero : D.generators (FreeGroup.of 0)=D.x := by simp [generators]
@[simp] theorem generators_one : D.generators (FreeGroup.of 1)=D.t := by simp [generators]

theorem generators_surjective : Function.Surjective D.generators := by
  let S := D.generators.range
  have hx : D.x∈S := ⟨FreeGroup.of 0,D.generators_zero⟩
  have ht : D.t∈S := ⟨FreeGroup.of 1,D.generators_one⟩
  have hu : D.embedding D.u∈S := by
    rw [←D.conjugates_b]
    exact S.mul_mem (S.mul_mem (S.inv_mem ht) hx) ht
  have hv : D.ofBase (D.inPair v)∈S := by
    have heq : D.ofBase (D.inPair v)=D.t*D.x*D.t⁻¹ := by
      rw [←D.conjugates_v]
      group
    rw [heq]
    exact S.mul_mem (S.mul_mem ht hx) (S.inv_mem ht)
  have hp (g : Pair) : D.ofBase (D.inPair g)∈S := by
    induction g using Coprod.induction_on with
    | inl g =>
      rw [←PreparationCyclic.generator_pow_val g,map_pow,map_pow,map_pow]
      exact S.pow_mem hx _
    | inr g =>
      rw [←PreparationCyclic.generator_pow_val g,map_pow,map_pow,map_pow]
      exact S.pow_mem hv _
    | mul g h hg hh =>
      simpa only [map_mul] using S.mul_mem hg hh
  have hP (g : P) : D.embedding g∈S := by
    have hle : Subgroup.closure ({D.u} ∪ Set.range (fun i => D.j (FreeGroup.of i))) ≤
        S.comap D.embedding := by
      apply (Subgroup.closure_le _).mpr
      rintro g (hg|⟨i,rfl⟩)
      · have heq := Set.mem_singleton_iff.mp hg
        subst g
        exact hu
      · change D.ofBase (D.inP (D.j (FreeGroup.of i)))∈S
        rw [D.identifies]
        exact hp _
    rw [D.generates] at hle
    exact hle (Subgroup.mem_top g)
  have hbase (g : D.Amalgam) : D.ofBase g∈S := by
    induction g using PushoutI.induction_on with
    | of i g =>
      cases i
      · exact hP g
      · exact hp g
    | base a =>
      rw [←PushoutI.of_apply_eq_base D.diagram false a]
      exact hP _
    | mul g h hg hh =>
      simpa only [map_mul] using S.mul_mem hg hh
  intro g
  change g∈S
  induction g using HNNExtension.induction_on with
  | of g => exact hbase g
  | t =>
    have hi := S.inv_mem ht
    simpa only [t,IdentifyingHNN.stable,inv_inv] using hi
  | mul g h hg hh => exact S.mul_mem hg hh
  | inv g hg => exact S.inv_mem hg

instance [Group.IsFinitelyPresented P] : Group.IsFinitelyPresented D.Host := by
  have hP : Group.IsFinitelyPresented P := inferInstance
  have hpair : Group.IsFinitelyPresented Pair := inferInstance
  let hfac : (i : Bool) → Group.IsFinitelyPresented (Factor (P:=P) i) := fun i => by
    cases i
    · exact hP
    · exact hpair
  have : Group.IsFinitelyPresented D.Amalgam := PreparationFinite.pushoutBool _ D.diagram
  let : Group.FG Pair := by
    obtain ⟨k,f,hf,_⟩ := hpair
    exact Group.fg_of_surjective hf
  exact PreparationFinite.identifyingHNN _ _ _ _

end Input
end
end UniversalGroup.PreparationTwoGenerators
