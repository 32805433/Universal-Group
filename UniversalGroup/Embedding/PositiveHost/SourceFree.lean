module

public import UniversalGroup.Foundations.HNN.CentralizerMap
public import UniversalGroup.Preparation.FreeProduct

@[expose] public section

/-! A free triple in the centralizer HNN `⟨f,h,k | [k, f fʰ]⟩`.
The two-state action proves the needed part of the index-two Schreier calculation. -/
namespace UniversalGroup.Embedding.PositiveHost.SourceFree

open HNNLemmas
noncomputable section

abbrev Pair := FreeGroup (Fin 2)
abbrev Triple := FreeGroup (Fin 3)
def f : Pair := FreeGroup.of 0
def h : Pair := FreeGroup.of 1
def fh : Pair := h⁻¹ * f * h

def schreier : Triple →* Pair := FreeGroup.lift ![f, fh, h ^ 2]

abbrev State := Bool × Triple

def write : Equiv.Perm State where
  toFun z := (z.1, FreeGroup.of (if z.1 then 1 else 0) * z.2)
  invFun z := (z.1, (FreeGroup.of (if z.1 then 1 else 0))⁻¹ * z.2)
  left_inv := by intro ⟨i,w⟩; simp
  right_inv := by intro ⟨i,w⟩; simp

def shift : Equiv.Perm State where
  toFun z := if z.1 then (false, FreeGroup.of 2 * z.2) else (true,z.2)
  invFun z := if z.1 then (false,z.2) else (true,(FreeGroup.of 2)⁻¹ * z.2)
  left_inv := by intro ⟨i,w⟩; cases i <;> simp
  right_inv := by intro ⟨i,w⟩; cases i <;> simp

def representation : Pair →* Equiv.Perm State := FreeGroup.lift ![write,shift]

def ActsAs (p : Equiv.Perm State) (x : Triple) : Prop :=
  ∀ w, p (false,w) = (false,x*w)

theorem actsAs_one : ActsAs 1 1 := by intro w; simp

theorem ActsAs.mul {p q : Equiv.Perm State} {x y : Triple}
    (hp : ActsAs p x) (hq : ActsAs q y) : ActsAs (p*q) (x*y) := by
  intro w
  rw [Equiv.Perm.mul_apply,hq,hp,mul_assoc]

theorem ActsAs.inv {p : Equiv.Perm State} {x : Triple}
    (hp : ActsAs p x) : ActsAs p⁻¹ x⁻¹ := by
  intro w
  apply p.injective
  rw [hp]
  simp

theorem schreier_action (g : Triple) : ActsAs (representation (schreier g)) g := by
  induction g using FreeGroup.induction_on with
  | one => simpa only [map_one] using actsAs_one
  | of i =>
      intro w
      fin_cases i <;>
        simp [schreier,representation,f,fh,h,write,shift,pow_succ,Equiv.Perm.mul_apply]
  | inv_of i hi => simpa only [map_inv] using hi.inv
  | mul g k hg hk => simpa only [map_mul] using hg.mul hk

theorem schreier_injective : Function.Injective schreier := by
  intro u v huv
  have he := congrArg (fun g => representation g (false,1)) huv
  rw [schreier_action,schreier_action] at he
  simpa using he

/-- The free factor on the first and third Schreier generators. -/
def pairInTriple : Pair →* Triple := FreeGroup.lift ![FreeGroup.of 0,FreeGroup.of 2]
def pairRetract : Triple →* Pair := FreeGroup.lift ![FreeGroup.of 0,1,FreeGroup.of 1]

theorem pairInTriple_injective : Function.Injective pairInTriple := by
  have he : pairRetract.comp pairInTriple = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [pairRetract,pairInTriple]
  exact Function.LeftInverse.injective (fun x => DFunLike.congr_fun he x)

def evenPair : Pair →* Pair := schreier.comp pairInTriple

theorem evenPair_injective : Function.Injective evenPair :=
  schreier_injective.comp pairInTriple_injective

@[simp] theorem evenPair_of (i : Fin 2) :
    evenPair (FreeGroup.of i) = ![f,h^2] i := by
  fin_cases i <;> simp [evenPair,pairInTriple,schreier]

def exponent : Triple →* Multiplicative ℤ :=
  FreeGroup.lift ![1,Multiplicative.ofAdd 1,1]

theorem exponent_pairInTriple (x : Pair) : exponent (pairInTriple x) = 1 := by
  have he : exponent.comp pairInTriple = 1 := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [exponent,pairInTriple]
  exact DFunLike.congr_fun he x

/-- The pair `f,h²` meets the cyclic associated subgroup trivially. -/
theorem evenPair_mem (x : Pair) :
    x ∈ (⊥ : Subgroup Pair) ↔ evenPair x ∈ Subgroup.zpowers (f*fh) := by
  constructor
  · intro hx
    have hx' : x = 1 := hx
    simp [hx']
  · rintro ⟨n,hn⟩
    have he : schreier ((FreeGroup.of 0 * FreeGroup.of 1 : Triple)^n) =
        schreier (pairInTriple x) := by
      simpa [schreier,evenPair] using hn
    have ht := schreier_injective he
    have hn0 := congrArg exponent ht
    rw [exponent_pairInTriple] at hn0
    have hn' : n = 0 := by
      simpa [exponent] using hn0
    apply evenPair_injective
    simpa [hn'] using hn.symm

def associated : Subgroup Pair := Subgroup.zpowers (f*fh)
abbrev Model := CentralizerHNN Pair associated

def qf : Model := centralizerOf associated f
def qh : Model := centralizerOf associated h
def qk : Model := centralizerStable associated

/-- Restriction of the centralizer HNN along the pair `f,h²`. -/
def inclusion : CentralizerHNN Pair (⊥ : Subgroup Pair) →* Model :=
  CentralizerMap.hom ⊥ associated evenPair evenPair_mem

theorem inclusion_injective : Function.Injective inclusion :=
  CentralizerMap.hom_injective ⊥ associated evenPair evenPair_mem evenPair_injective

def freeTriple : Triple →* Model := FreeGroup.lift ![qf,qk,qh^2]

def emptyTriple : Triple →* CentralizerHNN Pair (⊥ : Subgroup Pair) :=
  FreeGroup.lift ![centralizerOf ⊥ f,centralizerStable (⊥ : Subgroup Pair),
    centralizerOf ⊥ h]

def emptyRetraction : CentralizerHNN Pair (⊥ : Subgroup Pair) →* Triple :=
  HNNExtension.lift pairInTriple (FreeGroup.of 1) (by
    intro a
    have ha : (a : Pair) = 1 := a.property
    simp [ha])

theorem emptyTriple_injective : Function.Injective emptyTriple := by
  have he : emptyRetraction.comp emptyTriple = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;>
      simp [emptyRetraction,emptyTriple,centralizerOf,centralizerStable,pairInTriple,f,h]
  exact Function.LeftInverse.injective (fun x => DFunLike.congr_fun he x)

theorem freeTriple_eq : freeTriple = inclusion.comp emptyTriple := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp [freeTriple,emptyTriple,inclusion,qf,qk,qh,CentralizerMap.hom,
      centralizerOf,centralizerStable,f,h]

theorem freeTriple_injective : Function.Injective freeTriple := by
  rw [freeTriple_eq]
  exact inclusion_injective.comp emptyTriple_injective

theorem commute_relation : Commute qk (qf * (qh⁻¹*qf*qh)) := by
  apply Commute.symm
  rw [show qf * (qh⁻¹*qf*qh) = centralizerOf associated (f*fh) by
    simp [qf,qh,fh]]
  exact (centralizerOf_commute_stable_iff associated _).mpr (Subgroup.mem_zpowers _)

end
end UniversalGroup.Embedding.PositiveHost.SourceFree
