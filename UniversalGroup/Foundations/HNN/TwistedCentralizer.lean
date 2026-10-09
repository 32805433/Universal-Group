module

public import UniversalGroup.Foundations.HNN.Identifying
public import UniversalGroup.Foundations.HNN.NormalForms
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# A centralizer extension with a shifted stable letter

Replace the stable letter `q` by `T = P*q*P⁻¹*f`. The new attaching
subgroups are the conjugates of `C` by `P` and by `f⁻¹*P`. If `f`
centralizes `H`, the attaching isomorphism preserves membership in `H`.
Restricted HNN normal forms therefore control the subgroup `⟨H,T⟩`.
-/

namespace UniversalGroup.TwistedCentralizer
noncomputable section
open HNNLemmas
set_option maxHeartbeats 800000

variable {G : Type*} [Group G] (C : Subgroup G) (P f : G)

def left : C →* G := (MulAut.conj P).toMonoidHom.comp C.subtype
def right : C →* G := (MulAut.conj f⁻¹).toMonoidHom.comp (left C P)

theorem left_injective : Function.Injective (left C P) :=
  (MulAut.conj P).injective.comp Subtype.val_injective

theorem right_injective : Function.Injective (right C P f) :=
  (MulAut.conj f⁻¹).injective.comp (left_injective C P)

abbrev Model := IdentifyingHNN (left C P) (right C P f) (left_injective C P) (right_injective C P f)
def of : G →* Model C P f := IdentifyingHNN.of _ _ _ _
def stable : Model C P f := IdentifyingHNN.stable _ _ _ _

def target : CentralizerHNN G C :=
  centralizerOf C P * centralizerStable C * centralizerOf C (P⁻¹ * f)

@[simp] theorem left_apply (c : C) : left C P c = P * (c : G) * P⁻¹ := rfl
@[simp] theorem right_apply (c : C) : right C P f c = f⁻¹ * (P * (c : G) * P⁻¹) * f := by
  simp [right]

theorem target_relation (c : C) :
    (target C P f)⁻¹ * centralizerOf C (left C P c) * target C P f =
      centralizerOf C (right C P f c) := by
  have hc : (centralizerStable C)⁻¹ * centralizerOf C (c : G) * centralizerStable C =
      centralizerOf C (c : G) :=
    ((centralizerOf_commute_stable_iff C (c : G)).mpr c.property).symm.inv_mul_cancel
  have hh := congrArg (fun z => centralizerOf C (f⁻¹ * P) * z * centralizerOf C (P⁻¹ * f)) hc
  simpa [target, mul_assoc] using hh

def toAmbient : Model C P f →* CentralizerHNN G C :=
  IdentifyingHNN.lift _ _ _ _ (centralizerOf C) (target C P f) (target_relation C P f)

@[simp] theorem toAmbient_of (g : G) : toAmbient C P f (of C P f g) = centralizerOf C g :=
  IdentifyingHNN.lift_of _ _ _ _ _ _ _ g
@[simp] theorem toAmbient_stable : toAmbient C P f (stable C P f) = target C P f :=
  IdentifyingHNN.lift_stable _ _ _ _ _ _ _

def oldStable : Model C P f := of C P f P⁻¹ * stable C P f * of C P f (f⁻¹ * P)

theorem oldStable_commutes (c : C) : Commute (oldStable C P f) (of C P f (c : G)) := by
  have hh := IdentifyingHNN.conjugates (left C P) (right C P f)
    (left_injective C P) (right_injective C P f) c
  change (stable C P f)⁻¹ * of C P f (left C P c) * stable C P f = of C P f (right C P f c) at hh
  have h := congrArg (fun z => of C P f P⁻¹ * stable C P f * z * of C P f (f⁻¹ * P)) hh
  rw [commute_iff_eq]
  simpa [oldStable, mul_assoc] using h.symm

def fromAmbient : CentralizerHNN G C →* Model C P f :=
  HNNExtension.lift (of C P f) (oldStable C P f) (fun c => (oldStable_commutes C P f c).eq)

@[simp] theorem fromAmbient_of (g : G) : fromAmbient C P f (centralizerOf C g) = of C P f g := by
  exact HNNExtension.lift_of _ _ _ g
@[simp] theorem fromAmbient_stable : fromAmbient C P f (centralizerStable C) = oldStable C P f := by
  exact HNNExtension.lift_t _ _ _

@[simp] theorem fromAmbient_target : fromAmbient C P f (target C P f) = stable C P f := by
  simp [target, oldStable, mul_assoc]

/-- The shifted-stable presentation and the original centralizer extension
are isomorphic, with the base fixed. -/
def equiv : Model C P f ≃* CentralizerHNN G C where
  toFun := toAmbient C P f
  invFun := fromAmbient C P f
  map_mul' := map_mul _
  left_inv z := by
    have h : (fromAmbient C P f).comp (toAmbient C P f) = MonoidHom.id _ := by
      apply IdentifyingHNN.hom_ext
      · intro g
        exact fromAmbient_of C P f g
      · change fromAmbient C P f (toAmbient C P f (stable C P f)) = stable C P f
        rw [toAmbient_stable, fromAmbient_target]
    exact DFunLike.congr_fun h z
  right_inv z := by
    have h : (toAmbient C P f).comp (fromAmbient C P f) = MonoidHom.id _ := by
      apply HNNExtension.hom_ext
      · ext g
        change toAmbient C P f (fromAmbient C P f (centralizerOf C g)) = centralizerOf C g
        rw [fromAmbient_of, toAmbient_of]
      · simp [fromAmbient, oldStable, target, of, stable, toAmbient,
          IdentifyingHNN.lift, IdentifyingHNN.stable, IdentifyingHNN.of,
          centralizerOf, centralizerStable, mul_assoc]
    exact DFunLike.congr_fun h z

@[simp] theorem equiv_of (g : G) : equiv C P f (of C P f g) = centralizerOf C g := toAmbient_of C P f g
@[simp] theorem equiv_stable : equiv C P f (stable C P f) = target C P f := toAmbient_stable C P f
@[simp] theorem equiv_symm_of (g : G) : (equiv C P f).symm (centralizerOf C g) = of C P f g := fromAmbient_of C P f g
@[simp] theorem equiv_symm_target : (equiv C P f).symm (target C P f) = stable C P f := fromAmbient_target C P f

@[simp] theorem toAmbient_t :
    toAmbient C P f (HNNExtension.t : Model C P f) = (target C P f)⁻¹ := by
  simpa [stable, IdentifyingHNN.stable] using congrArg Inv.inv (toAmbient_stable C P f)

@[simp] theorem toAmbient_comp_of : (toAmbient C P f).comp (of C P f) = centralizerOf C := by
  ext g
  exact toAmbient_of C P f g

variable (H : Subgroup G) (hf : ∀ a ∈ H, Commute f a)

include hf in
theorem membership_iff (c : C) : left C P c ∈ H ↔ right C P f c ∈ H := by
  have hright : right C P f c = f⁻¹ * left C P c * f := by simp
  constructor
  · intro hc
    rw [hright, (hf _ hc).inv_mul_cancel]
    exact hc
  · intro hc
    have hh := (hf _ hc).mul_inv_cancel
    rw [hright] at hh
    have heq : left C P c = right C P f c := by simpa [mul_assoc] using hh
    exact heq ▸ hc

include hf in
theorem preserves_H (a : (left C P).range) :
    (a : G) ∈ H ↔
      ((UniversalGroup.rangeEquiv (left C P) (right C P f) (left_injective C P)
        (right_injective C P f) a : (right C P f).range) : G) ∈ H := by
  rcases a with ⟨_,c,rfl⟩
  rw [UniversalGroup.rangeEquiv_apply_range]
  exact membership_iff C P f H hf c

/-- The subgroup whose original generators are `H` and `P*q*P⁻¹*f`. -/
def subgroup : Subgroup (CentralizerHNN G C) :=
  generatedWith (H.map (centralizerOf C)) (target C P f)

/-- The same subgroup in the shifted-stable presentation. -/
def rebasedSubgroup : Subgroup (Model C P f) :=
  generatedWithStable (phi := UniversalGroup.rangeEquiv (left C P) (right C P f)
    (left_injective C P) (right_injective C P f)) H

theorem map_rebasedSubgroup : (rebasedSubgroup C P f H).map (toAmbient C P f) = subgroup C P f H := by
  unfold rebasedSubgroup generatedWithStable subgroup generatedWith
  rw [Subgroup.closure_union, Subgroup.closure_union,
    Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.map_sup, Subgroup.map_map]
  change H.map ((toAmbient C P f).comp (of C P f)) ⊔ _ = _
  rw [toAmbient_comp_of, MonoidHom.map_closure, Set.image_singleton, toAmbient_t,
    Subgroup.closure_singleton_inv]

theorem map_base : (of C P f).range.map (toAmbient C P f) = (centralizerOf C).range := by
  rw [← MonoidHom.range_comp, toAmbient_comp_of]

include hf in
/-- The subgroup generated by `H` and the twisted stable letter meets
the original base group exactly in `H`. -/
theorem subgroup_inf_base : subgroup C P f H ⊓ (centralizerOf C).range = H.map (centralizerOf C) := by
  have hh := generatedWithStable_inf_base H (preserves_H C P f H hf)
  change rebasedSubgroup C P f H ⊓ (of C P f).range = H.map (of C P f) at hh
  have h := congrArg (fun S : Subgroup (Model C P f) => S.map (toAmbient C P f)) hh
  rw [Subgroup.map_inf _ _ _ (equiv C P f).injective, map_rebasedSubgroup,
    map_base, Subgroup.map_map, toAmbient_comp_of] at h
  exact h

include hf in
/-- A useful equivalent formulation of the exact base intersection. -/
theorem of_mem_subgroup_iff (g : G) : centralizerOf C g ∈ subgroup C P f H ↔ g ∈ H := by
  constructor
  · intro hg
    have hm : centralizerOf C g ∈ subgroup C P f H ⊓ (centralizerOf C).range := ⟨hg,g,rfl⟩
    rw [subgroup_inf_base C P f H hf] at hm
    rcases hm with ⟨x,hx,hxg⟩
    exact (HNNExtension.of_injective (MulEquiv.refl C) hxg) ▸ hx
  · intro hg
    exact Subgroup.subset_closure (Or.inl ⟨g,hg,rfl⟩)

include hf in
/-- Every element of `⟨H,T⟩` has a reduced word in the shifted-stable
presentation whose head and all base coefficients lie in `H`. The explicit
isomorphism `toAmbient` evaluates this word in the original centralizer HNN. -/
theorem exists_reducedWord {x : CentralizerHNN G C} (hx : x ∈ subgroup C P f H) :
    ∃ w : HNNExtension.NormalWord.ReducedWord G (left C P).range (right C P f).range,
      toAmbient C P f (w.prod (UniversalGroup.rangeEquiv (left C P) (right C P f)
        (left_injective C P) (right_injective C P f))) = x ∧
        w.head ∈ H ∧ ∀ p ∈ w.toList, p.2 ∈ H := by
  rw [← map_rebasedSubgroup] at hx
  rcases hx with ⟨y,hy,rfl⟩
  obtain ⟨w,hw,hhead,hcoeff⟩ := exists_reducedWord_of_mem_generatedWithStable
    H (preserves_H C P f H hf) hy
  exact ⟨w,congrArg (toAmbient C P f) hw,hhead,hcoeff⟩


end
end UniversalGroup.TwistedCentralizer
