module

public import UniversalGroup.Foundations.FinitePresentation.Extensions
public import Mathlib.GroupTheory.NoncommCoprod

@[expose] public section

/-!
# Finite presentation of direct products

A finite generating set of each factor supplies finitely many mixed
commutator relations.  These generate the kernel of the free-product map.
-/

namespace UniversalGroup.PreparationFinite

open Monoid
open scoped commutatorElement

private theorem commute_of_generators {G H K : Type*} [Group G] [Group H] [Group K]
    (l : G →* K) (r : H →* K) {S : Set G} {T : Set H}
    (hS : Subgroup.closure S = ⊤) (hT : Subgroup.closure T = ⊤)
    (hc : ∀ g ∈ S, ∀ h ∈ T, Commute (l g) (r h)) :
    ∀ g h, Commute (l g) (r h) := by
  have hfirst (g : G) (hg : g ∈ S) (h : H) : Commute (l g) (r h) := by
    have hh : h ∈ Subgroup.closure T := by rw [hT]; trivial
    induction hh using Subgroup.closure_induction with
    | mem x hx => exact hc g hg x hx
    | one => simp
    | mul x y hx hy ihx ihy => simpa using ihx.mul_right ihy
    | inv x hx ih => simpa using ih.inv_right
  intro g h
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hfirst x hx h
  | one => simp
  | mul x y hx hy ihx ihy => simpa using ihx.mul_left ihy
  | inv x hx ih => simpa using ih.inv_left

/-- A direct product of finitely presented groups is finitely presented. -/
theorem prod (G H : Type*) [Group G] [Group H]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  obtain ⟨ng, πg, hπg, hkg⟩ := (inferInstance : Group.IsFinitelyPresented G).out
  obtain ⟨nh, πh, hπh, hkh⟩ := (inferInstance : Group.IsFinitelyPresented H).out
  let : Group.FG G := Group.fg_of_surjective hπg
  let : Group.FG H := Group.fg_of_surjective hπh
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let P := Monoid.Coprod G H
  let rel : G × H → P := fun a => ⁅(Coprod.inl a.1 : P), (Coprod.inr a.2 : P)⁆
  let R : Set P := rel '' (S ×ˢ T)
  let N : Subgroup P := Subgroup.normalClosure R
  let q : P →* P ⧸ N := QuotientGroup.mk' N
  let f : P →* G × H := Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)
  have fl (g : G) : f (Coprod.inl g) = (g, 1) := Coprod.lift_apply_inl _ _ _
  have fr (h : H) : f (Coprod.inr h) = (1, h) := Coprod.lift_apply_inr _ _ _
  have hf : Function.Surjective f := by
    rintro ⟨g, h⟩
    exact ⟨Coprod.inl g * Coprod.inr h,
      (map_mul f _ _).trans ((congrArg₂ (· * ·) (fl g) (fr h)).trans (by simp))⟩
  have hNf : N ≤ f.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨⟨g, h⟩, hgh, rfl⟩
    change f (rel (g, h)) = 1
    change f ⁅(Coprod.inl g : P), (Coprod.inr h : P)⁆ = 1
    have he : ⁅f (Coprod.inl g), f (Coprod.inr h)⁆ = ⁅(g, (1 : H)), ((1 : G), h)⁆ :=
      congrArg₂ (fun x y : G × H => ⁅x, y⁆) (fl g) (fr h)
    have hc : ⁅(g, (1 : H)), ((1 : G), h)⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (MonoidHom.commute_inl_inr g h)
    exact (map_commutatorElement f _ _).trans (he.trans hc)
  let l : G →* P ⧸ N := q.comp Coprod.inl
  let r : H →* P ⧸ N := q.comp Coprod.inr
  have hc : ∀ g h, Commute (l g) (r h) := by
    apply commute_of_generators l r hS hT
    intro g hg h hh
    have hm : rel (g, h) ∈ N := Subgroup.subset_normalClosure ⟨(g, h), ⟨hg, hh⟩, rfl⟩
    have hq : q (rel (g, h)) = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [rel, map_commutatorElement, l, r] using hq
  let F : G × H →* P ⧸ N := l.noncommCoprod r hc
  have hF : F.comp f = q := by
    apply Coprod.hom_ext
    · ext g
      change F (f (Coprod.inl g)) = q (Coprod.inl g)
      rw [fl]
      simp [F, l, r]
    · ext h
      change F (f (Coprod.inr h)) = q (Coprod.inr h)
      rw [fr]
      simp [F, l, r]
  have hfN : f.ker ≤ N := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change q x = 1
    rw [← DFunLike.congr_fun hF]
    change F (f x) = 1
    rw [show f x = 1 from hx, map_one]
  exact Group.IsFinitelyPresented.of_surjective f hf
    ⟨R, (hSfin.prod hTfin).image rel, le_antisymm hNf hfN⟩

end UniversalGroup.PreparationFinite
