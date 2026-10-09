module

public import UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.PushoutI

@[expose] public section

/-!
# Finite presentation of the HNN constructions used in preparation

Only one conjugation relation per generator of the associated subgroup is
needed.  The proof identifies the full kernel with the normal closure of
this finite set by the universal property of the HNN extension.
-/

namespace UniversalGroup.PreparationFinite

open Monoid

variable {G : Type*} [Group G]

/-- An HNN extension of a finitely presented group along finitely generated
associated subgroups is finitely presented. -/
theorem hnnExtension [Group.IsFinitelyPresented G]
    (A B : Subgroup G) [Group.FG A] (φ : A ≃* B) :
    Group.IsFinitelyPresented (HNNExtension G A B φ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG A)
  let P := Monoid.Coprod G (Multiplicative ℤ)
  let z : P := Coprod.inr (Multiplicative.ofAdd 1)
  let rel : A → P := fun a =>
    z * Coprod.inl (a : G) * z⁻¹ * (Coprod.inl (φ a : G))⁻¹
  let N : Subgroup P := Subgroup.normalClosure (rel '' S)
  let q : P →* P ⧸ N := QuotientGroup.mk' N
  let f : P →* HNNExtension G A B φ := (HNNExtension.con G A B φ).mk'
  have hNf : N ≤ f.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a, ha, rfl⟩
    change f (rel a) = 1
    change (HNNExtension.t * HNNExtension.of (a : G) * HNNExtension.t⁻¹ *
      (HNNExtension.of (φ a : G))⁻¹ : HNNExtension G A B φ) = 1
    rw [← HNNExtension.equiv_eq_conj]
    exact mul_inv_cancel _
  let l : A →* P ⧸ N :=
    { toFun := fun a => q z * q (Coprod.inl (a : G)) * (q z)⁻¹
      map_one' := by simp
      map_mul' := by intros; simp [mul_assoc] }
  let r : A →* P ⧸ N := q.comp (Coprod.inl.comp (B.subtype.comp φ.toMonoidHom))
  have hlr : l = r := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro a ha
    have hm : rel a ∈ N := Subgroup.subset_normalClosure ⟨a, ha, rfl⟩
    have hq : q (rel a) = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    change l a * (r a)⁻¹ = 1 at hq
    exact mul_inv_eq_one.mp hq
  have hconj (a : A) : q z * q (Coprod.inl (a : G)) =
      q (Coprod.inl (φ a : G)) * q z := by
    have h := DFunLike.congr_fun hlr a
    change q z * q (Coprod.inl (a : G)) * (q z)⁻¹ =
      q (Coprod.inl (φ a : G)) at h
    simpa [mul_assoc] using congrArg (fun x => x * q z) h
  let F : HNNExtension G A B φ →* P ⧸ N :=
    HNNExtension.lift (q.comp Coprod.inl) (q z) hconj
  have hF : F.comp f = q := by
    apply Coprod.hom_ext
    · ext g
      change F (HNNExtension.of g) = q (Coprod.inl g)
      exact HNNExtension.lift_of _ _ _ _
    · apply MonoidHom.ext_mint
      change F HNNExtension.t = q z
      exact HNNExtension.lift_t _ _ _
  have hfN : f.ker ≤ N := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change q x = 1
    rw [← DFunLike.congr_fun hF]
    change F (f x) = 1
    rw [show f x = 1 from hx, map_one]
  exact Group.IsFinitelyPresented.of_surjective f Con.mk'_surjective
    ⟨rel '' S, hSfin.image rel, le_antisymm hNf hfN⟩

/-- The same preservation theorem for HNN extensions specified by two
embeddings of a finitely generated parameter group. -/
theorem identifyingHNN {A : Type*} [Group A]
    [Group.IsFinitelyPresented G] [Group.FG A]
    (left right : A →* G)
    (hl : Function.Injective left) (hr : Function.Injective right) :
    Group.IsFinitelyPresented (IdentifyingHNN left right hl hr) :=
  hnnExtension left.range right.range (rangeEquiv left right hl hr)

set_option backward.isDefEq.respectTransparency false in
/-- A pushout of two finitely presented groups over a finitely generated
group is finitely presented.  This fact needs no injectivity hypothesis on
the two maps; it therefore applies in particular to amalgamated products. -/
theorem pushoutBool {A : Type*} [Group A] [Group.FG A]
    (G : Bool → Type*) [∀ i, Group (G i)] [∀ i, Group.IsFinitelyPresented (G i)]
    (φ : ∀ i, A →* G i) : Group.IsFinitelyPresented (Monoid.PushoutI φ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG A)
  let P := Monoid.Coprod (G false) (G true)
  let rel : A → P := fun a => Coprod.inl (φ false a) * (Coprod.inr (φ true a))⁻¹
  let N : Subgroup P := Subgroup.normalClosure (rel '' S)
  let q : P →* P ⧸ N := QuotientGroup.mk' N
  let f : P →* Monoid.PushoutI φ := Coprod.lift
    (Monoid.PushoutI.of false) (Monoid.PushoutI.of true)
  have hf : Function.Surjective f := by
    intro x
    induction x using Monoid.PushoutI.induction_on with
    | of i g =>
        cases i with
        | false => exact ⟨Coprod.inl g, Coprod.lift_apply_inl _ _ _⟩
        | true => exact ⟨Coprod.inr g, Coprod.lift_apply_inr _ _ _⟩
    | base a =>
        exact ⟨Coprod.inl (φ false a), (Coprod.lift_apply_inl _ _ _).trans
          (Monoid.PushoutI.of_apply_eq_base φ false a)⟩
    | mul x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' * y', map_mul f _ _⟩
  have hNf : N ≤ f.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a, ha, rfl⟩
    change f (rel a) = 1
    have hl : f (Coprod.inl (φ false a)) = Monoid.PushoutI.base φ a :=
      (Coprod.lift_apply_inl _ _ _).trans (Monoid.PushoutI.of_apply_eq_base φ false a)
    have hr : f (Coprod.inr (φ true a)) = Monoid.PushoutI.base φ a :=
      (Coprod.lift_apply_inr _ _ _).trans (Monoid.PushoutI.of_apply_eq_base φ true a)
    calc
      f (rel a) = f (Coprod.inl (φ false a)) * f ((Coprod.inr (φ true a))⁻¹) :=
        map_mul f _ _
      _ = Monoid.PushoutI.base φ a * (Monoid.PushoutI.base φ a)⁻¹ :=
        congrArg₂ (· * ·) hl ((map_inv f _).trans (congrArg Inv.inv hr))
      _ = 1 := mul_inv_cancel _
  let l : A →* P ⧸ N := q.comp (Coprod.inl.comp (φ false))
  let r : A →* P ⧸ N := q.comp (Coprod.inr.comp (φ true))
  have hlr : l = r := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro a ha
    have hm : rel a ∈ N := Subgroup.subset_normalClosure ⟨a, ha, rfl⟩
    have hq : q (rel a) = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    change l a * (r a)⁻¹ = 1 at hq
    exact mul_inv_eq_one.mp hq
  let maps : ∀ i, G i →* P ⧸ N := fun i => match i with
    | false => q.comp Coprod.inl
    | true => q.comp Coprod.inr
  have hm : ∀ i, (maps i).comp (φ i) = l := by
    intro i
    cases i
    · rfl
    · exact hlr.symm
  let F : Monoid.PushoutI φ →* P ⧸ N := Monoid.PushoutI.lift maps l hm
  have hF : F.comp f = q := by
    apply Coprod.hom_ext
    · ext g
      simp [F, f, maps]
      rfl
    · ext g
      simp [F, f, maps]
      rfl
  have hfN : f.ker ≤ N := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change q x = 1
    rw [← DFunLike.congr_fun hF]
    change F (f x) = 1
    rw [show f x = 1 from hx, map_one]
  exact Group.IsFinitelyPresented.of_surjective f hf
    ⟨rel '' S, hSfin.image rel, le_antisymm hNf hfN⟩

end UniversalGroup.PreparationFinite
