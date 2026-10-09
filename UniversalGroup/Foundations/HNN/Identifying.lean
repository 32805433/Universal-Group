module

public import Mathlib.GroupTheory.HNNExtension

@[expose] public section

/-!
# HNN extensions specified by two embeddings

The HNN constructions identify subgroups by giving embeddings of the same
parameter group.  This file turns that data into an HNN extension and records
the canonical embedding, conjugation equations, and universal property.

The stable letter uses the convention `x ^ r = r⁻¹ * x * r`, so it is the
inverse of the stable letter used by mathlib's `HNNExtension`.
-/

namespace UniversalGroup

variable {A G : Type*} [Group A] [Group G]

/-- An injective homomorphism identifies its domain with its range. -/
noncomputable def equivRangeOfInjective
    (f : A →* G) (hf : Function.Injective f) : A ≃* f.range :=
  MulEquiv.ofBijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hf, f.rangeRestrict_surjective⟩

/-- The isomorphism between two copies of the same parameter group. -/
noncomputable def rangeEquiv
    (left right : A →* G)
    (hl : Function.Injective left) (hr : Function.Injective right) :
    left.range ≃* right.range :=
  (equivRangeOfInjective left hl).symm.trans (equivRangeOfInjective right hr)

@[simp]
theorem rangeEquiv_apply_range
    (left right : A →* G)
    (hl : Function.Injective left) (hr : Function.Injective right) (a : A) :
    ((rangeEquiv left right hl hr ⟨left a, ⟨a, rfl⟩⟩ : right.range) : G) =
      right a := by
  change right ((equivRangeOfInjective left hl).symm ⟨left a, ⟨a, rfl⟩⟩) = right a
  have h : (equivRangeOfInjective left hl).symm ⟨left a, ⟨a, rfl⟩⟩ = a := by
    apply hl
    exact congrArg Subtype.val
      ((equivRangeOfInjective left hl).apply_symm_apply ⟨left a, ⟨a, rfl⟩⟩)
  exact congrArg right h

/-- Adjoin a letter that conjugates the left copy of `A` to the right copy. -/
noncomputable abbrev IdentifyingHNN
    (left right : A →* G)
    (hl : Function.Injective left) (hr : Function.Injective right) :=
  HNNExtension G left.range right.range (rangeEquiv left right hl hr)

namespace IdentifyingHNN

variable (left right : A →* G)
  (hl : Function.Injective left) (hr : Function.Injective right)

/-- The canonical homomorphism from the base group. -/
noncomputable def of : G →* IdentifyingHNN left right hl hr :=
  HNNExtension.of

/-- The base group embeds, by the HNN normal-form theorem. -/
theorem of_injective : Function.Injective (of left right hl hr) :=
  HNNExtension.of_injective (rangeEquiv left right hl hr)

/-- The stable letter in the convention `r⁻¹ * left a * r = right a`. -/
noncomputable def stable : IdentifyingHNN left right hl hr :=
  HNNExtension.t⁻¹

theorem conjugates (a : A) :
    (stable left right hl hr)⁻¹ * of left right hl hr (left a) *
        stable left right hl hr = of left right hl hr (right a) := by
  simpa [stable, of] using
    (HNNExtension.equiv_eq_conj
      (φ := rangeEquiv left right hl hr) ⟨left a, ⟨a, rfl⟩⟩).symm

variable {H : Type*} [Group H]

/-- Extend a homomorphism when the chosen target stable letter obeys all the
conjugation equations. -/
noncomputable def lift (f : G →* H) (r : H)
    (h : ∀ a : A, r⁻¹ * f (left a) * r = f (right a)) :
    IdentifyingHNN left right hl hr →* H :=
  HNNExtension.lift f r⁻¹ (by
    rintro ⟨_, a, rfl⟩
    rw [rangeEquiv_apply_range, ← h a]
    simp only [mul_assoc, mul_inv_cancel, mul_one])

@[simp]
theorem lift_of (f : G →* H) (r : H)
    (h : ∀ a : A, r⁻¹ * f (left a) * r = f (right a)) (g : G) :
    lift left right hl hr f r h (of left right hl hr g) = f g := by
  simp [lift, of]

@[simp]
theorem lift_stable (f : G →* H) (r : H)
    (h : ∀ a : A, r⁻¹ * f (left a) * r = f (right a)) :
    lift left right hl hr f r h (stable left right hl hr) = r := by
  simp [lift, stable]

/-- A homomorphism is determined by its values on the base group and the
stable letter. -/
theorem hom_ext {f g : IdentifyingHNN left right hl hr →* H}
    (hbase : ∀ x : G, f (of left right hl hr x) = g (of left right hl hr x))
    (hstable : f (stable left right hl hr) = g (stable left right hl hr)) :
    f = g := by
  apply HNNExtension.hom_ext
  · ext x
    exact hbase x
  · simpa [stable] using congrArg Inv.inv hstable

end IdentifyingHNN
end UniversalGroup
