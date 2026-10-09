module

public import UniversalGroup.Foundations.Amalgam.Conjugated

@[expose] public section

/-! Base-subgroup geometry used in the recognition intersection argument. -/

namespace UniversalGroup.RecognitionGeometry

open HNNLemmas
noncomputable section

variable {K : Type*} [Group K] (C S V : Subgroup K)

abbrev Stage := CentralizerHNN K C
abbrev ofCore : K →* Stage C := centralizerOf C
abbrev f : Stage C := centralizerStable C

def wide : Subgroup (Stage C) :=
  generatedWithStable (A := C) (B := C) (phi := MulEquiv.refl C) S

def aBase : Subgroup (Stage C) := ConjugatedAmalgam.subgroup V S C
theorem wide_inf_core : wide C S ⊓ (ofCore C).range = S.map (ofCore C) :=
  generatedWithStable_inf_base S (by intro a; rfl)

theorem ofCore_mem_wide_iff (x : K) : ofCore C x ∈ wide C S ↔ x ∈ S := by
  constructor
  · intro hx
    have hm : ofCore C x ∈ S.map (ofCore C) := by
      rw [← wide_inf_core C S]
      exact ⟨hx, ⟨x, rfl⟩⟩
    obtain ⟨y, hy, heq⟩ := hm
    exact (HNNExtension.of_injective (φ := MulEquiv.refl C) heq) ▸ hy
  · intro hx
    exact (wide_inf_core C S ▸ (show ofCore C x ∈ S.map (ofCore C) from
      ⟨x, hx, rfl⟩)).1

theorem f_mem_wide : f C ∈ wide C S := by
  apply Subgroup.subset_closure
  exact Or.inr rfl

variable (hVS : V ≤ S) (hSC : S ⊓ C = ⊥)
include hVS hSC

theorem aBase_inf_core : aBase C S V ⊓ (ofCore C).range = V.map (ofCore C) := by
  have hCV : C ⊓ V = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hm : x ∈ S ⊓ C := ⟨hVS hx.2, hx.1⟩
      rwa [hSC] at hm
    · exact bot_le
  exact ConjugatedAmalgam.subgroup_inf_base V S ⊥ bot_le bot_le C bot_le
    hCV (inf_comm C S ▸ hSC)

theorem ofCore_mem_aBase_iff (x : K) : ofCore C x ∈ aBase C S V ↔ x ∈ V := by
  constructor
  · intro hx
    have hm : ofCore C x ∈ V.map (ofCore C) := by
      rw [← aBase_inf_core C S V hVS hSC]
      exact ⟨hx, ⟨x, rfl⟩⟩
    obtain ⟨y, hy, heq⟩ := hm
    exact (HNNExtension.of_injective (φ := MulEquiv.refl C) heq) ▸ hy
  · intro hx
    apply le_sup_left (b := S.map (ConjugatedAmalgam.conjugatedOf C))
    exact ⟨x, hx, rfl⟩

omit hSC in
theorem aBase_le_wide : aBase C S V ≤ wide C S := by
  apply sup_le
  · rintro x ⟨v, hv, rfl⟩
    exact (ofCore_mem_wide_iff C S v).2 (hVS hv)
  · rintro x ⟨s, hs, rfl⟩
    change (f C)⁻¹ * ofCore C s * f C ∈ wide C S
    exact (wide C S).mul_mem
      ((wide C S).mul_mem ((wide C S).inv_mem (f_mem_wide C S))
        ((ofCore_mem_wide_iff C S s).2 hs)) (f_mem_wide C S)

omit hVS hSC in
theorem conjugated_mem_aBase {x : K} (hx : x ∈ S) :
    (f C)⁻¹ * ofCore C x * f C ∈ aBase C S V := by
  apply le_sup_right (a := V.map (ofCore C))
  exact ⟨x, hx, rfl⟩

/-- In the negative-negative case, the intervening coefficient forces the
first free-letter word into the code subgroup. -/
theorem negative_next_negative {v x : K} {j : Stage C}
    (hv : v ∈ S) (hj : j ∈ aBase C S V)
    (heq : ofCore C v * j = (f C)⁻¹ * ofCore C x * f C) : v ∈ V := by
  have hprod : ofCore C v * j ∈ wide C S :=
    (wide C S).mul_mem ((ofCore_mem_wide_iff C S v).2 hv)
      (aBase_le_wide C S V hVS hj)
  have hxwide : ofCore C x ∈ wide C S := by
    have hh := (wide C S).mul_mem
      ((wide C S).mul_mem (f_mem_wide C S) hprod)
      ((wide C S).inv_mem (f_mem_wide C S))
    simpa [heq, mul_assoc] using hh
  have hx : x ∈ S := (ofCore_mem_wide_iff C S x).1 hxwide
  have hm : ofCore C v * j ∈ aBase C S V := by
    rw [heq]
    exact conjugated_mem_aBase C S V hx
  apply (ofCore_mem_aBase_iff C S V hVS hSC v).1
  simpa only [mul_inv_cancel_right] using
    (aBase C S V).mul_mem hm ((aBase C S V).inv_mem hj)

/-- The terminal negative case also leaves a word in the code subgroup. -/
theorem negative_terminal {v x : K} {j : Stage C}
    (hv : v ∈ S) (hj : j ∈ aBase C S V) (hx : x ∈ C)
    (heq : ofCore C v * j = ofCore C x) : v ∈ V := by
  have hprod : ofCore C x ∈ wide C S := by
    rw [← heq]
    exact (wide C S).mul_mem ((ofCore_mem_wide_iff C S v).2 hv)
      (aBase_le_wide C S V hVS hj)
  have hxs : x ∈ S := (ofCore_mem_wide_iff C S x).1 hprod
  have hxone : x = 1 := by
    have hm : x ∈ S ⊓ C := ⟨hxs, hx⟩
    simpa only [hSC, Subgroup.mem_bot] using hm
  have hvj : ofCore C v * j = 1 := by simpa [hxone] using heq
  apply (ofCore_mem_aBase_iff C S V hVS hSC v).1
  rw [eq_inv_of_mul_eq_one_left hvj]
  exact (aBase C S V).inv_mem hj

end
end UniversalGroup.RecognitionGeometry
