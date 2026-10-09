module

public import UniversalGroup.Foundations.HNN.NormalForms

@[expose] public section

/-! Faithful maps between centralizer HNN extensions that reflect their
associated subgroups. -/

namespace UniversalGroup.CentralizerMap

open HNNLemmas

noncomputable section

variable {H G : Type*} [Group H] [Group G]
  (A : Subgroup H) (C : Subgroup G) (φ : H →* G)
  (hmem : ∀ x, x ∈ A ↔ φ x ∈ C)

def hom : CentralizerHNN H A →* CentralizerHNN G C :=
  HNNExtension.lift ((centralizerOf C).comp φ) (centralizerStable C) (by
    intro a
    exact HNNExtension.t_mul_of (φ := MulEquiv.refl C) ⟨φ a, (hmem a).mp a.property⟩)

@[simp] theorem hom_of (x : H) : hom A C φ hmem (centralizerOf A x) = centralizerOf C (φ x) := by
  simp [hom, centralizerOf]

@[simp] theorem hom_stable : hom A C φ hmem (centralizerStable A) = centralizerStable C := by
  simp [hom, centralizerStable]

private def mapWord (w : HNNExtension.NormalWord.ReducedWord H A A) :
    HNNExtension.NormalWord.ReducedWord G C C where
  head := φ w.head
  toList := w.toList.map (fun x => (x.1, φ x.2))
  chain := by
    rw [List.isChain_map]
    apply w.chain.imp
    intro a b hab ha
    apply hab
    rcases Int.units_eq_one_or a.1 with h | h
    · simpa [h] using (hmem a.2).mpr (by simpa [h] using ha)
    · simpa [h] using (hmem a.2).mpr (by simpa [h] using ha)

private theorem mapWord_prod (w : HNNExtension.NormalWord.ReducedWord H A A) :
    (mapWord A C φ hmem w).prod (MulEquiv.refl C) = hom A C φ hmem (w.prod (MulEquiv.refl A)) := by
  simp only [HNNExtension.NormalWord.ReducedWord.prod,
    mapWord, List.map_map, map_mul, map_list_prod]
  congr 1
  induction w.toList with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      simp [hom, centralizerOf, centralizerStable]

theorem preimage_base (y : CentralizerHNN H A)
    (hy : hom A C φ hmem y ∈ (centralizerOf C).range) :
    ∃ x : H, y = centralizerOf A x := by
  let : Nonempty (HNNExtension.NormalWord.TransversalPair H A A) :=
    HNNExtension.NormalWord.TransversalPair.nonempty _ _ _
  let d : HNNExtension.NormalWord.TransversalPair H A A := Classical.choice inferInstance
  let w : HNNExtension.NormalWord d := (HNNExtension.NormalWord.equiv (MulEquiv.refl A) d) y
  have hwy : w.toReducedWord.prod (MulEquiv.refl A) = y :=
    (HNNExtension.NormalWord.equiv (MulEquiv.refl A) d).symm_apply_apply y
  have hm : (mapWord A C φ hmem w.toReducedWord).prod (MulEquiv.refl C) ∈
      (centralizerOf C).range := by
    rw [mapWord_prod, hwy]
    exact hy
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (MulEquiv.refl C) (mapWord A C φ hmem w.toReducedWord) hm
  have hn' : w.toList = [] := by simpa [mapWord] using hn
  refine ⟨w.head, ?_⟩
  rw [← hwy]
  simp [HNNExtension.NormalWord.ReducedWord.prod, hn', centralizerOf]

theorem hom_injective (hφ : Function.Injective φ) : Function.Injective (hom A C φ hmem) := by
  apply (injective_iff_map_eq_one (hom A C φ hmem)).mpr
  intro y hy
  have hm : hom A C φ hmem y ∈ (centralizerOf C).range := ⟨1, by simpa using hy.symm⟩
  rcases preimage_base A C φ hmem y hm with ⟨x, rfl⟩
  rw [hom_of] at hy
  have hx : φ x = 1 := (HNNExtension.of_injective _) (by simpa [centralizerOf] using hy)
  have hx' : x = 1 := hφ (by simpa using hx)
  simp [hx']


theorem range_eq_generated : (hom A C φ hmem).range =
    generatedWithStable (A := C) (B := C) (phi := MulEquiv.refl C) φ.range := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using HNNExtension.induction_on with
    | of h =>
        rw [show HNNExtension.of h = centralizerOf A h from rfl, hom_of]
        exact Subgroup.subset_closure (Or.inl ⟨φ h, ⟨h, rfl⟩, rfl⟩)
    | t =>
        rw [show HNNExtension.t = centralizerStable A from rfl, hom_stable]
        exact Subgroup.subset_closure (Or.inr rfl)
    | mul x y hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x hx => simpa using Subgroup.inv_mem _ hx
  · rw [generatedWithStable, Subgroup.closure_le]
    rintro x (hx | rfl)
    · rcases hx with ⟨y, ⟨h, rfl⟩, rfl⟩
      exact ⟨centralizerOf A h, hom_of A C φ hmem h⟩
    · exact ⟨centralizerStable A, hom_stable A C φ hmem⟩

end

end UniversalGroup.CentralizerMap
