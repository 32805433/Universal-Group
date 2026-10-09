module

public import UniversalGroup.Foundations.HNN.NormalForms

@[expose] public section

/-! A centralizer HNN subgroup of a general HNN extension. -/

namespace UniversalGroup.CentralizerIntoHNN
open HNNLemmas
noncomputable section

variable {P M : Type*} [Group P] [Group M]
  (A : Subgroup P) (L R : Subgroup M) (e : L ≃* R) (f : P →* M)
  (hL : ∀ x, x ∈ A ↔ f x ∈ L) (hR : ∀ x, x ∈ A ↔ f x ∈ R)
  (hfix : ∀ x : A, (e ⟨f x, (hL x).mp x.property⟩ : M) = f x)

def hom : CentralizerHNN P A →* HNNExtension M L R e :=
  HNNExtension.lift (HNNExtension.of.comp f) HNNExtension.t (by
    intro a
    have h := HNNExtension.t_mul_of (φ := e) ⟨f a, (hL a).mp a.property⟩
    simpa only [hfix, MonoidHom.comp_apply, MulEquiv.refl_apply] using h)

@[simp] theorem hom_of (x : P) :
    hom A L R e f hL hfix (centralizerOf A x) = HNNExtension.of (f x) := by
  simp [hom, centralizerOf]

@[simp] theorem hom_stable :
    hom A L R e f hL hfix (centralizerStable A) = HNNExtension.t := by
  simp [hom, centralizerStable]

private def mapWord (w : HNNExtension.NormalWord.ReducedWord P A A) :
    HNNExtension.NormalWord.ReducedWord M L R where
  head := f w.head
  toList := w.toList.map (fun x => (x.1, f x.2))
  chain := by
    rw [List.isChain_map]
    apply w.chain.imp
    intro a b hab ha
    apply hab
    rcases Int.units_eq_one_or a.1 with h | h
    · simpa [h] using (hL a.2).mpr (by simpa [h] using ha)
    · simpa [h] using (hR a.2).mpr (by simpa [h] using ha)

private theorem mapWord_prod (w : HNNExtension.NormalWord.ReducedWord P A A) :
    (mapWord A L R f hL hR w).prod e = hom A L R e f hL hfix (w.prod (MulEquiv.refl A)) := by
  simp only [HNNExtension.NormalWord.ReducedWord.prod,
    mapWord, List.map_map, map_mul, map_list_prod]
  congr 1
  induction w.toList with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    simp [hom]

include hR in
theorem preimage_base (y : CentralizerHNN P A)
    (hy : hom A L R e f hL hfix y ∈ (HNNExtension.of (φ := e)).range) :
    ∃ x : P, y = centralizerOf A x := by
  let : Nonempty (HNNExtension.NormalWord.TransversalPair P A A) :=
    HNNExtension.NormalWord.TransversalPair.nonempty _ _ _
  let d : HNNExtension.NormalWord.TransversalPair P A A := Classical.choice inferInstance
  let w : HNNExtension.NormalWord d := (HNNExtension.NormalWord.equiv (MulEquiv.refl A) d) y
  have hwy : w.toReducedWord.prod (MulEquiv.refl A) = y :=
    (HNNExtension.NormalWord.equiv (MulEquiv.refl A) d).symm_apply_apply y
  have hm : (mapWord A L R f hL hR w.toReducedWord).prod e ∈
      (HNNExtension.of (φ := e)).range := by
    rw [mapWord_prod, hwy]
    exact hy
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    e (mapWord A L R f hL hR w.toReducedWord) hm
  have hn' : w.toList = [] := by simpa [mapWord] using hn
  refine ⟨w.head, ?_⟩
  rw [← hwy]
  simp [HNNExtension.NormalWord.ReducedWord.prod, hn', centralizerOf]

include hR in
theorem hom_injective (hf : Function.Injective f) :
    Function.Injective (hom A L R e f hL hfix) := by
  apply (injective_iff_map_eq_one _).mpr
  intro y hy
  have hm : hom A L R e f hL hfix y ∈ (HNNExtension.of (φ := e)).range :=
    ⟨1, by simpa using hy.symm⟩
  obtain ⟨x, rfl⟩ := preimage_base A L R e f hL hR hfix y hm
  rw [hom_of] at hy
  have hx : f x = 1 := (HNNExtension.of_injective _) (by simpa using hy)
  have hx' : x = 1 := hf (by simpa using hx)
  simp [hx']

end
end UniversalGroup.CentralizerIntoHNN
