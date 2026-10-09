module

public import UniversalGroup.Foundations.HNN.Identifying

@[expose] public section

/-! Injectivity of HNN maps which reflect both associated subgroups. -/

namespace UniversalGroup.HNNMap
noncomputable section

variable {P M : Type*} [Group P] [Group M]
  (A B : Subgroup P) (e : A ≃* B) (L R : Subgroup M) (d : L ≃* R)
  (f : P →* M) (F : HNNExtension P A B e →* HNNExtension M L R d)
  (hA : ∀ x, x ∈ A ↔ f x ∈ L) (hB : ∀ x, x ∈ B ↔ f x ∈ R)
  (hof : ∀ x, F (HNNExtension.of x) = HNNExtension.of (f x))
  (ht : F HNNExtension.t = HNNExtension.t)

private def mapWord (w : HNNExtension.NormalWord.ReducedWord P A B) :
    HNNExtension.NormalWord.ReducedWord M L R where
  head := f w.head
  toList := w.toList.map (fun x => (x.1, f x.2))
  chain := by
    rw [List.isChain_map]
    apply w.chain.imp
    intro a b hab ha
    apply hab
    rcases Int.units_eq_one_or a.1 with h | h
    · simpa [h] using (hA a.2).mpr (by simpa [h] using ha)
    · simpa [h] using (hB a.2).mpr (by simpa [h] using ha)

include hof ht in
private theorem mapWord_prod (w : HNNExtension.NormalWord.ReducedWord P A B) :
    (mapWord A B L R f hA hB w).prod d = F (w.prod e) := by
  simp only [HNNExtension.NormalWord.ReducedWord.prod,
    mapWord, List.map_map, map_mul, map_list_prod, hof]
  congr 1
  induction w.toList with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.prod_cons, ih, Function.comp_apply, map_mul, map_zpow, ht, hof]

include hA hB hof ht in
theorem preimage_base (y : HNNExtension P A B e)
    (hy : F y ∈ (HNNExtension.of (φ := d)).range) :
    ∃ x : P, y = HNNExtension.of x := by
  let : Nonempty (HNNExtension.NormalWord.TransversalPair P A B) :=
    HNNExtension.NormalWord.TransversalPair.nonempty _ _ _
  let t : HNNExtension.NormalWord.TransversalPair P A B := Classical.choice inferInstance
  let w : HNNExtension.NormalWord t := (HNNExtension.NormalWord.equiv e t) y
  have hwy : w.toReducedWord.prod e = y :=
    (HNNExtension.NormalWord.equiv e t).symm_apply_apply y
  have hm : (mapWord A B L R f hA hB w.toReducedWord).prod d ∈
      (HNNExtension.of (φ := d)).range := by
    rw [mapWord_prod A B e L R d f F hA hB hof ht, hwy]
    exact hy
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    d (mapWord A B L R f hA hB w.toReducedWord) hm
  have hn' : w.toList = [] := by simpa [mapWord] using hn
  refine ⟨w.head, ?_⟩
  rw [← hwy]
  simp [HNNExtension.NormalWord.ReducedWord.prod, hn']

include hA hB hof ht in
theorem injective (hf : Function.Injective f) : Function.Injective F := by
  apply (injective_iff_map_eq_one _).mpr
  intro y hy
  have hm : F y ∈ (HNNExtension.of (φ := d)).range := ⟨1, by simpa using hy.symm⟩
  obtain ⟨x, rfl⟩ := preimage_base A B e L R d f F hA hB hof ht y hm
  rw [hof] at hy
  have hx : f x = 1 := (HNNExtension.of_injective _) (by simpa using hy)
  have hx' : x = 1 := hf (by simpa using hx)
  simp [hx']

section Identifying
variable {A₀ P₀ C₀ M₀ : Type*} [Group A₀] [Group P₀] [Group C₀] [Group M₀]
  (l r : A₀ →* P₀) (hl : Function.Injective l) (hr : Function.Injective r)
  (l' r' : C₀ →* M₀) (hl' : Function.Injective l') (hr' : Function.Injective r')
  (f₀ : P₀ →* M₀)
  (F₀ : IdentifyingHNN l r hl hr →* IdentifyingHNN l' r' hl' hr')

theorem identifying_injective
    (hA₀ : ∀ x, x ∈ l.range ↔ f₀ x ∈ l'.range)
    (hB₀ : ∀ x, x ∈ r.range ↔ f₀ x ∈ r'.range)
    (hof₀ : ∀ x, F₀ (IdentifyingHNN.of l r hl hr x) = IdentifyingHNN.of l' r' hl' hr' (f₀ x))
    (ht₀ : F₀ (IdentifyingHNN.stable l r hl hr) = IdentifyingHNN.stable l' r' hl' hr')
    (hf₀ : Function.Injective f₀) : Function.Injective F₀ := by
  apply injective l.range r.range (UniversalGroup.rangeEquiv l r hl hr)
    l'.range r'.range (UniversalGroup.rangeEquiv l' r' hl' hr') f₀ F₀ hA₀ hB₀ hof₀
  · simpa only [IdentifyingHNN.stable, map_inv, inv_inv] using congrArg Inv.inv ht₀
  · exact hf₀
end Identifying

end
end UniversalGroup.HNNMap
