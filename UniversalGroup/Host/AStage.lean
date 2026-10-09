module

public import UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Compression of four consecutive conjugates

The shift extension of `U × F(x₀,x₁,x₂,x₃)` is `U × F(a,x₀)`.
An injective realization of the four-column product in any ambient group
therefore gives the same free product factor after adjoining the shift letter.
-/

namespace UniversalGroup.ShiftCompression
noncomputable section
set_option maxHeartbeats 800000

section ChangeBase
variable {S P Q : Type*} [Group S] [Group P] [Group Q]
variable (l r : S →* P) (hl : Function.Injective l) (hr : Function.Injective r)
variable (j : P →* Q) (hj : Function.Injective j)

abbrev Ambient := IdentifyingHNN (j.comp l) (j.comp r) (hj.comp hl) (hj.comp hr)

def embed : IdentifyingHNN l r hl hr →* Ambient l r hl hr j hj :=
  IdentifyingHNN.lift l r hl hr
    ((IdentifyingHNN.of _ _ _ _).comp j) (IdentifyingHNN.stable _ _ _ _)
    (fun s => IdentifyingHNN.conjugates _ _ _ _ s)

@[simp] theorem embed_of (p : P) :
    embed l r hl hr j hj (HNNExtension.of p) = HNNExtension.of (j p) := by
  simp [embed, IdentifyingHNN.lift, IdentifyingHNN.of]

@[simp] theorem embed_t :
    embed l r hl hr j hj HNNExtension.t = HNNExtension.t := by
  simp [embed, IdentifyingHNN.lift, IdentifyingHNN.stable]

include hj in
private theorem mem_image_range_iff (f : S →* P) (p : P) :
    j p ∈ (j.comp f).range ↔ p ∈ f.range := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, hj hs⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

private def mapWord
    (w : HNNExtension.NormalWord.ReducedWord P l.range r.range) :
    HNNExtension.NormalWord.ReducedWord Q (j.comp l).range (j.comp r).range where
  head := j w.head
  toList := w.toList.map (fun x => (x.1, j x.2))
  chain := by
    rw [List.isChain_map]
    apply w.chain.imp
    intro a b hab hmem
    apply hab
    rcases Int.units_eq_one_or a.1 with h | h
    · simpa [h, mem_image_range_iff j hj] using hmem
    · simpa [h, mem_image_range_iff j hj] using hmem

private theorem mapWord_prod
    (w : HNNExtension.NormalWord.ReducedWord P l.range r.range) :
    (mapWord l r j hj w).prod (rangeEquiv (j.comp l) (j.comp r) (hj.comp hl) (hj.comp hr)) =
      embed l r hl hr j hj (w.prod (rangeEquiv l r hl hr)) := by
  simp only [HNNExtension.NormalWord.ReducedWord.prod,
    mapWord, List.map_map, map_mul, map_list_prod, embed_of]
  congr 1
  induction w.toList with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A reduced word entering the ambient base already belongs to the small base. -/
theorem embed_preimage_base (y : IdentifyingHNN l r hl hr)
    (hy : embed l r hl hr j hj y ∈
      (HNNExtension.of : Q →* Ambient l r hl hr j hj).range) :
    ∃ p : P, y = HNNExtension.of p := by
  rcases HNNExtension.NormalWord.TransversalPair.nonempty P l.range r.range with ⟨d⟩
  let w := HNNExtension.NormalWord.equiv (rangeEquiv l r hl hr) d y
  have hwy : w.toReducedWord.prod (rangeEquiv l r hl hr) = y :=
    (HNNExtension.NormalWord.equiv (rangeEquiv l r hl hr) d).symm_apply_apply y
  have hmapped : (mapWord l r j hj w.toReducedWord).prod
      (rangeEquiv (j.comp l) (j.comp r) (hj.comp hl) (hj.comp hr)) ∈
      (HNNExtension.of : Q →* Ambient l r hl hr j hj).range := by
    rw [mapWord_prod, hwy]
    exact hy
  have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (rangeEquiv (j.comp l) (j.comp r) (hj.comp hl) (hj.comp hr)) _ hmapped
  have hw : w.toList = [] := by simpa [mapWord] using hnil
  refine ⟨w.head, ?_⟩
  rw [← hwy]
  simp [HNNExtension.NormalWord.ReducedWord.prod, hw]

theorem embed_injective : Function.Injective (embed l r hl hr j hj) := by
  apply (injective_iff_map_eq_one _).mpr
  intro y hy
  obtain ⟨p, rfl⟩ := embed_preimage_base l r hl hr j hj y
    (by exact ⟨1, by simpa using hy.symm⟩)
  rw [embed_of] at hy
  have hp : p = 1 := hj ((HNNExtension.of_injective _)
    (by simpa using hy : HNNExtension.of (j p) = HNNExtension.of (j 1)))
  simp [hp]

end ChangeBase

section Shift
variable (U : Type*) [Group U]

/-- Include the first three columns. -/
def left : U × FreeGroup (Fin 3) →* U × FreeGroup (Fin 4) :=
  (MonoidHom.id U).prodMap (FreeGroup.map Fin.castSucc)

/-- Include the last three columns. -/
def right : U × FreeGroup (Fin 3) →* U × FreeGroup (Fin 4) :=
  (MonoidHom.id U).prodMap (FreeGroup.map Fin.succ)

@[simp] theorem left_apply (u : U) (w : FreeGroup (Fin 3)) :
    left U (u,w) = (u,FreeGroup.map Fin.castSucc w) := rfl
@[simp] theorem right_apply (u : U) (w : FreeGroup (Fin 3)) :
    right U (u,w) = (u,FreeGroup.map Fin.succ w) := rfl

theorem left_injective : Function.Injective (left U) :=
  Prod.map_injective.mpr ⟨Function.injective_id, FreeGroup.map_injective (Fin.castSucc_injective 3)⟩

theorem right_injective : Function.Injective (right U) :=
  Prod.map_injective.mpr ⟨Function.injective_id, FreeGroup.map_injective (Fin.succ_injective 3)⟩

abbrev Grid := IdentifyingHNN (left U) (right U) (left_injective U) (right_injective U)
def old : U × FreeGroup (Fin 4) →* Grid U := IdentifyingHNN.of _ _ _ _
@[simp] theorem old_one_pair : old U (1,1) = 1 := map_one (old U)

def stable : Grid U := IdentifyingHNN.stable _ _ _ _
def column (i : Fin 4) : Grid U := old U (1, FreeGroup.of i)

@[simp] theorem shift_column (i : Fin 3) :
    (stable U)⁻¹ * column U i.castSucc * stable U = column U i.succ := by
  simpa [stable, column, old] using
    IdentifyingHNN.conjugates (left U) (right U) (left_injective U)
      (right_injective U) (1, FreeGroup.of i)

/-- The old columns expressed through `a` and `x₀`. -/
def columns : FreeGroup (Fin 4) →* FreeGroup (Fin 2) :=
  FreeGroup.lift (fun i => (FreeGroup.of 0)⁻¹ ^ i.val * FreeGroup.of 1 * FreeGroup.of 0 ^ i.val)

def oldToProduct : U × FreeGroup (Fin 4) →* U × FreeGroup (Fin 2) :=
  (MonoidHom.id U).prodMap columns

private theorem columns_shift (w : FreeGroup (Fin 3)) :
    (FreeGroup.of 0)⁻¹ * columns (FreeGroup.map Fin.castSucc w) * FreeGroup.of 0 =
      columns (FreeGroup.map Fin.succ w) := by
  have h : (MulAut.conj ((FreeGroup.of 0 : FreeGroup (Fin 2))⁻¹)).toMonoidHom.comp
      (columns.comp (FreeGroup.map Fin.castSucc)) =
      columns.comp (FreeGroup.map Fin.succ) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [columns, pow_succ] <;> group
  simpa [MulAut.conj_apply] using DFunLike.congr_fun h w

/-- The Tietze map sends the stable letter to the first free generator. -/
def toProduct : Grid U →* U × FreeGroup (Fin 2) :=
  IdentifyingHNN.lift _ _ _ _ (oldToProduct U) (1, FreeGroup.of 0) (by
    rintro ⟨u, w⟩
    apply Prod.ext
    · simp [oldToProduct, left, right]
    · exact columns_shift w)

@[simp] theorem toProduct_old (u : U) (w : FreeGroup (Fin 4)) :
    toProduct U (old U (u,w)) = (u, columns w) := by
  simp [toProduct, old, oldToProduct]

@[simp] theorem toProduct_stable : toProduct U (stable U) = (1, FreeGroup.of 0) := by
  simp [toProduct, stable]

/-- The unchanged factor in the finite shift presentation. -/
def ofU : U →* Grid U := (old U).comp (MonoidHom.inl _ _)
def freePair : FreeGroup (Fin 2) →* Grid U :=
  FreeGroup.lift ![stable U, column U 0]

@[simp] theorem ofU_apply (u : U) : ofU U u = old U (u,1) := rfl
@[simp] theorem freePair_a : freePair U (FreeGroup.of 0) = stable U := by
  simp [freePair]
@[simp] theorem freePair_x : freePair U (FreeGroup.of 1) = column U 0 := by
  simp [freePair]

theorem ofU_commute_stable (u : U) : Commute (ofU U u) (stable U) := by
  have h := IdentifyingHNN.conjugates (left U) (right U) (left_injective U)
    (right_injective U) (u,1)
  change (stable U)⁻¹ * old U (left U (u,1)) * stable U = old U (right U (u,1)) at h
  simp only [left_apply, right_apply, map_one] at h
  rw [commute_iff_eq]
  have := congrArg (fun z => stable U * z) h
  simpa [mul_assoc, ofU_apply] using this

theorem ofU_commute_freePair (u : U) (w : FreeGroup (Fin 2)) :
    Commute (ofU U u) (freePair U w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
      fin_cases i
      · simpa using ofU_commute_stable U u
      · simpa [column, ofU] using
          (MonoidHom.commute_inl_inr (M := U) (N := FreeGroup (Fin 4)) u (FreeGroup.of 0)).map (old U)
  | inv_of i hi => simpa using hi.inv_right
  | mul w v hw hv => simpa using hw.mul_right hv

/-- The inverse Tietze map, with free basis `(a,x₀)`. -/
def fromProduct : U × FreeGroup (Fin 2) →* Grid U :=
  (ofU U).noncommCoprod (freePair U) (ofU_commute_freePair U)

@[simp] theorem fromProduct_apply (u : U) (w : FreeGroup (Fin 2)) :
    fromProduct U (u,w) = ofU U u * freePair U w := rfl
@[simp] theorem fromProduct_u (u : U) : fromProduct U (u,1) = ofU U u := by simp
@[simp] theorem fromProduct_free (w : FreeGroup (Fin 2)) :
    fromProduct U (1,w) = freePair U w := by simp

theorem column_eq (i : Fin 4) :
    column U i = (stable U)⁻¹ ^ i.val * column U 0 * stable U ^ i.val := by
  have h0 := shift_column U 0
  have h1 := shift_column U 1
  have h2 := shift_column U 2
  change (stable U)⁻¹ * column U 0 * stable U = column U 1 at h0
  change (stable U)⁻¹ * column U 1 * stable U = column U 2 at h1
  change (stable U)⁻¹ * column U 2 * stable U = column U 3 at h2
  fin_cases i
  · simp
  · simpa using h0.symm
  · change column U 2 = (stable U)⁻¹ ^ 2 * column U 0 * stable U ^ 2
    rw [← h1, ← h0]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · change column U 3 = (stable U)⁻¹ ^ 3 * column U 0 * stable U ^ 3
    rw [← h2, ← h1, ← h0]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

private theorem freePair_columns (w : FreeGroup (Fin 4)) :
    freePair U (columns w) = old U (1,w) := by
  have h : (freePair U).comp columns = (old U).comp (MonoidHom.inr _ _) := by
    apply FreeGroup.ext_hom
    intro i
    simpa [columns, column] using (column_eq U i).symm
  exact DFunLike.congr_fun h w

@[simp] theorem fromProduct_toProduct_old (u : U) (w : FreeGroup (Fin 4)) :
    fromProduct U (toProduct U (old U (u,w))) = old U (u,w) := by
  rw [toProduct_old, fromProduct_apply, freePair_columns, ofU_apply, ← map_mul]
  simp

@[simp] theorem fromProduct_toProduct_stable :
    fromProduct U (toProduct U (stable U)) = stable U := by simp

private theorem toProduct_freePair (w : FreeGroup (Fin 2)) :
    toProduct U (freePair U w) = (1,w) := by
  have h : (toProduct U).comp (freePair U) = MonoidHom.inr _ _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [column, columns]
  exact DFunLike.congr_fun h w

@[simp] theorem toProduct_fromProduct (u : U) (w : FreeGroup (Fin 2)) :
    toProduct U (fromProduct U (u,w)) = (u,w) := by
  simp [fromProduct_apply, toProduct_freePair]

/-- The four-column shift presentation is exactly the indicated product. -/
def gridEquiv : Grid U ≃* U × FreeGroup (Fin 2) :=
  { toFun := toProduct U
    invFun := fromProduct U
    map_mul' := map_mul _
    left_inv := by
      intro z
      have h : (fromProduct U).comp (toProduct U) = MonoidHom.id _ := by
        apply IdentifyingHNN.hom_ext
        · rintro ⟨u,w⟩
          exact fromProduct_toProduct_old U u w
        · exact fromProduct_toProduct_stable U
      exact DFunLike.congr_fun h z
    right_inv := by rintro ⟨u,w⟩; exact toProduct_fromProduct U u w }

variable {J : Type*} [Group J] (j : U × FreeGroup (Fin 4) →* J)
    (hj : Function.Injective j)

/-- Adjoin `a`, shifting columns 0,1,2 to 1,2,3 and fixing `U`. -/
abbrev Stage := Ambient (left U) (right U) (left_injective U) (right_injective U) j hj

def inclusion : J →* Stage U j hj := HNNExtension.of
def a : Stage U j hj := IdentifyingHNN.stable _ _ _ _

theorem inclusion_injective : Function.Injective (inclusion U j hj) :=
  HNNExtension.of_injective _

/-- The compressed product subgroup, with free basis `(a,x₀)`. -/
def productEmbedding : U × FreeGroup (Fin 2) →* Stage U j hj :=
  (embed (left U) (right U) (left_injective U) (right_injective U) j hj).comp
    (fromProduct U)

theorem productEmbedding_injective : Function.Injective (productEmbedding U j hj) :=
  (embed_injective _ _ _ _ j hj).comp (gridEquiv U).symm.injective

@[simp] theorem productEmbedding_u (u : U) :
    productEmbedding U j hj (u,1) = inclusion U j hj (j (u,1)) := by
  simp [productEmbedding, ofU, old, IdentifyingHNN.of, inclusion]

@[simp] theorem productEmbedding_a :
    productEmbedding U j hj (1,FreeGroup.of 0) = a U j hj := by
  simp [productEmbedding, stable, a, IdentifyingHNN.stable]

@[simp] theorem productEmbedding_x :
    productEmbedding U j hj (1,FreeGroup.of 1) = inclusion U j hj (j (1,FreeGroup.of 0)) := by
  simp only [productEmbedding, MonoidHom.comp_apply, fromProduct_free, freePair_x]
  exact embed_of _ _ _ _ j hj (1,FreeGroup.of 0)

/-- Replacing each old column by its conjugate in `(a,x₀)` recovers
its original image in the ambient group. -/
@[simp] theorem productEmbedding_columns (u : U) (w : FreeGroup (Fin 4)) :
    productEmbedding U j hj (u, columns w) = inclusion U j hj (j (u,w)) := by
  change embed _ _ _ _ j hj (fromProduct U (u, columns w)) = _
  rw [fromProduct_apply, freePair_columns, ofU_apply, ← map_mul]
  simp [old, IdentifyingHNN.of, inclusion]

end Shift
end
end UniversalGroup.ShiftCompression
