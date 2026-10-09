module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Data.Int.Cast.Lemmas

@[expose] public section

/-!
# Injectivity lemmas for indexed free products

This file supplies two reusable criteria for injectivity of maps out of an
indexed free product.  The first says that the free product of a family of
injective component maps is injective.  The second reduces injectivity of a
lift to nontriviality on every nonempty normal-form word.
-/

open Function

namespace Monoid.CoprodI

variable {ι : Type*} {M N : ι → Type*}
variable [∀ i, Group (M i)] [∀ i, Group (N i)]

private def letterMap (f : ∀ i, M i →* N i) : (Σ i, M i) → (Σ i, N i)
  | ⟨i, x⟩ => ⟨i, f i x⟩

private theorem letterMap_injective (f : ∀ i, M i →* N i)
    (hf : ∀ i, Injective (f i)) : Injective (letterMap f) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  refine Sigma.ext (x := ⟨i, x⟩) (y := ⟨i, y⟩) rfl ?_
  exact heq_of_eq (hf i (eq_of_heq (Sigma.ext_iff.mp h).2))

private def wordMap (f : ∀ i, M i →* N i) (hf : ∀ i, Injective (f i))
    (w : Word M) : Word N where
  toList := w.toList.map (letterMap f)
  ne_one := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨l', hl', rfl⟩
    rcases l' with ⟨i, x⟩
    simp only [letterMap]
    intro hx
    exact w.ne_one ⟨i, x⟩ hl' (hf i (hx.trans (f i).map_one.symm))
  chain_ne := by
    rw [List.isChain_map]
    exact w.chain_ne.imp fun a b hab h => hab (by simpa [letterMap] using h)

private theorem wordMap_injective (f : ∀ i, M i →* N i)
    (hf : ∀ i, Injective (f i)) : Injective (wordMap f hf) := by
  intro u v huv
  apply Word.ext
  have h := congrArg Word.toList huv
  change u.toList.map (letterMap f) = v.toList.map (letterMap f) at h
  exact (List.map_injective_iff.mpr (letterMap_injective f hf))
    h

/-- The homomorphism between indexed free products induced componentwise by
a family of homomorphisms. -/
def familyMap (f : ∀ i, M i →* N i) : CoprodI M →* CoprodI N :=
  lift fun i => (of : N i →* CoprodI N).comp (f i)

private theorem wordMap_prod (f : ∀ i, M i →* N i)
    (hf : ∀ i, Injective (f i)) (w : Word M) :
    (wordMap f hf w).prod = familyMap f w.prod := by
  simp only [Word.prod, wordMap, List.map_map, map_list_prod]
  congr 1

/-- Applying injective maps independently to the factors of an indexed free
product gives an injective homomorphism of indexed free products. -/
theorem familyMap_injective (f : ∀ i, M i →* N i)
    [DecidableEq ι] [∀ i, DecidableEq (M i)] [∀ i, DecidableEq (N i)]
    (hf : ∀ i, Injective (f i)) : Injective (familyMap f) := by
  intro x y hxy
  apply Word.equiv.injective
  apply wordMap_injective f hf
  apply Word.equiv.symm.injective
  change (wordMap f hf (Word.equiv x)).prod =
    (wordMap f hf (Word.equiv y)).prod
  rw [wordMap_prod, wordMap_prod]
  have hx : (Word.equiv x).prod = x := Word.equiv.symm_apply_apply x
  have hy : (Word.equiv y).prod = y := Word.equiv.symm_apply_apply y
  simpa [hx, hy] using hxy

/-- The map from a free group to the indexed free product of infinite cyclic
groups that sends each free generator to the generator of its factor. -/
def intOfFree (I : Type*) : FreeGroup I →*
    CoprodI (fun _ : I ↦ Multiplicative ℤ) :=
  FreeGroup.lift fun i ↦ of (i := i) (Multiplicative.ofAdd 1)

/-- The inverse-on-generators map associated to `intOfFree`. -/
def intToFree (I : Type*) : CoprodI (fun _ : I ↦ Multiplicative ℤ) →*
    FreeGroup I :=
  lift fun i ↦ zpowersHom (FreeGroup I) (FreeGroup.of i)

theorem intOfFree_injective (I : Type*) : Function.Injective (intOfFree I) := by
  apply Function.LeftInverse.injective (g := intToFree I)
  intro x
  have hcomp : (intToFree I).comp (intOfFree I) = MonoidHom.id (FreeGroup I) := by
    apply FreeGroup.ext_hom
    intro i
    simp [intToFree, intOfFree]
  exact DFunLike.congr_fun hcomp x

end Monoid.CoprodI

