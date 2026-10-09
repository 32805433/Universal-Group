module

public import UniversalGroup.Higman.Diagonal
public import UniversalGroup.Computability.WordProblem
public import UniversalGroup.Foundations.FinitePresentation.Generators

@[expose] public section

/-!
# Positive signed covers and the final Higman interface

The signed cover has one positive letter for each generator and one for
its inverse. Its positive word problem is recursively enumerable, and all
inverse generators have positive representatives. These are precisely the
hypotheses needed by the diagonal-subgroup embedding construction.
-/

namespace UniversalGroup.HigmanAssembly

noncomputable section

variable {n : ℕ}

/-- Positive and negative occurrences become separate unsigned letters. -/
def positiveIndex (i : Fin n) : Fin (n+n) := finSumFinEquiv (Sum.inl i)
def negativeIndex (i : Fin n) : Fin (n+n) := finSumFinEquiv (Sum.inr i)

def signedLetter (i : Fin (n+n)) : Fin n × Bool :=
  match finSumFinEquiv.symm i with
  | Sum.inl j => (j, true)
  | Sum.inr j => (j, false)

@[simp] theorem signedLetter_positive (i : Fin n) :
    signedLetter (positiveIndex i) = (i, true) := by
  unfold signedLetter positiveIndex
  rw [Equiv.symm_apply_apply]

@[simp] theorem signedLetter_negative (i : Fin n) :
    signedLetter (negativeIndex i) = (i, false) := by
  unfold signedLetter negativeIndex
  rw [Equiv.symm_apply_apply]

def signedWord (w : List (Fin (n+n))) : List (Fin n × Bool) := w.map signedLetter

/-- The signed cover maps both signs to their intended values in the input group. -/
def cover (R : RecursivePresentation (Fin n)) : FreeGroup (Fin (n+n)) →* R.Group :=
  FreeGroup.lift (fun i =>
    if (signedLetter i).2 then PresentedGroup.of (signedLetter i).1
    else (PresentedGroup.of (signedLetter i).1)⁻¹)

@[simp] theorem cover_positive (R : RecursivePresentation (Fin n)) (i : Fin n) :
    cover R (FreeGroup.of (positiveIndex i)) = PresentedGroup.of i := by
  simp [cover]

@[simp] theorem cover_negative (R : RecursivePresentation (Fin n)) (i : Fin n) :
    cover R (FreeGroup.of (negativeIndex i)) = (PresentedGroup.of i)⁻¹ := by
  simp [cover]

theorem cover_surjective (R : RecursivePresentation (Fin n)) : Function.Surjective (cover R) := by
  have h : (cover R).comp (FreeGroup.map positiveIndex) = PresentedGroup.mk R.relSet := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, cover_positive]
    rfl
  intro g
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective R.relSet g
  exact ⟨FreeGroup.map positiveIndex w, DFunLike.congr_fun h w⟩

/-- In the signed cover each inverse generator has a one-letter positive spelling. -/
theorem cover_positive_inverses (R : RecursivePresentation (Fin n)) :
    ∀ i : Fin (n+n), ∃ w : List (Fin (n+n)),
      cover R (PositiveKernel.positive w) = (cover R (FreeGroup.of i))⁻¹ := by
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
      refine ⟨[negativeIndex j], ?_⟩
      change cover R (PositiveKernel.positive [negativeIndex j]) =
        (cover R (FreeGroup.of (positiveIndex j)))⁻¹
      simp
  | inr j =>
      refine ⟨[positiveIndex j], ?_⟩
      change cover R (PositiveKernel.positive [positiveIndex j]) =
        (cover R (FreeGroup.of (negativeIndex j)))⁻¹
      simp

theorem cover_positive_word (R : RecursivePresentation (Fin n)) (w : List (Fin (n+n))) :
    cover R (PositiveKernel.positive w) = PresentedGroup.mk R.relSet (FreeGroup.mk (signedWord w)) := by
  have hmk : PresentedGroup.mk R.relSet = FreeGroup.lift (PresentedGroup.of (rels := R.relSet)) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  rw [hmk, FreeGroup.lift_mk]
  simp only [PositiveKernel.positive, map_list_prod, List.map_map, signedWord]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [cover]

/-- The positive word problem of the signed cover. -/
def language (R : RecursivePresentation (Fin n)) (w : List (Fin (n+n))) : Prop :=
  cover R (PositiveKernel.positive w) = 1

/-- Identity must be accepted by the signed-cover language. -/
@[simp] theorem language_nil (R : RecursivePresentation (Fin n)) : language R [] := by
  simp [language]

theorem signedWord_primrec : Primrec (@signedWord n) :=
  Primrec.list_map Primrec.id ((Primrec.dom_finite signedLetter).comp Primrec.snd).to₂

theorem language_enumerable (R : RecursivePresentation (Fin n)) : REPred (language R) := by
  apply (RecursiveEnumerable.comp (RecursiveWordProblem.word_problem_enumerable R)
    signedWord_primrec.to_comp).of_eq
  intro w
  exact Iff.of_eq (congrArg (· = 1) (cover_positive_word R w)).symm

/-- Convert an abstract finite-presented overgroup into the original literal
`FP a b` interface. -/
theorem exists_FP_of_embedsInFP {G : Type} [Group G] (h : HigmanBenign.EmbedsInFP G) :
    ∃ a b : ℕ, ∃ P : FP a b, Nonempty (GroupEmbedding G P.Group) := by
  obtain ⟨K, instK, hK, f, hf⟩ := h
  let : Group K := instK
  let : Group.IsFinitelyPresented K := hK
  obtain ⟨a, π, hπ, _⟩ := hK.out
  obtain ⟨b, P, e, _⟩ := PreparationGenerators.presentation_of_surjective π hπ
  exact ⟨a, b, P, ⟨⟨e.symm.toMonoidHom.comp f, e.symm.injective.comp hf⟩⟩⟩

/-- Once the positive diagonal subgroup is benign, the original recursive
presentation embeds in a literal finite presentation. -/
theorem exists_FP_of_benign_positive_diagonal (R : RecursivePresentation (Fin n))
    (h : HigmanBenign.Benign (HigmanDelta.subgroup (PositiveKernel.elements (cover R)))) :
    ∃ a b : ℕ, ∃ P : FP a b, Nonempty (GroupEmbedding R.Group P.Group) :=
  exists_FP_of_embedsInFP (HigmanDelta.embedsInFP_of_positive_diagonal
    (cover R) (cover_surjective R) (cover_positive_inverses R) h)

end
end UniversalGroup.HigmanAssembly
