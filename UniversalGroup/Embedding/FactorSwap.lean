module

public import UniversalGroup.Embedding.Presentations
public import UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Conditional embedding in the two-generator, thirteen-relator group

The geometric assumptions are exactly two specified injective maps from
`F₂ × F₃`. The HNN embedding, all five generator eliminations, and all six
relator deletions are proved here without further assumptions.
-/

namespace UniversalGroup.Embedding

attribute [local irreducible] positiveBasePresentation thirteenPresentation
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

abbrev FactorSwapDomain := FreeGroup (Fin 2) × FreeGroup (Fin 3)
def factorFirst (i : Fin 2) : FactorSwapDomain := (FreeGroup.of i, 1)
def factorSecond (i : Fin 3) : FactorSwapDomain := (1, FreeGroup.of i)

/-- Exact associated subgroups, on the displayed ordered bases. -/
structure FactorSwapData (D : CodeWords) where
  left : FactorSwapDomain →* (positiveBasePresentation D).Group
  right : FactorSwapDomain →* (positiveBasePresentation D).Group
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  left_c : left (factorFirst 0) = generators (positiveBasePresentation D) 0
  left_d : left (factorFirst 1) = generators (positiveBasePresentation D) 1
  left_f : left (factorSecond 0) = generators (positiveBasePresentation D) 2
  left_k : left (factorSecond 1) = generators (positiveBasePresentation D) 3
  left_h2 : left (factorSecond 2) =
    (positiveBasePresentation D).evalWord (Word.pow baseWords.h 2)
  right_a : right (factorFirst 0) = generators (positiveBasePresentation D) 4
  right_x : right (factorFirst 1) = (positiveBasePresentation D).evalWord baseWords.x
  right_A : right (factorSecond 0) = (positiveBasePresentation D).evalWord (swapA baseWords)
  right_B : right (factorSecond 1) = (positiveBasePresentation D).evalWord (swapB baseWords)
  right_b : right (factorSecond 2) = generators (positiveBasePresentation D) 5

namespace FactorSwapData

variable {D : CodeWords} (data : FactorSwapData D)

noncomputable abbrev Extension :=
  IdentifyingHNN data.left data.right data.left_injective data.right_injective

noncomputable def inclusion : (positiveBasePresentation D).Group →* data.Extension :=
  IdentifyingHNN.of data.left data.right data.left_injective data.right_injective

theorem inclusion_injective : Function.Injective data.inclusion :=
  IdentifyingHNN.of_injective data.left data.right data.left_injective data.right_injective

noncomputable def stable : data.Extension :=
  IdentifyingHNN.stable data.left data.right data.left_injective data.right_injective

noncomputable def oldValues (i : Fin 6) : data.Extension :=
  data.inclusion (generators (positiveBasePresentation D) i)

theorem stable_equations :
    data.stable⁻¹ * data.oldValues 0 * data.stable = data.oldValues 4 ∧
    data.stable⁻¹ * data.oldValues 1 * data.stable =
      (data.oldValues 3)⁻¹ * data.oldValues 2 * data.oldValues 3 ∧
    data.stable⁻¹ * data.oldValues 2 * data.stable =
      rowA (data.oldValues 0) (data.oldValues 5) ∧
    data.stable⁻¹ * data.oldValues 3 * data.stable =
      rowB (data.oldValues 0) (data.oldValues 5) ∧
    data.stable⁻¹ * (((data.oldValues 4) ^ 2)⁻¹ *
      ((data.oldValues 3)⁻¹ * data.oldValues 2 * data.oldValues 3) *
        (data.oldValues 4) ^ 2) ^ 2 * data.stable = data.oldValues 5 := by
  have hc := IdentifyingHNN.conjugates data.left data.right
    data.left_injective data.right_injective (factorFirst 0)
  have hd := IdentifyingHNN.conjugates data.left data.right
    data.left_injective data.right_injective (factorFirst 1)
  have hf := IdentifyingHNN.conjugates data.left data.right
    data.left_injective data.right_injective (factorSecond 0)
  have hk := IdentifyingHNN.conjugates data.left data.right
    data.left_injective data.right_injective (factorSecond 1)
  have hh := IdentifyingHNN.conjugates data.left data.right
    data.left_injective data.right_injective (factorSecond 2)
  rw [data.left_c, data.right_a] at hc
  rw [data.left_d, data.right_x] at hd
  rw [data.left_f, data.right_A] at hf
  rw [data.left_k, data.right_B] at hk
  rw [data.left_h2, data.right_b] at hh
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · simpa [oldValues, inclusion, stable, FP.evalWord, BaseWords.x, baseWords,
      generators, mul_assoc] using hd
  · simpa [oldValues, inclusion, stable, FP.evalWord, swapA, swapB, rowA, rowB,
      baseWords, generators, mul_assoc] using hf
  · simpa [oldValues, inclusion, stable, FP.evalWord, swapB, rowB,
      baseWords, generators, mul_assoc] using hk
  · simpa [oldValues, inclusion, stable, FP.evalWord, BaseWords.h, BaseWords.x,
      baseWords, generators, mul_assoc] using hh

noncomputable def newValues : Fin 2 → data.Extension := ![data.oldValues 0, data.stable]

/-- All old generators are recovered inside the proper HNN extension. -/
theorem reconstructs (i : Fin 6) :
    Word.eval data.newValues (thirteenSubstitution i) = data.oldValues i := by
  obtain ⟨hc, hd, hf, hk, hh⟩ := data.stable_equations
  obtain ⟨ha, hb, hk', hf', _, hd'⟩ := factor_swap_substitutions
    (data.oldValues 0) (data.oldValues 1) (data.oldValues 2)
    (data.oldValues 3) (data.oldValues 4) (data.oldValues 5) data.stable
    hc hd hf hk hh
  rw [hb] at hk' hf'
  fin_cases i
  · simp [thirteenSubstitution, newValues]
  · simpa [thirteenSubstitution, newValues] using hd'.symm
  · simpa [thirteenSubstitution, newValues] using hf'.symm
  · simpa [thirteenSubstitution, newValues] using hk'.symm
  · simpa [thirteenSubstitution, newValues] using ha.symm
  · simpa [thirteenSubstitution, newValues] using hb.symm

theorem reconstructs_word (w : Word 6) :
    Word.eval data.newValues (Word.substitute thirteenSubstitution w) =
      data.inclusion ((positiveBasePresentation D).evalWord w) := by
  rw [Word.eval_substitute, FP.evalWord, Word.map_eval]
  congr 1
  funext i
  exact data.reconstructs i

end FactorSwapData

private theorem word_commutator_eq_one_iff {G : Type*} [Group G]
    (v : Fin n → G) (u w : Word n) :
    Word.eval v (Word.commutator u w) = 1 ↔
      Commute (Word.eval v u) (Word.eval v w) := by
  rw [Word.eval_commutator, mul_assoc, mul_assoc, inv_mul_eq_one,
    eq_inv_mul_iff_mul_eq, commute_iff_eq]
  exact eq_comm

/-- Every host relator follows from the thirteen selected rows. This is the
explicit certificate for all six deletions. -/
theorem factorSwapRelators (D : CodeWords) {G : Type*} [Group G]
    (v : Fin 2 → G)
    (h : ∀ i, Word.eval v ((thirteenPresentation D).relator i) = 1) :
    ∀ i, Word.eval (fun j => Word.eval v (thirteenSubstitution j))
      ((positiveBasePresentation D).relator i) = 1 := by
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hca : Commute (Word.eval v thirteenWords.c) (Word.eval v thirteenWords.a) := by
    apply (word_commutator_eq_one_iff v _ _).mp
    simpa [thirteenPresentation, thirteenRelatorIndex, positiveBasePresentation,
      Fin.append, Fin.addCases, baseWords, thirteenSubstitution] using h 11
  have hbx : Commute (Word.eval v thirteenWords.b) (Word.eval v thirteenWords.x) := by
    apply (word_commutator_eq_one_iff v _ _).mp
    simpa [thirteenPresentation, thirteenRelatorIndex, positiveBasePresentation,
      Fin.append, Fin.addCases, baseWords, thirteenSubstitution, BaseWords.x] using h 12
  have hca' : Commute (v 0) ((v 1)⁻¹ * v 0 * v 1) := by
    rw [hv] at hca
    simpa only [eval_thirteen_c, eval_thirteen_a] using hca
  have hab : Commute (Word.eval v thirteenWords.a) (Word.eval v thirteenWords.b) := by
    rw [hv]
    simpa only [eval_thirteen_a, eval_thirteen_b] using final_commutation (v 0) (v 1) hca'
  obtain ⟨hc, hd, hf, hk, hh⟩ := eval_factor_swap_equations (v 0) (v 1)
  rw [← hv] at hc hd hf hk hh
  have hx : Word.eval v thirteenWords.x =
      (Word.eval v thirteenWords.k)⁻¹ * Word.eval v thirteenWords.f *
        Word.eval v thirteenWords.k := by
    simp [BaseWords.x, mul_assoc]
  have heh : Word.eval v thirteenWords.h =
      ((Word.eval v thirteenWords.a) ^ 2)⁻¹ *
        ((Word.eval v thirteenWords.k)⁻¹ * Word.eval v thirteenWords.f *
          Word.eval v thirteenWords.k) * (Word.eval v thirteenWords.a) ^ 2 := by
    simp [BaseWords.h, BaseWords.x, mul_assoc]
  have hdel := factor_swap_deleted_commutations
    (Word.eval v thirteenWords.c) (Word.eval v thirteenWords.d)
    (Word.eval v thirteenWords.f) (Word.eval v thirteenWords.k)
    (Word.eval v thirteenWords.a) (Word.eval v thirteenWords.b) (v 1)
    hc (hx ▸ hd) (by simpa only [eval_swapA] using hf)
    (by simpa only [eval_swapB] using hk) (heh ▸ hh) hca hab (hx ▸ hbx)
  have hdh : Commute (Word.eval v thirteenWords.d)
      (Word.eval v (Word.pow thirteenWords.h 2)) := by
    simpa only [Word.eval_pow, heh] using hdel.2.2.2.2
  intro i
  rw [← Word.eval_substitute]
  fin_cases i
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 0
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 1
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 2
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 3
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 4
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 5
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 6
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 7
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 8
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 9
  · simpa [positiveBasePresentation, positiveCoreRelators, Fin.append, Fin.addCases,
      baseWords, thirteenSubstitution, BaseWords.h, BaseWords.x] using
      (word_commutator_eq_one_iff v _ _).mpr hdh
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 10
  · simpa [positiveBasePresentation, Fin.append, Fin.addCases, baseWords,
      thirteenSubstitution] using (word_commutator_eq_one_iff v _ _).mpr hdel.1
  · simpa [positiveBasePresentation, Fin.append, Fin.addCases, baseWords,
      thirteenSubstitution] using (word_commutator_eq_one_iff v _ _).mpr hdel.2.2.1
  · simpa [positiveBasePresentation, Fin.append, Fin.addCases, baseWords,
      thirteenSubstitution] using (word_commutator_eq_one_iff v _ _).mpr hdel.2.1
  · simpa [positiveBasePresentation, Fin.append, Fin.addCases, baseWords,
      thirteenSubstitution] using (word_commutator_eq_one_iff v _ _).mpr hdel.2.2.2.1
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 11
  · simpa [positiveBasePresentation, Fin.append, Fin.addCases, baseWords,
      thirteenSubstitution] using (word_commutator_eq_one_iff v _ _).mpr hab
  · simpa [thirteenPresentation, thirteenRelatorIndex] using h 12

def factorSwapHom (D : CodeWords) :
    (positiveBasePresentation D).Group →* (thirteenPresentation D).Group :=
  (positiveBasePresentation D).homOfRelators
    (fun i => (thirteenPresentation D).evalWord (thirteenSubstitution i))
    (factorSwapRelators D (generators (thirteenPresentation D))
      ((thirteenPresentation D).relator_eq_one))

@[simp] theorem factorSwapHom_generator (D : CodeWords) (i : Fin 6) :
    factorSwapHom D (generators (positiveBasePresentation D) i) =
      (thirteenPresentation D).evalWord (thirteenSubstitution i) :=
  FP.homOfRelators_of _ _ _ i

namespace FactorSwapData

variable {D : CodeWords} (data : FactorSwapData D)

theorem relators_in_extension (i : Fin 13) :
    Word.eval data.newValues ((thirteenPresentation D).relator i) = 1 := by
  rw [thirteenPresentation_relator, data.reconstructs_word, FP.relator_eq_one, map_one]

noncomputable def toExtension : (thirteenPresentation D).Group →* data.Extension :=
  (thirteenPresentation D).homOfRelators data.newValues data.relators_in_extension

theorem composite_eq_inclusion :
    data.toExtension.comp (factorSwapHom D) = data.inclusion := by
  apply PresentedGroup.ext
  intro i
  change data.toExtension (factorSwapHom D
      (generators (positiveBasePresentation D) i)) = data.oldValues i
  rw [factorSwapHom_generator]
  exact (FP.homOfRelators_evalWord _ _ _ _).trans (data.reconstructs i)

end FactorSwapData

/-- A proper factor-swap HNN extension embeds the positive nineteen-relator
host in the explicit two-generator, thirteen-relator presentation. -/
noncomputable def factorSwapEmbedding (D : CodeWords) (data : FactorSwapData D) :
    GroupEmbedding (positiveBasePresentation D).Group (thirteenPresentation D).Group where
  hom := factorSwapHom D
  injective := by
    intro x y h
    apply data.inclusion_injective
    have hxy := congrArg data.toExtension h
    change (data.toExtension.comp (factorSwapHom D)) x =
      (data.toExtension.comp (factorSwapHom D)) y at hxy
    simpa only [data.composite_eq_inclusion] using hxy

end UniversalGroup.Embedding
