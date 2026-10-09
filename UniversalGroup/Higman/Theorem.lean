module

public import UniversalGroup.Higman.EffectiveEmbedding.Recursive
public import UniversalGroup.Computability.Generators
public import UniversalGroup.Higman.SignedCover
public import UniversalGroup.Higman.Simulator.Embedding
public import UniversalGroup.Higman.Recognizer.TriangularRecognizer
public import UniversalGroup.Higman.Recognizer.CodeRecognizer

@[expose] public section

/-!
# Higman embedding and the universal finitely presented input

The effective presentation of the universal free product is constructed in
`Enumeration`. The effective two-generator embedding and Higman embedding
give the finite host.
-/

namespace UniversalGroup.HigmanCompletion

variable {n : ℕ}

/-- A supported finite simulator recognizing the positive word problem of
the signed cover yields the original finite-presentation embedding statement. -/
theorem exists_FP_of_recognizer (R : RecursivePresentation (Fin n))
    (D : HigmanSimulatorB.Data (n+n))
    (hD : ∀ g : FreeGroup (Fin (n+n)),
      HigmanSimulatorB.Accepted D g ↔ g ∈ PositiveKernel.elements (HigmanAssembly.cover R)) :
    ∃ a b : ℕ, ∃ P : FP a b, Nonempty (GroupEmbedding R.Group P.Group) := by
  apply HigmanAssembly.exists_FP_of_benign_positive_diagonal R
  have hs : {g | HigmanSimulatorB.Accepted D g} =
      PositiveKernel.elements (HigmanAssembly.cover R) := Set.ext hD
  rw [← hs]
  exact HigmanSimulatorB.diagonal_benign D

end UniversalGroup.HigmanCompletion

namespace UniversalGroup

/-- **Effective HNN embedding theorem.** The countably generated
recursive input embeds into a two-generator recursively presented group.
Preservation of recursive enumerability is part of this statement. -/
theorem effective_two_generator_embedding (R : RecursivePresentation ℕ) :
    ∃ S : RecursivePresentation (Fin 2),
      Nonempty (GroupEmbedding R.Group S.Group) := by
  obtain ⟨S, ⟨e⟩⟩ := RecursiveGeneratorTransfer.exists_equiv_of_surjective
    (EffectiveEmbeddingRecursive.presentation R) (EffectiveEmbeddingRecursive.generators R)
    (EffectiveEmbeddingRecursive.generators_surjective R)
  exact ⟨S, ⟨(EffectiveEmbeddingRecursive.embedding R).trans
    (GroupEmbedding.ofEquiv e.symm)⟩⟩

/-- **Higman embedding theorem.** A finitely generated recursively
presented group embeds into a finitely presented group. -/
theorem higman_embedding (R : RecursivePresentation (Fin n)) :
    ∃ a b : ℕ, ∃ P : FP a b,
      Nonempty (GroupEmbedding R.Group P.Group) := by
  obtain ⟨T⟩ := HigmanTriangularRecognizer.exists_data
    (HigmanAssembly.language_enumerable R)
    (by simp [HigmanAssembly.language, PositiveKernel.positive])
  let W := BooneCollinsWords.words T.r T.t T.lhs T.rhs
  have hF := BooneCollinsWords.words_F_support T.r T.t T.lhs T.rhs
  have hE := BooneCollinsWords.words_E_support T.r T.t T.lhs T.rhs
  apply HigmanCompletion.exists_FP_of_recognizer R
    (HigmanCodeRecognizer.data T.input (2*T.t) W hF hE)
  exact HigmanCodeRecognizer.accepted_iff_elements T.input (2*T.t) W hF hE
    (HigmanAssembly.cover R) (fun w => (T.binary_recognizes w).symm)

/-- The single universal finitely presented input used by the final theorem.
The finite presentation is chosen before the universally quantified input. -/
theorem exists_finitely_presented_universal_group :
    ∃ n m : ℕ, ∃ P : FP n m, IsUniversal P.Group := by
  obtain ⟨R, ⟨eR⟩⟩ := allFinitePresentations_recursive
  obtain ⟨S, ⟨eS⟩⟩ := effective_two_generator_embedding R
  obtain ⟨n, m, P, ⟨eP⟩⟩ := higman_embedding S
  refine ⟨n, m, P, ?_⟩
  exact allFinitePresentations_universal.of_embedding
    (((GroupEmbedding.ofEquiv eR).trans eS).trans eP)

end UniversalGroup
