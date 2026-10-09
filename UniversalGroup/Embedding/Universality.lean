module

public import UniversalGroup.Embedding.AttachingMaps
public import UniversalGroup.Embedding.ProtectedInput.Theorem
public import UniversalGroup.Coding.Valiev
public import UniversalGroup.Simulator.Intersections
public import UniversalGroup.Higman.Theorem

@[expose] public section

/-!
# Assembly of the thirteen-relator universal group

The protected preparation, faithful host, and five-equation factor swap
combine to embed any finite presentation in a two-generator presentation
with thirteen relators. Applying this to Higman's universal input proves
the unconditional universal-group theorem.
-/

namespace UniversalGroup.Embedding

/-- The presentations and embeddings used in the final composition. -/
structure Construction (Q : FP n m) where
  prepared : PreparedInput
  inputEmbedding : GroupEmbedding Q.Group prepared.presentation.Group
  datum : ValievDatum prepared
  hostEmbedding : GroupEmbedding prepared.presentation.Group
    (positiveBasePresentation datum.toCodeWords).Group
  factorSwap : FactorSwapData datum.toCodeWords

/-- Assemble the main construction from its explicitly isolated upstream steps. -/
theorem exists_construction (Q : FP n m) : Nonempty (Construction Q) := by
  obtain ⟨G, ⟨inputEmbedding⟩, hp⟩ := prepare_protected_input Q
  obtain ⟨D⟩ := exists_valievDatum G
  have hi := valiev_intersections G D
  let hostEmbedding := PositiveHost.InputEmbedding.embedding G D hi
  obtain ⟨data⟩ := positive_factorSwapData G D hi hp
  exact ⟨⟨G, inputEmbedding, D, hostEmbedding, data⟩⟩

namespace Construction

variable {Q : FP n m} (C : Construction Q)

def presentation : FP 2 13 := thirteenPresentation C.datum.toCodeWords

/-- Given the construction data, the input embeds in the literal
two-generator thirteen-relator presentation. -/
noncomputable def embedding : GroupEmbedding Q.Group C.presentation.Group :=
  (C.inputEmbedding.trans C.hostEmbedding).trans
    (factorSwapEmbedding C.datum.toCodeWords C.factorSwap)

theorem universal (hQ : IsUniversal Q.Group) : IsUniversal C.presentation.Group :=
  hQ.of_embedding C.embedding

end Construction

/-- Choose one finitely presented universal input before constructing the host;
the final presentation consequently works for every finite presentation. -/
theorem exists_universal_datum :
    ∃ D : CodeWords, IsUniversal (thirteenPresentation D).Group := by
  obtain ⟨n, m, Q, hQ⟩ := exists_finitely_presented_universal_group
  obtain ⟨C⟩ := exists_construction Q
  exact ⟨C.datum.toCodeWords, C.universal hQ⟩

end UniversalGroup.Embedding
