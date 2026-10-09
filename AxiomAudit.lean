module

import UniversalGroup
public meta import Lean

/-!
# Axiom audit of the thirteen-relator construction

Every checkpoint must use only `propext`, `Classical.choice`, and `Quot.sound`.
The checkpoints cover preparation, both product embeddings, compression,
and the public universal-group theorem.
-/

-- Print a checkpoint's transitive axioms and reject any unpermitted axiom.
open Lean Elab Command in
elab "#audit_axioms " target:ident : command => do
  let name := target.getId
  unless ((← getEnv).find? name).isSome do
    throwError "Unknown audit checkpoint: {name}"
  let axioms ← Lean.collectAxioms name
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "{name} depends on unpermitted axiom {axiomName}"
  logInfo m!"{name} depends on axioms: {axioms}"

#audit_axioms UniversalGroup.Embedding.factor_swap_substitutions
#audit_axioms UniversalGroup.Embedding.factor_swap_deleted_commutations
#audit_axioms UniversalGroup.Embedding.final_commutation
#audit_axioms UniversalGroup.Embedding.eval_factor_swap_equations
#audit_axioms UniversalGroup.Embedding.factorSwapRelators
#audit_axioms UniversalGroup.Embedding.factorSwapEmbedding
#audit_axioms UniversalGroup.Embedding.RowTriple.changeBasis_injective
#audit_axioms UniversalGroup.Embedding.compressionTriple_injective
#audit_axioms UniversalGroup.Embedding.RowModel.toModel_injective
#audit_axioms UniversalGroup.Embedding.PositiveHost.CoreSymmetry.twistHom
#audit_axioms UniversalGroup.Embedding.PositiveHost.equivK
#audit_axioms UniversalGroup.Embedding.PositiveHost.HStage.inputEmbedding
#audit_axioms UniversalGroup.Embedding.PositiveHost.HStage.commutes_d_square
#audit_axioms UniversalGroup.Embedding.PositiveHost.HGrid.product_injective
#audit_axioms UniversalGroup.Embedding.PositiveHost.BaseModelLaws.relators
#audit_axioms UniversalGroup.Embedding.PositiveHost.InputEmbedding.embedding
#audit_axioms UniversalGroup.Embedding.positiveSource_commute
#audit_axioms UniversalGroup.Embedding.positiveTarget_commute
#audit_axioms UniversalGroup.Embedding.positiveSource_h2
#audit_axioms UniversalGroup.Embedding.positiveTarget_A
#audit_axioms UniversalGroup.Embedding.Construction.embedding
#audit_axioms UniversalGroup.Embedding.Construction.universal

#audit_axioms UniversalGroup.Embedding.prepare_protected_input
#audit_axioms UniversalGroup.Embedding.positive_source_injective
#audit_axioms UniversalGroup.Embedding.positive_target_injective
#audit_axioms UniversalGroup.Embedding.positive_factorSwapData
#audit_axioms UniversalGroup.Embedding.exists_construction
#audit_axioms UniversalGroup.Embedding.exists_universal_datum
#audit_axioms UniversalGroup.exists_two_generator_thirteen_relator_universal_group

#audit_axioms UniversalGroup.Embedding.MarkedQuotient.exists_prepared_with_values
#audit_axioms UniversalGroup.Embedding.ProtectedAction.relation
#audit_axioms UniversalGroup.Embedding.ProtectedAction.triple_injective
#audit_axioms UniversalGroup.Embedding.PositiveHost.SourceFree.freeTriple_injective
#audit_axioms UniversalGroup.Embedding.PositiveHost.SourceQuotient.hom
#audit_axioms UniversalGroup.Embedding.PositiveHost.Source.injective_of_coordinates
#audit_axioms UniversalGroup.Embedding.RowProduct.product_injective
#audit_axioms UniversalGroup.Embedding.PositiveHost.Target.product_injective
