module

public import UniversalGroup.Higman.EffectiveEmbedding.Presentation
public import UniversalGroup.Computability.Enumerable

@[expose] public section

/-! Recursive enumerability is preserved by the explicit countable HNN embedding. -/
namespace UniversalGroup.EffectiveEmbeddingRecursive
noncomputable section
open EffectiveEmbeddingWords EffectiveEmbeddingPresentation

theorem relations_enumerable (R : RecursivePresentation ℕ) :
    REPred (fun w=>w∈relations R) := by
  have hs : REPred (fun p : RawWord × RawWord => p.2∈R.relators ∧ shiftWord p.2=p.1) :=
    RecursiveEnumerable.and
      (RecursiveEnumerable.comp R.enumerable Computable.snd)
      (Primrec.eq.comp (shiftWord_primrec.comp Primrec.snd) Primrec.fst).computablePred.to_re
  have ht : PrimrecPred (fun p : RawWord × ℕ => hnnWord p.2=p.1) :=
    Primrec.eq.comp (hnnWord_primrec.comp Primrec.snd) Primrec.fst
  exact RecursiveEnumerable.or (RecursiveEnumerable.exists_re hs)
    (RecursiveEnumerable.exists_of_primrec ht)

def presentation (R : RecursivePresentation ℕ) : RecursivePresentation ℕ :=
  ⟨relations R,relations_enumerable R⟩

def equiv (R : RecursivePresentation ℕ) : (presentation R).Group ≃* EffectiveEmbeddingHNN.Host R :=
  EffectiveEmbeddingPresentation.equiv R

def embedding (R : RecursivePresentation ℕ) : GroupEmbedding R.Group (presentation R).Group where
  hom := (equiv R).symm.toMonoidHom.comp (EffectiveEmbeddingHNN.embedding R)
  injective := (equiv R).symm.injective.comp (EffectiveEmbeddingHNN.embedding_injective R)

def generators (R : RecursivePresentation ℕ) : FreeGroup (Fin 2) →* (presentation R).Group :=
  (equiv R).symm.toMonoidHom.comp (EffectiveEmbeddingHNN.generators R)

theorem generators_surjective (R : RecursivePresentation ℕ) : Function.Surjective (generators R) :=
  (equiv R).symm.surjective.comp (EffectiveEmbeddingHNN.generators_surjective R)

end
end UniversalGroup.EffectiveEmbeddingRecursive
