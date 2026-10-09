module

public import UniversalGroup.Embedding.Universality

@[expose] public section

/-!
# A two-generator thirteen-relator universal group

The protected preparation, faithful host, literal compression, and universal
assembly are proved without admissions. See `AxiomAudit.lean` and
`FORMALIZATION.md` for the audit checkpoints and proof guide.
-/

namespace UniversalGroup

/-- There is a presentation on two generator slots and thirteen relator slots
whose group contains every finitely presented group. -/
theorem exists_two_generator_thirteen_relator_universal_group :
    ∃ P : FP 2 13,
      ∀ (n m : ℕ) (Q : FP n m),
        ∃ f : PresentedGroup Q.relSet →* PresentedGroup P.relSet,
          Function.Injective f := by
  obtain ⟨D, hD⟩ := UniversalGroup.Embedding.exists_universal_datum
  exact ⟨UniversalGroup.Embedding.thirteenPresentation D, hD⟩

end UniversalGroup
