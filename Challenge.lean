module

public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

/-! Standalone comparator challenge; the proof hole is intentional. -/

namespace UniversalGroup

/-- A letter in a word on `n` generators. The Boolean records the sign. -/
abbrev SignedGenerator (n : ℕ) := Fin n × Bool

/-- A word on `n` generators. -/
abbrev Word (n : ℕ) := List (SignedGenerator n)

/--
Syntax for a finite group presentation with exactly `n` generator slots and
exactly `m` relator slots.
-/
structure FP (n m : ℕ) where
  relator : Fin m → Word n

namespace FP

/-- The relators of a finite presentation, interpreted in the free group. -/
def relSet (P : FP n m) : Set (FreeGroup (Fin n)) :=
  Set.range fun i => FreeGroup.mk (P.relator i)

end FP

/-- There is a presentation on two generator slots and thirteen relator slots
whose group contains every finitely presented group. -/
theorem exists_two_generator_thirteen_relator_universal_group :
    ∃ P : FP 2 13,
      ∀ (n m : ℕ) (Q : FP n m),
        ∃ f : PresentedGroup Q.relSet →* PresentedGroup P.relSet,
          Function.Injective f := by
  sorry

end UniversalGroup
