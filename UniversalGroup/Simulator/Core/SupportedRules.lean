module

public import UniversalGroup.Coding.Data

@[expose] public section

/-!
# The rule assumptions needed by the simulator normal forms

The Borisov rank-five and single-letter subgroup arguments use positivity
and both-letter support. They do not use undecidability, recognition, the
marker, or the input group. Keeping this smaller datum explicit allows the
subgroup arguments to apply to every Valiev datum.
-/

namespace UniversalGroup

/-- Evaluate a positive binary word at two group elements. This definition
agrees with the positive evaluation in the Borisov simulator. -/
def evalPositive {H : Type*} [Group H] (s₁ s₂ : H) (w : PositiveWord) : H :=
  (w.map fun i => if i = 0 then s₁ else s₂).prod

structure SupportedRules where
  F : Fin 3 → PositiveWord
  E : Fin 3 → PositiveWord
  F_support : ∀ i, ContainsBoth (F i)
  E_support : ∀ i, ContainsBoth (E i)

/-- The symmetric rewriting relation uses the same displayed orientation
as `CodeWords.rules`; individual steps may apply a rule in either direction. -/
def SupportedRules.rules (D : SupportedRules) : Set (PositiveWord × PositiveWord) :=
  Set.range (fun i => (D.E i, D.F i))

theorem containsBoth_ne_nil {w : PositiveWord} (h : ContainsBoth w) : w ≠ [] := by
  rintro rfl
  simp [ContainsBoth] at h

theorem SupportedRules.F_nonempty (D : SupportedRules) (i : Fin 3) : D.F i ≠ [] :=
  containsBoth_ne_nil (D.F_support i)

theorem SupportedRules.E_nonempty (D : SupportedRules) (i : Fin 3) : D.E i ≠ [] :=
  containsBoth_ne_nil (D.E_support i)

def CodeWords.supportedRules (D : CodeWords)
    (hF : ∀ i, ContainsBoth (D.F i)) (hE : ∀ i, ContainsBoth (D.E i)) : SupportedRules :=
  ⟨D.F, D.E, hF, hE⟩

end UniversalGroup
