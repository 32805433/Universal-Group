module

public import UniversalGroup.Simulator.Data
public import UniversalGroup.Foundations.Amalgam.Centralizing

@[expose] public section

/-!
# The input amalgam of the host construction

Adjoin the input group to the simulator so that it centralizes the four grid
letters. The generic amalgam embedding supplies the initial faithful stage;
the subsequent `ell,h,a,b` extensions lead to the nineteen-relator host.
-/

namespace UniversalGroup


/-- The four grid letters in the simulator before adjoining the input.
The first is `x₀ = k⁻¹ f k`; the others are the images of `x₁,x₂,x₃` in `L`. -/
def simulatorGridValues (D : CodeWords) : Fin 4 → (simulatorK D).Group :=
  Fin.cons
    ((generators (simulatorK D) 7)⁻¹ * generators (simulatorK D) 5 *
      generators (simulatorK D) 7)
    (fun i => simulatorInclusion D ((simulatorL D).evalWord (simulatorLWords.x D i)))

def simulatorGrid (D : CodeWords) : Subgroup (simulatorK D).Group :=
  Subgroup.closure (Set.range (simulatorGridValues D))

/-- The concrete changed amalgam `M_*` of the construction. -/
abbrev InputAmalgam (G : PreparedInput) (D : CodeWords) :=
  CentralizingAmalgam.Model (simulatorGrid D) G.presentation.Group

def inputAmalgamEmbedding (G : PreparedInput) (D : CodeWords) :
    GroupEmbedding G.presentation.Group (InputAmalgam G D) :=
  ⟨CentralizingAmalgam.ofInput (simulatorGrid D) G.presentation.Group,
    CentralizingAmalgam.ofInput_injective (simulatorGrid D) G.presentation.Group⟩

/-- The eight commutations adjoined in the changed-amalgam construction. -/
theorem inputAmalgam_commute (G : PreparedInput) (D : CodeWords)
    (i : Fin 2) (j : Fin 4) :
    Commute ((inputAmalgamEmbedding G D).hom (generators G.presentation i))
      (CentralizingAmalgam.ofBase (simulatorGrid D) G.presentation.Group
        (simulatorGridValues D j)) := by
  exact (CentralizingAmalgam.commute (simulatorGrid D) G.presentation.Group
    ⟨simulatorGridValues D j, Subgroup.subset_closure ⟨j, rfl⟩⟩
    (generators G.presentation i)).symm

end UniversalGroup
