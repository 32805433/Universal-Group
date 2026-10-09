module

public import UniversalGroup.Preparation.ReflectionStage
public import UniversalGroup.Preparation.TwoGenerators

@[expose] public section

/-!
# Reflection input for two-generator preparation

The reflection extension provides an order-four element and an embedded free
family. These satisfy the marked input interface used by the two-generator
preparation and its quotient map.
-/
namespace UniversalGroup.PreparationReflectionInput
noncomputable section

variable (Q : FP n m)

def input : PreparationTwoGenerators.Input (PreparationReflectionStage.Model Q) (n+n+1) where
  u := PreparationReflectionStage.u Q
  fourthPower := PreparationReflectionStage.fourthPower Q
  j := PreparationReflectionStage.j Q
  injective := PreparationReflectionStage.j_injective Q
  rho := PreparationReflectionStage.rho Q
  rho_u := PreparationReflectionStage.rho_u Q
  rho_j := PreparationReflectionStage.rho_j Q
  generates := PreparationReflectionStage.generates Q

end
end UniversalGroup.PreparationReflectionInput
