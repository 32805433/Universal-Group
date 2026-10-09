module

public import UniversalGroup.Simulator.Core.CStage

@[expose] public section

/-! Coefficient classification consumed by the signed-outer-word recognition induction. -/
namespace UniversalGroup
namespace BorisovCStage
noncomputable section

theorem thueStep_rule_forward (datum : UniversalGroup.SupportedRules)
    (l r : List (Fin 2)) (i : Fin 3) :
    UniversalGroup.PositiveStep datum.rules
      (l ++ datum.F i ++ r) (l ++ datum.E i ++ r) := by
  exact ⟨l, r, datum.E i, datum.F i, ⟨i, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem thueStep_rule_backward (datum : UniversalGroup.SupportedRules)
    (l r : List (Fin 2)) (i : Fin 3) :
    UniversalGroup.PositiveStep datum.rules
      (l ++ datum.E i ++ r) (l ++ datum.F i ++ r) := by
  exact ⟨l, r, datum.E i, datum.F i, ⟨i, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

end
end BorisovCStage
namespace BorisovLemma4Pinch
open BorisovCStage
noncomputable section
/-- Borisov's Assertion V in the exact coefficient form consumed by Lemma 4.
An `U`-coefficient is transported by `cEquiv`; a `V`-coefficient is
transported by its inverse.  In both cases the positive middle word changes
by finitely many (in the published proof, at most one) Thue steps. -/
structure PinchClassification (datum : UniversalGroup.SupportedRules)
    (hfree : RankFiveFree datum) : Prop where
  source : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (hmem : BorisovHNNModel.d3 ^ f * positive3 Q *
        BorisovHNNModel.e3 ^ r ∈ U datum),
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      UniversalGroup.PositiveEq datum.rules Q Q' ∧
      ((cEquiv datum hfree
        ⟨BorisovHNNModel.d3 ^ f * positive3 Q *
          BorisovHNNModel.e3 ^ r, hmem⟩ : V datum) :
            BorisovHNNModel.Gamma3) =
        BorisovHNNModel.d3 ^ f' * positive3 Q' *
          BorisovHNNModel.e3 ^ r'
  target : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (hmem : BorisovHNNModel.d3 ^ f * positive3 Q *
        BorisovHNNModel.e3 ^ r ∈ V datum),
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      UniversalGroup.PositiveEq datum.rules Q Q' ∧
      (((cEquiv datum hfree).symm
        ⟨BorisovHNNModel.d3 ^ f * positive3 Q *
          BorisovHNNModel.e3 ^ r, hmem⟩ : U datum) :
            BorisovHNNModel.Gamma3) =
        BorisovHNNModel.d3 ^ f' * positive3 Q' *
          BorisovHNNModel.e3 ^ r'


end
end BorisovLemma4Pinch
end UniversalGroup
