module

public import UniversalGroup.Simulator.Core.ContextNormalForm
public import UniversalGroup.Simulator.Core.Lemma4Pinch
public import UniversalGroup.Simulator.Core.Mod5.Sparsity
public import UniversalGroup.Simulator.Core.PositiveWords

@[expose] public section

/-!
# Positivity and semigroup recognition in the simulator core

An arbitrary signed word on the stable generators lying in the double coset
`<c,d> * P * <c,e>` of a positive word is itself positive, and its positive
spelling is equivalent to `P` under the three semigroup rules. The proof uses
only support of the rule words, the proved coefficient classifier, and Britton
normal forms. No Valiev intersection hypothesis is used.
-/

namespace UniversalGroup.SimulatorRecognitionCore

open BorisovCStage BorisovContextNormalForm

noncomputable section

/-- The previously proved rank-five intersections supply the context
normal-form hypotheses without any recognition assumption. -/
theorem baseIntersections (R : SupportedRules) : BaseIntersections R :=
  ⟨BorisovInputsBridge.U_inf_DE3 R, BorisovInputsBridge.V_inf_DE3 R⟩

/-- The c-stage separator with an arbitrary signed outer word. -/
theorem signed_recognition (R : SupportedRules) (hfree : RankFiveFree R) :
    BorisovLemma4 R hfree :=
  BorisovLemma4Pinch.borisovLemma4_of_classification R hfree
    (BorisovModFiveSparsity.pinchClassification R hfree)

/-- A signed stable word in a positive double coset has a positive spelling
related by the semigroup rules to the specified middle word. -/
theorem of_context_factorization
    (R : SupportedRules) (hfree : RankFiveFree R)
    (W : FreeGroup (Fin 2)) (P : PositiveWord)
    (u v : Gamma2 R hfree) (hu : u ∈ CD R hfree) (hv : v ∈ CE R hfree)
    (h : sLift2 R hfree W = u * positive2 R hfree P * v) :
    ∃ Q : PositiveWord, W = positiveFree Q ∧ PositiveEq R.rules Q P := by
  rcases exists_leftContext_of_mem_CD R hfree (baseIntersections R) hu with ⟨L, hL⟩
  rcases exists_rightContext_of_mem_CE R hfree (baseIntersections R) hv with ⟨V, hV⟩
  have heq : Lemma4Equation R hfree W P L V := by
    change (sLift2 R hfree W)⁻¹ * leftValue R hfree L *
      positive2 R hfree P * rightValue R hfree V = 1
    rw [hL, hV]
    exact (equation_iff_factorization _ _ _ _).2 h
  rcases signed_recognition R hfree W P L V heq with ⟨Q, hW, hPQ⟩
  exact ⟨Q, hW, PositiveEq.symm hPQ⟩


end

end UniversalGroup.SimulatorRecognitionCore
