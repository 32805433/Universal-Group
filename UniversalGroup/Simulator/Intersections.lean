module

public import UniversalGroup.Simulator.Recognition.AIntersection
public import UniversalGroup.Simulator.Recognition.BIntersection

@[expose] public section

/-!
# Valiev's simulator intersection theorem

The presentations and subgroup interfaces live in `Simulator.Data` so that
normal-form and recognition proofs can be imported here without a cycle.
-/

namespace UniversalGroup

/-- **Valiev's intersection theorem (Lemma 5.1).** Recognition in the core,
literal code-marker cancellation, and induction on reduced HNN words give
both exact intersections. -/
theorem valiev_intersections (G : PreparedInput) (D : ValievDatum G) :
    ValievIntersections G D := by
  exact ⟨SimulatorIntersectionAUpper.intersection_eq G D,
    SimulatorIntersectionBUpper.intersection_eq G D⟩

end UniversalGroup
