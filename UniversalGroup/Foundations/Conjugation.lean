module

public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Conjugation identities

These identities recover elements and commutation relations from their
simultaneous conjugates. They are used in the host and factor-swap construction.
-/

namespace UniversalGroup

variable {G : Type*} [Group G]

/-- Recover an element from its conjugate by a stable letter. -/
theorem eq_conjugate_of_inv_conjugate_eq {g y z : G}
    (h : g⁻¹ * y * g = z) : y = g * z * g⁻¹ := by
  calc
    y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [h]

/-- Commutation can be pulled back through simultaneous conjugation. -/
theorem commute_of_inv_conjugates {g y z : G}
    (h : Commute (g⁻¹ * y * g) (g⁻¹ * z * g)) : Commute y z := by
  apply (Commute.conj_iff g⁻¹).mp
  simpa only [inv_inv] using h

end UniversalGroup
