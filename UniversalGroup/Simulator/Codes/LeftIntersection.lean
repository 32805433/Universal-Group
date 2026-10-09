module

public import UniversalGroup.Simulator.Codes.Free

@[expose] public section

/-!
# Exact single-letter intersections of the coded free subgroup

The permutation decoder also controls subgroup intersections. For the
first single-letter subgroup, its two ambient generators preserve exactly
the decoder states carrying powers of the designated `x₁` basis element.
-/

namespace UniversalGroup.CodeSubgroups

noncomputable section

/-- Permutations preserving membership in a set in both directions. -/
def preserves {α : Type*} (S : Set α) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x, x ∈ S ↔ p x ∈ S}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro p q hp hq x
    exact (hq x).trans (hp (q x))
  inv_mem' := by
    intro p hp x
    simpa using (hp (p⁻¹ x)).symm

private def leftCoordinates : Subgroup (FreeGroup (Fin 5)) :=
  Subgroup.closure ({FreeGroup.of 2} : Set (FreeGroup (Fin 5)))

private def leftStates : Set (State (FreeGroup (Fin 5))) :=
  {p | (p.1 = 0 ∨ p.1 = 3) ∧ p.2 ∈ leftCoordinates}

/-- The ambient free subgroup on `s₁,f`. -/
def leftAmbient : Subgroup (FreeGroup (Fin 4)) :=
  Subgroup.closure ({FreeGroup.of 0, FreeGroup.of 2} : Set (FreeGroup (Fin 4)))

private theorem left_generator_mem : (FreeGroup.of 2 : FreeGroup (Fin 5)) ∈ leftCoordinates :=
  Subgroup.subset_closure (Set.mem_singleton _)

private theorem leftAmbient_le_preserver (D : CodeWords) :
    leftAmbient ≤ (preserves leftStates).comap (aRep D) := by
  rw [leftAmbient, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · change ∀ p, p ∈ leftStates ↔ aRep D (FreeGroup.of 0) p ∈ leftStates
    intro ⟨i, w⟩
    fin_cases i <;> simp [leftStates, aRep, aRepValues, letterA]
    exact (leftCoordinates.mul_mem_cancel_left left_generator_mem).symm
  · rcases hx with rfl
    change ∀ p, p ∈ leftStates ↔ aRep D (FreeGroup.of 2) p ∈ leftStates
    intro ⟨i, w⟩
    fin_cases i <;> simp [leftStates, aRep, aRepValues]

theorem aRep_word_action (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r)
    (w : FreeGroup (Fin 5)) : ActsAs (aRep D (aFreeLift D w)) w := by
  induction w using FreeGroup.induction_on with
  | one => simpa only [map_one] using (actsAs_one (H := FreeGroup (Fin 5)))
  | of i => simpa [aFreeLift] using aRep_actions D r hcode i
  | inv_of i hi => simpa only [map_inv] using hi.inv
  | mul u v hu hv => simpa only [map_mul] using hu.mul hv

/-- If a word in the displayed `A` basis lies in `⟨s₁,f⟩`, it is a power of `x₁`. -/
theorem aFreeLift_mem_left_iff (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r)
    (w : FreeGroup (Fin 5)) :
    aFreeLift D w ∈ leftAmbient ↔
      w ∈ Subgroup.closure ({FreeGroup.of 2} : Set (FreeGroup (Fin 5))) := by
  constructor
  · intro hw
    have hpres := leftAmbient_le_preserver D hw
    have hbase : (0, (1 : FreeGroup (Fin 5))) ∈ leftStates := by simp [leftStates]
    have himage := (hpres (0, 1)).mp hbase
    rw [aRep_word_action D r hcode w 1] at himage
    simpa [leftStates, leftCoordinates] using himage
  · intro hw
    rcases Subgroup.mem_closure_singleton.mp hw with ⟨n, rfl⟩
    rw [map_zpow]
    apply leftAmbient.zpow_mem
    change aFreeValues D 2 ∈ leftAmbient
    have ha : (FreeGroup.of 0 : FreeGroup (Fin 4)) ∈ leftAmbient :=
      Subgroup.subset_closure (by simp)
    have hf : (FreeGroup.of 2 : FreeGroup (Fin 4)) ∈ leftAmbient :=
      Subgroup.subset_closure (by simp)
    exact leftAmbient.mul_mem (leftAmbient.mul_mem (leftAmbient.inv_mem hf) ha) hf

/-- The exact first single-letter intersection in the free four-letter group. -/
theorem aFree_inter_left (D : CodeWords) (r : ℕ) (hcode : D.code = valievCode r) :
    (aFreeLift D).range ⊓ leftAmbient =
      Subgroup.closure ({aFreeValues D 2} : Set (FreeGroup (Fin 4))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := hx.1
    have hw := (aFreeLift_mem_left_iff D r hcode w).mp hx.2
    rcases Subgroup.mem_closure_singleton.mp hw with ⟨n, rfl⟩
    rw [map_zpow]
    apply Subgroup.zpow_mem
    exact Subgroup.subset_closure (Set.mem_singleton _)
  · rw [Subgroup.closure_le, Set.singleton_subset_iff]
    refine ⟨⟨FreeGroup.of 2, by simp [aFreeLift]⟩, ?_⟩
    apply (aFreeLift_mem_left_iff D r hcode (FreeGroup.of 2)).mpr
    exact Subgroup.subset_closure (Set.mem_singleton _)

end
end UniversalGroup.CodeSubgroups
