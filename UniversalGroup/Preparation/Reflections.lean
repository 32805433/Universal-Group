module

public import UniversalGroup.Coding.Data
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

/-! Faithful simultaneous reflection extensions of finite presentations. -/

namespace UniversalGroup.PreparationReflections

noncomputable section
open scoped IsMulCommutative

section Permutations
variable {H : Type*} [Group H] (x : H)

def transversal : Set H := (Subgroup.exists_isComplement_right (Subgroup.zpowers x) 1).choose
theorem complementary : Subgroup.IsComplement (Subgroup.zpowers x : Set H) (transversal x) :=
  (Subgroup.exists_isComplement_right (Subgroup.zpowers x) 1).choose_spec.1
def decompose : H ≃ (Subgroup.zpowers x) × transversal x := (complementary x).equiv

/-- Reverse the cyclic coordinate of each right coset of the cyclic subgroup. -/
def reflection : Equiv.Perm H :=
  ((decompose x).trans (Equiv.prodCongr (Equiv.inv (Subgroup.zpowers x)) (Equiv.refl _))).trans
    (decompose x).symm

private theorem decompose_reflection (g : H) :
    decompose x (reflection x g) = ((decompose x g).1⁻¹,(decompose x g).2) := by
  simp only [reflection, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.inv_apply,
    Equiv.apply_symm_apply]
  rfl

@[simp] theorem reflection_squared : reflection x * reflection x = 1 := by
  apply Equiv.ext
  intro g
  apply (decompose x).injective
  change decompose x (reflection x (reflection x g)) = decompose x g
  rw [decompose_reflection, decompose_reflection]
  simp

/-- The reflection reverses the regular translation by x. -/
theorem reflection_mul (g : H) : reflection x (x*g) = x⁻¹ * reflection x g := by
  apply (decompose x).injective
  rw [decompose_reflection]
  change (((complementary x).equiv (x*g)).1⁻¹,
    ((complementary x).equiv (x*g)).2) = (complementary x).equiv (x⁻¹ * reflection x g)
  rw [Subgroup.IsComplement.equiv_mul_left_of_mem (complementary x) (Subgroup.mem_zpowers x),
    Subgroup.IsComplement.equiv_mul_left_of_mem (complementary x)
      ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))]
  have hr := decompose_reflection x g
  change (complementary x).equiv (reflection x g) =
    (((complementary x).equiv g).1⁻¹, ((complementary x).equiv g).2) at hr
  rw [hr]
  simp only [Prod.mk.injEq, and_true, mul_inv_rev]
  exact mul_comm ((decompose x g).1)⁻¹ (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x)⁻¹

/-- Left multiplication, as a faithful permutation representation. -/
def regular : H →* Equiv.Perm H := MulAction.toPermHom H H

@[simp] theorem regular_apply (h g : H) : regular h g = h*g := rfl

theorem regular_injective : Function.Injective (regular : H →* Equiv.Perm H) := by
  intro a b hab
  have h := congrArg (fun p : Equiv.Perm H => p 1) hab
  simpa only [regular_apply, mul_one] using h

/-- Both r and r*x are involutions; these equations admit a simultaneous
permutation model for every family of original group elements. -/
theorem reflection_regular_squared : (reflection x * regular x)^2 = 1 := by
  apply Equiv.ext
  intro g
  change reflection x (x * reflection x (x*g)) = g
  rw [reflection_mul x g, mul_inv_cancel_left]
  have h := congrArg (fun p : Equiv.Perm H => p g) (reflection_squared x)
  exact h

end Permutations


section Presentations
variable (Q : FP n m)

/-- The old generators and one new reflection for each of them. -/
def relators : Fin (m+(n+n)) → Word (n+n) :=
  Fin.addCases (fun i => Word.mapGenerators (Fin.castAdd n) (Q.relator i))
    (Fin.addCases (fun i => Word.pow (Word.generator (Fin.natAdd n i)) 2)
      (fun i => Word.pow (Word.product
        [Word.generator (Fin.natAdd n i), Word.generator (Fin.castAdd n i)]) 2))

def presentation : FP (n+n) (m+(n+n)) := ⟨relators Q⟩

abbrev old (i : Fin n) := generators (presentation Q) (Fin.castAdd n i)
abbrev r (i : Fin n) := generators (presentation Q) (Fin.natAdd n i)

@[simp] theorem relator_old (i : Fin m) :
    (presentation Q).relator (Fin.castAdd (n+n) i) =
      Word.mapGenerators (Fin.castAdd n) (Q.relator i) := by simp only [presentation,relators,Fin.addCases_left]
@[simp] theorem relator_r (i : Fin n) :
    (presentation Q).relator (Fin.natAdd m (Fin.castAdd n i)) =
      Word.pow (Word.generator (Fin.natAdd n i)) 2 := by simp only [presentation,relators,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem relator_pair (i : Fin n) :
    (presentation Q).relator (Fin.natAdd m (Fin.natAdd n i)) =
      Word.pow (Word.product [Word.generator (Fin.natAdd n i), Word.generator (Fin.castAdd n i)]) 2 := by
  simp only [presentation,relators,Fin.addCases_right]

theorem r_squared (i : Fin n) : r Q i ^ 2 = 1 := by
  have h := (presentation Q).relator_eq_one (Fin.natAdd m (Fin.castAdd n i))
  simpa only [relator_r, FP.evalWord, Word.eval_pow, Word.eval_generator,r,generators] using h

theorem pair_squared (i : Fin n) : (r Q i * old Q i)^2 = 1 := by
  have h := (presentation Q).relator_eq_one (Fin.natAdd m (Fin.natAdd n i))
  simpa only [relator_pair, FP.evalWord, Word.eval_pow, Word.eval_product,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Word.eval_generator, mul_one,r,old,generators] using h

/-- The canonical map from the original presentation. -/
def ofOld : Q.Group →* (presentation Q).Group := Q.homOfRelators (old Q) (by
  intro i
  have h := (presentation Q).relator_eq_one (Fin.castAdd (n+n) i)
  rw [relator_old, FP.evalWord, Word.eval_mapGenerators] at h
  exact h)

@[simp] theorem ofOld_generator (i : Fin n) : ofOld Q (generators Q i) = old Q i := by
  exact Q.homOfRelators_of (old Q) _ i

def permValues : Fin (n+n) → Equiv.Perm Q.Group :=
  Fin.addCases (fun i => regular (generators Q i)) (fun i => reflection (generators Q i))

/-- All reflection relations hold simultaneously in the regular permutation model. -/
def model : (presentation Q).Group →* Equiv.Perm Q.Group :=
  (presentation Q).homOfRelators (permValues Q) (by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [relator_old, Word.eval_mapGenerators]
      have he : permValues Q ∘ Fin.castAdd n = regular ∘ generators Q := by
        funext k
        simp [permValues]
      rw [he, ← Word.map_eval]
      change regular (Q.evalWord (Q.relator j)) = 1
      rw [FP.relator_eq_one, map_one]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · rw [relator_r,Word.eval_pow,Word.eval_generator]
        simpa only [permValues, Fin.addCases_right, pow_two] using reflection_squared (generators Q k)
      · rw [relator_pair,Word.eval_pow,Word.eval_product]
        simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
          Word.eval_generator,permValues,Fin.addCases_left,Fin.addCases_right,mul_one]
          using reflection_regular_squared (generators Q k))

theorem model_comp_ofOld : (model Q).comp (ofOld Q) = regular := by
  apply PresentedGroup.ext
  intro i
  change model Q (ofOld Q (generators Q i)) = regular (generators Q i)
  rw [ofOld_generator, model, old, generators, FP.homOfRelators_of]
  simp only [permValues, Fin.addCases_left]

/-- Simultaneously adjoining these reflections preserves the original group. -/
theorem ofOld_injective : Function.Injective (ofOld Q) := by
  intro a b hab
  apply regular_injective
  have h := congrArg (model Q) hab
  simpa only [← MonoidHom.comp_apply,model_comp_ofOld] using h

/-- The new group is generated by the indicated involutions. -/
def involutions : Fin (n+n) → (presentation Q).Group :=
  Fin.addCases (r Q) (fun i => r Q i * old Q i)

theorem involutions_squared (i : Fin (n+n)) : involutions Q i ^ 2 = 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [involutions,Fin.addCases_left] using r_squared Q j
  · simpa only [involutions,Fin.addCases_right] using pair_squared Q j

theorem involutions_generate : Subgroup.closure (Set.range (involutions Q)) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of (presentation Q).relSet]
  rw [Subgroup.closure_le]
  rintro _ ⟨i,rfl⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change old Q j ∈ Subgroup.closure (Set.range (involutions Q))
    have hr : r Q j ∈ Subgroup.closure (Set.range (involutions Q)) :=
      Subgroup.subset_closure ⟨Fin.castAdd n j, by simp only [involutions,Fin.addCases_left,r,generators]⟩
    have hp : r Q j * old Q j ∈ Subgroup.closure (Set.range (involutions Q)) :=
      Subgroup.subset_closure ⟨Fin.natAdd n j, by simp only [involutions,Fin.addCases_right,r,generators]⟩
    simpa only [inv_mul_cancel_left] using
      (Subgroup.closure (Set.range (involutions Q))).mul_mem
        ((Subgroup.closure (Set.range (involutions Q))).inv_mem hr) hp
  · exact Subgroup.subset_closure ⟨Fin.castAdd n j, by simp only [involutions,Fin.addCases_left,r,generators]⟩

end Presentations

end
end UniversalGroup.PreparationReflections
