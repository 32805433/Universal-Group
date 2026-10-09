module

public import UniversalGroup.Simulator.Core.IntersectionsTransport

@[expose] public section

/-!
# Free subgroups of the simulator core

The rank-five associated subgroups meet the free base on `d,e` trivially.
Restricting the `c` extension to this base therefore gives a free group on
the three named elements `c,d,e`.
-/

namespace UniversalGroup.CoreFreeSubgroups

open BorisovCStage BorisovHNNModel BorisovInputsBridge HNNLemmas

noncomputable section

variable (R : SupportedRules)

abbrev Core := Gamma2 R (rankFiveFree R)

private theorem associated_eq_one {A : Subgroup Gamma3}
    (hA : A ⊓ DE3 = ⊥) (a : A) (ha : (a : Gamma3) ∈ DE3) : a = 1 := by
  apply Subtype.ext
  have h : (a : Gamma3) ∈ (⊥ : Subgroup Gamma3) := by
    rw [← hA]
    exact ⟨a.property, ha⟩
  exact h

/-- Compatibility for restricting the core HNN extension to its free base. -/
theorem cEquiv_mem_DE3_iff (a : U R) :
    (a : Gamma3) ∈ DE3 ↔ (cEquiv R (rankFiveFree R) a : Gamma3) ∈ DE3 := by
  constructor
  · intro ha
    have ha1 := associated_eq_one (U_inf_DE3 R) a ha
    simp [ha1]
  · intro ha
    have ha1 := associated_eq_one (V_inf_DE3 R) (cEquiv R (rankFiveFree R) a) ha
    have h : a = 1 := (cEquiv R (rankFiveFree R)).injective (by simpa using ha1)
    simp [h]

/-- The HNN extension restricted to the subgroup on `d,e`. -/
abbrev Restricted :=
  HNNExtension DE3 (restrictedA (A := U R) DE3) (restrictedB (B := V R) DE3)
    (restrictedPhi DE3 (cEquiv_mem_DE3_iff R))

private def baseEquiv : Base ≃* DE3 :=
  (MonoidHom.ofInjective baseEmbedding_injective).trans
    (MulEquiv.subgroupCongr BorisovBaseRange.DE3_eq_range_baseEmbedding.symm)

private def baseD : DE3 := ⟨d3, Subgroup.subset_closure (by simp)⟩
private def baseE : DE3 := ⟨e3, Subgroup.subset_closure (by simp)⟩

private theorem baseEquiv_d : baseEquiv (FreeGroup.of (0 : Fin 2)) = baseD := by
  apply Subtype.ext
  rfl

private theorem baseEquiv_e : baseEquiv (FreeGroup.of (1 : Fin 2)) = baseE := by
  apply Subtype.ext
  rfl

private def baseToFree : DE3 →* FreeGroup (Fin 3) :=
  (FreeGroup.lift ![FreeGroup.of 1, FreeGroup.of 2]).comp baseEquiv.symm.toMonoidHom

private theorem baseToFree_d : baseToFree baseD = FreeGroup.of 1 := by
  rw [← baseEquiv_d]
  simp [baseToFree]

private theorem baseToFree_e : baseToFree baseE = FreeGroup.of 2 := by
  rw [← baseEquiv_e]
  simp [baseToFree]

private def restrictedToFree : Restricted R →* FreeGroup (Fin 3) :=
  HNNExtension.lift baseToFree (FreeGroup.of 0)⁻¹ (by
    intro a
    have ha : a = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have h : (((a : DE3) : Gamma3)) ∈ (⊥ : Subgroup Gamma3) := by
        rw [← U_inf_DE3 R]
        exact ⟨a.property, (a : DE3).property⟩
      exact h
    subst a
    simp)

private def freeToRestricted : FreeGroup (Fin 3) →* Restricted R :=
  FreeGroup.lift ![HNNExtension.t⁻¹, HNNExtension.of baseD, HNNExtension.of baseE]

private theorem freeToRestricted_injective : Function.Injective (freeToRestricted R) := by
  have h : (restrictedToFree R).comp (freeToRestricted R) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;>
      simp [freeToRestricted, restrictedToFree, baseToFree_d, baseToFree_e]
  exact Function.LeftInverse.injective (fun x => DFunLike.congr_fun h x)

/-- The free triple in the core, in generator order `c,d,e`. -/
def triple : FreeGroup (Fin 3) →* Core R :=
  FreeGroup.lift ![c R (rankFiveFree R),
    of3 R (rankFiveFree R) d3, of3 R (rankFiveFree R) e3]

@[simp] theorem triple_c : triple R (FreeGroup.of 0) = c R (rankFiveFree R) := by
  simp [triple]

@[simp] theorem triple_d : triple R (FreeGroup.of 1) = of3 R (rankFiveFree R) d3 := by
  simp [triple]

@[simp] theorem triple_e : triple R (FreeGroup.of 2) = of3 R (rankFiveFree R) e3 := by
  simp [triple]

/-- No nontrivial word on `c,d,e` becomes trivial in the simulator core. -/
theorem triple_injective : Function.Injective (triple R) := by
  have h : (restrictedEmbedding DE3 (cEquiv_mem_DE3_iff R)).comp
      (freeToRestricted R) = triple R := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;>
      simp [freeToRestricted, triple, c, of3, baseD, baseE]
  rw [← h]
  exact (restrictedEmbedding_injective DE3 (cEquiv_mem_DE3_iff R)).comp
    (freeToRestricted_injective R)

/-- The designated pair `c,d` in the core. -/
def pairD : FreeGroup (Fin 2) →* Core R :=
  FreeGroup.lift ![c R (rankFiveFree R), of3 R (rankFiveFree R) d3]

@[simp] theorem pairD_c : pairD R (FreeGroup.of 0) = c R (rankFiveFree R) := by
  simp [pairD]

@[simp] theorem pairD_d : pairD R (FreeGroup.of 1) = of3 R (rankFiveFree R) d3 := by
  simp [pairD]

theorem pairD_injective : Function.Injective (pairD R) := by
  have h : (triple R).comp (FreeGroup.map (![0, 1] : Fin 2 → Fin 3)) = pairD R := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [pairD]
  rw [← h]
  apply (triple_injective R).comp
  apply FreeGroup.map_injective
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

end

end UniversalGroup.CoreFreeSubgroups
