module

public import UniversalGroup.Simulator.Core.IntersectionsTransport

@[expose] public section

/-!
# Positive single-letter symmetry at the `c` stage

Restrict the `c`-stage HNN extension to the two single-letter subgroups.
Only both-letter support of the three semigroup rules is required.

The resulting isomorphism between the exact subgroups `⟨d,e,c,s₁⟩` and
`⟨d,e,c,s₂⟩` fixes `c` and sends `d ↦ e`, `e ↦ d`, `s₁ ↦ s₂⁻¹`.
-/

namespace UniversalGroup.Embedding.PositiveHost.CoreSymmetry

open BorisovCStage
open BorisovG0HNN
open BorisovHNNModel
open BorisovInputsBridge
open HNNLemmas

noncomputable section

variable (datum : UniversalGroup.SupportedRules)

/-! ## The symmetry between `J₁` and `J₂`

The following base change is defined before adjoining `c`:
`d ↦ e`, `e ↦ d`, `s₁ ↦ s₂⁻¹`.  We construct it as an
automorphism of the four-generator group `Gamma3`; it is an involution on the four displayed generators.
-/

def twistGenerator : Fin 4 → Gamma3 :=
  ![e3, d3, s2_3⁻¹, s1_3⁻¹]

def untwistGenerator : Fin 4 → Gamma3 :=
  ![e3, d3, s2_3⁻¹, s1_3⁻¹]

private theorem stable_conjugates_d
    (s : Gamma3) (hs : d3 ^ 4 * s = s * d3) :
    s * d3 * s⁻¹ = d3 ^ 4 := by
  rw [← hs]
  simp

private theorem stable_conjugates_e_four
    (s : Gamma3) (hs : e3 * s = s * e3 ^ 4) :
    s * e3 ^ 4 * s⁻¹ = e3 := by
  rw [← hs]
  simp

theorem twist_relators :
    ∀ r ∈ BorisovIntersections.presentation.relSet,
      FreeGroup.lift twistGenerator r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s1Word, twistGenerator, mul_assoc] using
      stable_conjugates_e_four s2_3 gamma3_e_mul_s2
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s1Word, twistGenerator, mul_assoc] using
      stable_conjugates_d s2_3 gamma3_d_four_mul_s2
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s2Word, twistGenerator, mul_assoc] using
      stable_conjugates_e_four s1_3 gamma3_e_mul_s1
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s2Word, twistGenerator, mul_assoc] using
      stable_conjugates_d s1_3 gamma3_d_four_mul_s1

theorem untwist_relators :
    ∀ r ∈ BorisovIntersections.presentation.relSet,
      FreeGroup.lift untwistGenerator r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s1Word, untwistGenerator, mul_assoc] using
      stable_conjugates_e_four s2_3 gamma3_e_mul_s2
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s1Word, untwistGenerator, mul_assoc] using
      stable_conjugates_d s2_3 gamma3_d_four_mul_s2
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s2Word, untwistGenerator, mul_assoc] using
      stable_conjugates_e_four s1_3 gamma3_e_mul_s1
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s2Word, untwistGenerator, mul_assoc] using
      stable_conjugates_d s1_3 gamma3_d_four_mul_s1

def twistFromG0 : BorisovIntersections.G0 →* Gamma3 :=
  PresentedGroup.toGroup twist_relators

def untwistFromG0 : BorisovIntersections.G0 →* Gamma3 :=
  PresentedGroup.toGroup untwist_relators

@[simp] private theorem twistFromG0_of (i : Fin 4) :
    twistFromG0 (PresentedGroup.of i) = twistGenerator i :=
  PresentedGroup.toGroup.of twist_relators

@[simp] private theorem untwistFromG0_of (i : Fin 4) :
    untwistFromG0 (PresentedGroup.of i) = untwistGenerator i :=
  PresentedGroup.toGroup.of untwist_relators

def twistHom : Gamma3 →* Gamma3 :=
  twistFromG0.comp g0Equiv.symm.toMonoidHom

def untwistHom : Gamma3 →* Gamma3 :=
  untwistFromG0.comp g0Equiv.symm.toMonoidHom

private theorem gamma3_hom_ext {Q : Type*} [Group Q]
    {f g : Gamma3 →* Q}
    (hd : f d3 = g d3) (he : f e3 = g e3)
    (hs1 : f s1_3 = g s1_3) (hs2 : f s2_3 = g s2_3) : f = g := by
  apply HNNExtension.hom_ext
  · apply HNNExtension.hom_ext
    · apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · exact hd
      · exact he
    · exact hs1
  · exact hs2

@[simp] theorem twistHom_d3 : twistHom d3 = e3 := by
  change twistFromG0 (fromHNN hnnD) = _
  rw [fromHNN_hnnD, presentedD_eq_of, twistFromG0_of]
  rfl

@[simp] theorem twistHom_e3 : twistHom e3 = d3 := by
  change twistFromG0 (fromHNN hnnE) = _
  rw [fromHNN_hnnE, presentedE_eq_of, twistFromG0_of]
  rfl

@[simp] theorem twistHom_s1_3 : twistHom s1_3 = s2_3⁻¹ := by
  change twistFromG0 (fromHNN hnnS1) = _
  rw [fromHNN_hnnS1, presentedS1_eq_of, twistFromG0_of]
  rfl

@[simp] theorem twistHom_s2_3 : twistHom s2_3 = s1_3⁻¹ := by
  change twistFromG0 (fromHNN hnnS2) = _
  rw [fromHNN_hnnS2, presentedS2_eq_of, twistFromG0_of]
  rfl

@[simp] theorem untwistHom_d3 : untwistHom d3 = e3 := by
  change untwistFromG0 (fromHNN hnnD) = _
  rw [fromHNN_hnnD, presentedD_eq_of, untwistFromG0_of]
  rfl

@[simp] theorem untwistHom_e3 : untwistHom e3 = d3 := by
  change untwistFromG0 (fromHNN hnnE) = _
  rw [fromHNN_hnnE, presentedE_eq_of, untwistFromG0_of]
  rfl

@[simp] theorem untwistHom_s1_3 : untwistHom s1_3 = s2_3⁻¹ := by
  change untwistFromG0 (fromHNN hnnS1) = _
  rw [fromHNN_hnnS1, presentedS1_eq_of, untwistFromG0_of]
  rfl

@[simp] theorem untwistHom_s2_3 : untwistHom s2_3 = s1_3⁻¹ := by
  change untwistFromG0 (fromHNN hnnS2) = _
  rw [fromHNN_hnnS2, presentedS2_eq_of, untwistFromG0_of]
  rfl

theorem untwist_comp_twist :
    untwistHom.comp twistHom = MonoidHom.id Gamma3 := by
  apply gamma3_hom_ext <;> simp

theorem twist_comp_untwist :
    twistHom.comp untwistHom = MonoidHom.id Gamma3 := by
  apply gamma3_hom_ext <;> simp

theorem twist_mem_J3 {x : Gamma3} (hx : x ∈ J3 0) :
    twistHom x ∈ J3 1 := by
  let K : Subgroup Gamma3 := (J3 1).comap twistHom
  have hle : J3 0 ≤ K := by
    rw [J3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · change twistHom d3 ∈ J3 1
      rw [twistHom_d3]
      exact Subgroup.subset_closure (by simp)
    · change twistHom e3 ∈ J3 1
      rw [twistHom_e3]
      exact Subgroup.subset_closure (by simp)
    · change twistHom (stable3 0) ∈ J3 1
      rw [show stable3 0 = s1_3 by rfl, twistHom_s1_3]
      exact (J3 1).inv_mem (Subgroup.subset_closure (by simp [stable3]))
  exact hle hx

theorem untwist_mem_J3 {x : Gamma3} (hx : x ∈ J3 1) :
    untwistHom x ∈ J3 0 := by
  let K : Subgroup Gamma3 := (J3 0).comap untwistHom
  have hle : J3 1 ≤ K := by
    rw [J3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · change untwistHom d3 ∈ J3 0
      rw [untwistHom_d3]
      exact Subgroup.subset_closure (by simp)
    · change untwistHom e3 ∈ J3 0
      rw [untwistHom_e3]
      exact Subgroup.subset_closure (by simp)
    · change untwistHom (stable3 1) ∈ J3 0
      rw [show stable3 1 = s2_3 by rfl, untwistHom_s2_3]
      exact (J3 0).inv_mem (Subgroup.subset_closure (by simp [stable3]))
  exact hle hx

/-- The base isomorphism `J₁ ≃ J₂` used by the restricted `c`-HNN
extensions. -/
def jEquiv : J3 0 ≃* J3 1 where
  toFun x := ⟨twistHom x, twist_mem_J3 x.property⟩
  invFun x := ⟨untwistHom x, untwist_mem_J3 x.property⟩
  left_inv x := Subtype.ext (DFunLike.congr_fun untwist_comp_twist (x : Gamma3))
  right_inv x := Subtype.ext (DFunLike.congr_fun twist_comp_untwist (x : Gamma3))
  map_mul' x y := Subtype.ext (map_mul twistHom (x : Gamma3) (y : Gamma3))

private theorem twist_mem_stableCyclic {x : Gamma3}
    (hx : x ∈ stableCyclic3 0) :
    twistHom x ∈ stableCyclic3 1 := by
  rcases Subgroup.mem_closure_singleton.mp hx with ⟨n, hn⟩
  rw [← hn, map_zpow, show stable3 0 = s1_3 by rfl, twistHom_s1_3]
  exact (stableCyclic3 1).zpow_mem
    ((stableCyclic3 1).inv_mem
      (Subgroup.subset_closure (Set.mem_singleton (stable3 1)))) n

private theorem untwist_mem_stableCyclic {x : Gamma3}
    (hx : x ∈ stableCyclic3 1) :
    untwistHom x ∈ stableCyclic3 0 := by
  rcases Subgroup.mem_closure_singleton.mp hx with ⟨n, hn⟩
  rw [← hn, map_zpow, show stable3 1 = s2_3 by rfl, untwistHom_s2_3]
  exact (stableCyclic3 0).zpow_mem
    ((stableCyclic3 0).inv_mem
      (Subgroup.subset_closure (Set.mem_singleton (stable3 0)))) n

theorem twist_mem_U {x : Gamma3}
    (hxU : x ∈ U datum) (hxJ : x ∈ J3 0) : twistHom x ∈ U datum := by
  apply stableCyclic3_le_U datum 1
  apply twist_mem_stableCyclic
  rw [← U_inf_J3 datum 0]
  exact ⟨hxU, hxJ⟩

theorem untwist_mem_U {x : Gamma3}
    (hxU : x ∈ U datum) (hxJ : x ∈ J3 1) : untwistHom x ∈ U datum := by
  apply stableCyclic3_le_U datum 0
  apply untwist_mem_stableCyclic
  rw [← U_inf_J3 datum 1]
  exact ⟨hxU, hxJ⟩

theorem twist_mem_V {x : Gamma3}
    (hxV : x ∈ V datum) (hxJ : x ∈ J3 0) : twistHom x ∈ V datum := by
  apply stableCyclic3_le_V datum 1
  apply twist_mem_stableCyclic
  rw [← V_inf_J3 datum 0]
  exact ⟨hxV, hxJ⟩

theorem untwist_mem_V {x : Gamma3}
    (hxV : x ∈ V datum) (hxJ : x ∈ J3 1) : untwistHom x ∈ V datum := by
  apply stableCyclic3_le_V datum 0
  apply untwist_mem_stableCyclic
  rw [← V_inf_J3 datum 1]
  exact ⟨hxV, hxJ⟩

abbrev CRestrictedA (beta : Fin 2) :=
  restrictedA (A := U datum) (J3 beta)

abbrev CRestrictedB (beta : Fin 2) :=
  restrictedB (B := V datum) (J3 beta)

def cRestrictedPhi (beta : Fin 2) :
    CRestrictedA datum beta ≃* CRestrictedB datum beta :=
  restrictedPhi (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)

/-- The exact restricted `c`-HNN extension over `J_beta`. -/
abbrev CRestricted (beta : Fin 2) :=
  HNNExtension (J3 beta) (CRestrictedA datum beta) (CRestrictedB datum beta)
    (cRestrictedPhi datum beta)

def cRestrictedAEquiv :
    CRestrictedA datum 0 ≃* CRestrictedA datum 1 where
  toFun a :=
    ⟨jEquiv (a : J3 0),
      twist_mem_U datum a.property (a : J3 0).property⟩
  invFun a :=
    ⟨(jEquiv).symm (a : J3 1),
      untwist_mem_U datum a.property (a : J3 1).property⟩
  left_inv a := Subtype.ext ((jEquiv).symm_apply_apply (a : J3 0))
  right_inv a := Subtype.ext ((jEquiv).apply_symm_apply (a : J3 1))
  map_mul' a b := Subtype.ext (map_mul jEquiv (a : J3 0) (b : J3 0))

def cRestrictedBEquiv :
    CRestrictedB datum 0 ≃* CRestrictedB datum 1 where
  toFun b :=
    ⟨jEquiv (b : J3 0),
      twist_mem_V datum b.property (b : J3 0).property⟩
  invFun b :=
    ⟨(jEquiv).symm (b : J3 1),
      untwist_mem_V datum b.property (b : J3 1).property⟩
  left_inv b := Subtype.ext ((jEquiv).symm_apply_apply (b : J3 0))
  right_inv b := Subtype.ext ((jEquiv).apply_symm_apply (b : J3 1))
  map_mul' a b := Subtype.ext (map_mul jEquiv (a : J3 0) (b : J3 0))

private theorem cEquiv_eq_on_J (beta : Fin 2) (a : U datum)
    (haJ : (a : Gamma3) ∈ J3 beta) :
    (cEquiv datum (rankFiveFree datum) a : Gamma3) = (a : Gamma3) := by
  have haC : (a : Gamma3) ∈ stableCyclic3 beta := by
    rw [← U_inf_J3 datum beta]
    exact ⟨a.property, haJ⟩
  rcases Subgroup.mem_closure_singleton.mp haC with ⟨n, hn⟩
  have ha : a = (uStable datum beta) ^ n := Subtype.ext hn.symm
  rw [ha, map_zpow]
  change
    (cEquiv datum (rankFiveFree datum) (uStable datum beta) : Gamma3) ^ n =
      (stable3 beta) ^ n
  rw [cEquiv_uStable]

theorem cRestricted_intertwines (a : CRestrictedA datum 0) :
    cRestrictedBEquiv datum (cRestrictedPhi datum 0 a) =
      cRestrictedPhi datum 1 (cRestrictedAEquiv datum a) := by
  apply Subtype.ext
  apply Subtype.ext
  change
    twistHom
        (cEquiv datum (rankFiveFree datum)
          (⟨((a : J3 0) : Gamma3), a.property⟩ : U datum) : Gamma3) =
      (cEquiv datum (rankFiveFree datum)
          (⟨twistHom ((a : J3 0) : Gamma3),
            twist_mem_U datum a.property (a : J3 0).property⟩ : U datum) : Gamma3)
  rw [cEquiv_eq_on_J datum 0 _ (a : J3 0).property]
  rw [cEquiv_eq_on_J datum 1 _
    (twist_mem_J3 (a : J3 0).property)]

/-- The exact `c`-stage symmetry, obtained by transporting both restricted
associated subgroups along `jEquiv`. -/
def cRestrictedEquiv : CRestricted datum 0 ≃* CRestricted datum 1 :=
  HNNLemmas.congr jEquiv (cRestrictedAEquiv datum) (cRestrictedBEquiv datum)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (cRestricted_intertwines datum)

@[simp] private theorem cRestrictedEquiv_of (x : J3 0) :
    cRestrictedEquiv datum (HNNExtension.of x) =
      HNNExtension.of (jEquiv x) := rfl

@[simp] private theorem cRestrictedEquiv_t :
    cRestrictedEquiv datum
        (HNNExtension.t : CRestricted datum 0) =
      (HNNExtension.t : CRestricted datum 1) := rfl

/-- The exact subgroup `⟨d,e,c,s_beta⟩` of `Gamma2`. -/
def CSubgroup (beta : Fin 2) : Subgroup (Gamma2 datum (rankFiveFree datum)) :=
  generatedWithStable (A := U datum) (B := V datum)
    (phi := cEquiv datum (rankFiveFree datum)) (J3 beta)

def cRestrictedRangeEquiv (beta : Fin 2) :
    CRestricted datum beta ≃* CSubgroup datum beta :=
  restrictedEquivGeneratedWithStable (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)

@[simp] private theorem cRestrictedRangeEquiv_of_coe
    (beta : Fin 2) (x : J3 beta) :
    ((cRestrictedRangeEquiv datum beta (HNNExtension.of x) :
        CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum)) =
      of3 datum (rankFiveFree datum) (x : Gamma3) := by
  change _ = (HNNExtension.of (x : Gamma3) :
    HNNExtension Gamma3 (U datum) (V datum)
      (cEquiv datum (rankFiveFree datum)))
  exact restrictedEquivGeneratedWithStable_coe (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)
    (HNNExtension.of x)

@[simp] private theorem cRestrictedRangeEquiv_t_coe (beta : Fin 2) :
    ((cRestrictedRangeEquiv datum beta
        (HNNExtension.t : CRestricted datum beta) : CSubgroup datum beta) :
      Gamma2 datum (rankFiveFree datum)) = HNNExtension.t := by
  change _ = (HNNExtension.t :
    HNNExtension Gamma3 (U datum) (V datum)
      (cEquiv datum (rankFiveFree datum)))
  exact restrictedEquivGeneratedWithStable_coe (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)
    (HNNExtension.t : CRestricted datum beta)

private theorem cRestrictedRangeEquiv_inv_t_coe (beta : Fin 2) :
    ((cRestrictedRangeEquiv datum beta
        ((HNNExtension.t : CRestricted datum beta)⁻¹) :
      CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum)) =
      BorisovCStage.c datum (rankFiveFree datum) := by
  change
    ((cRestrictedRangeEquiv datum beta
        ((HNNExtension.t : CRestricted datum beta)⁻¹) :
      CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum)) =
      (HNNExtension.t : Gamma2 datum (rankFiveFree datum))⁻¹
  rw [map_inv]
  exact congrArg Inv.inv (cRestrictedRangeEquiv_t_coe datum beta)

/-- The induced isomorphism
`⟨d,e,c,s₁⟩ ≃ ⟨d,e,c,s₂⟩`. -/
def cSubgroupEquiv : CSubgroup datum 0 ≃* CSubgroup datum 1 :=
  (cRestrictedRangeEquiv datum 0).symm.trans
    ((cRestrictedEquiv datum).trans (cRestrictedRangeEquiv datum 1))

theorem d3_mem_J3 (beta : Fin 2) : d3 ∈ J3 beta :=
  Subgroup.subset_closure (by simp)

theorem e3_mem_J3 (beta : Fin 2) : e3 ∈ J3 beta :=
  Subgroup.subset_closure (by simp)

theorem stable3_mem_J3 (beta : Fin 2) : stable3 beta ∈ J3 beta :=
  Subgroup.subset_closure (by simp)

def coreD (beta : Fin 2) : CSubgroup datum beta :=
  ⟨of3 datum (rankFiveFree datum) d3,
    Subgroup.subset_closure (Or.inl ⟨d3, d3_mem_J3 beta, rfl⟩)⟩

def coreE (beta : Fin 2) : CSubgroup datum beta :=
  ⟨of3 datum (rankFiveFree datum) e3,
    Subgroup.subset_closure (Or.inl ⟨e3, e3_mem_J3 beta, rfl⟩)⟩

def coreStable (beta : Fin 2) : CSubgroup datum beta :=
  ⟨of3 datum (rankFiveFree datum) (stable3 beta),
    Subgroup.subset_closure
      (Or.inl ⟨stable3 beta, stable3_mem_J3 beta, rfl⟩)⟩

def coreC (beta : Fin 2) : CSubgroup datum beta :=
  ⟨BorisovCStage.c datum (rankFiveFree datum),
    (CSubgroup datum beta).inv_mem
      (Subgroup.subset_closure (Or.inr (Set.mem_singleton _)))⟩

private theorem cRestrictedRangeEquiv_symm_of (beta : Fin 2) (x : J3 beta) :
    (cRestrictedRangeEquiv datum beta).symm
        ⟨of3 datum (rankFiveFree datum) (x : Gamma3),
          Subgroup.subset_closure (Or.inl ⟨x, x.property, rfl⟩)⟩ =
      HNNExtension.of x := by
  apply (cRestrictedRangeEquiv datum beta).injective
  rw [(cRestrictedRangeEquiv datum beta).apply_symm_apply]
  apply Subtype.ext
  exact (restrictedEquivGeneratedWithStable_coe (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)
    (HNNExtension.of x)).symm

private theorem cRestrictedRangeEquiv_symm_c (beta : Fin 2) :
    (cRestrictedRangeEquiv datum beta).symm (coreC datum beta) =
      (HNNExtension.t : CRestricted datum beta)⁻¹ := by
  apply (cRestrictedRangeEquiv datum beta).injective
  rw [(cRestrictedRangeEquiv datum beta).apply_symm_apply]
  apply Subtype.ext
  change
    BorisovCStage.c datum (rankFiveFree datum) =
      ((cRestrictedRangeEquiv datum beta
          ((HNNExtension.t : CRestricted datum beta)⁻¹) :
        CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum))
  exact (cRestrictedRangeEquiv_inv_t_coe datum beta).symm

private theorem cRestrictedRangeEquiv_symm_coreD :
    (cRestrictedRangeEquiv datum 0).symm (coreD datum 0) =
      HNNExtension.of (⟨d3, d3_mem_J3 0⟩ : J3 0) := by
  simpa [coreD] using cRestrictedRangeEquiv_symm_of datum 0
    (⟨d3, d3_mem_J3 0⟩ : J3 0)

private theorem cRestrictedRangeEquiv_symm_coreE :
    (cRestrictedRangeEquiv datum 0).symm (coreE datum 0) =
      HNNExtension.of (⟨e3, e3_mem_J3 0⟩ : J3 0) := by
  simpa [coreE] using cRestrictedRangeEquiv_symm_of datum 0
    (⟨e3, e3_mem_J3 0⟩ : J3 0)

private theorem cRestrictedRangeEquiv_symm_coreStable :
    (cRestrictedRangeEquiv datum 0).symm (coreStable datum 0) =
      HNNExtension.of (⟨stable3 0, stable3_mem_J3 0⟩ : J3 0) := by
  simpa [coreStable] using cRestrictedRangeEquiv_symm_of datum 0
    (⟨stable3 0, stable3_mem_J3 0⟩ : J3 0)

@[simp] theorem cSubgroupEquiv_coreD :
    cSubgroupEquiv datum (coreD datum 0) = coreE datum 1 := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_coreD]
  change
    cRestrictedRangeEquiv datum 1
        (cRestrictedEquiv datum (HNNExtension.of
          (⟨d3, d3_mem_J3 0⟩ : J3 0))) = _
  rw [cRestrictedEquiv_of]
  apply Subtype.ext
  rw [cRestrictedRangeEquiv_of_coe]
  simp [coreE, jEquiv]

@[simp] theorem cSubgroupEquiv_coreE :
    cSubgroupEquiv datum (coreE datum 0) = coreD datum 1 := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_coreE]
  change
    cRestrictedRangeEquiv datum 1
        (cRestrictedEquiv datum (HNNExtension.of
          (⟨e3, e3_mem_J3 0⟩ : J3 0))) = _
  rw [cRestrictedEquiv_of]
  apply Subtype.ext
  rw [cRestrictedRangeEquiv_of_coe]
  simp [coreD, jEquiv]

@[simp] theorem cSubgroupEquiv_coreC :
    cSubgroupEquiv datum (coreC datum 0) = coreC datum 1 := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_c]
  rw [map_inv, cRestrictedEquiv_t]
  apply Subtype.ext
  rw [map_inv]
  simp [coreC, BorisovCStage.c]

@[simp] theorem cSubgroupEquiv_coreS1 :
    cSubgroupEquiv datum (coreStable datum 0) = (coreStable datum 1)⁻¹ := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_coreStable]
  change
    cRestrictedRangeEquiv datum 1
        (cRestrictedEquiv datum (HNNExtension.of
          (⟨stable3 0, stable3_mem_J3 0⟩ : J3 0))) = _
  rw [cRestrictedEquiv_of]
  apply Subtype.ext
  rw [cRestrictedRangeEquiv_of_coe]
  simp [coreStable, jEquiv, stable3]

end

end UniversalGroup.Embedding.PositiveHost.CoreSymmetry
