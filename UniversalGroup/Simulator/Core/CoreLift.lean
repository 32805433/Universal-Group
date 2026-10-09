module

public import UniversalGroup.Simulator.Core.CStage
public import UniversalGroup.Simulator.Core.BaseHNN

@[expose] public section

/-!
# The universal property of the faithful five-generator simulator core

Choose values of `d,e,s₁,s₂,c` in an arbitrary group satisfying the four
power equations, two commutations, and three transport equations. They
extend to the actual iterated HNN model of the simulator core. The rank-five
freeness certificate used to define that model is an explicit parameter.
-/

namespace UniversalGroup.CoreLift

open BorisovCStage BorisovHNNModel BorisovG0HNN HNNLemmas

noncomputable section

variable {H : Type*} [Group H]

/-- The defining equations of the simulator core, in arbitrary target values. -/
structure Relations (R : SupportedRules) (d e : H) (s : Fin 2 → H) (c : H) : Prop where
  d_power : ∀ i, d ^ 4 * s i = s i * d
  e_power : ∀ i, e * s i = s i * e ^ 4
  c_commutes : ∀ i, Commute c (s i)
  simulation : ∀ i : Fin 3,
    c⁻¹ * (d ^ (i.val + 1) * evalPositive (s 0) (s 1) (R.F i) *
      e ^ (i.val + 1)) * c =
      d ^ (i.val + 1) * evalPositive (s 0) (s 1) (R.E i) * e ^ (i.val + 1)

variable (R : SupportedRules) (d e : H) (s : Fin 2 → H) (c : H)
  (h : Relations R d e s c)

def g0Values : Fin 4 → H := ![d, e, s 0, s 1]

include h

theorem g0_relators (i : Fin 4) :
    Word.eval (g0Values d e s) (BorisovIntersections.presentation.relator i) = 1 := by
  have hd (j : Fin 2) : (s j)⁻¹ * d ^ 4 * s j = d := by
    simpa [mul_assoc] using congrArg (fun z => (s j)⁻¹ * z) (h.d_power j)
  have he (j : Fin 2) : (s j)⁻¹ * e * s j = e ^ 4 := by
    simpa [mul_assoc] using congrArg (fun z => (s j)⁻¹ * z) (h.e_power j)
  fin_cases i
  all_goals simp only [BorisovIntersections.presentation,
    Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
    | rw [BorisovIntersections.sDRelator, Word.eval_relation_eq_one_iff]
    | rw [BorisovIntersections.sERelator, Word.eval_relation_eq_one_iff]
  all_goals simp [BorisovIntersections.dWord,
      BorisovIntersections.eWord, BorisovIntersections.s1Word,
      BorisovIntersections.s2Word, g0Values, ← mul_assoc, hd, he]

def g0Lift : BorisovIntersections.G0 →* H :=
  BorisovIntersections.presentation.homOfRelators (g0Values d e s)
    (g0_relators R d e s c h)

/-- The homomorphism on the four-generator iterated HNN base. -/
def baseLift : BorisovHNNModel.Gamma3 →* H :=
  (g0Lift R d e s c h).comp BorisovG0HNN.fromHNN

@[simp] theorem baseLift_d3 : baseLift R d e s c h d3 = d := by
  change g0Lift R d e s c h (fromHNN hnnD) = d
  rw [fromHNN_hnnD, presentedD_eq_of]
  exact FP.homOfRelators_of _ _ _ _

@[simp] theorem baseLift_e3 : baseLift R d e s c h e3 = e := by
  change g0Lift R d e s c h (fromHNN hnnE) = e
  rw [fromHNN_hnnE, presentedE_eq_of]
  exact FP.homOfRelators_of _ _ _ _

@[simp] theorem baseLift_s1_3 : baseLift R d e s c h s1_3 = s 0 := by
  change g0Lift R d e s c h (fromHNN hnnS1) = s 0
  rw [fromHNN_hnnS1, presentedS1_eq_of]
  exact FP.homOfRelators_of _ _ _ _

@[simp] theorem baseLift_s2_3 : baseLift R d e s c h s2_3 = s 1 := by
  change g0Lift R d e s c h (fromHNN hnnS2) = s 1
  rw [fromHNN_hnnS2, presentedS2_eq_of]
  exact FP.homOfRelators_of _ _ _ _

@[simp] theorem baseLift_stable3 (i : Fin 2) :
    baseLift R d e s c h (stable3 i) = s i := by
  fin_cases i <;> simp [stable3]

@[simp] theorem baseLift_positive3 (w : PositiveWord) :
    baseLift R d e s c h (positive3 w) = evalPositive (s 0) (s 1) w := by
  simp only [positive3, evalPositive, map_list_prod, List.map_map]
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      fin_cases i <;> simp

private theorem conjugates_basis (q : RuleBasis) :
    c⁻¹ * baseLift R d e s c h (uBasis R q) * c =
      baseLift R d e s c h (vBasis R q) := by
  cases q with
  | inl i =>
      simpa [uBasis, vBasis] using (h.c_commutes i).inv_mul_cancel
  | inr i =>
      simpa [uBasis, vBasis, a3, b3, map_mul, map_pow] using h.simulation i

private theorem conjugates_uLift (x : FreeGroup RuleBasis) :
    c⁻¹ * baseLift R d e s c h (uLift R x) * c =
      baseLift R d e s c h (vLift R x) := by
  have heq :
      (MulAut.conj c⁻¹).toMonoidHom.comp ((baseLift R d e s c h).comp (uLift R)) =
        (baseLift R d e s c h).comp (vLift R) := by
    apply FreeGroup.ext_hom
    intro q
    simpa [MonoidHom.comp_apply, uLift, vLift] using conjugates_basis R d e s c h q
  simpa [MonoidHom.comp_apply] using DFunLike.congr_fun heq x

theorem lift_condition (hfree : RankFiveFree R) (a : U R) :
    c⁻¹ * baseLift R d e s c h (a : Gamma3) =
      baseLift R d e s c h (cEquiv R hfree a : Gamma3) * c⁻¹ := by
  rcases a.property with ⟨x, hx⟩
  let ax : U R := ⟨uLift R x, ⟨x, rfl⟩⟩
  have hax : a = ax := Subtype.ext hx.symm
  subst a
  have hphi : ((cEquiv R hfree ax : V R) : Gamma3) = vLift R x := by
    simp [ax, cEquiv, rangeEquiv_apply_range]
  calc
    c⁻¹ * baseLift R d e s c h (ax : Gamma3) =
        (c⁻¹ * baseLift R d e s c h (uLift R x) * c) * c⁻¹ := by
          simp [ax, mul_assoc]
    _ = baseLift R d e s c h (vLift R x) * c⁻¹ := by
      rw [conjugates_uLift R d e s c h x]
    _ = baseLift R d e s c h (cEquiv R hfree ax : Gamma3) * c⁻¹ := by rw [hphi]

end

noncomputable section

variable {H : Type*} [Group H]
variable (R : SupportedRules) (hfree : RankFiveFree R)
  (d e : H) (s : Fin 2 → H) (c : H) (h : Relations R d e s c)

/-- Extend the five chosen generator values to the faithful simulator core. -/
def lift : BorisovCStage.Gamma2 R hfree →* H :=
  HNNExtension.lift (baseLift R d e s c h) c⁻¹ (lift_condition R d e s c h hfree)

@[simp] theorem lift_of3 (x : Gamma3) :
    lift R hfree d e s c h (of3 R hfree x) = baseLift R d e s c h x := by
  simp [lift, of3]

@[simp] theorem lift_d :
    lift R hfree d e s c h (of3 R hfree d3) = d := by simp

@[simp] theorem lift_e :
    lift R hfree d e s c h (of3 R hfree e3) = e := by simp

@[simp] theorem lift_s1 :
    lift R hfree d e s c h (of3 R hfree s1_3) = s 0 := by simp

@[simp] theorem lift_s2 :
    lift R hfree d e s c h (of3 R hfree s2_3) = s 1 := by simp

@[simp] theorem lift_c :
    lift R hfree d e s c h (BorisovCStage.c R hfree) = c := by
  simp [lift, BorisovCStage.c]

end

/-- A homomorphism on the four-generator HNN base is determined by the
displayed values of `d,e,s₁,s₂`. -/
theorem base_hom_ext {H : Type*} [Group H]
    {φ ψ : BorisovHNNModel.Gamma3 →* H}
    (hd : φ d3 = ψ d3) (he : φ e3 = ψ e3)
    (hs1 : φ s1_3 = ψ s1_3) (hs2 : φ s2_3 = ψ s2_3) : φ = ψ := by
  apply HNNExtension.hom_ext
  · apply HNNExtension.hom_ext
    · apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · exact hd
      · exact he
    · exact hs1
  · exact hs2

/-- A homomorphism on the five-generator simulator core is determined by
the values of `c,d,e,s₁,s₂`. The inverse convention for `c` is accounted for. -/
theorem hom_ext {H : Type*} [Group H]
    {R : SupportedRules} {hfree : RankFiveFree R}
    {φ ψ : BorisovCStage.Gamma2 R hfree →* H}
    (hc : φ (BorisovCStage.c R hfree) = ψ (BorisovCStage.c R hfree))
    (hd : φ (of3 R hfree d3) = ψ (of3 R hfree d3))
    (he : φ (of3 R hfree e3) = ψ (of3 R hfree e3))
    (hs1 : φ (of3 R hfree s1_3) = ψ (of3 R hfree s1_3))
    (hs2 : φ (of3 R hfree s2_3) = ψ (of3 R hfree s2_3)) : φ = ψ := by
  apply HNNExtension.hom_ext
  · exact base_hom_ext hd he hs1 hs2
  · simpa only [BorisovCStage.c, map_inv, inv_inv] using congrArg Inv.inv hc

end UniversalGroup.CoreLift
