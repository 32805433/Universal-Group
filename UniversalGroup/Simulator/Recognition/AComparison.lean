module

public import UniversalGroup.Simulator.Recognition.ACoefficients
public import UniversalGroup.Simulator.Recognition.CoefficientTransport
public import UniversalGroup.Foundations.HNN.ReducedWordPeel

@[expose] public section

/-! The second comparison needed after an initial inverse T in `A`. -/

namespace UniversalGroup.SimulatorIntersectionACompare

open SimulatorIntersectionB SimulatorCoefficientTransport SimulatorIntersectionA ReducedWordPeel
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable (G : PreparedInput) (D : ValievDatum G)

abbrev RW := ReducedWordPeel.Word (FStage G D) (left G D).range (right G D).range

theorem phi_symm_coe (b : (right G D).range) :
    ((phi G D).symm b : FStage G D) = f G D * (b : FStage G D) * (f G D)⁻¹ := by
  obtain ⟨c, hc⟩ := b.property
  have he : (phi G D).symm b = ⟨left G D c, ⟨c, rfl⟩⟩ := by
    apply (phi G D).injective
    apply Subtype.ext
    simpa only [MulEquiv.apply_symm_apply, UniversalGroup.rangeEquiv_apply_range] using hc.symm
  rw [he, ← hc, TwistedCentralizer.right_apply]
  change marker G D * (c : FStage G D) * (marker G D)⁻¹ = _
  group

theorem negative_carry (v u : Core G D) (hu : u ∈ CD G D)
    (b : (right G D).range)
    (hb : (b : FStage G D) =
      ((f G D)⁻¹ * ofCore G D v * f G D)⁻¹ * ofCore G D u) :
    ((phi G D).symm b : FStage G D) = ofCore G D (v⁻¹ * u) := by
  rw [phi_symm_coe, hb, map_mul, map_inv]
  have huComm : Commute (f G D) (ofCore G D u) :=
    SimulatorDModel.f_commutes D.toCodeWords D.F_support D.E_support _ ⟨u, hu, rfl⟩
  calc
    _ = (ofCore G D v)⁻¹ * (f G D * ofCore G D u * (f G D)⁻¹) := by group
    _ = _ := by rw [huComm.eq]; group

/-- Strip the initial inverse displayed T; the other head becomes
`v⁻¹*u`, with `u` still in the coefficient subgroup. -/
theorem negative_tail (w z : RW G D) (v : Core G D)
    (hhead : w.head = (f G D)⁻¹ * ofCore G D v * f G D)
    (hzhead : z.head ∈ coefficients G D)
    (hzcoeff : ∀ p ∈ z.toList, p.2 ∈ coefficients G D)
    (heq : w.prod (phi G D) = z.prod (phi G D))
    (a : FStage G D) (rest : List (ℤˣ × FStage G D))
    (hw : w.toList = (1, a) :: rest) :
    ∃ (u : Core G D) (z' : RW G D), u ∈ CD G D ∧
      (tail w 1 a rest hw 1).prod (phi G D) = z'.prod (phi G D) ∧
      z'.head = ofCore G D (v⁻¹ * u) ∧
      (∀ p ∈ z'.toList, p.2 ∈ coefficients G D) := by
  obtain ⟨b, more, hz, hcoset, _⟩ := first_comparison (phi G D) w z heq 1 a rest hw
  have hcoset' : w.head⁻¹ * z.head ∈ (right G D).range := by simpa using hcoset
  obtain ⟨u₀, hu₀, hu₀eq⟩ := hzhead
  obtain ⟨u₁, hu₁, hu₁eq⟩ := hzcoeff (1, b) (by simp [hz])
  let c : (right G D).range := ⟨w.head⁻¹ * z.head, hcoset'⟩
  let z' := tail z 1 b more hz ((phi G D).symm c : FStage G D)
  refine ⟨u₀ * u₁, z', (CD G D).mul_mem hu₀ hu₁, ?_, ?_, ?_⟩
  · exact tail_comparison_one (phi G D) w z a b rest more hw hz heq hcoset'
  · have hc : ((phi G D).symm c : FStage G D) = ofCore G D (v⁻¹ * u₀) := by
      apply negative_carry G D v u₀ hu₀ c
      simp only [c, hhead, hu₀eq]
    change ((phi G D).symm c : FStage G D) * b = _
    change ofCore G D u₁ = b at hu₁eq
    rw [hc, ← hu₁eq, ← map_mul, mul_assoc]
  · intro p hp
    exact hzcoeff p (by simp only [hz, List.mem_cons]; exact Or.inr hp)

/-- After a negative first syllable, either its stable word already lies
in the code subgroup, or a genuine negative-positive boundary supplies
the marker-cancellation equation. -/
theorem negative_head_alternative (w z : RW G D) (W : FreeGroup (Fin 2))
    (hhead : w.head = (f G D)⁻¹ * ofCore G D
      (SimulatorFreeLetters.coreLetters D.toCodeWords D.F_support D.E_support W) * f G D)
    (hwcoeff : ∀ p ∈ w.toList, p.2 ∈ SimulatorIntersectionA.Base G D)
    (hzhead : z.head ∈ coefficients G D)
    (hzcoeff : ∀ p ∈ z.toList, p.2 ∈ coefficients G D)
    (heq : w.prod (phi G D) = z.prod (phi G D))
    (a : FStage G D) (rest : List (ℤˣ × FStage G D))
    (hw : w.toList = (1, a) :: rest) :
    SimulatorFreeLetters.coreLetters D.toCodeWords D.F_support D.E_support W ∈
        (codeCore G D).range ∨
      ∃ (g : FreeGroup (Fin 2)) (Q : PositiveWord), g ≠ 1 ∧
        (W * CodeSubgroups.codeLift D.r g) * BorisovCStage.positiveFree D.P =
          BorisovCStage.positiveFree Q ∧ PositiveEq D.toCodeWords.rules Q D.P := by
  let v := SimulatorFreeLetters.coreLetters D.toCodeWords D.F_support D.E_support W
  have hv : v ∈ Letters G D := ⟨W, rfl⟩
  have ha : a ∈ SimulatorIntersectionA.Base G D := hwcoeff (1, a) (by simp [hw])
  obtain ⟨u, z', hu, ht, hz'head, hz'coeff⟩ := negative_tail G D w z v hhead
    hzhead hzcoeff heq a rest hw
  let w' := tail w 1 a rest hw 1
  have hw'head : w'.head = a := by simp [w', tail]
  have hzt : w'.prod (phi G D) = z'.prod (phi G D) := ht
  cases hr : rest with
  | nil =>
      have hn : z'.toList = [] := by
        have hh := (HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq (phi G D) hzt).1
        simpa [w', tail, hr] using hh.symm
      have he : a = z'.head := by
        apply HNNExtension.of_injective (phi G D)
        simpa [w', tail, hr, hn, HNNExtension.NormalWord.ReducedWord.prod] using hzt
      apply Or.inl
      apply SimulatorIntersectionA.negative_terminal G D hv ha hu
      rw [he, hz'head, map_mul, map_inv]
      group
  | cons next more =>
      obtain ⟨s, b⟩ := next
      have hw' : w'.toList = (s, b) :: more := hr
      obtain ⟨_, _, _, hcoset, _⟩ := first_comparison (phi G D) w' z' hzt s b more hw'
      have hcoset' : (ofCore G D v * a)⁻¹ * ofCore G D u ∈
          HNNExtension.toSubgroup (left G D).range (right G D).range (-s) := by
        simpa only [hw'head, hz'head, map_mul, map_inv, mul_inv_rev, mul_assoc] using hcoset
      have huCoeff : ofCore G D u ∈ coefficients G D := ⟨u, hu, rfl⟩
      rcases Int.units_eq_one_or s with rfl | rfl
      · have hh : (ofCore G D v * a)⁻¹ * ofCore G D u ∈ (right G D).range := by
          simpa using hcoset'
        obtain ⟨p, q, hp, hq, he⟩ := right_coefficient_factorization G D _ _ huCoeff hh
        exact Or.inl (SimulatorIntersectionA.negative_next_negative G D hv ha he)
      · have hh : (ofCore G D v * a)⁻¹ * ofCore G D u ∈ (left G D).range := by
          simpa using hcoset'
        obtain ⟨p, q, hp, hq, he⟩ := left_coefficient_factorization G D _ _ huCoeff hh
        obtain ⟨g, Q, hag, hQ, hQP⟩ := SimulatorIntersectionA.negative_next_positive
          G D W a ha p q hp hq he
        refine Or.inr ⟨g, Q, ?_, hQ, hQP⟩
        intro hg
        have haone : a = 1 := by simpa [hg] using hag
        have hc := (List.isChain_cons.mp (hw ▸ w.chain)).1 (-1, b) (by simp [hr])
        have hh : (1 : ℤˣ) = -1 := hc (by simp [haone])
        norm_num at hh

end
end UniversalGroup.SimulatorIntersectionACompare
